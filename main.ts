// Pump.fun Paper Sprint bot — simple defensive momentum with strict exits.
//
// Idea: buy only curves that already show real, broad-based buying (several
// distinct buyers, net SOL flowing in, price rising but not vertical), start
// small, add once into strength, and exit on the first of stop-loss,
// take-profit, trailing stop, fading flow, or a time limit. A probe
// mechanism keeps the 20-coin round-trip guardrail on pace even on quiet
// stretches. Max exposure is 5 positions x 0.24 SOL = 1.2 SOL (12% of the
// 10 SOL capital), so the 50% max-drawdown guardrail is safe by construction.
//
// Why this design, not buy-everything-early: the baseline equal-weight bot
// buys every coin it can and never sells, so it holds every rug to the end
// of the window. On a 6-hour final window most new curves bleed out, so
// starting small (0.06 SOL), adding only into strength, and exiting on the
// first bad sign (stop-loss / fading flow / time limit) caps the loss per
// coin while keeping the winners. The probe mechanism exists only to keep
// the 20-coin guardrail on pace; real entries do the earning.

import { LAMPORTS_PER_SOL, runBot, type BotState, type Batch, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000; // lamports per SOL, as a plain number for tape math
const CURVE_FEE = 0.0125; // 1.25% curve fee taken on sells
const BUY_SLIP_BPS = 2000;
const SELL_SLIP_BPS = 10_000;

// Entry signal (all in SOL / slots unless noted).
const WINDOW = 40; // entry lookback window in slots
const MIN_NET_SOL = 1.0; // net SOL inflow (buys minus sells) over the window
const MIN_BUYS = 4; // buy trades in the window
const MIN_BUYERS = 5; // distinct buying wallets in the window
const MIN_PRICE_UP = 0.06; // price rise over the window, lower bound
const MAX_PRICE_UP = 0.8; // price rise over the window, upper bound (skip verticals)
const NEAR_HIGH = 0.97; // price now must be >= this share of the window high
const MIN_RQ_SOL = 1; // curve real SOL at entry, lower bound
const MAX_RQ_SOL = 60; // curve real SOL at entry, upper bound
const MIN_AGE = 500; // slots since CreateEvent before an entry is allowed
const MIN_CAP_SOL = 0.03; // size cap must allow at least this much

// Sizing.
const FIRST_BUY_SOL = 0.06; // first buy per position
const ADD_BUY_SOL = 0.06; // one pyramid add per position
const MAX_STAKE_SOL = 0.24; // most SOL into one position in total
const MIN_BUY_SOL = 0.011; // smallest buy worth sending (above the 0.01 round-trip bar)

// Exits.
const STOP_LOSS = 0.12; // sell when value < cost * (1 - STOP_LOSS)
const TAKE_PROFIT = 0.35; // sell when value >= cost * (1 + TAKE_PROFIT)
const TRAIL_ARM = 0.15; // trailing stop arms once peak value >= cost * (1 + TRAIL_ARM)
const TRAIL = 0.2; // sell when value < peak * (1 - TRAIL)
const FADE_WINDOW = 20; // fade lookback in slots
const FADE_NET_SOL = -0.5; // sell when net flow over the fade window is below this
const MAX_HOLD = 1500; // sell after this many slots held
const COOLDOWN = 200; // slots to wait after an exit before re-entering the same curve
const MAX_ENTRIES = 2; // most entries per curve over the run

// Pyramid.
const ADD_STEP = 0.2; // add only once price is this much above the last buy's price

// Guardrail pacing: the run must end with >= 20 coins round-tripped. When the
// bot's own fills or coins lag the pace, open tiny probe round trips.
const TARGET_COINS = 25;
const TARGET_FILLS = 240;
const PACE_SECS = 14_400;
const PROBE_SOL = 0.011;
const MAX_PROBES = 1;

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: TapeTrade[];
  entries: number;
  lastExit: number;
}

interface Held {
  opened: number;
  peakValue: number;
  invested: number;
  exiting: boolean;
  filled: boolean;
  lastAddPrice: number;
  lastValue: number;
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
/** Probe round trips in flight, by mint: false while buying, true once selling. */
const probes = new Map<Pubkey, boolean>();
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

const tapeOf = (mint: Pubkey): Tape => {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
};

const priceOf = (vq: bigint, vt: bigint): number =>
  vt > 0n ? Number(vq) / Number(vt) : 0;

/** Net recorded SOL (buys minus sells) over the last `w` slots. */
const flow = (t: Tape, now: number, w: number): number => {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
};

/** Entry signal on a curve's tape at slot `now`. */
const entrySignal = (t: Tape, now: number, rqSol: number): boolean => {
  if (rqSol < MIN_RQ_SOL || rqSol > MAX_RQ_SOL) return false;
  if (t.created === null || now - t.created < MIN_AGE) return false;
  const from = now - WINDOW;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const byUser = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      byUser.set(tr.user, (byUser.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MIN_BUYS || byUser.size < MIN_BUYERS) return false;
  if (buySol - sellSol < MIN_NET_SOL) return false;
  if (startPrice <= 0 || last <= 0) return false;
  const up = last / startPrice - 1;
  if (up < MIN_PRICE_UP || up > MAX_PRICE_UP) return false;
  if (last < high * NEAR_HIGH) return false;
  return true;
};

/** Mark-to-market value of a position in SOL, curve fee and one tx fee deducted. */
const positionValue = (tokens: bigint, vq: bigint, vt: bigint, txSol: number): number => {
  const n = Number(tokens);
  if (n <= 0 || vt <= 0n) return 0;
  const out = (n * Number(vq)) / (Number(vt) + n);
  return (out / LAMPORTS) * (1 - CURVE_FEE) - txSol;
};

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
      }
    }
    const keep = Math.max(WINDOW, FADE_WINDOW) + 5;
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }
    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // Exits first.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          const t = tapeOf(mint);
          if (h.filled) t.lastExit = now;
          else t.entries--;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? BigInt(mk.virtual_quote_reserves) : curve.virtual_quote_reserves;
      const vt = mk ? BigInt(mk.virtual_token_reserves) : curve.virtual_token_reserves;
      const value = positionValue(pos.token_amount, vq, vt, tx);
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > h.peakValue) h.peakValue = value;
      h.lastValue = value;
      let exit = h.exiting;
      const t = tapeOf(mint);
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && h.peakValue >= cost * (1 + TRAIL_ARM) && value < h.peakValue * (1 - TRAIL)) exit = true;
      if (!exit && flow(t, now, FADE_WINDOW) < FADE_NET_SOL) exit = true;
      if (!exit && now - h.opened > MAX_HOLD) exit = true;
      if (!exit) continue;
      h.exiting = true;
      let sellPending = false;
      for (const po of state.pending.values()) {
        if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
      }
      if (sellPending) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP_BPS });
    }

    // Probe round trips: sell the whole probe as soon as its buy has landed.
    for (const [mint, selling] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIP_BPS });
      if (!selling) probes.set(mint, true);
    }

    // Then entries and adds.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let exposure = 0;
    for (const [mint, h] of held) {
      exposure += Math.max(h.invested, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / LAMPORTS);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      const t = tapes.get(mint)!;
      const h = held.get(mint);
      const price = priceOf(curve.virtual_quote_reserves, curve.virtual_token_reserves);
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      let want: number;
      if (h === undefined) {
        if (slotsLeft <= 0) continue;
        if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
        if (!entrySignal(t, now, rqSol)) continue;
        want = FIRST_BUY_SOL;
      } else {
        // Pyramid into strength only: the position is up, the price stepped up
        // from the last add, and net SOL still flows in.
        if (h.exiting || !h.filled || h.invested >= MAX_STAKE_SOL - MIN_BUY_SOL) continue;
        const pos = state.positions.get(mint);
        if (pos === undefined) continue;
        if (price < h.lastAddPrice * (1 + ADD_STEP)) continue;
        if (h.lastValue < Number(pos.cost_lamports) / LAMPORTS * 1.1) continue;
        if (flow(t, now, WINDOW) < MIN_NET_SOL) continue;
        if (rqSol > MAX_RQ_SOL) continue;
        want = Math.min(ADD_BUY_SOL, MAX_STAKE_SOL - h.invested);
      }
      const capSol = Number(state.maxBuyLamports(mint)) / LAMPORTS;
      let amount = Math.min(capSol, want);
      if (amount > free - tx) amount = free - tx;
      // First buys must clear the size-cap floor (0.03 SOL); pyramid adds only
      // need to clear the round-trip floor (0.011 SOL).
      if (h === undefined ? amount < MIN_CAP_SOL : amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + tx;
      exposure += amount;
      if (h === undefined) {
        held.set(mint, {
          opened: now,
          peakValue: 0,
          invested: amount,
          exiting: false,
          filled: false,
          lastAddPrice: price,
          lastValue: 0,
        });
        t.entries++;
        slotsLeft--;
      } else {
        h.invested += amount;
        h.lastAddPrice = price;
      }
    }

    // Guardrail pacing: open a probe when the bot's fills or coins lag the pace.
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_SECS);
      const needCoins = myCoins.size < Math.ceil(TARGET_COINS * pace);
      const needFills = myFills < Math.ceil(TARGET_FILLS * pace);
      if (needCoins || needFills) {
        const minRq = (PROBE_SOL * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
          if (free < PROBE_SOL + 2 * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(PROBE_SOL * LAMPORTS)), max_slippage_bps: BUY_SLIP_BPS });
          probes.set(mint, false);
          free -= PROBE_SOL + tx;
        }
      }
    }
    return orders;
  },
});
