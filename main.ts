// Room-decomposed push-optimal Sokoban solver.
// A level is a 1-wide hallway with 1-4 rooms off it; a box pushed out of a
// room can never come back, so each room is an independent problem and the
// level optimum is the sum of the rooms' optima. Each room is sv with a
// push-based A* (admissible min-assignment heuristic, deadlock pruning),
// then the rooms' move sequences are stitched together with hallway walks.
// Deterministic: the search is cut off by a fixed expansion budget, never
// by the clock, so two runs write the same bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const CAP = 400_000;
const D: [number, number, string][] = [[0, -1, 'u'], [0, 1, 'd'], [-1, 0, 'l'], [1, 0, 'r']];

type Lv = { w: number; h: number; wall: boolean[]; goals: number[]; boxes: number[]; player: number };

function ps(t: string): Lv {
  const rows = t.split('\n').filter((r) => r.length > 0);
  const w = Math.max(...rows.map((r) => r.length));
  const wall: boolean[] = new Array(w * rows.length).fill(true);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = false;
      if ('.*+'.includes(ch)) goals.push(i);
      if ('$*'.includes(ch)) boxes.push(i);
      if ('@+'.includes(ch)) player = i;
    }
  });
  boxes.sort((a, b) => a - b);
  return { w, h: rows.length, wall, goals, boxes, player };
}

// Shortest wk from `a` to `b` over cells where `pass` holds, or null.
function wk(a: number, b: number, pass: (c: number) => boolean, w: number): string | null {
  if (a === b) return '';
  const prev = new Map<number, [number, string]>([[a, [-1, '']]]);
  const q = [a];
  for (let i = 0; i < q.length; i++) {
    const c = q[i]!;
    for (const [dx, dy, ch] of D) {
      const n = c + dy * w + dx;
      if (!pass(n) || prev.has(n)) continue;
      prev.set(n, [c, ch]);
      if (n === b) {
        let s = ch;
        for (let t = c; t !== a; ) {
          const [p, pc] = prev.get(t)!;
          s = pc + s;
          t = p;
        }
        return s;
      }
      q.push(n);
    }
  }
  return null;
}

// Cells reachable from `a` over cells where `pass` holds.
function rg(a: number, pass: (c: number) => boolean, w: number): Set<number> {
  const out = new Set<number>([a]);
  const q = [a];
  for (let i = 0; i < q.length; i++) {
    const c = q[i]!;
    for (const [dx, dy] of D) {
      const n = c + dy * w + dx;
      if (pass(n) && !out.has(n)) {
        out.add(n);
        q.push(n);
      }
    }
  }
  return out;
}

function pm(n: number): number[][] {
  const out: number[][] = [];
  const a = [...Array(n).keys()];
  const gen = (k: number): void => {
    if (k === 1) {
      out.push([...a]);
      return;
    }
    for (let i = 0; i < k; i++) {
      gen(k - 1);
      const j = k % 2 === 0 ? i : 0;
      [a[j], a[k - 1]] = [a[k - 1], a[j]];
    }
  };
  gen(n);
  return out;
}

// Push-optimal A* over one room. `cells` are squares a box may occupy;
// `entry` is where the player starts (the hallway square outside the door,
// or the player's square for a whole-level fallback, where entry is in
// `cells`). Returns the move string, or null when over budget / unsolvable.
function sr(cells: Set<number>, entry: number, b0: number[], goals: number[], w: number): string | null {
  const gs = new Set(goals);
  const n = b0.length;
  const ps = n <= 5 ? pm(n) : null;
  const gd: Map<number, number>[] = goals.map((g) => {
    const d = new Map<number, number>([[g, 0]]);
    const q = [g];
    for (let i = 0; i < q.length; i++) {
      const c = q[i]!;
      for (const [dx, dy] of D) {
        const nn = c + dy * w + dx;
        if (cells.has(nn) && !d.has(nn)) {
          d.set(nn, d.get(c)! + 1);
          q.push(nn);
        }
      }
    }
    return d;
  });
  const st = (c: number): boolean => cells.has(c) || c === entry;
  const hh = (bs: number[]): number => {
    if (ps !== null) {
      let best = Infinity;
      for (const p of ps) {
        let s = 0;
        for (let i = 0; i < n; i++) {
          const d = gd[p[i]]!.get(bs[i]!);
          if (d === undefined) {
            s = Infinity;
            break;
          }
          s += d;
        }
        if (s < best) best = s;
      }
      return best;
    }
    let s = 0;
    for (const b of bs) {
      let m = Infinity;
      for (const d of gd) {
        const v = d.get(b);
        if (v !== undefined && v < m) m = v;
      }
      if (!isFinite(m)) return Infinity;
      s += m;
    }
    return s;
  };
  // Sound dd-position prunes only: a box with no grid path to any goal,
  // one frozen by walls alone, one in a full 2x2 block, or one trapped on
  // a wall segment (both ends closed by walls) that holds no goal.
  const dd = (bs: number[]): boolean => {
    const occ = new Set(bs);
    for (const b of bs) {
      if (gs.has(b)) continue;
      if (!gd.some((d) => d.has(b))) return true;
      let movable = false;
      for (const [dx, dy] of D) {
        if (cells.has(b + dy * w + dx) && st(b - dy * w - dx)) {
          movable = true;
          break;
        }
      }
      if (!movable) return true;
      for (const [dx, dy] of [[0, 0], [-1, 0], [0, -1], [-1, -1]] as [number, number][]) {
        const c0 = b + dy * w + dx;
        if ([c0, c0 + 1, c0 + w, c0 + w + 1].every((c) => (c !== entry && !cells.has(c)) || occ.has(c))) return true;
      }
      for (const [dx, dy] of D) {
        const side = b + dy * w + dx;
        if (cells.has(side) || side === entry) continue;
        const [px, py] = [-dy, dx];
        const step = py * w + px;
        const sd = dy * w + dx;
        let hasGoal = false;
        let closed = true;
        for (const sgn of [1, -1]) {
          for (let k = 0; ; k++) {
            const c = b + sgn * k * step;
            const inLine = step === 1 || step === -1 ? Math.floor(c / w) === Math.floor(b / w) : c % w === b % w;
            if (!inLine || !cells.has(c)) break;
            if (cells.has(c + sd)) {
              closed = false;
              break;
            }
            if (c !== b && occ.has(c)) {
              closed = false;
              break;
            }
            if (gs.has(c)) hasGoal = true;
          }
          if (!closed) break;
        }
        if (closed && !hasGoal) return true;
      }
    }
    return false;
  };
  const sv = (bs: number[]): boolean => bs.every((b) => gs.has(b));
  const key = (bs: number[], p: number): string => `${p}|${bs.join(',')}`;
  const cn = (bs: number[], p: number): number => {
    const occ = new Set(bs);
    let m = Infinity;
    for (const c of rg(p, (x) => st(x) && !occ.has(x), w)) if (c < m) m = c;
    return m;
  };
  const sB: number[][] = [b0.slice()];
  const sP: number[] = [entry];
  const sG: number[] = [0];
  const sPar: number[] = [-1];
  const sStep: string[] = [''];
  const best = new Map<string, number>([[key(b0, cn(b0, entry)), 0]]);
  if (dd(b0) || sv(b0)) return sv(b0) ? '' : null;
  const heap: [number, number, number, number][] = [];
  let seq = 0;
  const less = (a: [number, number, number, number], b: [number, number, number, number]): boolean =>
    a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  const hpush = (e: [number, number, number, number]): void => {
    heap.push(e);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const hpop = (): [number, number, number, number] => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
        if (!less(heap[c]!, heap[i]!)) break;
        [heap[i], heap[c]] = [heap[c]!, heap[i]!];
        i = c;
      }
    }
    return top;
  };
  const h0 = hh(b0);
  if (!isFinite(h0)) return null;
  hpush([h0, h0, seq++, 0]);
  let exp = 0;
  while (heap.length > 0) {
    const [, , , s] = hpop();
    const bs = sB[s]!;
    const g = sG[s]!;
    if (best.get(key(bs, cn(bs, sP[s]!))) !== s) continue;
    if (sv(bs)) {
      let moves = '';
      for (let t = s; t > 0; t = sPar[t]!) moves = sStep[t]! + moves;
      return moves;
    }
    if (++exp > CAP) return null;
    const p = sP[s]!;
    const occ = new Set(bs);
    const reach = rg(p, (c) => st(c) && !occ.has(c), w);
    for (let bi = 0; bi < n; bi++) {
      const b = bs[bi]!;
      for (const [dx, dy, ch] of D) {
        const dest = b + dy * w + dx;
        const behind = b - dy * w - dx;
        if (!cells.has(dest) || occ.has(dest)) continue;
        if (!st(behind) || occ.has(behind) || !reach.has(behind)) continue;
        const nb = bs.slice();
        nb[bi] = dest;
        nb.sort((a, b2) => a - b2);
        if (dd(nb)) continue;
        const w2 = wk(p, behind, (c) => st(c) && !occ.has(c), w);
        if (w2 === null) continue;
        const k2 = key(nb, cn(nb, b));
        const seen = best.get(k2);
        if (seen !== undefined && sG[seen]! <= g + 1) continue;
        const h = hh(nb);
        if (!isFinite(h)) continue;
        const t = sB.length;
        sB.push(nb);
        sP.push(b);
        sG.push(g + 1);
        sPar.push(s);
        sStep.push(w2 + ch);
        best.set(k2, t);
        hpush([g + 1 + h, h, seq++, t]);
      }
    }
  }
  return null;
}

// Replay moves on a level; pushes if sv, else -1.
function rp(t: string, moves: string): number {
  const lv = ps(t);
  const occ = new Set(lv.boxes);
  let p = lv.player;
  let pushes = 0;
  for (const ch of moves) {
    const d = D.find(([, , c]) => c === ch.toLowerCase());
    if (!d) return -1;
    const q = p + d[1] * lv.w + d[0];
    if (lv.wall[q]) return -1;
    if (occ.has(q)) {
      const beyond = q + d[1] * lv.w + d[0];
      if (lv.wall[beyond] || occ.has(beyond)) return -1;
      occ.delete(q);
      occ.add(beyond);
      pushes++;
    }
    p = q;
  }
  const goals = new Set(lv.goals);
  for (const b of occ) if (!goals.has(b)) return -1;
  return pushes;
}

function sl(t: string): string {
  const lv = ps(t);
  const H = Math.floor(lv.player / lv.w);
  const seen = new Set<number>();
  type Room = { cells: Set<number>; boxes: number[]; goals: number[]; door: number; entry: number };
  const rooms: Room[] = [];
  let ok = true;
  for (let y = 0; y < lv.h; y++) {
    for (let x = 0; x < lv.w; x++) {
      const i = y * lv.w + x;
      if (lv.wall[i] || y === H || seen.has(i)) continue;
      const cells = new Set<number>();
      const q = [i];
      seen.add(i);
      for (let j = 0; j < q.length; j++) {
        const c = q[j]!;
        cells.add(c);
        for (const [dx, dy] of D) {
          const nn = c + dy * lv.w + dx;
          if (Math.floor(nn / lv.w) === H || lv.wall[nn] || seen.has(nn)) continue;
          seen.add(nn);
          q.push(nn);
        }
      }
      const boxes = lv.boxes.filter((b) => cells.has(b));
      const goals = lv.goals.filter((g) => cells.has(g));
      const touch = [...cells].filter((c) => {
        const yy = Math.floor(c / lv.w);
        const nn = yy < H ? c + lv.w : c - lv.w;
        return Math.floor(nn / lv.w) === H && !lv.wall[nn];
      });
      if (boxes.length === 0 || boxes.length !== goals.length || touch.length !== 1) {
        ok = false;
        continue;
      }
      const door = touch[0]!;
      rooms.push({ cells, boxes, goals, door, entry: Math.floor(door / lv.w) < H ? door + lv.w : door - lv.w });
    }
  }
  if (ok && rooms.reduce((a, r) => a + r.boxes.length, 0) !== lv.boxes.length) ok = false;
  if (ok) {
    const sols = rooms.map((r) => ({ ...r, sol: sr(r.cells, r.entry, r.boxes, r.goals, lv.w) }));
    if (sols.every((r) => r.sol !== null)) {
      let cur = lv.player;
      let moves = '';
      const rest = [...sols];
      while (rest.length > 0) {
        let bi = 0;
        for (let i = 1; i < rest.length; i++) {
          const da = Math.abs((rest[i]!.entry % lv.w) - (cur % lv.w));
          const db = Math.abs((rest[bi]!.entry % lv.w) - (cur % lv.w));
          if (da < db || (da === db && rest[i]!.entry < rest[bi]!.entry)) bi = i;
        }
        const r = rest.splice(bi, 1)[0]!;
        const hall = (c: number): boolean => Math.floor(c / lv.w) === H && !lv.wall[c];
        const toDoor = wk(cur, r.entry, hall, lv.w);
        if (toDoor === null) return '';
        moves += toDoor + r.sol!;
        const occ = new Set(r.boxes);
        let p = r.entry;
        for (const ch of r.sol!) {
          const d = D.find(([, , c]) => c === ch)!;
          const q = p + d[1] * lv.w + d[0];
          if (occ.has(q)) {
            occ.delete(q);
            occ.add(q + d[1] * lv.w + d[0]);
          }
          p = q;
        }
        const exit = wk(p, r.door, (c) => (r.cells.has(c) || c === r.entry) && !occ.has(c), lv.w);
        if (exit === null) return '';
        moves += exit + (r.door < r.entry ? 'd' : 'u');
        cur = r.entry;
      }
      if (rp(t, moves) >= 0) return moves;
    }
  }
  const all = new Set<number>();
  for (let i = 0; i < lv.w * lv.h; i++) if (!lv.wall[i]) all.add(i);
  const sol = sr(all, lv.player, lv.boxes, lv.goals, lv.w);
  if (sol !== null && rp(t, sol) >= 0) return sol;
  return '';
}

for (const id of readdirSync(I).sort()) {
  const moves = sl(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
