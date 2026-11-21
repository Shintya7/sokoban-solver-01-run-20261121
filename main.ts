// Push-optimal Sokoban solver. The generator lays a one-cell hallway across
// the board with 1-4 rooms off it through one door each, and a box pushed
// out of a room can never return, so every box stays in its room and the
// level optimum is the sum of its rooms' optima. Split into rooms, solve
// each room push-optimally with A* over pushes, stitch with hallway walks
// (zero extra pushes). Heuristic: minimum assignment of boxes to goals by
// wall-only BFS distance (admissible and consistent). Deadlocks pruned:
// statically dead squares (pull reachability), frozen boxes, 2x2 blocks.
// Budgets count expanded states, never wall time, so runs are byte-identical.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const RCAP = 600_000, TCAP = 2_500_000;
const DX = [0, 0, -1, 1], DY = [-1, 1, 0, 0], LT = ['u', 'd', 'l', 'r'], OP = [1, 0, 3, 2];
let TE = 0;
function path(nbr, N, a, b, blk) {
  if (a === b) return '';
  const par = new Int32Array(N).fill(-1), pd = new Int8Array(N), q = new Int32Array(N);
  let qh = 0, qt = 0;
  q[qt++] = a; par[a] = a;
  while (qh < qt) {
    const c = q[qh++];
    for (let d = 0; d < 4; d++) {
      const nb = nbr[c * 4 + d];
      if (nb < 0 || par[nb] !== -1 || blk[nb]) continue;
      par[nb] = c; pd[nb] = d;
      if (nb === b) { let s = ''; for (let t = b; t !== a; t = par[t]) s = LT[pd[t]] + s; return s; }
      q[qt++] = nb;
    }
  }
  return null;
}
function parse(t) {
  const rows = t.split('\n').filter((r) => r.length > 0);
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1), goals = [], boxes = [];
  let pl = 0, px = 0, py = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#', i = y * w + x;
      if (ch !== '#') wall[i] = 0;
      if ('.*+'.includes(ch)) goals.push(i);
      if ('$*'.includes(ch)) boxes.push(i);
      if ('@+'.includes(ch)) { pl = i; px = x; py = y; }
    }
  });
  boxes.sort((a, b) => a - b); goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, pl, px, py };
}
function roomsOf(L) {
  const { w, h, wall, boxes, goals, py } = L, hr = py;
  const fl = (x, y) => x >= 0 && y >= 0 && x < w && y < h && !wall[y * w + x];
  const seen = new Uint8Array(w * h), rooms = [];
  let bs = 0, gs = 0;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (y === hr || !fl(x, y) || seen[y * w + x]) continue;
    const comp = [], st = [y * w + x];
    seen[y * w + x] = 1;
    while (st.length) {
      const c = st.pop(), cx = c % w, cy = Math.floor(c / w);
      comp.push(c);
      for (let d = 0; d < 4; d++) {
        const nx = cx + DX[d], ny = cy + DY[d];
        if (ny === hr || !fl(nx, ny) || seen[ny * w + nx]) continue;
        seen[ny * w + nx] = 1; st.push(ny * w + nx);
      }
    }
    comp.sort((a, b) => a - b);
    const set = new Set(comp);
    const dr = comp.filter((c) => fl(c % w, hr) && Math.abs(Math.floor(c / w) - hr) === 1);
    if (dr.length !== 1) return null;
    const door = dr[0], rb = boxes.filter((b) => set.has(b)), rg = goals.filter((g) => set.has(g));
    if (!rb.length || rb.length !== rg.length) return null;
    bs += rb.length; gs += rg.length;
    rooms.push({ cells: comp, door, entry: hr * w + (door % w), boxes: rb, goals: rg });
  }
  if (bs !== boxes.length || gs !== goals.length) return null;
  rooms.sort((a, b) => a.door - b.door);
  return rooms;
}
function solveRoom(L, R, needExit) {
  const { w } = L, cells = R.cells, n = cells.length;
  const loc = new Map();
  cells.forEach((c, i) => loc.set(c, i));
  const eLoc = loc.has(R.entry) ? loc.get(R.entry) : n;
  const N = eLoc === n ? n + 1 : n;
  const lx = new Int32Array(N), ly = new Int32Array(N);
  cells.forEach((c, i) => { lx[i] = c % w; ly[i] = Math.floor(c / w); });
  if (eLoc === n) { lx[n] = R.entry % w; ly[n] = Math.floor(R.entry / w); }
  const wl = new Map(loc); wl.set(R.entry, eLoc);
  const at = (gx, gy) => {
    if (gx < 0 || gy < 0 || gx >= w || gy >= L.h) return -1;
    const j = wl.get(gy * w + gx);
    return j === undefined ? -1 : j;
  };
  const nbr = new Int32Array(N * 4).fill(-1);
  for (let i = 0; i < N; i++) for (let d = 0; d < 4; d++) nbr[i * 4 + d] = at(lx[i] + DX[d], ly[i] + DY[d]);
  const b0 = R.boxes.map((b) => loc.get(b)).sort((a, b) => a - b);
  const gl = R.goals.map((g) => loc.get(g)).sort((a, b) => a - b);
  const m = b0.length, gset = new Set(gl);
  const dist = new Float64Array(m * n).fill(Infinity);
  for (let g = 0; g < m; g++) {
    const q = [gl[g]]; dist[g * n + gl[g]] = 0;
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi];
      for (let d = 0; d < 4; d++) {
        const nb = nbr[c * 4 + d];
        if (nb < 0 || nb >= n || dist[g * n + nb] !== Infinity) continue;
        dist[g * n + nb] = dist[g * n + c] + 1; q.push(nb);
      }
    }
  }
  const alive = new Uint8Array(n), wk = [];
  for (const g of gl) { alive[g] = 1; wk.push(g); }
  while (wk.length) {
    const y = wk.pop();
    for (let d = 0; d < 4; d++) {
      const od = OP[d], x = nbr[y * 4 + od];
      if (x < 0 || x >= n || alive[x]) continue;
      if (nbr[x * 4 + od] < 0) continue;
      alive[x] = 1; wk.push(x);
    }
  }
  const dead = new Uint8Array(n);
  for (let i = 0; i < n; i++) if (!alive[i]) dead[i] = 1;
  const perms = [];
  const pr = (cur, used) => {
    if (cur.length === m) { perms.push(cur.slice()); return; }
    for (let g = 0; g < m; g++) {
      if (used[g]) continue;
      used[g] = true; cur.push(g); pr(cur, used); cur.pop(); used[g] = false;
    }
  };
  pr([], new Array(m).fill(false));
  const hc = new Map();
  const enc = (bs) => {
    if (bs.length > 5) return bs.join(',');
    let c = 0, k = 1;
    for (let i = 0; i < bs.length; i++) { c += bs[i] * k; k *= 256; }
    return c;
  };
  const dec = (code) => {
    if (typeof code === 'string') return code.split(',').map(Number);
    const bs = []; let c = code;
    for (let i = 0; i < m; i++) { bs.push(c % 256); c = Math.floor(c / 256); }
    return bs;
  };
  const key = (bs, rep) => {
    const c = enc(bs);
    return typeof c === 'number' ? c * 256 + rep : c + ':' + rep;
  };
  const heur = (bs) => {
    const c = enc(bs), hit = hc.get(c);
    if (hit !== undefined) return hit;
    let best = Infinity;
    for (const p of perms) {
      let s = 0;
      for (let i = 0; i < m; i++) {
        const d = dist[p[i] * n + bs[i]];
        if (d === Infinity) { s = Infinity; break; }
        s += d;
      }
      if (s < best) best = s;
    }
    hc.set(c, best);
    return best;
  };
  const rmk = new Int32Array(N), rpm = new Int32Array(N);
  const rr = { v: 0 }, pr2 = { v: 0 };
  const flood = (mk, st, s, bm) => {
    st.v++;
    const v = st.v, q = [s];
    mk[s] = v;
    let mn = s;
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi];
      for (let d = 0; d < 4; d++) {
        const nb = nbr[c * 4 + d];
        if (nb < 0 || mk[nb] === v || bm[nb]) continue;
        mk[nb] = v; if (nb < mn) mn = nb; q.push(nb);
      }
    }
    return mn;
  };
  const fmin = (s, bm) => flood(rmk, rr, s, bm);
  const frep = (s, bm) => flood(rpm, pr2, s, bm);
  const markOf = (bs) => {
    const mk = new Uint8Array(N);
    for (const b of bs) mk[b] = 1;
    return mk;
  };
  const isGoal = (bs) => {
    for (let i = 0; i < m; i++) if (bs[i] !== gl[i]) return false;
    return true;
  };
  const frozen = (bs) => {
    const fr = new Uint8Array(n);
    let ch = true;
    while (ch) {
      ch = false;
      for (const b of bs) {
        if (fr[b]) continue;
        const bl = (j) => j === -1 || (j < n && fr[j] === 1);
        if ((bl(nbr[b * 4 + 2]) || bl(nbr[b * 4 + 3])) && (bl(nbr[b * 4]) || bl(nbr[b * 4 + 1]))) {
          fr[b] = 1; ch = true;
        }
      }
    }
    for (const b of bs) if (fr[b] && !gset.has(b)) return true;
    return false;
  };
  const two = (bs, t, set) => {
    const tx = lx[t], ty = ly[t];
    const kd = (gx, gy) => {
      const j = at(gx, gy);
      if (j < 0) return 2;
      if (j < n && set.has(j)) return 1;
      return 0;
    };
    for (const [ox, oy] of [[-1, -1], [0, -1], [-1, 0], [0, 0]]) {
      let solid = true, off = false;
      for (let a = 0; a < 2 && solid; a++) for (let b = 0; b < 2; b++) {
        const k = kd(tx + ox + a, ty + oy + b);
        if (k === 0) { solid = false; break; }
        if (k === 1 && !gset.has(at(tx + ox + a, ty + oy + b))) off = true;
      }
      if (solid && off) return true;
    }
    return false;
  };
  const sDead = (bs, mv) => {
    for (const b of bs) if (dead[b]) return true;
    if (frozen(bs)) return true;
    if (two(bs, mv, new Set(bs))) return true;
    return false;
  };
  const cA = [], pA = [], paA = [], pbA = [], pdA = [], gA = [], fA = [], sA = [], kA = [];
  let sq = 0;
  const add = (code, pl, par, pb, pd, g, f, ky) => {
    const i = cA.length;
    cA.push(code); pA.push(pl); paA.push(par); pbA.push(pb); pdA.push(pd);
    gA.push(g); fA.push(f); sA.push(sq++); kA.push(ky);
    return i;
  };
  const hp = [];
  const hl = (a, b) => {
    if (fA[a] !== fA[b]) return fA[a] < fA[b];
    if (gA[a] !== gA[b]) return gA[a] > gA[b];
    return sA[a] < sA[b];
  };
  const hpush = (x) => {
    let i = hp.length;
    hp.push(x);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!hl(hp[i], hp[p])) break;
      const t = hp[i]; hp[i] = hp[p]; hp[p] = t; i = p;
    }
  };
  const hpop = () => {
    const top = hp[0], last = hp.pop();
    if (hp.length > 0) {
      hp[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= hp.length) break;
        if (c + 1 < hp.length && hl(hp[c + 1], hp[c])) c++;
        if (!hl(hp[c], hp[i])) break;
        const t = hp[i]; hp[i] = hp[c]; hp[c] = t; i = c;
      }
    }
    return top;
  };
  const best = new Map();
  const rm = markOf(b0);
  if (b0.some((b) => sDead(b0, b))) return null;
  const h0 = heur(b0);
  if (h0 === Infinity) return null;
  const rk = key(b0, fmin(eLoc, rm));
  const rt = add(enc(b0), eLoc, -1, -1, -1, 0, h0, rk);
  best.set(rk, 0); hpush(rt);
  let ex = 0, gi = -1;
  while (hp.length > 0) {
    const ix = hpop();
    if (best.get(kA[ix]) !== gA[ix]) continue;
    const bs = dec(cA[ix]), g = gA[ix];
    if (isGoal(bs)) {
      if (!needExit) { gi = ix; break; }
      const mk = markOf(bs);
      fmin(pA[ix], mk);
      if (rmk[eLoc] === rr.v) { gi = ix; break; }
      continue;
    }
    ex++; TE++;
    if (ex > RCAP || TE > TCAP) return null;
    const mk = markOf(bs);
    fmin(pA[ix], mk);
    const ms = rr.v;
    for (let bi = 0; bi < m; bi++) {
      const b = bs[bi];
      for (let d = 0; d < 4; d++) {
        const t = nbr[b * 4 + d];
        if (t < 0 || t >= n || mk[t]) continue;
        const fr = nbr[b * 4 + OP[d]];
        if (fr < 0 || rmk[fr] !== ms) continue;
        const nb2 = bs.slice();
        nb2[bi] = t; nb2.sort((a, c) => a - c);
        if (sDead(nb2, t)) continue;
        const h = heur(nb2);
        if (h === Infinity) continue;
        const ng = g + 1;
        mk[b] = 0; mk[t] = 1;
        const rep = frep(b, mk);
        mk[b] = 1; mk[t] = 0;
        const ky = key(nb2, rep), pv = best.get(ky);
        if (pv !== undefined && pv <= ng) continue;
        best.set(ky, ng);
        hpush(add(enc(nb2), b, ix, b, d, ng, ng + h, ky));
      }
    }
  }
  if (gi < 0) return null;
  const fb = dec(cA[gi]), parts = [];
  let cur = gi;
  while (paA[cur] !== -1) {
    const p = paA[cur], pb2 = dec(cA[p]), pm = markOf(pb2);
    const fr = nbr[pbA[cur] * 4 + OP[pdA[cur]]];
    const wk2 = path(nbr, N, pA[p], fr, pm);
    if (wk2 === null) return null;
    parts.push(wk2 + LT[pdA[cur]]);
    cur = p;
  }
  parts.reverse();
  let mv = parts.join('');
  const fm = markOf(fb);
  const ew = path(nbr, N, pA[gi], eLoc, fm);
  let exited = false;
  if (ew !== null) { mv += ew; exited = true; }
  return { moves: mv, pushes: gA[gi], exited, expansions: ex };
}
function solveLevel(t) {
  const L = parse(t);
  const { w, h, wall, boxes, goals, pl } = L;
  let R = roomsOf(L);
  if (R === null) {
    const cells = [];
    for (let i = 0; i < w * h; i++) if (!wall[i]) cells.push(i);
    R = [{ cells, door: pl, entry: pl, boxes, goals }];
  }
  const S = R.map((r) => solveRoom(L, r, false));
  for (let i = 0; i < R.length; i++) if (S[i] === null) return '';
  const trap = [];
  for (let i = 0; i < R.length; i++) if (!S[i].exited) trap.push(i);
  const good = [];
  for (let i = 0; i < R.length; i++) if (!trap.includes(i)) good.push(i);
  if (trap.length > 1) {
    for (let k = 0; k < trap.length - 1; k++) {
      const ri = trap[k], rt2 = solveRoom(L, R[ri], true);
      if (rt2 !== null && rt2.exited) { S[ri] = rt2; good.push(ri); }
    }
  }
  const last = trap.filter((ri) => !good.includes(ri));
  const order = [...good, ...last];
  const gn = new Int32Array(w * h * 4).fill(-1);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = y * w + x;
    if (wall[i]) continue;
    for (let d = 0; d < 4; d++) {
      const nx = x + DX[d], ny = y + DY[d];
      if (nx < 0 || ny < 0 || nx >= w || ny >= h || wall[ny * w + nx]) continue;
      gn[i * 4 + d] = ny * w + nx;
    }
  }
  const gm = new Uint8Array(w * h);
  for (const b of boxes) gm[b] = 1;
  let pp = pl, mv = '';
  for (const ri of order) {
    const rm2 = R[ri], sl = S[ri];
    const wk3 = path(gn, w * h, pp, rm2.entry, gm);
    if (wk3 === null) return '';
    mv += wk3;
    for (const b of rm2.boxes) gm[b] = 0;
    for (const g of rm2.goals) gm[g] = 1;
    mv += sl.moves;
    pp = rm2.entry;
    if (!sl.exited) pp = -1;
    if (pp === -1 && ri !== order[order.length - 1]) return '';
  }
  return mv;
}
for (const id of readdirSync(I).sort()) {
  const mv = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${mv}\n`);
}
