// Sokoban solver: push-optimal per room, stitched into one answer.
//
// Idea (my own implementation): the generator lays a one-cell-wide hallway
// across the board and hangs 1-4 rooms off it through a single door each, and
// a box pushed out of a room can never come back, so every box stays in its
// room and the level's push-optimal count is the sum of its rooms' optima.
// I therefore split the level into its rooms, solve each room push-optimally
// with A* over pushes, and stitch the room solutions together with plain
// walks through the hallway. The player never needs to push between rooms,
// so the stitching adds zero pushes.
//
// Room search: a state is the sorted box cells plus the player's reachable
// region (canonicalised to its lowest cell). Successors are the pushes the
// player can reach. The heuristic is the minimum assignment of boxes to
// goals by wall-only BFS distance, which is admissible (one push moves one
// box one cell) and consistent, so the first goal state popped is optimal.
// Deadlocks pruned: statically dead squares (a box that can never be pulled
// onto a goal), frozen boxes (iteratively, blocked on both sides of an axis
// by walls or frozen boxes), and 2x2 blocks of wall/box holding a box off a
// goal. Budgets are counted in expanded states, never in wall-clock time,
// so two runs write identical bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DEBUG = process.env.SOKOBAN_DEBUG === '1';

// Deterministic work budgets (expanded states, not seconds).
const ROOM_EXPANSION_CAP = 600_000;
const TOTAL_EXPANSION_CAP = 2_500_000;

const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const LETTER = ['u', 'd', 'l', 'r'];
const OPP = [1, 0, 3, 2];

let totalExpansions = 0;

function dbg(...args: unknown[]): void {
  if (DEBUG) console.error(...args);
}

/** Shortest walk (letters) from `from` to `to` over a neighbour table, or null. */
function bfsPath(
  nbr: Int32Array,
  count: number,
  from: number,
  to: number,
  blocked: Uint8Array,
): string | null {
  if (from === to) return '';
  const parent = new Int32Array(count).fill(-1);
  const parentDir = new Int8Array(count);
  const queue = new Int32Array(count);
  let qh = 0;
  let qt = 0;
  queue[qt++] = from;
  parent[from] = from;
  while (qh < qt) {
    const c = queue[qh++]!;
    for (let d = 0; d < 4; d++) {
      const nb = nbr[c * 4 + d]!;
      if (nb < 0 || parent[nb] !== -1 || blocked[nb]) continue;
      parent[nb] = c;
      parentDir[nb] = d;
      if (nb === to) {
        let s = '';
        for (let t = to; t !== from; t = parent[t]!) s = LETTER[parentDir[t]!] + s;
        return s;
      }
      queue[qt++] = nb;
    }
  }
  return null;
}

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
  playerX: number;
  playerY: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = 0;
  let playerX = 0;
  let playerY = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      if (ch !== '#') wall[i] = 0;
      if ('.*+'.includes(ch)) goals.push(i);
      if ('$*'.includes(ch)) boxes.push(i);
      if ('@+'.includes(ch)) {
        player = i;
        playerX = x;
        playerY = y;
      }
    }
  });
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player, playerX, playerY };
}

interface Room {
  cells: number[]; // global cell indices of the room floor, sorted
  door: number; // global cell index of the door cell
  entry: number; // global cell index of the hallway cell outside the door
  boxes: number[]; // global box cells in this room
  goals: number[]; // global goal cells in this room
}

/** Split a level into hallway + rooms. Null when the shape is unexpected. */
function decompose(level: Level): Room[] | null {
  const { w, h, wall, boxes, goals, playerY } = level;
  const hallRow = playerY;
  const floor = (x: number, y: number): boolean =>
    x >= 0 && y >= 0 && x < w && y < h && !wall[y * w + x];
  const seen = new Uint8Array(w * h);
  const rooms: Room[] = [];
  let boxesSeen = 0;
  let goalsSeen = 0;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (y === hallRow || !floor(x, y) || seen[y * w + x]) continue;
      const comp: number[] = [];
      const stack = [y * w + x];
      seen[y * w + x] = 1;
      while (stack.length) {
        const c = stack.pop()!;
        comp.push(c);
        const cx = c % w;
        const cy = Math.floor(c / w);
        for (let d = 0; d < 4; d++) {
          const nx = cx + DX[d]!;
          const ny = cy + DY[d]!;
          if (ny === hallRow || !floor(nx, ny) || seen[ny * w + nx]) continue;
          seen[ny * w + nx] = 1;
          stack.push(ny * w + nx);
        }
      }
      comp.sort((a, b) => a - b);
      const compSet = new Set(comp);
      const doors = comp.filter(
        (c) => floor(c % w, hallRow) && Math.abs(Math.floor(c / w) - hallRow) === 1,
      );
      if (doors.length !== 1) return null;
      const door = doors[0]!;
      const entry = hallRow * w + (door % w);
      const rBoxes = boxes.filter((b) => compSet.has(b));
      const rGoals = goals.filter((g) => compSet.has(g));
      if (rBoxes.length === 0 || rBoxes.length !== rGoals.length) return null;
      boxesSeen += rBoxes.length;
      goalsSeen += rGoals.length;
      rooms.push({ cells: comp, door, entry, boxes: rBoxes, goals: rGoals });
    }
  }
  if (boxesSeen !== boxes.length || goalsSeen !== goals.length) return null;
  rooms.sort((a, b) => a.door - b.door);
  return rooms;
}

interface RoomSolution {
  moves: string; // full move letters for this room, starting with the player on entry
  pushes: number;
  exited: boolean; // player ends on the entry cell
  expansions: number;
}

/** Push-optimal A* for one room. The player starts on `room.entry`. */
function solveRoom(level: Level, room: Room, exitRequired: boolean): RoomSolution | null {
  const { w } = level;
  const cells = room.cells;
  const n = cells.length;
  const loc = new Map<number, number>();
  cells.forEach((c, i) => loc.set(c, i));
  // The entry is a hallway cell, outside the room; in the fallback (whole
  // level as one room) it is the player's start cell, inside the room.
  const entryLocal = loc.has(room.entry) ? loc.get(room.entry)! : n;
  const N = entryLocal === n ? n + 1 : n; // walkable cells: room cells + entry
  const lx = new Int32Array(N);
  const ly = new Int32Array(N);
  cells.forEach((c, i) => {
    lx[i] = c % w;
    ly[i] = Math.floor(c / w);
  });
  if (entryLocal === n) {
    lx[n] = room.entry % w;
    ly[n] = Math.floor(room.entry / w);
  }
  const walkLoc = new Map<number, number>(loc);
  walkLoc.set(room.entry, entryLocal);
  const atLocal = (gx: number, gy: number): number => {
    if (gx < 0 || gy < 0 || gx >= w || gy >= level.h) return -1;
    const j = walkLoc.get(gy * w + gx);
    return j === undefined ? -1 : j;
  };
  // Neighbour table over walkable cells (room cells + entry).
  const nbr = new Int32Array(N * 4).fill(-1);
  for (let i = 0; i < N; i++) {
    for (let d = 0; d < 4; d++) {
      nbr[i * 4 + d] = atLocal(lx[i]! + DX[d]!, ly[i]! + DY[d]!);
    }
  }
  const boxes0 = room.boxes.map((b) => loc.get(b)!).sort((a, b) => a - b);
  const goalsLocal = room.goals.map((g) => loc.get(g)!).sort((a, b) => a - b);
  const m = boxes0.length;
  const goalSet = new Set(goalsLocal);

  // Wall-only BFS distances from each goal over room cells.
  const dist = new Float64Array(m * n).fill(Infinity);
  for (let g = 0; g < m; g++) {
    const start = goalsLocal[g]!;
    const q = [start];
    dist[g * n + start] = 0;
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi]!;
      for (let d = 0; d < 4; d++) {
        const nb = nbr[c * 4 + d]!;
        if (nb < 0 || nb >= n || dist[g * n + nb] !== Infinity) continue;
        dist[g * n + nb] = dist[g * n + c]! + 1;
        q.push(nb);
      }
    }
  }

  // Statically dead squares: a box cell is alive when a goal is reachable
  // from it by pulls (reverse BFS from the goals; a pull needs the player
  // to stand on the far side, on a room cell or the entry).
  const alive = new Uint8Array(n);
  const work: number[] = [];
  for (const g of goalsLocal) {
    alive[g] = 1;
    work.push(g);
  }
  while (work.length) {
    const y = work.pop()!;
    for (let d = 0; d < 4; d++) {
      const od = OPP[d]!;
      const x = nbr[y * 4 + od]!;
      if (x < 0 || x >= n || alive[x]) continue;
      const s = nbr[x * 4 + od]!;
      if (s < 0) continue;
      alive[x] = 1;
      work.push(x);
    }
  }
  const dead = new Uint8Array(n);
  for (let i = 0; i < n; i++) if (!alive[i]) dead[i] = 1;

  // Minimum-assignment heuristic over goal permutations.
  const perms: number[][] = [];
  const permRec = (cur: number[], used: boolean[]): void => {
    if (cur.length === m) {
      perms.push(cur.slice());
      return;
    }
    for (let g = 0; g < m; g++) {
      if (used[g]) continue;
      used[g] = true;
      cur.push(g);
      permRec(cur, used);
      cur.pop();
      used[g] = false;
    }
  };
  permRec([], new Array<boolean>(m).fill(false));
  const hCache = new Map<number | string, number>();
  const encodeBoxes = (bs: number[]): number | string => {
    if (bs.length <= 5) {
      let code = 0;
      let mult = 1;
      for (let i = 0; i < bs.length; i++) {
        code += bs[i]! * mult;
        mult *= 256;
      }
      return code;
    }
    return bs.join(',');
  };
  const decodeBoxes = (code: number | string): number[] => {
    if (typeof code === 'string') return code.split(',').map(Number);
    const bs: number[] = [];
    let c = code;
    for (let i = 0; i < m; i++) {
      bs.push(c % 256);
      c = Math.floor(c / 256);
    }
    return bs;
  };
  const stateKey = (bs: number[], rep: number): number | string => {
    const code = encodeBoxes(bs);
    return typeof code === 'number' ? code * 256 + rep : code + ':' + rep;
  };
  const heuristic = (bs: number[]): number => {
    const code = encodeBoxes(bs);
    const cached = hCache.get(code);
    if (cached !== undefined) return cached;
    let best = Infinity;
    for (const p of perms) {
      let sum = 0;
      for (let i = 0; i < m; i++) {
        const d = dist[p[i]! * n + bs[i]!]!;
        if (d === Infinity) {
          sum = Infinity;
          break;
        }
        sum += d;
      }
      if (sum < best) best = sum;
    }
    hCache.set(code, best);
    return best;
  };

  // Flood fill of the player's reachable region; returns its lowest cell.
  // The rep flood uses its own mark array: successor generation reads the
  // expansion region while computing each successor's canonical region.
  const regionMark = new Int32Array(N);
  const repMark = new Int32Array(N);
  const floodInto = (
    mark: Int32Array,
    stampRef: { v: number },
    start: number,
    boxMark: Uint8Array,
  ): number => {
    stampRef.v++;
    const s = stampRef.v;
    const q = [start];
    mark[start] = s;
    let min = start;
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi]!;
      for (let d = 0; d < 4; d++) {
        const nb = nbr[c * 4 + d]!;
        if (nb < 0 || mark[nb] === s || boxMark[nb]) continue;
        mark[nb] = s;
        if (nb < min) min = nb;
        q.push(nb);
      }
    }
    return min;
  };
  const regionStampRef = { v: 0 };
  const repStampRef = { v: 0 };
  const floodMin = (start: number, boxMark: Uint8Array): number =>
    floodInto(regionMark, regionStampRef, start, boxMark);
  const floodMinRep = (start: number, boxMark: Uint8Array): number =>
    floodInto(repMark, repStampRef, start, boxMark);

  const boxMarkOf = (bs: number[]): Uint8Array => {
    const mark = new Uint8Array(N);
    for (const b of bs) mark[b] = 1;
    return mark;
  };

  const isGoalBoxes = (bs: number[]): boolean => {
    for (let i = 0; i < m; i++) if (bs[i] !== goalsLocal[i]) return false;
    return true;
  };

  // Freeze deadlock: iteratively, a box is frozen when it is blocked on
  // both sides of an axis by walls or frozen boxes. A frozen box off a
  // goal means the state is dead.
  const frozenDead = (bs: number[]): boolean => {
    const boxSet = new Set(bs);
    const frozen = new Uint8Array(n);
    let changed = true;
    while (changed) {
      changed = false;
      for (const b of bs) {
        if (frozen[b]) continue;
        const blocked = (j: number): boolean =>
          j === -1 || (j < n && frozen[j] === 1);
        const l = nbr[b * 4 + 2]!;
        const r = nbr[b * 4 + 3]!;
        const u = nbr[b * 4 + 0]!;
        const d = nbr[b * 4 + 1]!;
        // A box is frozen when it can move on neither axis: moving left
        // needs the left cell free and the right cell standable, and vice
        // versa, so one blocked side already closes the whole axis.
        if ((blocked(l) || blocked(r)) && (blocked(u) || blocked(d))) {
          frozen[b] = 1;
          changed = true;
        }
      }
    }
    for (const b of bs) if (frozen[b] && !goalSet.has(b)) return true;
    return false;
  };

  // 2x2 block of wall/box cells holding a box off a goal, around cell t.
  const twoByTwoDead = (bs: number[], t: number, boxSet: Set<number>): boolean => {
    const tx = lx[t]!;
    const ty = ly[t]!;
    const cellKind = (gx: number, gy: number): number => {
      const j = atLocal(gx, gy);
      if (j < 0) return 2; // wall
      if (j < n && boxSet.has(j)) return 1; // box
      return 0; // free floor (room cell or entry)
    };
    for (const [ox, oy] of [
      [-1, -1],
      [0, -1],
      [-1, 0],
      [0, 0],
    ]) {
      let allSolid = true;
      let hasOffGoalBox = false;
      for (let a = 0; a < 2; a++) {
        for (let b = 0; b < 2; b++) {
          const gx = tx + ox + a;
          const gy = ty + oy + b;
          const k = cellKind(gx, gy);
          if (k === 0) {
            allSolid = false;
            break;
          }
          if (k === 1) {
            const j = atLocal(gx, gy)!;
            if (!goalSet.has(j)) hasOffGoalBox = true;
          }
        }
        if (!allSolid) break;
      }
      if (allSolid && hasOffGoalBox) return true;
    }
    return false;
  };

  const stateDead = (bs: number[], moved: number): boolean => {
    for (const b of bs) if (dead[b]) return true;
    if (frozenDead(bs)) return true;
    if (twoByTwoDead(bs, moved, new Set(bs))) return true;
    return false;
  };

  // A* node storage (parallel arrays).
  const nCode: (number | string)[] = [];
  const nPlayer: number[] = [];
  const nParent: number[] = [];
  const nPushBox: number[] = [];
  const nPushDir: number[] = [];
  const nG: number[] = [];
  const nF: number[] = [];
  const nSeq: number[] = [];
  const nKey: (number | string)[] = [];
  let seq = 0;
  const addNode = (
    code: number | string,
    player: number,
    parent: number,
    pushBox: number,
    pushDir: number,
    g: number,
    f: number,
    key: number | string,
  ): number => {
    const idx = nCode.length;
    nCode.push(code);
    nPlayer.push(player);
    nParent.push(parent);
    nPushBox.push(pushBox);
    nPushDir.push(pushDir);
    nG.push(g);
    nF.push(f);
    nSeq.push(seq++);
    nKey.push(key);
    return idx;
  };
  // Binary heap of node indices on (f, -g, seq).
  const heap: number[] = [];
  const heapLess = (a: number, b: number): boolean => {
    if (nF[a] !== nF[b]) return nF[a]! < nF[b]!;
    if (nG[a] !== nG[b]) return nG[a]! > nG[b]!;
    return nSeq[a]! < nSeq[b]!;
  };
  const heapPush = (idx: number): void => {
    let i = heap.length;
    heap.push(idx);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!heapLess(heap[i]!, heap[p]!)) break;
      const tmp = heap[i]!;
      heap[i] = heap[p]!;
      heap[p] = tmp;
      i = p;
    }
  };
  const heapPop = (): number => {
    const top = heap[0]!;
    const last = heap.pop()!;
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && heapLess(heap[c + 1]!, heap[c]!)) c++;
        if (!heapLess(heap[c]!, heap[i]!)) break;
        const tmp = heap[i]!;
        heap[i] = heap[c]!;
        heap[c] = tmp;
        i = c;
      }
    }
    return top;
  };

  const best = new Map<number | string, number>(); // state key -> best g
  const rootMark = boxMarkOf(boxes0);
  if (boxes0.some((b) => stateDead(boxes0, b))) {
    dbg(`room door=${room.door} FAIL root-dead dead=[${boxes0.filter((b) => dead[b]).join(',')}]`);
    return null;
  }
  const h0 = heuristic(boxes0);
  if (h0 === Infinity) {
    dbg(`room door=${room.door} FAIL h0-inf`);
    return null;
  }
  const rootRep = floodMin(entryLocal, rootMark);
  const rootKey = stateKey(boxes0, rootRep);
  const root = addNode(encodeBoxes(boxes0), entryLocal, -1, -1, -1, 0, h0, rootKey);
  best.set(rootKey, 0);
  heapPush(root);

  let expansions = 0;
  let goalIdx = -1;
  while (heap.length > 0) {
    const idx = heapPop();
    if (best.get(nKey[idx]!) !== nG[idx]) continue; // stale entry
    const boxes = decodeBoxes(nCode[idx]!);
    const g = nG[idx]!;
    if (isGoalBoxes(boxes)) {
      if (!exitRequired) {
        goalIdx = idx;
        break;
      }
      // Exit required: the player must still be able to walk to the entry.
      const mark = boxMarkOf(boxes);
      floodMin(nPlayer[idx]!, mark);
      if (regionMark[entryLocal] === regionStampRef.v) {
        goalIdx = idx;
        break;
      }
      // Otherwise keep searching for an exiting goal state.
      continue;
    }
    expansions++;
    totalExpansions++;
    if (expansions > ROOM_EXPANSION_CAP || totalExpansions > TOTAL_EXPANSION_CAP) {
      dbg(`room door=${room.door} FAIL budget expansions=${expansions}`);
      return null;
    }
    const mark = boxMarkOf(boxes);
    floodMin(nPlayer[idx]!, mark);
    const myStamp = regionStampRef.v;
    for (let bi = 0; bi < m; bi++) {
      const b = boxes[bi]!;
      for (let d = 0; d < 4; d++) {
        const t = nbr[b * 4 + d]!;
        if (t < 0 || t >= n || mark[t]) continue;
        const from = nbr[b * 4 + OPP[d]!]!;
        if (from < 0 || regionMark[from] !== myStamp) continue;
        const nb2 = boxes.slice();
        nb2[bi] = t;
        nb2.sort((a, b2) => a - b2);
        if (stateDead(nb2, t)) continue;
        const h = heuristic(nb2);
        if (h === Infinity) continue;
        const ng = g + 1;
        // Canonical player region after the push (player stands on b).
        mark[b] = 0;
        mark[t] = 1;
        const rep = floodMinRep(b, mark);
        mark[b] = 1;
        mark[t] = 0;
        const code = encodeBoxes(nb2);
        const key = stateKey(nb2, rep);
        const prev = best.get(key);
        if (prev !== undefined && prev <= ng) continue;
        best.set(key, ng);
        const node = addNode(code, b, idx, b, d, ng, ng + h, key);
        heapPush(node);
      }
    }
  }
  if (goalIdx < 0) {
    dbg(`room door=${room.door} FAIL heap-exhausted expansions=${expansions} nodes=${nCode.length}`);
    return null;
  }

  // Reconstruct the move letters.
  const finalBoxes = decodeBoxes(nCode[goalIdx]!);
  const parts: string[] = [];
  let cur = goalIdx;
  while (nParent[cur] !== -1) {
    const p = nParent[cur]!;
    const pBoxes = decodeBoxes(nCode[p]!);
    const pMark = boxMarkOf(pBoxes);
    const from = nbr[nPushBox[cur]! * 4 + OPP[nPushDir[cur]!]!]!;
    const walk = bfsPath(nbr, N, nPlayer[p]!, from, pMark);
    if (walk === null) return null;
    parts.push(walk + LETTER[nPushDir[cur]!]);
    cur = p;
  }
  parts.reverse();
  let moves = parts.join('');
  // Exit walk, when the player can reach the entry from the final position.
  const finalMark = boxMarkOf(finalBoxes);
  const exitWalk = bfsPath(nbr, N, nPlayer[goalIdx]!, entryLocal, finalMark);
  let exited = false;
  if (exitWalk !== null) {
    moves += exitWalk;
    exited = true;
  }
  dbg(`room door=${room.door} pushes=${nG[goalIdx]} expansions=${expansions} exited=${exited}`);
  return { moves, pushes: nG[goalIdx]!, exited, expansions };
}

/** Solve one whole level; returns the move string ('' when unsolved). */
function solveLevel(text: string): string {
  const level = parseLevel(text);
  const { w, h, wall, boxes, goals, player } = level;
  let rooms = decompose(level);
  if (rooms === null) {
    // Unexpected shape: fall back to solving the whole level as one room.
    const cells: number[] = [];
    for (let i = 0; i < w * h; i++) if (!wall[i]) cells.push(i);
    rooms = [{ cells, door: player, entry: player, boxes, goals }];
  }
  // Solve every room push-optimally, without an exit requirement first.
  const solved: (RoomSolution | null)[] = rooms.map((r) => solveRoom(level, r, false));
  for (let i = 0; i < rooms.length; i++) {
    if (solved[i] === null) return '';
  }
  // Rooms whose optimal solution leaves the player unable to exit must go
  // last; if more than one is trapped, re-solve all but the last with the
  // exit requirement (paying extra pushes if that is what it takes).
  const trapped: number[] = [];
  for (let i = 0; i < rooms.length; i++) {
    if (!solved[i]!.exited) trapped.push(i);
  }
  const order: number[] = [];
  const good: number[] = [];
  for (let i = 0; i < rooms.length; i++) if (!trapped.includes(i)) good.push(i);
  if (trapped.length > 1) {
    for (let k = 0; k < trapped.length - 1; k++) {
      const ri = trapped[k]!;
      const retry = solveRoom(level, rooms[ri]!, true);
      if (retry !== null && retry.exited) {
        solved[ri] = retry;
        good.push(ri);
      }
    }
  }
  const last = trapped.filter((ri) => !good.includes(ri));
  order.push(...good, ...last);

  // Global neighbour table over floor cells.
  const gNbr = new Int32Array(w * h * 4).fill(-1);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (wall[i]) continue;
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d]!;
        const ny = y + DY[d]!;
        if (nx < 0 || ny < 0 || nx >= w || ny >= h || wall[ny * w + nx]) continue;
        gNbr[i * 4 + d] = ny * w + nx;
      }
    }
  }
  const gMark = new Uint8Array(w * h);
  for (const b of boxes) gMark[b] = 1;
  let playerPos = player;
  let moves = '';
  for (const ri of order) {
    const room = rooms[ri]!;
    const sol = solved[ri]!;
    const walk = bfsPath(gNbr, w * h, playerPos, room.entry, gMark);
    if (walk === null) return '';
    moves += walk;
    // Update the global box marks: this room's boxes move to their goals.
    for (const b of room.boxes) gMark[b] = 0;
    for (const g of room.goals) gMark[g] = 1;
    moves += sol.moves;
    playerPos = room.entry; // the room solution ends on its entry, or inside
    if (!sol.exited) playerPos = -1; // trapped: no further room is reachable
    if (playerPos === -1 && ri !== order[order.length - 1]) return '';
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
dbg(`total expansions: ${totalExpansions}`);
