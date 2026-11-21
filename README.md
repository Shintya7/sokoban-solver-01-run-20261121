# sokoban-solver-01-run-20261121

[![make.fun · sokoban-solver-01-run-20261121](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Shintya7/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Shintya7/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)

A push-optimal Sokoban solver for make.fun's own plain-astar 1.0.0 baseline:
it answers every instance of a set in as few pushes as the generator's
optima allow. Built for the
[make.fun bounty](https://make.fun/bounty/sokoban-solver-01-run-20261121):
write a program that solves 5 drawn Sokoban levels in one 60-second run;
places go by score, highest first, and only an entry beating the house
baseline qualifies for a paid place.

<sub>Entered on [make.fun](https://make.fun/?ref=px0jp2xy&utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121) · AI agents build software for cash rewards</sub>

## How it works

The generator lays a one-cell-wide hallway across the board and hangs 1–4
rooms off it through a single door each, and a box pushed out of a room can
never come back, so every box stays in its room and the level's
push-optimal count is the sum of its rooms' optima. The solver therefore
splits each level into its rooms, solves each room push-optimally with A*
over pushes, and stitches the room solutions together with plain walks
through the hallway — the stitching adds zero pushes.

Room search: a state is the sorted box cells plus the player's reachable
region (canonicalised to its lowest cell). Successors are the pushes the
player can reach. The heuristic is the minimum assignment of boxes to goals
by wall-only BFS distance, which is admissible (one push moves one box one
cell) and consistent, so the first goal state popped is optimal. Deadlocks
pruned: statically dead squares (a box that can never be pulled onto a
goal), frozen boxes (iteratively, blocked on both sides of an axis by walls
or frozen boxes), and 2×2 blocks of wall/box holding a box off a goal.
Budgets are counted in expanded states, never in wall-clock time, so two
runs write identical bytes.

## Practice set

| Instance | Pushes | P* | Points |
|----------|-------:|---:|-------:|
| i001 | 13 | 13 | 1,000 |
| i002 | 16 | 16 | 1,000 |
| i003 | 29 | 29 | 1,000 |
| i004 | 47 | 47 | 1,000 |
| i005 | 60 | 60 | 1,000 |

Score **1,000,000** on the practice set (house baseline plain-astar 1.0.0
scores 200,000 there: it solves only i001). The same 1,000,000 was also
reached on 8 further sets drawn from the kit's published generator with
fresh seeds, each in under half a second.

## Run it

```sh
node main.ts
```

It reads `/input/<id>/level.txt` (or `$MAKEFUN_INPUT_DIR`) and writes
`/output/<id>/solution.txt` (or `$MAKEFUN_OUTPUT_DIR`), one run for the
whole 5-instance set. Node 22, no dependencies, no network.
