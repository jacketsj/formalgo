import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.CodeAlgorithm

/-!
# Dijkstra's algorithm with a Fibonacci heap

LLM-generated; not checked by a human.

Vertex `u` has id `u + 1`; `0` means none. Node `0` is a root above all roots of the heap, so the
root list is its child array. Arrays `k = 0, …, 9` sit at `H + k R`, with `H = A + ℓ` and
`R = n + D + 3`; register `breg k` holds the base.

| `k` | array | `k` | array                       |
|-----|-------|-----|-----------------------------|
| 0   | key   | 5   | position in parent's array  |
| 1   | status (0 new, 1 in heap, 2 done) | 6 | degree table |
| 2   | parent| 7   | first half-edge             |
| 3   | degree| 8   | address of the child array  |
| 4   | mark  | 9   | output                      |

Half-edges are triples `[next, target, weight]` from `H + 10 R`; their address is their name.
Child arrays follow: node `0` has `n + 1` slots, the others `D + 1`. Register `27` holds `n`,
`28` holds `D`, `29` the minimum root; `2`, `6` and `7` are scratch for the macros.
-/

namespace Formalgo.Algorithms.ShortestPaths.Prog

open LLMUnchecked Cmd

/-- No operation. -/
def nop : Cmd := const 2 0

/-- The register holding the base of array `k`. -/
def breg (k : ℕ) : ℕ := if k = 9 then 10 else 18 + k

/-- `M[d] := A_k[M[i]]`. -/
def rd (d k i : ℕ) : Cmd := seq (add 2 (breg k) i) (load d 2)

/-- `A_k[M[i]] := M[s]`. -/
def wr (k i s : ℕ) : Cmd := seq (add 2 (breg k) i) (store 2 s)

/-- `M[2] :=` the address of child `M[j]` of `M[p]`. -/
def chAt (p j : ℕ) : Cmd := seq (add 2 26 p) (seq (load 2 2) (add 2 2 j))

/-- `M[d] :=` child `M[j]` of `M[p]`. -/
def chRd (d p j : ℕ) : Cmd := seq (chAt p j) (load d 2)

/-- Child `M[j]` of `M[p]` `:= M[s]`. -/
def chWr (p j s : ℕ) : Cmd := seq (chAt p j) (store 2 s)

/-! ### Heap macros -/

/-- Remove `M[v]` from the child array of `M[p]`, moving its last entry into the gap. -/
def detach (v p : ℕ) : Cmd :=
  seqs [rd 6 3 p, sub 6 6 3, wr 3 p 6, chRd 7 p 6, rd 6 5 v, wr 5 7 6, chWr p 6 7]

/-- Append `M[v]` to the child array of `M[p]`, and make `M[p]` its parent. -/
def attach (v p : ℕ) : Cmd := seqs [rd 6 3 p, add 7 6 3, wr 3 p 7, wr 5 v 6, chWr p 6 v, wr 2 v p]

/-- Make `M[v]` the minimum root if it is smaller, or if there is none. -/
def updMin (v : ℕ) : Cmd :=
  ite 29 8 (copy 29 v) (seqs [rd 6 0 v, rd 7 0 29, less 6 6 7, ite 6 3 (copy 29 v) nop])

/-- Cut `M[v]` from its parent `M[p]` to the roots, unmarked. -/
def cut (v p : ℕ) : Cmd := seqs [detach v p, attach v 8, wr 4 v 8]

/-- One link in consolidation: link roots `x` (`14`) and `y` (`12`) of degree `dx` (`15`). -/
def linkBody : Cmd := seqs [wr 6 15 8, rd 11 0 12, rd 31 0 14, less 11 11 31,
  ite 11 3 (seqs [copy 11 14, copy 14 12, copy 12 11]) nop,
  attach 12 14, wr 4 12 8, add 15 15 3, rd 12 6 15, less 17 8 12]

/-- Pop the last root `x`, link it with roots of equal degree, and put it in the table. -/
def popBody : Cmd := seqs [load 11 21, sub 11 11 3, store 21 11, chRd 14 8 11, rd 15 3 14,
  rd 12 6 15, less 17 8 12, loop 17 3 linkBody, wr 6 15 14, load 11 21, less 13 8 11]

/-- Move the last child of `z` (`30`) to the roots. -/
def moveBody : Cmd := seqs [rd 11 3 30, sub 11 11 3, wr 3 30 11, chRd 14 30 11, attach 14 8,
  less 13 8 11]

/-- Move the table entry `d` (`11`) to the roots. -/
def tableBody : Cmd := seqs [rd 14 6 11, ite 14 8 nop (seqs [wr 6 11 8, attach 14 8, updMin 14]),
  add 11 11 3, less 13 28 11]

/-- Remove the minimum root into `30`, and consolidate. -/
def extractMin : Cmd := seqs [copy 30 29, detach 30 8, rd 12 3 30, less 13 8 12,
  loop 13 3 moveBody, load 11 21, less 13 8 11, loop 13 3 popBody,
  const 29 0, const 11 0, less 13 28 11, loop 13 8 tableBody]

/-- The cascade condition: `3` if `p` (`15`) has a parent and is marked. -/
def cascCond : Cmd := seqs [rd 17 2 15, less 17 8 17, rd 11 4 15, add 17 17 11, add 17 17 3]

/-- Cut a marked `p` (`15`) and move to its parent. -/
def cascBody : Cmd := seqs [rd 12 2 15, cut 15 12, copy 15 12, cascCond]

/-- Make `v` (`13`) the minimum if its key `nk` (`14`) is smaller. -/
def updMinKey : Cmd := seqs [rd 17 0 29, less 17 14 17, ite 17 3 (copy 29 13) nop]

/-- Decrease the key of `v` (`13`) to `nk` (`14`); its parent goes in `15`. -/
def decKey : Cmd := seqs [wr 0 13 14, rd 15 2 13,
  ite 15 8 updMinKey (seqs [rd 17 0 15, less 17 14 17,
    ite 17 3 (seqs [cut 13 15, cascCond, loop 17 16 cascBody,
      rd 17 2 15, ite 17 8 nop (wr 4 15 3), updMinKey]) nop])]

/-- Relax the half-edge `h` (`31`) from `u` (`30`). -/
def relaxBody : Cmd := seqs [add 2 31 3, load 13 2, add 2 2 3, load 14 2,
  rd 15 0 30, add 14 15 14, rd 15 1 13,
  ite 15 8 (seqs [wr 0 13 14, wr 1 13 3, attach 13 8, updMin 13])
    (ite 15 3 (seqs [rd 15 0 13, less 15 14 15, ite 15 3 decKey nop]) nop),
  load 31 31, less 11 8 31]

/-- Settle the minimum and relax its edges. -/
def mainBody : Cmd := seqs [extractMin, add 6 3 3, wr 1 30 6,
  rd 31 7 30, less 11 8 31, loop 11 3 relaxBody, load 11 21, less 12 8 11]

/-! ### Setting up -/

/-- `L` (`13`): double `p` (`12`) while `p ≤ n`. -/
def logBody : Cmd := seqs [add 12 12 12, add 13 13 3, less 14 27 12]

/-- `n`, `D`, and the bases; `E` in `11`, the half-edges' base in `13`. -/
def setup : Cmd := seqs [load 27 9, add 2 9 3, load 11 2,
  const 12 1, const 13 0, less 14 27 12, loop 14 8 logBody, add 28 13 13,
  add 12 27 28, add 12 12 16, add 18 9 4,
  add 19 18 12, add 20 19 12, add 21 20 12, add 22 21 12, add 23 22 12, add 24 23 12,
  add 25 24 12, add 26 25 12, add 10 26 12, add 13 10 12]

/-- Add the two half-edges of the edge at `30`, weight at `31`, from `13`. -/
def buildBody : Cmd := seqs [load 11 30, add 11 11 3, add 2 30 3, load 12 2, add 12 12 3,
  load 14 31,
  rd 15 7 11, store 13 15, add 2 13 3, store 2 12, add 2 2 3, store 2 14, wr 7 11 13,
  add 13 13 16,
  rd 15 7 12, store 13 15, add 2 13 3, store 2 11, add 2 2 3, store 2 14, wr 7 12 13,
  add 13 13 16,
  add 30 30 3, add 30 30 3, add 31 31 3, less 15 31 17]

/-- The half-edges; then `13` is the base of the child arrays and `17` the source's address. -/
def build : Cmd := seqs [add 30 9 3, add 30 30 3, add 31 30 11, add 31 31 11, add 31 31 3,
  add 17 31 11, less 15 31 17, loop 15 3 buildBody]

/-- Set the address of the child array of `v` (`30`) to `c` (`15`). -/
def cbBody : Cmd := seqs [wr 8 30 15, add 15 15 14, add 30 30 3, less 31 27 30]

/-- The addresses of the child arrays. -/
def cbInit : Cmd := seqs [store 26 13, add 15 13 27, add 15 15 3, add 14 28 3, const 30 1,
  less 31 27 30, loop 31 8 cbBody]

/-- Put the source in the heap, if it is a vertex. -/
def source : Cmd := seqs [load 11 17, const 29 0, less 12 11 27,
  ite 12 3 (seqs [add 11 11 3, wr 1 11 3, attach 11 8, updMin 11]) nop]

/-- Write the key of vertex `v` (`11`) if it is settled, or `0`. -/
def outBody : Cmd := seqs [rd 13 1 11, add 6 3 3,
  ite 13 6 (seqs [rd 14 0 11]) (const 14 0), wr 9 11 14, add 11 11 3, less 12 27 11]

/-- Write the output code: `n`, then the distances. -/
def output : Cmd := seqs [store 10 27, const 11 1, less 12 27 11, loop 12 8 outBody, add 17 27 3]

/-- Dijkstra's algorithm on the code at `A`. -/
def core : Cmd := seqs [setup, build, cbInit, source, load 11 21, less 12 8 11,
  loop 12 3 mainBody, output]

end Formalgo.Algorithms.ShortestPaths.Prog
