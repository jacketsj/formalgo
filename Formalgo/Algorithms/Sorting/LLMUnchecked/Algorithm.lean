import Formalgo.LLMUnchecked.Machine.ListAlgorithm

/-!
# Merge sort

LLM-generated; not checked by a human.

Bottom-up merge sort of the array at `A` (register `9`), with scratch array `A + n` (register
`10`).

| register | content         | register | content                 |
|----------|-----------------|----------|-------------------------|
| 18       | source array    | 25       | end of left run         |
| 19       | destination     | 26       | `q`, read in right run  |
| 20       | run width `w`   | 27       | end of right run        |
| 21       | `i`, start      | 28       | `k`, write position     |
| 22       | `mid`           | 29       | end of output           |
| 23       | `hi`            | 30, 31   | `M[p]`, `M[q]`          |
| 24       | `p`, read left  | 11–15    | conditions, temporaries |
-/

namespace Formalgo.Algorithms.Sorting.MergeSort

open LLMUnchecked Cmd

/-- No operation. -/
def nop : Cmd := const 2 0

/-- Take the left element: `M[k] := M[p]`, `p += 1`, `k += 1`. -/
def takeLeft : Cmd := seqs [load 30 24, store 28 30, add 24 24 3, add 28 28 3]

/-- Take the right element: `M[k] := M[q]`, `q += 1`, `k += 1`. -/
def takeRight : Cmd := seqs [load 31 26, store 28 31, add 26 26 3, add 28 28 3]

/-- One merge step. -/
def mergeBody : Cmd := seqs [less 13 24 25,
  ite 13 3
    (seqs [less 14 26 27,
      ite 14 3 (seqs [load 30 24, load 31 26, less 15 31 30, ite 15 3 takeRight takeLeft])
        takeLeft])
    takeRight,
  less 12 28 29]

/-- Merge the runs at `i`, then move to the next pair. -/
def pairBody : Cmd := seqs [add 22 21 20, less 12 22 4, ite 12 3 nop (copy 22 4),
  add 23 22 20, less 12 23 4, ite 12 3 nop (copy 23 4),
  add 24 18 21, add 25 18 22, copy 26 25, add 27 18 23, add 28 19 21, add 29 19 23,
  less 12 28 29, loop 12 3 mergeBody, copy 21 23, less 11 21 4]

/-- One pass: merge all pairs of runs, swap the arrays, and double the width. -/
def passBody : Cmd := seqs [const 21 0, less 11 21 4, loop 11 3 pairBody,
  copy 13 18, copy 18 19, copy 19 13, add 20 20 20, less 11 20 4]

/-- Copy the source array back to `A`. -/
def copyBody : Cmd := seqs [add 13 18 21, load 30 13, add 14 9 21, store 14 30, add 21 21 3,
  less 11 21 4]

/-- Merge sort of the array at `A`. -/
def core : Cmd := seqs [copy 18 9, copy 19 10, const 20 1, less 11 20 4, loop 11 3 passBody,
  ite 18 9 nop (seqs [const 21 0, less 11 21 4, loop 11 3 copyBody])]

end Formalgo.Algorithms.Sorting.MergeSort
