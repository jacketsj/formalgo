import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.Refine

/-!
# A model of the program

LLM-generated; not checked by a human.

The program's arrays as functions, and each part of the program as a function on them, step for
step. Ghost fields record link times and heights for the degree bound, and the steps taken.

Keys and weights have a type `R`: `ℕ` for the word RAM (`St`, `Ctx`), the reals for the real RAM.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Function

/-- The data fixed by the input: `n`, `D`, the fuel of the loops, and the adjacency lists, with
weights in `R`. -/
structure CtxW (R : Type*) where
  /-- The number of vertices. -/
  n : ℕ
  /-- The capacity of the degree table, less one. -/
  D : ℕ
  /-- Fuel for the loops. -/
  F : ℕ
  /-- The `(target, weight)` pairs at each vertex. -/
  adj : ℕ → List (ℕ × R)

/-- The data fixed by the input, with weights in `ℕ`. -/
abbrev Ctx := CtxW ℕ

/-- The program's state, with keys in `R`. -/
@[ext] structure StW (R : Type*) where
  key : ℕ → R
  stat : ℕ → ℕ
  par : ℕ → ℕ
  deg : ℕ → ℕ
  mark : ℕ → ℕ
  pos : ℕ → ℕ
  tbl : ℕ → ℕ
  /-- `ch v j` is child `j` of `v`. -/
  ch : ℕ → ℕ → ℕ
  /-- The minimum root, or `0`. -/
  hmin : ℕ
  /-- Ghost: when each node was linked. -/
  lt : ℕ → ℕ
  /-- Ghost: heights, above those of children. -/
  ht : ℕ → ℕ
  /-- Ghost: the number of links so far. -/
  clock : ℕ
  /-- Ghost: the steps taken. -/
  time : ℕ

/-- The program's state, with keys in `ℕ`. -/
abbrev St := StW ℕ

namespace St

variable {R : Type*}

/-- Pay for `c` steps. -/
def tick (c : ℕ) (s : StW R) : StW R := { s with time := s.time + c }

/-- Remove `v` from the child array of `p`, moving the last child into the gap. -/
def detach (v p : ℕ) (s : StW R) : StW R :=
  { s with deg := update s.deg p (s.deg p - 1),
           pos := update s.pos (s.ch p (s.deg p - 1)) (s.pos v),
           ch := update s.ch p (update (s.ch p) (s.pos v) (s.ch p (s.deg p - 1))) }

/-- Append `v` to the child array of `p`, with parent `p`. -/
def attach (v p : ℕ) (s : StW R) : StW R :=
  { s with deg := update s.deg p (s.deg p + 1), pos := update s.pos v (s.deg p),
           ch := update s.ch p (update (s.ch p) (s.deg p) v), par := update s.par v p }

/-- Make `v` the minimum root if it is smaller, or if there is none. -/
def updMin [LT R] [DecidableLT R] (v : ℕ) (s : StW R) : StW R :=
  if s.hmin = 0 then { s with hmin := v }
  else if s.key v < s.key s.hmin then { s with hmin := v } else s

/-- Cut `v` from `p` to the roots, unmarked. -/
def cut (v p : ℕ) (s : StW R) : StW R :=
  let s := attach v 0 (detach v p s)
  { s with mark := update s.mark v 0 }

/-- Set a key. -/
def setKey (v : ℕ) (k : R) (s : StW R) : StW R := { s with key := update s.key v k }

/-- Set a status. -/
def setStat (v k : ℕ) (s : StW R) : StW R := { s with stat := update s.stat v k }

/-- Set a table entry. -/
def setTbl (d x : ℕ) (s : StW R) : StW R := { s with tbl := update s.tbl d x }

/-- Set a mark. -/
def setMark (v k : ℕ) (s : StW R) : StW R := { s with mark := update s.mark v k }

/-- Link `y` below `x`, unmarked, with ghost link time and height. -/
def link (y x : ℕ) (s : StW R) : StW R :=
  let s := attach y x s
  { s with mark := update s.mark y 0, lt := update s.lt y s.clock, clock := s.clock + 1,
           ht := update s.ht x (max (s.ht x) (s.ht y + 1)) }

end St

open St

variable {R : Type*} (C : CtxW R)

/-! ### Consolidation -/

/-- Link the root `x` of degree `dx` with the table entry `y` of the same degree. -/
def linkStep [LT R] [DecidableLT R] (a : StW R × ℕ × ℕ) : StW R × ℕ × ℕ :=
  let s := a.1; let x := a.2.1; let dx := a.2.2
  let y := s.tbl dx
  let s := setTbl dx 0 s
  let x' := if s.key y < s.key x then y else x
  let y' := if s.key y < s.key x then x else y
  (tick 40 (link y' x' s), x', dx + 1)

/-- While the table has an entry at the degree. -/
def linkCond (a : StW R × ℕ × ℕ) : Prop := a.1.tbl a.2.2 ≠ 0

instance : DecidablePred (linkCond (R := R)) := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Pop the last root, link it with roots of equal degree, and put it in the table. -/
def popStep [LT R] [DecidableLT R] (s : StW R) : StW R :=
  let s := { s with deg := update s.deg 0 (s.deg 0 - 1) }
  let x := s.ch 0 (s.deg 0)
  let a := whileF linkCond linkStep C.F (s, x, s.deg x)
  tick 25 (setTbl a.2.2 a.2.1 a.1)

/-- While there are roots. -/
def rootsCond (s : StW R) : Prop := s.deg 0 ≠ 0

instance : DecidablePred (rootsCond (R := R)) := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Move the last child of `z` to the roots. -/
def moveStep (a : StW R × ℕ) : StW R × ℕ :=
  let s := { a.1 with deg := update a.1.deg a.2 (a.1.deg a.2 - 1) }
  (tick 30 (attach (s.ch a.2 (s.deg a.2)) 0 s), a.2)

/-- While `z` has children. -/
def moveCond (a : StW R × ℕ) : Prop := a.1.deg a.2 ≠ 0

instance : DecidablePred (moveCond (R := R)) := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Move table entry `d` to the roots. -/
def tabStep [LT R] [DecidableLT R] (a : StW R × ℕ) : StW R × ℕ :=
  let s := a.1; let d := a.2
  let x := s.tbl d
  (tick 40 (if x = 0 then s else updMin x (attach x 0 (setTbl d 0 s))), d + 1)

/-- While `d ≤ D`. -/
def tabCond (a : StW R × ℕ) : Prop := a.2 ≤ C.D

instance : DecidablePred (tabCond C (R := R)) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Remove the minimum root and consolidate. -/
def extract [LT R] [DecidableLT R] (s : StW R) : StW R :=
  let z := s.hmin
  let s := detach z 0 s
  let s := (whileF moveCond moveStep C.F (s, z)).1
  let s := whileF rootsCond (popStep C) C.F s
  let s := { s with hmin := 0 }
  tick 40 (whileF (tabCond C) tabStep C.F (s, 0)).1

/-! ### Decreasing a key -/

/-- Cut a marked `p`, and move to its parent. -/
def cascStep (a : StW R × ℕ) : StW R × ℕ := (tick 50 (cut a.2 (a.1.par a.2) a.1), a.1.par a.2)

/-- While `p` has a parent and is marked. -/
def cascCond (a : StW R × ℕ) : Prop := a.1.par a.2 ≠ 0 ∧ a.1.mark a.2 = 1

instance : DecidablePred (cascCond (R := R)) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Make `v` the minimum if its key `nk` is smaller. -/
def updMinKey [LT R] [DecidableLT R] (v : ℕ) (nk : R) (s : StW R) : StW R :=
  if nk < s.key s.hmin then { s with hmin := v } else s

/-- Decrease the key of `v` to `nk`. -/
def decKey [LT R] [DecidableLT R] (v : ℕ) (nk : R) (s : StW R) : StW R :=
  let s := tick 80 (setKey v nk s)
  let p := s.par v
  if p = 0 then updMinKey v nk s
  else if nk < s.key p then
    let a := whileF cascCond cascStep C.F (cut v p s, p)
    let s := if a.1.par a.2 ≠ 0 then setMark a.2 1 a.1 else a.1
    updMinKey v nk s
  else s

/-! ### Dijkstra -/

/-- Relax the edge from `u` to `v` of weight `w`. -/
def relax [LT R] [DecidableLT R] [Add R] (u v : ℕ) (w : R) (s : StW R) : StW R :=
  let nk := s.key u + w
  if s.stat v = 0 then updMin v (attach v 0 (setStat v 1 (setKey v nk s)))
  else if s.stat v = 1 then (if nk < s.key v then decKey C v nk s else s)
  else s

/-- Relax the next half-edge. -/
def scanStep [LT R] [DecidableLT R] [Add R] (a : StW R × ℕ × List (ℕ × R)) :
    StW R × ℕ × List (ℕ × R) :=
  match a.2.2 with
  | [] => a
  | (v, w) :: l => (tick 50 (relax C a.2.1 v w a.1), a.2.1, l)

/-- While half-edges remain. -/
def scanCond (a : StW R × ℕ × List (ℕ × R)) : Prop := a.2.2 ≠ []

instance : DecidablePred (scanCond (R := R)) := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Settle the minimum root and relax its edges. -/
def mainStep [LT R] [DecidableLT R] [Add R] (s : StW R) : StW R :=
  let u := s.hmin
  let s := setStat u 2 (extract C s)
  tick 20 (whileF scanCond (scanStep C) C.F (s, u, C.adj u)).1

/-- The blank state. -/
def blank [Zero R] : StW R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The state once the source is in the heap, if it is a vertex. -/
def start [LT R] [DecidableLT R] [Zero R] (src : ℕ) : StW R :=
  if src < C.n then updMin (src + 1) (attach (src + 1) 0 (setStat (src + 1) 1 blank)) else blank

/-- The state at the end. -/
def finish [LT R] [DecidableLT R] [Add R] [Zero R] (src : ℕ) : StW R :=
  whileF rootsCond (mainStep C) C.F (start C src)

/-- The output for vertex id `v`. -/
def outVal [Zero R] (s : StW R) (v : ℕ) : R := if s.stat v = 2 then s.key v else 0

end Formalgo.Algorithms.ShortestPaths
