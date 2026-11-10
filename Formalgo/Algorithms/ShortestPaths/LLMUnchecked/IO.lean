import Mathlib.Tactic.Ring
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Codes

/-!
# Shortest-paths input and output on the tape

LLM-generated; not checked by a human.

The input code is `n, E, u₁, v₁, …, u_E, v_E, E, w₁, …, w_E, source`, of length `3 E + 4`.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Function

/-- The number of encoded edges. -/
noncomputable def numEdges (x : EInput) : ℕ := (lexEdges x.wg.graph).length

theorem flatMap_ncode_pairs (l : List (ℕ × ℕ)) :
    l.flatMap ncode = l.flatMap fun p => [p.1, p.2] := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih, ncode_prod, ncode_nat, ncode_nat]; rfl

theorem flatMap_ncode_nats (l : List ℕ) : l.flatMap ncode = l := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [List.flatMap_cons, ih, ncode_nat]; rfl

theorem ncode_input_eq (x : EInput) : ncode x =
    [x.wg.n, numEdges x] ++ (edgesNat x.wg.graph).flatMap (fun p => [p.1, p.2]) ++
      [numEdges x] ++ (lexEdges x.wg.graph).map (fun e => x.wg.weight s(e.1, e.2)) ++
      [x.source] := by
  have h1 : ncode x = ncode (x.wg.n, edgesNat x.wg.graph) ++
      ncode ((lexEdges x.wg.graph).map fun e => x.wg.weight s(e.1, e.2)) ++
      ncode x.source := by
    have e : ncode x = ncode (x.n, edgesNat x.graph) ++
        ncode ((edgeList x.graph).map x.weight) ++ ncode x.source := rfl
    rw [e, values_eq]
    rfl
  rw [h1, ncode_prod, ncode_nat, ncode_list, ncode_list, ncode_nat, flatMap_ncode_pairs,
    flatMap_ncode_nats]
  simp [numEdges, edgesNat]

theorem length_ncode_input (x : EInput) : (ncode x).length = 3 * numEdges x + 4 := by
  rw [ncode_input_eq]
  have h : ∀ l : List (ℕ × ℕ), (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons p l ih => simp [List.flatMap_cons, ih]; ring
  simp only [List.length_append, List.length_cons, List.length_nil, h, edgesNat, numEdges,
    List.length_map]
  ring

end Formalgo.Algorithms.ShortestPaths
