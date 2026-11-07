import Mathlib.Combinatorics.SimpleGraph.Basic
import Formalgo.Core.Code

/-!
# Graphs
Codes for Mathlib's simple graphs on `Fin n`.
-/

namespace Formalgo

namespace Code

variable {Value : Type*} [Code ℕ Value]

open Classical in
/-- The edges `(u, v)` of `G` with `u < v`, in lexicographic order. -/
noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v ∧ G.Adj u v).map (u, ·)

/-- A graph on `Fin n` is written as `n`, then its edges. -/
noncomputable instance graph : Code (Σ n, SimpleGraph (Fin n)) Value where
  encode G := encode (G.1, (edges G.2).map fun e => ((e.1 : ℕ), (e.2 : ℕ)))
  decode stream :=
    let ((n, edges), stream) : (ℕ × List (ℕ × ℕ)) × _ := decode stream
    (⟨n, .fromEdgeSet {e | ∃ u v : Fin n, ((u : ℕ), (v : ℕ)) ∈ edges ∧ e = s(u, v)}⟩, stream)

end Code

end Formalgo
