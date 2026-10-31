import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.ENat.Lattice
import Formalgo.Core.Code

/-!
# Graphs
Weighted graphs, and codes for Mathlib's simple graphs on `Fin n`.
-/

namespace Formalgo

/-- A graph on `Fin n` with natural-number edge weights. -/
structure WeightedGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin n)
  /-- The weight of each edge. -/
  weight : Sym2 (Fin n) → ℕ

/-- The weight of a shortest walk from `u` to `v`, or `⊤` if there is none. -/
noncomputable def WeightedGraph.dist (G : WeightedGraph) (u v : Fin G.n) : ℕ∞ :=
  ⨅ p : G.graph.Walk u v, ((p.edges.map G.weight).sum : ℕ∞)

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

/-- A weighted graph is written as its graph, then the weights of its edges, in order. -/
noncomputable instance weightedGraph : Code WeightedGraph Value where
  encode G := encode ((⟨G.n, G.graph⟩ : Σ n, SimpleGraph (Fin n)),
    (edges G.graph).map fun e => G.weight s(e.1, e.2))
  decode stream :=
    let ((⟨n, G⟩, weights), stream) : ((Σ n, SimpleGraph (Fin n)) × List ℕ) × _ := decode stream
    let weight (e : Sym2 (Fin n)) :=
      (((edges G).zip weights).find? fun (e', _) => s(e'.1, e'.2) = e).elim 0 (·.2)
    (⟨n, G, weight⟩, stream)

end Code

end Formalgo
