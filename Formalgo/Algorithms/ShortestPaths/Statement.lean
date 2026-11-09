import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Proof

/-!
# Single-source shortest paths
-/

namespace Formalgo.Algorithms.ShortestPaths

/-- The number of vertices `n`, a graph on `Fin n`, a weight on each edge, and a source. -/
abbrev Input := Σ n, Σ G : SimpleGraph (Fin n), (G.edgeSet → ℕ) × ℕ

/-- The weight of a shortest walk from `u` to `v` (`0` if there is none). -/
noncomputable def dist {n : ℕ} (G : SimpleGraph (Fin n)) (weight : G.edgeSet → ℕ) (u v : Fin n) :
    ℕ :=
  ⨅ p : G.Walk u v, (p.darts.map fun d => weight ⟨d.edge, d.edge_mem⟩).sum

/-- Shortest paths: if the graph is connected and the source is a vertex, the distance from the
source to each vertex. -/
noncomputable def shortestPaths : IOSpec Input (Σ n, Fin n → ℕ) where
  valid := fun ⟨n, G, weight, source⟩ output =>
    G.Connected → ∀ h : source < n, output = ⟨n, dist G weight ⟨source, h⟩⟩

/-- A TD word RAM with `<`, `+` and `−` finds shortest paths in `O(E + V log V)` steps
(Dijkstra's algorithm with a Fibonacci heap). -/
theorem shortestPathsInEPlusVLogV :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin shortestPaths fun ⟨V, G, _⟩ =>
      c * (G.edgeSet.ncard + V * Nat.log 2 V) + c :=
  shortestPaths_wordRAM shortestPaths fun _ _ _ _ _ h => h

end Formalgo.Algorithms.ShortestPaths
