import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Proof

/-!
# Single-source shortest paths
-/

namespace Formalgo.Algorithms.ShortestPaths

/-- The number of vertices `n`, a graph on `Fin n`, a weight in `W` on each edge, and a source. -/
abbrev Input (W : Type*) := Σ n, Σ G : SimpleGraph (Fin n), (G.edgeSet → W) × ℕ

/-- The total weight of the edges of a walk. -/
def walkWeight (W : Type*) [AddMonoid W] {n : ℕ} {G : SimpleGraph (Fin n)}
    (weight : G.edgeSet → W) {u v : Fin n} (p : G.Walk u v) : W :=
  (p.darts.map fun d => weight ⟨d.edge, d.edge_mem⟩).sum

/-- Single-source shortest paths: if the graph is connected and the source is a vertex, the
weight of a lightest walk from the source to each vertex. -/
def singleSourceShortestPaths (W : Type*) [AddMonoid W] [LE W] :
    IOSpec (Input W) (Σ n, Fin n → W) where
  valid := fun ⟨n, G, weight, source⟩ output =>
    G.Connected → ∀ h : source < n, ∃ d : Fin n → W, output = ⟨n, d⟩ ∧
      ∀ v, IsLeast {walkWeight W weight p | p : G.Walk ⟨source, h⟩ v} (d v)

/-- A TD word RAM with `<`, `+` and `−` finds single-source shortest paths in `O(E + V log V)`
steps (Dijkstra's algorithm with a Fibonacci heap). -/
theorem singleSourceShortestPathsInEPlusVLogV :
    ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin (singleSourceShortestPaths ℕ)
      fun ⟨V, G, _⟩ => c * (G.edgeSet.ncard + V * Nat.log 2 V) + c :=
  shortestPaths_wordRAM _ fun _ _ _ _ _ h => h

end Formalgo.Algorithms.ShortestPaths
