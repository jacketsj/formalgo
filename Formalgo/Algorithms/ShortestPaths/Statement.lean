import Mathlib.Data.Set.Card
import Formalgo.Core.Graph
import Formalgo.Core.TDWordRAM

/-!
# Single-source shortest paths
-/

namespace Formalgo.Algorithms.ShortestPaths

/-- A weighted graph, and a source vertex. -/
structure Input where
  /-- The graph. -/
  graph : WeightedGraph
  /-- The source vertex. -/
  source : ℕ

/-- An input is written as its graph, then its source. -/
noncomputable instance {Value : Type*} [Code ℕ Value] : Code Input Value where
  encode input := Code.encode (input.graph, input.source)
  decode stream :=
    let ((graph, source), stream) : (WeightedGraph × ℕ) × _ := Code.decode stream
    (⟨graph, source⟩, stream)

/-- Shortest paths: the distance from the source to each vertex, if the source is a vertex. -/
noncomputable def shortestPaths : IOSpec Input (List ℕ∞) where
  valid input output := ∀ h : input.source < input.graph.n,
    output = List.ofFn (input.graph.dist ⟨input.source, h⟩)

/-- A TD word RAM with `<`, `+` and `−` finds shortest paths in `O(E + V log V)` steps
(Dijkstra's algorithm with a Fibonacci heap). -/
def ShortestPathsInEPlusVLogV : Prop :=
  ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin shortestPaths fun input =>
    let V := input.graph.n
    c * (input.graph.graph.edgeSet.ncard + V * Nat.log 2 V) + c

end Formalgo.Algorithms.ShortestPaths
