import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Formalgo.Core.Code

/-!
# Codes for graphs
Codes for Mathlib's simple graphs, digraphs and multigraphs.
-/

namespace Formalgo.Code

open Graph

variable {α β Value : Type*} [Finite α] [LinearOrder α] [Finite β] [LinearOrder β] [Code ℕ Value]

/-- A simple graph is written as the set of neighbours of each vertex. -/
noncomputable instance simpleGraph : Code (SimpleGraph α) Value :=
  ofInj (β := α → Set α) SimpleGraph.Adj SimpleGraph.adj_injective

/-- A digraph is written as the set of out-neighbours of each vertex. -/
noncomputable instance digraph : Code (Digraph α) Value :=
  ofInj (β := α → Set α) Digraph.Adj Digraph.adj_injective

/-- A multigraph is written as its vertex set, then the set of ends of each edge (empty for
non-edges). -/
noncomputable instance graph : Code (Graph α β) Value :=
  ofInj (β := Set α × (β → Set α)) (fun G => (V(G), G.Inc)) fun _ _ h => by
    simp only [Prod.ext_iff] at h
    exact Graph.ext_inc h.1 (by simp [h.2])

end Formalgo.Code
