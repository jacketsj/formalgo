import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sym.Sym2.Order
import Formalgo.Core.Code

/-!
# Codes for graphs
Codes for Mathlib's simple graphs, digraphs and multigraphs, and for labellings of their edges.
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

/-- Unordered pairs `s(a, b)` with `a ≤ b`, ordered lexicographically by `(a, b)`. -/
abbrev sym2LinearOrder (α : Type*) [LinearOrder α] : LinearOrder (Sym2 α) :=
  LinearOrder.lift' (fun z => toLex (Sym2.sortEquiv z : α × α))
    fun _ _ h => Sym2.sortEquiv.injective (Subtype.ext (toLex.injective h))

/-- A labelling of a set of unordered pairs (e.g. edge weights `G.edgeSet → ℕ`) is written as the
list of its values, with `s(a, b)` (`a ≤ b`) in lexicographic order of `(a, b)`. -/
noncomputable instance edgeLabels {s : Set (Sym2 α)} [Inhabited β] [Code (List β) Value] :
    Code (s → β) Value :=
  letI := sym2LinearOrder α
  labels

end Formalgo.Code
