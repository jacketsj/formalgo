import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Formalgo.Core.Graph
import Formalgo.Core.TDWordRAM

/-!
# Single-source shortest paths
-/

namespace Formalgo.Algorithms.ShortestPaths

open Classical in
/-- A function is written as the list of its values at `points`. -/
@[reducible] noncomputable def functionCode {α β Value : Type*} [Code ℕ Value] [Code β Value] [Inhabited β]
    (points : List α) : Code (α → β) Value where
  encode f := Code.encode (points.map f)
  decode stream :=
    let (values, stream) : List β × _ := Code.decode stream
    (fun a => ((points.zip values).find? fun p => p.1 = a).elim default (·.2), stream)

open Classical in
/-- The edges of `G`, in the order the code of `G` writes them. -/
noncomputable def edgeList {n : ℕ} (G : SimpleGraph (Fin n)) : List G.edgeSet :=
  (Code.edges G).filterMap fun e => if h : s(e.1, e.2) ∈ G.edgeSet then some ⟨_, h⟩ else none

/-- A graph, a weight on each of its edges, and a source vertex. -/
structure Input where
  /-- The number of vertices. -/
  n : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin n)
  /-- The weight of each edge. -/
  weight : graph.edgeSet → ℕ
  /-- The source vertex. -/
  source : ℕ

/-- An input is written as its graph, then its weights in the order of its edges, then its source. -/
noncomputable instance {Value : Type*} [Code ℕ Value] : Code Input Value where
  encode input :=
    letI := functionCode (Value := Value) (β := ℕ) (edgeList input.graph)
    Code.encode (⟨input.n, input.graph⟩ : Σ n, SimpleGraph (Fin n)) ++ Code.encode input.weight ++
      Code.encode input.source
  decode stream :=
    let (⟨n, G⟩, stream) : (Σ n, SimpleGraph (Fin n)) × _ := Code.decode stream
    letI := functionCode (Value := Value) (β := ℕ) (edgeList G)
    let (weight, stream) : (G.edgeSet → ℕ) × _ := Code.decode stream
    let (source, stream) : ℕ × _ := Code.decode stream
    (⟨n, G, weight, source⟩, stream)

/-- `⊤` is written as `0`, and `n : ℕ` as `n + 1`. -/
instance enatCode {Value : Type*} [Code ℕ Value] : Code ℕ∞ Value where
  encode d := Code.encode (if d = ⊤ then 0 else d.toNat + 1)
  decode stream :=
    let (k, stream) : ℕ × _ := Code.decode stream
    (if k = 0 then ⊤ else (k - 1 : ℕ), stream)

/-- The weight of a shortest walk from `u` to `v`, or `⊤` if there is none. -/
noncomputable def dist {n : ℕ} (G : SimpleGraph (Fin n)) (weight : G.edgeSet → ℕ) (u v : Fin n) :
    ℕ∞ :=
  ⨅ p : G.Walk u v,
    ((p.edges.attach.map fun e => weight ⟨e.1, p.edges_subset_edgeSet e.2⟩).sum : ℕ∞)

/-- Shortest paths: the distance from the source to each vertex, if the source is a vertex. -/
noncomputable def shortestPaths : IOSpec Input (List ℕ∞) where
  valid input output := ∀ h : input.source < input.n,
    output = List.ofFn (dist input.graph input.weight ⟨input.source, h⟩)

/-- A TD word RAM with `<`, `+` and `−` finds shortest paths in `O(E + V log V)` steps
(Dijkstra's algorithm with a Fibonacci heap). -/
def ShortestPathsInEPlusVLogV : Prop :=
  ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin shortestPaths fun input =>
    let V := input.n
    c * (input.graph.edgeSet.ncard + V * Nat.log 2 V) + c

end Formalgo.Algorithms.ShortestPaths
