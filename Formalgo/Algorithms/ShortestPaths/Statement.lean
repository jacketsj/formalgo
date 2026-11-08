import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Formalgo.Core.Code.Graph
import Formalgo.Core.TDWordRAM

/-!
# Single-source shortest paths
-/

namespace Formalgo.Algorithms.ShortestPaths

/-- The edges of `G`, as pairs `(u, v)` with `u < v`, ordered lexicographically. -/
abbrev Edges {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n ×ₗ Fin n) :=
  {p | (ofLex p).1 < (ofLex p).2 ∧ G.Adj (ofLex p).1 (ofLex p).2}

/-- The number of vertices `n`, a graph on `Fin n`, a weight on each edge, and a source. -/
abbrev Input := Σ n, Σ G : SimpleGraph (Fin n), (Edges G → ℕ) × ℕ

/-- `⊤` is written as `0`, and `n : ℕ` as `n + 1`. -/
noncomputable instance enatCode {Value : Type*} [Code ℕ Value] : Code ℕ∞ Value :=
  Code.ofInj (fun d : ℕ∞ => if d = ⊤ then 0 else d.toNat + 1) fun a b h => by
    induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe <;> simp_all

/-- The weight of the edge between adjacent `u` and `v`. -/
def edgeWeight {n : ℕ} {G : SimpleGraph (Fin n)} (weight : Edges G → ℕ) {u v : Fin n}
    (h : G.Adj u v) : ℕ :=
  if huv : u < v then weight ⟨toLex (u, v), huv, h⟩
  else weight ⟨toLex (v, u), lt_of_le_of_ne (not_lt.1 huv) h.ne.symm, h.symm⟩

/-- The weight of a shortest walk from `u` to `v`, or `⊤` if there is none. -/
noncomputable def dist {n : ℕ} (G : SimpleGraph (Fin n)) (weight : Edges G → ℕ) (u v : Fin n) :
    ℕ∞ :=
  ⨅ p : G.Walk u v, ((p.darts.map fun d => edgeWeight weight d.adj).sum : ℕ∞)

/-- Shortest paths: the distance from the source to each vertex, if the source is a vertex. -/
noncomputable def shortestPaths : IOSpec Input (Σ n, Fin n → ℕ∞) where
  valid := fun ⟨n, G, weight, source⟩ output =>
    ∀ h : source < n, output = ⟨n, dist G weight ⟨source, h⟩⟩

/-- A TD word RAM with `<`, `+` and `−` finds shortest paths in `O(E + V log V)` steps
(Dijkstra's algorithm with a Fibonacci heap). -/
def ShortestPathsInEPlusVLogV : Prop :=
  ∃ c, (tdWordRAM [.less, .add, .sub]).SolvableWithin shortestPaths fun ⟨V, G, _⟩ =>
    c * (G.edgeSet.ncard + V * Nat.log 2 V) + c

end Formalgo.Algorithms.ShortestPaths
