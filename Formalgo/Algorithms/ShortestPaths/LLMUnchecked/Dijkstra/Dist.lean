import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.EInput
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.ENat.Lattice

/-!
# Distances

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked

/-- A graph with a weight on every pair of vertices, for the proof. -/
structure WGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)
  weight : Sym2 (Fin n) → ℕ

/-- The weight of a shortest walk from `u` to `v`, or `⊤` if there is none. -/
noncomputable def WGraph.dist (G : WGraph) (u v : Fin G.n) : ℕ∞ :=
  ⨅ p : G.graph.Walk u v, ((p.edges.map G.weight).sum : ℕ∞)

open Classical in
/-- The graph of an input, with weight `0` off its edges. -/
noncomputable def EInput.wg (x : EInput) : WGraph :=
  ⟨x.n, x.graph, fun e => if h : e ∈ x.graph.edgeSet then x.weight ⟨e, h⟩ else 0⟩

theorem wg_weight (x : EInput) {e : Sym2 (Fin x.n)} (h : e ∈ x.graph.edgeSet) :
    x.wg.weight e = x.weight ⟨e, h⟩ := dif_pos h

variable (G : WGraph)

/-- The weight of a walk. -/
def wlen {u v : Fin G.n} (p : G.graph.Walk u v) : ℕ := (p.edges.map G.weight).sum

variable {G}

theorem dist_le_wlen {u v : Fin G.n} (p : G.graph.Walk u v) : G.dist u v ≤ wlen G p :=
  iInf_le (fun p : G.graph.Walk u v => ((wlen G p : ℕ) : ℕ∞)) p

theorem wlen_reverse {u v : Fin G.n} (p : G.graph.Walk u v) : wlen G p.reverse = wlen G p := by
  simp [wlen, SimpleGraph.Walk.edges_reverse, List.sum_reverse]

theorem wlen_cons {u v w : Fin G.n} (h : G.graph.Adj u v) (p : G.graph.Walk v w) :
    wlen G (.cons h p) = G.weight s(u, v) + wlen G p := by
  simp [wlen]

theorem wlen_concat {u v w : Fin G.n} (p : G.graph.Walk u v) (h : G.graph.Adj v w) :
    wlen G (p.concat h) = wlen G p + G.weight s(v, w) := by
  simp [wlen]

theorem dist_self (u : Fin G.n) : G.dist u u = 0 :=
  le_antisymm (by simpa [wlen] using dist_le_wlen (G := G) (SimpleGraph.Walk.nil : G.graph.Walk u u))
    bot_le

/-- The triangle inequality over an edge. -/
theorem dist_edge {s a b : Fin G.n} (h : G.graph.Adj a b) :
    G.dist s b ≤ G.dist s a + G.weight s(a, b) := by
  unfold WGraph.dist
  rw [ENat.iInf_add]
  refine le_iInf fun p => ?_
  refine (iInf_le _ (p.concat h)).trans ?_
  have := wlen_concat p h
  simp only [wlen] at this
  rw [this]; push_cast; rfl

/-- A walk reaching `v` makes its distance finite. -/
theorem dist_ne_top {u v : Fin G.n} (p : G.graph.Walk u v) : G.dist u v ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (dist_le_wlen p)

/-- With no walk, the distance is `⊤`. -/
theorem dist_eq_top {u v : Fin G.n} (h : ∀ _ : G.graph.Walk u v, False) : G.dist u v = ⊤ := by
  unfold WGraph.dist
  haveI : IsEmpty (G.graph.Walk u v) := ⟨h⟩
  simp

/-- The distance is at most a bound on all walks. -/
theorem le_dist {u v : Fin G.n} {d : ℕ∞} (h : ∀ p : G.graph.Walk u v, d ≤ wlen G p) :
    d ≤ G.dist u v :=
  le_iInf h

theorem wlen_toE (x : Input) {u v : Fin x.1} (p : x.2.1.Walk u v) :
    wlen (toE x).wg p = (p.darts.map fun d => x.2.2.1 ⟨d.edge, d.edge_mem⟩).sum := by
  unfold wlen SimpleGraph.Walk.edges
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun d _ => wg_weight (toE x) d.edge_mem

theorem dist_toE (x : Input) (u v : Fin x.1) :
    ((toE x).wg.dist u v).toNat =
      ⨅ p : x.2.1.Walk u v, (p.darts.map fun d => x.2.2.1 ⟨d.edge, d.edge_mem⟩).sum := by
  unfold WGraph.dist
  rcases isEmpty_or_nonempty (x.2.1.Walk u v) with h | h
  · haveI : IsEmpty ((toE x).wg.graph.Walk u v) := h
    rw [iInf_of_isEmpty, sInf_empty, ENat.toNat_top, iInf_of_isEmpty, Nat.sInf_empty]
  · haveI : Nonempty ((toE x).wg.graph.Walk u v) := h
    rw [← ENat.coe_iInf, ENat.toNat_coe]
    exact iInf_congr fun p => wlen_toE x p

end Formalgo.Algorithms.ShortestPaths
