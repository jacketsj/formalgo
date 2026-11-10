import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Sym2.Order
import Formalgo.Core.Code.Graph
import Formalgo.Core.TDWordRAM

/-!
# The input as an edge list

LLM-generated; not checked by a human.

The core of the program reads the input as `n`, the edges `(u, v)` with `u < v` in lexicographic
order, their weights in the same order, and the source. A first stage writes the statement's input
in this form.
-/

namespace Formalgo.Algorithms.ShortestPaths

/-- The statement's input type (the proof does not import the statement). -/
abbrev LLMUnchecked.Input := Σ n, Σ G : SimpleGraph (Fin n), (G.edgeSet → ℕ) × ℕ

open LLMUnchecked

open Classical in
/-- The edges `(u, v)` of `G` with `u < v`, in lexicographic order. -/
noncomputable def lexEdges {n : ℕ} (G : SimpleGraph (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v ∧ G.Adj u v).map (u, ·)

open Classical in
/-- The edges of `G`, in the order of `lexEdges`. -/
noncomputable def edgeList {n : ℕ} (G : SimpleGraph (Fin n)) : List G.edgeSet :=
  (lexEdges G).filterMap fun e => if h : s(e.1, e.2) ∈ G.edgeSet then some ⟨_, h⟩ else none

/-- The edges of a graph as pairs of numbers. -/
noncomputable def edgesNat {n : ℕ} (G : SimpleGraph (Fin n)) : List (ℕ × ℕ) :=
  (lexEdges G).map fun e => ((e.1 : ℕ), (e.2 : ℕ))

/-- A graph, a weight on each of its edges, and a source vertex. -/
structure EInput where
  n : ℕ
  graph : SimpleGraph (Fin n)
  weight : graph.edgeSet → ℕ
  source : ℕ

/-- The parts of the code of an input. -/
noncomputable def inTuple (x : EInput) : ((ℕ × List (ℕ × ℕ)) × List ℕ) × ℕ :=
  (((x.n, edgesNat x.graph), (edgeList x.graph).map x.weight), x.source)

section Edges

variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem mem_edges {u v : Fin n} : (u, v) ∈ lexEdges G ↔ u < v ∧ G.Adj u v := by
  classical
  unfold lexEdges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨u', v', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨u, v, ⟨h1, h2⟩, rfl, rfl⟩

theorem mem_edgeList (e : G.edgeSet) : e ∈ edgeList G := by
  classical
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    have hab : G.Adj a b := he
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact List.mem_filterMap.2 ⟨(a, b), mem_edges.2 ⟨h, hab⟩, dif_pos he⟩
    · refine List.mem_filterMap.2 ⟨(b, a), mem_edges.2 ⟨h, hab.symm⟩, ?_⟩
      rw [dif_pos (show s(b, a) ∈ G.edgeSet from hab.symm)]
      simp [Sym2.eq_swap]

end Edges

theorem inTuple_injective : Function.Injective inTuple := by
  rintro ⟨n, G, w, s⟩ ⟨n', G', w', s'⟩ h
  simp only [inTuple, Prod.mk.injEq] at h
  obtain ⟨⟨⟨rfl, hE⟩, hW⟩, rfl⟩ := h
  have hL : lexEdges G = lexEdges G' := List.map_injective_iff.2 (fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)) hE
  have hadj : ∀ u v, u < v → (G.Adj u v ↔ G'.Adj u v) := fun u v huv => by
    have h1 : (u, v) ∈ lexEdges G ↔ (u, v) ∈ lexEdges G' := by rw [hL]
    rw [mem_edges, mem_edges] at h1
    exact ⟨fun h => (h1.1 ⟨huv, h⟩).2, fun h => (h1.2 ⟨huv, h⟩).2⟩
  have hG : G = G' := by
    ext u v
    rcases lt_trichotomy u v with h | rfl | h
    · exact hadj u v h
    · simp
    · exact ⟨fun a => ((hadj v u h).1 a.symm).symm, fun a => ((hadj v u h).2 a.symm).symm⟩
  subst hG
  have hw : w = w' := funext fun e => List.map_inj_left.1 hW e (mem_edgeList e)
  subst hw
  rfl

instance : Nonempty EInput := ⟨⟨0, ⊥, fun _ => 0, 0⟩⟩

/-- An input is written as `n`, its edges, its weights in the order of its edges, and its
source. -/
noncomputable instance {Value : Type*} [Code ℕ Value] : Code EInput Value :=
  Code.ofInj inTuple inTuple_injective

theorem encode_einput {Value : Type*} [Code ℕ Value] (x : EInput) :
    (Code.encode x : List Value) = Code.encode (inTuple x) := rfl

/-- The statement's input as an edge-list input. -/
noncomputable def toE (x : Input) : EInput := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

end Formalgo.Algorithms.ShortestPaths
