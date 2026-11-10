import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapInsert
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.Dist

/-!
# Dijkstra's algorithm on the model: invariants

LLM-generated; not checked by a human.

Vertex `u : Fin n` has id `u + 1`. Status `1` means in the heap, `2` settled. Keys and weights
are in `R`, a linear order with nonnegative addition (`ℕ`, or the nonnegative reals). A settled key
is the least weight of a walk from the source; a key in the heap is the weight of some walk.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*}

/-- The ids in the heap. -/
def hset (n : ℕ) (s : StW R) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun v => v ≠ 0 ∧ s.stat v = 1

/-- The settled ids. -/
def done (n : ℕ) (s : StW R) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun v => v ≠ 0 ∧ s.stat v = 2

theorem mem_hset {n v : ℕ} {s : StW R} : v ∈ hset n s ↔ v ≤ n ∧ v ≠ 0 ∧ s.stat v = 1 := by
  simp only [hset, Finset.mem_filter, Finset.mem_range]; omega

theorem mem_done {n v : ℕ} {s : StW R} : v ∈ done n s ↔ v ≤ n ∧ v ≠ 0 ∧ s.stat v = 2 := by
  simp only [done, Finset.mem_filter, Finset.mem_range]; omega

theorem card_hset_le (n : ℕ) (s : StW R) : (hset n s).card ≤ n :=
  card_le_n fun v hv => by have := mem_hset.1 hv; omega

theorem card_done_le (n : ℕ) (s : StW R) : (done n s).card ≤ n :=
  card_le_n fun v hv => by have := mem_done.1 hv; omega

variable [AddCommMonoid R] [LinearOrder R] (C : CtxW R) (G : WGraphW R) (src : ℕ) (W : R)

/-- The adjacency lists list the edges, with their weights. -/
structure AdjOK : Prop where
  n_eq : C.n = G.n
  sound : ∀ u : Fin G.n, ∀ p ∈ C.adj ((u : ℕ) + 1),
    ∃ v : Fin G.n, G.graph.Adj u v ∧ p = ((v : ℕ) + 1, G.weight s(u, v))
  complete : ∀ u v : Fin G.n, G.graph.Adj u v →
    ((v : ℕ) + 1, G.weight s(u, v)) ∈ C.adj ((u : ℕ) + 1)
  wmax : ∀ u, ∀ p ∈ C.adj u, p.2 ≤ W
  fuel : ∀ u, (C.adj u).length ≤ C.F

variable {C G src W}

/-- What holds of every state of the algorithm. -/
structure GInv (hs : src < G.n) (s : StW R) : Prop where
  statle : ∀ v, s.stat v ≤ 2
  range : ∀ v, s.stat v ≠ 0 → 1 ≤ v ∧ v ≤ G.n
  fresh : ∀ v, v ≠ 0 → s.stat v = 0 → s.par v = 0 ∧ s.deg v = 0 ∧ s.mark v = 0
  settled : ∀ u : Fin G.n, s.stat ((u : ℕ) + 1) = 2 →
    IsLeast (Set.range fun p : G.graph.Walk ⟨src, hs⟩ u => wlen G p) (s.key ((u : ℕ) + 1))
  upper : ∀ u : Fin G.n, s.stat ((u : ℕ) + 1) ≠ 0 →
    ∃ p : G.graph.Walk ⟨src, hs⟩ u, wlen G p ≤ s.key ((u : ℕ) + 1)
  source : s.stat (src + 1) ≠ 0 ∧ s.key (src + 1) = 0
  heap : HeapInv G.n s (hset G.n s)
  empty : hset G.n s = ∅ → s.hmin = 0

/-- Settled vertices other than `x` have relaxed their edges. -/
def Relaxed (G : WGraphW R) (x : ℕ) (s : StW R) : Prop :=
  ∀ u v : Fin G.n, (u : ℕ) + 1 ≠ x → s.stat ((u : ℕ) + 1) = 2 → G.graph.Adj u v →
    s.stat ((v : ℕ) + 1) ≠ 0 ∧
      (s.stat ((v : ℕ) + 1) = 1 → s.key ((v : ℕ) + 1) ≤ s.key ((u : ℕ) + 1) + G.weight s(u, v))

/-! ### The first unsettled vertex on a walk -/

variable [CanonicallyOrderedAdd R]

/-- A walk to the source from an unsettled vertex passes a vertex in the heap, with a key at
most the walk's weight. -/
theorem first_unsettled {hs : src < G.n} {s : StW R} (hI : GInv hs s) (hR : Relaxed G 0 s) :
    ∀ {b t : Fin G.n} (q : G.graph.Walk b t), t = ⟨src, hs⟩ → s.stat ((b : ℕ) + 1) ≠ 2 →
      ∃ y : Fin G.n, s.stat ((y : ℕ) + 1) = 1 ∧ s.key ((y : ℕ) + 1) ≤ wlen G q := by
  intro b t q
  induction q with
  | nil =>
    rename_i b
    intro ht hb
    subst ht
    refine ⟨⟨src, hs⟩, ?_, by rw [hI.source.2]; exact zero_le⟩
    have := hI.statle (src + 1); have := hI.source.1; simp only at hb ⊢; omega
  | @cons b c t h q ih =>
    intro ht hb
    by_cases hc : s.stat ((c : ℕ) + 1) = 2
    · obtain ⟨h1, h2⟩ := hR c b (by omega) hc h.symm
      have hb1 : s.stat ((b : ℕ) + 1) = 1 := by have := hI.statle ((b : ℕ) + 1); omega
      refine ⟨b, hb1, ?_⟩
      have hk := h2 hb1
      subst ht
      have hd : s.key ((c : ℕ) + 1) ≤ wlen G q := by
        rw [← wlen_reverse]; exact (hI.settled c hc).2 ⟨q.reverse, rfl⟩
      rw [wlen_cons, Sym2.eq_swap, add_comm (G.weight _)]
      exact hk.trans (add_le_add hd le_rfl)
    · obtain ⟨y, hy, hk⟩ := ih ht hc
      exact ⟨y, hy, by rw [wlen_cons]; exact hk.trans le_add_self⟩

/-- The minimum of the heap is at its distance: the least weight of a walk from the source. -/
theorem key_min_eq {hs : src < G.n} {s : StW R} (hI : GInv hs s) (hR : Relaxed G 0 s)
    {u : Fin G.n} (hu : s.stat ((u : ℕ) + 1) = 1)
    (hmin : ∀ y : Fin G.n, s.stat ((y : ℕ) + 1) = 1 → s.key ((u : ℕ) + 1) ≤ s.key ((y : ℕ) + 1)) :
    IsLeast (Set.range fun p : G.graph.Walk ⟨src, hs⟩ u => wlen G p) (s.key ((u : ℕ) + 1)) := by
  have hlow : ∀ p : G.graph.Walk ⟨src, hs⟩ u, s.key ((u : ℕ) + 1) ≤ wlen G p := fun p => by
    obtain ⟨y, hy, hk⟩ := first_unsettled hI hR p.reverse rfl (by omega)
    rw [wlen_reverse] at hk
    exact (hmin y hy).trans hk
  obtain ⟨p, hp⟩ := hI.upper u (by omega)
  exact ⟨⟨p, le_antisymm hp (hlow p)⟩, by rintro _ ⟨q, rfl⟩; exact hlow q⟩

/-- With the heap empty, unsettled vertices are unreachable. -/
theorem no_walk {hs : src < G.n} {s : StW R} (hI : GInv hs s) (hR : Relaxed G 0 s)
    (hempty : ∀ y : Fin G.n, s.stat ((y : ℕ) + 1) ≠ 1) {v : Fin G.n}
    (hv : s.stat ((v : ℕ) + 1) ≠ 2) : IsEmpty (G.graph.Walk ⟨src, hs⟩ v) :=
  ⟨fun p => by
    obtain ⟨y, hy, _⟩ := first_unsettled hI hR p.reverse rfl hv
    exact hempty y hy⟩

end Formalgo.Algorithms.ShortestPaths
