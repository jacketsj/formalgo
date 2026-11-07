import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapInsert
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.Dist

/-!
# Dijkstra's algorithm on the model: invariants

LLM-generated; not checked by a human.

Vertex `u : Fin n` has id `u + 1`. Status `1` means in the heap, `2` settled.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

/-- The ids in the heap. -/
def hset (n : ℕ) (s : St) : Finset ℕ := (Finset.range (n + 1)).filter fun v => v ≠ 0 ∧ s.stat v = 1

/-- The settled ids. -/
def done (n : ℕ) (s : St) : Finset ℕ := (Finset.range (n + 1)).filter fun v => v ≠ 0 ∧ s.stat v = 2

variable (C : Ctx) (G : WGraph) (src W : ℕ)

/-- The adjacency lists list the edges, with their weights. -/
structure AdjOK : Prop where
  n_eq : C.n = G.n
  sound : ∀ u : Fin G.n, ∀ p ∈ C.adj ((u : ℕ) + 1),
    ∃ v : Fin G.n, G.graph.Adj u v ∧ p = ((v : ℕ) + 1, G.weight s(u, v))
  complete : ∀ u v : Fin G.n, G.graph.Adj u v → ((v : ℕ) + 1, G.weight s(u, v)) ∈ C.adj ((u : ℕ) + 1)
  wmax : ∀ u, ∀ p ∈ C.adj u, p.2 ≤ W
  fuel : ∀ u, (C.adj u).length ≤ C.F

variable {C G src W}

/-- What holds of every state of the algorithm. -/
structure GInv (hs : src < G.n) (s : St) : Prop where
  statle : ∀ v, s.stat v ≤ 2
  range : ∀ v, s.stat v ≠ 0 → 1 ≤ v ∧ v ≤ G.n
  fresh : ∀ v, v ≠ 0 → s.stat v = 0 → s.par v = 0 ∧ s.deg v = 0 ∧ s.mark v = 0
  settled : ∀ u : Fin G.n, s.stat ((u : ℕ) + 1) = 2 → (s.key ((u : ℕ) + 1) : ℕ∞) = G.dist ⟨src, hs⟩ u
  upper : ∀ u : Fin G.n, s.stat ((u : ℕ) + 1) ≠ 0 → G.dist ⟨src, hs⟩ u ≤ s.key ((u : ℕ) + 1)
  source : s.stat (src + 1) ≠ 0 ∧ s.key (src + 1) = 0
  heap : HeapInv G.n s (hset G.n s)
  empty : hset G.n s = ∅ → s.hmin = 0

/-- Settled vertices other than `x` have relaxed their edges. -/
def Relaxed (G : WGraph) (x : ℕ) (s : St) : Prop :=
  ∀ u v : Fin G.n, (u : ℕ) + 1 ≠ x → s.stat ((u : ℕ) + 1) = 2 → G.graph.Adj u v →
    s.stat ((v : ℕ) + 1) ≠ 0 ∧
      (s.stat ((v : ℕ) + 1) = 1 → s.key ((v : ℕ) + 1) ≤ s.key ((u : ℕ) + 1) + G.weight s(u, v))

theorem mem_hset {n v : ℕ} {s : St} : v ∈ hset n s ↔ v ≤ n ∧ v ≠ 0 ∧ s.stat v = 1 := by
  simp only [hset, Finset.mem_filter, Finset.mem_range]; omega

theorem mem_done {n v : ℕ} {s : St} : v ∈ done n s ↔ v ≤ n ∧ v ≠ 0 ∧ s.stat v = 2 := by
  simp only [done, Finset.mem_filter, Finset.mem_range]; omega

theorem card_hset_le (n : ℕ) (s : St) : (hset n s).card ≤ n :=
  card_le_n fun v hv => by have := mem_hset.1 hv; omega

theorem card_done_le (n : ℕ) (s : St) : (done n s).card ≤ n :=
  card_le_n fun v hv => by have := mem_done.1 hv; omega

/-! ### The first unsettled vertex on a walk -/

/-- A walk to the source from an unsettled vertex passes a vertex in the heap, with a key at
most the walk's weight. -/
theorem first_unsettled {hs : src < G.n} {s : St} (hI : GInv hs s) (hR : Relaxed G 0 s) :
    ∀ {b t : Fin G.n} (q : G.graph.Walk b t), t = ⟨src, hs⟩ → s.stat ((b : ℕ) + 1) ≠ 2 →
      ∃ y : Fin G.n, s.stat ((y : ℕ) + 1) = 1 ∧ s.key ((y : ℕ) + 1) ≤ wlen G q := by
  intro b t q
  induction q with
  | nil =>
    rename_i b
    intro ht hb
    subst ht
    refine ⟨⟨src, hs⟩, ?_, by rw [hI.source.2]; exact Nat.zero_le _⟩
    have := hI.statle (src + 1); have := hI.source.1; simp only at hb ⊢; omega
  | @cons b c t h q ih =>
    intro ht hb
    by_cases hc : s.stat ((c : ℕ) + 1) = 2
    · obtain ⟨h1, h2⟩ := hR c b (by omega) hc h.symm
      have hb1 : s.stat ((b : ℕ) + 1) = 1 := by have := hI.statle ((b : ℕ) + 1); omega
      refine ⟨b, hb1, ?_⟩
      have hk := h2 hb1
      subst ht
      have hd : (s.key ((c : ℕ) + 1) : ℕ∞) ≤ wlen G q.reverse := by
        rw [hI.settled c hc]; exact dist_le_wlen _
      rw [wlen_reverse] at hd
      have hd' : s.key ((c : ℕ) + 1) ≤ wlen G q := by exact_mod_cast hd
      rw [wlen_cons, Sym2.eq_swap]; omega
    · obtain ⟨y, hy, hk⟩ := ih ht hc
      exact ⟨y, hy, by rw [wlen_cons]; omega⟩

/-- The minimum of the heap is at its distance. -/
theorem key_min_eq {hs : src < G.n} {s : St} (hI : GInv hs s) (hR : Relaxed G 0 s)
    {u : Fin G.n} (hu : s.stat ((u : ℕ) + 1) = 1)
    (hmin : ∀ y : Fin G.n, s.stat ((y : ℕ) + 1) = 1 → s.key ((u : ℕ) + 1) ≤ s.key ((y : ℕ) + 1)) :
    (s.key ((u : ℕ) + 1) : ℕ∞) = G.dist ⟨src, hs⟩ u := by
  refine le_antisymm (le_dist fun p => ?_) (hI.upper u (by omega))
  obtain ⟨y, hy, hk⟩ := first_unsettled hI hR p.reverse rfl (by omega)
  rw [wlen_reverse] at hk
  exact_mod_cast (hmin y hy).trans hk

/-- With the heap empty, unsettled vertices are unreachable. -/
theorem dist_top {hs : src < G.n} {s : St} (hI : GInv hs s) (hR : Relaxed G 0 s)
    (hempty : ∀ y : Fin G.n, s.stat ((y : ℕ) + 1) ≠ 1) {v : Fin G.n}
    (hv : s.stat ((v : ℕ) + 1) ≠ 2) : G.dist ⟨src, hs⟩ v = ⊤ :=
  dist_eq_top fun p => by
    obtain ⟨y, hy, _⟩ := first_unsettled hI hR p.reverse rfl hv
    exact hempty y hy

end Formalgo.Algorithms.ShortestPaths
