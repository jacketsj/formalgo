import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.DijkstraMain
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Codes

/-!
# Dijkstra's algorithm on the model: start and finish

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [CanonicallyOrderedAdd R]
  {C : CtxW R} {G : WGraphW R} {src : ℕ} {W : R}

omit [CanonicallyOrderedAdd R] in
theorem heapInv_blank (n : ℕ) : HeapInv n (blank : StW R) ∅ :=
  ⟨fun v hv => absurd hv (Finset.notMem_empty v),
    ⟨Finset.notMem_empty 0, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
      fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
      fun v hv => absurd hv (Finset.notMem_empty v), fun v hv => absurd hv (Finset.notMem_empty v),
      fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun j hj => absurd hj (Nat.not_lt_zero j),
      fun v hv => absurd hv (Finset.notMem_empty v)⟩,
    fun h => absurd h Finset.not_nonempty_empty, fun _ => rfl⟩

omit [CanonicallyOrderedAdd R] in
theorem start_eq (h : src < C.n) : start C src = insertSt (src + 1) (0 : R) 1 blank := by
  have hb : setKey (src + 1) (0 : R) blank = blank := by
    refine StW.ext ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    funext x; change update (0 : ℕ → R) (src + 1) 0 x = 0
    rcases eq_or_ne x (src + 1) with rfl | hx
    · simp
    · rw [update_of_ne hx]; rfl
  simp only [start, if_pos h, insertSt, hb]

theorem DInv.start (hA : AdjOK C G W) (hs : src < G.n) : DInv C G W hs (start C src) := by
  rw [start_eq (by rw [hA.n_eq]; exact hs)]
  obtain ⟨hH, hkey, hstat, hout, htime, hpot⟩ := insert_spec (heapInv_blank G.n) (fun _ => rfl)
    (v := src + 1) (by omega) (by omega) (Finset.notMem_empty _) rfl rfl (Nat.zero_le 1) (0 : R) 1
  set S := insertSt (src + 1) (0 : R) 1 blank with hS
  have hst : ∀ x, S.stat x = if x = src + 1 then 1 else 0 := fun x => by
    rw [hstat]; rcases eq_or_ne x (src + 1) with rfl | hx
    · simp
    · rw [update_of_ne hx, if_neg hx]; rfl
  have hk0 : ∀ x, S.key x = 0 := fun x => by
    rw [hkey]; rcases eq_or_ne x (src + 1) with rfl | hx
    · simp
    · rw [update_of_ne hx]; rfl
  have hset1 : hset G.n S = insert (src + 1) ∅ := by
    ext x; simp only [mem_hset, hst, Finset.mem_insert, Finset.notMem_empty, or_false]
    split_ifs with h
    · subst h; simp; omega
    · simp [h]
  have hdone : done G.n S = ∅ := by
    ext x; rw [mem_done, hst]; simp only [Finset.notMem_empty, iff_false]
    rintro ⟨-, -, h⟩; split_ifs at h; omega
  refine ⟨⟨fun x => ?_, fun x hx => ?_, fun x hx0 hx => ?_, fun x hx => ?_, fun x hx => ?_,
    ⟨by rw [hst]; simp, hk0 _⟩, by rw [hset1]; exact hH, fun h => by rw [hset1] at h; simp at h⟩,
    fun a b _ ha _ => ?_, fun x _ => by rw [hk0]; exact zero_le, ?_⟩
  · rw [hst]; split_ifs <;> omega
  · rw [hst] at hx; split_ifs at hx with h
    · omega
    · exact absurd rfl hx
  · have hxs : x ≠ src + 1 := by intro h; rw [hst, if_pos h] at hx; omega
    obtain ⟨a, b, c⟩ := hout x hxs hx0
    exact ⟨c, a, b⟩
  · rw [hst] at hx; split_ifs at hx; omega
  · rw [hst] at hx
    split_ifs at hx with h
    · have : x = ⟨src, hs⟩ := Fin.ext (by simp at h ⊢; omega)
      subst this; exact ⟨.nil, by rw [hk0]; exact (wlen_nil _).le⟩
    · exact absurd rfl hx
  · rw [hst] at ha; split_ifs at ha; omega
  · rw [hdone, hset1, htime, hpot]
    change 0 + 65 * (0 + 2 * (marked blank ∅).card + 1) ≤ _
    simp [marked]

/-- The model's final state: the output for a vertex is the least weight of a walk to it from the
source, or `0` if there is none. -/
theorem finish_spec_least (hC : CtxOK C) (hA : AdjOK C G W) (hs : src < G.n) :
    DInv C G W hs (finish C src) ∧ (finish C src).deg 0 = 0 ∧
      (∀ v : Fin G.n, Nonempty (G.graph.Walk ⟨src, hs⟩ v) →
        IsLeast (Set.range fun p : G.graph.Walk ⟨src, hs⟩ v => wlen G p)
          (outVal (finish C src) ((v : ℕ) + 1))) ∧
      (∀ v : Fin G.n, IsEmpty (G.graph.Walk ⟨src, hs⟩ v) →
        outVal (finish C src) ((v : ℕ) + 1) = 0) ∧
      (finish C src).time ≤
        65 + G.n * perVertex C + (∑ v ∈ Finset.range (G.n + 1), (C.adj v).length) * 325 := by
  have h0 := DInv.start hA hs (C := C)
  have hI := whileF_induct (DInv C G W hs) (fun b hb hc => (hb.step hC hA hc).1) C.F _ h0
  have hstop := whileF_stops (DInv C G W hs) (fun b => G.n - (done G.n b).card)
    (fun b hb hc => hb.step hC hA hc) C.F _ h0 (by have := hC.fuel; rw [hA.n_eq] at this; omega)
  simp only [rootsCond, not_not] at hstop
  change DInv C G W hs (finish C src) at hI
  change (finish C src).deg 0 = 0 at hstop
  -- The heap is empty.
  have hempty : ∀ y : Fin G.n, (finish C src).stat ((y : ℕ) + 1) ≠ 1 := by
    intro y hy
    have hm : (y : ℕ) + 1 ∈ hset G.n (finish C src) := mem_hset.2 ⟨by omega, by omega, hy⟩
    obtain ⟨r, hr, hrp, _⟩ := hI.g.heap.forest.root_le _ hm
    have := (hI.g.heap.roots.root r hr hrp (Finset.notMem_empty _)).1
    omega
  refine ⟨hI, hstop, fun v ⟨p⟩ => ?_, fun v hv => ?_, ?_⟩
  · unfold outVal
    split_ifs with h2
    · exact hI.g.settled v h2
    · exact ((no_walk hI.g hI.rel hempty h2).false p).elim
  · unfold outVal
    split_ifs with h2
    · obtain ⟨⟨p, -⟩, -⟩ := hI.g.settled v h2
      exact (hv.false p).elim
    · rfl
  · have hc := hI.cost
    have h1 := card_done_le G.n (finish C src)
    have h2 : ∑ v ∈ done G.n (finish C src), (C.adj v).length ≤
        ∑ v ∈ Finset.range (G.n + 1), (C.adj v).length :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h3 : (done G.n (finish C src)).card * perVertex C ≤ G.n * perVertex C :=
      Nat.mul_le_mul_right _ h1
    have h4 := Nat.mul_le_mul_right 325 h2
    omega

/-- The model's final state, for natural weights: the output for a vertex is its distance. -/
theorem finish_spec {C : Ctx} {G : WGraph} {W : ℕ} (hC : CtxOK C) (hA : AdjOK C G W)
    (hs : src < G.n) :
    DInv C G W hs (finish C src) ∧ (finish C src).deg 0 = 0 ∧
      (∀ v : Fin G.n, outVal (finish C src) ((v : ℕ) + 1) = encDist (G.dist ⟨src, hs⟩ v)) ∧
      (finish C src).time ≤
        65 + G.n * perVertex C + (∑ v ∈ Finset.range (G.n + 1), (C.adj v).length) * 325 := by
  obtain ⟨hI, hstop, hl, hz, ht⟩ := finish_spec_least hC hA hs
  refine ⟨hI, hstop, fun v => ?_, ht⟩
  rcases isEmpty_or_nonempty (G.graph.Walk ⟨src, hs⟩ v) with h | h
  · rw [hz v h, dist_eq_top fun p => h.false p]; rfl
  · rw [← coe_eq_dist (hl v h)]; rfl

omit [CanonicallyOrderedAdd R] in
theorem finish_invalid (hs : C.n ≤ src) : finish C src = blank := by
  simp only [finish, start, if_neg (by omega : ¬src < C.n)]
  exact whileF_stop (by simp [rootsCond, blank])

end Formalgo.Algorithms.ShortestPaths
