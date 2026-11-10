import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapDecKey
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.Fib

/-!
# Extracting the minimum: removing it and moving its children

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s s' : StW R} {M L : Finset ℕ} {e v p z : ℕ}

/-- Keys, statuses, and nodes outside `M` are left alone. -/
structure Keep (M : Finset ℕ) (s s' : StW R) : Prop where
  key : s'.key = s.key
  stat : s'.stat = s.stat
  out : ∀ w ∉ M, w ≠ 0 → s'.deg w = s.deg w ∧ s'.mark w = s.mark w ∧ s'.par w = s.par w

omit [LinearOrder R] in
theorem Keep.refl : Keep M s s := ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

omit [LinearOrder R] in
theorem Keep.trans {s'' : StW R} (h : Keep M s s') (h' : Keep M s' s'') : Keep M s s'' :=
  ⟨h'.key.trans h.key, h'.stat.trans h.stat, fun w hw h0 => by
    obtain ⟨a, b, c⟩ := h.out w hw h0; obtain ⟨a', b', c'⟩ := h'.out w hw h0
    exact ⟨a'.trans a, b'.trans b, c'.trans c⟩⟩

omit [LinearOrder R] in
theorem Keep.mono {M' : Finset ℕ} (h : Keep M' s s') (hM : M' ⊆ M) : Keep M s s' :=
  ⟨h.key, h.stat, fun w hw h0 => h.out w (fun hm => hw (hM hm)) h0⟩

omit [LinearOrder R] in
theorem Keep.tick (h : Keep M s s') (c : ℕ) : Keep M s (tick c s') := ⟨h.key, h.stat, h.out⟩

/-! ### The potential under moves -/

omit [LinearOrder R] in
theorem marked_moveRoot : marked (moveRoot v p s) M ⊆ marked s M := by
  intro w hw
  simp only [marked, Finset.mem_filter, moveRoot_par, moveRoot_mark] at hw ⊢
  obtain ⟨h1, h2, h3⟩ := hw
  rcases eq_or_ne w v with rfl | hwv
  · simp at h2
  · rw [update_of_ne hwv] at h2; exact ⟨h1, h2, h3⟩

omit [LinearOrder R] in
theorem pot_moveRoot (hp : p ≠ 0) : pot (moveRoot v p s) M ≤ pot s M + 1 := by
  have h1 := Finset.card_le_card (marked_moveRoot (v := v) (p := p) (s := s) (M := M))
  simp only [pot]; rw [moveRoot_deg _ _ _ hp, update_self]; omega

omit [LinearOrder R] in
theorem pot_erase_root (hz : s.par z = 0) : pot s (M.erase z) = pot s M := by
  have : marked s (M.erase z) = marked s M := by
    ext w; simp only [marked, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨by rintro rfl; exact h'.1 hz, h⟩, h'⟩
  simp only [pot, this]

/-! ### Removing the minimum from the root array -/

theorem detach_min (hH : HeapInv n s M) (hne : M.Nonempty) :
    Forest (detach s.hmin 0 s) M 0 ∧ RootList (detach s.hmin 0 s) M {s.hmin} ∧
      (detach s.hmin 0 s).par s.hmin = 0 ∧ pot (detach s.hmin 0 s) M + 1 = pot s M ∧
      (detach s.hmin 0 s).time = s.time ∧ (detach s.hmin 0 s).tbl = s.tbl ∧
      Keep M s (detach s.hmin 0 s) := by
  obtain ⟨m1, m2, _⟩ := hH.min hne
  obtain ⟨r1, _⟩ := hH.roots.root _ m1 m2 (Finset.notMem_empty _)
  have hlast := (hH.roots.list (s.deg 0 - 1) (by omega)).2.2.1
  refine ⟨hH.forest.detach_root hlast,
    (by simpa using hH.roots.detach_root m1 m2 (Finset.notMem_empty _)), m2, ?_, rfl, rfl, rfl, rfl,
    fun w _ h0 => ⟨?_, rfl, rfl⟩⟩
  · have hm : marked (detach s.hmin 0 s) M = marked s M := rfl
    change update s.deg 0 (s.deg 0 - 1) 0 + 2 * (marked (detach s.hmin 0 s) M).card + 1 =
      s.deg 0 + 2 * (marked s M).card
    rw [hm, update_self]; omega
  · change update s.deg 0 (s.deg 0 - 1) w = s.deg w; rw [update_of_ne h0]

/-! ### Moving the children of the minimum -/

omit [LinearOrder R] in
theorem moveStep_fst (_hz : z ≠ 0) (hpos : s.pos (s.ch z (s.deg z - 1)) = s.deg z - 1) :
    (moveStep (s, z)).1 = tick 30 (moveRoot (s.ch z (s.deg z - 1)) z s) := by
  have hX : update (s.ch z) (s.pos (s.ch z (s.deg z - 1))) (s.ch z (s.deg z - 1)) = s.ch z := by
    rw [hpos, update_eq_self]
  have e1 : (moveStep (s, z)).1 = tick 30 (attach (s.ch z (update s.deg z (s.deg z - 1) z)) 0
      { s with deg := update s.deg z (s.deg z - 1) }) := rfl
  rw [e1, update_self]
  refine StW.ext rfl rfl rfl ?_ rfl ?_ rfl ?_ rfl rfl rfl rfl rfl
  · change update (update s.deg z (s.deg z - 1)) 0 (update s.deg z (s.deg z - 1) 0 + 1) =
      update (update s.deg z (s.deg z - 1)) 0 (update s.deg z (s.deg z - 1) 0 + 1)
    rfl
  · change update s.pos (s.ch z (s.deg z - 1)) (update s.deg z (s.deg z - 1) 0) =
      update (update s.pos (s.ch z (s.deg z - 1)) (s.pos (s.ch z (s.deg z - 1))))
        (s.ch z (s.deg z - 1)) (update s.deg z (s.deg z - 1) 0)
    rw [update_eq_self]
  · change update s.ch 0 (update (s.ch 0) (update s.deg z (s.deg z - 1) 0) (s.ch z (s.deg z - 1))) =
      update (update s.ch z (update (s.ch z) (s.pos (s.ch z (s.deg z - 1)))
        (s.ch z (s.deg z - 1)))) 0
        (update (update s.ch z (update (s.ch z) (s.pos (s.ch z (s.deg z - 1)))
          (s.ch z (s.deg z - 1))) 0) (update s.deg z (s.deg z - 1) 0) (s.ch z (s.deg z - 1)))
    rw [hX, update_eq_self]

/-- The invariant of the moves. -/
structure MoveInv (M : Finset ℕ) (z Q : ℕ) (s₀ : StW R) (a : StW R × ℕ) : Prop where
  z_eq : a.2 = z
  zM : z ∈ M
  forest : Forest a.1 M 0
  roots : RootList a.1 M {z}
  zpar : a.1.par z = 0
  cost : a.1.time + 65 * pot a.1 M + 95 * a.1.deg z ≤ Q
  keep : Keep M s₀ a.1
  tbl : a.1.tbl = s₀.tbl

theorem MoveInv.step {Q : ℕ} {s₀ : StW R} {a : StW R × ℕ} (h : MoveInv M z Q s₀ a)
    (hc : moveCond a) :
    MoveInv M z Q s₀ (moveStep a) ∧ (moveStep a).1.deg z < a.1.deg z := by
  obtain ⟨s, z'⟩ := a
  obtain ⟨hz, hzM, hF, hR, hzp, hQ, hk, ht⟩ := h
  simp only at hz hF hR hzp hQ hk ht
  subst hz
  simp only [moveCond] at hc
  have hz0 : z' ≠ 0 := ne_zero_of_mem hF hzM
  obtain ⟨c1, c2, c3⟩ := hF.down z' hzM (s.deg z' - 1) (by omega)
  have hf : CutFacts s M (s.ch z' (s.deg z' - 1)) z' := by
    have := hF.cutFacts c1 (by rw [c2]; exact hz0); rwa [c2] at this
  have hcz : s.ch z' (s.deg z' - 1) ≠ z' := by intro hc'; rw [hc', hzp] at c2; exact hz0 c2.symm
  have he : moveStep (s, z') = (tick 30 (moveRoot (s.ch z' (s.deg z' - 1)) z' s), z') := by
    rw [← moveStep_fst hz0 c3]; rfl
  rw [he]
  have hd : (moveRoot (s.ch z' (s.deg z' - 1)) z' s).deg z' = s.deg z' - 1 := moveRoot_deg_p hz0
  have hpot := pot_moveRoot (v := s.ch z' (s.deg z' - 1)) (s := s) (M := M) hz0
  refine ⟨⟨rfl, hzM, ((hF.move_root hf (.inl rfl)).of_root (by
      rw [moveRoot_par, update_of_ne hcz.symm]; exact hzp)).tick 30,
    (hR.move_root hf).tick 30, by
      change update s.par _ 0 z' = 0; rw [update_of_ne hcz.symm]; exact hzp, ?_,
    hk.trans ⟨rfl, rfl, fun w hw h0 => ?_⟩, ht⟩, by
      change (moveRoot (s.ch z' (s.deg z' - 1)) z' s).deg z' < s.deg z'; rw [hd]; omega⟩
  · change s.time + 30 + 65 * pot (moveRoot _ z' s) M +
      95 * (moveRoot _ z' s).deg z' ≤ Q
    rw [hd]; omega
  · have hwc : w ≠ s.ch z' (s.deg z' - 1) := fun hc' => hw (hc' ▸ c1)
    have hwz : w ≠ z' := fun hc' => hw (hc' ▸ hzM)
    refine ⟨?_, rfl, ?_⟩
    · change (moveRoot _ z' s).deg w = s.deg w
      rw [moveRoot_deg _ _ _ hz0, update_of_ne h0, update_of_ne hwz]
    · change update s.par _ 0 w = s.par w; rw [update_of_ne hwc]

/-- After the moves. -/
theorem move_loop (C : CtxW R) {Q : ℕ} {s₀ : StW R} {a : StW R × ℕ} (h : MoveInv M z Q s₀ a)
    (hFu : a.1.deg z ≤ C.F) :
    MoveInv M z Q s₀ (whileF moveCond moveStep C.F a) ∧
      (whileF moveCond moveStep C.F a).1.deg z = 0 := by
  have hI := whileF_induct (MoveInv M z Q s₀) (fun b hb hc => (hb.step hc).1) C.F a h
  have hs := whileF_stops (MoveInv M z Q s₀) (fun b => b.1.deg z) (fun b hb hc => hb.step hc)
    C.F a h hFu
  refine ⟨hI, ?_⟩
  simp only [moveCond, not_not] at hs
  rw [hI.z_eq] at hs; exact hs

end Formalgo.Algorithms.ShortestPaths
