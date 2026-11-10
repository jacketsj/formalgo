import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.Heap

/-!
# Moving roots in and out of the root array

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M L : Finset ℕ} {e v : ℕ}

theorem ne_zero_of_mem (h : Forest s M e) {x : ℕ} (hx : x ∈ M) : x ≠ 0 :=
  fun h0 => h.zero (h0 ▸ hx)

/-! ### Appending a loose root -/

theorem Forest.attach_root (h : Forest s M e) (hv : s.par v = 0) : Forest (attach v 0 s) M e :=
  h.congr (by simp only [attach]; rw [← hv, update_eq_self]) rfl rfl rfl
    (fun x hx => by simp [attach, update_of_ne (ne_zero_of_mem h hx)])
    (fun x hx => by simp [attach, update_of_ne (ne_zero_of_mem h hx)]) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun w _ hp => by
      simp only [attach]; rw [update_of_ne (by rintro rfl; exact hp hv)])

omit [LinearOrder R] in
theorem RootList.attach_root (h : RootList s M L) (hvL : v ∈ L) :
    RootList (attach v 0 s) M (L.erase v) := by
  obtain ⟨hvM, hv⟩ := h.loose v hvL
  have hpar0 : update s.par v 0 = s.par := by rw [← hv, update_eq_self]
  have hpar : (attach v 0 s).par = s.par := hpar0
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · rw [hpar]; exact h.loose w (Finset.mem_of_mem_erase hw)
  · simp only [attach, update_self] at hj ⊢
    rw [hpar0]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
      have hne : s.ch 0 j ≠ v := by rintro hc; exact h2 (hc ▸ hvL)
      rw [update_of_ne (Nat.ne_of_lt hj)]
      refine ⟨h1, fun hm => h2 (Finset.mem_of_mem_erase hm), ?_, ?_⟩
      · exact h3
      · rw [update_of_ne hne]; exact h4
    · simp [hvM, hv]
  · rw [hpar] at hp
    simp only [attach, update_self]
    by_cases hw' : w = v
    · subst hw'; simp
    · have hwL : w ∉ L := fun hm => hL (Finset.mem_erase.2 ⟨hw', hm⟩)
      obtain ⟨h1, h2⟩ := h.root w hw hp hwL
      rw [update_of_ne hw', update_of_ne (Nat.ne_of_lt h1)]
      exact ⟨by omega, h2⟩

/-! ### Popping the last root -/

/-- The state after taking the last root out of the array. -/
def popDeg (s : StW R) : StW R := { s with deg := update s.deg 0 (s.deg 0 - 1) }

theorem Forest.popDeg (h : Forest s M e) : Forest (popDeg s) M e :=
  h.congr rfl rfl rfl rfl (fun x hx => by
    simp [ShortestPaths.popDeg, update_of_ne (ne_zero_of_mem h hx)])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

omit [LinearOrder R] in
theorem RootList.popDeg (h : RootList s M L) (hd : s.deg 0 ≠ 0) :
    RootList (popDeg s) M (insert (s.ch 0 (s.deg 0 - 1)) L) := by
  obtain ⟨x1, x2, x3, x4⟩ := h.list (s.deg 0 - 1) (by omega)
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨x1, x3⟩
    · exact h.loose w hw
  · simp only [ShortestPaths.popDeg, update_self] at hj ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h.list j (by omega)
    refine ⟨h1, fun hm => ?_, h3, h4⟩
    rcases Finset.mem_insert.1 hm with hc | hm
    · have := congrArg s.pos hc; rw [h4, x4] at this; omega
    · exact h2 hm
  · simp only [ShortestPaths.popDeg, update_self] at hp ⊢
    obtain ⟨h1, h2⟩ := h.root w hw hp (fun hm => hL (Finset.mem_insert_of_mem hm))
    refine ⟨?_, h2⟩
    have : s.pos w ≠ s.deg 0 - 1 := by
      intro hc; apply hL; rw [← hc, h2]; exact Finset.mem_insert_self _ _
    omega

/-! ### Removing a root from the array -/

theorem Forest.detach_root (h : Forest s M e)
    (hlast : s.par (s.ch 0 (s.deg 0 - 1)) = 0) : Forest (detach v 0 s) M e :=
  h.congr rfl rfl rfl rfl (fun x hx => by simp [detach, update_of_ne (ne_zero_of_mem h hx)])
    (fun x hx => by simp [detach, update_of_ne (ne_zero_of_mem h hx)]) (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun w _ hp => by
      simp only [detach]; rw [update_of_ne (by rintro rfl; exact hp hlast)])

omit [LinearOrder R] in
theorem RootList.detach_root (h : RootList s M L) (hvM : v ∈ M) (hv : s.par v = 0)
    (hvL : v ∉ L) : RootList (detach v 0 s) M (insert v L) := by
  obtain ⟨v1, v2⟩ := h.root v hvM hv hvL
  set d := s.deg 0 with hd
  have hd0 : d ≠ 0 := by omega
  obtain ⟨x1, x2, x3, x4⟩ := h.list (d - 1) (by omega)
  set x := s.ch 0 (d - 1) with hx
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hvM, hv⟩
    · exact h.loose w hw
  · simp only [detach, update_self] at hj ⊢
    rw [← hd] at hj ⊢
    by_cases hjv : j = s.pos v
    · subst hjv
      have hxv : x ≠ v := by
        intro hc; have := congrArg s.pos hc; rw [x4] at this; omega
      simp only [update_self]
      refine ⟨x1, fun hm => ?_, x3, by simp⟩
      rcases Finset.mem_insert.1 hm with hc | hm
      · exact hxv hc
      · exact x2 hm
    · obtain ⟨h1, h2, h3, h4⟩ := h.list j (by omega)
      have hcx : s.ch 0 j ≠ x := by intro hc; have := congrArg s.pos hc; rw [h4, x4] at this; omega
      rw [update_of_ne hjv, update_of_ne hcx]
      refine ⟨h1, fun hm => ?_, h3, h4⟩
      rcases Finset.mem_insert.1 hm with hc | hm
      · have := congrArg s.pos hc; rw [h4] at this; exact hjv this
      · exact h2 hm
  · simp only [detach, update_self] at hp ⊢
    rw [← hd]
    have hwv : w ≠ v := fun hc => hL (hc ▸ Finset.mem_insert_self _ _)
    obtain ⟨h1, h2⟩ := h.root w hw hp (fun hm => hL (Finset.mem_insert_of_mem hm))
    by_cases hwx : w = x
    · rw [hwx, update_self, update_self]
      have hxv : x ≠ v := hwx ▸ hwv
      have : s.pos v ≠ d - 1 := by intro hc; rw [hc, ← hx] at v2; exact hxv v2
      exact ⟨by omega, rfl⟩
    · rw [update_of_ne hwx]
      have hpv : s.pos w ≠ s.pos v := by intro hc; rw [← h2, hc, v2] at hwv; exact hwv rfl
      have hpx : s.pos w ≠ d - 1 := by intro hc; rw [hc] at h2; exact hwx h2.symm
      rw [update_of_ne hpv]
      exact ⟨by omega, h2⟩

/-! ### Adding a fresh root, and removing a childless one -/

theorem Forest.insert_fresh (h : Forest s M e) (hvM : v ∉ M) (hv0 : v ≠ 0) (hv : s.par v = 0)
    (hd : s.deg v = 0) (hm : s.mark v ≤ 1) : Forest s (insert v M) e := by
  have hold : ∀ w ∈ M, s.par w ≠ 0 → older s (insert v M) w = older s M w := by
    intro w _ hp
    unfold older; rw [Finset.filter_insert, if_neg (by rw [hv]; exact fun h => hp h.1.symm)]
  refine ⟨?_, fun w hw hp => ?_, fun x hx j hj => ?_, fun w hw hp => ?_, fun w hw hp => ?_,
    fun w hw hp he => ?_, fun w hw w' hw' hp => ?_, fun w hw hp => ?_, fun w hw => ?_⟩
  · simp [hv0.symm, h.zero]
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · obtain ⟨h1, h2, h3⟩ := h.up w hw hp; exact ⟨Finset.mem_insert_of_mem h1, h2, h3⟩
  · rcases Finset.mem_insert.1 hx with rfl | hx
    · omega
    · obtain ⟨h1, h2, h3⟩ := h.down x hx j hj; exact ⟨Finset.mem_insert_of_mem h1, h2, h3⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · exact h.order w hw hp
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · exact h.height w hw hp
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · rw [hold w hw hp]; exact h.fib w hw hp he
  · intro hpp hlt
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [hv] at hpp; exact absurd hpp.symm hp
      · exact h.ltinj w hw w' hw' hp hpp hlt
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd hv hp
    · exact h.ltclock w hw hp
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hm
    · exact h.mark w hw

omit [LinearOrder R] in
theorem RootList.insert_fresh (h : RootList s M L) (hvM : v ∉ M) (hv : s.par v = 0) :
    RootList s (insert v M) (insert v L) := by
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨Finset.mem_insert_self _ _, hv⟩
    · exact ⟨Finset.mem_insert_of_mem (h.loose w hw).1, (h.loose w hw).2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
    refine ⟨Finset.mem_insert_of_mem h1, fun hm => ?_, h3, h4⟩
    rcases Finset.mem_insert.1 hm with hc | hm
    · exact hvM (hc ▸ h1)
    · exact h2 hm
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact absurd (Finset.mem_insert_self _ _) hL
    · exact h.root w hw hp (fun hm => hL (Finset.mem_insert_of_mem hm))

/-- Removing a root without children. -/
theorem Forest.erase_root (h : Forest s M e) (hvM : v ∈ M) (hv : s.par v = 0) (hd : s.deg v = 0) :
    Forest s (M.erase v) e := by
  have hnc : ∀ w ∈ M, s.par w ≠ v := by
    intro w hw hc
    have hp : s.par w ≠ 0 := by rw [hc]; exact ne_zero_of_mem h hvM
    have := (h.up w hw hp).2.1; rw [hc, hd] at this; omega
  have hold : ∀ w ∈ M, s.par w ≠ 0 → older s (M.erase v) w ≤ older s M w := fun w _ _ =>
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
  refine ⟨fun h0 => h.zero (Finset.mem_of_mem_erase h0), fun w hw hp => ?_, fun x hx j hj => ?_,
    fun w hw hp => h.order w (Finset.mem_of_mem_erase hw) hp,
    fun w hw hp => h.height w (Finset.mem_of_mem_erase hw) hp, fun w hw hp he => ?_,
    fun w hw w' hw' hp =>
      h.ltinj w (Finset.mem_of_mem_erase hw) w' (Finset.mem_of_mem_erase hw') hp,
    fun w hw hp => h.ltclock w (Finset.mem_of_mem_erase hw) hp,
    fun w hw => h.mark w (Finset.mem_of_mem_erase hw)⟩
  · have hwM := Finset.mem_of_mem_erase hw
    obtain ⟨h1, h2, h3⟩ := h.up w hwM hp
    exact ⟨Finset.mem_erase.2 ⟨hnc w hwM, h1⟩, h2, h3⟩
  · have hxM := Finset.mem_of_mem_erase hx
    obtain ⟨h1, h2, h3⟩ := h.down x hxM j hj
    refine ⟨Finset.mem_erase.2 ⟨fun hc => ?_, h1⟩, h2, h3⟩
    rw [hc, hv] at h2; exact ne_zero_of_mem h hxM h2.symm
  · have hwM := Finset.mem_of_mem_erase hw
    exact (hold w hwM hp).trans (h.fib w hwM hp he)

omit [LinearOrder R] in
theorem RootList.erase_root (h : RootList s M L) (hvL : v ∈ L) :
    RootList s (M.erase v) (L.erase v) := by
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · obtain ⟨h1, h2⟩ := h.loose w (Finset.mem_of_mem_erase hw)
    exact ⟨Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hw, h1⟩, h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
    have hne : s.ch 0 j ≠ v := fun hc => h2 (hc ▸ hvL)
    exact ⟨Finset.mem_erase.2 ⟨hne, h1⟩, fun hm => h2 (Finset.mem_of_mem_erase hm), h3, h4⟩
  · exact h.root w (Finset.mem_of_mem_erase hw) hp
      (fun hm => hL (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hw, hm⟩))

end Formalgo.Algorithms.ShortestPaths
