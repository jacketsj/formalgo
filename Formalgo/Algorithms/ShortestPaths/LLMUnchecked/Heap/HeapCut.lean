import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapLink

/-!
# Cutting a node to the roots

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M L : Finset ℕ} {e v p : ℕ}

/-- Move `v` from the children of `p` to the root array. -/
def moveRoot (v p : ℕ) (s : StW R) : StW R := attach v 0 (detach v p s)

section
variable (v p s)
omit [LinearOrder R] in
theorem moveRoot_par : (moveRoot v p s).par = update s.par v 0 := rfl
omit [LinearOrder R] in
theorem moveRoot_deg (hp : p ≠ 0) :
    (moveRoot v p s).deg = update (update s.deg p (s.deg p - 1)) 0 (s.deg 0 + 1) := by
  simp [moveRoot, attach, detach, update_of_ne hp.symm]
omit [LinearOrder R] in
theorem moveRoot_pos (hp : p ≠ 0) : (moveRoot v p s).pos =
    update (update s.pos (s.ch p (s.deg p - 1)) (s.pos v)) v (s.deg 0) := by
  simp [moveRoot, attach, detach, update_of_ne hp.symm]
omit [LinearOrder R] in
theorem moveRoot_ch (hp : p ≠ 0) : (moveRoot v p s).ch =
    update (update s.ch p (update (s.ch p) (s.pos v) (s.ch p (s.deg p - 1)))) 0
      (update (s.ch 0) (s.deg 0) v) := by
  simp [moveRoot, attach, detach, update_of_ne hp.symm]
omit [LinearOrder R] in
theorem moveRoot_key : (moveRoot v p s).key = s.key := rfl
omit [LinearOrder R] in
theorem moveRoot_ht : (moveRoot v p s).ht = s.ht := rfl
omit [LinearOrder R] in
theorem moveRoot_lt : (moveRoot v p s).lt = s.lt := rfl
omit [LinearOrder R] in
theorem moveRoot_clock : (moveRoot v p s).clock = s.clock := rfl
omit [LinearOrder R] in
theorem moveRoot_mark : (moveRoot v p s).mark = s.mark := rfl
end

/-- Facts about `v`, its parent and the parent's last child. -/
structure CutFacts (s : StW R) (M : Finset ℕ) (v p : ℕ) : Prop where
  vM : v ∈ M
  pM : p ∈ M
  p0 : p ≠ 0
  vp : s.par v = p
  i_lt : s.pos v < s.deg p
  chv : s.ch p (s.pos v) = v
  lastM : s.ch p (s.deg p - 1) ∈ M
  lastp : s.par (s.ch p (s.deg p - 1)) = p
  lastpos : s.pos (s.ch p (s.deg p - 1)) = s.deg p - 1

theorem Forest.cutFacts (h : Forest s M e) (hv : v ∈ M) (hp : s.par v ≠ 0) :
    CutFacts s M v (s.par v) := by
  obtain ⟨h1, h2, h3⟩ := h.up v hv hp
  obtain ⟨l1, l2, l3⟩ := h.down _ h1 (s.deg (s.par v) - 1) (by omega)
  exact ⟨hv, h1, hp, rfl, h2, h3, l1, l2, l3⟩

omit [LinearOrder R] in
theorem older_moveRoot_le {w : ℕ} (hw : w ≠ v) (hwp : s.par w ≠ 0) :
    older (moveRoot v p s) M w ≤ older s M w := by
  refine Finset.card_le_card fun c hc => ?_
  simp only [Finset.mem_filter, moveRoot_par, moveRoot_lt] at hc ⊢
  obtain ⟨hcM, hcp, hcl⟩ := hc
  rw [update_of_ne hw] at hcp
  by_cases hcv : c = v
  · subst hcv; rw [update_self] at hcp; exact absurd hcp.symm hwp
  · rw [update_of_ne hcv] at hcp; exact ⟨hcM, hcp, hcl⟩

theorem Forest.move_root (h : Forest s M e) (hf : CutFacts s M v p) (he : e = 0 ∨ e = v) :
    Forest (moveRoot v p s) M p := by
  obtain ⟨vM, pM, p0, vp, i_lt, chv, lastM, lastp, lastpos⟩ := hf
  set d := s.deg p with hd
  set i := s.pos v with hi
  set last := s.ch p (d - 1) with hlast
  have hv0 : v ≠ 0 := ne_zero_of_mem h vM
  have hpv : p ≠ v := by
    rintro rfl; have := h.height _ vM (by rw [vp]; exact p0); rw [vp] at this; omega
  have hlv : last ≠ v → i ≠ d - 1 := fun hne hc => hne (by rw [hlast, ← hc, chv])
  have hpar : ∀ w, w ≠ v → (moveRoot v p s).par w = s.par w := fun w hw => by
    rw [moveRoot_par, update_of_ne hw]
  have hposw : ∀ w, w ≠ v → w ≠ last → (moveRoot v p s).pos w = s.pos w := fun w hw hwl => by
    rw [moveRoot_pos _ _ _ p0, update_of_ne hw, update_of_ne hwl]
  have hdegp : (moveRoot v p s).deg p = d - 1 := by
    rw [moveRoot_deg _ _ _ p0, update_of_ne p0, update_self]
  have hdegx : ∀ x, x ≠ p → x ≠ 0 → (moveRoot v p s).deg x = s.deg x := fun x hx hx0 => by
    rw [moveRoot_deg _ _ _ p0, update_of_ne hx0, update_of_ne hx]
  have hchp : (moveRoot v p s).ch p = update (s.ch p) i last := by
    rw [moveRoot_ch _ _ _ p0, update_of_ne p0, update_self]
  have hchx : ∀ x, x ≠ p → x ≠ 0 → (moveRoot v p s).ch x = s.ch x := fun x hx hx0 => by
    rw [moveRoot_ch _ _ _ p0, update_of_ne hx0, update_of_ne hx]
  refine ⟨h.zero, fun w hw hp => ?_, fun x hx j hj => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun w hw hp hwp => ?_, fun w hw w' hw' hp => ?_, fun w hw hp => ?_,
    fun w hw => ?_⟩
  · -- up
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    rw [hpar w hwv] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := h.up w hw hp
    by_cases hwl : w = last
    · have hlv' : last ≠ v := hwl ▸ hwv
      have hil := hlv hlv'
      rw [hwl, lastp, moveRoot_pos _ _ _ p0, update_of_ne hlv', update_self, hdegp, hchp,
        update_self]
      exact ⟨pM, by omega, rfl⟩
    · rw [hposw w hwv hwl]
      by_cases hwp : s.par w = p
      · rw [hwp] at h2 h3 ⊢
        have hne1 : s.pos w ≠ d - 1 := fun hc => hwl (by rw [hlast, ← hc, h3])
        have hne2 : s.pos w ≠ i := fun hc => hwv (by rw [← h3, hc, chv])
        rw [hdegp, hchp, update_of_ne hne2]
        exact ⟨pM, by omega, h3⟩
      · rw [hdegx _ hwp hp, hchx _ hwp hp]; exact ⟨h1, h2, h3⟩
  · -- down
    have hx0 := ne_zero_of_mem h hx
    by_cases hxp : x = p
    · subst hxp
      rw [hdegp] at hj
      rw [hchp]
      by_cases hji : j = i
      · subst hji
        have hlv' : last ≠ v := fun hc => by
          have := congrArg s.pos hc; rw [lastpos] at this; omega
        rw [update_self, hpar _ hlv', moveRoot_pos _ _ _ p0, update_of_ne hlv', update_self]
        exact ⟨lastM, lastp, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := h.down x hx j (by omega)
        have hcv : s.ch x j ≠ v := fun hc => hji (by rw [← h3, hc])
        have hcl : s.ch x j ≠ last := fun hc => by
          have := congrArg s.pos hc; rw [h3, lastpos] at this; omega
        rw [update_of_ne hji, hpar _ hcv, hposw _ hcv hcl]
        exact ⟨h1, h2, h3⟩
    · rw [hdegx x hxp hx0] at hj
      obtain ⟨h1, h2, h3⟩ := h.down x hx j hj
      have hcv : s.ch x j ≠ v := fun hc => hxp (by rw [← h2, hc, vp])
      have hcl : s.ch x j ≠ last := fun hc => hxp (by rw [← h2, hc, lastp])
      rw [hchx x hxp hx0, hpar _ hcv, hposw _ hcv hcl]
      exact ⟨h1, h2, h3⟩
  · -- order
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    rw [hpar w hwv] at hp ⊢; exact h.order w hw hp
  · -- height
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    rw [hpar w hwv] at hp ⊢; exact h.height w hw hp
  · -- fib
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    have hw0 : w ≠ 0 := ne_zero_of_mem h hw
    rw [hpar w hwv] at hp
    have hwe : w ≠ e := by rcases he with rfl | rfl <;> assumption
    rw [hdegx w hwp hw0, moveRoot_mark]
    exact (older_moveRoot_le hwv hp).trans (h.fib w hw hp hwe)
  · -- ltinj
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    intro hpp hll
    rw [hpar w hwv] at hp hpp
    have hw'v : w' ≠ v := by
      rintro rfl; rw [moveRoot_par, update_self] at hpp; exact hp hpp.symm
    rw [hpar w' hw'v] at hpp
    exact h.ltinj w hw w' hw' hp hpp hll
  · -- ltclock
    have hwv : w ≠ v := by rintro rfl; rw [moveRoot_par, update_self] at hp; exact hp rfl
    rw [hpar w hwv] at hp; exact h.ltclock w hw hp
  · exact h.mark w hw

omit [LinearOrder R] in
theorem RootList.move_root (h : RootList s M L) (hf : CutFacts s M v p) :
    RootList (moveRoot v p s) M L := by
  obtain ⟨vM, pM, p0, vp, i_lt, chv, lastM, lastp, lastpos⟩ := hf
  have hvL : v ∉ L := fun hm => p0 (by rw [← vp]; exact (h.loose v hm).2)
  have hpar : ∀ w, w ≠ v → (moveRoot v p s).par w = s.par w := fun w hw => by
    rw [moveRoot_par, update_of_ne hw]
  have hdeg0 : (moveRoot v p s).deg 0 = s.deg 0 + 1 := by
    rw [moveRoot_deg _ _ _ p0, update_self]
  have hch0 : (moveRoot v p s).ch 0 = update (s.ch 0) (s.deg 0) v := by
    rw [moveRoot_ch _ _ _ p0, update_self]
  -- Roots are neither `v` nor the last child of `p`.
  have hroot : ∀ w, s.par w = 0 → (moveRoot v p s).pos w = s.pos w := fun w hw => by
    have h1 : w ≠ v := by rintro rfl; rw [vp] at hw; exact p0 hw
    have h2 : w ≠ s.ch p (s.deg p - 1) := by rintro rfl; rw [lastp] at hw; exact p0 hw
    rw [moveRoot_pos _ _ _ p0, update_of_ne h1, update_of_ne h2]
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · have hwv : w ≠ v := fun hc => hvL (hc ▸ hw)
    rw [hpar w hwv]; exact h.loose w hw
  · rw [hdeg0] at hj; rw [hch0]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
      have hcv : s.ch 0 j ≠ v := by intro hc; rw [hc, vp] at h3; exact p0 h3
      rw [update_of_ne (Nat.ne_of_lt hj), hpar _ hcv, hroot _ h3]
      exact ⟨h1, h2, h3, h4⟩
    · rw [update_self, moveRoot_par, update_self, moveRoot_pos _ _ _ p0, update_self]
      exact ⟨vM, hvL, rfl, rfl⟩
  · by_cases hwv : w = v
    · subst hwv
      rw [moveRoot_pos _ _ _ p0, update_self, hdeg0, hch0, update_self]
      exact ⟨by omega, rfl⟩
    · rw [hpar w hwv] at hp
      obtain ⟨h1, h2⟩ := h.root w hw hp hL
      rw [hroot w hp, hdeg0, hch0, update_of_ne (Nat.ne_of_lt h1)]
      exact ⟨by omega, h2⟩

omit [LinearOrder R] in
theorem moveRoot_deg_p (hp : p ≠ 0) : (moveRoot v p s).deg p = s.deg p - 1 := by
  rw [moveRoot_deg _ _ _ hp, update_of_ne hp, update_self]

end Formalgo.Algorithms.ShortestPaths
