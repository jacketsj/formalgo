import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapCut

/-!
# Marks, keys, and the cascade of cuts

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M L : Finset ℕ} {e v p : ℕ}

/-- The marked nodes that are not roots. -/
def marked (s : StW R) (M : Finset ℕ) : Finset ℕ := M.filter fun w => s.par w ≠ 0 ∧ s.mark w = 1

/-- The potential: roots in the array, and twice the marked non-roots. -/
def pot (s : StW R) (M : Finset ℕ) : ℕ := s.deg 0 + 2 * (marked s M).card

omit [LinearOrder R] in
theorem cut_eq (v p : ℕ) (s : StW R) : cut v p s = setMark v 0 (moveRoot v p s) := rfl

theorem Forest.tick (h : Forest s M e) (c : ℕ) : Forest (tick c s) M e :=
  h.congr rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

omit [LinearOrder R] in
theorem RootList.tick (h : RootList s M L) (c : ℕ) : RootList (tick c s) M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

/-! ### Marks and keys -/

theorem Forest.setMark_root (h : Forest s M e) (hv : s.par v = 0) :
    Forest (setMark v 0 s) M e :=
  { h with
    fib := fun w hw hp hwe => by
      have hwv : w ≠ v := by rintro rfl; exact hp hv
      have := h.fib w hw hp hwe
      simp only [setMark, older] at this ⊢; rw [update_of_ne hwv]; exact this
    mark := fun w hw => by
      simp only [setMark]; rcases eq_or_ne w v with rfl | hwv
      · simp
      · rw [update_of_ne hwv]; exact h.mark w hw }

omit [LinearOrder R] in
theorem RootList.setMark (h : RootList s M L) (v k : ℕ) : RootList (setMark v k s) M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

theorem Forest.setMark_one (h : Forest s M p) (hpM : p ∈ M) (hm : s.mark p = 0)
    (hold : older s M p ≤ s.deg p + 1) : Forest (setMark p 1 s) M 0 :=
  { h with
    fib := fun w hw hp _ => by
      change s.par w ≠ 0 at hp
      change older s M w ≤ s.deg w + update s.mark p 1 w
      rcases eq_or_ne w p with rfl | hwp
      · rw [update_self]; exact hold
      · rw [update_of_ne hwp]; exact h.fib w hw hp hwp
    mark := fun w hw => by
      simp only [setMark]; rcases eq_or_ne w p with rfl | hwp
      · simp
      · rw [update_of_ne hwp]; exact h.mark w hw }

theorem Forest.setKey (h : Forest s M e) (hv : v ∈ M) {nk : R} (hnk : nk ≤ s.key v)
    (hp : s.par v = 0 ∨ s.key (s.par v) ≤ nk) : Forest (setKey v nk s) M e :=
  { h with
    order := fun w hw hpw => by
      change s.par w ≠ 0 at hpw
      change update s.key v nk (s.par w) ≤ update s.key v nk w
      have := h.order w hw hpw
      rcases eq_or_ne w v with rfl | hwv
      · rcases hp with hp | hp
        · exact absurd hp hpw
        · have hpv : s.par w ≠ w := by
            intro hc; have := h.height w hw hpw; rw [hc] at this; omega
          rw [update_self, update_of_ne hpv]; exact hp
      · rw [update_of_ne hwv]
        rcases eq_or_ne (s.par w) v with hpv | hpv
        · rw [hpv, update_self]; rw [hpv] at this; exact hnk.trans this
        · rw [update_of_ne hpv]; exact this }

omit [LinearOrder R] in
theorem RootList.setKey (h : RootList s M L) (v : ℕ) (k : R) : RootList (setKey v k s) M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

/-! ### Marked nodes under a cut -/

omit [LinearOrder R] in
theorem marked_cut (_hp : p ≠ 0) : marked (cut v p s) M = (marked s M).erase v := by
  ext w
  simp only [marked, cut_eq, Finset.mem_filter, Finset.mem_erase, setMark, moveRoot_par,
    moveRoot_mark]
  rcases eq_or_ne w v with rfl | hwv
  · simp
  · simp [hwv]

omit [LinearOrder R] in
theorem marked_setMark_one : marked (setMark p 1 s) M ⊆ insert p (marked s M) := by
  intro w hw
  simp only [marked, setMark, Finset.mem_filter, Finset.mem_insert] at hw ⊢
  rcases eq_or_ne w p with rfl | hwp
  · exact .inl rfl
  · rw [update_of_ne hwp] at hw; exact .inr hw

omit [LinearOrder R] in
theorem cut_deg0 (hp : p ≠ 0) : (cut v p s).deg 0 = s.deg 0 + 1 := by
  rw [cut_eq]; simp only [setMark]; rw [moveRoot_deg _ _ _ hp, update_self]

/-! ### The cascade -/

/-- The invariant of the cascade at `(s, p)`. -/
structure CascInv (M : Finset ℕ) (Q : ℕ) (a : StW R × ℕ) : Prop where
  forest : Forest a.1 M a.2
  roots : RootList a.1 M ∅
  pM : a.2 ∈ M
  slack : a.1.par a.2 ≠ 0 → older a.1 M a.2 ≤ a.1.deg a.2 + a.1.mark a.2 + 1
  cost : a.1.time + 65 * pot a.1 M ≤ Q

theorem CascInv.step {Q : ℕ} {a : StW R × ℕ} (h : CascInv M Q a) (hc : cascCond a) :
    CascInv M Q (cascStep a) ∧ (marked (cascStep a).1 M).card < (marked a.1 M).card := by
  obtain ⟨s, p⟩ := a
  obtain ⟨hF, hR, hpM, hsl, hQ⟩ := h
  obtain ⟨hp0, hm⟩ := hc
  simp only at hF hR hpM hsl hQ hp0 hm
  have hf := hF.cutFacts hpM hp0
  have hstep : cascStep (s, p) = (St.tick 50 (cut p (s.par p) s), s.par p) := rfl
  rw [hstep]
  have hF' : Forest (cut p (s.par p) s) M (s.par p) := by
    rw [cut_eq]
    exact (hF.move_root hf (.inr rfl)).setMark_root (by rw [moveRoot_par, update_self])
  have hR' : RootList (cut p (s.par p) s) M ∅ := by
    rw [cut_eq]; exact (hR.move_root hf).setMark _ _
  have hgp : s.par p ∈ M := hf.pM
  have hpmk : p ∈ marked s M := by simp [marked, hpM, hp0, hm]
  have hmk : marked (cut p (s.par p) s) M = (marked s M).erase p := marked_cut hp0
  have hcard := Finset.card_erase_of_mem hpmk
  have hpos := Finset.card_pos.2 ⟨p, hpmk⟩
  refine ⟨⟨hF'.tick 50, hR'.tick 50, hgp, fun hgp0 => ?_, ?_⟩, ?_⟩
  · -- The grandparent has lost one child.
    change (cut p (s.par p) s).par (s.par p) ≠ 0 at hgp0
    change older (cut p (s.par p) s) M (s.par p) ≤
      (cut p (s.par p) s).deg (s.par p) + (cut p (s.par p) s).mark (s.par p) + 1
    have hgpp : s.par p ≠ p := fun hc => by
      have := hF.height p hpM hp0; rw [hc] at this; omega
    have hpar' : (cut p (s.par p) s).par (s.par p) = s.par (s.par p) := by
      rw [cut_eq]; simp only [setMark]; rw [moveRoot_par, update_of_ne hgpp]
    rw [hpar'] at hgp0
    have h1 : older (cut p (s.par p) s) M (s.par p) ≤ older s M (s.par p) :=
      older_moveRoot_le hgpp hgp0
    have h2 := hF.fib _ hgp hgp0 hgpp
    have h3 : (cut p (s.par p) s).deg (s.par p) = s.deg (s.par p) - 1 := by
      rw [cut_eq]; exact moveRoot_deg_p hp0
    have h4 : (cut p (s.par p) s).mark (s.par p) = s.mark (s.par p) := by
      rw [cut_eq]; simp only [setMark]; rw [moveRoot_mark, update_of_ne hgpp]
    have h5 : 1 ≤ s.deg (s.par p) := by have := hf.i_lt; omega
    rw [h3, h4]; omega
  · change (cut p (s.par p) s).time + 50 + 65 * pot (cut p (s.par p) s) M ≤ Q
    have ht : (cut p (s.par p) s).time = s.time := rfl
    simp only [pot] at hQ ⊢
    rw [ht, cut_deg0 hp0, hmk]
    omega
  · change (marked (cut p (s.par p) s) M).card < (marked s M).card
    rw [hmk]; omega

/-- After the cascade: the forest holds with no exception. -/
theorem CascInv.finish {Q : ℕ} {a : StW R × ℕ} (h : CascInv M Q a) (hc : ¬cascCond a) :
    let s := if a.1.par a.2 ≠ 0 then setMark a.2 1 a.1 else a.1
    Forest s M 0 ∧ RootList s M ∅ ∧ s.time + 65 * pot s M ≤ Q + 130 := by
  obtain ⟨s, p⟩ := a
  obtain ⟨hF, hR, hpM, hsl, hQ⟩ := h
  simp only [cascCond, not_and] at hc hF hR hpM hsl hQ ⊢
  split_ifs with hp0
  · have hm : s.mark p = 0 := by have := hF.mark p hpM; have := hc hp0; omega
    refine ⟨hF.setMark_one hpM hm (by have := hsl hp0; omega), hR.setMark _ _, ?_⟩
    have h1 := Finset.card_le_card (marked_setMark_one (p := p) (s := s) (M := M))
    have h2 := Finset.card_insert_le p (marked s M)
    change s.time + 65 * (s.deg 0 + 2 * (marked (setMark p 1 s) M).card) ≤ Q + 130
    simp only [pot] at hQ
    omega
  · exact ⟨hF.of_root (by simpa using hp0), hR, by omega⟩

end Formalgo.Algorithms.ShortestPaths
