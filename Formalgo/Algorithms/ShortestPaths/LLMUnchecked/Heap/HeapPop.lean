import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapMove

/-!
# Extracting the minimum: consolidating the roots

LLM-generated; not checked by a human.

Roots are popped from the root array and linked by degree through the table.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M L : Finset ℕ} {e v p x y : ℕ}

/-- The roots in the degree table. -/
def tset (D : ℕ) (s : StW R) : Finset ℕ := ((Finset.range D).image s.tbl).erase 0

/-- Table entries are roots of the degree they sit at, below `D`. -/
def TblInv (D : ℕ) (M : Finset ℕ) (s : StW R) : Prop :=
  ∀ d, s.tbl d ≠ 0 → d < D ∧ s.tbl d ∈ M ∧ s.deg (s.tbl d) = d

omit [LinearOrder R] in
theorem mem_tset {D : ℕ} : v ∈ tset D s ↔ v ≠ 0 ∧ ∃ d < D, s.tbl d = v := by
  simp only [tset, Finset.mem_erase, Finset.mem_image, Finset.mem_range]

omit [LinearOrder R] in
theorem TblInv.eq_of_tbl {D : ℕ} (h : TblInv D M s) {d d' : ℕ} (hd : s.tbl d ≠ 0)
    (he : s.tbl d' = s.tbl d) : d' = d := by
  have h1 := (h d hd).2.2
  have h2 := (h d' (he ▸ hd)).2.2
  rw [he] at h2; omega

omit [LinearOrder R] in
theorem tset_setTbl_zero {D dx : ℕ} (h : TblInv D M s) (hy : s.tbl dx ≠ 0) :
    tset D (setTbl dx 0 s) = (tset D s).erase (s.tbl dx) := by
  ext w
  simp only [mem_tset, Finset.mem_erase, setTbl]
  constructor
  · rintro ⟨hw, d, hd, hdw⟩
    rcases eq_or_ne d dx with rfl | hne
    · rw [update_self] at hdw; exact absurd hdw.symm hw
    · rw [update_of_ne hne] at hdw
      refine ⟨fun hc => hne ?_, hw, d, hd, hdw⟩
      exact h.eq_of_tbl hy (hdw.trans hc)
  · rintro ⟨hne, hw, d, hd, hdw⟩
    have hdx : d ≠ dx := by rintro rfl; exact hne hdw.symm
    exact ⟨hw, d, hd, by rw [update_of_ne hdx]; exact hdw⟩

omit [LinearOrder R] in
theorem tset_setTbl_new {D dx : ℕ} (h0 : s.tbl dx = 0) (hdx : dx < D) (hx : x ≠ 0) :
    tset D (setTbl dx x s) = insert x (tset D s) := by
  ext w
  simp only [mem_tset, Finset.mem_insert, setTbl]
  constructor
  · rintro ⟨hw, d, hd, hdw⟩
    rcases eq_or_ne d dx with rfl | hne
    · rw [update_self] at hdw; exact .inl hdw.symm
    · rw [update_of_ne hne] at hdw; exact .inr ⟨hw, d, hd, hdw⟩
  · rintro (rfl | ⟨hw, d, hd, hdw⟩)
    · exact ⟨hx, dx, hdx, by rw [update_self]⟩
    · have hdx' : d ≠ dx := by rintro rfl; rw [h0] at hdw; exact hw hdw.symm
      exact ⟨hw, d, hd, by rw [update_of_ne hdx']; exact hdw⟩

theorem Forest.setTbl (h : Forest s M e) (d k : ℕ) : Forest (setTbl d k s) M e :=
  h.congr rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

omit [LinearOrder R] in
theorem RootList.setTbl (h : RootList s M L) (d k : ℕ) : RootList (setTbl d k s) M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

omit [LinearOrder R] in
theorem marked_link (hy : s.par y = 0) : marked (St.link y x s) M = marked s M := by
  ext w
  simp only [marked, Finset.mem_filter, link_par, link_mark]
  rcases eq_or_ne w y with rfl | hwy
  · simp [hy]
  · rw [update_of_ne hwy, update_of_ne hwy]

/-! ### Linking through the table -/

/-- The invariant of the links after a pop. -/
structure LinkInv (D : ℕ) (M : Finset ℕ) (Q d₀ : ℕ) (s₀ : StW R) (a : StW R × ℕ × ℕ) : Prop where
  forest : Forest a.1 M 0
  roots : RootList a.1 M (insert a.2.1 (tset D a.1))
  xM : a.2.1 ∈ M
  xT : a.2.1 ∉ tset D a.1
  xpar : a.1.par a.2.1 = 0
  xdeg : a.1.deg a.2.1 = a.2.2
  tbl : TblInv D M a.1
  deg0 : a.1.deg 0 = d₀
  cost : a.1.time + 65 * pot a.1 M + 40 * (tset D a.1).card + 40 ≤ Q
  keep : Keep M s₀ a.1

theorem LinkInv.step {D Q d₀ : ℕ} {s₀ : StW R} {a : StW R × ℕ × ℕ} (h : LinkInv D M Q d₀ s₀ a)
    (hc : linkCond a) :
    LinkInv D M Q d₀ s₀ (linkStep a) ∧ (tset D (linkStep a).1).card < (tset D a.1).card := by
  obtain ⟨s, x, dx⟩ := a
  obtain ⟨hF, hR, hxM, hxT, hxp, hxd, hT, hd0, hQ, hk⟩ := h
  simp only [linkCond] at hc hF hR hxM hxT hxp hxd hT hd0 hQ hk
  obtain ⟨hdxD, hyM, hyd⟩ := hT dx hc
  set y := s.tbl dx with hy_def
  have hyT : y ∈ tset D s := mem_tset.2 ⟨hc, dx, hdxD, rfl⟩
  have hyp : s.par y = 0 := (hR.loose y (Finset.mem_insert_of_mem hyT)).2
  have hxy : x ≠ y := fun hc' => hxT (hc' ▸ hyT)
  have hx0 := ne_zero_of_mem hF hxM
  have hts : tset D (setTbl dx 0 s) = (tset D s).erase y := tset_setTbl_zero hT hc
  have hcard := Finset.card_erase_of_mem hyT
  have hpos := Finset.card_pos.2 ⟨y, hyT⟩
  -- The new root `x'` and the linked root `y'`.
  set s₁ := setTbl dx 0 s with hs₁
  set x' := if s.key y < s.key x then y else x with hx'
  set y' := if s.key y < s.key x then x else y with hy'
  have hstep : linkStep (s, x, dx) = (tick 40 (St.link y' x' s₁), x', dx + 1) := rfl
  rw [hstep]
  have hx'M : x' ∈ M := by rw [hx']; split_ifs <;> assumption
  have hy'M : y' ∈ M := by rw [hy']; split_ifs <;> assumption
  have hx'p : s₁.par x' = 0 := by change s.par x' = 0; rw [hx']; split_ifs <;> assumption
  have hy'p : s₁.par y' = 0 := by change s.par y' = 0; rw [hy']; split_ifs <;> assumption
  have hne : x' ≠ y' := by rw [hx', hy']; split_ifs <;> [exact hxy.symm; exact hxy]
  have hdeg : s₁.deg y' = s₁.deg x' := by
    change s.deg y' = s.deg x'; rw [hx', hy']; split_ifs <;> rw [hxd, hyd]
  have hkey : s₁.key x' ≤ s₁.key y' := by
    change s.key x' ≤ s.key y'; rw [hx', hy']
    split_ifs with h
    · exact h.le
    · exact not_lt.1 h
  have hx'd : s₁.deg x' = dx := by
    change s.deg x' = dx; rw [hx']; split_ifs <;> [exact hyd; exact hxd]
  have hx'0 := ne_zero_of_mem hF hx'M
  have hF₁ : Forest s₁ M 0 := hF.setTbl _ _
  have hR₁ : RootList s₁ M (insert x (tset D s)) := hR.setTbl _ _
  -- Sets of loose roots.
  have hL : (insert x (tset D s)).erase y' = insert x' ((tset D s).erase y) := by
    rw [hx', hy']; split_ifs
    · rw [Finset.erase_insert hxT, Finset.insert_erase hyT]
    · rw [Finset.erase_insert_of_ne hxy]
  have htl : tset D (tick 40 (St.link y' x' s₁)) = (tset D s).erase y := hts
  refine ⟨⟨(hF₁.link hx'M hy'M hx'p hy'p hne hdeg hkey).tick 40, ?_, hx'M, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [htl, ← hL]; exact (hR₁.link hx'0 (by
      rw [hy']; split_ifs
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem hyT) hne).tick 40
  · rw [htl]; intro hm
    rw [hx'] at hm; split_ifs at hm
    · exact (Finset.notMem_erase y _) hm
    · exact hxT (Finset.mem_of_mem_erase hm)
  · change update s₁.par y' x' x' = 0; rw [update_of_ne hne]; exact hx'p
  · change update s₁.deg x' (s₁.deg x' + 1) x' = dx + 1; rw [update_self, hx'd]
  · intro d hd
    change update s.tbl dx 0 d ≠ 0 at hd
    have hdx : d ≠ dx := by rintro rfl; simp at hd
    rw [update_of_ne hdx] at hd
    obtain ⟨h1, h2, h3⟩ := hT d hd
    have hw : s.tbl d ≠ x' := by
      intro hc'; rw [hx'] at hc'; split_ifs at hc'
      · exact hdx (hT.eq_of_tbl hc hc')
      · exact hxT (hc' ▸ mem_tset.2 ⟨hd, d, h1, rfl⟩)
    refine ⟨h1, ?_, ?_⟩
    · change update s.tbl dx 0 d ∈ M; rw [update_of_ne hdx]; exact h2
    · change update s₁.deg x' (s₁.deg x' + 1) (update s.tbl dx 0 d) = d
      rw [update_of_ne hdx, update_of_ne hw]; exact h3
  · change update s₁.deg x' (s₁.deg x' + 1) 0 = d₀; rw [update_of_ne (Ne.symm hx'0)]; exact hd0
  · rw [htl]
    have hm := marked_link (M := M) (x := x') hy'p
    change s.time + 40 + 65 * ((St.link y' x' s₁).deg 0 + 2 * (marked (St.link y' x' s₁) M).card)
      + 40 * ((tset D s).erase y).card + 40 ≤ Q
    rw [hm, link_deg, update_of_ne (Ne.symm hx'0)]
    have : marked s₁ M = marked s M := rfl
    have h0' : s₁.deg 0 = s.deg 0 := rfl
    simp only [pot] at hQ; rw [this, h0']; omega
  · refine hk.trans ⟨rfl, rfl, fun w hw h0 => ?_⟩
    have hwx : w ≠ x' := fun hc' => hw (hc' ▸ hx'M)
    have hwy : w ≠ y' := fun hc' => hw (hc' ▸ hy'M)
    refine ⟨?_, ?_, ?_⟩
    · change update s₁.deg x' _ w = s.deg w; rw [update_of_ne hwx]; rfl
    · change update s₁.mark y' 0 w = s.mark w; rw [update_of_ne hwy]; rfl
    · change update s₁.par y' x' w = s.par w; rw [update_of_ne hwy]; rfl
  · change (tset D (tick 40 (St.link y' x' s₁))).card < (tset D s).card
    rw [htl]; omega

end Formalgo.Algorithms.ShortestPaths
