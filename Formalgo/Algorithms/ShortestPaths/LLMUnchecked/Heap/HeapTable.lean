import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapConsol

/-!
# Extracting the minimum: rebuilding the root array

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {s : St} {M : Finset ℕ} {e : ℕ}

theorem tset_zero {D : ℕ} (h : ∀ d, s.tbl d = 0) : tset D s = ∅ := by
  ext v; simp only [mem_tset, h, Finset.notMem_empty, iff_false, not_and]
  rintro hv ⟨d, _, hd⟩; exact hv hd.symm

/-- The root array holds at most `|M|` roots. -/
theorem RootList.deg0_le {L : Finset ℕ} (h : RootList s M L) : s.deg 0 ≤ M.card := by
  have : (Finset.range (s.deg 0)).image (s.ch 0) ⊆ M := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
    exact (h.list j (Finset.mem_range.1 hj)).1
  have hinj : Set.InjOn (s.ch 0) (Finset.range (s.deg 0)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [← (h.list i hi).2.2.2, ← (h.list j hj).2.2.2, hij]
  have := Finset.card_le_card this
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at this

/-- Every node has a root above it with no larger key. -/
theorem Forest.root_le (h : Forest s M e) : ∀ w ∈ M, ∃ r ∈ M, s.par r = 0 ∧ s.key r ≤ s.key w := by
  have key : ∀ k, ∀ w ∈ M, M.sup s.ht - s.ht w = k → ∃ r ∈ M, s.par r = 0 ∧ s.key r ≤ s.key w := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro w hw hk
    by_cases hp : s.par w = 0
    · exact ⟨w, hw, hp, le_refl _⟩
    · obtain ⟨h1, _, _⟩ := h.up w hw hp
      have h2 := h.height w hw hp
      have h3 : s.ht (s.par w) ≤ M.sup s.ht := Finset.le_sup h1
      obtain ⟨r, hr, hrp, hrk⟩ := ih _ (by omega) _ h1 rfl
      exact ⟨r, hr, hrp, hrk.trans (h.order w hw hp)⟩
  exact fun w hw => key _ w hw rfl

/-! ### The table loop -/

/-- The invariant of the table loop. -/
structure TabInv (D : ℕ) (M : Finset ℕ) (Q : ℕ) (s₀ : St) (a : St × ℕ) : Prop where
  forest : Forest a.1 M 0
  roots : RootList a.1 M (tset D a.1)
  tbl : TblInv D M a.1
  low : ∀ d < a.2, a.1.tbl d = 0
  dle : a.2 ≤ D + 1
  hmin0 : a.1.deg 0 = 0 → a.1.hmin = 0
  hmin1 : a.1.deg 0 ≠ 0 → a.1.hmin ∈ M ∧ a.1.par a.1.hmin = 0 ∧ a.1.hmin ∉ tset D a.1 ∧
    ∀ r ∈ M, a.1.par r = 0 → r ∉ tset D a.1 → a.1.key a.1.hmin ≤ a.1.key r
  cost : a.1.time + 65 * pot a.1 M + 40 * (tset D a.1).card + 105 * (D + 1 - a.2) ≤ Q
  keep : Keep M s₀ a.1

theorem TabInv.step (C : Ctx) {Q : ℕ} {s₀ : St} {a : St × ℕ} (h : TabInv C.D M Q s₀ a)
    (hc : tabCond C a) : TabInv C.D M Q s₀ (tabStep a) ∧ C.D + 1 - (tabStep a).2 < C.D + 1 - a.2 := by
  obtain ⟨s, d⟩ := a
  obtain ⟨hF, hR, hT, hlow, hdle, hm0, hm1, hQ, hk⟩ := h
  simp only [tabCond] at hc hF hR hT hlow hdle hm0 hm1 hQ hk
  refine ⟨?_, by change C.D + 1 - (d + 1) < C.D + 1 - d; omega⟩
  by_cases hx : s.tbl d = 0
  · have e : tabStep (s, d) = (tick 40 s, d + 1) := by simp [tabStep, hx]
    rw [e]
    refine ⟨hF.tick 40, hR.tick 40, hT, fun d' hd' => ?_, by omega, hm0, hm1, ?_, hk.tick 40⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hd' with hd' | rfl
      · exact hlow d' hd'
      · exact hx
    · change s.time + 40 + 65 * pot s M + 40 * (tset C.D s).card + 105 * (C.D + 1 - (d + 1)) ≤ Q
      omega
  · set x := s.tbl d with hx_def
    have hxT : x ∈ tset C.D s := mem_tset.2 ⟨hx, d, (hT d hx).1, rfl⟩
    obtain ⟨hxM, hxp⟩ := hR.loose x hxT
    have hx0 := ne_zero_of_mem hF hxM
    set s₂ := attach x 0 (setTbl d 0 s) with hs₂
    have e : tabStep (s, d) = (tick 40 (updMin x s₂), d + 1) := by
      show (tick 40 (if x = 0 then s else updMin x (attach x 0 (setTbl d 0 s))), d + 1) = _
      rw [if_neg hx]
    rw [e]
    have hts : tset C.D s₂ = (tset C.D s).erase x := tset_setTbl_zero hT hx
    have hpar : s₂.par = s.par := by change update s.par x 0 = s.par; rw [← hxp, update_eq_self]
    have hF₂ : Forest s₂ M 0 := (hF.setTbl _ _).attach_root hxp
    have hR₂ : RootList s₂ M (tset C.D s₂) := by
      rw [hts]; exact (hR.setTbl _ _).attach_root (L := tset C.D s) hxT
    have hdeg0 : s₂.deg 0 = s.deg 0 + 1 := by change update s.deg 0 (s.deg 0 + 1) 0 = _; simp
    have hcard := Finset.card_erase_of_mem hxT
    have hpos := Finset.card_pos.2 ⟨x, hxT⟩
    -- What `updMin` leaves alone.
    have hU : ∀ t : St, (updMin x t).par = t.par ∧ (updMin x t).deg = t.deg ∧
        (updMin x t).tbl = t.tbl ∧ (updMin x t).key = t.key ∧ (updMin x t).time = t.time ∧
        (updMin x t).mark = t.mark ∧ (updMin x t).stat = t.stat := by
      intro t; unfold St.updMin; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := hU s₂
    have htsU : tset C.D (tick 40 (updMin x s₂)) = (tset C.D s).erase x := by
      rw [← hts]; simp only [tset]; rw [show (tick 40 (updMin x s₂)).tbl = s₂.tbl from u3]
    refine ⟨((hF₂.updMin).tick 40), ?_, fun d' hd' => ?_, fun d' hd' => ?_, by omega,
      fun h0 => ?_, fun _ => ?_, ?_, ?_⟩
    · rw [htsU, ← hts]; exact (hR₂.updMin).tick 40
    · change (updMin x s₂).tbl d' ≠ 0 at hd'
      change d' < C.D ∧ (updMin x s₂).tbl d' ∈ M ∧ (updMin x s₂).deg ((updMin x s₂).tbl d') = d'
      rw [u3] at hd'; rw [u3, u2]
      change update s.tbl d 0 d' ≠ 0 at hd'
      change d' < C.D ∧ update s.tbl d 0 d' ∈ M ∧ s₂.deg (update s.tbl d 0 d') = d'
      have hne : d' ≠ d := by rintro rfl; simp at hd'
      rw [update_of_ne hne] at hd' ⊢
      obtain ⟨h1, h2, h3⟩ := hT d' hd'
      refine ⟨h1, h2, ?_⟩
      change update s.deg 0 (s.deg 0 + 1) (s.tbl d') = d'
      rw [update_of_ne (ne_zero_of_mem hF h2)]; exact h3
    · change (updMin x s₂).tbl d' = 0; rw [u3]
      change update s.tbl d 0 d' = 0
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd' with hd' | rfl
      · rw [update_of_ne (by omega)]; exact hlow d' hd'
      · simp
    · change (updMin x s₂).deg 0 = 0 at h0; rw [u2, hdeg0] at h0; omega
    · -- The minimum over the root array.
      change (updMin x s₂).hmin ∈ M ∧ (updMin x s₂).par (updMin x s₂).hmin = 0 ∧
        (updMin x s₂).hmin ∉ tset C.D (tick 40 (updMin x s₂)) ∧
        ∀ r ∈ M, (updMin x s₂).par r = 0 → r ∉ tset C.D (tick 40 (updMin x s₂)) →
          (updMin x s₂).key (updMin x s₂).hmin ≤ (updMin x s₂).key r
      have hhm : (updMin x s₂).hmin = if s₂.hmin = 0 then x
          else if s₂.key x < s₂.key s₂.hmin then x else s₂.hmin := by
        unfold St.updMin; split_ifs <;> rfl
      have hh₂ : s₂.hmin = s.hmin := rfl
      rw [htsU, u1, u4, hpar, hhm, hh₂]
      have hold : ∀ r ∈ M, s.par r = 0 → r ∉ (tset C.D s).erase x → r ≠ x → r ∉ tset C.D s :=
        fun r _ _ hr hrx hm => hr (Finset.mem_erase.2 ⟨hrx, hm⟩)
      have hk₂ : s₂.key = s.key := rfl
      rw [hk₂]
      by_cases hd0 : s.deg 0 = 0
      · rw [if_pos (hm0 hd0)]
        refine ⟨hxM, hxp, Finset.notMem_erase x _, fun r hr hrp hrT => ?_⟩
        rcases eq_or_ne r x with rfl | hrx
        · exact le_refl _
        · have := (hR.root r hr hrp (hold r hr hrp hrT hrx)).1; omega
      · obtain ⟨n1, n2, n3, n4⟩ := hm1 hd0
        rw [if_neg (ne_zero_of_mem hF n1)]
        split_ifs with hlt
        · refine ⟨hxM, hxp, Finset.notMem_erase x _, fun r hr hrp hrT => ?_⟩
          rcases eq_or_ne r x with rfl | hrx
          · exact le_refl _
          · have := n4 r hr hrp (hold r hr hrp hrT hrx); omega
        · refine ⟨n1, n2, fun hm => n3 (Finset.mem_of_mem_erase hm), fun r hr hrp hrT => ?_⟩
          rcases eq_or_ne r x with rfl | hrx
          · omega
          · exact n4 r hr hrp (hold r hr hrp hrT hrx)
    · rw [htsU]
      have hm : marked (tick 40 (updMin x s₂)) M = marked s M := by
        simp only [marked]; rw [show (tick 40 (updMin x s₂)).par = s.par from u1.trans hpar,
          show (tick 40 (updMin x s₂)).mark = s.mark from u6]
      change (updMin x s₂).time + 40 + 65 * ((updMin x s₂).deg 0 +
        2 * (marked (tick 40 (updMin x s₂)) M).card) + 40 * ((tset C.D s).erase x).card +
        105 * (C.D + 1 - (d + 1)) ≤ Q
      rw [u5, u2, hdeg0, hm]
      have : s₂.time = s.time := rfl
      simp only [pot] at hQ; omega
    · refine hk.trans ⟨u4.trans rfl, u7.trans rfl, fun w hw h0 => ?_⟩
      have hwx : w ≠ x := fun hc' => hw (hc' ▸ hxM)
      refine ⟨?_, ?_, ?_⟩
      · change (updMin x s₂).deg w = s.deg w; rw [u2]
        change update s.deg 0 _ w = _; rw [update_of_ne h0]
      · change (updMin x s₂).mark w = s.mark w; rw [u6]; rfl
      · change (updMin x s₂).par w = s.par w; rw [u1, hpar]

theorem tab_loop (C : Ctx) {Q : ℕ} {s₀ : St} {a : St × ℕ} (h : TabInv C.D M Q s₀ a)
    (hFu : C.D + 1 ≤ C.F) :
    TabInv C.D M Q s₀ (whileF (tabCond C) tabStep C.F a) ∧
      ¬tabCond C (whileF (tabCond C) tabStep C.F a) :=
  ⟨whileF_induct (TabInv C.D M Q s₀) (fun b hb hc => (hb.step C hc).1) C.F a h,
    whileF_stops (TabInv C.D M Q s₀) (fun b => C.D + 1 - b.2) (fun b hb hc => hb.step C hc)
      C.F a h (by omega)⟩

end Formalgo.Algorithms.ShortestPaths
