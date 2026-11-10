import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapDec

/-!
# Decreasing a key

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {s s' : St} {M L : Finset ℕ} {e v p nk : ℕ}

/-- The heap invariant between operations. -/
structure HeapInv (n : ℕ) (s : St) (M : Finset ℕ) : Prop where
  range : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n
  forest : Forest s M 0
  roots : RootList s M ∅
  min : M.Nonempty → s.hmin ∈ M ∧ s.par s.hmin = 0 ∧ ∀ w ∈ M, s.key s.hmin ≤ s.key w
  tbl : ∀ d, s.tbl d = 0

/-! ### The minimum root -/

theorem Forest.setHmin (h : Forest s M e) (x : ℕ) : Forest { s with hmin := x } M e :=
  h.congr rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

theorem RootList.setHmin (h : RootList s M L) (x : ℕ) : RootList { s with hmin := x } M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

theorem Forest.updMinKey (h : Forest s M e) : Forest (updMinKey v nk s) M e := by
  unfold ShortestPaths.updMinKey; split_ifs
  · exact h.setHmin _
  · exact h

theorem RootList.updMinKey (h : RootList s M L) : RootList (updMinKey v nk s) M L := by
  unfold ShortestPaths.updMinKey; split_ifs
  · exact h.setHmin _
  · exact h

theorem Forest.updMin (h : Forest s M e) : Forest (updMin v s) M e := by
  unfold St.updMin; split_ifs
  · exact h.setHmin _
  · exact h.setHmin _
  · exact h

theorem RootList.updMin (h : RootList s M L) : RootList (updMin v s) M L := by
  unfold St.updMin; split_ifs
  · exact h.setHmin _
  · exact h.setHmin _
  · exact h

/-- The minimum after lowering the key of `v`, a root, to `nk`. -/
theorem min_updMinKey {s₀ : St} (hm : s₀.hmin ∈ M ∧ s₀.par s₀.hmin = 0 ∧
      ∀ w ∈ M, s₀.key s₀.hmin ≤ s₀.key w) (hv : v ∈ M) (hnk : nk < s₀.key v)
    (hkey : s'.key = update s₀.key v nk) (hh : s'.hmin = s₀.hmin) (hr : s'.par s₀.hmin = 0)
    (hvr : s'.par v = 0) :
    (updMinKey v nk s').hmin ∈ M ∧ (updMinKey v nk s').par (updMinKey v nk s').hmin = 0 ∧
      ∀ w ∈ M, (updMinKey v nk s').key (updMinKey v nk s').hmin ≤ (updMinKey v nk s').key w := by
  obtain ⟨m1, m2, m3⟩ := hm
  unfold ShortestPaths.updMinKey
  split_ifs with hc
  · refine ⟨hv, hvr, fun w hw => ?_⟩
    simp only [hkey, hh, update_self] at hc ⊢
    have hmv : s₀.hmin ≠ v := by rintro hc'; rw [hc', update_self] at hc; omega
    rw [update_of_ne hmv] at hc
    rcases eq_or_ne w v with rfl | hwv
    · simp
    · rw [update_of_ne hwv]; have := m3 w hw; omega
  · refine ⟨hh ▸ m1, hh ▸ hr, fun w hw => ?_⟩
    rw [hkey, hh] at hc ⊢
    rcases eq_or_ne w v with rfl | hwv
    · rw [update_self]; omega
    · rw [update_of_ne hwv]
      have := m3 w hw
      rcases eq_or_ne s₀.hmin v with hmv | hmv
      · rw [hmv, update_self]; rw [hmv] at this; omega
      · rw [update_of_ne hmv]; exact this

/-! ### What a cascade leaves alone -/

/-- What decreasing a key leaves alone. -/
structure DecFrame (M : Finset ℕ) (s s' : St) : Prop where
  key : s'.key = s.key
  stat : s'.stat = s.stat
  tbl : s'.tbl = s.tbl
  hmin : s'.hmin = s.hmin
  roots : ∀ w, s.par w = 0 → s'.par w = 0
  out : ∀ w ∉ M, w ≠ 0 → s'.deg w = s.deg w ∧ s'.mark w = s.mark w ∧ s'.par w = s.par w

theorem DecFrame.refl : DecFrame M s s := ⟨rfl, rfl, rfl, rfl, fun _ h => h, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem DecFrame.trans {s'' : St} (h : DecFrame M s s') (h' : DecFrame M s' s'') :
    DecFrame M s s'' :=
  ⟨h'.key.trans h.key, h'.stat.trans h.stat, h'.tbl.trans h.tbl, h'.hmin.trans h.hmin,
    fun w hw => h'.roots w (h.roots w hw), fun w hw h0 => by
      obtain ⟨a, b, c⟩ := h.out w hw h0; obtain ⟨a', b', c'⟩ := h'.out w hw h0
      exact ⟨a'.trans a, b'.trans b, c'.trans c⟩⟩

theorem DecFrame.cut (hf : CutFacts s M v p) (c : ℕ) : DecFrame M s (tick c (cut v p s)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun w hw => ?_, fun w hw h0 => ?_⟩
  · change update s.par v 0 w = 0
    rcases eq_or_ne w v with rfl | hwv
    · simp
    · rw [update_of_ne hwv]; exact hw
  · have hwv : w ≠ v := fun hc => hw (hc ▸ hf.vM)
    have hwp : w ≠ p := fun hc => hw (hc ▸ hf.pM)
    refine ⟨?_, ?_, ?_⟩
    · change (moveRoot v p s).deg w = s.deg w
      rw [moveRoot_deg _ _ _ hf.p0, update_of_ne h0, update_of_ne hwp]
    · change update s.mark v 0 w = s.mark w
      rw [update_of_ne hwv]
    · change update s.par v 0 w = s.par w
      rw [update_of_ne hwv]

theorem DecFrame.setMark (hp : p ∈ M) (k : ℕ) : DecFrame M s (setMark p k s) := by
  refine ⟨rfl, rfl, rfl, rfl, fun w hw => hw, fun w hw _ => ⟨rfl, ?_, rfl⟩⟩
  change update s.mark p k w = s.mark w
  have hwp : w ≠ p := by rintro rfl; exact hw hp
  rw [update_of_ne hwp]

/-! ### The cascade as a whole -/

theorem marked_subset : marked s M ⊆ M := Finset.filter_subset _ _

theorem casc_loop (C : Ctx) {Q : ℕ} {a : St × ℕ} (h : CascInv M Q a) (hF : M.card ≤ C.F) :
    CascInv M Q (whileF cascCond cascStep C.F a) ∧ ¬cascCond (whileF cascCond cascStep C.F a) ∧
      DecFrame M a.1 (whileF cascCond cascStep C.F a).1 := by
  have hP := whileF_induct (c := cascCond) (f := cascStep)
    (fun b => CascInv M Q b ∧ DecFrame M a.1 b.1) (fun b ⟨hb, hfr⟩ hc => by
      refine ⟨(hb.step hc).1, hfr.trans ?_⟩
      obtain ⟨t, q⟩ := b
      exact DecFrame.cut (hb.forest.cutFacts hb.pM hc.1) 50) C.F a ⟨h, DecFrame.refl⟩
  refine ⟨hP.1, ?_, hP.2⟩
  exact whileF_stops (CascInv M Q) (fun b => (marked b.1 M).card)
    (fun b hb hc => hb.step hc) C.F a h
    ((Finset.card_le_card marked_subset).trans hF)

/-- The slack at `p` after cutting its child `v`. -/
theorem slack_cut (h : Forest s M e) (hf : CutFacts s M v p) (hpe : p ≠ e)
    (hp : s.par p ≠ 0) :
    older (cut v p s) M p ≤ (cut v p s).deg p + (cut v p s).mark p + 1 := by
  have hpv : p ≠ v := by
    rintro rfl; have := h.height p hf.vM (by rw [hf.vp]; exact hf.p0); rw [hf.vp] at this; omega
  have h1 : older (cut v p s) M p ≤ older s M p := older_moveRoot_le hpv hp
  have h2 := h.fib p hf.pM hp hpe
  have h3 : (cut v p s).deg p = s.deg p - 1 := by rw [cut_eq]; exact moveRoot_deg_p hf.p0
  have h4 : (cut v p s).mark p = s.mark p := by
    change update s.mark v 0 p = s.mark p; rw [update_of_ne hpv]
  have h5 : 1 ≤ s.deg p := by have := hf.i_lt; omega
  rw [h3, h4]; omega

/-! ### Decreasing a key -/

theorem updMinKey_of (P : St → Prop) (hP : ∀ x, P { s with hmin := x }) (h : P s) :
    P (updMinKey v nk s) := by
  unfold ShortestPaths.updMinKey; split_ifs
  · exact hP _
  · exact h

/-- What decreasing a key gives. -/
structure DecOut (n : ℕ) (s : St) (M : Finset ℕ) (v nk : ℕ) (r : St) : Prop where
  inv : HeapInv n r M
  key : r.key = update s.key v nk
  stat : r.stat = s.stat
  out : ∀ w ∉ M, w ≠ 0 → r.deg w = s.deg w ∧ r.mark w = s.mark w ∧ r.par w = s.par w
  cost : r.time + 65 * pot r M ≤ s.time + 65 * pot s M + 275

theorem decKey_root (C : Ctx) (hH : HeapInv C.n s M) (hv : v ∈ M) (hnk : nk < s.key v)
    (hp : s.par v = 0) : DecOut C.n s M v nk (updMinKey v nk (tick 80 (setKey v nk s))) := by
  obtain ⟨m1, m2, m3⟩ := hH.min ⟨v, hv⟩
  refine ⟨⟨hH.range, ((hH.forest.setKey hv hnk.le (.inl hp)).tick 80).updMinKey,
    ((hH.roots.setKey v nk).tick 80).updMinKey,
    fun _ => min_updMinKey ⟨m1, m2, m3⟩ hv hnk rfl rfl m2 hp,
    updMinKey_of (fun t => ∀ d, t.tbl d = 0) (fun _ => hH.tbl) hH.tbl⟩,
    updMinKey_of (fun t => t.key = update s.key v nk) (fun _ => rfl) rfl,
    updMinKey_of (fun t => t.stat = s.stat) (fun _ => rfl) rfl,
    updMinKey_of (fun t => ∀ w ∉ M, w ≠ 0 → t.deg w = s.deg w ∧ t.mark w = s.mark w ∧
      t.par w = s.par w) (fun _ _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl, rfl⟩),
    updMinKey_of (fun t => t.time + 65 * pot t M ≤ s.time + 65 * pot s M + 275)
      (fun _ => by change s.time + 80 + 65 * pot s M ≤ _; omega)
      (by change s.time + 80 + 65 * pot s M ≤ _; omega)⟩

theorem decKey_keep (C : Ctx) (hH : HeapInv C.n s M) (hv : v ∈ M) (hnk : nk < s.key v)
    (hp : s.par v ≠ 0) (hk : s.key (s.par v) ≤ nk) :
    DecOut C.n s M v nk (tick 80 (setKey v nk s)) := by
  obtain ⟨m1, m2, m3⟩ := hH.min ⟨v, hv⟩
  have hmv : s.hmin ≠ v := by rintro hc; rw [hc] at m2; exact hp m2
  refine ⟨⟨hH.range, (hH.forest.setKey hv hnk.le (.inr hk)).tick 80,
    (hH.roots.setKey v nk).tick 80, fun _ => ⟨m1, m2, fun w hw => ?_⟩, hH.tbl⟩, rfl, rfl,
    fun _ _ _ => ⟨rfl, rfl, rfl⟩, by change s.time + 80 + 65 * pot s M ≤ _; omega⟩
  change update s.key v nk s.hmin ≤ update s.key v nk w
  rw [update_of_ne hmv]
  rcases eq_or_ne w v with rfl | hwv
  · rw [update_self]; exact (m3 _ (hH.forest.up w hv hp).1).trans hk
  · rw [update_of_ne hwv]; exact m3 w hw

/-- The end of a cascade. -/
def cascFin (a : St × ℕ) : St := if a.1.par a.2 ≠ 0 then setMark a.2 1 a.1 else a.1

/-- The cascade starts in its invariant. -/
theorem cascInv_start {n : ℕ} (hH : HeapInv n s M) (hv : v ∈ M) (hnk : nk < s.key v) (hp : s.par v ≠ 0) :
    CascInv M (s.time + 80 + 65 * (pot s M + 1))
      (cut v (s.par v) (tick 80 (setKey v nk s)), s.par v) := by
  have hf := hH.forest.cutFacts hv hp
  have hcomm : cut v (s.par v) (tick 80 (setKey v nk s)) =
      tick 80 (setKey v nk (cut v (s.par v) s)) := rfl
  have hvr : (cut v (s.par v) s).par v = 0 := by change update s.par v 0 v = 0; simp
  have hF0 : Forest (cut v (s.par v) s) M (s.par v) := by
    rw [cut_eq]
    exact (hH.forest.move_root hf (.inl rfl)).setMark_root (by rw [moveRoot_par, update_self])
  have hR0 : RootList (cut v (s.par v) s) M ∅ := by
    rw [cut_eq]; exact (hH.roots.move_root hf).setMark _ _
  have hpot : pot (cut v (s.par v) s) M ≤ pot s M + 1 := by
    have h1 := cut_deg0 (v := v) (s := s) hf.p0
    have h2 := marked_cut (v := v) (s := s) (M := M) hf.p0
    have h3 := Finset.card_erase_le (s := marked s M) (a := v)
    simp only [pot]; rw [h1, h2]; omega
  refine ⟨?_, ?_, hf.pM, fun hpp => ?_, ?_⟩
  · show Forest (cut v (s.par v) (tick 80 (setKey v nk s))) M (s.par v)
    rw [hcomm]; exact (hF0.setKey hv hnk.le (.inl hvr)).tick 80
  · show RootList (cut v (s.par v) (tick 80 (setKey v nk s))) M ∅
    rw [hcomm]; exact (hR0.setKey v nk).tick 80
  · change older (cut v (s.par v) s) M (s.par v) ≤
      (cut v (s.par v) s).deg (s.par v) + (cut v (s.par v) s).mark (s.par v) + 1
    have hpv : s.par v ≠ v := by
      intro hc; have := hH.forest.height v hv hp; rw [hc] at this; omega
    change update s.par v 0 (s.par v) ≠ 0 at hpp
    rw [update_of_ne hpv] at hpp
    exact slack_cut hH.forest hf hf.p0 hpp
  · change s.time + 80 + 65 * pot (cut v (s.par v) s) M ≤ _; omega

theorem decKey_cut (C : Ctx) (hH : HeapInv C.n s M) (hv : v ∈ M) (hnk : nk < s.key v)
    (hp : s.par v ≠ 0) (hFM : M.card ≤ C.F) :
    DecOut C.n s M v nk (updMinKey v nk (cascFin
      (whileF cascCond cascStep C.F (cut v (s.par v) (tick 80 (setKey v nk s)), s.par v)))) := by
  obtain ⟨m1, m2, m3⟩ := hH.min ⟨v, hv⟩
  have hf := hH.forest.cutFacts hv hp
  set a₀ := (cut v (s.par v) (tick 80 (setKey v nk s)), s.par v) with ha₀
  have hI : CascInv M (s.time + 80 + 65 * (pot s M + 1)) a₀ := cascInv_start hH hv hnk hp
  have hvr : (cut v (s.par v) s).par v = 0 := by change update s.par v 0 v = 0; simp
  obtain ⟨hb, hstop, hfr⟩ := casc_loop C hI hFM
  set b := whileF cascCond cascStep C.F a₀ with hb_def
  obtain ⟨hF2, hR2, hc2⟩ := hb.finish hstop
  -- The frame from the cut to the end of the cascade.
  have hfr2 : DecFrame M a₀.1 (cascFin b) := by
    unfold cascFin; split_ifs
    · exact hfr.trans (DecFrame.setMark hb.pM 1)
    · exact hfr
  have hout0 := (DecFrame.cut hf 80).out
  refine ⟨⟨hH.range, hF2.updMinKey, hR2.updMinKey,
    fun _ => min_updMinKey ⟨m1, m2, m3⟩ hv hnk hfr2.key hfr2.hmin
      (hfr2.roots _ (by change update s.par v 0 s.hmin = 0
                        rcases eq_or_ne s.hmin v with h | h
                        · rw [h, update_self]
                        · rw [update_of_ne h]; exact m2))
      (hfr2.roots _ hvr),
    updMinKey_of (fun t => ∀ d, t.tbl d = 0) (fun _ => by rw [hfr2.tbl]; exact hH.tbl)
      (by rw [hfr2.tbl]; exact hH.tbl)⟩,
    updMinKey_of (fun t => t.key = update s.key v nk) (fun _ => hfr2.key) hfr2.key,
    updMinKey_of (fun t => t.stat = s.stat) (fun _ => hfr2.stat) hfr2.stat,
    updMinKey_of (fun t => ∀ w ∉ M, w ≠ 0 → t.deg w = s.deg w ∧ t.mark w = s.mark w ∧
      t.par w = s.par w) (fun _ w hw h0 => ?_) (fun w hw h0 => ?_),
    updMinKey_of (fun t => t.time + 65 * pot t M ≤ s.time + 65 * pot s M + 275)
      (fun _ => ?_) ?_⟩
  · obtain ⟨a, b', c⟩ := hfr2.out w hw h0; obtain ⟨a', b'', c'⟩ := hout0 w hw h0
    exact ⟨a.trans a', b'.trans b'', c.trans c'⟩
  · obtain ⟨a, b', c⟩ := hfr2.out w hw h0; obtain ⟨a', b'', c'⟩ := hout0 w hw h0
    exact ⟨a.trans a', b'.trans b'', c.trans c'⟩
  · change (cascFin b).time + 65 * pot (cascFin b) M ≤ _
    unfold cascFin; omega
  · unfold cascFin; omega

theorem decKey_spec (C : Ctx) (hH : HeapInv C.n s M) (hv : v ∈ M) (hnk : nk < s.key v)
    (hFM : M.card ≤ C.F) : DecOut C.n s M v nk (decKey C v nk s) := by
  by_cases hp : s.par v = 0
  · have e : decKey C v nk s = updMinKey v nk (tick 80 (setKey v nk s)) := by
      unfold decKey; rw [if_pos (show (tick 80 (setKey v nk s)).par v = 0 from hp)]
    rw [e]; exact decKey_root C hH hv hnk hp
  · have hpv : s.par v ≠ v := by
      intro hc; have := hH.forest.height v hv hp; rw [hc] at this; omega
    by_cases hk : nk < s.key (s.par v)
    · have e : decKey C v nk s = updMinKey v nk (cascFin
          (whileF cascCond cascStep C.F (cut v (s.par v) (tick 80 (setKey v nk s)), s.par v))) := by
        unfold decKey
        rw [if_neg (show ¬(tick 80 (setKey v nk s)).par v = 0 from hp),
          if_pos (show nk < (tick 80 (setKey v nk s)).key ((tick 80 (setKey v nk s)).par v) by
            change nk < update s.key v nk (s.par v); rw [update_of_ne hpv]; exact hk)]
        rfl
      rw [e]; exact decKey_cut C hH hv hnk hp hFM
    · have e : decKey C v nk s = tick 80 (setKey v nk s) := by
        unfold decKey
        rw [if_neg (show ¬(tick 80 (setKey v nk s)).par v = 0 from hp),
          if_neg (show ¬nk < (tick 80 (setKey v nk s)).key ((tick 80 (setKey v nk s)).par v) by
            change ¬nk < update s.key v nk (s.par v); rw [update_of_ne hpv]; exact hk)]
      rw [e]; exact decKey_keep C hH hv hnk hp (by omega)

end Formalgo.Algorithms.ShortestPaths
