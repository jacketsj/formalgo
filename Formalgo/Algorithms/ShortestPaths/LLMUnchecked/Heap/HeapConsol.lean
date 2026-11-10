import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapPop

/-!
# Extracting the minimum: the pop loop

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M : Finset ℕ}

omit [LinearOrder R] in
theorem card_tset_le (D : ℕ) (s : StW R) : (tset D s).card ≤ D :=
  (Finset.card_erase_le).trans (Finset.card_image_le.trans (by simp))

theorem link_loop (C : CtxW R) {D Q d₀ : ℕ} {s₀ : StW R} {a : StW R × ℕ × ℕ}
    (h : LinkInv D M Q d₀ s₀ a) (hFu : D ≤ C.F) :
    LinkInv D M Q d₀ s₀ (whileF linkCond linkStep C.F a) ∧
      ¬linkCond (whileF linkCond linkStep C.F a) :=
  ⟨whileF_induct (LinkInv D M Q d₀ s₀) (fun _ hb hc => (hb.step hc).1) C.F a h,
    whileF_stops (LinkInv D M Q d₀ s₀) (fun b => (tset D b.1).card) (fun _ hb hc => hb.step hc)
      C.F a h ((card_tset_le D a.1).trans hFu)⟩

/-- The invariant of the pops. -/
structure PopInv (D : ℕ) (M : Finset ℕ) (Q : ℕ) (s₀ s : StW R) : Prop where
  forest : Forest s M 0
  roots : RootList s M (tset D s)
  tbl : TblInv D M s
  cost : s.time + 65 * pot s M + 40 * (tset D s).card ≤ Q
  keep : Keep M s₀ s

/-- The end of a pop: put the root in the table. -/
def popFin (a : StW R × ℕ × ℕ) : StW R := tick 25 (setTbl a.2.2 a.2.1 a.1)

/-- The start of a pop. -/
theorem PopInv.start {Q : ℕ} {s₀ : StW R} {D : ℕ} (h : PopInv D M Q s₀ s) (hc : rootsCond s) :
    LinkInv D M (Q - 25) (s.deg 0 - 1) s₀
      (popDeg s, s.ch 0 (s.deg 0 - 1), (popDeg s).deg (s.ch 0 (s.deg 0 - 1))) ∧ 65 ≤ Q := by
  obtain ⟨hF, hR, hT, hQ, hk⟩ := h
  simp only [rootsCond] at hc
  obtain ⟨x1, x2, x3, _⟩ := hR.list (s.deg 0 - 1) (by omega)
  have hdeg : ∀ w, w ≠ 0 → (popDeg s).deg w = s.deg w := fun w hw => by
    change update s.deg 0 _ w = _; rw [update_of_ne hw]
  have hp : pot (popDeg s) M + 1 = pot s M := by
    change update s.deg 0 (s.deg 0 - 1) 0 + 2 * (marked (popDeg s) M).card + 1 =
      s.deg 0 + 2 * (marked s M).card
    have : marked (popDeg s) M = marked s M := rfl
    rw [update_self, this]; omega
  refine ⟨⟨hF.popDeg, hR.popDeg hc, x1, x2, x3, rfl, fun d hd => ?_, ?_, ?_, ?_⟩, by omega⟩
  · obtain ⟨h1, h2, h3⟩ := hT d hd
    exact ⟨h1, h2, by rw [hdeg _ hd]; exact h3⟩
  · change update s.deg 0 (s.deg 0 - 1) 0 = s.deg 0 - 1; rw [update_self]
  · change s.time + 65 * pot (popDeg s) M + 40 * (tset D s).card + 40 ≤ Q - 25
    omega
  · exact hk.trans ⟨rfl, rfl, fun w _ h0 => ⟨hdeg w h0, rfl, rfl⟩⟩

/-- The end of a pop. -/
theorem PopInv.finish (C : CtxW R) {n Q d₀ : ℕ} {s₀ : StW R} {b : StW R × ℕ × ℕ}
    (hb : LinkInv C.D M (Q - 25) d₀ s₀ b) (hstop : ¬linkCond b) (h65 : 65 ≤ Q)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n) (hD : C.D = 2 * Nat.size n) :
    PopInv C.D M Q s₀ (popFin b) ∧ (popFin b).deg 0 = d₀ := by
  simp only [linkCond, not_not] at hstop
  have hdx : b.2.2 < C.D := by rw [← hb.xdeg, hD]; exact hb.forest.deg_lt hM hb.xM
  have hbx0 := ne_zero_of_mem hb.forest hb.xM
  have hts : tset C.D (popFin b) = insert b.2.1 (tset C.D b.1) :=
    tset_setTbl_new hstop hdx hbx0
  refine ⟨⟨(hb.forest.setTbl _ _).tick 25, ?_, fun d hd => ?_, ?_, ?_⟩, hb.deg0⟩
  · rw [hts]; exact (hb.roots.setTbl _ _).tick 25
  · change update b.1.tbl b.2.2 b.2.1 d ≠ 0 at hd
    change d < C.D ∧ update b.1.tbl b.2.2 b.2.1 d ∈ M ∧ b.1.deg (update b.1.tbl b.2.2 b.2.1 d) = d
    rcases eq_or_ne d b.2.2 with rfl | hne
    · rw [update_self]; exact ⟨hdx, hb.xM, hb.xdeg⟩
    · rw [update_of_ne hne] at hd ⊢; exact hb.tbl d hd
  · rw [hts, Finset.card_insert_of_notMem hb.xT]
    have := hb.cost
    change b.1.time + 25 + 65 * pot b.1 M + 40 * ((tset C.D b.1).card + 1) ≤ Q
    omega
  · exact hb.keep.trans ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem PopInv.step (C : CtxW R) {n Q : ℕ} {s₀ : StW R} (h : PopInv C.D M Q s₀ s) (hc : rootsCond s)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n) (hD : C.D = 2 * Nat.size n) (hFu : C.D ≤ C.F) :
    PopInv C.D M Q s₀ (popStep C s) ∧ (popStep C s).deg 0 < s.deg 0 := by
  obtain ⟨hF, hR, hT, hQ, hk⟩ := h
  simp only [rootsCond] at hc
  have e1 : popStep C s = popFin (whileF linkCond linkStep C.F (popDeg s,
      s.ch 0 (update s.deg 0 (s.deg 0 - 1) 0),
      (popDeg s).deg (s.ch 0 (update s.deg 0 (s.deg 0 - 1) 0)))) := rfl
  rw [update_self] at e1
  rw [e1]
  set x := s.ch 0 (s.deg 0 - 1) with hx
  obtain ⟨x1, x2, x3, _⟩ := hR.list (s.deg 0 - 1) (by omega)
  have hx0 := ne_zero_of_mem hF x1
  have hdeg : ∀ w, w ≠ 0 → (popDeg s).deg w = s.deg w := fun w hw => by
    change update s.deg 0 _ w = _; rw [update_of_ne hw]
  have hI : LinkInv C.D M (Q - 25) (s.deg 0 - 1) s₀ (popDeg s, x, (popDeg s).deg x) := by
    refine ⟨hF.popDeg, hR.popDeg hc, x1, x2, x3, rfl, fun d hd => ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hT d hd
      exact ⟨h1, h2, by rw [hdeg _ hd]; exact h3⟩
    · change update s.deg 0 (s.deg 0 - 1) 0 = s.deg 0 - 1; rw [update_self]
    · have hp : pot (popDeg s) M + 1 = pot s M := by
        change update s.deg 0 (s.deg 0 - 1) 0 + 2 * (marked (popDeg s) M).card + 1 =
          s.deg 0 + 2 * (marked s M).card
        have : marked (popDeg s) M = marked s M := rfl
        rw [update_self, this]; omega
      change s.time + 65 * pot (popDeg s) M + 40 * (tset C.D s).card + 40 ≤ Q - 25
      omega
    · exact hk.trans ⟨rfl, rfl, fun w _ h0 => ⟨hdeg w h0, rfl, rfl⟩⟩
  obtain ⟨hb, hstop⟩ := link_loop C hI hFu
  set b := whileF linkCond linkStep C.F (popDeg s, x, (popDeg s).deg x) with hb_def
  simp only [linkCond, not_not] at hstop
  have hdx : b.2.2 < C.D := by rw [← hb.xdeg, hD]; exact hb.forest.deg_lt hM hb.xM
  have hbx0 := ne_zero_of_mem hb.forest hb.xM
  have hts : tset C.D (popFin b) = insert b.2.1 (tset C.D b.1) :=
    tset_setTbl_new hstop hdx hbx0
  refine ⟨⟨(hb.forest.setTbl _ _).tick 25, ?_, fun d hd => ?_, ?_, ?_⟩, ?_⟩
  · rw [hts]; exact (hb.roots.setTbl _ _).tick 25
  · change update b.1.tbl b.2.2 b.2.1 d ≠ 0 at hd
    change d < C.D ∧ update b.1.tbl b.2.2 b.2.1 d ∈ M ∧ b.1.deg (update b.1.tbl b.2.2 b.2.1 d) = d
    rcases eq_or_ne d b.2.2 with rfl | hne
    · rw [update_self]; exact ⟨hdx, hb.xM, hb.xdeg⟩
    · rw [update_of_ne hne] at hd ⊢; exact hb.tbl d hd
  · rw [hts, Finset.card_insert_of_notMem hb.xT]
    have := hb.cost
    change b.1.time + 25 + 65 * pot b.1 M + 40 * ((tset C.D b.1).card + 1) ≤ Q
    have : 65 ≤ Q := by
      have : 1 ≤ pot s M := by simp only [pot]; omega
      omega
    omega
  · exact hb.keep.trans ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩
  · change b.1.deg 0 < s.deg 0; rw [hb.deg0]; omega

theorem pop_loop (C : CtxW R) {n Q : ℕ} {s₀ : StW R} (h : PopInv C.D M Q s₀ s)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n) (hD : C.D = 2 * Nat.size n) (hFu : C.D ≤ C.F)
    (hF0 : s.deg 0 ≤ C.F) :
    PopInv C.D M Q s₀ (whileF rootsCond (popStep C) C.F s) ∧
      (whileF rootsCond (popStep C) C.F s).deg 0 = 0 := by
  refine ⟨whileF_induct (PopInv C.D M Q s₀) (fun b hb hc => (hb.step C hc hM hD hFu).1) C.F s h,
    ?_⟩
  have := whileF_stops (PopInv C.D M Q s₀) (fun b => b.deg 0)
    (fun b hb hc => hb.step C hc hM hD hFu) C.F s h hF0
  simpa [rootsCond] using this

end Formalgo.Algorithms.ShortestPaths
