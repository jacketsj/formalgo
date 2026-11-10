import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapExtract

/-!
# Inserting a node

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M : Finset ℕ} {n v : ℕ}

/-- Insert a fresh node `v` with key `k` and status `st`. -/
def insertSt (v : ℕ) (k : R) (st : ℕ) (s : StW R) : StW R :=
  updMin v (attach v 0 (setStat v st (setKey v k s)))

theorem updMin_hmin (v : ℕ) (t : StW R) : (updMin v t).hmin =
    if t.hmin = 0 then v else if t.key v < t.key t.hmin then v else t.hmin := by
  unfold St.updMin; split_ifs <;> rfl

theorem updMin_of (P : StW R → Prop) {t : StW R} (hP : ∀ x, P { t with hmin := x }) (h : P t) :
    P (updMin v t) := by
  unfold St.updMin; split_ifs
  · exact hP _
  · exact hP _
  · exact h

theorem insert_spec (hH : HeapInv n s M) (he : M = ∅ → s.hmin = 0) (hv1 : 1 ≤ v) (hvn : v ≤ n)
    (hvM : v ∉ M) (hp : s.par v = 0) (hd : s.deg v = 0) (hm : s.mark v ≤ 1) (k : R) (st : ℕ) :
    HeapInv n (insertSt v k st s) (insert v M) ∧
      (insertSt v k st s).key = update s.key v k ∧
      (insertSt v k st s).stat = update s.stat v st ∧
      (∀ w, w ≠ v → w ≠ 0 → (insertSt v k st s).deg w = s.deg w ∧
        (insertSt v k st s).mark w = s.mark w ∧ (insertSt v k st s).par w = s.par w) ∧
      (insertSt v k st s).time = s.time ∧
      pot (insertSt v k st s) (insert v M) = pot s M + 1 := by
  have hv0 : v ≠ 0 := by omega
  set t := setStat v st (setKey v k s) with ht
  have hFt : Forest t M 0 := hH.forest.congr rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x hx => by
      change update s.key v k x = s.key x; rw [update_of_ne (by rintro rfl; exact hvM hx)])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
  have hRt : RootList t M ∅ := hH.roots.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)
  have hF' : Forest (attach v 0 t) (insert v M) 0 :=
    (hFt.insert_fresh hvM hv0 hp hd hm).attach_root hp
  have hR' : RootList (attach v 0 t) (insert v M) ∅ := by
    simpa using (hRt.insert_fresh hvM hp).attach_root (Finset.mem_insert_self v ∅)
  have hpar : (attach v 0 t).par = s.par := by
    change update s.par v 0 = s.par; rw [← hp, update_eq_self]
  have hrange : ∀ w ∈ insert v M, 1 ≤ w ∧ w ≤ n := by
    intro w hw; rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hv1, hvn⟩
    · exact hH.range w hw
  refine ⟨⟨hrange, hF'.updMin, hR'.updMin, fun _ => ?_,
      updMin_of (fun t => ∀ d, t.tbl d = 0) (fun _ => hH.tbl) hH.tbl⟩,
    updMin_of (fun t => t.key = update s.key v k) (fun _ => rfl) rfl,
    updMin_of (fun t => t.stat = update s.stat v st) (fun _ => rfl) rfl,
    fun w hw h0 => updMin_of (fun t => t.deg w = s.deg w ∧ t.mark w = s.mark w ∧
        t.par w = s.par w)
      (fun _ => ⟨by change update s.deg 0 _ w = _; rw [update_of_ne h0], rfl,
        by rw [show _ = _ from hpar]⟩)
      ⟨by change update s.deg 0 _ w = _; rw [update_of_ne h0], rfl, by rw [hpar]⟩,
    updMin_of (fun t => t.time = s.time) (fun _ => rfl) rfl, ?_⟩
  · -- The minimum.
    unfold insertSt
    rw [updMin_hmin]
    have hk : (attach v 0 t).key = update s.key v k := rfl
    have hh : (attach v 0 t).hmin = s.hmin := rfl
    have hk' : ∀ w ∈ M, update s.key v k w = s.key w := fun w hw => by
      rw [update_of_ne (by rintro rfl; exact hvM hw)]
    rw [← ht]
    have hP : (updMin v (attach v 0 t)).par = s.par :=
      updMin_of (fun t => t.par = s.par) (fun _ => hpar) hpar
    have hK : (updMin v (attach v 0 t)).key = update s.key v k :=
      updMin_of (fun t => t.key = update s.key v k) (fun _ => rfl) rfl
    rw [hP, hK, hk, hh]
    by_cases hM : M = ∅
    · rw [if_pos (he hM)]
      refine ⟨Finset.mem_insert_self _ _, hp, fun w hw => ?_⟩
      rw [hM] at hw; rw [show w = v by simpa using hw]
    · obtain ⟨m1, m2, m3⟩ := hH.min (Finset.nonempty_iff_ne_empty.2 hM)
      rw [if_neg (ne_zero_of_mem hH.forest m1)]
      have hmv : s.hmin ≠ v := fun h => hvM (h ▸ m1)
      split_ifs with hlt
      · refine ⟨Finset.mem_insert_self _ _, hp, fun w hw => ?_⟩
        rw [update_self] at hlt ⊢
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [update_self]
        · rw [hk' w hw]; rw [hk' _ m1] at hlt; have := m3 w hw; exact (hlt.trans_le this).le
      · refine ⟨Finset.mem_insert_of_mem m1, m2, fun w hw => ?_⟩
        rw [hk' _ m1] at hlt ⊢
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [update_self] at hlt ⊢; exact not_lt.1 hlt
        · rw [hk' w hw]; exact m3 w hw
  · -- The potential.
    have hmk : marked (insertSt v k st s) (insert v M) = marked s M := by
      ext w
      simp only [marked, Finset.mem_filter, Finset.mem_insert]
      have h1 : (insertSt v k st s).par = s.par :=
        updMin_of (fun t => t.par = s.par) (fun _ => hpar) hpar
      have h2 : (insertSt v k st s).mark = s.mark :=
        updMin_of (fun t => t.mark = s.mark) (fun _ => rfl) rfl
      rw [h1, h2]
      constructor
      · rintro ⟨rfl | hw, h⟩
        · exact absurd hp h.1
        · exact ⟨hw, h⟩
      · rintro ⟨hw, h⟩; exact ⟨.inr hw, h⟩
    have hdeg : (insertSt v k st s).deg 0 = s.deg 0 + 1 :=
      updMin_of (fun t => t.deg 0 = s.deg 0 + 1) (fun _ => by simp [attach, setStat, setKey])
        (by simp [attach, setStat, setKey])
    simp only [pot, hmk, hdeg]; omega

end Formalgo.Algorithms.ShortestPaths
