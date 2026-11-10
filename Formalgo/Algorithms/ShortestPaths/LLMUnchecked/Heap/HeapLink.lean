import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapRoots

/-!
# Linking two roots

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M L : Finset ℕ} {x y : ℕ}

omit [LinearOrder R] in
theorem link_par : (St.link y x s).par = update s.par y x := rfl
omit [LinearOrder R] in
theorem link_deg : (St.link y x s).deg = update s.deg x (s.deg x + 1) := rfl
omit [LinearOrder R] in
theorem link_pos : (St.link y x s).pos = update s.pos y (s.deg x) := rfl
omit [LinearOrder R] in
theorem link_ch : (St.link y x s).ch = update s.ch x (update (s.ch x) (s.deg x) y) := rfl
omit [LinearOrder R] in
theorem link_mark : (St.link y x s).mark = update s.mark y 0 := rfl
omit [LinearOrder R] in
theorem link_lt : (St.link y x s).lt = update s.lt y s.clock := rfl
omit [LinearOrder R] in
theorem link_clock : (St.link y x s).clock = s.clock + 1 := rfl
omit [LinearOrder R] in
theorem link_ht : (St.link y x s).ht = update s.ht x (max (s.ht x) (s.ht y + 1)) := rfl
omit [LinearOrder R] in
theorem link_key : (St.link y x s).key = s.key := rfl

theorem Forest.link (h : Forest s M 0) (hx : x ∈ M) (hy : y ∈ M) (hxp : s.par x = 0)
    (hyp : s.par y = 0) (hxy : x ≠ y) (hdeg : s.deg y = s.deg x) (hkey : s.key x ≤ s.key y) :
    Forest (St.link y x s) M 0 := by
  have hx0 := ne_zero_of_mem h hx
  have hyx : y ≠ x := Ne.symm hxy
  -- A non-root other than `y` keeps its parent.
  have hpar : ∀ w, w ≠ y → (St.link y x s).par w = s.par w := fun w hw => by
    rw [link_par, update_of_ne hw]
  refine ⟨h.zero, fun w hw hp => ?_, fun x' hx' j hj => ?_, fun w hw hp => ?_,
    fun w hw hp => ?_, fun w hw hp _ => ?_, fun w hw w' hw' hp => ?_, fun w hw hp => ?_,
    fun w hw => ?_⟩
  · -- up
    by_cases hwy : w = y
    · subst hwy
      simp only [link_par, link_pos, link_deg, link_ch, update_self]
      exact ⟨hx, by omega, by simp⟩
    · rw [hpar w hwy] at hp ⊢
      obtain ⟨h1, h2, h3⟩ := h.up w hw hp
      rw [link_pos, update_of_ne hwy, link_deg, link_ch]
      refine ⟨h1, ?_, ?_⟩
      · rcases eq_or_ne (s.par w) x with hpx | hpx
        · rw [hpx, update_self]; rw [hpx] at h2; omega
        · rw [update_of_ne hpx]; exact h2
      · rcases eq_or_ne (s.par w) x with hpx | hpx
        · rw [hpx, update_self, update_of_ne (by rw [hpx] at h2; omega)]; rw [hpx] at h3; exact h3
        · rw [update_of_ne hpx]; exact h3
  · -- down
    rw [link_deg] at hj
    by_cases hxx : x' = x
    · subst hxx
      rw [update_self] at hj
      rw [link_ch, update_self]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨h1, h2, h3⟩ := h.down x' hx' j hj
        have hcy : s.ch x' j ≠ y := by intro hc; rw [hc, hyp] at h2; exact hx0 h2.symm
        rw [update_of_ne (Nat.ne_of_lt hj), hpar _ hcy, link_pos, update_of_ne hcy]
        exact ⟨h1, h2, h3⟩
      · simp [link_par, link_pos, hy]
    · rw [update_of_ne hxx] at hj
      obtain ⟨h1, h2, h3⟩ := h.down x' hx' j hj
      have hcy : s.ch x' j ≠ y := by
        intro hc; rw [hc, hyp] at h2; exact ne_zero_of_mem h hx' h2.symm
      rw [link_ch, update_of_ne hxx, hpar _ hcy, link_pos, update_of_ne hcy]
      exact ⟨h1, h2, h3⟩
  · -- order
    rw [link_key]
    by_cases hwy : w = y
    · subst hwy; rw [link_par, update_self]; exact hkey
    · rw [hpar w hwy] at hp ⊢; exact h.order w hw hp
  · -- height
    rw [link_ht]
    by_cases hwy : w = y
    · subst hwy; rw [link_par, update_self, update_self, update_of_ne hyx]; omega
    · rw [hpar w hwy] at hp ⊢
      have hwx : w ≠ x := by rintro rfl; exact hp hxp
      have hh := h.height w hw hp
      rw [update_of_ne hwx]
      rcases eq_or_ne (s.par w) x with hpx | hpx
      · rw [hpx, update_self]; rw [hpx] at hh; omega
      · rw [update_of_ne hpx]; exact hh
  · -- fib
    by_cases hwy : w = y
    · subst hwy
      have hle : older (St.link w x s) M w ≤ s.deg x := by
        rw [← h.card_children hx]
        refine Finset.card_le_card fun c hc => ?_
        simp only [Finset.mem_filter, link_par, link_lt, update_self] at hc ⊢
        obtain ⟨hcM, hcp, hcl⟩ := hc
        have hcw : c ≠ w := by rintro rfl; simp at hcl
        rw [update_of_ne hcw] at hcp hcl
        exact ⟨hcM, hcp⟩
      rw [link_deg, link_mark, update_of_ne hyx, update_self, hdeg]; omega
    · rw [hpar w hwy] at hp
      have hle : older (St.link y x s) M w ≤ older s M w := by
        refine Finset.card_le_card fun c hc => ?_
        simp only [Finset.mem_filter, link_par, link_lt] at hc ⊢
        obtain ⟨hcM, hcp, hcl⟩ := hc
        rw [update_of_ne hwy] at hcp hcl
        by_cases hcy : c = y
        · subst hcy
          rw [update_self] at hcl
          exact absurd hcl (by have := h.ltclock w hw hp; omega)
        · rw [update_of_ne hcy] at hcp hcl; exact ⟨hcM, hcp, hcl⟩
      have hf := h.fib w hw hp (ne_zero_of_mem h hw)
      rw [link_deg, link_mark, update_of_ne hwy]
      have hd : s.deg w ≤ update s.deg x (s.deg x + 1) w := by
        rcases eq_or_ne w x with hwx | hwx
        · subst hwx; rw [update_self]; omega
        · rw [update_of_ne hwx]
      omega
  · -- ltinj
    intro hpp hll
    rw [link_lt] at hll
    by_cases hwy : w = y
    · subst hwy
      by_cases hw'y : w' = w
      · exact hw'y
      · rw [update_of_ne hw'y, update_self] at hll
        rw [hpar w' hw'y, link_par, update_self] at hpp
        have := h.ltclock w' hw' (by rw [hpp]; exact hx0)
        omega
    · rw [update_of_ne hwy] at hll
      rw [hpar w hwy] at hp hpp
      by_cases hw'y : w' = y
      · subst hw'y
        rw [update_self] at hll
        have := h.ltclock w hw hp; omega
      · rw [update_of_ne hw'y] at hll; rw [hpar w' hw'y] at hpp
        exact h.ltinj w hw w' hw' hp hpp hll
  · -- ltclock
    rw [link_lt, link_clock]
    by_cases hwy : w = y
    · subst hwy; simp
    · rw [hpar w hwy] at hp; rw [update_of_ne hwy]; have := h.ltclock w hw hp; omega
  · -- mark
    rw [link_mark]
    by_cases hwy : w = y
    · subst hwy; simp
    · rw [update_of_ne hwy]; exact h.mark w hw

omit [LinearOrder R] in
theorem RootList.link (h : RootList s M L) (hx0 : x ≠ 0) (hyL : y ∈ L) (hxy : x ≠ y) :
    RootList (St.link y x s) M (L.erase y) := by
  have hpar : ∀ w, w ≠ y → (St.link y x s).par w = s.par w := fun w hw => by
    rw [link_par, update_of_ne hw]
  refine ⟨fun w hw => ?_, fun j hj => ?_, fun w hw hp hL => ?_⟩
  · rw [hpar w (Finset.ne_of_mem_erase hw)]; exact h.loose w (Finset.mem_of_mem_erase hw)
  · rw [link_deg, update_of_ne hx0.symm] at hj
    rw [link_ch, update_of_ne hx0.symm]
    obtain ⟨h1, h2, h3, h4⟩ := h.list j hj
    have hcy : s.ch 0 j ≠ y := fun hc => h2 (hc ▸ hyL)
    rw [hpar _ hcy, link_pos, update_of_ne hcy]
    exact ⟨h1, fun hm => h2 (Finset.mem_of_mem_erase hm), h3, h4⟩
  · have hwy : w ≠ y := by
      rintro rfl; rw [link_par, update_self] at hp; exact hx0 hp
    rw [hpar w hwy] at hp
    rw [link_pos, update_of_ne hwy, link_deg, update_of_ne hx0.symm, link_ch,
      update_of_ne hx0.symm]
    exact h.root w hw hp (fun hm => hL (Finset.mem_erase.2 ⟨hwy, hm⟩))

end Formalgo.Algorithms.ShortestPaths
