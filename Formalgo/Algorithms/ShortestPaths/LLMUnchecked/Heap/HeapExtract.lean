import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapTable

/-!
# Extracting the minimum

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [LinearOrder R]

variable {s : StW R} {M : Finset ℕ}

/-- The context fits the input: `D = 2 · size n`, and the fuel covers every loop. -/
structure CtxOK (C : CtxW R) : Prop where
  D_eq : C.D = 2 * Nat.size C.n
  fuel : C.n + C.D + 1 ≤ C.F

theorem card_le_n {n : ℕ} (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ n) : M.card ≤ n :=
  calc M.card ≤ ((Finset.range (n + 1)).erase 0).card := Finset.card_le_card fun v hv => by
        have := hM v hv; simp only [Finset.mem_erase, Finset.mem_range]; omega
    _ = n := by rw [Finset.card_erase_of_mem (by simp), Finset.card_range]; rfl

theorem extract_spec (C : CtxW R) (hC : CtxOK C) (hH : HeapInv C.n s M) (hne : M.Nonempty) :
    HeapInv C.n (extract C s) (M.erase s.hmin) ∧ Keep M s (extract C s) ∧
      (extract C s).time + 65 * pot (extract C s) (M.erase s.hmin) ≤
        s.time + 65 * pot s M + 200 * (C.D + 1) ∧
      (M.erase s.hmin = ∅ → (extract C s).hmin = 0) := by
  obtain ⟨m1, m2, m3⟩ := hH.min hne
  have hfu := hC.fuel
  set z := s.hmin with hz
  have hz0 := ne_zero_of_mem hH.forest m1
  -- Removing `z` from the root array.
  obtain ⟨hF1, hR1, hzp1, hpot1, ht1, htb1, hk1⟩ := detach_min hH hne
  set s₁ := detach z 0 s with hs₁
  have hdz : s₁.deg z = s.deg z := by
    change update s.deg 0 _ z = _; rw [update_of_ne hz0]
  have hdzD : s.deg z < C.D := by rw [hC.D_eq]; exact hH.forest.deg_lt hH.range m1
  -- Moving its children.
  have hI : MoveInv M z (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s (s₁, z) :=
    ⟨rfl, m1, hF1, hR1, hzp1, le_refl _, hk1, htb1⟩
  obtain ⟨hmv, hd0⟩ := move_loop C hI (by change s₁.deg z ≤ C.F; rw [hdz]; omega)
  set s₂ := (whileF moveCond moveStep C.F (s₁, z)).1 with hs₂
  have hF2 : Forest s₂ (M.erase z) 0 := hmv.forest.erase_root m1 hmv.zpar hd0
  have hR2 : RootList s₂ (M.erase z) ∅ := by
    simpa using hmv.roots.erase_root (Finset.mem_singleton_self z)
  have hpot2 : pot s₂ (M.erase z) = pot s₂ M := pot_erase_root hmv.zpar
  have hrange : ∀ v ∈ M.erase z, 1 ≤ v ∧ v ≤ C.n := fun v hv =>
    hH.range v (Finset.mem_of_mem_erase hv)
  have htbl2 : ∀ d, s₂.tbl d = 0 := by intro d; rw [hmv.tbl]; exact hH.tbl d
  have hts2 : tset C.D s₂ = ∅ := tset_zero htbl2
  -- Popping and linking.
  have hP : PopInv C.D (M.erase z) (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s₂ s₂ :=
    ⟨hF2, by rw [hts2]; exact hR2, fun d hd => absurd (htbl2 d) hd,
      by rw [hts2, hpot2]; have := hmv.cost; rw [hd0] at this; simpa using this, Keep.refl⟩
  obtain ⟨hpop, hdeg0⟩ := pop_loop C hP hrange hC.D_eq (by omega)
    ((hR2.deg0_le.trans (card_le_n hrange)).trans (by omega))
  set s₃ := whileF rootsCond (popStep C) C.F s₂ with hs₃
  -- Rebuilding the root array.
  have hT : TabInv C.D (M.erase z) (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z + 105 * (C.D + 1))
      s₂ ({ s₃ with hmin := 0 }, 0) := by
    refine ⟨hpop.forest.setHmin 0, hpop.roots.setHmin 0, hpop.tbl, fun d hd => absurd hd (by omega),
      by omega, fun _ => rfl, fun h => absurd hdeg0 h, ?_,
      ⟨hpop.keep.key, hpop.keep.stat, hpop.keep.out⟩⟩
    have := hpop.cost
    change s₃.time + 65 * pot s₃ (M.erase z) + 40 * (tset C.D s₃).card + 105 * (C.D + 1 - 0) ≤ _
    omega
  obtain ⟨htab, hstop⟩ := tab_loop C hT (by have := hC.fuel; omega)
  set b := whileF (tabCond C) tabStep C.F ({ s₃ with hmin := 0 }, 0) with hb
  simp only [tabCond, not_le] at hstop
  have hball : ∀ d, b.1.tbl d = 0 := by
    intro d
    by_contra hd
    have h1 := (htab.tbl d hd).1
    exact hd (htab.low d (by omega))
  have htsb : tset C.D b.1 = ∅ := tset_zero hball
  have hRb : RootList b.1 (M.erase z) ∅ := htsb ▸ htab.roots
  have hext : extract C s = tick 40 b.1 := rfl
  rw [hext]
  refine ⟨⟨hrange, htab.forest.tick 40, hRb.tick 40, fun hne' => ?_, hball⟩,
    ((hmv.keep.trans (htab.keep.mono (Finset.erase_subset _ _))).tick 40), ?_, ?_⟩
  · -- The minimum over all nodes.
    obtain ⟨w, hw⟩ := hne'
    obtain ⟨r, hr, hrp, _⟩ := htab.forest.root_le w hw
    have hd0' : b.1.deg 0 ≠ 0 := by have := (hRb.root r hr hrp (by simp)).1; omega
    obtain ⟨n1, n2, _, n4⟩ := htab.hmin1 hd0'
    refine ⟨n1, n2, fun w hw => ?_⟩
    obtain ⟨r, hr, hrp, hrk⟩ := htab.forest.root_le w hw
    exact (n4 r hr hrp (by rw [htsb]; simp)).trans hrk
  · have := htab.cost
    rw [htsb] at this
    change b.1.time + 40 + 65 * pot b.1 (M.erase z) ≤ _
    have h1 : s₁.time = s.time := ht1
    rw [hdz] at this
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] at this
    omega
  · intro he
    have := hRb.deg0_le; rw [he, Finset.card_empty] at this
    exact htab.hmin0 (by omega)

end Formalgo.Algorithms.ShortestPaths
