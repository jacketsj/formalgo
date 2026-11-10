import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunTable
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapExtract

/-!
# Running the extraction of the minimum

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

/-- The registers `extractMin` uses. -/
def TE (a : ℕ) : Prop := TT a ∨ TP a ∨ TM a ∨ a = 12 ∨ a = 30

theorem extractMin_spec (C : Ctx) (hC : CtxOK C) (hLn : L.n = C.n) (hLD : L.D = C.D)
    (hB : L.top < B) {s : St} {M : Finset ℕ} (hH : HeapInv C.n s M) (hne : M.Nonempty)
    (hR : Rep L s m) (hF : Fixed L x m) :
    Runs B extractMin m fun m' k => Rep L (extract C s) m' ∧ Fixed L x m' ∧ Frm L TE m m' ∧
      m' 30 = s.hmin ∧ s.time + k ≤ (extract C s).time := by
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hfu := hC.fuel
  have hD := hC.D_eq
  -- The model, phase by phase, as in `extract_spec`.
  obtain ⟨m1, m2, m3⟩ := hH.min hne
  set z := s.hmin with hz
  have hz0 := ne_zero_of_mem hH.forest m1
  have hzn : z ≤ L.n := by rw [hLn]; exact (hH.range z m1).2
  obtain ⟨hF1, hR1, hzp1, hpot1, ht1, htb1, hk1⟩ := detach_min hH hne
  set s₁ := St.detach z 0 s with hs₁
  have hdz : s₁.deg z = s.deg z := by
    change update s.deg 0 _ z = _; rw [update_of_ne hz0]
  have hdzD : s.deg z < C.D := by rw [hD]; exact hH.forest.deg_lt hH.range m1
  have hI : MoveInv M z (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s (s₁, z) :=
    ⟨rfl, m1, hF1, hR1, hzp1, le_refl _, hk1, htb1⟩
  have hd0s : s.deg 0 ≤ L.n := by rw [hLn]; exact hH.roots.deg0_le.trans (card_le_n hH.range)
  obtain ⟨zp, zch⟩ := hH.roots.root z m1 m2 (Finset.notMem_empty _)
  obtain ⟨l1, _, _, _⟩ := hH.roots.list (s.deg 0 - 1) (by omega)
  -- Copy `z`, and take it out of the root array.
  unfold extractMin
  refine Runs.seqs_cons (Runs.copyR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
  have h₁30 : m₁ 30 = z := by rw [g₁, hR.hmin]
  have R₁ : Rep L s m₁ := hR.regs1 (r := 30) (by simp [Tmp]) (by omega) f₁
  have z₁ : m₁ 8 = 0 := by rw [f₁ 8 (by omega), hR.zero]
  have X₁ : Fixed L x m₁ := hF.frame hH32 (fun a ha _ => f₁ a (by omega))
  refine Runs.seqs_cons (Runs.mono (detach_spec R₁ X₁ (rv := 30) (rp := 8) (by rw [h₁30]; exact hzn)
    (by rw [z₁]; omega) (by rw [z₁]; omega) (by rw [z₁]; simp [Lay.cap]; omega)
    (by rw [z₁]; rw [hLn]; exact (hH.range _ l1).2) (by rw [z₁, h₁30]; simp [Lay.cap]; omega)
    (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₂ c₂ ⟨R₂, X₂, F₂, hc₂⟩ => ?_)
  rw [h₁30, z₁] at R₂
  have q₂ : ∀ r, r < 32 → ¬T267 r → m₂ r = m₁ r := F₂.1
  have h₂30 : m₂ 30 = z := by rw [q₂ 30 (by omega) (by simp [T267]), h₁30]
  -- The moves.
  refine Runs.seqs_cons (Runs.mono (rd_spec R₂ (k := 3) (d := 12) (i := 30) (by omega)
    (by rw [h₂30]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₃ c₃ ⟨h₃, f₃, hc₃⟩ => ?_)
  rw [h₂30] at h₃
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₄ h₄ f₄ => ?_)
  have R₄ : Rep L s₁ m₄ := (R₂.regs2 (r₁ := 2) (r₂ := 12) (by simp [Tmp]) (by simp [Tmp]) (by omega)
    (by omega) f₃).regs1 (r := 13) (by simp [Tmp]) (by omega) f₄
  have X₄ : Fixed L x m₄ := X₂.frame hH32 ((Frm.reg (L := L) (T := TE) (r := 12) (by simp [TE])
    (by omega) f₃ (by simp [TE, TT, T29, T267])).trans (Frm.reg1 (by simp [TE,
        TT]) (by omega) f₄)).2
  have hMR : MoveR L x m₄ (MoveInv M z (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s) (s₁, z) m₄ := by
    refine ⟨R₄, X₄, Frm.refl, by rw [f₄ 30 (by omega), f₃ 30 (by omega) (by omega), h₂30], ?_, hI⟩
    rw [h₄, f₃ 8 (by omega) (by omega), q₂ 8 (by omega) (by simp [T267]), z₁, h₃]; rfl
  refine Runs.seqs_cons (Runs.mono (moveLoop_spec C hLn hLD hD hH.range hB hfu hMR)
    fun m₅ c₅ ⟨hmv, hk5, hd0⟩ => ?_)
  set s₂ := (whileF moveCond moveStep C.F (s₁, z)).1 with hs₂
  have hmi := hmv.inv
  have hF2 : Forest s₂ (M.erase z) 0 := hmi.forest.erase_root m1 hmi.zpar hd0
  have hR2 : RootList s₂ (M.erase z) ∅ := by
    simpa using hmi.roots.erase_root (Finset.mem_singleton_self z)
  have hpot2 : pot s₂ (M.erase z) = pot s₂ M := pot_erase_root hmi.zpar
  have hrange : ∀ v ∈ M.erase z, 1 ≤ v ∧ v ≤ C.n := fun v hv =>
    hH.range v (Finset.mem_of_mem_erase hv)
  have htbl2 : ∀ d, s₂.tbl d = 0 := by intro d; rw [hmi.tbl]; exact hH.tbl d
  have hts2 : tset C.D s₂ = ∅ := tset_zero htbl2
  have hP : PopInv C.D (M.erase z) (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s₂ s₂ :=
    ⟨hF2, by rw [hts2]; exact hR2, fun d hd => absurd (htbl2 d) hd,
      by rw [hts2, hpot2]; have := hmi.cost; rw [hd0] at this; simpa using this, Keep.refl⟩
  have h₅30 : m₅ 30 = z := hmv.r30.trans hmi.z_eq
  -- The pops.
  have hb21 : m₅ 21 = L.H + 3 * L.R := hmv.rep.base 3 (by omega)
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₆ h₆ f₆ => ?_)
  have h₆11 : m₆ 11 = s₂.deg 0 := by
    rw [h₆, hb21]; have := hmv.rep.arr 3 (by omega) 0 (by simp [Lay.bnd]); rw [Nat.add_zero] at this
    exact this
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₇ h₇ f₇ => ?_)
  have R₇ : Rep L s₂ m₇ := (hmv.rep.regs1 (r := 11) (by simp [Tmp]) (by omega) f₆).regs1 (r := 13)
    (by simp [Tmp]) (by omega) f₇
  have X₇ : Fixed L x m₇ := hmv.fixed.frame hH32 (fun a ha _ => by rw [f₇ a (by omega), f₆ a
      (by omega)])
  have hPR : PopR L x m₇ (PopInv C.D (M.erase z)
      (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z) s₂) s₂ m₇ :=
    ⟨R₇, X₇, Frm.refl, by rw [h₇, f₆ 8 (by omega), hmv.rep.zero, h₆11], hP⟩
  refine Runs.seqs_cons (Runs.mono (popLoop_spec C hLn hLD hD hrange hB hfu hPR)
    fun m₈ c₈ ⟨hpo, hk8, hdeg0⟩ => ?_)
  set s₃ := whileF rootsCond (popStep C) C.F s₂ with hs₃
  have hpi := hpo.inv
  have hT : TabInv C.D (M.erase z) (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z + 105 * (C.D + 1))
      s₂ ({ s₃ with hmin := 0 }, 0) := by
    refine ⟨hpi.forest.setHmin 0, hpi.roots.setHmin 0, hpi.tbl, fun d hd => absurd hd (by omega),
      by omega, fun _ => rfl, fun h => absurd hdeg0 h, ?_,
      ⟨hpi.keep.key, hpi.keep.stat, hpi.keep.out⟩⟩
    have := hpi.cost
    change s₃.time + 65 * pot s₃ (M.erase z) + 40 * (tset C.D s₃).card + 105 * (C.D + 1 - 0) ≤ _
    omega
  -- Reset the minimum, and rebuild the root array.
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₉ h₉ f₉ => ?_)
  have R₉ : Rep L { s₃ with hmin := 0 } m₉ := hpo.rep.setHmin 0 (fun a ha _ _ => f₉ a ha)
    (fun a ha => f₉ a (by omega)) h₉
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₁₀ h₁₀ f₁₀ => ?_)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₁₁ h₁₁ f₁₁ => ?_)
  have R₁₁ : Rep L { s₃ with hmin := 0 } m₁₁ := (R₉.regs1 (r := 11) (by simp [Tmp]) (by omega)
    f₁₀).regs1 (r := 13) (by simp [Tmp]) (by omega) f₁₁
  have X₁₁ : Fixed L x m₁₁ := hpo.fixed.frame hH32 (fun a ha _ => by
    rw [f₁₁ a (by omega), f₁₀ a (by omega), f₉ a (by omega)])
  have hTR : TabR L x m₁₁ (TabInv C.D (M.erase z)
      (s₁.time + 65 * pot s₁ M + 95 * s₁.deg z + 105 * (C.D + 1)) s₂)
      ({ s₃ with hmin := 0 }, 0) m₁₁ := by
    refine ⟨R₁₁, X₁₁, Frm.refl, by rw [f₁₁ 11 (by omega), h₁₀], ?_, hT⟩
    rw [h₁₁, f₁₀ 28 (by omega), f₉ 28 (by omega), hpo.rep.D, h₁₀]
  refine Runs.seqs_cons (Runs.mono (tableLoop_spec C hLn hLD hrange hB hfu hTR)
    fun m₁₂ c₁₂ ⟨htb, hk12, _⟩ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₁₃ h₁₃ f₁₃ => ?_
  set b := whileF (tabCond C) tabStep C.F ({ s₃ with hmin := 0 }, 0) with hb
  have hext : extract C s = St.tick 40 b.1 := rfl
  rw [hext]
  -- Frames.
  have Fa : Frm L TE m m₄ := (Frm.reg1 (by simp [TE]) (by omega) f₁).trans
    ((F₂.mono fun a ha => Or.inl (Or.inl (Or.inl ha))).trans
      ((Frm.reg (by simp) (by omega) f₃ (by simp [T267])).trans
        (Frm.reg1 (by simp) (by omega) f₄)))
  have Fb : Frm L TE m₄ m₈ := (hmv.frm.mono fun a ha => Or.inr (Or.inr (Or.inl ha))).trans
    ((Frm.reg1 (by simp [TT]) (by omega) f₆).trans ((Frm.reg1 (by simp [TT]) (by omega) f₇).trans
      (hpo.frm.mono fun a ha => Or.inr (Or.inl ha))))
  have Fc : Frm L TE m₈ m₁₃ := (Frm.reg1 (by simp [TE, TT, T29]) (by omega) f₉).trans
    ((Frm.reg1 (by simp [TE, TT]) (by omega) f₁₀).trans ((Frm.reg1 (by simp [TE, TT]) (by omega)
        f₁₁).trans
      ((htb.frm.mono fun a ha => Or.inl ha).trans (Frm.reg1 (by simp [TT, T29, T267]) (by omega)
          f₁₃))))
  have Fall : Frm L TE m m₁₃ := Fa.trans (Fb.trans Fc)
  refine ⟨(htb.rep.regs1 (r := 2) (by simp [Tmp]) (by omega) f₁₃).same
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF.frame hH32 Fall.2, Fall, ?_, ?_⟩
  · rw [f₁₃ 30 (by omega), htb.frm.1 30 (by omega) (by simp [TT, T29, T267]), f₁₁ 30 (by omega),
      f₁₀ 30 (by omega), f₉ 30 (by omega), hpo.frm.1 30 (by omega) (by simp [TP, TL, T267]),
      f₇ 30 (by omega), f₆ 30 (by omega), h₅30]
  · change s.time + _ ≤ b.1.time + 40
    have e1 : s₁.time = s.time := ht1
    have e3 : ({ s₃ with hmin := 0 } : St).time = s₃.time := rfl
    simp only [] at hk5 hk8 hk12
    omega

end Formalgo.Algorithms.ShortestPaths
