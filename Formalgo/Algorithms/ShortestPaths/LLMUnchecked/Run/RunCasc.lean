import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunExtract

/-!
# Running the cascade of cuts

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

/-- The cascade condition's value. -/
def cascVal (σ : St) (p : ℕ) : ℕ := (if 0 < σ.par p then 1 else 0) + σ.mark p + 1

theorem cascVal_iff {σ : St} {p : ℕ} (hm : σ.mark p ≤ 1) :
    cascVal σ p = 3 ↔ σ.par p ≠ 0 ∧ σ.mark p = 1 := by
  unfold cascVal; split_ifs with h <;> omega

theorem cascCond_spec (hR : Rep L σ m) {p : ℕ} (h15 : m 15 = p) (hp : p ≤ L.n)
    (hm : σ.mark p ≤ 1) (hB : L.top < B) :
    Runs B Prog.cascCond m fun m' k => Rep L σ m' ∧ m' 17 = cascVal σ p ∧
      (∀ a, a ≠ 2 → a ≠ 11 → a ≠ 17 → m' a = m a) ∧ k = 8 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  unfold Prog.cascCond
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 2) (d := 17) (i := 15) (by omega)
    (by rw [h15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h15] at h₁
  have R₁ := hR.regs2 (r₁ := 2) (r₂ := 17) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₁
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  have R₂ := R₁.regs1 (r := 17) (by simp [Tmp]) (by omega) f₂
  refine Runs.seqs_cons (Runs.mono (rd_spec R₂ (k := 4) (d := 11) (i := 15) (by omega)
    (by rw [f₂ 15 (by omega), f₁ 15 (by omega) (by omega), h15]; simp [Lay.bnd]; omega) (by omega)
    (by omega) (by omega) hB) fun m₃ c₃ ⟨h₃, f₃, hc₃⟩ => ?_)
  rw [f₂ 15 (by omega), f₁ 15 (by omega) (by omega), h15] at h₃
  have R₃ := R₂.regs2 (r₁ := 2) (r₂ := 11) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₃
  have h₃17 : m₃ 17 = if 0 < σ.par p then 1 else 0 := by
    rw [f₃ 17 (by omega) (by omega), h₂, f₁ 8 (by omega) (by omega), hR.zero, h₁]; rfl
  have hm' : fld σ 4 p ≤ 1 := hm
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h₃17, h₃]; split_ifs <;> omega) fun m₄ h₄ f₄ => ?_)
  have h₄17 : m₄ 17 = (if 0 < σ.par p then 1 else 0) + σ.mark p := by rw [h₄, h₃17, h₃]; rfl
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h₄17, f₄ 3 (by omega), f₃ 3 (by omega) (by omega), f₂ 3 (by omega),
      f₁ 3 (by omega) (by omega), hR.one]; split_ifs <;> omega) fun m₅ h₅ f₅ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₆ h₆ f₆ => ?_
  refine ⟨(R₃.regs1 (r := 17) (by simp [Tmp]) (by omega) f₄ |>.regs1 (r := 17) (by simp [Tmp])
    (by omega) f₅ |>.regs1 (r := 2) (by simp [Tmp]) (by omega) f₆), ?_,
    fun a a2 a11 a17 => ?_, by omega⟩
  · rw [f₆ 17 (by omega), h₅, h₄17, f₄ 3 (by omega), f₃ 3 (by omega) (by omega), f₂ 3 (by omega),
      f₁ 3 (by omega) (by omega), hR.one]; rfl
  · rw [f₆ a a2, f₅ a a17, f₄ a a17, f₃ a a2 a11, f₂ a a17, f₁ a a2 a17]

/-- The registers the cascade uses. -/
def TC (a : ℕ) : Prop := T267 a ∨ a = 11 ∨ a = 12 ∨ a = 15 ∨ a = 17

theorem TC_tmp {a : ℕ} (h : TC a) : Tmp a := by
  rcases h with (h | h | h) | h | h | h | h <;> simp [Tmp, h]

/-- The cascade's state in memory. -/
structure CascR (L : Lay) (x : EInput) (m₀ : Mem) (M : Finset ℕ) (Q : ℕ) (a : St × ℕ) (m : Mem) :
    Prop where
  rep : Rep L a.1 m
  fixed : Fixed L x m
  frm : Frm L TC m₀ m
  r15 : m 15 = a.2
  r17 : m 17 = cascVal a.1 a.2
  inv : CascInv M Q a
  range : ∀ v ∈ M, 1 ≤ v ∧ v ≤ L.n
  degs : ∀ w ∈ M, a.1.deg w ≤ L.D

theorem cut_deg_le {s : St} {v p w : ℕ} (hp : p ≠ 0) (hw : w ≠ 0) :
    (St.cut v p s).deg w ≤ s.deg w := by
  rw [cut_eq]; change (moveRoot v p s).deg w ≤ _
  rw [moveRoot_deg _ _ _ hp, update_of_ne hw]
  rcases eq_or_ne w p with rfl | hwp
  · rw [update_self]; omega
  · rw [update_of_ne hwp]

theorem cascBody_spec {M : Finset ℕ} {Q : ℕ} {m₀ : Mem} (hB : L.top < B) {a : St × ℕ}
    (h : CascR L x m₀ M Q a m) (hc : cascCond a) :
    Runs B cascBody m fun m' k => CascR L x m₀ M Q (cascStep a) m' ∧
      a.1.time + k + 2 ≤ (cascStep a).1.time := by
  obtain ⟨s, p⟩ := a
  obtain ⟨hR, hF, hfr, h15, h17, hI, hM, hdg⟩ := h
  replace hR : Rep L s m := hR
  replace hdg : ∀ w ∈ M, s.deg w ≤ L.D := hdg
  have hc' : s.par p ≠ 0 ∧ s.mark p = 1 := hc
  have h15' : m 15 = p := h15
  have hpM : p ∈ M := hI.pM
  have hFo : Forest s M p := hI.forest
  have hf := hFo.cutFacts hpM hc'.1
  have hgM := hf.pM
  have hpn : p ≤ L.n := (hM p hpM).2
  have hgn : s.par p ≤ L.n := (hM _ hgM).2
  have hd0 : s.deg 0 ≤ L.n := (hI.roots.deg0_le).trans (card_le_n hM)
  have hdg' := hdg _ hgM
  have hlast : s.ch (s.par p) (s.deg (s.par p) - 1) ≤ L.n := (hM _ hf.lastM).2
  have hcap : L.cap (s.par p) = L.D + 1 := by simp [Lay.cap, hf.p0]
  have hil : s.pos p < s.deg (s.par p) := hf.i_lt
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hstep := hI.step hc
  have hcs : cascStep (s, p) = (St.tick 50 (St.cut p (s.par p) s), s.par p) := rfl
  rw [hcs] at hstep ⊢
  unfold cascBody
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 2) (d := 12) (i := 15) (by omega)
    (by rw [h15']; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h15'] at h₁
  have h₁12 : m₁ 12 = s.par p := h₁
  have h₁15 : m₁ 15 = p := by rw [f₁ 15 (by omega) (by omega), h15']
  have R₁ := hR.regs2 (r₁ := 2) (r₂ := 12) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₁
  have X₁ : Fixed L x m₁ := hF.frame hH (fun a ha _ => f₁ a (by omega) (by omega))
  refine Runs.seqs_cons (Runs.mono (cut_spec R₁ X₁ (rv := 15) (rp := 12) (by rw [h₁15]; exact hpn)
    (by rw [h₁12]; exact hgn) (by rw [h₁12]; exact hf.p0)
    (by rw [h₁12]; omega) (by rw [h₁12, hcap]; omega)
    (by rw [h₁12]; exact hlast) (by rw [h₁15, h₁12, hcap]; omega) hd0
    (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₂ c₂ ⟨R₂, X₂, F₂, hc₂⟩ => ?_)
  rw [h₁15, h₁12] at R₂
  have q₂ : ∀ r, r < 32 → ¬T267 r → m₂ r = m₁ r := F₂.1
  refine Runs.seqs_cons (Runs.copyR (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
  have h₃15 : m₃ 15 = s.par p := by rw [g₃, q₂ 12 (by omega) (by simp [T267]), h₁12]
  have R₃ := R₂.regs1 (r := 15) (by simp [Tmp]) (by omega) f₃
  have hgm : (St.cut p (s.par p) s).mark (s.par p) ≤ 1 := by
    have hgp : s.par p ≠ p := fun e => by
      have := hFo.height p hpM hc'.1; rw [e] at this; omega
    change update s.mark p 0 (s.par p) ≤ 1
    rw [update_of_ne hgp]; exact hFo.mark _ hgM
  refine Runs.seqs_cons (Runs.mono (cascCond_spec R₃ h₃15 hgn hgm hB) fun m₄ c₄ ⟨R₄, h₄, f₄,
      hc₄⟩ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₅ h₅ f₅ => ?_
  have F₄ : Frm L TC m₃ m₄ := ⟨fun a _ hT => f₄ a (fun e => hT (by simp [TC, T267, e]))
    (fun e => hT (by simp [TC, e])) (fun e => hT (by simp [TC, e])),
    fun a ha _ => f₄ a (by omega) (by omega) (by omega)⟩
  have F₅ : Frm L TC m m₅ := (Frm.reg (by simp [TC]) (by omega) f₁ (by simp [TC, T267])).trans
    ((F₂.mono fun a ha => Or.inl ha).trans ((Frm.reg1 (by simp) (by omega) f₃).trans
      (F₄.trans (Frm.reg1 (by simp [TC, T267]) (by omega) f₅))))
  refine ⟨⟨(R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅).same
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF.frame hH F₅.2, hfr.trans F₅,
    by rw [f₅ 15 (by omega), f₄ 15 (by omega) (by omega) (by omega), h₃15],
    by rw [f₅ 17 (by omega), h₄]; rfl, hstep.1, hM,
    fun w hw => (cut_deg_le hf.p0 (by have := (hM w hw).1; omega)).trans (hdg w hw)⟩, ?_⟩
  change s.time + _ + 2 ≤ s.time + 50
  omega

theorem cascLoop_spec (C : Ctx) {M : Finset ℕ} {Q : ℕ} {m₀ : Mem} (hB : L.top < B)
    (hFM : M.card ≤ C.F) {a : St × ℕ} (h : CascR L x m₀ M Q a m) :
    Runs B (loop 17 16 cascBody) m fun m' k =>
      CascR L x m₀ M Q (whileF cascCond cascStep C.F a) m' ∧
        a.1.time + k ≤ (whileF cascCond cascStep C.F a).1.time + 1 ∧
        ¬cascCond (whileF cascCond cascStep C.F a) ∧
        DecFrame M a.1 (whileF cascCond cascStep C.F a).1 := by
  have ht := top_ge (L := L)
  have hH := h.rep.H32
  have hloop := casc_loop C h.inv hFM
  refine Runs.mono (Runs.loop_refine (CascR L x m₀ M Q) cascCond cascStep
    (fun a => a.1.time) (by omega) (by omega) (fun a m hR => ?_)
    (fun a m hR hc => cascBody_spec hB hR hc) C.F a m h hloop.2.1)
    fun m' k ⟨hR, hk⟩ => ⟨hR, hk, hloop.2.1, hloop.2.2⟩
  rw [hR.r17, hR.rep.three]
  exact cascVal_iff (hR.inv.forest.mark _ hR.inv.pM)

end Formalgo.Algorithms.ShortestPaths
