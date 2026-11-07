import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunCasc

/-!
# Running `decKey`

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : Input}

/-- The registers `updMinKey` uses. -/
def TU (a : ℕ) : Prop := a = 2 ∨ a = 17 ∨ a = 29

theorem updMinKey_spec (hR : Rep L σ m) (hF : Fixed L x m) {v nk : ℕ} (h13 : m 13 = v)
    (h14 : m 14 = nk) (hm : σ.hmin ≤ L.n) (hB : L.top < B) :
    Runs B Prog.updMinKey m fun m' c => Rep L (ShortestPaths.updMinKey v nk σ) m' ∧
      Fixed L x m' ∧ Frm L TU m m' ∧ c ≤ 7 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have h29 : m 29 = σ.hmin := hR.hmin
  unfold Prog.updMinKey
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 0) (d := 17) (i := 29) (by omega)
    (by rw [h29]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h29] at h₁
  have R₁ := hR.regs2 (r₁ := 2) (r₂ := 17) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₁
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  have R₂ := R₁.regs1 (r := 17) (by simp [Tmp]) (by omega) f₂
  have h₂17 : m₂ 17 = if nk < σ.key σ.hmin then 1 else 0 := by
    rw [h₂, f₁ 14 (by omega) (by omega), h14, h₁]; rfl
  have F₂ : Frm L TU m m₂ := (Frm.reg (by simp [TU]) (by omega) f₁ (by simp [TU])).trans
    (Frm.reg1 (by simp [TU]) (by omega) f₂)
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun hlt => ?_) (fun hlt => ?_))
  · rw [h₂17, R₂.one] at hlt
    have hlt' : nk < σ.key σ.hmin := by by_contra hc; simp [hc] at hlt
    refine Runs.copyR (by omega) (by omega) fun m₃ h₃ f₃ => Runs.seqs_nilR (by omega)
      fun m₄ h₄ f₄ => ?_
    have e : ShortestPaths.updMinKey v nk σ = { σ with hmin := v } := by
      simp [ShortestPaths.updMinKey, hlt']
    rw [e]
    have F₄ : Frm L TU m m₄ := F₂.trans ((Frm.reg1 (by simp [TU]) (by omega) f₃).trans
      (Frm.reg1 (by simp [TU]) (by omega) f₄))
    have hv₂ : m₂ 13 = v := by rw [F₂.1 13 (by omega) (by simp [TU]), h13]
    refine ⟨?_, hF.frame hH F₄.2, F₄, by omega⟩
    refine R₂.setHmin _ (fun a ha hT _ => ?_) (fun a ha => ?_) ?_
    · rw [f₄ a (fun e => hT (by simp [Tmp, e])), f₃ a ha]
    · rw [f₄ a (by omega), f₃ a (by omega)]
    · rw [f₄ 29 (by omega), h₃, hv₂]
  · rw [h₂17, R₂.one] at hlt
    have hlt' : ¬nk < σ.key σ.hmin := by intro hc; simp [hc] at hlt
    refine Runs.constR (by omega) (by omega) fun m₃ h₃ f₃ => Runs.seqs_nilR (by omega)
      fun m₄ h₄ f₄ => ?_
    have e : ShortestPaths.updMinKey v nk σ = σ := by simp [ShortestPaths.updMinKey, hlt']
    rw [e]
    have F₄ : Frm L TU m m₄ := F₂.trans ((Frm.reg1 (by simp [TU]) (by omega) f₃).trans
      (Frm.reg1 (by simp [TU]) (by omega) f₄))
    exact ⟨(R₂.regs1 (r := 2) (by simp [Tmp]) (by omega) f₃).regs1 (r := 2) (by simp [Tmp])
      (by omega) f₄, hF.frame hH F₄.2, F₄, by omega⟩

/-- The registers the cut branch of `decKey` uses. -/
def TD (a : ℕ) : Prop := TC a ∨ TU a

theorem TC_TD {a : ℕ} (h : TC a) : TD a := .inl h

theorem T267_TD {a : ℕ} (h : T267 a) : TD a := .inl (by
  rcases h with h | h | h <;> simp [TC, T267, h])

theorem decCut_spec (C : Ctx) {M : Finset ℕ} {Q v nk p : ℕ} {s : St} (hR : Rep L s m)
    (hF : Fixed L x m) (h13 : m 13 = v) (h14 : m 14 = nk) (h15 : m 15 = p)
    (hf : CutFacts s M v p) (hI : CascInv M Q (St.cut v p s, p)) (hMr : ∀ w ∈ M, 1 ≤ w ∧ w ≤ L.n)
    (hdg : ∀ w ∈ M, s.deg w ≤ L.D) (hd0 : s.deg 0 ≤ L.n) (hm : s.hmin ≤ L.n) (hFM : M.card ≤ C.F)
    (hB : L.top < B) :
    Runs B (seqs [Prog.cut 13 15, Prog.cascCond, loop 17 16 cascBody, rd 17 2 15,
        ite 17 8 nop (wr 4 15 3), Prog.updMinKey]) m fun m' k =>
      Rep L (ShortestPaths.updMinKey v nk
        (cascFin (whileF cascCond cascStep C.F (St.cut v p s, p)))) m' ∧ Fixed L x m' ∧
      Frm L TD m m' ∧
      s.time + k ≤ (cascFin (whileF cascCond cascStep C.F (St.cut v p s, p))).time + 57 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hvn := (hMr v hf.vM).2
  have hpn := (hMr p hf.pM).2
  have hcap : L.cap p = L.D + 1 := by simp [Lay.cap, hf.p0]
  have hil := hf.i_lt
  have hdp := hdg p hf.pM
  have hlast := (hMr _ hf.lastM).2
  refine Runs.seqs_cons (Runs.mono (cut_spec hR hF (rv := 13) (rp := 15) (by rw [h13]; exact hvn)
    (by rw [h15]; exact hpn) (by rw [h15]; exact hf.p0) (by rw [h15]; omega)
    (by rw [h15, hcap]; omega) (by rw [h15]; exact hlast) (by rw [h13, h15, hcap]; omega) hd0
    (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₁ c₁ ⟨R₁, X₁, F₁, hc₁⟩ => ?_)
  rw [h13, h15] at R₁
  have q₁ : ∀ r, r < 32 → ¬T267 r → m₁ r = m r := F₁.1
  have e13 : m₁ 13 = v := by rw [q₁ 13 (by omega) (by simp [T267]), h13]
  have e14 : m₁ 14 = nk := by rw [q₁ 14 (by omega) (by simp [T267]), h14]
  have e15 : m₁ 15 = p := by rw [q₁ 15 (by omega) (by simp [T267]), h15]
  refine Runs.seqs_cons (Runs.mono (cascCond_spec R₁ e15 hpn (hI.forest.mark _ hI.pM) hB)
    fun m₂ c₂ ⟨R₂, h₂, f₂, hc₂⟩ => ?_)
  have X₂ : Fixed L x m₂ := X₁.frame hH (fun a ha _ => f₂ a (by omega) (by omega) (by omega))
  have F₂ : Frm L TD m₁ m₂ := ⟨fun a _ hT => f₂ a (fun e => hT (.inl (by simp [TC, T267, e])))
    (fun e => hT (.inl (by simp [TC, e]))) (fun e => hT (.inl (by simp [TC, e]))),
    fun a ha _ => f₂ a (by omega) (by omega) (by omega)⟩
  have hC₂ : CascR L x m₂ M Q (St.cut v p s, p) m₂ :=
    ⟨R₂, X₂, Frm.refl, by rw [f₂ 15 (by omega) (by omega) (by omega), e15], h₂, hI, hMr,
      fun w hw => (cut_deg_le hf.p0 (by have := (hMr w hw).1; omega)).trans (hdg w hw)⟩
  refine Runs.seqs_cons (Runs.mono (cascLoop_spec C hB hFM hC₂)
    fun m₃ c₃ ⟨hC₃, ht₃, hn₃, hD₃⟩ => ?_)
  set b := whileF cascCond cascStep C.F (St.cut v p s, p) with hb
  have R₃ := hC₃.rep
  have h₃15 : m₃ 15 = b.2 := hC₃.r15
  have hbn := (hMr _ hC₃.inv.pM).2
  have F₃ : Frm L TD m₂ m₃ := hC₃.frm.mono fun _ => TC_TD
  have F₃' : Frm L TD m m₃ := (F₁.mono fun _ => T267_TD).trans (F₂.trans F₃)
  have e₃13 : m₃ 13 = v := by rw [F₃'.1 13 (by omega) (by simp [TD, TC, TU, T267]), h13]
  have e₃14 : m₃ 14 = nk := by rw [F₃'.1 14 (by omega) (by simp [TD, TC, TU, T267]), h14]
  have hfin : (cascFin b).hmin = s.hmin := by
    have : b.1.hmin = s.hmin := hD₃.hmin
    unfold cascFin; split_ifs <;> exact this
  have htime : s.time + c₃ ≤ (cascFin b).time + 1 := by
    have e1 : (cascFin b).time = b.1.time := by unfold cascFin; split_ifs <;> rfl
    have e2 : (St.cut v p s).time + c₃ ≤ b.1.time + 1 := ht₃
    have e3 : (St.cut v p s).time = s.time := rfl
    omega
  have fin : ∀ m₅ : Mem, Rep L (cascFin b) m₅ → Fixed L x m₅ → Frm L TD m m₅ → m₅ 13 = v →
      m₅ 14 = nk → Runs B (seqs [Prog.updMinKey]) m₅ fun m' k =>
        Rep L (ShortestPaths.updMinKey v nk (cascFin b)) m' ∧ Fixed L x m' ∧ Frm L TD m m' ∧
          k ≤ 8 := by
    intro m₅ R₅ X₅ F₅ a13 a14
    refine Runs.seqs_cons (Runs.mono (updMinKey_spec R₅ X₅ a13 a14 (by rw [hfin]; exact hm) hB)
      fun m₆ c₆ ⟨R₆, X₆, F₆, hc₆⟩ => ?_)
    refine Runs.seqs_nilR (by omega) fun m₇ h₇ f₇ => ?_
    have F₇ : Frm L TD m₆ m₇ := Frm.reg1 (.inr (by simp [TU])) (by omega) f₇
    exact ⟨R₆.regs1 (r := 2) (by simp [Tmp]) (by omega) f₇,
      X₆.frame hH F₇.2, F₅.trans ((F₆.mono fun _ h => .inr h).trans F₇), by omega⟩
  refine Runs.seqs_cons (Runs.mono (rd_spec R₃ (k := 2) (d := 17) (i := 15) (by omega)
    (by rw [h₃15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₄ c₄ ⟨h₄, f₄, hc₄⟩ => ?_)
  rw [h₃15] at h₄
  have h₄17 : m₄ 17 = b.1.par b.2 := h₄
  have R₄ := R₃.regs2 (r₁ := 2) (r₂ := 17) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₄
  have X₄ : Fixed L x m₄ := hC₃.fixed.frame hH (fun a ha _ => f₄ a (by omega) (by omega))
  have F₄ : Frm L TD m m₄ := F₃'.trans (Frm.reg (.inl (by simp [TC])) (by omega) f₄
    (.inl (by simp [TC, T267])))
  have e₄13 : m₄ 13 = v := by rw [f₄ 13 (by omega) (by omega), e₃13]
  have e₄14 : m₄ 14 = nk := by rw [f₄ 14 (by omega) (by omega), e₃14]
  have e₄15 : m₄ 15 = b.2 := by rw [f₄ 15 (by omega) (by omega), h₃15]
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun h0 => ?_) (fun h0 => ?_))
  · rw [h₄17, R₄.zero] at h0
    have e : cascFin b = b.1 := by simp [cascFin, h0]
    refine Runs.constR (by omega) (by omega) fun m₅ h₅ f₅ => ?_
    have F₅ : Frm L TD m₄ m₅ := Frm.reg1 (.inl (by simp [TC, T267])) (by omega) f₅
    refine Runs.mono (fin m₅ (by rw [e]; exact R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅)
      (X₄.frame hH F₅.2) (F₄.trans F₅) (by rw [f₅ 13 (by omega), e₄13])
      (by rw [f₅ 14 (by omega), e₄14])) fun m' k ⟨a, b', c, d⟩ => ⟨a, b', c, by omega⟩
  · rw [h₄17, R₄.zero] at h0
    have e : cascFin b = St.setMark b.2 1 b.1 := by unfold cascFin; rw [if_pos h0]
    have hbnd : m₄ 15 ≤ L.bnd 4 := by rw [e₄15]; simp [Lay.bnd]; omega
    refine Runs.mono (wr_spec R₄ (k := 4) (i := 15) (s := 3) (by omega) hbnd (by omega) (by omega)
      (by omega) hB) fun m₅ c₅ ⟨R₅, f₅, hc₅⟩ => ?_
    have F₅ : Frm L TD m₄ m₅ := Frm.dyn (dyn_arr (k := 4) (by omega) hbnd)
      (.inl (by simp [TC, T267])) f₅ hH
    rw [e₄15, R₄.one] at R₅
    refine Runs.mono (fin m₅ (by rw [e]; exact R₅) (X₄.frame hH F₅.2) (F₄.trans F₅)
      (by rw [f₅ 13 (by omega) (by omega), e₄13]) (by rw [f₅ 14 (by omega) (by omega), e₄14]))
      fun m' k ⟨a, b', c, d⟩ => ⟨a, b', c, by omega⟩

theorem updMinKey_time {v nk : ℕ} {s : St} : (ShortestPaths.updMinKey v nk s).time = s.time := by
  unfold ShortestPaths.updMinKey; split_ifs <;> rfl

theorem decKey_run (C : Ctx) {M : Finset ℕ} {v nk : ℕ} {s : St} (hR : Rep L s m)
    (hF : Fixed L x m) (h13 : m 13 = v) (h14 : m 14 = nk) (hH : HeapInv C.n s M) (hv : v ∈ M)
    (hnk : nk < s.key v) (hMr : ∀ w ∈ M, 1 ≤ w ∧ w ≤ L.n) (hdg : ∀ w ∈ M, s.deg w ≤ L.D)
    (hFM : M.card ≤ C.F) (hB : L.top < B) :
    Runs B Prog.decKey m fun m' k => Rep L (ShortestPaths.decKey C v nk s) m' ∧ Fixed L x m' ∧
      Frm L TD m m' ∧ s.time + k ≤ (ShortestPaths.decKey C v nk s).time := by
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hvn := (hMr v hv).2
  have hm : s.hmin ≤ L.n := (hMr _ (hH.min ⟨v, hv⟩).1).2
  have hd0 : s.deg 0 ≤ L.n := (hH.roots.deg0_le).trans (card_le_n hMr)
  set s₁ := St.tick 80 (St.setKey v nk s) with hs₁
  have hbnd : m 13 ≤ L.bnd 0 := by rw [h13]; simp [Lay.bnd]; omega
  unfold Prog.decKey
  refine Runs.seqs_cons (Runs.mono (wr_spec hR (k := 0) (i := 13) (s := 14) (by omega) hbnd
    (by omega) (by omega) (by omega) hB) fun m₁ c₁ ⟨R₁, f₁, hc₁⟩ => ?_)
  have F₁ : Frm L TD m m₁ := Frm.dyn (dyn_arr (k := 0) (by omega) hbnd)
    (.inl (by simp [TC, T267])) f₁ hH32
  rw [h13, h14] at R₁
  have R₁' : Rep L s₁ m₁ := R₁.same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have X₁ : Fixed L x m₁ := hF.frame hH32 F₁.2
  have e₁13 : m₁ 13 = v := by rw [f₁ 13 (by omega) (by omega), h13]
  have e₁14 : m₁ 14 = nk := by rw [f₁ 14 (by omega) (by omega), h14]
  refine Runs.seqs_cons (Runs.mono (rd_spec R₁' (k := 2) (d := 15) (i := 13) (by omega)
    (by rw [e₁13]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₂ c₂ ⟨h₂, f₂, hc₂⟩ => ?_)
  rw [e₁13] at h₂
  have h₂15 : m₂ 15 = s.par v := h₂
  have R₂ := R₁'.regs2 (r₁ := 2) (r₂ := 15) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₂
  have F₂ : Frm L TD m m₂ := F₁.trans (Frm.reg (.inl (by simp [TC])) (by omega) f₂
    (.inl (by simp [TC, T267])))
  have X₂ : Fixed L x m₂ := hF.frame hH32 F₂.2
  have e₂13 : m₂ 13 = v := by rw [f₂ 13 (by omega) (by omega), e₁13]
  have e₂14 : m₂ 14 = nk := by rw [f₂ 14 (by omega) (by omega), e₁14]
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun h0 => ?_) (fun h0 => ?_))
  · rw [h₂15, R₂.zero] at h0
    have e : ShortestPaths.decKey C v nk s = ShortestPaths.updMinKey v nk s₁ := by
      unfold ShortestPaths.decKey; rw [if_pos (show s₁.par v = 0 from h0)]
    rw [e]
    refine Runs.mono (updMinKey_spec R₂ X₂ e₂13 e₂14 hm hB) fun m₃ c₃ ⟨R₃, X₃, F₃, hc₃⟩ => ?_
    refine Runs.seqs_nilR (by omega) fun m₄ h₄ f₄ => ?_
    have F₄ : Frm L TD m₃ m₄ := Frm.reg1 (.inr (by simp [TU])) (by omega) f₄
    refine ⟨R₃.regs1 (r := 2) (by simp [Tmp]) (by omega) f₄, X₃.frame hH32 F₄.2,
      F₂.trans ((F₃.mono fun _ h => .inr h).trans F₄), ?_⟩
    rw [updMinKey_time]
    change s.time + _ ≤ s.time + 80
    omega
  · rw [h₂15, R₂.zero] at h0
    have hf := hH.forest.cutFacts hv h0
    have hpv : s.par v ≠ v := by
      intro hc; have := hH.forest.height v hv h0; rw [hc] at this; omega
    have hpn := (hMr _ hf.pM).2
    have hf₁ : CutFacts s₁ M v (s.par v) := ⟨hf.vM, hf.pM, hf.p0, hf.vp, hf.i_lt, hf.chv, hf.lastM,
      hf.lastp, hf.lastpos⟩
    have hkey : s₁.key (s.par v) = s.key (s.par v) := by
      change update s.key v nk (s.par v) = _; rw [update_of_ne hpv]
    have hpar : s₁.par v = s.par v := rfl
    refine Runs.seqs_cons (Runs.mono (rd_spec R₂ (k := 0) (d := 17) (i := 15) (by omega)
      (by rw [h₂15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
      fun m₃ c₃ ⟨h₃, f₃, hc₃⟩ => ?_)
    rw [h₂15] at h₃
    have R₃ := R₂.regs2 (r₁ := 2) (r₂ := 17) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₃
    refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₄ h₄ f₄ => ?_)
    have R₄ := R₃.regs1 (r := 17) (by simp [Tmp]) (by omega) f₄
    have h₄17 : m₄ 17 = if nk < s.key (s.par v) then 1 else 0 := by
      rw [h₄, f₃ 14 (by omega) (by omega), e₂14, h₃]
      change (if nk < s₁.key (s.par v) then 1 else 0) = _
      rw [hkey]
    have F₄ : Frm L TD m m₄ := F₂.trans ((Frm.reg (.inl (by simp [TC])) (by omega) f₃
      (.inl (by simp [TC, T267]))).trans (Frm.reg1 (.inl (by simp [TC])) (by omega) f₄))
    have X₄ : Fixed L x m₄ := hF.frame hH32 F₄.2
    have e₄13 : m₄ 13 = v := by rw [f₄ 13 (by omega), f₃ 13 (by omega) (by omega), e₂13]
    have e₄14 : m₄ 14 = nk := by rw [f₄ 14 (by omega), f₃ 14 (by omega) (by omega), e₂14]
    have e₄15 : m₄ 15 = s.par v := by rw [f₄ 15 (by omega), f₃ 15 (by omega) (by omega), h₂15]
    refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun hlt => ?_) (fun hlt => ?_))
    · rw [h₄17, R₄.one] at hlt
      have hlt' : nk < s.key (s.par v) := by by_contra hc; simp [hc] at hlt
      have e : ShortestPaths.decKey C v nk s = ShortestPaths.updMinKey v nk (cascFin
          (whileF cascCond cascStep C.F (St.cut v (s.par v) s₁, s.par v))) := by
        unfold ShortestPaths.decKey
        rw [if_neg (show ¬s₁.par v = 0 from h0),
          if_pos (show nk < s₁.key (s₁.par v) by rw [hpar, hkey]; exact hlt')]
        rfl
      rw [e]
      refine Runs.mono (decCut_spec C R₄ X₄ e₄13 e₄14 e₄15 hf₁ (cascInv_start hH hv hnk h0) hMr hdg
        hd0 hm hFM hB) fun m₅ c₅ ⟨R₅, X₅, F₅, hc₅⟩ => ?_
      refine Runs.seqs_nilR (by omega) fun m₆ h₆ f₆ => ?_
      refine Runs.seqs_nilR (by omega) fun m₇ h₇ f₇ => ?_
      have F₇ : Frm L TD m₅ m₇ := (Frm.reg1 (.inr (by simp [TU])) (by omega) f₆).trans
        (Frm.reg1 (.inr (by simp [TU])) (by omega) f₇)
      refine ⟨(R₅.regs1 (r := 2) (by simp [Tmp]) (by omega) f₆).regs1 (r := 2) (by simp [Tmp])
        (by omega) f₇, X₅.frame hH32 F₇.2, F₄.trans (F₅.trans F₇), ?_⟩
      rw [updMinKey_time]
      have : s₁.time = s.time + 80 := rfl
      omega
    · rw [h₄17, R₄.one] at hlt
      have hlt' : ¬nk < s.key (s.par v) := by intro hc; simp [hc] at hlt
      have e : ShortestPaths.decKey C v nk s = s₁ := by
        unfold ShortestPaths.decKey
        rw [if_neg (show ¬s₁.par v = 0 from h0),
          if_neg (show ¬nk < s₁.key (s₁.par v) by rw [hpar, hkey]; exact hlt')]
      rw [e]
      refine Runs.constR (by omega) (by omega) fun m₅ h₅ f₅ => ?_
      refine Runs.seqs_nilR (by omega) fun m₆ h₆ f₆ => ?_
      refine Runs.seqs_nilR (by omega) fun m₇ h₇ f₇ => ?_
      have tD : TD 2 := .inr (by simp [TU])
      have F₇ : Frm L TD m₄ m₇ := (Frm.reg1 tD (by omega) f₅).trans
        ((Frm.reg1 tD (by omega) f₆).trans (Frm.reg1 tD (by omega) f₇))
      refine ⟨((R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅).regs1 (r := 2) (by simp [Tmp])
        (by omega) f₆).regs1 (r := 2) (by simp [Tmp]) (by omega) f₇, X₄.frame hH32 F₇.2,
        F₄.trans F₇, ?_⟩
      have : s₁.time = s.time + 80 := rfl
      omega

end Formalgo.Algorithms.ShortestPaths
