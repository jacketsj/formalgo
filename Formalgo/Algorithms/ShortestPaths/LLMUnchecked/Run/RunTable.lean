import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunMove
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapTable

/-!
# Running the table loop of extraction

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m m' : Mem} {B : ℕ} {x : Input}

theorem Rep.regs2 (h : Rep L σ m) {r₁ r₂ : ℕ} (h1 : Tmp r₁) (h2 : Tmp r₂) (h1' : r₁ < 32)
    (h2' : r₂ < 32) (hf : ∀ a, a ≠ r₁ → a ≠ r₂ → m' a = m a) : Rep L σ m' :=
  h.congr (fun a ha _ => hf a (fun e => ha (e ▸ h1)) (fun e => ha (e ▸ h2)))
    (fun a ha => hf a (by omega) (by omega))

theorem Rep.regs1 (h : Rep L σ m) {r : ℕ} (h1 : Tmp r) (h1' : r < 32)
    (hf : ∀ a, a ≠ r → m' a = m a) : Rep L σ m' :=
  h.congr (fun a ha _ => hf a (fun e => ha (e ▸ h1))) (fun a ha => hf a (by omega))

/-- The registers the table loop uses. -/
def TT (a : ℕ) : Prop := T29 a ∨ a = 11 ∨ a = 13 ∨ a = 14

/-- The table loop's state in memory. -/
structure TabR (L : Lay) (x : Input) (m₀ : Mem) (P : St × ℕ → Prop) (a : St × ℕ) (m : Mem) :
    Prop where
  rep : Rep L a.1 m
  fixed : Fixed L x m
  frm : Frm L TT m₀ m
  r11 : m 11 = a.2
  r13 : m 13 = if L.D < a.2 then 1 else 0
  inv : P a

/-- The end of a table step: `d := d + 1`, and the loop condition. -/
theorem tabTail_spec (hR : Rep L σ m) {d : ℕ} (h11 : m 11 = d) (hd : d ≤ L.D) (hB : L.top < B) :
    Runs B (seqs [add 11 11 3, less 13 28 11]) m fun m' k => Rep L σ m' ∧ m' 11 = d + 1 ∧
      m' 13 = (if L.D < d + 1 then 1 else 0) ∧ Frm L TT m m' ∧ k = 3 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h11, hR.one]; omega) fun m₁ h₁ f₁ => ?_)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₃ h₃ f₃ => ?_
  have h₁11 : m₁ 11 = d + 1 := by rw [h₁, h11, hR.one]
  refine ⟨(hR.regs1 (r := 11) (by simp [Tmp]) (by omega) f₁).regs1 (r := 13) (by simp [Tmp])
    (by omega) f₂ |>.regs1 (r := 2) (by simp [Tmp]) (by omega) f₃,
    by rw [f₃ 11 (by omega), f₂ 11 (by omega), h₁11], ?_,
    (Frm.reg1 (by simp [TT]) (by omega) f₁).trans ((Frm.reg1 (by simp [TT]) (by omega) f₂).trans
      (Frm.reg1 (by simp [TT, T29, T267]) (by omega) f₃)), by omega⟩
  rw [f₃ 13 (by omega), h₂, f₁ 28 (by omega), hR.D, h₁11]

theorem tableBody_spec (C : Ctx) {M : Finset ℕ} {Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B)
    {a : St × ℕ} (h : TabR L x m₀ (TabInv C.D M Q s₀) a m) (hc : tabCond C a) :
    Runs B tableBody m fun m' k => TabR L x m₀ (TabInv C.D M Q s₀) (tabStep a) m' ∧
      a.1.time + k + 2 ≤ (tabStep a).1.time := by
  obtain ⟨s, d⟩ := a
  obtain ⟨hR, hF, hfr, h11, h13, hI⟩ := h
  have hdD : d ≤ C.D := hc
  have h11' : m 11 = d := h11
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hstep := hI.step C hc
  have hd0 : s.deg 0 ≤ L.n := by rw [hLn]; exact hI.roots.deg0_le.trans (card_le_n hM)
  have hmin : s.hmin ≤ L.n := by
    rw [hLn]
    by_cases h0 : s.deg 0 = 0
    · rw [hI.hmin0 h0]; omega
    · exact (hM _ (hI.hmin1 h0).1).2
  unfold tableBody
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 6) (d := 14) (i := 11) (by omega)
    (by rw [h11']; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h11'] at h₁
  have h₁14 : m₁ 14 = s.tbl d := h₁
  have F₁ : Frm L TT m m₁ := Frm.reg (by simp [TT]) (by omega) f₁ (by simp [TT, T29, T267])
  have R₁ : Rep L s m₁ := hR.regs2 (r₁ := 2) (r₂ := 14) (by simp [Tmp]) (by simp [Tmp]) (by omega)
    (by omega) f₁
  have h₁11 : m₁ 11 = d := by rw [f₁ 11 (by omega) (by omega), h11']
  have z₁ : m₁ 8 = 0 := by rw [f₁ 8 (by omega) (by omega), hR.zero]
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun hx => ?_) (fun hx => ?_))
  · -- An empty entry.
    rw [h₁14, z₁] at hx
    refine Runs.constR (by omega) (by omega) fun m₂ h₂ f₂ => ?_
    have e : tabStep (s, d) = (St.tick 40 s, d + 1) := by simp [tabStep, hx]
    rw [e] at hstep ⊢
    refine Runs.mono (tabTail_spec (d := d) (R₁.regs1 (r := 2) (by simp [Tmp]) (by omega) f₂)
      (by rw [f₂ 11 (by omega), h₁11]) (by omega) hB) fun m₃ c₃ ⟨R₃, h₃11, h₃13, F₃, hc₃⟩ => ?_
    have Fall : Frm L TT m m₃ := F₁.trans ((Frm.reg1 (by simp [TT, T29, T267]) (by omega) f₂).trans F₃)
    refine ⟨⟨R₃.same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF.frame hH Fall.2,
      hfr.trans Fall, h₃11, h₃13, hstep.1⟩, ?_⟩
    change s.time + _ + 2 ≤ s.time + 40
    omega
  · -- Move entry `x` to the roots.
    rw [h₁14, z₁] at hx
    have hxT := hI.tbl d hx
    have hxn : s.tbl d ≤ L.n := by rw [hLn]; exact (hM _ hxT.2.1).2
    set xv := s.tbl d with hxv
    have e : tabStep (s, d) = (St.tick 40 (St.updMin xv (St.attach xv 0 (St.setTbl d 0 s))), d + 1) := by
      simp [tabStep, ← hxv, hx]
    rw [e] at hstep ⊢
    refine Runs.seqs_cons (Runs.mono (wr_spec R₁ (k := 6) (i := 11) (s := 8) (by omega)
      (by rw [h₁11]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
      fun m₂ c₂ ⟨R₂, f₂, hc₂⟩ => ?_)
    rw [h₁11, z₁] at R₂
    have hd2 : L.Dyn (L.H + 6 * L.R + m₁ 11) := dyn_arr (k := 6) (by omega)
      (by rw [h₁11]; simp [Lay.bnd]; omega)
    have F₂ : Frm L TT m₁ m₂ := Frm.dyn hd2 (by simp [TT, T29, T267]) f₂ hH
    have g₂ : ∀ r, r < 32 → r ≠ 2 → m₂ r = m₁ r := fun r hr h2 => f₂ r h2 (by omega)
    have X₂ : Fixed L x m₂ := hF.frame hH (F₁.trans F₂).2
    refine Runs.seqs_cons (Runs.mono (attach_spec R₂ X₂ (rv := 14) (rp := 8)
      (by rw [g₂ 14 (by omega) (by omega), h₁14]; exact hxn)
      (by rw [g₂ 8 (by omega) (by omega), z₁]; omega)
      (by rw [g₂ 8 (by omega) (by omega), z₁]; change s.deg 0 < _; simp [Lay.cap]; omega)
      (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₃ c₃ ⟨R₃, X₃, F₃, hc₃⟩ => ?_)
    rw [g₂ 14 (by omega) (by omega), h₁14, g₂ 8 (by omega) (by omega), z₁] at R₃
    have g₃ : ∀ r, r < 32 → ¬T267 r → m₃ r = m₂ r := F₃.1
    refine Runs.seqs_cons (Runs.mono (updMin_spec R₃ X₃ (rv := 14)
      (by rw [g₃ 14 (by omega) (by simp [T267]), g₂ 14 (by omega) (by omega), h₁14]; exact hxn)
      (by change s.hmin ≤ _; exact hmin) (by omega) (by simp [T29, T267]) hB)
      fun m₄ c₄ ⟨R₄, X₄, F₄, hc₄⟩ => ?_)
    rw [g₃ 14 (by omega) (by simp [T267]), g₂ 14 (by omega) (by omega), h₁14] at R₄
    refine Runs.seqs_nilR (by omega) fun m₅ h₅ f₅ => ?_
    have R₅ := R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅
    have g₄ : ∀ r, r < 32 → ¬T29 r → m₄ r = m₃ r := F₄.1
    have h₅11 : m₅ 11 = d := by
      rw [f₅ 11 (by omega), g₄ 11 (by omega) (by simp [T29, T267]), g₃ 11 (by omega) (by simp [T267]),
        g₂ 11 (by omega) (by omega), h₁11]
    refine Runs.mono (tabTail_spec R₅ h₅11 (by omega) hB) fun m₆ c₆ ⟨R₆, h₆11, h₆13, F₆, hc₆⟩ => ?_
    have Fall : Frm L TT m m₆ := F₁.trans (F₂.trans ((F₃.mono fun a ha => Or.inl (Or.inl ha)).trans
      ((F₄.mono fun a ha => Or.inl ha).trans ((Frm.reg1 (by simp [TT, T29, T267]) (by omega) f₅).trans
        F₆))))
    refine ⟨⟨R₆.same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF.frame hH Fall.2,
      hfr.trans Fall, h₆11, h₆13, hstep.1⟩, ?_⟩
    change s.time + _ + 2 ≤ (St.updMin xv (St.attach xv 0 (St.setTbl d 0 s))).time + 40
    have : (St.updMin xv (St.attach xv 0 (St.setTbl d 0 s))).time = s.time :=
      updMin_of (fun t => t.time = s.time) (fun _ => rfl) rfl
    omega

theorem tableLoop_spec (C : Ctx) {M : Finset ℕ} {Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B)
    (hFu : C.n + C.D + 1 ≤ C.F) {a : St × ℕ} (h : TabR L x m₀ (TabInv C.D M Q s₀) a m) :
    Runs B (loop 13 8 tableBody) m fun m' k =>
      TabR L x m₀ (TabInv C.D M Q s₀) (whileF (tabCond C) tabStep C.F a) m' ∧
        a.1.time + k ≤ (whileF (tabCond C) tabStep C.F a).1.time + 1 ∧
        ¬tabCond C (whileF (tabCond C) tabStep C.F a) := by
  have ht := top_ge (L := L)
  have hH := h.rep.H32
  have hloop := tab_loop C h.inv (by omega)
  refine Runs.mono (Runs.loop_refine (TabR L x m₀ (TabInv C.D M Q s₀)) (tabCond C) tabStep
    (fun a => a.1.time) (by omega) (by omega) (fun a m hR => ?_)
    (fun a m hR hc => tableBody_spec C hLn hLD hM hB hR hc) C.F a m h hloop.2)
    fun m' k ⟨hR, hk⟩ => ⟨hR, hk, hloop.2⟩
  rw [hR.r13, hR.rep.zero]
  simp only [tabCond]
  rw [hLD]
  constructor
  · intro he; split_ifs at he with hp <;> omega
  · intro hle; rw [if_neg (by omega)]

end Formalgo.Algorithms.ShortestPaths
