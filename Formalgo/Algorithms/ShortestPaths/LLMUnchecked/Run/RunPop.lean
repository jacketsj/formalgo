import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunLink

/-!
# Running the pops of consolidation

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

/-- The registers the pop loop uses. -/
def TP (a : ℕ) : Prop := TL a ∨ a = 13

theorem TP_tmp {a : ℕ} (h : TP a) : Tmp a := by
  rcases h with h | h
  · exact TL_tmp h
  · simp [Tmp, h]

/-- The pop loop's state in memory. -/
structure PopR (L : Lay) (x : EInput) (m₀ : Mem) (P : St → Prop) (s : St) (m : Mem) : Prop where
  rep : Rep L s m
  fixed : Fixed L x m
  frm : Frm L TP m₀ m
  r13 : m 13 = if 0 < s.deg 0 then 1 else 0
  inv : P s

theorem Same.popFin (b : St × ℕ × ℕ) : Same (setFld 6 b.2.2 b.2.1 b.1) (popFin b) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem popBody_spec (C : Ctx) {M : Finset ℕ} {Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hD : C.D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) (hFu : C.D ≤ C.F) {s : St}
    (h : PopR L x m₀ (PopInv C.D M Q s₀) s m) (hc : rootsCond s) :
    Runs B popBody m fun m' k => PopR L x m₀ (PopInv C.D M Q s₀) (popStep C s) m' ∧
      s.time + k + 2 ≤ (popStep C s).time := by
  obtain ⟨hR, hF, hfr, h13, hI⟩ := h
  have hc' : s.deg 0 ≠ 0 := hc
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hd0 : s.deg 0 ≤ L.n := by rw [hLn]; exact hI.roots.deg0_le.trans (card_le_n hM)
  obtain ⟨hLI, h65⟩ := hI.start hc
  set xv := s.ch 0 (s.deg 0 - 1) with hxv
  have hxM : xv ∈ M := hLI.xM
  have hxn : xv ≤ L.n := by rw [hLn]; exact (hM _ hxM).2
  have hx0 : xv ≠ 0 := by have := (hM _ hxM).1; omega
  have hdx : s.deg xv < C.D := by rw [hD]; exact hI.forest.deg_lt hM hxM
  have hb3 : m 21 = L.H + 3 * L.R := hR.base 3 (by omega)
  have hpop : popStep C s = popFin (whileF linkCond linkStep C.F (popDeg s,
      s.ch 0 (update s.deg 0 (s.deg 0 - 1) 0),
      (popDeg s).deg (s.ch 0 (update s.deg 0 (s.deg 0 - 1) 0)))) := rfl
  rw [update_self] at hpop
  rw [hpop]
  unfold popBody
  -- `M[11] := deg 0 - 1`, stored back.
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₁ h₁ f₁ => ?_)
  have h₁11 : m₁ 11 = s.deg 0 := by
    rw [h₁, hb3]; have := hR.arr 3 (by omega) 0 (by simp [Lay.bnd]); rw [Nat.add_zero] at this
    exact this
  refine Runs.seqs_cons (Runs.subR (by omega) (by omega) (by omega)
    (by rw [h₁11, f₁ 3 (by omega), hR.one]; omega) fun m₂ h₂ f₂ => ?_)
  have h₂11 : m₂ 11 = s.deg 0 - 1 := by rw [h₂, h₁11, f₁ 3 (by omega), hR.one]
  have F₂ : Frm L TP m m₂ := (Frm.reg1 (by simp [TP, TL]) (by omega) f₁).trans
    (Frm.reg1 (by simp [TP, TL]) (by omega) f₂)
  have R₂ : Rep L s m₂ := hR.reg (T := TP) (fun a ha => TP_tmp ha) F₂
    (fun a ha => by rw [f₂ a (by omega), f₁ a (by omega)])
  have g₂ : ∀ r, r ≠ 11 → m₂ r = m r := fun r hr => by rw [f₂ r hr, f₁ r hr]
  refine Runs.seqs_cons (Runs.store (by omega) (by omega) ?_)
  rw [g₂ 21 (by omega), hb3, h₂11]
  have R₃ : Rep L (popDeg s) (update m₂ (L.H + 3 * L.R) (s.deg 0 - 1)) := by
    have := R₂.store (k := 3) (i := 0) (v := s.deg 0 - 1) (by omega) (by simp [Lay.bnd])
    rw [Nat.add_zero] at this; exact this
  set m₃ := update m₂ (L.H + 3 * L.R) (s.deg 0 - 1) with hm₃
  have hdyn3 : L.Dyn (L.H + 3 * L.R) := by
    have := dyn_arr (L := L) (k := 3) (i := 0) (by omega) (by simp [Lay.bnd])
    rw [Nat.add_zero] at this; exact this
  have F₃ : Frm L TP m m₃ := F₂.trans ⟨fun a ha _ => by rw [hm₃, update_of_ne (by omega)],
    fun a _ hd => by rw [hm₃, update_of_ne (by rintro rfl; exact hd hdyn3)]⟩
  have g₃ : ∀ r, r < 32 → r ≠ 11 → m₃ r = m r := fun r hr h11 => by
    rw [hm₃, update_of_ne (by omega), g₂ r h11]
  have X₃ : Fixed L x m₃ := hF.frame hH F₃.2
  -- `x := ch 0 (deg 0 - 1)`, `dx := deg x`, `y := tbl dx`.
  refine Runs.seqs_cons (Runs.mono (chRd_spec R₃ X₃ (d := 14) (p := 8) (j := 11)
    (by rw [g₃ 8 (by omega) (by omega), hR.zero]; omega)
    (by rw [g₃ 8 (by omega) (by omega), hR.zero, hm₃, update_of_ne (by omega), h₂11]
        simp [Lay.cap]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hB) fun m₄ c₄ ⟨h₄, f₄, hc₄⟩ => ?_)
  rw [g₃ 8 (by omega) (by omega), hR.zero, hm₃, update_of_ne (by omega), h₂11] at h₄
  have h₄14 : m₄ 14 = xv := h₄
  have R₄ : Rep L (popDeg s) m₄ := R₃.reg (T := TP) (fun a ha => TP_tmp ha)
    (Frm.reg (by simp [TP, TL]) (by omega) f₄ (by simp [TP, TL, T267]))
    (fun a ha => f₄ a (by omega) (by omega))
  refine Runs.seqs_cons (Runs.mono (rd_spec R₄ (k := 3) (d := 15) (i := 14) (by omega)
    (by rw [h₄14]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₅ c₅ ⟨h₅, f₅, hc₅⟩ => ?_)
  rw [h₄14] at h₅
  have hpd : (popDeg s).deg xv = s.deg xv := by
    change update s.deg 0 _ xv = _; rw [update_of_ne hx0]
  have h₅15 : m₅ 15 = (popDeg s).deg xv := h₅
  have R₅ : Rep L (popDeg s) m₅ := R₄.reg (T := TP) (fun a ha => TP_tmp ha)
    (Frm.reg (by simp [TP, TL]) (by omega) f₅ (by simp [TP, TL, T267]))
    (fun a ha => f₅ a (by omega) (by omega))
  refine Runs.seqs_cons (Runs.mono (rd_spec R₅ (k := 6) (d := 12) (i := 15) (by omega)
    (by rw [h₅15, hpd]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₆ c₆ ⟨h₆, f₆, hc₆⟩ => ?_)
  rw [h₅15] at h₆
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₇ h₇ f₇ => ?_)
  have F₇ : Frm L TL m₃ m₇ := (Frm.reg (by simp [TL]) (by omega) f₄ (by simp [TL, T267])).trans
    ((Frm.reg (by simp [TL]) (by omega) f₅ (by simp [TL, T267])).trans
      ((Frm.reg (by simp [TL]) (by omega) f₆ (by simp [TL, T267])).trans
        (Frm.reg1 (by simp [TL]) (by omega) f₇)))
  have R₇ : Rep L (popDeg s) m₇ := R₅.reg (T := TL) (fun a ha => TL_tmp ha)
    ((Frm.reg (by simp [TL]) (by omega) f₆ (by simp [TL, T267])).trans
      (Frm.reg1 (by simp [TL]) (by omega) f₇))
    (fun a ha => by rw [f₇ a (by omega), f₆ a (by omega) (by omega)])
  have hLR : LinkR L x m₃ (LinkInv C.D M (Q - 25) (s.deg 0 - 1) s₀)
      (popDeg s, xv, (popDeg s).deg xv) m₇ := by
    refine ⟨R₇, hF.frame hH (F₃.trans (F₇.mono fun a ha => Or.inl ha)).2,
      F₇, ?_, ?_, ?_, ?_, hLI⟩
    · rw [f₇ 14 (by omega), f₆ 14 (by omega) (by omega), f₅ 14 (by omega) (by omega), h₄14]
    · rw [f₇ 15 (by omega), f₆ 15 (by omega) (by omega), h₅15]
    · rw [f₇ 12 (by omega), h₆]; rfl
    · rw [h₇, f₆ 8 (by omega) (by omega), f₅ 8 (by omega) (by omega), f₄ 8 (by omega) (by omega),
        g₃ 8 (by omega) (by omega), hR.zero, h₆]; rfl
  -- The links.
  refine Runs.seqs_cons (Runs.mono (linkLoop_spec C hLn hLD hD hM hB hFu hLR)
    fun m₈ c₈ ⟨hL8, hk8, hstop⟩ => ?_)
  set b := whileF linkCond linkStep C.F (popDeg s, xv, (popDeg s).deg xv) with hb
  have hbI := hL8.inv
  have hbx : b.2.1 ∈ M := hbI.xM
  have hbdx : b.2.2 < C.D := by rw [← hbI.xdeg, hD]; exact hbI.forest.deg_lt hM hbx
  -- `tbl dx := x`
  refine Runs.seqs_cons (Runs.mono (wr_spec hL8.rep (k := 6) (i := 15) (s := 14) (by omega)
    (by rw [hL8.r15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₉ c₉ ⟨R₉, f₉, hc₉⟩ => ?_)
  rw [hL8.r15, hL8.r14] at R₉
  have hd9 : L.Dyn (L.H + 6 * L.R + m₈ 15) := dyn_arr (k := 6) (by omega)
    (by rw [hL8.r15]; simp [Lay.bnd]; omega)
  have F₉ : Frm L TP m₈ m₉ := Frm.dyn hd9 (by simp [TP, TL, T267]) f₉ hH
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₁₀ h₁₀ f₁₀ => ?_)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₁₁ h₁₁ f₁₁ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₁₂ h₁₂ f₁₂ => ?_
  have F₁₂ : Frm L TP m₉ m₁₂ := (Frm.reg1 (by simp [TP, TL]) (by omega) f₁₀).trans
    ((Frm.reg1 (by simp [TP]) (by omega) f₁₁).trans (Frm.reg1 (by simp [TP, TL, T267])
        (by omega) f₁₂))
  have Fall : Frm L TP m m₁₂ := F₃.trans
    ((hL8.frm.mono fun a ha => Or.inl ha).trans (F₉.trans F₁₂))
  have R₁₂ := R₉.reg (T := TP) (fun a ha => TP_tmp ha) F₁₂ (fun a ha => by
    rw [f₁₂ a (by omega), f₁₁ a (by omega), f₁₀ a (by omega)])
  have hfin := PopInv.finish C hbI hstop h65 hM hD
  have hb21 : m₉ 21 = L.H + 3 * L.R := R₉.base 3 (by omega)
  have h₁₀11 : m₁₀ 11 = b.1.deg 0 := by
    rw [h₁₀, hb21]; have := R₉.arr 3 (by omega) 0 (by simp [Lay.bnd]); rw [Nat.add_zero] at this
    exact this
  refine ⟨⟨R₁₂.same (Same.popFin b), hF.frame hH Fall.2, hfr.trans Fall, ?_, hfin.1⟩, ?_⟩
  · rw [f₁₂ 13 (by omega), h₁₁, f₁₀ 8 (by omega), f₉ 8 (by omega) (by omega)]
    rw [show m₈ 8 = 0 from by rw [hL8.frm.1 8 (by omega) (by simp [TL, T267]),
      g₃ 8 (by omega) (by omega), hR.zero], h₁₀11]
    rfl
  · change s.time + _ + 2 ≤ b.1.time + 25
    have : (popDeg s, xv, (popDeg s).deg xv).1.time = s.time := rfl
    omega

theorem popLoop_spec (C : Ctx) {M : Finset ℕ} {Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hD : C.D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) (hFu : C.n + C.D + 1 ≤ C.F) {s : St}
    (h : PopR L x m₀ (PopInv C.D M Q s₀) s m) :
    Runs B (loop 13 3 popBody) m fun m' k =>
      PopR L x m₀ (PopInv C.D M Q s₀) (whileF rootsCond (popStep C) C.F s) m' ∧
        s.time + k ≤ (whileF rootsCond (popStep C) C.F s).time + 1 ∧
        (whileF rootsCond (popStep C) C.F s).deg 0 = 0 := by
  have ht := top_ge (L := L)
  have hH := h.rep.H32
  have hd0 : s.deg 0 ≤ C.F := by
    have := h.inv.roots.deg0_le.trans (card_le_n hM); omega
  have hloop := pop_loop C h.inv hM hD (by omega) hd0
  refine Runs.mono (Runs.loop_refine (PopR L x m₀ (PopInv C.D M Q s₀)) rootsCond (popStep C)
    (fun s => s.time) (by omega) (by omega) (fun s m hR => ?_)
    (fun s m hR hc => popBody_spec C hLn hLD hD hM hB (by omega) hR hc) C.F s m h
    (by simp only [rootsCond, not_not]; exact hloop.2))
    fun m' k ⟨hR, hk⟩ => ⟨hR, hk, hloop.2⟩
  rw [hR.r13, hR.rep.one]
  simp only [rootsCond]
  constructor
  · intro he; split_ifs at he with hp; omega
  · intro hne; rw [if_pos (by omega)]

end Formalgo.Algorithms.ShortestPaths
