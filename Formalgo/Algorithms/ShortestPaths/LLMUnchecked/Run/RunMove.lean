import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunPop

/-!
# Running the moves of extraction

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

/-- The registers the move loop uses. -/
def TM (a : ℕ) : Prop := T267 a ∨ a = 11 ∨ a = 13 ∨ a = 14

theorem TM_tmp {a : ℕ} (h : TM a) : Tmp a := by
  rcases h with (h | h | h) | h | h | h <;> simp [Tmp, h]

/-- The move loop's state in memory. -/
structure MoveR (L : Lay) (x : EInput) (m₀ : Mem) (P : St × ℕ → Prop) (a : St × ℕ) (m : Mem) :
    Prop where
  rep : Rep L a.1 m
  fixed : Fixed L x m
  frm : Frm L TM m₀ m
  r30 : m 30 = a.2
  r13 : m 13 = if 0 < a.1.deg a.2 then 1 else 0
  inv : P a

theorem moveBody_spec (C : Ctx) {M : Finset ℕ} {z Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hD : C.D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) {a : St × ℕ}
    (h : MoveR L x m₀ (MoveInv M z Q s₀) a m) (hc : moveCond a) :
    Runs B moveBody m fun m' k => MoveR L x m₀ (MoveInv M z Q s₀) (moveStep a) m' ∧
      a.1.time + k + 2 ≤ (moveStep a).1.time := by
  obtain ⟨s, z'⟩ := a
  obtain ⟨hR, hF, hfr, h30, h13, hI⟩ := h
  simp only [moveCond] at hc h30 h13 hI
  have hz := hI.z_eq
  simp only at hz
  subst hz
  have hc' : s.deg z' ≠ 0 := hc
  have h30' : m 30 = z' := h30
  have hzM : z' ∈ M := hI.zM
  have hzn : z' ≤ L.n := by rw [hLn]; exact (hM _ hzM).2
  have hz0 : z' ≠ 0 := by have := (hM _ hzM).1; omega
  have hdz : s.deg z' < C.D := by rw [hD]; exact hI.forest.deg_lt hM hzM
  have hd0 : s.deg 0 ≤ L.n := by rw [hLn]; exact hI.roots.deg0_le.trans (card_le_n hM)
  obtain ⟨c1, c2, c3⟩ := hI.forest.down z' hzM (s.deg z' - 1) (show s.deg z' - 1 < s.deg z' by omega)
  have hcn : s.ch z' (s.deg z' - 1) ≤ L.n := by rw [hLn]; exact (hM _ c1).2
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hstep := hI.step hc
  have hms : moveStep (s, z') = (St.tick 30 (St.attach (s.ch z' (update s.deg z' (s.deg z' - 1) z')) 0
      (setFld 3 z' (s.deg z' - 1) s)), z') := rfl
  rw [update_self] at hms
  rw [hms] at hstep ⊢
  unfold moveBody
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 3) (d := 11) (i := 30) (by omega)
    (by rw [h30]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h30] at h₁
  refine Runs.seqs_cons (Runs.subR (by omega) (by omega) (by omega)
    (by rw [h₁, f₁ 3 (by omega) (by omega), hR.one]; change 1 ≤ s.deg z'; omega)
    fun m₂ h₂ f₂ => ?_)
  have h₂11 : m₂ 11 = s.deg z' - 1 := by rw [h₂, h₁, f₁ 3 (by omega) (by omega), hR.one]; rfl
  have F₂ : Frm L TM m m₂ := (Frm.reg (by simp [TM]) (by omega) f₁ (by simp [TM, T267])).trans
    (Frm.reg1 (by simp [TM]) (by omega) f₂)
  have R₂ : Rep L s m₂ := hR.reg (T := TM) (fun a ha => TM_tmp ha) F₂
    (fun a ha => by rw [f₂ a (by omega), f₁ a (by omega) (by omega)])
  have g₂ : ∀ r, r ≠ 2 → r ≠ 11 → m₂ r = m r := fun r a2 a11 => by rw [f₂ r a11, f₁ r a2 a11]
  refine Runs.seqs_cons (Runs.mono (wr_spec R₂ (k := 3) (i := 30) (s := 11) (by omega)
    (by rw [g₂ 30 (by omega) (by omega), h30]; simp [Lay.bnd]; omega) (by omega) (by omega)
    (by omega) hB) fun m₃ c₃ ⟨R₃, f₃, hc₃⟩ => ?_)
  rw [g₂ 30 (by omega) (by omega), h30, h₂11] at R₃
  have hd3 : L.Dyn (L.H + 3 * L.R + m₂ 30) := dyn_arr (k := 3) (by omega)
    (by rw [g₂ 30 (by omega) (by omega), h30]; simp [Lay.bnd]; omega)
  have F₃ : Frm L TM m m₃ := F₂.trans (Frm.dyn hd3 (by simp [TM, T267]) f₃ hH)
  have g₃ : ∀ r, r < 32 → r ≠ 2 → m₃ r = m₂ r := fun r hr h2 => f₃ r h2 (by omega)
  have X₃ : Fixed L x m₃ := hF.frame hH F₃.2
  refine Runs.seqs_cons (Runs.mono (chRd_spec R₃ X₃ (d := 14) (p := 30) (j := 11)
    (by rw [g₃ 30 (by omega) (by omega), g₂ 30 (by omega) (by omega), h30]; omega)
    (by rw [g₃ 30 (by omega) (by omega), g₂ 30 (by omega) (by omega), h30,
          g₃ 11 (by omega) (by omega), h₂11]; simp [Lay.cap, hz0]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hB) fun m₄ c₄ ⟨h₄, f₄, hc₄⟩ => ?_)
  rw [g₃ 30 (by omega) (by omega), g₂ 30 (by omega) (by omega), h30, g₃ 11 (by omega) (by omega),
    h₂11] at h₄
  have h₄14 : m₄ 14 = s.ch z' (s.deg z' - 1) := h₄
  have R₄ := R₃.reg (T := TM) (fun a ha => TM_tmp ha)
    (Frm.reg (by simp [TM]) (by omega) f₄ (by simp [TM, T267])) (fun a ha => f₄ a (by omega) (by omega))
  have X₄ : Fixed L x m₄ := X₃.frame hH (Frm.reg (L := L) (T := TM) (by simp [TM]) (by omega) f₄
    (by simp [TM, T267])).2
  have z₄ : m₄ 8 = 0 := by
    rw [f₄ 8 (by omega) (by omega), g₃ 8 (by omega) (by omega), g₂ 8 (by omega) (by omega), hR.zero]
  refine Runs.seqs_cons (Runs.mono (attach_spec R₄ X₄ (rv := 14) (rp := 8)
    (by rw [h₄14]; exact hcn) (by rw [z₄]; omega)
    (by rw [z₄]; change update s.deg z' _ 0 < _; rw [update_of_ne (Ne.symm hz0)]
        simp [Lay.cap]; omega)
    (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₅ c₅ ⟨R₅, X₅, F₅, hc₅⟩ => ?_)
  rw [h₄14, z₄] at R₅
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₆ h₆ f₆ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₇ h₇ f₇ => ?_
  have F₇ : Frm L TM m₃ m₇ := (Frm.reg (by simp [TM]) (by omega) f₄ (by simp [TM, T267])).trans
    ((F₅.mono fun a ha => Or.inl ha).trans ((Frm.reg1 (by simp [TM]) (by omega) f₆).trans
      (Frm.reg1 (by simp [TM, T267]) (by omega) f₇)))
  have Fall : Frm L TM m m₇ := F₃.trans F₇
  have R₇ := R₅.reg (T := TM) (fun a ha => TM_tmp ha) ((Frm.reg1 (by simp [TM]) (by omega) f₆).trans
    (Frm.reg1 (by simp [TM, T267]) (by omega) f₇)) (fun a ha => by rw [f₇ a (by omega), f₆ a (by omega)])
  have g₅ : ∀ r, r < 32 → ¬T267 r → m₅ r = m₄ r := F₅.1
  refine ⟨⟨R₇.same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hF.frame hH Fall.2,
    hfr.trans Fall, ?_, ?_, hstep.1⟩, ?_⟩
  · rw [f₇ 30 (by omega), f₆ 30 (by omega), g₅ 30 (by omega) (by simp [T267]), f₄ 30 (by omega) (by omega),
      g₃ 30 (by omega) (by omega), g₂ 30 (by omega) (by omega), h30]
  · rw [f₇ 13 (by omega), h₆, g₅ 8 (by omega) (by simp [T267]), z₄, g₅ 11 (by omega) (by simp [T267]),
      f₄ 11 (by omega) (by omega), g₃ 11 (by omega) (by omega), h₂11]
    change _ = if 0 < update (update s.deg z' (s.deg z' - 1)) 0 _ z' then 1 else 0
    rw [update_of_ne hz0, update_self]
  · change s.time + _ + 2 ≤ s.time + 30
    omega

theorem moveLoop_spec (C : Ctx) {M : Finset ℕ} {z Q : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = C.D) (hD : C.D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) (hFu : C.n + C.D + 1 ≤ C.F) {a : St × ℕ}
    (h : MoveR L x m₀ (MoveInv M z Q s₀) a m) :
    Runs B (loop 13 3 moveBody) m fun m' k =>
      MoveR L x m₀ (MoveInv M z Q s₀) (whileF moveCond moveStep C.F a) m' ∧
        a.1.time + k ≤ (whileF moveCond moveStep C.F a).1.time + 1 ∧
        (whileF moveCond moveStep C.F a).1.deg z = 0 := by
  have ht := top_ge (L := L)
  have hH := h.rep.H32
  have hz := h.inv.z_eq
  have hdz : a.1.deg z ≤ C.F := by
    have := h.inv.forest.deg_lt hM h.inv.zM; rw [← hD] at this; omega
  have hloop := move_loop C h.inv hdz
  refine Runs.mono (Runs.loop_refine (MoveR L x m₀ (MoveInv M z Q s₀)) moveCond moveStep
    (fun a => a.1.time) (by omega) (by omega) (fun a m hR => ?_)
    (fun a m hR hc => moveBody_spec C hLn hLD hD hM hB hR hc) C.F a m h
    (by simp only [moveCond, not_not]; rw [hloop.1.z_eq]; exact hloop.2))
    fun m' k ⟨hR, hk⟩ => ⟨hR, hk, hloop.2⟩
  rw [hR.r13, hR.rep.one]
  simp only [moveCond]
  constructor
  · intro he; split_ifs at he with hp <;> omega
  · intro hne; rw [if_pos (by omega)]

end Formalgo.Algorithms.ShortestPaths
