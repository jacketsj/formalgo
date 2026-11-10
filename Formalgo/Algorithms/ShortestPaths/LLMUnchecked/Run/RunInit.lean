import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunBuild

/-!
# Running the child-array addresses and the source

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m m' : Mem} {B : ℕ} {x : EInput}

theorem Lst.frame' (hm : ∀ a, L.HE ≤ a → a < L.CH → m' a = m a) :
    ∀ (l : List (ℕ × ℕ)) (h : ℕ), Lst L m h l → Lst L m' h l
  | [], h, hl => hl
  | (v, w) :: l, h, ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨h1, h2, by rw [hm _ (by omega) (by omega)]; exact h3,
      by rw [hm _ (by omega) (by omega)]; exact h4, ?_⟩
    rw [hm h h1 (by omega)]
    exact Lst.frame' hm l _ h5

/-- The addresses of the child arrays. -/
def H8 (L : Lay) : ℕ := L.H + 8 * L.R

/-- The registers `cbInit` uses. -/
def TB (a : ℕ) : Prop := a = 2 ∨ a = 14 ∨ a = 15 ∨ a = 30 ∨ a = 31

theorem TB_BT {a : ℕ} (h : TB a) : BT a := by
  simp only [TB] at h; simp only [BT]; omega

/-- The array of addresses: entries below `v` are set. -/
structure CbR (L : Lay) (m₀ : Mem) (v : ℕ) (m : Mem) : Prop where
  ok : Pre L m
  r13 : m 30 = v
  r15 : m 15 = L.CH + (L.n + 1) + (v - 1) * (L.D + 1)
  r14 : m 14 = L.D + 1
  r31 : m 31 = if L.n < v then 1 else 0
  set : ∀ j, j < v → m (H8 L + j) = L.cb j
  lo : ∀ a, a < 32 → ¬TB a → m a = m₀ a
  hi : ∀ a, 32 ≤ a → (a < H8 L ∨ H8 L + L.R ≤ a) → m a = m₀ a

/-- Set the entry of `v`, and move on. -/
theorem cbBody_spec {m₀ : Mem} {v : ℕ} (h : CbR L m₀ v m) (h1 : 1 ≤ v) (hv : v ≤ L.n)
    (hB : L.top < B) :
    Runs B cbBody m fun m' k => CbR L m₀ (v + 1) m' ∧ k ≤ 6 := by
  obtain ⟨hP, r30, r15, r14, r31, hset, lo, hi⟩ := h
  have hcb : L.cb v = L.CH + (L.n + 1) + (v - 1) * (L.D + 1) := by
    unfold Lay.cb; rw [if_neg (by omega)]
  have hstep : L.cb v + (L.D + 1) = L.CH + (L.n + 1) + (v + 1 - 1) * (L.D + 1) := by
    rw [hcb, show v + 1 - 1 = v - 1 + 1 by omega, Nat.succ_mul]; omega
  have hvn : v * (L.D + 1) ≤ L.n * (L.D + 1) := Nat.mul_le_mul_right _ hv
  have facts : L.cb v + (L.D + 1) < B ∧ (∀ {r}, r < 32 → r < B) ∧ H8 L + v < B ∧ v + 1 < B ∧
      32 ≤ H8 L + v ∧ v < L.R ∧ (∀ {a}, L.Dyn a → a ≠ H8 L + v) ∧ (∀ {a},
          a < 32 → a ≠ H8 L + v) := by
    have H32 := hP.H32
    have ht := top_ge (L := L)
    have hCH := CH_ge (L := L)
    have hRn : L.n + L.D + 3 = L.R := rfl
    have hTop : L.top = L.CH + (L.n + 1) + L.n * (L.D + 1) := rfl
    have hs : (v + 1 - 1) * (L.D + 1) = v * (L.D + 1) := by simp
    rw [hs] at hstep
    unfold H8
    refine ⟨?_, fun h => ?_, ?_, ?_, ?_, ?_, fun hd => ?_, fun h => ?_⟩
    all_goals first | omega | (unfold Lay.Dyn at hd; omega)
  obtain ⟨cB, rB, aB, vB, a32, vR, dyn, low⟩ := facts
  have b8 : m 26 = H8 L := hP.base 8 (by omega)
  have br : breg 8 = 26 := rfl
  have one : m 3 = 1 := hP.one
  have hn : m 27 = L.n := hP.n
  unfold cbBody
  refine Runs.seqs_cons (Runs.seq (Runs.addR (rB (by decide)) (by rw [br]; exact rB (by decide))
    (rB (by decide)) (by rw [br, b8, r30]; exact aB) fun m₁ g₁ f₁ =>
      Runs.store (rB (by decide)) (rB (by decide)) ?_))
  rw [br, b8, r30] at g₁
  rw [g₁, f₁ 15 (by decide), r15, ← hcb]
  set m₂ := update m₁ (H8 L + v) (L.cb v) with hm₂
  have f₂ : ∀ a, a ≠ H8 L + v → m₂ a = m₁ a := fun a h => update_of_ne h _ _
  have s₂ : m₂ (H8 L + v) = L.cb v := update_self _ _ _
  have e₂ : ∀ a, a ≠ 2 → a ≠ H8 L + v → m₂ a = m a := fun a h h' => by rw [f₂ a h', f₁ a h]
  have y15 : m₂ 15 = L.cb v := by rw [e₂ 15 (by decide) (low (by decide)), r15, hcb]
  have y14 : m₂ 14 = L.D + 1 := by rw [e₂ 14 (by decide) (low (by decide)), r14]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [y15, y14]; exact cB) fun m₃ g₃ f₃ => ?_)
  rw [y15, y14, hstep] at g₃
  have y30 : m₃ 30 = v := by
    rw [f₃ 30 (by decide), e₂ 30 (by decide) (low (by decide)), r30]
  have y3 : m₃ 3 = 1 := by
    rw [f₃ 3 (by decide), e₂ 3 (by decide) (low (by decide)), one]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [y30, y3]; exact vB) fun m₄ g₄ f₄ => ?_)
  rw [y30, y3] at g₄
  refine Runs.seqs_cons (Runs.lessR (rB (by decide)) (rB (by decide)) (rB (by decide))
    fun m₅ g₅ f₅ => ?_)
  have y27 : m₄ 27 = L.n := by
    rw [f₄ 27 (by decide), f₃ 27 (by decide), e₂ 27 (by decide) (low (by decide)), hn]
  rw [y27, g₄] at g₅
  refine Runs.seqs_nilR (rB (by decide)) fun m₆ g₆ f₆ => ?_
  have E : ∀ a, a ≠ 2 → a ≠ 15 → a ≠ 30 → a ≠ 31 → a ≠ H8 L + v → m₆ a = m a :=
    fun a a2 a15 a30 a31 ah => by
      rw [f₆ a a2, f₅ a a31, f₄ a a30, f₃ a a15, e₂ a a2 ah]
  have dyn32 : ∀ {a}, L.Dyn a → 32 ≤ a := fun hd => by
    have H32 := hP.H32
    have hCH := CH_ge (L := L)
    unfold Lay.Dyn at hd
    omega
  have hH8 : 32 ≤ H8 L := by
    have H32 := hP.H32
    unfold H8; omega
  refine ⟨⟨hP.keep (fun a ha hT => E a (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e])) (low ha))
      (fun a hd => have h := dyn32 hd
        E a (by omega) (by omega) (by omega) (by omega) (dyn hd)), ?_, ?_, ?_, ?_, fun j hj => ?_,
      fun a ha hT => ?_, fun a ha hr => ?_⟩, by norm_num⟩
  · rw [f₆ 30 (by decide), f₅ 30 (by decide), g₄]
  · rw [f₆ 15 (by decide), f₅ 15 (by decide), f₄ 15 (by decide), g₃]
  · rw [E 14 (by decide) (by decide) (by decide) (by decide) (low (by decide)), r14]
  · rw [f₆ 31 (by decide), g₅]
  · rcases Nat.lt_or_ge j v with hlt | hge
    · rw [E _ (by omega) (by omega) (by omega) (by omega) (by omega), hset j hlt]
    · have hj' : j = v := by omega
      subst hj'
      rw [f₆ _ (by omega), f₅ _ (by omega), f₄ _ (by omega), f₃ _ (by omega), s₂]
  · rw [E a (fun e => hT (by simp [TB, e])) (fun e => hT (by simp [TB, e]))
      (fun e => hT (by simp [TB, e])) (fun e => hT (by simp [TB, e])) (low ha), lo a ha hT]
  · rw [E a (by omega) (by omega) (by omega) (by omega) (by omega), hi a ha hr]

theorem cbInit_run {adj : ℕ → List (ℕ × ℕ)} (hP : Pre L m) (h13 : m 13 = L.CH)
    (hl : ∀ v ≤ L.n, Lst L m (m (H7 L + v)) (adj v)) (hB : L.top < B) :
    Runs B cbInit m fun m' k => Pre L m' ∧ (∀ v ≤ L.n, m' (H8 L + v) = L.cb v) ∧
      (∀ v ≤ L.n, Lst L m' (m' (H7 L + v)) (adj v)) ∧ (∀ a, a < 32 → ¬TB a → m' a = m a) ∧
      (∀ a, 32 ≤ a → (a < H8 L ∨ H8 L + L.R ≤ a) → m' a = m a) ∧ k ≤ 8 * L.n + 12 := by
  have facts : (∀ {r}, r < 32 → r < B) ∧ L.CH + L.n + 1 < B ∧ L.D + 1 < B ∧ 32 ≤ H8 L ∧
      (∀ {a}, L.Dyn a → a ≠ H8 L) ∧ (∀ {a}, a < 32 → a ≠ H8 L) ∧ 0 < L.R := by
    have H32 := hP.H32
    have ht := top_ge (L := L)
    have hCH := CH_ge (L := L)
    have hRn : L.n + L.D + 3 = L.R := rfl
    have hTop : L.top = L.CH + (L.n + 1) + L.n * (L.D + 1) := rfl
    unfold H8
    refine ⟨fun h => ?_, ?_, ?_, ?_, fun hd => ?_, fun h => ?_, ?_⟩
    all_goals first | omega | (unfold Lay.Dyn at hd; omega)
  obtain ⟨rB, sB, dB, a32, dyn, low, Rp⟩ := facts
  have b8 : m 26 = H8 L := hP.base 8 (by omega)
  have o3 : m 3 = 1 := hP.one
  have hn : m 27 = L.n := hP.n
  have hD : m 28 = L.D := hP.D
  unfold cbInit
  refine Runs.seqs_cons (Runs.store (rB (by decide)) (rB (by decide)) ?_)
  rw [b8, h13]
  set m₁ := update m (H8 L) L.CH with hm₁
  have f₁ : ∀ a, a ≠ H8 L → m₁ a = m a := fun a h => update_of_ne h _ _
  have s₁ : m₁ (H8 L) = L.CH := update_self _ _ _
  have y13 : m₁ 13 = L.CH := by rw [f₁ 13 (low (by decide)), h13]
  have y27 : m₁ 27 = L.n := by rw [f₁ 27 (low (by decide)), hn]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [y13, y27]; omega) fun m₂ g₂ f₂ => ?_)
  rw [y13, y27] at g₂
  have y3 : m₂ 3 = 1 := by rw [f₂ 3 (by decide), f₁ 3 (low (by decide)), o3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [g₂, y3]; exact sB) fun m₃ g₃ f₃ => ?_)
  rw [g₂, y3] at g₃
  have y28 : m₃ 28 = L.D := by
    rw [f₃ 28 (by decide), f₂ 28 (by decide), f₁ 28 (low (by decide)), hD]
  have y3' : m₃ 3 = 1 := by rw [f₃ 3 (by decide), y3]
  refine Runs.seqs_cons (Runs.addR (rB (by decide)) (rB (by decide)) (rB (by decide))
    (by rw [y28, y3']; exact dB) fun m₄ g₄ f₄ => ?_)
  rw [y28, y3'] at g₄
  refine Runs.seqs_cons (Runs.constR (rB (by decide)) (rB (by decide)) fun m₅ g₅ f₅ => ?_)
  refine Runs.seqs_cons (Runs.lessR (rB (by decide)) (rB (by decide)) (rB (by decide))
    fun m₆ g₆ f₆ => ?_)
  have E₆ : ∀ a, a ≠ 14 → a ≠ 15 → a ≠ 30 → a ≠ 31 → a ≠ H8 L → m₆ a = m a :=
    fun a a14 a15 a30 a31 ah => by
      rw [f₆ a a31, f₅ a a30, f₄ a a14, f₃ a a15, f₂ a a15, f₁ a ah]
  have y27' : m₅ 27 = L.n := by
    rw [f₅ 27 (by decide), f₄ 27 (by decide), f₃ 27 (by decide), f₂ 27 (by decide), y27]
  rw [y27', g₅] at g₆
  have dyn32 : ∀ {a}, L.Dyn a → 32 ≤ a := fun hd => by
    have H32 := hP.H32
    have hCH := CH_ge (L := L)
    unfold Lay.Dyn at hd
    omega
  have hR0 : CbR L m 1 m₆ := by
    refine ⟨hP.keep (fun a ha hT => E₆ a (fun e => hT (by simp [BT, e]))
        (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e]))
        (fun e => hT (by simp [BT, e])) (low ha))
        (fun a hd => have h := dyn32 hd
          E₆ a (by omega) (by omega) (by omega) (by omega) (dyn hd)), ?_, ?_, ?_, g₆,
      fun j hj => ?_, fun a ha hT => ?_, fun a ha hr => ?_⟩
    · rw [f₆ 30 (by decide), g₅]
    · rw [f₆ 15 (by decide), f₅ 15 (by decide), f₄ 15 (by decide), g₃]; simp; omega
    · rw [f₆ 14 (by decide), f₅ 14 (by decide), g₄]
    · have hj' : j = 0 := by omega
      subst hj'
      rw [Nat.add_zero, f₆ _ (by omega), f₅ _ (by omega), f₄ _ (by omega), f₃ _ (by omega),
        f₂ _ (by omega), s₁]
      simp [Lay.cb]
    · rw [E₆ a (fun e => hT (by simp [TB, e])) (fun e => hT (by simp [TB, e]))
        (fun e => hT (by simp [TB, e])) (fun e => hT (by simp [TB, e])) (low ha)]
    · rw [E₆ a (by omega) (by omega) (by omega) (by omega) (by omega)]
  clear g₂ g₃ g₄ g₅ g₆ f₂ f₃ f₄ f₅ f₆ y3 y3' y13 y27 y27' y28
  let P : Mem → ℕ → Prop := fun m' c => ∃ v, 1 ≤ v ∧ v ≤ L.n + 1 ∧ CbR L m v m' ∧ c ≤ 8 * (v - 1)
  refine Runs.seqs_cons (Runs.loop P (fun m' => L.n + 1 - m' 30) (rB (by decide)) (rB (by decide))
    ?_ ?_ ⟨1, le_refl _, by omega, hR0, by omega⟩)
  · rintro m' c ⟨v, h1, hv, hR, hc⟩ heq
    have hvn : v ≤ L.n := by
      rw [hR.r31, hR.ok.zero] at heq
      by_contra hn'
      rw [if_pos (by omega)] at heq
      omega
    refine Runs.mono (cbBody_spec hR h1 hvn hB) fun m₁ k ⟨R₁, hk⟩ =>
      ⟨⟨v + 1, by omega, by omega, R₁, ?_⟩, ?_⟩
    · simp only [Nat.add_sub_cancel]
      have : 8 * v = 8 * (v - 1) + 8 := by omega
      omega
    · rw [R₁.r13, hR.r13]; omega
  · rintro m' c ⟨v, h1, hv, hR, hc⟩ heq
    have hvn : v = L.n + 1 := by
      rw [hR.r31, hR.ok.zero] at heq
      by_contra hn'
      exact heq (by rw [if_neg (by omega)])
    subst hvn
    refine Runs.seqs_nilR (rB (by decide)) fun m₁ g₁' f₁' => ?_
    have hi₁ : ∀ {a}, 32 ≤ a → m₁ a = m' a := fun h => f₁' _ (by omega)
    have hE : ∀ a, 32 ≤ a → (a < H8 L ∨ H8 L + L.R ≤ a) → m₁ a = m a := fun a h1 h2 => by
      rw [hi₁ h1, hR.hi a h1 h2]
    refine ⟨hR.ok.keep (fun a _ hT => f₁' a fun e => hT (by simp [BT, e]))
        (fun a hd => hi₁ (dyn32 hd)), fun v hv => ?_, fun v hv => ?_,
      fun a ha hT => ?_, hE, ?_⟩
    · rw [hi₁ (by omega), hR.set v (by omega)]
    · have hRn : L.n + L.D + 3 = L.R := rfl
      have H32 := hP.H32
      have hHE : L.HE = L.H + 10 * L.R := rfl
      have hCH : L.CH = L.HE + 6 * L.E := rfl
      have hge : 32 ≤ H7 L + v := by unfold H7; omega
      have hb : H7 L + v < H8 L := by unfold H7 H8; omega
      rw [hE _ hge (.inl hb)]
      exact Lst.frame' (fun a h1 h2 => hE a (by omega) (.inr (by unfold H8; omega))) _ _ (hl v hv)
    · rw [f₁' a fun e => hT (by simp [TB, e]), hR.lo a ha hT]
    · simp only [Nat.add_sub_cancel] at hc
      have : 8 * L.n + 12 ≥ c + 6 := by omega
      omega

theorem fld_blank (k i : ℕ) : fld blank k i = 0 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> rfl

theorem Pre.rep (hP : Pre L m) (h29 : m 29 = 0) : Rep L blank m :=
  ⟨hP.H32, hP.base, hP.n, hP.D, h29, hP.one, hP.zero, hP.three,
    fun k hk i hi => by rw [hP.dyn _ (dyn_arr hk hi), fld_blank],
    fun v hv j hj => hP.dyn _ (dyn_ch hv hj)⟩

/-- The registers `source` uses. -/
def TI (a : ℕ) : Prop := T29 a ∨ a = 11 ∨ a = 12

/-- Put the source in the heap. -/
theorem sourceIn_spec {src : ℕ} (hR : Rep L blank m) (hF : Fixed L x m)
    (h11 : m 11 = src) (hs : src < L.n) (hB : L.top < B) :
    Runs B (seqs [add 11 11 3, wr 1 11 3, attach 11 8, updMin 11]) m fun m' k =>
      Rep L (St.updMin (src + 1) (St.attach (src + 1) 0 (St.setStat (src + 1) 1 blank))) m' ∧
        Fixed L x m' ∧ Frm L TI m m' ∧ k ≤ 30 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have t2 : TI 2 := .inl (.inl (by simp [T267]))
  have t11 : TI 11 := by simp [TI]
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h11, hR.one]; omega) fun m₁ g₁ f₁ => ?_)
  rw [h11, hR.one] at g₁
  have R₁ := hR.regs1 (r := 11) (by simp [Tmp]) (by omega) f₁
  have b1 : m₁ 11 ≤ L.bnd 1 := by rw [g₁]; simp [Lay.bnd]; omega
  refine Runs.seqs_cons (Runs.mono (wr_spec R₁ (k := 1) (i := 11) (s := 3) (by omega) b1
    (by omega) (by omega) (by omega) hB) fun m₂ c₂ ⟨R₂, f₂, hc₂⟩ => ?_)
  have F₂ : Frm L TI m m₂ := (Frm.reg1 t11 (by omega) f₁).trans
    (Frm.dyn (dyn_arr (k := 1) (by omega) b1) t2 f₂ hH)
  rw [g₁, R₁.one] at R₂
  have R₂' : Rep L (St.setStat (src + 1) 1 blank) m₂ := R₂
  have X₂ : Fixed L x m₂ := hF.frame hH F₂.2
  have e₂ : m₂ 11 = src + 1 := by rw [f₂ 11 (by omega) (by omega), g₁]
  have z₂ : m₂ 8 = 0 := R₂'.zero
  refine Runs.seqs_cons (Runs.mono (attach_spec R₂' X₂ (rv := 11) (rp := 8) (by omega) (by omega)
    (by rw [z₂]; change 0 < L.cap 0; simp [Lay.cap]) (by omega) (by omega) (by simp [T267])
    (by simp [T267]) hB) fun m₃ c₃ ⟨R₃, X₃, F₃, hc₃⟩ => ?_)
  rw [e₂, z₂] at R₃
  have e₃ : m₃ 11 = src + 1 := by rw [F₃.1 11 (by omega) (by simp [T267]), e₂]
  refine Runs.seqs_cons (Runs.mono (updMin_spec R₃ X₃ (rv := 11) (by omega)
    (by change 0 ≤ L.n; omega) (by omega) (by simp [T29, T267]) hB)
    fun m₄ c₄ ⟨R₄, X₄, F₄, hc₄⟩ => ?_)
  rw [e₃] at R₄
  refine Runs.seqs_nilR (by omega) fun m₅ g₅ f₅ => ?_
  have F₅ : Frm L TI m₄ m₅ := Frm.reg1 t2 (by omega) f₅
  exact ⟨R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅, X₄.frame hH F₅.2,
    F₂.trans ((F₃.mono fun _ h => .inl (.inl h)).trans ((F₄.mono fun _ h => .inl h).trans F₅)),
    by omega⟩

theorem source_run {C : Ctx} {Z src : ℕ} (hP : Pre L m) (hF : Fixed L x m) (h17 : m 17 = Z)
    (hZ : m Z = src) (hLn : L.n = C.n) (hB : L.top < B) :
    Runs B source m fun m' k => Rep L (start C src) m' ∧ Fixed L x m' ∧ Frm L TI m m' ∧
      k ≤ 40 := by
  have hH := hP.H32
  have ht := top_ge (L := L)
  have t2 : TI 2 := .inl (.inl (by simp [T267]))
  have t11 : TI 11 := by simp [TI]
  have t12 : TI 12 := by simp [TI]
  have t29 : TI 29 := .inl (by simp [T29])
  have hRn : L.n + L.D + 3 = L.R := rfl
  unfold source
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
  rw [h17, hZ] at g₁
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₂ g₂ f₂ => ?_)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
  have F₃ : Frm L TI m m₃ := (Frm.reg1 t11 (by omega) f₁).trans ((Frm.reg1 t29 (by omega) f₂).trans
    (Frm.reg1 t12 (by omega) f₃))
  have E₃ : ∀ a, a ≠ 11 → a ≠ 12 → a ≠ 29 → m₃ a = m a := fun a a11 a12 a29 => by
    rw [f₃ a a12, f₂ a a29, f₁ a a11]
  have P₃ : Pre L m₃ := hP.keep (fun a _ hT => E₃ a (fun e => hT (by simp [BT, e]))
      (fun e => hT (by simp [BT, e])) (fun e => hT (by simp [BT, e])))
    (fun a hd => E₃ a (by
      have hCH := CH_ge (L := L)
      unfold Lay.Dyn at hd
      omega) (by
      have hCH := CH_ge (L := L)
      unfold Lay.Dyn at hd
      omega) (by
      have hCH := CH_ge (L := L)
      unfold Lay.Dyn at hd
      omega))
  have R₃ : Rep L blank m₃ := P₃.rep (by rw [f₃ 29 (by omega), g₂])
  have X₃ : Fixed L x m₃ := hF.frame hH F₃.2
  have e11 : m₃ 11 = src := by rw [f₃ 11 (by omega), f₂ 11 (by omega), g₁]
  have e12 : m₃ 12 = if src < L.n then 1 else 0 := by
    rw [g₃, f₂ 11 (by omega), g₁, f₂ 27 (by omega), f₁ 27 (by omega)]
    have : m 27 = L.n := hP.n
    rw [this]
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun h1 => ?_) (fun h1 => ?_))
  · rw [e12, R₃.one] at h1
    have hs : src < L.n := by by_contra hc; simp [hc] at h1
    have hs' : src < C.n := by omega
    have e : start C src =
        St.updMin (src + 1) (St.attach (src + 1) 0 (St.setStat (src + 1) 1 blank)) := by
      simp only [start, if_pos hs']
    rw [e]
    refine Runs.mono (sourceIn_spec R₃ X₃ e11 hs hB) fun m₄ c₄ ⟨R₄, X₄, F₄, hc₄⟩ => ?_
    refine Runs.seqs_nilR (by omega) fun m₅ g₅ f₅ => ?_
    have F₅ : Frm L TI m₄ m₅ := Frm.reg1 t2 (by omega) f₅
    exact ⟨R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅, X₄.frame hH F₅.2,
      F₃.trans (F₄.trans F₅), by omega⟩
  · rw [e12, R₃.one] at h1
    have hs : ¬src < L.n := by intro hc; simp [hc] at h1
    have hs' : ¬src < C.n := by omega
    have e : start C src = blank := by simp only [start, if_neg hs']
    rw [e]
    refine Runs.constR (by omega) (by omega) fun m₄ g₄ f₄ => ?_
    refine Runs.seqs_nilR (by omega) fun m₅ g₅ f₅ => ?_
    have F₅ : Frm L TI m₃ m₅ := (Frm.reg1 t2 (by omega) f₄).trans (Frm.reg1 t2 (by omega) f₅)
    exact ⟨(R₃.regs1 (r := 2) (by simp [Tmp]) (by omega) f₄).regs1 (r := 2) (by simp [Tmp])
      (by omega) f₅, X₃.frame hH F₅.2, F₃.trans F₅, by omega⟩

end Formalgo.Algorithms.ShortestPaths
