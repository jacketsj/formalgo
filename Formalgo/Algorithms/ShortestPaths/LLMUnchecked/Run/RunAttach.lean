import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.Access

/-!
# Running `attach` and `detach`

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : Input}

/-- Only registers in `T` and heap addresses changed. -/
def Frm (L : Lay) (T : ℕ → Prop) (m m' : Mem) : Prop :=
  (∀ a, a < 32 → ¬T a → m' a = m a) ∧ (∀ a, 32 ≤ a → ¬L.Dyn a → m' a = m a)

theorem Frm.refl {T : ℕ → Prop} : Frm L T m m := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frm.trans {T : ℕ → Prop} {m₁ m₂ : Mem} (h : Frm L T m m₁) (h' : Frm L T m₁ m₂) :
    Frm L T m m₂ :=
  ⟨fun a ha hT => (h'.1 a ha hT).trans (h.1 a ha hT),
    fun a ha hd => (h'.2 a ha hd).trans (h.2 a ha hd)⟩

theorem Frm.reg {T : ℕ → Prop} {m₁ : Mem} {r : ℕ} (hr : T r) (hr32 : r < 32)
    (h : ∀ a, a ≠ 2 → a ≠ r → m₁ a = m a) (h2 : T 2) : Frm L T m m₁ :=
  ⟨fun a _ hT => h a (fun e => hT (e ▸ h2)) (fun e => hT (e ▸ hr)),
    fun a ha _ => h a (by omega) (by omega)⟩

theorem Frm.reg1 {T : ℕ → Prop} {m₁ : Mem} {r : ℕ} (hr : T r) (hr32 : r < 32)
    (h : ∀ a, a ≠ r → m₁ a = m a) : Frm L T m m₁ :=
  ⟨fun a _ hT => h a (fun e => hT (e ▸ hr)), fun a ha _ => h a (by omega)⟩

theorem Frm.dyn {T : ℕ → Prop} {m₁ : Mem} {p : ℕ} (hp : L.Dyn p) (h2 : T 2)
    (h : ∀ a, a ≠ 2 → a ≠ p → m₁ a = m a) (H32 : 32 ≤ L.H) : Frm L T m m₁ := by
  have hp32 : 32 ≤ p := by unfold Lay.Dyn at hp; have := CH_ge (L := L); omega
  exact ⟨fun a ha hT => h a (fun e => hT (e ▸ h2)) (by omega),
    fun a ha hd => h a (by omega) (fun e => hd (e ▸ hp))⟩

theorem dyn_arr {k i : ℕ} (hk : k < 7) (hi : i ≤ L.bnd k) : L.Dyn (L.H + k * L.R + i) :=
  .inl ⟨by omega, arr_lt hk hi⟩

theorem dyn_ch {v j : ℕ} (hv : v ≤ L.n) (hj : j < L.cap v) : L.Dyn (L.cb v + j) :=
  .inr (cb_slot hv hj)

theorem Rep.reg {m₁ : Mem} (h : Rep L σ m) {T : ℕ → Prop} (hT : ∀ a, T a → Tmp a)
    (hf : Frm L T m m₁) (hhi : ∀ a, 32 ≤ a → m₁ a = m a) : Rep L σ m₁ :=
  h.congr (fun a ha h32 => hf.1 a h32 fun hTa => ha (hT a hTa)) hhi

theorem cap_le {v : ℕ} : L.cap v ≤ L.n + L.D + 1 := by unfold Lay.cap; split_ifs <;> omega

/-- The registers `attach` uses. -/
def T267 (a : ℕ) : Prop := a = 2 ∨ a = 6 ∨ a = 7

theorem attach_spec (hR : Rep L σ m) (hF : Fixed L x m) {rv rp : ℕ} (hv : m rv ≤ L.n)
    (hp : m rp ≤ L.n) (hcap : σ.deg (m rp) < L.cap (m rp)) (hrv : rv < 32) (hrp : rp < 32)
    (hrvT : ¬T267 rv) (hrpT : ¬T267 rp) (hB : L.top < B) :
    Runs B (attach rv rp) m fun m' c => Rep L (St.attach (m rv) (m rp) σ) m' ∧ Fixed L x m' ∧
      Frm L T267 m m' ∧ c ≤ 14 := by
  simp only [T267, not_or] at hrvT hrpT
  obtain ⟨v2, v6, v7⟩ := hrvT
  obtain ⟨p2, p6, p7⟩ := hrpT
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hcl := cap_le (L := L) (v := m rp)
  have hRn : L.n + L.D + 3 = L.R := rfl
  set V := m rv with hV
  set P := m rp with hP
  set d := σ.deg P with hd
  unfold attach
  -- `M[6] := deg P`
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 3) (d := 6) (i := rp) (by omega)
    (by simp [Lay.bnd]; omega) (by omega) (by omega) hrp hB) fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  have F₁ : Frm L T267 m m₁ := Frm.reg (by simp [T267]) (by omega) f₁ (by simp [T267])
  have R₁ : Rep L σ m₁ := hR.reg (fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h]) F₁
    (fun a ha => f₁ a (by omega) (by omega))
  have h₁6 : m₁ 6 = d := h₁
  -- `M[7] := deg P + 1`
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h₁6, f₁ 3 (by omega) (by omega), hR.one]; omega) fun m₂ h₂ f₂ => ?_)
  have F₂ : Frm L T267 m m₂ := F₁.trans (Frm.reg1 (by simp [T267]) (by omega) f₂)
  have R₂ : Rep L σ m₂ := R₁.reg (T := T267) (fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h])
    (Frm.reg1 (by simp [T267]) (by omega) f₂) (fun a ha => f₂ a (by omega))
  have r₂ : ∀ r, r < 32 → ¬T267 r → m₂ r = m r := F₂.1
  have h₂7 : m₂ 7 = d + 1 := by rw [h₂, h₁6, f₁ 3 (by omega) (by omega), hR.one]
  have h₂6 : m₂ 6 = d := by rw [f₂ 6 (by omega), h₁6]
  -- `deg P := deg P + 1`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₂ (k := 3) (i := rp) (s := 7) (by omega)
    (by rw [r₂ rp hrp (by simp [T267]; omega)]; simp [Lay.bnd]; omega) (by omega) hrp (by omega) hB)
    fun m₃ c₃ ⟨R₃, f₃, hc₃⟩ => ?_)
  rw [r₂ rp hrp (by simp [T267]; omega), h₂7] at R₃
  have F₃ : Frm L T267 m m₃ := F₂.trans (Frm.dyn (dyn_arr (k := 3) (by omega)
    (by rw [r₂ rp hrp (by simp [T267]; omega)]; simp [Lay.bnd]; omega)) (by simp [T267]) f₃ hH)
  have r₃ : ∀ r, r < 32 → ¬T267 r → m₃ r = m r := F₃.1
  have h₃6 : m₃ 6 = d := by rw [f₃ 6 (by omega) (by omega), h₂6]
  -- `pos V := deg P`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₃ (k := 5) (i := rv) (s := 6) (by omega)
    (by rw [r₃ rv hrv (by simp [T267]; omega)]; simp [Lay.bnd]; omega) (by omega) hrv (by omega) hB)
    fun m₄ c₄ ⟨R₄, f₄, hc₄⟩ => ?_)
  rw [r₃ rv hrv (by simp [T267]; omega), h₃6] at R₄
  have F₄ : Frm L T267 m m₄ := F₃.trans (Frm.dyn (dyn_arr (k := 5) (by omega)
    (by rw [r₃ rv hrv (by simp [T267]; omega)]; simp [Lay.bnd]; omega)) (by simp [T267]) f₄ hH)
  have r₄ : ∀ r, r < 32 → ¬T267 r → m₄ r = m r := F₄.1
  have h₄6 : m₄ 6 = d := by rw [f₄ 6 (by omega) (by omega), h₃6]
  have hF₄ : Fixed L x m₄ := hF.frame hH F₄.2
  -- `ch P d := V`
  refine Runs.seqs_cons (Runs.mono (chWr_spec R₄ hF₄ (p := rp) (j := 6) (s := rv)
    (by rw [r₄ rp hrp (by simp [T267]; omega)]; omega)
    (by rw [r₄ rp hrp (by simp [T267]; omega), h₄6]; exact hcap) hrp (by omega) (by omega)
    (by omega) (by omega) hrv hB) fun m₅ c₅ ⟨R₅, f₅, hc₅⟩ => ?_)
  rw [r₄ rp hrp (by simp [T267]; omega), h₄6, r₄ rv hrv (by simp [T267]; omega)] at R₅
  have F₅ : Frm L T267 m m₅ := F₄.trans (Frm.dyn (by
    rw [r₄ rp hrp (by simp [T267]; omega), h₄6]; exact dyn_ch hp hcap) (by simp [T267]) f₅ hH)
  have r₅ : ∀ r, r < 32 → ¬T267 r → m₅ r = m r := F₅.1
  -- `par V := P`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₅ (k := 2) (i := rv) (s := rp) (by omega)
    (by rw [r₅ rv hrv (by simp [T267]; omega)]; simp [Lay.bnd]; omega) (by omega) hrv hrp hB)
    fun m₆ c₆ ⟨R₆, f₆, hc₆⟩ => ?_)
  rw [r₅ rv hrv (by simp [T267]; omega), r₅ rp hrp (by simp [T267]; omega)] at R₆
  have F₆ : Frm L T267 m m₆ := F₅.trans (Frm.dyn (dyn_arr (k := 2) (by omega)
    (by rw [r₅ rv hrv (by simp [T267]; omega)]; simp [Lay.bnd]; omega)) (by simp [T267]) f₆ hH)
  refine Runs.seqs_nilR (by omega) fun m₇ h₇ f₇ => ?_
  have F₇ : Frm L T267 m m₇ := F₆.trans (Frm.reg1 (by simp [T267]) (by omega) f₇)
  refine ⟨R₆.reg (T := T267) (fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h])
    (Frm.reg1 (by simp [T267]) (by omega) f₇) (fun a ha => f₇ a (by omega)),
    hF.frame hH F₇.2, F₇, by omega⟩

theorem detach_spec (hR : Rep L σ m) (hF : Fixed L x m) {rv rp : ℕ} (hv : m rv ≤ L.n)
    (hp : m rp ≤ L.n) (hd1 : 1 ≤ σ.deg (m rp)) (hcap : σ.deg (m rp) ≤ L.cap (m rp))
    (hlast : σ.ch (m rp) (σ.deg (m rp) - 1) ≤ L.n) (hpos : σ.pos (m rv) < L.cap (m rp))
    (hrv : rv < 32) (hrp : rp < 32) (hrvT : ¬T267 rv) (hrpT : ¬T267 rp) (hB : L.top < B) :
    Runs B (detach rv rp) m fun m' c => Rep L (St.detach (m rv) (m rp) σ) m' ∧ Fixed L x m' ∧
      Frm L T267 m m' ∧ c ≤ 18 := by
  simp only [T267, not_or] at hrvT hrpT
  obtain ⟨v2, v6, v7⟩ := hrvT
  obtain ⟨p2, p6, p7⟩ := hrpT
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hcl := cap_le (L := L) (v := m rp)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have tT : ∀ a, T267 a → Tmp a := fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h]
  unfold detach
  -- `M[6] := deg P - 1`
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 3) (d := 6) (i := rp) (by omega)
    (by simp [Lay.bnd]; omega) (by omega) (by omega) hrp hB) fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  have F₁ : Frm L T267 m m₁ := Frm.reg (by simp [T267]) (by omega) f₁ (by simp [T267])
  have R₁ : Rep L σ m₁ := hR.reg tT F₁ (fun a ha => f₁ a (by omega) (by omega))
  have h₁6 : m₁ 6 = σ.deg (m rp) := h₁
  refine Runs.seqs_cons (Runs.subR (by omega) (by omega) (by omega)
    (by rw [h₁6, f₁ 3 (by omega) (by omega), hR.one]; omega) fun m₂ h₂ f₂ => ?_)
  have F₂ : Frm L T267 m m₂ := F₁.trans (Frm.reg1 (by simp [T267]) (by omega) f₂)
  have R₂ : Rep L σ m₂ := R₁.reg tT (Frm.reg1 (by simp [T267]) (by omega) f₂)
    (fun a ha => f₂ a (by omega))
  have r₂ : ∀ r, r < 32 → ¬T267 r → m₂ r = m r := F₂.1
  have h₂6 : m₂ 6 = σ.deg (m rp) - 1 := by rw [h₂, h₁6, f₁ 3 (by omega) (by omega), hR.one]
  -- `deg P := deg P - 1`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₂ (k := 3) (i := rp) (s := 6) (by omega)
    (by rw [r₂ rp hrp (by simp [T267]; omega)]; simp [Lay.bnd]; omega) (by omega) hrp (by omega) hB)
    fun m₃ c₃ ⟨R₃, f₃, hc₃⟩ => ?_)
  rw [r₂ rp hrp (by simp [T267]; omega), h₂6] at R₃
  have F₃ : Frm L T267 m m₃ := F₂.trans (Frm.dyn (dyn_arr (k := 3) (by omega)
    (by rw [r₂ rp hrp (by simp [T267]; omega)]; simp [Lay.bnd]; omega)) (by simp [T267]) f₃ hH)
  have r₃ : ∀ r, r < 32 → ¬T267 r → m₃ r = m r := F₃.1
  have h₃6 : m₃ 6 = σ.deg (m rp) - 1 := by rw [f₃ 6 (by omega) (by omega), h₂6]
  have hF₃ : Fixed L x m₃ := hF.frame hH F₃.2
  -- `M[7] := last`
  refine Runs.seqs_cons (Runs.mono (chRd_spec R₃ hF₃ (d := 7) (p := rp) (j := 6)
    (by rw [r₃ rp hrp (by simp [T267]; omega)]; omega)
    (by rw [r₃ rp hrp (by simp [T267]; omega), h₃6]; omega) hrp (by omega) (by omega) (by omega)
    (by omega) hB) fun m₄ c₄ ⟨h₄, f₄, hc₄⟩ => ?_)
  rw [r₃ rp hrp (by simp [T267]; omega), h₃6] at h₄
  have F₄ : Frm L T267 m m₄ := F₃.trans (Frm.reg (by simp [T267]) (by omega) f₄ (by simp [T267]))
  have R₄ : Rep L (setFld 3 (m rp) (σ.deg (m rp) - 1) σ) m₄ := R₃.reg tT
    (Frm.reg (by simp [T267]) (by omega) f₄ (by simp [T267])) (fun a ha => f₄ a (by omega) (by omega))
  have r₄ : ∀ r, r < 32 → ¬T267 r → m₄ r = m r := F₄.1
  have h₄7 : m₄ 7 = σ.ch (m rp) (σ.deg (m rp) - 1) := h₄
  -- `M[6] := pos V`
  refine Runs.seqs_cons (Runs.mono (rd_spec R₄ (k := 5) (d := 6) (i := rv) (by omega)
    (by rw [r₄ rv hrv (by simp [T267]; omega)]; simp [Lay.bnd]; omega) (by omega) (by omega) hrv hB)
    fun m₅ c₅ ⟨h₅, f₅, hc₅⟩ => ?_)
  rw [r₄ rv hrv (by simp [T267]; omega)] at h₅
  have F₅ : Frm L T267 m m₅ := F₄.trans (Frm.reg (by simp [T267]) (by omega) f₅ (by simp [T267]))
  have R₅ : Rep L (setFld 3 (m rp) (σ.deg (m rp) - 1) σ) m₅ := R₄.reg tT
    (Frm.reg (by simp [T267]) (by omega) f₅ (by simp [T267])) (fun a ha => f₅ a (by omega) (by omega))
  have r₅ : ∀ r, r < 32 → ¬T267 r → m₅ r = m r := F₅.1
  have h₅6 : m₅ 6 = σ.pos (m rv) := h₅
  have h₅7 : m₅ 7 = σ.ch (m rp) (σ.deg (m rp) - 1) := by rw [f₅ 7 (by omega) (by omega), h₄7]
  -- `pos last := pos V`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₅ (k := 5) (i := 7) (s := 6) (by omega)
    (by rw [h₅7]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₆ c₆ ⟨R₆, f₆, hc₆⟩ => ?_)
  rw [h₅7, h₅6] at R₆
  have F₆ : Frm L T267 m m₆ := F₅.trans (Frm.dyn (dyn_arr (k := 5) (by omega)
    (by rw [h₅7]; simp [Lay.bnd]; omega)) (by simp [T267]) f₆ hH)
  have r₆ : ∀ r, r < 32 → ¬T267 r → m₆ r = m r := F₆.1
  have h₆6 : m₆ 6 = σ.pos (m rv) := by rw [f₆ 6 (by omega) (by omega), h₅6]
  have h₆7 : m₆ 7 = σ.ch (m rp) (σ.deg (m rp) - 1) := by rw [f₆ 7 (by omega) (by omega), h₅7]
  have hF₆ : Fixed L x m₆ := hF.frame hH F₆.2
  -- `ch P (pos V) := last`
  refine Runs.seqs_cons (Runs.mono (chWr_spec R₆ hF₆ (p := rp) (j := 6) (s := 7)
    (by rw [r₆ rp hrp (by simp [T267]; omega)]; omega)
    (by rw [r₆ rp hrp (by simp [T267]; omega), h₆6]; exact hpos) hrp (by omega) (by omega)
    (by omega) (by omega) (by omega) hB) fun m₇ c₇ ⟨R₇, f₇, hc₇⟩ => ?_)
  rw [r₆ rp hrp (by simp [T267]; omega), h₆6, h₆7] at R₇
  have F₇ : Frm L T267 m m₇ := F₆.trans (Frm.dyn (by
    rw [r₆ rp hrp (by simp [T267]; omega), h₆6]; exact dyn_ch hp hpos) (by simp [T267]) f₇ hH)
  refine Runs.seqs_nilR (by omega) fun m₈ h₈ f₈ => ?_
  have F₈ : Frm L T267 m m₈ := F₇.trans (Frm.reg1 (by simp [T267]) (by omega) f₈)
  refine ⟨R₇.reg (T := T267) tT (Frm.reg1 (by simp [T267]) (by omega) f₈)
    (fun a ha => f₈ a (by omega)), hF.frame hH F₈.2, F₈, by omega⟩

theorem fld_hmin (σ : St) (h k : ℕ) : fld { σ with hmin := h } k = fld σ k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- Changing the minimum root. -/
theorem Rep.setHmin {m' : Mem} (hR : Rep L σ m) (h : ℕ)
    (hm : ∀ a, a ≠ 29 → ¬Tmp a → a < 32 → m' a = m a) (hhi : ∀ a, 32 ≤ a → m' a = m a)
    (h29 : m' 29 = h) : Rep L { σ with hmin := h } m' := by
  have hr : ∀ a, a ≠ 29 → ¬Tmp a → m' a = m a := fun a h1 h2 => by
    by_cases h32 : a < 32
    · exact hm a h1 h2 h32
    · exact hhi a (by omega)
  refine ⟨hR.H32, fun k hk => ?_, ?_, ?_, h29, ?_, ?_, ?_, fun k hk i hi => ?_, fun v hv j hj => ?_⟩
  · rw [hr _ (by have := breg_lt k hk; unfold breg; split_ifs <;> omega) (breg_not_tmp hk)]
    exact hR.base k hk
  · rw [hr 27 (by omega) (by simp [Tmp])]; exact hR.n
  · rw [hr 28 (by omega) (by simp [Tmp])]; exact hR.D
  · rw [hr 3 (by omega) (by simp [Tmp])]; exact hR.one
  · rw [hr 8 (by omega) (by simp [Tmp])]; exact hR.zero
  · rw [hr 16 (by omega) (by simp [Tmp])]; exact hR.three
  · rw [hhi _ (by have := hR.H32; omega), fld_hmin]; exact hR.arr k hk i hi
  · rw [hhi _ (by have := cb_slot hv hj; have := hR.H32; have := CH_ge (L := L); omega)]
    exact hR.ch v hv j hj

/-- The registers `updMin` uses. -/
def T29 (a : ℕ) : Prop := T267 a ∨ a = 29

theorem Frm.mono {T T' : ℕ → Prop} {m' : Mem} (h : Frm L T m m') (hT : ∀ a, T a → T' a) :
    Frm L T' m m' := ⟨fun a ha hT' => h.1 a ha fun hTa => hT' (hT a hTa), h.2⟩

theorem updMin_spec (hR : Rep L σ m) (hF : Fixed L x m) {rv : ℕ} (hv : m rv ≤ L.n)
    (hm : σ.hmin ≤ L.n) (hrv : rv < 32) (hrvT : ¬T29 rv) (hB : L.top < B) :
    Runs B (updMin rv) m fun m' c => Rep L (St.updMin (m rv) σ) m' ∧ Fixed L x m' ∧
      Frm L T29 m m' ∧ c ≤ 10 := by
  simp only [T29, T267, not_or] at hrvT
  obtain ⟨⟨v2, v6, v7⟩, v29⟩ := hrvT
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have tT : ∀ a, T267 a → Tmp a := fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h]
  have hhi29 : m 29 = σ.hmin := hR.hmin
  unfold updMin
  refine Runs.ite (by omega) (by omega) (fun h0 => ?_) (fun h0 => ?_)
  · -- No minimum yet.
    rw [hR.hmin, hR.zero] at h0
    refine Runs.copyR (by omega) (by omega) fun m₁ h₁ f₁ => ?_
    have F₁ : Frm L T29 m m₁ := Frm.reg1 (by simp [T29]) (by omega) f₁
    have e : St.updMin (m rv) σ = { σ with hmin := m rv } := by simp [St.updMin, h0]
    rw [e]
    exact ⟨hR.setHmin _ (fun a ha _ _ => f₁ a ha) (fun a ha => f₁ a (by omega)) h₁,
      hF.frame hH F₁.2, F₁, by omega⟩
  · rw [hR.hmin, hR.zero] at h0
    refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 0) (d := 6) (i := rv) (by omega)
      (by simp [Lay.bnd]; omega) (by omega) (by omega) hrv hB) fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
    have R₁ : Rep L σ m₁ := hR.reg (T := T267) tT
      (Frm.reg (by simp [T267]) (by omega) f₁ (by simp [T267])) (fun a ha => f₁ a (by omega) (by omega))
    refine Runs.seqs_cons (Runs.mono (rd_spec R₁ (k := 0) (d := 7) (i := 29) (by omega)
      (by rw [f₁ 29 (by omega) (by omega), hhi29]; simp [Lay.bnd]; omega) (by omega) (by omega)
      (by omega) hB) fun m₂ c₂ ⟨h₂, f₂, hc₂⟩ => ?_)
    have R₂ : Rep L σ m₂ := R₁.reg (T := T267) tT
      (Frm.reg (by simp [T267]) (by omega) f₂ (by simp [T267])) (fun a ha => f₂ a (by omega) (by omega))
    rw [f₁ 29 (by omega) (by omega), hhi29] at h₂
    refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₃ h₃ f₃ => ?_)
    have h₃6 : m₃ 6 = if σ.key (m rv) < σ.key σ.hmin then 1 else 0 := by
      rw [h₃, f₂ 6 (by omega) (by omega), h₁, h₂]; rfl
    have F₃ : Frm L T29 m m₃ := (Frm.reg (by simp [T29, T267]) (by omega) f₁ (by simp [T29, T267])).trans
      ((Frm.reg (by simp [T29, T267]) (by omega) f₂ (by simp [T29, T267])).trans
        (Frm.reg1 (by simp [T29, T267]) (by omega) f₃))
    have R₃ : Rep L σ m₃ := R₂.reg (T := T267) tT (Frm.reg1 (by simp [T267]) (by omega) f₃)
      (fun a ha => f₃ a (by omega))
    have hv₃ : m₃ rv = m rv := F₃.1 rv hrv (by simp [T29, T267]; omega)
    refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun hlt => ?_) (fun hlt => ?_))
    · rw [h₃6, R₃.one] at hlt
      have hlt' : σ.key (m rv) < σ.key σ.hmin := by by_contra hc; simp [hc] at hlt
      refine Runs.copyR (by omega) (by omega) fun m₄ h₄ f₄ => Runs.seqs_nilR (by omega)
        fun m₅ h₅ f₅ => ?_
      have e : St.updMin (m rv) σ = { σ with hmin := m rv } := by simp [St.updMin, h0, hlt']
      rw [e]
      have F₅ : Frm L T29 m m₅ := F₃.trans ((Frm.reg1 (by simp [T29]) (by omega) f₄).trans
        (Frm.reg1 (by simp [T29, T267]) (by omega) f₅))
      refine ⟨?_, hF.frame hH F₅.2, F₅, by omega⟩
      have nt : ∀ a, ¬Tmp a → a ≠ 2 ∧ a ≠ 6 ∧ a ≠ 7 := fun a ha =>
        ⟨fun h => ha (by simp [Tmp, h]), fun h => ha (by simp [Tmp, h]), fun h => ha (by simp [Tmp, h])⟩
      refine hR.setHmin _ (fun a ha hT _ => ?_) (fun a ha => ?_) ?_
      · obtain ⟨a2, a6, a7⟩ := nt a hT
        rw [f₅ a a2, f₄ a ha, f₃ a a6, f₂ a a2 a7, f₁ a a2 a6]
      · rw [f₅ a (by omega), f₄ a (by omega), f₃ a (by omega), f₂ a (by omega) (by omega),
          f₁ a (by omega) (by omega)]
      · rw [f₅ 29 (by omega), h₄, hv₃]
    · rw [h₃6, R₃.one] at hlt
      have hlt' : ¬σ.key (m rv) < σ.key σ.hmin := by intro hc; simp [hc] at hlt
      refine Runs.constR (by omega) (by omega) fun m₄ h₄ f₄ => Runs.seqs_nilR (by omega)
        fun m₅ h₅ f₅ => ?_
      have e : St.updMin (m rv) σ = σ := by simp [St.updMin, h0, hlt']
      rw [e]
      have F₅ : Frm L T29 m m₅ := F₃.trans ((Frm.reg1 (by simp [T29, T267]) (by omega) f₄).trans
        (Frm.reg1 (by simp [T29, T267]) (by omega) f₅))
      refine ⟨R₃.reg (T := T267) tT ((Frm.reg1 (by simp [T267]) (by omega) f₄).trans
        (Frm.reg1 (by simp [T267]) (by omega) f₅)) (fun a ha => by
          rw [f₅ a (by omega), f₄ a (by omega)]), hF.frame hH F₅.2, F₅, by omega⟩

end Formalgo.Algorithms.ShortestPaths
