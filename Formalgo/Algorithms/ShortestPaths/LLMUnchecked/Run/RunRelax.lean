import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunDecKey

/-!
# Running the relaxation of a half-edge

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

/-- The registers `relaxBody` uses. -/
def TR (a : ℕ) : Prop := TD a ∨ a = 13 ∨ a = 14 ∨ a = 31

theorem T29_TD {a : ℕ} (h : T29 a) : TD a := by
  simp only [T29, T267] at h
  simp only [TD, TC, TU, T267]; omega

theorem TD_TR {a : ℕ} (h : TD a) : TR a := .inl h

theorem updMin_time {v : ℕ} {s : St} : (St.updMin v s).time = s.time := by
  unfold St.updMin; split_ifs <;> rfl

/-- Put a new vertex in the heap. -/
theorem relaxNew_spec {s : St} (hR : Rep L s m) (hF : Fixed L x m) {v nk : ℕ} (h13 : m 13 = v)
    (h14 : m 14 = nk) (hv : v ≤ L.n) (hd0 : s.deg 0 ≤ L.n) (hm : s.hmin ≤ L.n) (hB : L.top < B) :
    Runs B (seqs [wr 0 13 14, wr 1 13 3, attach 13 8, updMin 13]) m fun m' c =>
      Rep L (St.updMin v (St.attach v 0 (St.setStat v 1 (St.setKey v nk s)))) m' ∧ Fixed L x m' ∧
        Frm L T29 m m' ∧ c ≤ 30 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have t2 : T29 2 := .inl (by simp [T267])
  have b0 : m 13 ≤ L.bnd 0 := by rw [h13]; simp [Lay.bnd]; omega
  refine Runs.seqs_cons (Runs.mono (wr_spec hR (k := 0) (i := 13) (s := 14) (by omega) b0
    (by omega) (by omega) (by omega) hB) fun m₁ c₁ ⟨R₁, f₁, hc₁⟩ => ?_)
  have F₁ : Frm L T29 m m₁ := Frm.dyn (dyn_arr (k := 0) (by omega) b0) t2 f₁ hH
  rw [h13, h14] at R₁
  have X₁ : Fixed L x m₁ := hF.frame hH F₁.2
  have e₁ : m₁ 13 = v := by rw [f₁ 13 (by omega) (by omega), h13]
  have b1 : m₁ 13 ≤ L.bnd 1 := by rw [e₁]; simp [Lay.bnd]; omega
  refine Runs.seqs_cons (Runs.mono (wr_spec R₁ (k := 1) (i := 13) (s := 3) (by omega) b1
    (by omega) (by omega) (by omega) hB) fun m₂ c₂ ⟨R₂, f₂, hc₂⟩ => ?_)
  have F₂ : Frm L T29 m₁ m₂ := Frm.dyn (dyn_arr (k := 1) (by omega) b1) t2 f₂ hH
  rw [e₁, R₁.one] at R₂
  have R₂' : Rep L (St.setStat v 1 (St.setKey v nk s)) m₂ := R₂
  have X₂ : Fixed L x m₂ := X₁.frame hH F₂.2
  have e₂ : m₂ 13 = v := by rw [f₂ 13 (by omega) (by omega), e₁]
  have z₂ : m₂ 8 = 0 := R₂'.zero
  refine Runs.seqs_cons (Runs.mono (attach_spec R₂' X₂ (rv := 13) (rp := 8) (by omega) (by omega)
    (by rw [z₂]; change s.deg 0 < L.cap 0; simp [Lay.cap]; omega) (by omega) (by omega)
    (by simp [T267]) (by simp [T267]) hB) fun m₃ c₃ ⟨R₃, X₃, F₃, hc₃⟩ => ?_)
  rw [e₂, z₂] at R₃
  have e₃ : m₃ 13 = v := by rw [F₃.1 13 (by omega) (by simp [T267]), e₂]
  refine Runs.seqs_cons (Runs.mono (updMin_spec R₃ X₃ (rv := 13) (by omega) hm (by omega)
    (by simp [T29, T267]) hB) fun m₄ c₄ ⟨R₄, X₄, F₄, hc₄⟩ => ?_)
  rw [e₃] at R₄
  refine Runs.seqs_nilR (by omega) fun m₅ h₅ f₅ => ?_
  have F₅ : Frm L T29 m₄ m₅ := Frm.reg1 t2 (by omega) f₅
  exact ⟨R₄.regs1 (r := 2) (by simp [Tmp]) (by omega) f₅, X₄.frame hH F₅.2,
    F₁.trans (F₂.trans ((F₃.mono fun _ h => .inl h).trans (F₄.trans F₅))), by omega⟩

/-- Compare with the key of a vertex in the heap, and decrease it. -/
theorem relaxDec_spec (C : Ctx) {M : Finset ℕ} {u v w : ℕ} {s : St} (hR : Rep L s m)
    (hF : Fixed L x m) (h13 : m 13 = v) (h14 : m 14 = s.key u + w) (hv : v ≤ L.n)
    (hH : HeapInv C.n s M) (hvM : v ∈ M) (hMr : ∀ a ∈ M, 1 ≤ a ∧ a ≤ L.n)
    (hdg : ∀ a ∈ M, s.deg a ≤ L.D) (hFM : M.card ≤ C.F) (hB : L.top < B) :
    Runs B (seqs [rd 15 0 13, less 15 14 15, ite 15 3 Prog.decKey nop]) m fun m' k =>
      Rep L (if s.key u + w < s.key v then ShortestPaths.decKey C v (s.key u + w) s else s) m' ∧
        Fixed L x m' ∧ Frm L TD m m' ∧
        s.time + k ≤ (if s.key u + w < s.key v then ShortestPaths.decKey C v (s.key u + w) s
          else s).time + 10 := by
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have t2 : TD 2 := .inl (by simp [TC, T267])
  have t15 : TD 15 := .inl (by simp [TC])
  refine Runs.seqs_cons (Runs.mono (rd_spec hR (k := 0) (d := 15) (i := 13) (by omega)
    (by rw [h13]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ => ?_)
  rw [h13] at h₁
  have R₁ := hR.regs2 (r₁ := 2) (r₂ := 15) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₁
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  have R₂ := R₁.regs1 (r := 15) (by simp [Tmp]) (by omega) f₂
  have F₂ : Frm L TD m m₂ := (Frm.reg t15 (by omega) f₁ t2).trans (Frm.reg1 t15 (by omega) f₂)
  have X₂ : Fixed L x m₂ := hF.frame hH32 F₂.2
  have e13 : m₂ 13 = v := by rw [f₂ 13 (by omega), f₁ 13 (by omega) (by omega), h13]
  have e14 : m₂ 14 = s.key u + w := by rw [f₂ 14 (by omega), f₁ 14 (by omega) (by omega), h14]
  have e15 : m₂ 15 = if s.key u + w < s.key v then 1 else 0 := by
    rw [h₂, f₁ 14 (by omega) (by omega), h14, h₁]; rfl
  refine Runs.seqs_cons (Runs.ite (by omega) (by omega) (fun hlt => ?_) (fun hlt => ?_))
  · rw [e15, R₂.one] at hlt
    have hlt' : s.key u + w < s.key v := by by_contra hc; simp [hc] at hlt
    rw [if_pos hlt']
    refine Runs.mono (decKey_run C R₂ X₂ e13 e14 hH hvM hlt' hMr hdg hFM hB)
      fun m₃ c₃ ⟨R₃, X₃, F₃, hc₃⟩ => ?_
    refine Runs.seqs_nilR (by omega) fun m₄ h₄ f₄ => ?_
    have F₄ : Frm L TD m₃ m₄ := Frm.reg1 t2 (by omega) f₄
    exact ⟨R₃.regs1 (r := 2) (by simp [Tmp]) (by omega) f₄, X₃.frame hH32 F₄.2,
      F₂.trans (F₃.trans F₄), by omega⟩
  · rw [e15, R₂.one] at hlt
    have hlt' : ¬s.key u + w < s.key v := by intro hc; simp [hc] at hlt
    rw [if_neg hlt']
    refine Runs.constR (by omega) (by omega) fun m₃ h₃ f₃ => ?_
    refine Runs.seqs_nilR (by omega) fun m₄ h₄ f₄ => ?_
    have F₄ : Frm L TD m₂ m₄ := (Frm.reg1 t2 (by omega) f₃).trans (Frm.reg1 t2 (by omega) f₄)
    exact ⟨(R₂.regs1 (r := 2) (by simp [Tmp]) (by omega) f₃).regs1 (r := 2) (by simp [Tmp])
      (by omega) f₄, X₂.frame hH32 F₄.2, F₂.trans F₄, by omega⟩

/-- The three cases of a relaxation. -/
theorem relaxIte_spec (C : Ctx) {M : Finset ℕ} {u v w : ℕ} {s : St} (hR : Rep L s m)
    (hF : Fixed L x m) (h13 : m 13 = v) (h14 : m 14 = s.key u + w) (h15 : m 15 = s.stat v)
    (hv : v ≤ L.n) (hH : HeapInv C.n s M) (hd0 : s.deg 0 ≤ L.n) (hm : s.hmin ≤ L.n)
    (hv1 : s.stat v = 1 → v ∈ M) (hMr : ∀ a ∈ M, 1 ≤ a ∧ a ≤ L.n)
    (hdg : ∀ a ∈ M, s.deg a ≤ L.D) (hFM : M.card ≤ C.F) (hB : L.top < B) :
    Runs B (ite 15 8 (seqs [wr 0 13 14, wr 1 13 3, attach 13 8, updMin 13])
        (ite 15 3 (seqs [rd 15 0 13, less 15 14 15, ite 15 3 Prog.decKey nop]) nop)) m
      fun m' k => Rep L (relax C u v w s) m' ∧ Fixed L x m' ∧ Frm L TD m m' ∧
        s.time + k ≤ (relax C u v w s).time + 32 := by
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  refine Runs.ite (by omega) (by omega) (fun h0 => ?_) (fun h0 => ?_)
  · rw [h15, hR.zero] at h0
    have e : relax C u v w s =
        St.updMin v (St.attach v 0 (St.setStat v 1 (St.setKey v (s.key u + w) s))) := by
      unfold relax; dsimp only; rw [if_pos h0]
    rw [e]
    refine Runs.mono (relaxNew_spec hR hF h13 h14 hv hd0 hm hB) fun m' c ⟨R', X', F', hc⟩ =>
      ⟨R', X', F'.mono fun _ => T29_TD, ?_⟩
    rw [updMin_time]
    change s.time + _ ≤ s.time + 32
    omega
  · rw [h15, hR.zero] at h0
    refine Runs.ite (by omega) (by omega) (fun h1 => ?_) (fun h1 => ?_)
    · rw [h15, hR.one] at h1
      have e : relax C u v w s =
          if s.key u + w < s.key v then ShortestPaths.decKey C v (s.key u + w) s else s := by
        unfold relax; dsimp only; rw [if_neg h0, if_pos h1]
      rw [e]
      exact Runs.mono (relaxDec_spec C hR hF h13 h14 hv hH (hv1 h1) hMr hdg hFM hB)
        fun m' c ⟨R', X', F', hc⟩ => ⟨R', X', F', by omega⟩
    · rw [h15, hR.one] at h1
      have e : relax C u v w s = s := by
        unfold relax; dsimp only; rw [if_neg h0, if_neg h1]
      rw [e]
      refine Runs.constR (by omega) (by omega) fun m' h' f' => ?_
      have F' : Frm L TD m m' := Frm.reg1 (.inl (by simp [TC, T267])) (by omega) f'
      exact ⟨hR.regs1 (r := 2) (by simp [Tmp]) (by omega) f', hF.frame hH32 F'.2, F', by omega⟩

/-- A step of the scan runs as the model says. -/
theorem relaxBody_run (C : Ctx) {M : Finset ℕ} {u v w h : ℕ} {l : List (ℕ × ℕ)} {s : St}
    (hR : Rep L s m) (hF : Fixed L x m) (h30 : m 30 = u) (h31 : m 31 = h)
    (hl : Lst L m h ((v, w) :: l)) (hu : u ≤ L.n) (hv : v ≤ L.n) (hsum : s.key u + w < B)
    (hH : HeapInv C.n s M) (hd0 : s.deg 0 ≤ L.n) (hm : s.hmin ≤ L.n)
    (hv1 : s.stat v = 1 → v ∈ M) (hMr : ∀ a ∈ M, 1 ≤ a ∧ a ≤ L.n)
    (hdg : ∀ a ∈ M, s.deg a ≤ L.D) (hFM : M.card ≤ C.F) (hB : L.top < B) :
    Runs B relaxBody m fun m' k => Rep L (St.tick 50 (relax C u v w s)) m' ∧ Fixed L x m' ∧
      Frm L TR m m' ∧ m' 30 = u ∧ Lst L m' (m' 31) l ∧ m' 11 = (if 0 < m' 31 then 1 else 0) ∧
      s.time + k + 2 ≤ (St.tick 50 (relax C u v w s)).time := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hl
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hHE : 32 ≤ L.HE := by unfold Lay.HE; omega
  have hCT : L.CH ≤ L.top := by unfold Lay.top; omega
  have t2 : TR 2 := by simp [TR, TD, TC, T267]
  have t13 : TR 13 := by simp [TR]
  have t14 : TR 14 := by simp [TR]
  have t15 : TR 15 := by simp [TR, TD, TC]
  have t11 : TR 11 := by simp [TR, TD, TC]
  have t31 : TR 31 := by simp [TR]
  have n30 : ¬TR 30 := by simp [TR, TD, TC, TU, T267]
  have d30 : ¬TD 30 := fun h => n30 (.inl h)
  have d31 : ¬TD 31 := by simp [TD, TC, TU, T267]
  have d13 : ¬TD 13 := by simp [TD, TC, TU, T267]
  unfold relaxBody
  -- Read the half-edge.
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h31, hR.one]; omega) fun m₁ g₁ f₁ => ?_)
  rw [h31, hR.one] at g₁
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₂ g₂ f₂ => ?_)
  have v₂ : m₂ 13 = v := by rw [g₂, g₁, f₁ _ (by omega), l3]
  have o₂ : m₂ 3 = 1 := by rw [f₂ 3 (by omega), f₁ 3 (by omega), hR.one]
  have a₂ : m₂ 2 = h + 1 := by rw [f₂ 2 (by omega), g₁]
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [a₂, o₂]; omega) fun m₃ g₃ f₃ => ?_)
  rw [a₂, o₂] at g₃
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₄ g₄ f₄ => ?_)
  have w₄ : m₄ 14 = w := by
    rw [g₄, g₃, f₃ _ (by omega), f₂ _ (by omega), f₁ _ (by omega)]; exact l4
  have tt : ∀ {r}, r = 2 ∨ r = 13 ∨ r = 14 → Tmp r := fun h => by
    rcases h with rfl | rfl | rfl <;> simp [Tmp]
  have R₄ : Rep L s m₄ := (((hR.regs1 (r := 2) (tt (by simp)) (by omega) f₁).regs1 (r := 13)
    (tt (by simp)) (by omega) f₂).regs1 (r := 2) (tt (by simp)) (by omega) f₃).regs1 (r := 14)
    (tt (by simp)) (by omega) f₄
  have F₄ : Frm L TR m m₄ := (Frm.reg1 t2 (by omega) f₁).trans ((Frm.reg1 t13 (by omega) f₂).trans
    ((Frm.reg1 t2 (by omega) f₃).trans (Frm.reg1 t14 (by omega) f₄)))
  have X₄ : Fixed L x m₄ := hF.frame hH32 F₄.2
  have u₄ : m₄ 30 = u := by rw [F₄.1 30 (by omega) n30, h30]
  have k₄ : m₄ 31 = h := by
    rw [f₄ 31 (by omega), f₃ 31 (by omega), f₂ 31 (by omega), f₁ 31 (by omega), h31]
  have v₄ : m₄ 13 = v := by rw [f₄ 13 (by omega), f₃ 13 (by omega), v₂]
  -- The new key.
  refine Runs.seqs_cons (Runs.mono (rd_spec R₄ (k := 0) (d := 15) (i := 30) (by omega)
    (by rw [u₄]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₅ c₅ ⟨g₅, f₅, hc₅⟩ => ?_)
  rw [u₄] at g₅
  replace g₅ : m₅ 15 = s.key u := g₅
  have R₅ := R₄.regs2 (r₁ := 2) (r₂ := 15) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₅
  have w₅ : m₅ 14 = w := by rw [f₅ 14 (by omega) (by omega), w₄]
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [g₅, w₅]; exact hsum) fun m₆ g₆ f₆ => ?_)
  rw [g₅, w₅] at g₆
  have R₆ := R₅.regs1 (r := 14) (by simp [Tmp]) (by omega) f₆
  have v₆ : m₆ 13 = v := by rw [f₆ 13 (by omega), f₅ 13 (by omega) (by omega), v₄]
  -- The status of `v`.
  refine Runs.seqs_cons (Runs.mono (rd_spec R₆ (k := 1) (d := 15) (i := 13) (by omega)
    (by rw [v₆]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₇ c₇ ⟨g₇, f₇, hc₇⟩ => ?_)
  rw [v₆] at g₇
  replace g₇ : m₇ 15 = s.stat v := g₇
  have R₇ := R₆.regs2 (r₁ := 2) (r₂ := 15) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₇
  have F₇ : Frm L TR m₄ m₇ := (Frm.reg t15 (by omega) f₅ t2).trans ((Frm.reg1 t14
      (by omega) f₆).trans
    (Frm.reg t15 (by omega) f₇ t2))
  have X₇ : Fixed L x m₇ := X₄.frame hH32 F₇.2
  have v₇ : m₇ 13 = v := by rw [f₇ 13 (by omega) (by omega), v₆]
  have n₇ : m₇ 14 = s.key u + w := by rw [f₇ 14 (by omega) (by omega), g₆]
  have u₇ : m₇ 30 = u := by rw [F₇.1 30 (by omega) n30, u₄]
  have k₇ : m₇ 31 = h := by
    rw [f₇ 31 (by omega) (by omega), f₆ 31 (by omega), f₅ 31 (by omega) (by omega), k₄]
  refine Runs.seqs_cons (Runs.mono (relaxIte_spec C R₇ X₇ v₇ n₇ g₇ hv hH hd0 hm hv1 hMr hdg hFM hB)
    fun m₈ c₈ ⟨R₈, X₈, F₈, hc₈⟩ => ?_)
  have Fa : Frm L TR m m₈ := F₄.trans (F₇.trans (F₈.mono fun _ => TD_TR))
  have nd : ¬L.Dyn h := fun hd => by unfold Lay.Dyn Lay.top at hd; unfold Lay.HE at l1; omega
  have k₈ : m₈ 31 = h := by rw [F₈.1 31 (by omega) d31, k₇]
  have u₈ : m₈ 30 = u := by rw [F₈.1 30 (by omega) d30, u₇]
  -- The next half-edge.
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₉ g₉ f₉ => ?_)
  have n₉ : m₉ 31 = m h := by rw [g₉, k₈, Fa.2 h (by omega) nd]
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₁₀ g₁₀ f₁₀ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₁₁ g₁₁ f₁₁ => ?_
  have z₉ : m₉ 8 = 0 := by rw [f₉ 8 (by omega), R₈.zero]
  have Fe : Frm L TR m₈ m₁₁ := (Frm.reg1 t31 (by omega) f₉).trans ((Frm.reg1 t11
      (by omega) f₁₀).trans
    (Frm.reg1 t2 (by omega) f₁₁))
  have Ft : Frm L TR m m₁₁ := Fa.trans Fe
  have e31 : m₁₁ 31 = m h := by rw [f₁₁ 31 (by omega), f₁₀ 31 (by omega), n₉]
  have e11 : m₁₁ 11 = if m₉ 8 < m₉ 31 then 1 else 0 := by rw [f₁₁ 11 (by omega), g₁₀]
  refine ⟨?_, X₈.frame hH32 Fe.2, Ft, ?_, ?_, ?_, ?_⟩
  · exact (((R₈.regs1 (r := 31) (by simp [Tmp]) (by omega) f₉).regs1 (r := 11) (by simp [Tmp])
      (by omega) f₁₀).regs1 (r := 2) (by simp [Tmp]) (by omega) f₁₁).same
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [Ft.1 30 (by omega) n30, h30]
  · rw [e31]; exact Lst.frame hH32 Ft.2 l _ l5
  · rw [e11, z₉, n₉, e31]
  · change s.time + _ + 2 ≤ (relax C u v w s).time + 50
    omega

end Formalgo.Algorithms.ShortestPaths
