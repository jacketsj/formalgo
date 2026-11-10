import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunCut
import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Heap.HeapConsol

/-!
# Running the links of consolidation

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ σ' : St} {m : Mem} {B : ℕ} {x : EInput}

/-- Two states agree on everything the memory holds. -/
structure Same (σ σ' : St) : Prop where
  key : σ'.key = σ.key
  stat : σ'.stat = σ.stat
  par : σ'.par = σ.par
  deg : σ'.deg = σ.deg
  mark : σ'.mark = σ.mark
  pos : σ'.pos = σ.pos
  tbl : σ'.tbl = σ.tbl
  ch : σ'.ch = σ.ch
  hmin : σ'.hmin = σ.hmin

theorem Rep.same (h : Rep L σ m) (hs : Same σ σ') : Rep L σ' m := by
  have hf : ∀ k, fld σ' k = fld σ k := fun k => by
    rcases k with _ | _ | _ | _ | _ | _ | _ | k
    · exact hs.key
    · exact hs.stat
    · exact hs.par
    · exact hs.deg
    · exact hs.mark
    · exact hs.pos
    · exact hs.tbl
    · rfl
  exact ⟨h.H32, h.base, h.n, h.D, by rw [hs.hmin]; exact h.hmin, h.one, h.zero, h.three,
    fun k hk i hi => by rw [hf]; exact h.arr k hk i hi, fun v hv j hj => by rw [hs.ch]; exact h.ch v hv j hj⟩

theorem Same.link_tick (y x' : ℕ) (s : St) :
    Same (setFld 4 y 0 (St.attach y x' s)) (St.tick 40 (St.link y x' s)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Swap `x` (`14`) and `y` (`12`) if `M[11] = 1`. -/
theorem swap_spec {xv yv : ℕ} (h14 : m 14 = xv) (h12 : m 12 = yv) (h3 : m 3 = 1) (hB : 32 < B)
    (c : Prop) [Decidable c] (h11 : m 11 = if c then 1 else 0) :
    Runs B (ite 11 3 (seqs [copy 11 14, copy 14 12, copy 12 11]) nop) m fun m' k =>
      m' 14 = (if c then yv else xv) ∧ m' 12 = (if c then xv else yv) ∧
      (∀ a, a ≠ 2 → a ≠ 11 → a ≠ 12 → a ≠ 14 → m' a = m a) ∧ k ≤ 6 := by
  refine Runs.ite (by omega) (by omega) (fun he => ?_) (fun he => ?_)
  · have hc : c := by by_contra hc; rw [h11, h3, if_neg hc] at he; omega
    refine Runs.seqs_cons (Runs.copyR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
    refine Runs.seqs_cons (Runs.copyR (by omega) (by omega) fun m₂ g₂ f₂ => ?_)
    refine Runs.seqs_cons (Runs.copyR (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
    refine Runs.seqs_nilR (by omega) fun m₄ g₄ f₄ => ?_
    simp only [if_pos hc]
    refine ⟨?_, ?_, fun a a2 a11 a12 a14 => ?_, by omega⟩
    · rw [f₄ 14 (by omega), f₃ 14 (by omega), g₂, f₁ 12 (by omega), h12]
    · rw [f₄ 12 (by omega), g₃, f₂ 11 (by omega), g₁, h14]
    · rw [f₄ a a2, f₃ a a12, f₂ a a14, f₁ a a11]
  · have hc : ¬c := by intro hc; rw [h11, h3, if_pos hc] at he; exact he rfl
    refine Runs.constR (by omega) (by omega) fun m₁ g₁ f₁ => ?_
    simp only [if_neg hc]
    exact ⟨by rw [f₁ 14 (by omega), h14], by rw [f₁ 12 (by omega), h12],
      fun a a2 _ _ _ => f₁ a a2, by omega⟩

/-- The registers the link loop uses. -/
def TL (a : ℕ) : Prop := T267 a ∨ a = 11 ∨ a = 12 ∨ a = 14 ∨ a = 15 ∨ a = 17 ∨ a = 31

theorem T267_TL {a : ℕ} (h : T267 a) : TL a := .inl h

theorem TL_tmp {a : ℕ} (h : TL a) : Tmp a := by
  rcases h with (h | h | h) | h | h | h | h | h | h <;> simp [Tmp, h]

/-- The link loop's state in memory. -/
structure LinkR (L : Lay) (x : EInput) (m₀ : Mem) (P : St × ℕ × ℕ → Prop) (a : St × ℕ × ℕ)
    (m : Mem) : Prop where
  rep : Rep L a.1 m
  fixed : Fixed L x m
  frm : Frm L TL m₀ m
  r14 : m 14 = a.2.1
  r15 : m 15 = a.2.2
  r12 : m 12 = a.1.tbl a.2.2
  r17 : m 17 = if 0 < a.1.tbl a.2.2 then 1 else 0
  inv : P a

theorem linkBody_spec (C : Ctx) {M : Finset ℕ} {D Q d₀ : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = D) (hD : D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) {a : St × ℕ × ℕ}
    (h : LinkR L x m₀ (LinkInv D M Q d₀ s₀) a m) (hc : linkCond a) :
    Runs B linkBody m fun m' k => LinkR L x m₀ (LinkInv D M Q d₀ s₀) (linkStep a) m' ∧
      a.1.time + k + 2 ≤ (linkStep a).1.time := by
  obtain ⟨s, xv, dx⟩ := a
  obtain ⟨hR, hF, hfr, h14, h15, h12, h17, hI⟩ := h
  simp only [linkCond] at hc h14 h15 h12 h17 hI
  obtain ⟨hdxD, hyM, hyd⟩ := hI.tbl dx hc
  have hxM : xv ∈ M := hI.xM
  have hyd' : s.deg (s.tbl dx) = dx := hyd
  have hxdeg : s.deg xv = dx := hI.xdeg
  have hxn := (hM _ hxM).2
  have hyn := (hM _ hyM).2
  have hxd : s.deg xv < D := by rw [hD]; exact hI.forest.deg_lt hM hxM
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have tT : ∀ a, TL a → Tmp a := fun a ha => TL_tmp ha
  have hstep := hI.step hc
  set y := s.tbl dx with hy
  set x' := if s.key y < s.key xv then y else xv with hx'
  set y' := if s.key y < s.key xv then xv else y with hy'
  have hls : linkStep (s, xv, dx) = (St.tick 40 (St.link y' x' (St.setTbl dx 0 s)), x', dx + 1) := rfl
  rw [hls] at hstep ⊢
  unfold linkBody
  -- `tbl dx := 0`
  refine Runs.seqs_cons (Runs.mono (wr_spec hR (k := 6) (i := 15) (s := 8) (by omega)
    (by rw [h15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₁ c₁ ⟨R₁, f₁, hc₁⟩ => ?_)
  rw [h15, hR.zero] at R₁
  have hd1 : L.Dyn (L.H + 6 * L.R + m 15) := dyn_arr (k := 6) (by omega) (by rw [h15]; simp [Lay.bnd]; omega)
  have F₁ : Frm L TL m m₁ := Frm.dyn hd1 (by simp [TL, T267]) f₁ hH
  have g₁ : ∀ r, r < 32 → r ≠ 2 → m₁ r = m r := fun r hr h2 => f₁ r h2 (by omega)
  -- `M[11] := key y`, `M[31] := key x`, compared.
  refine Runs.seqs_cons (Runs.mono (rd_spec R₁ (k := 0) (d := 11) (i := 12) (by omega)
    (by rw [g₁ 12 (by omega) (by omega), h12]; simp [Lay.bnd]; omega) (by omega) (by omega)
    (by omega) hB) fun m₂ c₂ ⟨h₂, f₂, hc₂⟩ => ?_)
  rw [g₁ 12 (by omega) (by omega), h12] at h₂
  refine Runs.seqs_cons (Runs.mono (rd_spec (σ := setFld 6 dx 0 s) (m := m₂)
    (R₁.reg (T := TL) tT (Frm.reg (by simp [TL]) (by omega) f₂ (by simp [TL, T267]))
      (fun a ha => f₂ a (by omega) (by omega))) (k := 0) (d := 31) (i := 14) (by omega)
    (by rw [f₂ 14 (by omega) (by omega), g₁ 14 (by omega) (by omega), h14]; simp [Lay.bnd]; omega)
    (by omega) (by omega) (by omega) hB) fun m₃ c₃ ⟨h₃, f₃, hc₃⟩ => ?_)
  rw [f₂ 14 (by omega) (by omega), g₁ 14 (by omega) (by omega), h14] at h₃
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₄ h₄ f₄ => ?_)
  have h₄11 : m₄ 11 = if s.key y < s.key xv then 1 else 0 := by
    rw [h₄, f₃ 11 (by omega) (by omega), h₂, h₃]; rfl
  have F₄ : Frm L TL m₁ m₄ := (Frm.reg (by simp [TL]) (by omega) f₂ (by simp [TL, T267])).trans
    ((Frm.reg (by simp [TL]) (by omega) f₃ (by simp [TL, T267])).trans
      (Frm.reg1 (by simp [TL]) (by omega) f₄))
  have R₄ : Rep L (setFld 6 dx 0 s) m₄ := R₁.reg tT F₄ (fun a ha => by
    rw [f₄ a (by omega), f₃ a (by omega) (by omega), f₂ a (by omega) (by omega)])
  have e₄ : ∀ r, r ≠ 2 → r ≠ 11 → r ≠ 31 → m₄ r = m₁ r := fun r a2 a11 a31 => by
    rw [f₄ r a11, f₃ r a2 a31, f₂ r a2 a11]
  -- Swap.
  refine Runs.seqs_cons (Runs.mono (swap_spec (xv := xv) (yv := y)
    (by rw [e₄ 14 (by omega) (by omega) (by omega), g₁ 14 (by omega) (by omega), h14])
    (by rw [e₄ 12 (by omega) (by omega) (by omega), g₁ 12 (by omega) (by omega), h12])
    (by rw [e₄ 3 (by omega) (by omega) (by omega), g₁ 3 (by omega) (by omega), hR.one])
    (by omega) (s.key y < s.key xv) h₄11) fun m₅ c₅ ⟨h₅14, h₅12, f₅, hc₅⟩ => ?_)
  have F₅ : Frm L TL m₄ m₅ := ⟨fun a _ hT => f₅ a (fun h => hT (by simp [TL, T267, h]))
    (fun h => hT (by simp [TL, h])) (fun h => hT (by simp [TL, h])) (fun h => hT (by simp [TL, h])),
    fun a ha _ => f₅ a (by omega) (by omega) (by omega) (by omega)⟩
  have R₅ : Rep L (setFld 6 dx 0 s) m₅ := R₄.reg tT F₅
    (fun a ha => f₅ a (by omega) (by omega) (by omega) (by omega))
  have X₅ : Fixed L x m₅ := hF.frame hH (F₁.trans (F₄.trans F₅)).2
  -- Link `y'` below `x'`.
  have hx'n : x' ≤ L.n := by rw [hx']; split_ifs <;> omega
  have hy'n : y' ≤ L.n := by rw [hy']; split_ifs <;> omega
  have hx'0 : x' ≠ 0 := by
    have := (hM _ hxM).1; have := (hM _ hyM).1; rw [hx']; split_ifs <;> omega
  have hdx' : s.deg x' = dx := by rw [hx']; split_ifs <;> [exact hyd'; exact hxdeg]
  refine Runs.seqs_cons (Runs.mono (attach_spec R₅ X₅ (rv := 12) (rp := 14) (by rw [h₅12]; exact hy'n)
    (by rw [h₅14]; exact hx'n) (by
      rw [h₅14]; change s.deg x' < L.cap x'; rw [hdx']; simp [Lay.cap, hx'0]; omega)
    (by omega) (by omega) (by simp [T267]) (by simp [T267]) hB) fun m₆ c₆ ⟨R₆, X₆, F₆, hc₆⟩ => ?_)
  rw [h₅12, h₅14] at R₆
  have g₆ : ∀ r, r < 32 → ¬T267 r → m₆ r = m₅ r := F₆.1
  -- `mark y' := 0`
  refine Runs.seqs_cons (Runs.mono (wr_spec R₆ (k := 4) (i := 12) (s := 8) (by omega)
    (by rw [g₆ 12 (by omega) (by simp [T267]), h₅12]; simp [Lay.bnd]; omega) (by omega) (by omega)
    (by omega) hB) fun m₇ c₇ ⟨R₇, f₇, hc₇⟩ => ?_)
  have z₆ : m₆ 8 = 0 := by
    rw [g₆ 8 (by omega) (by simp [T267]), f₅ 8 (by omega) (by omega) (by omega) (by omega),
      e₄ 8 (by omega) (by omega) (by omega), g₁ 8 (by omega) (by omega), hR.zero]
  rw [g₆ 12 (by omega) (by simp [T267]), h₅12, z₆] at R₇
  have hd7 : L.Dyn (L.H + 4 * L.R + m₆ 12) := dyn_arr (k := 4) (by omega)
    (by rw [g₆ 12 (by omega) (by simp [T267]), h₅12]; simp [Lay.bnd]; omega)
  have F₇ : Frm L TL m₆ m₇ := Frm.dyn hd7 (by simp [TL, T267]) f₇ hH
  have e₇ : ∀ r, r < 32 → r ≠ 2 → m₇ r = m₆ r := fun r hr h2 => f₇ r h2 (by omega)
  -- `dx := dx + 1`, `y := tbl (dx + 1)`
  have h₇15 : m₇ 15 = dx := by
    rw [e₇ 15 (by omega) (by omega), g₆ 15 (by omega) (by simp [T267]),
      f₅ 15 (by omega) (by omega) (by omega) (by omega), e₄ 15 (by omega) (by omega) (by omega),
      g₁ 15 (by omega) (by omega), h15]
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h₇15, e₇ 3 (by omega) (by omega), R₆.one]; simp [Lay.bnd] at *; omega)
    fun m₈ h₈ f₈ => ?_)
  have h₈15 : m₈ 15 = dx + 1 := by rw [h₈, h₇15, e₇ 3 (by omega) (by omega), R₆.one]
  have R₈ := R₇.reg (T := TL) tT (Frm.reg1 (by simp [TL]) (by omega) f₈) (fun a ha => f₈ a (by omega))
  refine Runs.seqs_cons (Runs.mono (rd_spec R₈ (k := 6) (d := 12) (i := 15) (by omega)
    (by rw [h₈15]; simp [Lay.bnd]; omega) (by omega) (by omega) (by omega) hB)
    fun m₉ c₉ ⟨h₉, f₉, hc₉⟩ => ?_)
  rw [h₈15] at h₉
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₁₀ h₁₀ f₁₀ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₁₁ h₁₁ f₁₁ => ?_
  have F₁₁ : Frm L TL m₇ m₁₁ := (Frm.reg1 (by simp [TL]) (by omega) f₈).trans
    ((Frm.reg (by simp [TL]) (by omega) f₉ (by simp [TL, T267])).trans
      ((Frm.reg1 (by simp [TL]) (by omega) f₁₀).trans (Frm.reg1 (by simp [TL, T267]) (by omega) f₁₁)))
  have Fall : Frm L TL m m₁₁ := F₁.trans (F₄.trans (F₅.trans
    ((F₆.mono fun a ha => T267_TL ha).trans (F₇.trans F₁₁))))
  have R₁₁ := R₇.reg (T := TL) tT F₁₁ (fun a ha => by
    rw [f₁₁ a (by omega), f₁₀ a (by omega), f₉ a (by omega) (by omega), f₈ a (by omega)])
  refine ⟨⟨R₁₁.same (Same.link_tick y' x' _), hF.frame hH Fall.2, hfr.trans Fall, ?_, ?_, ?_, ?_,
    hstep.1⟩, ?_⟩
  · rw [f₁₁ 14 (by omega), f₁₀ 14 (by omega), f₉ 14 (by omega) (by omega), f₈ 14 (by omega),
      e₇ 14 (by omega) (by omega), g₆ 14 (by omega) (by simp [T267]), h₅14]
  · rw [f₁₁ 15 (by omega), f₁₀ 15 (by omega), f₉ 15 (by omega) (by omega), h₈15]
  · rw [f₁₁ 12 (by omega), f₁₀ 12 (by omega), h₉]; rfl
  · rw [f₁₁ 17 (by omega), h₁₀, f₉ 8 (by omega) (by omega), f₈ 8 (by omega),
      e₇ 8 (by omega) (by omega), z₆, h₉]
    rfl
  · change s.time + _ + 2 ≤ s.time + 40
    omega

theorem linkLoop_spec (C : Ctx) {M : Finset ℕ} {D Q d₀ : ℕ} {s₀ : St} {m₀ : Mem}
    (hLn : L.n = C.n) (hLD : L.D = D) (hD : D = 2 * Nat.size C.n)
    (hM : ∀ v ∈ M, 1 ≤ v ∧ v ≤ C.n) (hB : L.top < B) (hFu : D ≤ C.F) {a : St × ℕ × ℕ}
    (h : LinkR L x m₀ (LinkInv D M Q d₀ s₀) a m) :
    Runs B (loop 17 3 linkBody) m fun m' k =>
      LinkR L x m₀ (LinkInv D M Q d₀ s₀) (whileF linkCond linkStep C.F a) m' ∧
        a.1.time + k ≤ (whileF linkCond linkStep C.F a).1.time + 1 ∧
        ¬linkCond (whileF linkCond linkStep C.F a) := by
  have ht := top_ge (L := L)
  have hH := h.rep.H32
  have hstop := (link_loop C h.inv hFu).2
  refine Runs.mono (Runs.loop_refine (LinkR L x m₀ (LinkInv D M Q d₀ s₀)) linkCond linkStep
    (fun a => a.1.time) (by omega) (by omega) (fun a m hR => ?_)
    (fun a m hR hc => linkBody_spec C hLn hLD hD hM hB hR hc) C.F a m h hstop)
    fun m' k ⟨hR, hk⟩ => ⟨hR, hk, hstop⟩
  rw [hR.r17, hR.rep.one]
  simp only [linkCond]
  constructor
  · intro he; split_ifs at he with hp <;> omega
  · intro hne; rw [if_pos (by omega)]

end Formalgo.Algorithms.ShortestPaths
