import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunScan

/-!
# Running the main loop

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : Input} {C : Ctx} {G : WGraph} {src W : ℕ}

/-- The registers the main loop uses. -/
def TW (a : ℕ) : Prop := TE a ∨ TR a

/-- Read the head of an adjacency list. -/
theorem rdHead_spec (hR : Rep L σ m) {d i : ℕ} (hi : m i ≤ L.n) (hd : d < 32) (hi32 : i < 32)
    (hB : L.top < B) :
    Runs B (rd d 7 i) m fun m' c => m' d = m (L.H + 7 * L.R + m i) ∧
      (∀ a, a ≠ 2 → a ≠ d → m' a = m a) ∧ c = 2 := by
  have ht := top_ge (L := L)
  have hH := hR.H32
  have hb := hR.base 7 (by omega)
  have hb' : m 25 = L.H + 7 * L.R := hb
  have hRn : L.n + L.D + 3 = L.R := rfl
  refine Runs.seq (Runs.addR (by omega) (by have := breg_lt 7 (by omega); omega) (by omega)
    (by rw [hb]; omega) fun m₁ h₁ f₁ => Runs.loadR (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  refine ⟨?_, fun a h2 hd' => by rw [f₂ a hd', f₁ a h2], rfl⟩
  rw [h₂, h₁, hb, f₁ _ (by omega)]

/-- A step of the main loop runs as the model says. -/
theorem mainBody_run (hC : CtxOK C) (hA : AdjOK C G W) (hLn : L.n = C.n) (hLD : L.D = C.D)
    (hadj : C.adj = adjX x) {hs : src < G.n} {s : St} (hD : DInv C G W hs s) (hc : rootsCond s)
    (hKB : (G.n + 1) * W < B) (hB : L.top < B) (hR : Rep L s m) (hF : Fixed L x m) :
    Runs B mainBody m fun m' k => Rep L (mainStep C s) m' ∧ Fixed L x m' ∧ Frm L TW m m' ∧
      m' 12 = (if 0 < (mainStep C s).deg 0 then 1 else 0) ∧
      s.time + k + 2 ≤ (mainStep C s).time := by
  have hH32 := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have hnG : L.n = G.n := hLn.trans hA.n_eq
  have hg := hD.g
  have hc' : s.deg 0 ≠ 0 := hc
  have hne : (hset G.n s).Nonempty := ⟨_, (hg.heap.roots.list 0 (by omega)).1⟩
  obtain ⟨m1, -, -⟩ := hg.heap.min hne
  obtain ⟨hun, hu0, -⟩ := mem_hset.1 m1
  have hle : s.hmin ≤ L.n := by omega
  let u' : Fin G.n := ⟨s.hmin - 1, by omega⟩
  have hu'1 : (u' : ℕ) + 1 = s.hmin := by simp only [u']; omega
  have hI := hD.scan_start hC hA hc hu'1
  have hH : HeapInv C.n s (hset G.n s) := by rw [hA.n_eq]; exact hg.heap
  have hKB' : ((done G.n s).card + 1) * W < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_right W (by have := card_done_le G.n s; omega)) hKB
  have t2 : TW 2 := .inr (by simp [TR, TD, TC, T267])
  have t6 : TW 6 := .inr (by simp [TR, TD, TC, T267])
  have t11 : TW 11 := .inr (by simp [TR, TD, TC])
  have t12 : TW 12 := .inr (by simp [TR, TD, TC])
  have t31 : TW 31 := .inr (by simp [TR])
  set s₂ := St.setStat s.hmin 2 (extract C s) with hs₂
  set t := (whileF scanCond (scanStep C) C.F (s₂, (u' : ℕ) + 1, C.adj ((u' : ℕ) + 1))).1 with ht'
  have e : mainStep C s = St.tick 20 t := by rw [ht', hu'1]; rfl
  rw [e]
  unfold mainBody
  -- Take out the minimum, and settle it.
  refine Runs.seqs_cons (Runs.mono (extractMin_spec C hC hLn hLD hB hH hne hR hF)
    fun m₁ c₁ ⟨R₁, X₁, F₁, z₁, hc₁⟩ => ?_)
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [R₁.one]; omega) fun m₂ g₂ f₂ => ?_)
  rw [R₁.one] at g₂
  have R₂ := R₁.regs1 (r := 6) (by simp [Tmp]) (by omega) f₂
  have z₂ : m₂ 30 = s.hmin := by rw [f₂ 30 (by omega), z₁]
  have b1 : m₂ 30 ≤ L.bnd 1 := by rw [z₂]; simpa [Lay.bnd] using hle
  refine Runs.seqs_cons (Runs.mono (wr_spec R₂ (k := 1) (i := 30) (s := 6) (by omega) b1
    (by omega) (by omega) (by omega) hB) fun m₃ c₃ ⟨R₃, f₃, hc₃⟩ => ?_)
  rw [z₂, g₂] at R₃
  replace R₃ : Rep L s₂ m₃ := R₃
  have F₃ : Frm L TW m₁ m₃ := (Frm.reg1 t6 (by omega) f₂).trans
    (Frm.dyn (dyn_arr (k := 1) (by omega) b1) t2 f₃ hH32)
  have X₃ : Fixed L x m₃ := X₁.frame hH32 F₃.2
  have z₃ : m₃ 30 = s.hmin := by rw [f₃ 30 (by omega) (by omega), z₂]
  -- Scan its adjacency list.
  refine Runs.seqs_cons (Runs.mono (rdHead_spec R₃ (d := 31) (i := 30) (by omega) (by omega)
    (by omega) hB) fun m₄ c₄ ⟨g₄, f₄, hc₄⟩ => ?_)
  rw [z₃] at g₄
  have R₄ := R₃.regs2 (r₁ := 2) (r₂ := 31) (by simp [Tmp]) (by simp [Tmp]) (by omega) (by omega) f₄
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₅ g₅ f₅ => ?_)
  have R₅ := R₄.regs1 (r := 11) (by simp [Tmp]) (by omega) f₅
  have F₅ : Frm L TW m₃ m₅ := (Frm.reg t31 (by omega) f₄ t2).trans (Frm.reg1 t11 (by omega) f₅)
  have X₅ : Fixed L x m₅ := X₃.frame hH32 F₅.2
  have z₅ : m₅ 30 = (u' : ℕ) + 1 := by
    rw [f₅ 30 (by omega), f₄ 30 (by omega) (by omega), z₃, hu'1]
  have ea : m₅ (L.H + 7 * L.R + s.hmin) = m₅ 31 := by
    rw [f₅ 31 (by omega), g₄, f₅ _ (by omega), f₄ _ (by omega) (by omega)]
  have hl : Lst L m₅ (m₅ 31) (C.adj ((u' : ℕ) + 1)) := by
    rw [hu'1, hadj, ← ea]; exact X₅.head _ hle
  have h11 : m₅ 11 = if 0 < m₅ 31 then 1 else 0 := by
    rw [g₅, f₅ 31 (by omega), R₄.zero]
  refine Runs.seqs_cons (Runs.mono (scan_run hC hA hLn hLD hKB' hB hI R₅ X₅ z₅ hl h11)
    fun m₆ c₆ ⟨R₆, X₆, F₆, hk₆⟩ => ?_)
  replace R₆ : Rep L t m₆ := R₆
  replace hk₆ : s₂.time + c₆ ≤ t.time + 1 := hk₆
  -- Are there more roots?
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₇ g₇ f₇ => ?_)
  have hd : m₇ 11 = t.deg 0 := by
    have h21 : m₆ 21 = L.H + 3 * L.R := R₆.base 3 (by omega)
    rw [g₇, h21]
    exact R₆.arr 3 (by omega) 0 (by omega)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₈ g₈ f₈ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₉ g₉ f₉ => ?_
  have F₉ : Frm L TW m₆ m₉ := (Frm.reg1 t11 (by omega) f₇).trans ((Frm.reg1 t12 (by omega) f₈).trans
    (Frm.reg1 t2 (by omega) f₉))
  have z₇ : m₇ 8 = 0 := by rw [f₇ 8 (by omega), R₆.zero]
  refine ⟨?_, X₆.frame hH32 F₉.2, (F₁.mono fun _ h => .inl h).trans (F₃.trans (F₅.trans
    ((F₆.mono fun _ h => .inr h).trans F₉))), ?_, ?_⟩
  · exact (((R₆.regs1 (r := 11) (by simp [Tmp]) (by omega) f₇).regs1 (r := 12) (by simp [Tmp])
      (by omega) f₈).regs1 (r := 2) (by simp [Tmp]) (by omega) f₉).same
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [f₉ 12 (by omega), g₈, z₇, hd]; rfl
  · have ht₂ : s₂.time = (extract C s).time := rfl
    change s.time + _ + 2 ≤ t.time + 20
    omega

/-- The main loop's state in memory. -/
structure MainR (L : Lay) (x : Input) (m₀ : Mem) (P : St → Prop) (a : St) (m : Mem) : Prop where
  inv : P a
  rep : Rep L a m
  fix : Fixed L x m
  frm : Frm L TW m₀ m
  r12 : m 12 = if 0 < a.deg 0 then 1 else 0

theorem main_run (hC : CtxOK C) (hA : AdjOK C G W) (hLn : L.n = C.n) (hLD : L.D = C.D)
    (hadj : C.adj = adjX x) {hs : src < G.n} {s₀ : St} (h0 : DInv C G W hs s₀)
    (hKB : (G.n + 1) * W < B) (hB : L.top < B) (hR : Rep L s₀ m) (hF : Fixed L x m)
    (h12 : m 12 = if 0 < s₀.deg 0 then 1 else 0) :
    Runs B (loop 12 3 mainBody) m fun m' k =>
      Rep L (whileF rootsCond (mainStep C) C.F s₀) m' ∧ Fixed L x m' ∧ Frm L TW m m' ∧
        s₀.time + k ≤ (whileF rootsCond (mainStep C) C.F s₀).time + 1 := by
  have ht := top_ge (L := L)
  have hH := hR.H32
  have hstop := whileF_stops (DInv C G W hs) (fun b => G.n - (done G.n b).card)
    (fun b hb hc => hb.step hC hA hc) C.F _ h0 (by have := hC.fuel; rw [hA.n_eq] at this; omega)
  refine Runs.mono (Runs.loop_refine (MainR L x m (DInv C G W hs)) rootsCond (mainStep C)
    (fun a => a.time) (by omega) (by omega) (fun a m' hR' => ?_) (fun a m' hR' hc => ?_) C.F _ m
    ⟨h0, hR, hF, Frm.refl, h12⟩ hstop) fun m' k ⟨hR', hk⟩ => ⟨hR'.rep, hR'.fix, hR'.frm, hk⟩
  · rw [hR'.r12, hR'.rep.one]
    change _ ↔ a.deg 0 ≠ 0
    by_cases h : 0 < a.deg 0
    · rw [if_pos h]; exact ⟨fun _ => by omega, fun _ => rfl⟩
    · rw [if_neg h]; exact ⟨fun e => by omega, fun e => by omega⟩
  · refine Runs.mono (mainBody_run hC hA hLn hLD hadj hR'.inv hc hKB hB hR'.rep hR'.fix)
      fun m₁ k ⟨R₁, X₁, F₁, g₁, hk⟩ => ⟨⟨(hR'.inv.step hC hA hc).1, R₁, X₁, hR'.frm.trans F₁, g₁⟩, hk⟩

end Formalgo.Algorithms.ShortestPaths
