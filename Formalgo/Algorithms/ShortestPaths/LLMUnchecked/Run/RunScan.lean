import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunRelax

/-!
# Running the scan of a settled vertex

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m : Mem} {B : ℕ} {x : Input} {C : Ctx} {G : WGraph} {src W : ℕ}

/-- A nonzero head means a nonempty list. -/
theorem Lst.pos (H32 : 32 ≤ L.H) : ∀ {l : List (ℕ × ℕ)} {h : ℕ}, Lst L m h l → (0 < h ↔ l ≠ [])
  | [], h, hl => by have : h = 0 := hl; simp [this]
  | (v, w) :: l, h, hl => by
    have h1 : L.HE ≤ h := hl.1
    have h2 : 32 ≤ L.HE := by unfold Lay.HE; omega
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, iff_true]; omega

/-- The scan's state in memory. -/
structure ScanR (L : Lay) (x : Input) (m₀ : Mem) (P : St × ℕ × List (ℕ × ℕ) → Prop)
    (a : St × ℕ × List (ℕ × ℕ)) (m : Mem) : Prop where
  inv : P a
  rep : Rep L a.1 m
  fix : Fixed L x m
  frm : Frm L TR m₀ m
  r30 : m 30 = a.2.1
  lst : Lst L m (m 31) a.2.2
  r11 : m 11 = if 0 < m 31 then 1 else 0

theorem scanBody_spec (hC : CtxOK C) (hA : AdjOK C G W) (hLn : L.n = C.n) (hLD : L.D = C.D)
    {hs : src < G.n} {u : Fin G.n} {K Q : ℕ} {s₀ : St} {m₀ : Mem} (hKB : K < B) (hB : L.top < B)
    {a : St × ℕ × List (ℕ × ℕ)} (h : ScanR L x m₀ (ScanP (C := C) (W := W) hs u K Q s₀) a m)
    (hc : scanCond a) :
    Runs B relaxBody m fun m' k =>
      ScanR L x m₀ (ScanP (C := C) (W := W) hs u K Q s₀) (scanStep C a) m' ∧
        a.1.time + k + 2 ≤ (scanStep C a).1.time := by
  have hstep := (ScanP.step hC hA h.inv hc).1
  obtain ⟨t, u', l⟩ := a
  obtain ⟨hP, hR, hF, hFr, h30, hl, h11⟩ := h
  replace hR : Rep L t m := hR
  replace h30 : m 30 = u' := h30
  replace hl : Lst L m (m 31) l := hl
  rcases l with _ | ⟨⟨v, w⟩, l⟩
  · exact absurd rfl hc
  obtain ⟨hu, ⟨pre, hI⟩, -⟩ := hP
  replace hu : u' = (u : ℕ) + 1 := hu
  subst hu
  replace hI : ScanInv (C := C) (W := W) hs u K Q pre t ((v, w) :: l) := hI
  have hnG : L.n = G.n := hLn.trans hA.n_eq
  have hpm : (v, w) ∈ C.adj ((u : ℕ) + 1) := by rw [hI.split]; simp
  obtain ⟨v', -, hp⟩ := hA.sound u _ hpm
  have hv : v = (v' : ℕ) + 1 := (Prod.mk.inj hp).1
  have hw : w ≤ W := hA.wmax _ _ hpm
  have hku := hI.ku
  have hH : HeapInv C.n t (hset G.n t) := by rw [hA.n_eq]; exact hI.g.heap
  have hMr : ∀ a ∈ hset G.n t, 1 ≤ a ∧ a ≤ L.n := by rw [hLn]; exact hH.range
  have hd0 : t.deg 0 ≤ L.n := hH.roots.deg0_le.trans (card_le_n hMr)
  have hm : t.hmin ≤ L.n := by
    by_cases he : hset G.n t = ∅
    · rw [hI.g.empty he]; omega
    · exact (hMr _ (hH.min (Finset.nonempty_iff_ne_empty.2 he)).1).2
  have hdg : ∀ a ∈ hset G.n t, t.deg a ≤ L.D := fun a ha => by
    have := hH.forest.deg_lt hH.range ha
    rw [hLD, hC.D_eq]; omega
  have hFM : (hset G.n t).card ≤ C.F := (card_le_n hH.range).trans (by have := hC.fuel; omega)
  have hvn : v ≤ L.n := by have := v'.2; omega
  have hun : (u : ℕ) + 1 ≤ L.n := by have := u.2; omega
  refine Runs.mono (relaxBody_run C hR hF h30 rfl hl hun hvn (by omega) hH hd0 hm
    (fun h1 => mem_hset.2 ⟨by omega, by omega, h1⟩) hMr hdg hFM hB)
    fun m' k ⟨R', X', F', a30, al, a11, ak⟩ => ?_
  exact ⟨⟨hstep, R', X', hFr.trans F', a30, al, a11⟩, ak⟩

theorem scan_run (hC : CtxOK C) (hA : AdjOK C G W) (hLn : L.n = C.n) (hLD : L.D = C.D)
    {hs : src < G.n} {u : Fin G.n} {K Q : ℕ} {s₀ : St} (hKB : K < B) (hB : L.top < B)
    (hI : ScanInv (C := C) (W := W) hs u K Q [] s₀ (C.adj ((u : ℕ) + 1)))
    (hR : Rep L s₀ m) (hF : Fixed L x m) (h30 : m 30 = (u : ℕ) + 1)
    (hl : Lst L m (m 31) (C.adj ((u : ℕ) + 1))) (h11 : m 11 = if 0 < m 31 then 1 else 0) :
    Runs B (loop 11 3 relaxBody) m fun m' k =>
      Rep L (whileF scanCond (scanStep C) C.F (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1))).1 m' ∧
        Fixed L x m' ∧ Frm L TR m m' ∧
        s₀.time + k ≤
          (whileF scanCond (scanStep C) C.F (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1))).1.time + 1 := by
  have ht := top_ge (L := L)
  have hH := hR.H32
  have h0 : ScanP (C := C) (W := W) hs u K Q s₀ (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1)) :=
    ⟨rfl, ⟨[], hI⟩, fun _ => Iff.rfl⟩
  have hstop := whileF_stops (ScanP (C := C) (W := W) hs u K Q s₀) (fun b => b.2.2.length)
    (fun b hb hc => hb.step hC hA hc) C.F _ h0 (hA.fuel _)
  refine Runs.mono (Runs.loop_refine (ScanR L x m (ScanP (C := C) (W := W) hs u K Q s₀)) scanCond
    (scanStep C) (fun a => a.1.time) (by omega) (by omega) (fun a m' hR' => ?_)
    (fun a m' hR' hc => scanBody_spec hC hA hLn hLD hKB hB hR' hc) C.F _ m
    ⟨h0, hR, hF, Frm.refl, h30, hl, h11⟩ hstop)
    fun m' k ⟨hR', hk⟩ => ⟨hR'.rep, hR'.fix, hR'.frm, hk⟩
  have hp := Lst.pos hR'.rep.H32 hR'.lst
  rw [hR'.r11, hR'.rep.one]
  by_cases h0 : 0 < m' 31
  · rw [if_pos h0]; exact ⟨fun _ => hp.1 h0, fun _ => rfl⟩
  · rw [if_neg h0]; exact ⟨fun e => by omega, fun hc => absurd (hp.2 hc) h0⟩

end Formalgo.Algorithms.ShortestPaths
