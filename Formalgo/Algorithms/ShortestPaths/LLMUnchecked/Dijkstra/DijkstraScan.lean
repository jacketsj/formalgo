import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.DijkstraRelax

/-!
# Dijkstra's algorithm on the model: the scan of a settled vertex

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [CanonicallyOrderedAdd R]
  {C : CtxW R} {G : WGraphW R} {src : ℕ} {W : R}

omit [AddCommMonoid R] [CanonicallyOrderedAdd R] in
theorem decKey_stat (C : CtxW R) (v : ℕ) (nk : R) (t : StW R) :
    (decKey C v nk t).stat = t.stat := by
  have hc : ∀ (b : StW R × ℕ), b.1.stat = t.stat →
      (whileF cascCond cascStep C.F b).1.stat = t.stat := fun b hb =>
    whileF_induct (c := cascCond) (f := cascStep) (fun b : StW R × ℕ => b.1.stat = t.stat)
      (fun b hb _ => hb) C.F b hb
  unfold decKey
  dsimp only
  split_ifs
  all_goals first
    | rfl
    | exact updMinKey_of (fun t' => t'.stat = t.stat) (fun _ => rfl) rfl
    | exact updMinKey_of (fun t' => t'.stat = t.stat) (fun _ => hc _ rfl) (hc _ rfl)

omit [CanonicallyOrderedAdd R] in
theorem relax_stat2 (u v : ℕ) (w : R) (t : StW R) (x : ℕ) :
    (relax C u v w t).stat x = 2 ↔ t.stat x = 2 := by
  unfold relax
  dsimp only
  split_ifs with h0 h1 hlt
  · have : (updMin v (attach v 0 (setStat v 1 (setKey v (t.key u + w) t)))).stat =
        update t.stat v 1 := updMin_of (fun t' => t'.stat = update t.stat v 1) (fun _ => rfl) rfl
    rw [this]
    rcases eq_or_ne x v with rfl | hx
    · rw [update_self, h0]; omega
    · rw [update_of_ne hx]
  · rw [decKey_stat C v (t.key u + w) t]
  · exact Iff.rfl
  · exact Iff.rfl

/-- The invariant of the scan loop. -/
def ScanP (hs : src < G.n) (u : Fin G.n) (K : R) (Q : ℕ) (s₀ : StW R)
    (a : StW R × ℕ × List (ℕ × R)) : Prop :=
  a.2.1 = (u : ℕ) + 1 ∧ (∃ pre, ScanInv (C := C) (W := W) hs u K Q pre a.1 a.2.2) ∧
    ∀ x, a.1.stat x = 2 ↔ s₀.stat x = 2

theorem ScanP.step (hC : CtxOK C) (hA : AdjOK C G W) {hs : src < G.n} {u : Fin G.n}
    {K : R} {Q : ℕ} {s₀ : StW R} {a : StW R × ℕ × List (ℕ × R)}
    (h : ScanP (C := C) (W := W) hs u K Q s₀ a) (hc : scanCond a) :
    ScanP (C := C) (W := W) hs u K Q s₀ (scanStep C a) ∧
      (scanStep C a).2.2.length < a.2.2.length := by
  obtain ⟨t, u', l⟩ := a
  obtain ⟨hu, ⟨pre, hI⟩, hst⟩ := h
  simp only [scanCond] at hc hu hst hI
  subst hu
  rcases l with _ | ⟨p, l⟩
  · exact absurd rfl hc
  have hpm : p ∈ C.adj ((u : ℕ) + 1) := by rw [hI.split]; simp
  obtain ⟨v', hadj, rfl⟩ := hA.sound u p hpm
  have hQ : 50 ≤ Q := by have := hI.cost; simp only [List.length_cons] at this; omega
  have e : scanStep C (t, (u : ℕ) + 1, ((v' : ℕ) + 1, G.weight s(u, v')) :: l) =
      (tick 50 (relax C ((u : ℕ) + 1) ((v' : ℕ) + 1) (G.weight s(u, v')) t), (u : ℕ) + 1, l) := rfl
  rw [e]
  refine ⟨⟨rfl, ⟨pre ++ [((v' : ℕ) + 1, G.weight s(u, v'))], ?_⟩, fun x => ?_⟩, by simp⟩
  · unfold relax; dsimp only
    by_cases h0 : t.stat ((v' : ℕ) + 1) = 0
    · rw [if_pos h0]; exact (relax_new hC hA hI hadj h0).tick hQ
    · rw [if_neg h0]
      by_cases h1 : t.stat ((v' : ℕ) + 1) = 1
      · rw [if_pos h1]
        by_cases hlt : t.key ((u : ℕ) + 1) + G.weight s(u, v') < t.key ((v' : ℕ) + 1)
        · rw [if_pos hlt]; exact (relax_dec hC hA hI hadj h1 hlt).tick hQ
        · rw [if_neg hlt]
          exact (relax_keep hI ⟨by omega, fun _ => not_lt.1 hlt⟩).tick hQ
      · rw [if_neg h1]
        exact (relax_keep hI ⟨h0, fun h => absurd h h1⟩).tick hQ
  · change (relax C _ _ _ t).stat x = 2 ↔ _
    rw [relax_stat2]; exact hst x

theorem scan_loop (hC : CtxOK C) (hA : AdjOK C G W) {hs : src < G.n} {u : Fin G.n} {K : R}
    {Q : ℕ} {s₀ : StW R} (h : ScanInv (C := C) (W := W) hs u K Q [] s₀ (C.adj ((u : ℕ) + 1))) :
    ScanInv (C := C) (W := W) hs u K Q (C.adj ((u : ℕ) + 1))
        (whileF scanCond (scanStep C) C.F (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1))).1 [] ∧
      ∀ x, (whileF scanCond (scanStep C) C.F (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1))).1.stat x = 2 ↔
        s₀.stat x = 2 := by
  have h0 : ScanP (C := C) (W := W) hs u K Q s₀ (s₀, (u : ℕ) + 1, C.adj ((u : ℕ) + 1)) :=
    ⟨rfl, ⟨[], h⟩, fun _ => Iff.rfl⟩
  obtain ⟨_, ⟨pre, hI⟩, hst⟩ := whileF_induct (ScanP (C := C) (W := W) hs u K Q s₀)
    (fun b hb hc => (hb.step hC hA hc).1) C.F _ h0
  have hstop := whileF_stops (ScanP (C := C) (W := W) hs u K Q s₀) (fun b => b.2.2.length)
    (fun b hb hc => hb.step hC hA hc) C.F _ h0 (hA.fuel _)
  simp only [scanCond, not_not] at hstop
  rw [hstop] at hI
  have hpre : pre = C.adj ((u : ℕ) + 1) := by have := hI.split; simpa using this.symm
  subst hpre
  exact ⟨hI, hst⟩

omit [CanonicallyOrderedAdd R] in
/-- After the scan, every settled vertex has relaxed its edges. -/
theorem ScanInv.relaxed (hA : AdjOK C G W) {hs : src < G.n} {u : Fin G.n} {K : R} {Q : ℕ}
    {t : StW R}
    (h : ScanInv (C := C) (W := W) hs u K Q (C.adj ((u : ℕ) + 1)) t []) : Relaxed G 0 t := by
  intro a b _ ha hab
  by_cases hau : a = u
  · subst hau
    exact h.pre _ (hA.complete a b hab)
  · exact h.rel a b (by intro h'; exact hau (Fin.ext (by omega))) ha hab

end Formalgo.Algorithms.ShortestPaths
