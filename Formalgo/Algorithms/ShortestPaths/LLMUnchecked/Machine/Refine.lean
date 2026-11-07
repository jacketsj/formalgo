import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.Prog

/-!
# Loops that follow a model

LLM-generated; not checked by a human.

A model loop runs `f` while `c` holds, for at most `N` rounds. A command loop follows it when its
body follows `f` under a relation `R`, with the model's clock `T` paying for the steps.
-/

namespace Formalgo.LLMUnchecked

/-- Run `f` while `c` holds, at most `N` times. -/
def whileF {α : Type*} (c : α → Prop) [DecidablePred c] (f : α → α) : ℕ → α → α
  | 0, a => a
  | N + 1, a => if c a then whileF c f N (f a) else a

theorem whileF_succ {α : Type*} {c : α → Prop} [DecidablePred c] {f : α → α} {N : ℕ} {a : α}
    (h : c a) : whileF c f (N + 1) a = whileF c f N (f a) := by
  simp [whileF, h]

theorem whileF_stop {α : Type*} {c : α → Prop} [DecidablePred c] {f : α → α} {N : ℕ} {a : α}
    (h : ¬c a) : whileF c f N a = a := by
  cases N <;> simp [whileF, h]

/-- Once the loop has stopped, more fuel changes nothing. -/
theorem whileF_mono {α : Type*} {c : α → Prop} [DecidablePred c] {f : α → α} :
    ∀ {N N' : ℕ} {a : α}, N ≤ N' → ¬c (whileF c f N a) → whileF c f N' a = whileF c f N a
  | 0, N', a, _, h => whileF_stop h
  | N + 1, 0, a, hle, _ => absurd hle (by omega)
  | N + 1, N' + 1, a, hle, h => by
    by_cases hc : c a
    · rw [whileF_succ hc] at h ⊢; rw [whileF_succ hc]; exact whileF_mono (by omega) h
    · rw [whileF_stop hc, whileF_stop hc]

/-- An invariant of each round holds after the loop. -/
theorem whileF_induct {α : Type*} {c : α → Prop} [DecidablePred c] {f : α → α}
    (P : α → Prop) (h : ∀ a, P a → c a → P (f a)) : ∀ N a, P a → P (whileF c f N a)
  | 0, a, ha => ha
  | N + 1, a, ha => by
    by_cases hc : c a
    · rw [whileF_succ hc]; exact whileF_induct P h N _ (h a ha hc)
    · rw [whileF_stop hc]; exact ha

/-- The loop stops within `N` rounds if a measure falls each round. -/
theorem whileF_stops {α : Type*} {c : α → Prop} [DecidablePred c] {f : α → α}
    (P : α → Prop) (μ : α → ℕ) (h : ∀ a, P a → c a → P (f a) ∧ μ (f a) < μ a) :
    ∀ N a, P a → μ a ≤ N → ¬c (whileF c f N a)
  | 0, a, ha, hμ => by
    intro hc; have := (h a ha hc).2; omega
  | N + 1, a, ha, hμ => by
    by_cases hc : c a
    · rw [whileF_succ hc]
      exact whileF_stops P μ h N _ (h a ha hc).1 (by have := (h a ha hc).2; omega)
    · rw [whileF_stop hc]; exact hc

namespace Runs

/-- A command loop follows a model loop. -/
theorem loop_refine {B l r : ℕ} {body : Cmd} {α : Type*} (R : α → Mem → Prop) (c : α → Prop)
    [DecidablePred c] (f : α → α) (T : α → ℕ) (hl : l < B) (hr : r < B)
    (hcond : ∀ a m, R a m → (m l = m r ↔ c a))
    (hbody : ∀ a m, R a m → c a → Runs B body m fun m' k => R (f a) m' ∧ T a + k + 2 ≤ T (f a)) :
    ∀ (N : ℕ) (a : α) (m : Mem), R a m → ¬c (whileF c f N a) →
      Runs B (.loop l r body) m fun m' k => R (whileF c f N a) m' ∧ T a + k ≤ T (whileF c f N a) + 1
  | 0, a, m, hR, hN => by
    have hne : m l ≠ m r := fun h => hN ((hcond a m hR).1 h)
    exact ⟨m, 1, .loopFalse hl hr hne, hR, le_refl _⟩
  | N + 1, a, m, hR, hN => by
    by_cases hc : c a
    · rw [whileF_succ hc] at hN ⊢
      obtain ⟨m₁, k₁, e₁, hR₁, hT₁⟩ := hbody a m hR hc
      obtain ⟨m₂, k₂, e₂, hR₂, hT₂⟩ := loop_refine R c f T hl hr hcond hbody N (f a) m₁ hR₁ hN
      exact ⟨m₂, k₁ + k₂ + 2, .loopTrue hl hr ((hcond a m hR).2 hc) e₁ e₂, hR₂, by omega⟩
    · rw [whileF_stop hc] at hN ⊢
      have hne : m l ≠ m r := fun h => hc ((hcond a m hR).1 h)
      exact ⟨m, 1, .loopFalse hl hr hne, hR, le_refl _⟩

end Runs

end Formalgo.LLMUnchecked
