import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Machine.Eval

/-!
# Registers over the input

LLM-generated; not checked by a human.

The input starts at cell `0`, so a program first saves cells `[0, K)` to a buffer at `S`, uses
them as registers, and restores them at the end. Cell `1` holds `S`, cell `2` is scratch, and the
body reads and writes cells below `K` through the buffer.
-/

namespace Formalgo.Algorithms.ShortestPaths.LLMUnchecked

open Function

namespace Cmd

/-- Run commands in order, then set the scratch cell `2` to `0`. -/
def seqs : List Cmd → Cmd
  | [] => const 2 0
  | c :: cs => seq c (seqs cs)

/-- Save cell `j` to `S + j`, with `S` in cell `0`. -/
def saveOne (j : ℕ) : Cmd := seqs [const 2 j, add 2 0 2, store 2 j]

/-- Restore cell `j` from `S + j`, with `S` in cell `0`. -/
def restoreOne (j : ℕ) : Cmd := seqs [const 2 j, add 2 0 2, load j 2]

/-- The registers that are saved: `1` and `3, …, K - 1`. -/
def regs (K : ℕ) : List ℕ := 1 :: List.range' 3 (K - 3)

/-- Compute `S` into cell `0`, save the registers, run `body`, and restore them. -/
def harness (K : ℕ) (setS body : Cmd) : Cmd :=
  seqs [setS, seqs ((regs K).map saveOne), store 0 3, copy 1 0, body, copy 0 1,
    seqs ((regs K).reverse.map restoreOne), const 0 1]

end Cmd

open Cmd

theorem mem_regs {K j : ℕ} (hK : 3 ≤ K) : j ∈ regs K ↔ j < K ∧ j ≠ 0 ∧ j ≠ 2 := by
  simp only [regs, List.mem_cons, List.mem_range']
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
  · intro h
    by_cases h1 : j = 1
    · exact .inl h1
    · exact .inr ⟨j - 3, by omega, by omega⟩

theorem length_regs {K : ℕ} (hK : 3 ≤ K) : (regs K).length = K - 2 := by
  simp [regs]; omega

theorem nodup_regs (K : ℕ) : (regs K).Nodup := by
  simp only [regs, List.nodup_cons, List.mem_range']
  exact ⟨by omega, List.nodup_range' ..⟩

/-- A sequence of commands with the given effects. -/
theorem exec_seqs_nil {B : ℕ} {m : Mem} (hB : 2 < B) : Exec B (seqs []) m 1 (update m 2 0) :=
  .const hB (by omega)

theorem exec_saveOne {B S j : ℕ} {m : Mem} (h0 : m 0 = S) (hj2 : j ≠ 2) (hjS : j < S)
    (h3 : 3 ≤ S) (hB : S + j < B) :
    ∃ m', Exec B (saveOne j) m 4 m' ∧ m' (S + j) = m j ∧ m' 2 = 0 ∧
      ∀ a, a ≠ 2 → a ≠ S + j → m' a = m a := by
  have h2B : 2 < B := by omega
  have e := Exec.seq (B := B) (m := m) (.const (d := 2) (v := j) h2B (by omega))
    (.seq (.add (d := 2) (l := 0) (r := 2) h2B (by omega) h2B (by simp [h0]; omega))
      (.seq (.store (p := 2) (s := j) h2B (by omega)) (.const (d := 2) (v := 0) h2B (by omega))))
  refine ⟨_, e, ?_, ?_, ?_⟩
  · simp [update_apply, h0, hj2]; omega
  · simp
  · intro a ha hb; simp [h0, ha, hb, hj2]

theorem exec_restoreOne {B S j : ℕ} {m : Mem} (h0 : m 0 = S) (hj2 : j ≠ 2)
    (hjS : j < S) (h3 : 3 ≤ S) (hB : S + j < B) :
    ∃ m', Exec B (restoreOne j) m 4 m' ∧ m' j = m (S + j) ∧ m' 2 = 0 ∧
      ∀ a, a ≠ 2 → a ≠ j → m' a = m a := by
  have h2B : 2 < B := by omega
  have e := Exec.seq (B := B) (m := m) (.const (d := 2) (v := j) h2B (by omega))
    (.seq (.add (d := 2) (l := 0) (r := 2) h2B (by omega) h2B (by simp [h0]; omega))
      (.seq (.load (d := j) (p := 2) (by omega) h2B) (.const (d := 2) (v := 0) h2B (by omega))))
  refine ⟨_, e, ?_, ?_, ?_⟩
  · simp [h0, hj2, show S + j ≠ 2 by omega]
  · simp
  · intro a ha hb; simp [update_apply, h0, ha, hb]

theorem exec_saveAll {B S : ℕ} (js : List ℕ) (hnd : js.Nodup) {m : Mem} (h0 : m 0 = S)
    (hjs : ∀ j ∈ js, j ≠ 0 ∧ j ≠ 2 ∧ j < S) (h3 : 3 ≤ S) (hB : ∀ j ∈ js, S + j < B)
    (h2B : 2 < B) :
    ∃ m', Exec B (seqs (js.map saveOne)) m (4 * js.length + 1) m' ∧ m' 0 = S ∧ m' 2 = 0 ∧
      (∀ j ∈ js, m' (S + j) = m j) ∧
      ∀ a, a ≠ 2 → (∀ j ∈ js, a ≠ S + j) → m' a = m a := by
  induction js generalizing m with
  | nil =>
    exact ⟨_, exec_seqs_nil h2B, by simp [h0], by simp, by simp,
      fun a ha _ => by simp [ha]⟩
  | cons j js ih =>
    obtain ⟨hj0, hj2, hjS⟩ := hjs j (by simp)
    obtain ⟨m₁, h₁, hm₁j, hm₁2, hm₁⟩ := exec_saveOne (B := B) h0 hj2 hjS h3 (hB j (by simp))
    have h0₁ : m₁ 0 = S := by rw [hm₁ 0 (by omega) (by omega), h0]
    obtain ⟨hjnot, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨m₂, h₂, h0₂, h2₂, hbuf, hrest⟩ := ih hnd' h0₁ (fun j hj => hjs j (by simp [hj]))
      (fun j hj => hB j (by simp [hj]))
    refine ⟨m₂, ?_, h0₂, h2₂, ?_, ?_⟩
    · have := Exec.seq h₁ h₂
      simpa [List.map_cons, seqs, show 4 + (4 * js.length + 1) = 4 * (js.length + 1) + 1 by omega]
        using this
    · intro j' hj'
      rcases List.mem_cons.1 hj' with rfl | hj'
      · rw [hrest _ (by omega) (fun j'' hj'' h => hjnot (by
          have : j' = j'' := by omega
          exact this ▸ hj'')), hm₁j]
      · have := hjs j' (by simp [hj'])
        rw [hbuf j' hj', hm₁ j' this.2.1 (by omega)]
    · intro a ha hne
      rw [hrest a ha (fun j' hj' => hne j' (by simp [hj'])),
        hm₁ a ha (hne j (by simp))]

theorem exec_restoreAll {B S : ℕ} (js : List ℕ) {m : Mem} (h0 : m 0 = S)
    (hjs : ∀ j ∈ js, j ≠ 0 ∧ j ≠ 2 ∧ j < S) (h3 : 3 ≤ S) (hB : ∀ j ∈ js, S + j < B)
    (h2B : 2 < B) :
    ∃ m', Exec B (seqs (js.map restoreOne)) m (4 * js.length + 1) m' ∧ m' 0 = S ∧ m' 2 = 0 ∧
      (∀ j ∈ js, m' j = m (S + j)) ∧
      ∀ a, a ≠ 2 → a ∉ js → m' a = m a := by
  induction js generalizing m with
  | nil =>
    exact ⟨_, exec_seqs_nil h2B, by simp [h0], by simp, by simp,
      fun a ha _ => by simp [ha]⟩
  | cons j js ih =>
    obtain ⟨hj0, hj2, hjS⟩ := hjs j (by simp)
    obtain ⟨m₁, h₁, hm₁j, hm₁2, hm₁⟩ := exec_restoreOne (B := B) h0 hj2 hjS h3 (hB j (by simp))
    have h0₁ : m₁ 0 = S := by rw [hm₁ 0 (by omega) (by omega), h0]
    obtain ⟨m₂, h₂, h0₂, h2₂, hreg, hrest⟩ := ih h0₁ (fun j hj => hjs j (by simp [hj]))
      (fun j hj => hB j (by simp [hj]))
    refine ⟨m₂, ?_, h0₂, h2₂, ?_, ?_⟩
    · have := Exec.seq h₁ h₂
      simpa [List.map_cons, seqs, show 4 + (4 * js.length + 1) = 4 * (js.length + 1) + 1 by omega]
        using this
    · intro j' hj'
      by_cases hin : j' ∈ js
      · rw [hreg j' hin, hm₁ _ (by omega) (by have := (hjs j' (by simp [hin])).2.2; omega)]
      · rcases List.mem_cons.1 hj' with rfl | hj'
        · rw [hrest j' (by omega) hin, hm₁j]
        · exact absurd hj' hin
    · intro a ha hne
      rw [hrest a ha (fun h => hne (by simp [h])), hm₁ a ha (fun h => hne (by simp [h]))]

/-- The harness: if the body leaves the final values in its cells from `K` and in the buffer, the
program leaves them in cells `[0, N)`. -/
theorem exec_harness {B K S N : ℕ} {setS body : Cmd} {m₀ m₁ : Mem} {k₀ : ℕ} (final : Mem)
    (T : ℕ) (hK : 4 ≤ K) (hKS : K ≤ S) (hNS : N ≤ S) (hB : S + K < B)
    (hset : Exec B setS m₀ k₀ m₁) (hm₁0 : m₁ 0 = S) (hm₁ : ∀ a, a ≠ 0 → a ≠ 2 → m₁ a = m₀ a)
    (h00 : m₀ 0 = 1) (h02 : m₀ 2 = 0) (h03 : m₀ 3 = 1) (hblank : ∀ a, S ≤ a → m₀ a = 0)
    (hf0 : final 0 = 1) (hf2 : final 2 = 0)
    (hbody : ∀ m, m 1 = S → (∀ j < K, m (S + j) = m₀ j) →
      (∀ a, 3 ≤ a → a < S ∨ S + K ≤ a → m a = m₀ a) →
      ∃ m' k, Exec B body m k m' ∧ k ≤ T ∧ m' 1 = S ∧
        (∀ j < K, j ≠ 0 → j ≠ 2 → m' (S + j) = final j) ∧
        ∀ a, K ≤ a → a < N → m' a = final a) :
    ∃ m' k, Exec B (harness K setS body) m₀ k m' ∧ k ≤ k₀ + T + 8 * K ∧
      ∀ i < N, m' i = final i := by
  have h3K : 3 ≤ K := by omega
  have h2B : 2 < B := by omega
  have hregs : ∀ j ∈ regs K, j ≠ 0 ∧ j ≠ 2 ∧ j < S := fun j hj => by
    have := (mem_regs h3K).1 hj; omega
  have hregsB : ∀ j ∈ regs K, S + j < B := fun j hj => by
    have := (mem_regs h3K).1 hj; omega
  -- Save.
  obtain ⟨m₂, hsave, h₂0, h₂2, h₂buf, h₂⟩ :=
    exec_saveAll (B := B) (regs K) (nodup_regs K) hm₁0 hregs (by omega) hregsB h2B
  have h₂3 : m₂ 3 = 1 := by
    rw [h₂ 3 (by omega) (fun j hj => by have := hregs j hj; omega), hm₁ 3 (by omega) (by omega),
      h03]
  -- `store 0 3`, then `copy 1 0`.
  have e₃ : Exec B (.store 0 3) m₂ 1 (update m₂ S 1) := by
    have := Exec.store (B := B) (m := m₂) (p := 0) (s := 3) (by omega) (by omega)
    rwa [h₂0, h₂3] at this
  set m₃ := update m₂ S 1
  have e₄ : Exec B (.copy 1 0) m₃ 1 (update m₃ 1 S) := by
    have := Exec.copy (B := B) (m := m₃) (d := 1) (s := 0) (by omega) (by omega)
    rwa [show m₃ 0 = S by simp [m₃, update_apply, h₂0]; omega] at this
  set m₄ := update m₃ 1 S
  -- The body.
  have hm₄buf : ∀ j < K, m₄ (S + j) = m₀ j := by
    intro j hj
    simp only [m₄, m₃, update_apply]
    rw [if_neg (by omega)]
    by_cases hj0 : j = 0
    · subst hj0; simp [h00]
    · rw [if_neg (by omega)]
      by_cases hj2 : j = 2
      · subst hj2
        rw [h₂ _ (by omega) (fun j hj => by have := hregs j hj; omega),
          hm₁ _ (by omega) (by omega), hblank _ (by omega), h02]
      · rw [h₂buf j ((mem_regs h3K).2 ⟨hj, hj0, hj2⟩), hm₁ j hj0 hj2]
  have hm₄rest : ∀ a, 3 ≤ a → a < S ∨ S + K ≤ a → m₄ a = m₀ a := by
    intro a ha hS
    simp only [m₄, m₃, update_apply]
    rw [if_neg (by omega), if_neg (by omega),
      h₂ a (by omega) (fun j hj => by have := (mem_regs h3K).1 hj; omega),
      hm₁ a (by omega) (by omega)]
  obtain ⟨m₅, k, hbe, hk, h₅1, h₅buf, h₅⟩ := hbody m₄ (by simp [m₄]) hm₄buf hm₄rest
  -- `copy 0 1`, then restore.
  have e₆ : Exec B (.copy 0 1) m₅ 1 (update m₅ 0 S) := by
    have := Exec.copy (B := B) (m := m₅) (d := 0) (s := 1) (by omega) (by omega)
    rwa [h₅1] at this
  have hregsr : ∀ j ∈ (regs K).reverse, j ≠ 0 ∧ j ≠ 2 ∧ j < S := fun j hj =>
    hregs j (List.mem_reverse.1 hj)
  obtain ⟨m₇, hrest, h₇0, h₇2, h₇reg, h₇⟩ :=
    exec_restoreAll (B := B) (regs K).reverse (m := update m₅ 0 S) (by simp) hregsr (by omega)
      (fun j hj => hregsB j (List.mem_reverse.1 hj)) h2B
  have e₈ : Exec B (.const 0 1) m₇ 1 (update m₇ 0 1) := .const (by omega) (by omega)
  have e₉ := exec_seqs_nil (B := B) (m := update m₇ 0 1) h2B
  refine ⟨_, _, .seq hset (.seq hsave (.seq e₃ (.seq e₄ (.seq hbe (.seq e₆ (.seq hrest
    (.seq e₈ e₉))))))), ?_, ?_⟩
  · simp only [List.length_reverse, length_regs h3K]
    omega
  · intro i hi
    simp only [update_apply]
    by_cases hi2 : i = 2
    · subst hi2; simp [hf2]
    · rw [if_neg hi2]
      by_cases hi0 : i = 0
      · subst hi0; simp [hf0]
      · rw [if_neg hi0]
        by_cases hiK : i < K
        · rw [h₇reg i (List.mem_reverse.2 ((mem_regs h3K).2 ⟨hiK, hi0, hi2⟩)), update_apply,
            if_neg (by omega), h₅buf i hiK hi0 hi2]
        · rw [h₇ i hi2 (fun h => by
            have := (mem_regs h3K).1 (List.mem_reverse.1 h); omega), update_apply,
            if_neg hi0, h₅ i (by omega) hi]

end Formalgo.Algorithms.ShortestPaths.LLMUnchecked
