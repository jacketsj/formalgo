import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunOutput

/-!
# Running the setup

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {m : Mem} {B : ℕ}

/-- The memory before the heap starts: the registers of `Rep`, and an empty heap. -/
structure Pre (L : Lay) (m : Mem) : Prop where
  H32 : 32 ≤ L.H
  base : ∀ k < 10, m (breg k) = L.H + k * L.R
  n : m 27 = L.n
  D : m 28 = L.D
  one : m 3 = 1
  zero : m 8 = 0
  three : m 16 = 3
  dyn : ∀ a, L.Dyn a → m a = 0

/-- The bit length of `n`, by doubling. -/
theorem logLoop_spec {n : ℕ} (h27 : m 27 = n) (h8 : m 8 = 0) (h3 : m 3 = 1) (h12 : m 12 = 1)
    (h13 : m 13 = 0) (h14 : m 14 = if n < 1 then 1 else 0) (hB : 2 * n + 40 < B) :
    Runs B (loop 14 8 logBody) m fun m' k => m' 13 = Nat.size n ∧
      (∀ a, a ≠ 2 → a ≠ 12 → a ≠ 13 → a ≠ 14 → m' a = m a) ∧ k ≤ 6 * Nat.size n + 1 := by
  let P : Mem → ℕ → Prop := fun m' c => ∃ i, i ≤ Nat.size n ∧ m' 12 = 2 ^ i ∧ m' 13 = i ∧
    m' 14 = (if n < 2 ^ i then 1 else 0) ∧
    (∀ a, a ≠ 2 → a ≠ 12 → a ≠ 13 → a ≠ 14 → m' a = m a) ∧ c ≤ 6 * i
  refine Runs.loop P (fun m' => Nat.size n + 1 - m' 13) (by omega) (by omega) ?_ ?_
    ⟨0, Nat.zero_le _, by simpa using h12, h13, by simpa using h14, fun _ _ _ _ _ => rfl, by omega⟩
  · rintro m' c ⟨i, hi, e12, e13, e14, hf, hc⟩ heq
    have r8 : m' 8 = 0 := by rw [hf 8 (by omega) (by omega) (by omega) (by omega), h8]
    have r3 : m' 3 = 1 := by rw [hf 3 (by omega) (by omega) (by omega) (by omega), h3]
    have r27 : m' 27 = n := by rw [hf 27 (by omega) (by omega) (by omega) (by omega), h27]
    have hge : 2 ^ i ≤ n := by
      rw [e14, r8] at heq
      by_contra hn; simp [show n < 2 ^ i by omega] at heq
    have hlt : i < Nat.size n := Nat.lt_size.2 hge
    have hi2 : i < 2 ^ i := Nat.lt_two_pow_self
    unfold logBody
    refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
      (by rw [e12]; omega) fun m₁ g₁ f₁ => ?_)
    refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
      (by rw [f₁ 13 (by omega), f₁ 3 (by omega), e13, r3]; omega) fun m₂ g₂ f₂ => ?_)
    refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
    refine Runs.seqs_nilR (by omega) fun m₄ g₄ f₄ => ?_
    have v12 : m₄ 12 = 2 ^ (i + 1) := by
      rw [f₄ 12 (by omega), f₃ 12 (by omega), f₂ 12 (by omega), g₁, e12, pow_succ]; omega
    have v13 : m₄ 13 = i + 1 := by
      rw [f₄ 13 (by omega), f₃ 13 (by omega), g₂, f₁ 13 (by omega), f₁ 3 (by omega), e13, r3]
    have v14 : m₄ 14 = if n < 2 ^ (i + 1) then 1 else 0 := by
      rw [f₄ 14 (by omega), g₃, f₂ 27 (by omega), f₁ 27 (by omega), r27, f₂ 12 (by omega), g₁, e12,
        pow_succ, show 2 ^ i * 2 = 2 ^ i + 2 ^ i by omega]
    refine ⟨⟨i + 1, by omega, v12, v13, v14, fun a h2 h12' h13' h14' => ?_, by omega⟩, ?_⟩
    · rw [f₄ a h2, f₃ a h14', f₂ a h13', f₁ a h12', hf a h2 h12' h13' h14']
    · rw [v13, e13]; omega
  · rintro m' c ⟨i, hi, e12, e13, e14, hf, hc⟩ heq
    have r8 : m' 8 = 0 := by rw [hf 8 (by omega) (by omega) (by omega) (by omega), h8]
    have hlt : n < 2 ^ i := by
      rw [e14, r8] at heq
      by_contra hn; exact heq (by rw [if_neg hn])
    have hsz : Nat.size n ≤ i := Nat.size_le.2 hlt
    exact ⟨by omega, hf, by omega⟩

/-- One more base. -/
theorem addBase {d l j j' : ℕ} (hj' : j' = j + 1) (hd : d < 32) (hl : l < 32) (hj : j ≤ 9)
    (h12 : m 12 = L.R) (hb : m l = L.H + j * L.R) (hd12 : d ≠ 12) (H32 : 32 ≤ L.H)
    (hB : L.top < B) {Q : Mem → ℕ → Prop}
    (hQ : ∀ m', m' d = L.H + j' * L.R → m' 12 = L.R → (∀ a, a ≠ d → m' a = m a) → Q m' 1) :
    Runs B (add d l 12) m Q := by
  subst hj'
  have ht := top_ge (L := L)
  have hjR : (j + 1) * L.R ≤ 10 * L.R := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at hjR
  refine Runs.addR (by omega) (by omega) (by omega) (by rw [hb, h12]; omega) fun m' g f => ?_
  refine hQ m' ?_ (by rw [f 12 hd12.symm, h12]) f
  rw [g, hb, h12, Nat.succ_mul]; omega

/-- The bases of the arrays. -/
theorem bases_spec {A ℓ : ℕ} (hH : L.H = A + ℓ) (H32 : 32 ≤ L.H) (h9 : m 9 = A) (h4 : m 4 = ℓ)
    (h12 : m 12 = L.R) (hB : L.top < B) :
    Runs B (seqs [add 18 9 4, add 19 18 12, add 20 19 12, add 21 20 12, add 22 21 12, add 23 22 12,
        add 24 23 12, add 25 24 12, add 26 25 12, add 10 26 12, add 13 10 12]) m fun m' k =>
      (∀ k < 10, m' (breg k) = L.H + k * L.R) ∧ m' 13 = L.HE ∧
      (∀ a, a ≠ 2 → a ≠ 10 → a ≠ 13 → ¬(18 ≤ a ∧ a ≤ 26) → m' a = m a) ∧ k ≤ 12 := by
  have ht := top_ge (L := L)
  have h32 : 32 < B := by omega
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [h9, h4]; omega) fun m₁ g₁ f₁ => ?_)
  rw [h9, h4, ← hH] at g₁
  have r₁ : m₁ 12 = L.R := by rw [f₁ 12 (by decide), h12]
  clear h12 h9 h4 hH ht
  refine Runs.seqs_cons (addBase (j := 0) (j' := 1) rfl (by decide) (by decide) (by decide) r₁ (by rw [g₁]; omega)
    (by decide) H32 hB fun m₂ g₂ r₂ f₂ => ?_)
  refine Runs.seqs_cons (addBase (j := 1) (j' := 2) rfl (by decide) (by decide) (by decide) r₂ g₂
    (by decide) H32 hB fun m₃ g₃ r₃ f₃ => ?_)
  refine Runs.seqs_cons (addBase (j := 2) (j' := 3) rfl (by decide) (by decide) (by decide) r₃ g₃
    (by decide) H32 hB fun m₄ g₄ r₄ f₄ => ?_)
  refine Runs.seqs_cons (addBase (j := 3) (j' := 4) rfl (by decide) (by decide) (by decide) r₄ g₄
    (by decide) H32 hB fun m₅ g₅ r₅ f₅ => ?_)
  refine Runs.seqs_cons (addBase (j := 4) (j' := 5) rfl (by decide) (by decide) (by decide) r₅ g₅
    (by decide) H32 hB fun m₆ g₆ r₆ f₆ => ?_)
  refine Runs.seqs_cons (addBase (j := 5) (j' := 6) rfl (by decide) (by decide) (by decide) r₆ g₆
    (by decide) H32 hB fun m₇ g₇ r₇ f₇ => ?_)
  refine Runs.seqs_cons (addBase (j := 6) (j' := 7) rfl (by decide) (by decide) (by decide) r₇ g₇
    (by decide) H32 hB fun m₈ g₈ r₈ f₈ => ?_)
  refine Runs.seqs_cons (addBase (j := 7) (j' := 8) rfl (by decide) (by decide) (by decide) r₈ g₈
    (by decide) H32 hB fun m₉ g₉ r₉ f₉ => ?_)
  refine Runs.seqs_cons (addBase (j := 8) (j' := 9) rfl (by decide) (by decide) (by decide) r₉ g₉
    (by decide) H32 hB fun m₁₀ g₁₀ r₁₀ f₁₀ => ?_)
  refine Runs.seqs_cons (addBase (j := 9) (j' := 10) rfl (by decide) (by decide) (by decide) r₁₀ g₁₀
    (by decide) H32 hB fun m₁₁ g₁₁ r₁₁ f₁₁ => ?_)
  refine Runs.seqs_nilR (by omega) fun m₁₂ g₁₂ f₁₂ => ?_
  have c₁ : ∀ a, a ≠ 2 → a ≠ 13 → a ≠ 10 → a ≠ 26 → a ≠ 25 → a ≠ 24 → a ≠ 23 → a ≠ 22 → a ≠ 21 →
      a ≠ 20 → a ≠ 19 → m₁₂ a = m₁ a := fun a a2 a13 a10 a26 a25 a24 a23 a22 a21 a20 a19 => by
    rw [f₁₂ a a2, f₁₁ a a13, f₁₀ a a10, f₉ a a26, f₈ a a25, f₇ a a24, f₆ a a23, f₅ a a22, f₄ a a21,
      f₃ a a20, f₂ a a19]
  have b9 : m₁₂ 10 = L.H + 9 * L.R := by rw [f₁₂ 10 (by decide), f₁₁ 10 (by decide), g₁₀]
  have b8 : m₁₂ 26 = L.H + 8 * L.R := by
    rw [f₁₂ 26 (by decide), f₁₁ 26 (by decide), f₁₀ 26 (by decide), g₉]
  have b7 : m₁₂ 25 = L.H + 7 * L.R := by
    rw [f₁₂ 25 (by decide), f₁₁ 25 (by decide), f₁₀ 25 (by decide), f₉ 25 (by decide), g₈]
  have b6 : m₁₂ 24 = L.H + 6 * L.R := by
    rw [f₁₂ 24 (by decide), f₁₁ 24 (by decide), f₁₀ 24 (by decide), f₉ 24 (by decide),
      f₈ 24 (by decide), g₇]
  have b5 : m₁₂ 23 = L.H + 5 * L.R := by
    rw [f₁₂ 23 (by decide), f₁₁ 23 (by decide), f₁₀ 23 (by decide), f₉ 23 (by decide),
      f₈ 23 (by decide), f₇ 23 (by decide), g₆]
  have b4 : m₁₂ 22 = L.H + 4 * L.R := by
    rw [f₁₂ 22 (by decide), f₁₁ 22 (by decide), f₁₀ 22 (by decide), f₉ 22 (by decide),
      f₈ 22 (by decide), f₇ 22 (by decide), f₆ 22 (by decide), g₅]
  have b3 : m₁₂ 21 = L.H + 3 * L.R := by
    rw [f₁₂ 21 (by decide), f₁₁ 21 (by decide), f₁₀ 21 (by decide), f₉ 21 (by decide),
      f₈ 21 (by decide), f₇ 21 (by decide), f₆ 21 (by decide), f₅ 21 (by decide), g₄]
  have b2 : m₁₂ 20 = L.H + 2 * L.R := by
    rw [f₁₂ 20 (by decide), f₁₁ 20 (by decide), f₁₀ 20 (by decide), f₉ 20 (by decide),
      f₈ 20 (by decide), f₇ 20 (by decide), f₆ 20 (by decide), f₅ 20 (by decide), f₄ 20 (by decide),
      g₃]
  have b1 : m₁₂ 19 = L.H + 1 * L.R := by
    rw [f₁₂ 19 (by decide), f₁₁ 19 (by decide), f₁₀ 19 (by decide), f₉ 19 (by decide),
      f₈ 19 (by decide), f₇ 19 (by decide), f₆ 19 (by decide), f₅ 19 (by decide), f₄ 19 (by decide),
      f₃ 19 (by decide), g₂]
  have b0 : m₁₂ 18 = L.H + 0 * L.R := by
    rw [c₁ 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), g₁, Nat.zero_mul, Nat.add_zero]
  refine ⟨fun k hk => ?_, ?_, fun a a2 a10 a13 hr => ?_, by decide⟩
  · match k, hk with
    | 0, _ => exact b0
    | 1, _ => exact b1
    | 2, _ => exact b2
    | 3, _ => exact b3
    | 4, _ => exact b4
    | 5, _ => exact b5
    | 6, _ => exact b6
    | 7, _ => exact b7
    | 8, _ => exact b8
    | 9, _ => exact b9
    | n + 10, h => exact absurd h (by omega)
  · rw [f₁₂ 13 (by decide), g₁₁]; rfl
  · have hne : ∀ b, 18 ≤ b → b ≤ 26 → a ≠ b := fun b h1 h2 e => hr ⟨e ▸ h1, e ▸ h2⟩
    rw [c₁ a a2 a13 a10 (hne 26 (by decide) (by decide)) (hne 25 (by decide) (by decide))
      (hne 24 (by decide) (by decide)) (hne 23 (by decide) (by decide))
      (hne 22 (by decide) (by decide)) (hne 21 (by decide) (by decide))
      (hne 20 (by decide) (by decide)) (hne 19 (by decide) (by decide)),
      f₁ a (hne 18 (by decide) (by decide))]

/-- The registers `setup` uses. -/
def TS (a : ℕ) : Prop := a = 2 ∨ (10 ≤ a ∧ a ≤ 14) ∨ (18 ≤ a ∧ a ≤ 28)

theorem setup_run {n E ℓ A : ℕ} (hLn : L.n = n) (hLD : L.D = 2 * Nat.size n) (hH : L.H = A + ℓ)
    (hA : 32 ≤ A) (h4 : m 4 = ℓ) (h8 : m 8 = 0) (h9 : m 9 = A) (h16 : m 16 = 3) (h3 : m 3 = 1)
    (h0 : m A = n) (h1 : m (A + 1) = E) (hz : ∀ a, A + ℓ ≤ a → m a = 0) (hB : L.top < B) :
    Runs B setup m fun m' k => Pre L m' ∧ m' 11 = E ∧ m' 13 = L.HE ∧
      (∀ a, 32 ≤ a → m' a = m a) ∧ (∀ a, a < 32 → ¬TS a → m' a = m a) ∧
      k ≤ 6 * Nat.size n + 30 := by
  have ht := top_ge (L := L)
  have hRn : L.R = L.n + L.D + 3 := rfl
  have hHE : L.HE = L.H + 10 * L.R := rfl
  have hlR : L.n + L.D + 3 = L.R := rfl
  unfold setup
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₁ g₁ f₁ => ?_)
  rw [h9, h0] at g₁
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [f₁ 9 (by omega), f₁ 3 (by omega), h9, h3]; omega) fun m₂ g₂ f₂ => ?_)
  rw [f₁ 9 (by omega), f₁ 3 (by omega), h9, h3] at g₂
  refine Runs.seqs_cons (Runs.loadR (by omega) (by omega) fun m₃ g₃ f₃ => ?_)
  rw [g₂, f₂ _ (by omega), f₁ _ (by omega), h1] at g₃
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₄ g₄ f₄ => ?_)
  refine Runs.seqs_cons (Runs.constR (by omega) (by omega) fun m₅ g₅ f₅ => ?_)
  refine Runs.seqs_cons (Runs.lessR (by omega) (by omega) (by omega) fun m₆ g₆ f₆ => ?_)
  have q₆ : ∀ a, a ≠ 2 → a ≠ 11 → a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 27 → m₆ a = m a :=
    fun a a2 a11 a12 a13 a14 a27 => by rw [f₆ a a14, f₅ a a13, f₄ a a12, f₃ a a11, f₂ a a2, f₁ a a27]
  have v27 : m₆ 27 = n := by
    rw [f₆ 27 (by omega), f₅ 27 (by omega), f₄ 27 (by omega), f₃ 27 (by omega), f₂ 27 (by omega), g₁]
  have v12 : m₆ 12 = 1 := by rw [f₆ 12 (by omega), f₅ 12 (by omega), g₄]
  have v13 : m₆ 13 = 0 := by rw [f₆ 13 (by omega), g₅]
  have v14 : m₆ 14 = if n < 1 then 1 else 0 := by
    rw [g₆, f₅ 27 (by omega), f₄ 27 (by omega), f₃ 27 (by omega), f₂ 27 (by omega), g₁,
      f₅ 12 (by omega), g₄]
  refine Runs.seqs_cons (Runs.mono (logLoop_spec v27 (by rw [q₆ 8 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), h8]) (by rw [q₆ 3 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), h3]) v12 v13 v14 (by omega)) fun m₇ c₇ ⟨g₇, f₇, hc₇⟩ => ?_)
  have q₇ : ∀ a, a ≠ 2 → a ≠ 11 → a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 27 → m₇ a = m a :=
    fun a a2 a11 a12 a13 a14 a27 => by rw [f₇ a a2 a12 a13 a14, q₆ a a2 a11 a12 a13 a14 a27]
  have w27 : m₇ 27 = n := by rw [f₇ 27 (by omega) (by omega) (by omega) (by omega), v27]
  have w3 : m₇ 3 = 1 := by
    rw [q₇ 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h3]
  have w4 : m₇ 4 = ℓ := by
    rw [q₇ 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h4]
  have w8 : m₇ 8 = 0 := by
    rw [q₇ 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h8]
  have w9 : m₇ 9 = A := by
    rw [q₇ 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h9]
  have w16 : m₇ 16 = 3 := by
    rw [q₇ 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h16]
  have w11 : m₇ 11 = E := by
    rw [f₇ 11 (by omega) (by omega) (by omega) (by omega), f₆ 11 (by omega), f₅ 11 (by omega),
      f₄ 11 (by omega), g₃]
  -- The sizes and the bases.
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [g₇]; omega) fun m₈ g₈ f₈ => ?_)
  rw [g₇] at g₈
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [f₈ 27 (by omega), w27, g₈]; omega) fun m₉ g₉ f₉ => ?_)
  rw [f₈ 27 (by omega), w27, g₈] at g₉
  refine Runs.seqs_cons (Runs.addR (by omega) (by omega) (by omega)
    (by rw [g₉, f₉ 16 (by omega), f₈ 16 (by omega), w16]; omega) fun m₁₀ g₁₀ f₁₀ => ?_)
  rw [g₉, f₉ 16 (by omega), f₈ 16 (by omega), w16] at g₁₀
  have eR : n + (Nat.size n + Nat.size n) + 3 = L.R := by omega
  rw [eR] at g₁₀
  have q₁₀ : ∀ a, a ≠ 12 → a ≠ 28 → m₁₀ a = m₇ a := fun a a12 a28 => by
    rw [f₁₀ a a12, f₉ a a12, f₈ a a28]
  have H32 : 32 ≤ L.H := by omega
  have g₈' : m₈ 28 = L.D := by omega
  refine Runs.mono (bases_spec hH H32 (by rw [q₁₀ 9 (by decide) (by decide), w9])
    (by rw [q₁₀ 4 (by decide) (by decide), w4]) g₁₀ hB) fun m' c ⟨hb, h13, hf, hc⟩ => ?_
  have r : ∀ a, a ≠ 2 → a ≠ 10 → a ≠ 13 → ¬(18 ≤ a ∧ a ≤ 26) → a ≠ 12 → a ≠ 28 → m' a = m₇ a :=
    fun a a2 a10 a13 hr a12 a28 => by rw [hf a a2 a10 a13 hr, q₁₀ a a12 a28]
  have hi : ∀ a, 32 ≤ a → m' a = m a := fun a ha => by
    rw [r a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q₇ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  refine ⟨⟨H32, hb, ?_, ?_, ?_, ?_, ?_, fun a hd => ?_⟩, ?_, h13, hi, fun a ha hT => ?_, ?_⟩
  · rw [hf 27 (by decide) (by decide) (by decide) (by decide), q₁₀ 27 (by decide) (by decide), w27,
      hLn]
  · rw [hf 28 (by decide) (by decide) (by decide) (by decide), f₁₀ 28 (by decide),
      f₉ 28 (by decide), g₈']
  · rw [r 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w3]
  · rw [r 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w8]
  · rw [r 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w16]
  · have hge : A + ℓ ≤ a := by
      have hCH := CH_ge (L := L)
      unfold Lay.Dyn at hd; omega
    rw [hi a (by omega), hz a hge]
  · rw [r 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), w11]
  · simp only [TS, not_or, not_and, not_le] at hT
    rw [r a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      q₇ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · omega

end Formalgo.Algorithms.ShortestPaths
