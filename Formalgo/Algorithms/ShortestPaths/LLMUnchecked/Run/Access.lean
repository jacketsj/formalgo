import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.Layout

/-!
# Reading and writing the arrays

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : EInput}

theorem top_ge : L.H + 10 * L.R ≤ L.top := by
  have := CH_ge (L := L); unfold Lay.top; omega

theorem arr_lt {k i : ℕ} (hk : k < 7) (hi : i ≤ L.bnd k) : L.H + k * L.R + i < L.H + 7 * L.R := by
  have := bnd_lt_R (L := L) k
  have := Nat.mul_le_mul_right L.R (show k + 1 ≤ 7 by omega)
  rw [Nat.succ_mul] at this; omega

theorem rd_spec (hR : Rep L σ m) {d k i : ℕ} (hk : k < 7) (hi : m i ≤ L.bnd k) (hd : d < 32)
    (hd2 : d ≠ 2) (hi32 : i < 32) (hB : L.top < B) :
    Runs B (rd d k i) m fun m' c => m' d = fld σ k (m i) ∧
      (∀ a, a ≠ 2 → a ≠ d → m' a = m a) ∧ c = 2 := by
  have ha := arr_lt (L := L) hk hi
  have ht := top_ge (L := L)
  have hH := hR.H32
  have hb := hR.base k (by omega)
  refine Runs.seq (Runs.addR (by omega) (by have := breg_lt k (by omega); omega) (by omega)
    (by rw [hb]; omega) fun m₁ h₁ f₁ => Runs.loadR (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  refine ⟨?_, fun a h2 hd' => by rw [f₂ a hd', f₁ a h2], rfl⟩
  rw [h₂, h₁, hb, f₁ _ (by omega)]
  exact hR.arr k hk _ hi

theorem wr_spec (hR : Rep L σ m) {k i s : ℕ} (hk : k < 7) (hi : m i ≤ L.bnd k) (hs : s ≠ 2)
    (hi32 : i < 32) (hs32 : s < 32) (hB : L.top < B) :
    Runs B (wr k i s) m fun m' c => Rep L (setFld k (m i) (m s) σ) m' ∧
      (∀ a, a ≠ 2 → a ≠ L.H + k * L.R + m i → m' a = m a) ∧ c = 2 := by
  have ha := arr_lt (L := L) hk hi
  have ht := top_ge (L := L)
  have hH := hR.H32
  have hb := hR.base k (by omega)
  refine Runs.seq (Runs.addR (by omega) (by have := breg_lt k (by omega); omega) (by omega)
    (by rw [hb]; omega) fun m₁ h₁ f₁ => Runs.store (by omega) (by omega) ?_)
  have hR₁ : Rep L σ m₁ := hR.congr (fun a ha _ => f₁ a (fun h => ha (by simp [Tmp, h])))
    (fun a ha => f₁ a (by omega))
  rw [h₁, hb, f₁ s hs]
  refine ⟨hR₁.store hk hi, fun a h2 ha' => ?_, rfl⟩
  rw [update_of_ne ha', f₁ a h2]

theorem chAt_spec (hR : Rep L σ m) (hF : Fixed L x m) {p j : ℕ} (hp : m p ≤ L.n)
    (hj : m j < L.cap (m p)) (hp32 : p < 32) (hj32 : j < 32) (hp2 : p ≠ 2) (hj2 : j ≠ 2)
    (hB : L.top < B) :
    Runs B (chAt p j) m fun m' c => m' 2 = L.cb (m p) + m j ∧ (∀ a, a ≠ 2 → m' a = m a) ∧
      c = 3 := by
  have hs := cb_slot hp hj
  have ht := top_ge (L := L)
  have hH := hR.H32
  have hb := hR.base 8 (by omega)
  have hR' : L.H + 8 * L.R + m p < L.H + 9 * L.R := by unfold Lay.R at *; omega
  have hcb := hF.cbv _ hp
  refine Runs.seq (Runs.addR (by omega) (by omega) (by omega) (by
      rw [show breg 8 = 26 from rfl] at hb; rw [hb]; omega) fun m₁ h₁ f₁ => ?_)
  refine Runs.seq (Runs.loadR (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  have hv2 : m₂ 2 = L.cb (m p) := by
    rw [show breg 8 = 26 from rfl] at hb
    rw [h₂, h₁, hb, f₁ _ (by omega), hcb]
  refine Runs.addR (by omega) (by omega) (by omega) (by rw [hv2, f₂ j hj2, f₁ j hj2]; omega)
    fun m₃ h₃ f₃ => ⟨by rw [h₃, hv2, f₂ j hj2, f₁ j hj2], fun a ha => by
      rw [f₃ a ha, f₂ a ha, f₁ a ha], rfl⟩

theorem chRd_spec (hR : Rep L σ m) (hF : Fixed L x m) {d p j : ℕ} (hp : m p ≤ L.n)
    (hj : m j < L.cap (m p)) (hp32 : p < 32) (hj32 : j < 32) (hp2 : p ≠ 2) (hj2 : j ≠ 2)
    (hd : d < 32) (hB : L.top < B) :
    Runs B (chRd d p j) m fun m' c => m' d = σ.ch (m p) (m j) ∧
      (∀ a, a ≠ 2 → a ≠ d → m' a = m a) ∧ c = 4 := by
  have hs := cb_slot hp hj
  have hH := hR.H32
  have hCH := CH_ge (L := L)
  refine Runs.seq (Runs.mono (chAt_spec hR hF hp hj hp32 hj32 hp2 hj2 hB) fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ =>
    Runs.loadR (by omega) (by omega) fun m₂ h₂ f₂ => ?_)
  refine ⟨?_, fun a h2 hd' => by rw [f₂ a hd', f₁ a h2], by omega⟩
  rw [h₂, h₁, f₁ _ (by omega)]
  exact hR.ch _ hp _ hj

theorem chWr_spec (hR : Rep L σ m) (hF : Fixed L x m) {p j s : ℕ} (hp : m p ≤ L.n)
    (hj : m j < L.cap (m p)) (hp32 : p < 32) (hj32 : j < 32) (hp2 : p ≠ 2) (hj2 : j ≠ 2)
    (hs : s ≠ 2) (hs32 : s < 32) (hB : L.top < B) :
    Runs B (chWr p j s) m fun m' c => Rep L (setCh (m p) (m j) (m s) σ) m' ∧
      (∀ a, a ≠ 2 → a ≠ L.cb (m p) + m j → m' a = m a) ∧ c = 4 := by
  have hs' := cb_slot hp hj
  have hH := hR.H32
  have hCH := CH_ge (L := L)
  refine Runs.seq (Runs.mono (chAt_spec hR hF hp hj hp32 hj32 hp2 hj2 hB) fun m₁ c₁ ⟨h₁, f₁, hc₁⟩ =>
    Runs.store (by omega) (by omega) ?_)
  have hR₁ : Rep L σ m₁ := hR.congr (fun a ha _ => f₁ a (fun h => ha (by simp [Tmp, h])))
    (fun a ha => f₁ a (by omega))
  rw [h₁, f₁ s hs]
  refine ⟨hR₁.chstore hp hj, fun a h2 ha' => ?_, by omega⟩
  rw [update_of_ne ha', f₁ a h2]

end Formalgo.Algorithms.ShortestPaths
