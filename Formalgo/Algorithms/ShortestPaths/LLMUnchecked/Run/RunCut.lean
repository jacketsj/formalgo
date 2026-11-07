import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Run.RunAttach

/-!
# Running `cut`

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open LLMUnchecked Cmd Prog Function

variable {L : Lay} {σ : St} {m : Mem} {B : ℕ} {x : Input}

theorem cut_spec (hR : Rep L σ m) (hF : Fixed L x m) {rv rp : ℕ} (hv : m rv ≤ L.n)
    (hp : m rp ≤ L.n) (hp0 : m rp ≠ 0) (hd1 : 1 ≤ σ.deg (m rp))
    (hcap : σ.deg (m rp) ≤ L.cap (m rp)) (hlast : σ.ch (m rp) (σ.deg (m rp) - 1) ≤ L.n)
    (hpos : σ.pos (m rv) < L.cap (m rp)) (hd0 : σ.deg 0 ≤ L.n)
    (hrv : rv < 32) (hrp : rp < 32) (hrvT : ¬T267 rv) (hrpT : ¬T267 rp) (hB : L.top < B) :
    Runs B (cut rv rp) m fun m' c => Rep L (St.cut (m rv) (m rp) σ) m' ∧ Fixed L x m' ∧
      Frm L T267 m m' ∧ c ≤ 35 := by
  have hH := hR.H32
  have ht := top_ge (L := L)
  have hRn : L.n + L.D + 3 = L.R := rfl
  have tT : ∀ a, T267 a → Tmp a := fun a ha => by rcases ha with h | h | h <;> simp [Tmp, h]
  have h8 : ¬T267 8 := by simp [T267]
  unfold cut
  refine Runs.seqs_cons (Runs.mono (detach_spec hR hF hv hp hd1 hcap hlast hpos hrv hrp hrvT hrpT
    hB) fun m₁ c₁ ⟨R₁, X₁, F₁, hc₁⟩ => ?_)
  have q₁ : m₁ rv = m rv := F₁.1 rv hrv hrvT
  have z₁ : m₁ 8 = 0 := by rw [F₁.1 8 (by omega) h8, hR.zero]
  have hd0' : (St.detach (m rv) (m rp) σ).deg 0 < L.cap 0 := by
    change update σ.deg (m rp) _ 0 < _; rw [update_of_ne (Ne.symm hp0)]; simp [Lay.cap]; omega
  refine Runs.seqs_cons (Runs.mono (attach_spec R₁ X₁ (rv := rv) (rp := 8) (by rw [q₁]; exact hv)
    (by rw [z₁]; omega) (by rw [z₁]; exact hd0') hrv (by omega) hrvT h8 hB)
    fun m₂ c₂ ⟨R₂, X₂, F₂, hc₂⟩ => ?_)
  rw [q₁, z₁] at R₂
  have q₂ : m₂ rv = m rv := by rw [F₂.1 rv hrv hrvT, q₁]
  have z₂ : m₂ 8 = 0 := by rw [F₂.1 8 (by omega) h8, z₁]
  refine Runs.seqs_cons (Runs.mono (wr_spec R₂ (k := 4) (i := rv) (s := 8) (by omega)
    (by rw [q₂]; simp [Lay.bnd]; omega) (by omega) hrv (by omega) hB)
    fun m₃ c₃ ⟨R₃, f₃, hc₃⟩ => ?_)
  rw [q₂, z₂] at R₃
  have F₃ : Frm L T267 m m₃ := F₁.trans (F₂.trans (Frm.dyn (dyn_arr (k := 4) (by omega)
    (by rw [q₂]; simp [Lay.bnd]; omega)) (by simp [T267]) f₃ hH))
  refine Runs.seqs_nilR (by omega) fun m₄ h₄ f₄ => ?_
  have F₄ : Frm L T267 m m₄ := F₃.trans (Frm.reg1 (by simp [T267]) (by omega) f₄)
  exact ⟨R₃.reg (T := T267) tT (Frm.reg1 (by simp [T267]) (by omega) f₄)
    (fun a ha => f₄ a (by omega)), hF.frame hH F₄.2, F₄, by omega⟩

end Formalgo.Algorithms.ShortestPaths
