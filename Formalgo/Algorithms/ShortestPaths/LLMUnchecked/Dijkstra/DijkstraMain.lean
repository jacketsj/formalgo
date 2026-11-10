import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.DijkstraScan

/-!
# Dijkstra's algorithm on the model: the main loop

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [CanonicallyOrderedAdd R]
  {C : CtxW R} {G : WGraphW R} {src : ℕ} {W : R}

/-- The steps paid per settled vertex, apart from its edges. -/
def perVertex (C : CtxW R) : ℕ := 200 * (C.D + 1) + 20

/-- The invariant of the main loop. -/
structure DInv (C : CtxW R) (G : WGraphW R) (W : R) (hs : src < G.n) (s : StW R) : Prop where
  g : GInv hs s
  rel : Relaxed G 0 s
  /-- Keys are at most `W` per settled vertex. -/
  keyle : ∀ v, s.stat v ≠ 0 → s.key v ≤ (done G.n s).card • W
  cost : s.time + 65 * pot s (hset G.n s) ≤
    65 + (done G.n s).card * perVertex C + (∑ v ∈ done G.n s, (C.adj v).length) * 325

omit [AddCommMonoid R] [CanonicallyOrderedAdd R] in
theorem Forest.setStat {s : StW R} {M : Finset ℕ} {e : ℕ} (h : Forest s M e) (v k : ℕ) :
    Forest (setStat v k s) M e :=
  h.congr rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

omit [AddCommMonoid R] [CanonicallyOrderedAdd R] in
omit [LinearOrder R] in
theorem RootList.setStat {s : StW R} {M L : Finset ℕ} (h : RootList s M L) (v k : ℕ) :
    RootList (setStat v k s) M L :=
  h.congr (fun _ _ => rfl) rfl rfl (fun _ _ _ => rfl)

/-- The state after extracting the minimum starts the scan. -/
theorem DInv.scan_start (hC : CtxOK C) (hA : AdjOK C G W) {hs : src < G.n} {s : StW R}
    (h : DInv C G W hs s) (hc : rootsCond s) {u' : Fin G.n} (hu'1 : (u' : ℕ) + 1 = s.hmin) :
    ScanInv (C := C) (W := W) hs u' (((done G.n s).card + 1) • W)
      ((setStat s.hmin 2 (extract C s)).time +
        65 * pot (setStat s.hmin 2 (extract C s)) (hset G.n (setStat s.hmin 2 (extract C s))) +
        325 * (C.adj ((u' : ℕ) + 1)).length) []
      (setStat s.hmin 2 (extract C s)) (C.adj ((u' : ℕ) + 1)) := by
  obtain ⟨hg, hrel, hkb, hcost⟩ := h
  simp only [rootsCond] at hc
  set M := hset G.n s with hM
  have hne : M.Nonempty := ⟨_, (hg.heap.roots.list 0 (by omega)).1⟩
  obtain ⟨m1, m2, m3⟩ := hg.heap.min hne
  obtain ⟨hun, hu0, hu1⟩ := mem_hset.1 m1
  set u := s.hmin with hu
  have hkeq : IsLeast (Set.range fun p : G.graph.Walk ⟨src, hs⟩ u' => wlen G p) (s.key u) := by
    rw [← hu'1]
    refine key_min_eq hg hrel (by rw [hu'1]; exact hu1) fun y hy => ?_
    rw [hu'1]; exact m3 _ (mem_hset.2 ⟨by have := y.2; omega, by omega, hy⟩)
  -- Extracting `u`.
  have hH : HeapInv C.n s M := by rw [hA.n_eq]; exact hg.heap
  obtain ⟨hH1, hk1, hc1, he1⟩ := extract_spec C hC hH hne
  rw [hA.n_eq] at hH1
  set s₁ := extract C s with hs₁
  set s₂ := setStat u 2 s₁ with hs₂
  have hst2 : ∀ x, s₂.stat x = update s.stat u 2 x := fun x => by
    change update s₁.stat u 2 x = _; rw [hk1.stat]
  have hst : ∀ x, x ≠ u → s₂.stat x = s.stat x := fun x hx => by rw [hst2, update_of_ne hx]
  have hsu : s₂.stat u = 2 := by rw [hst2, update_self]
  have hke : s₂.key = s.key := hk1.key
  have hset2 : hset G.n s₂ = M.erase u := by
    ext x; simp only [Finset.mem_erase, mem_hset, hM]
    rcases eq_or_ne x u with rfl | hx
    · rw [hsu]; simp
    · rw [hst x hx]; simp [hx]
  have hdone2 : done G.n s₂ = insert u (done G.n s) := by
    ext x; simp only [Finset.mem_insert, mem_done]
    rcases eq_or_ne x u with rfl | hx
    · rw [hsu]; simp; omega
    · rw [hst x hx]; simp [hx]
  have hund : u ∉ done G.n s := fun h => by have := (mem_done.1 h).2.2; omega
  refine ⟨rfl, ⟨fun x => ?_, fun x hx => ?_, fun x hx0 hx => ?_, fun x hx => ?_, fun x hx => ?_,
    ?_, ?_, fun he => ?_⟩, fun a b hab ha hadj => ?_, by rw [hu'1]; exact hsu,
    fun p hp => by simp at hp, fun x hx => ?_, ?_, le_refl _⟩
  · rw [hst2]; simp only [update_apply]; split_ifs
    · omega
    · exact hg.statle x
  · rcases eq_or_ne x u with rfl | hxu
    · omega
    · rw [hst x hxu] at hx; exact hg.range x hx
  · have hxu : x ≠ u := by rintro rfl; rw [hsu] at hx; omega
    rw [hst x hxu] at hx
    have hxM : x ∉ M := fun h => by have := (mem_hset.1 h).2.2; omega
    obtain ⟨a, b, c⟩ := hg.fresh x hx0 hx
    obtain ⟨a', b', c'⟩ := hk1.out x hxM hx0
    exact ⟨c'.trans a, a'.trans b, b'.trans c⟩
  · rw [hke]
    rcases eq_or_ne ((x : ℕ) + 1) u with h | hxu
    · have : x = u' := Fin.ext (by omega)
      subst this; rw [hu'1]; exact hkeq
    · rw [hst _ hxu] at hx; exact hg.settled x hx
  · rw [hke]
    rcases eq_or_ne ((x : ℕ) + 1) u with h | hxu
    · have : x = u' := Fin.ext (by omega)
      subst this; rw [hu'1]; obtain ⟨⟨p, hp⟩, -⟩ := hkeq; exact ⟨p, hp.le⟩
    · rw [hst _ hxu] at hx; exact hg.upper x hx
  · rw [hke]
    refine ⟨?_, hg.source.2⟩
    rcases eq_or_ne (src + 1) u with h | hxu
    · rw [h, hsu]; omega
    · rw [hst _ hxu]; exact hg.source.1
  · rw [hset2]
    exact ⟨hH1.range, hH1.forest.setStat _ _, hH1.roots.setStat _ _, hH1.min, hH1.tbl⟩
  · rw [hset2] at he; exact he1 he
  · have hau : (a : ℕ) + 1 ≠ u := by omega
    rw [hst _ hau] at ha
    obtain ⟨h1, h2⟩ := hrel a b (by omega) ha hadj
    rw [hke]
    rcases eq_or_ne ((b : ℕ) + 1) u with hb | hbu
    · rw [hb, hsu]; omega
    · rw [hst _ hbu]; exact ⟨h1, h2⟩
  · rw [hke]
    rcases eq_or_ne x u with h | hxu
    · rw [h, succ_nsmul]; exact (hkb u (by omega)).trans le_self_add
    · rw [hst x hxu] at hx; rw [succ_nsmul]; exact (hkb x hx).trans le_self_add
  · rw [hke, hu'1, succ_nsmul]; exact add_le_add (hkb u (by omega)) le_rfl

theorem DInv.step (hC : CtxOK C) (hA : AdjOK C G W) {hs : src < G.n} {s : StW R}
    (h : DInv C G W hs s) (hc : rootsCond s) :
    DInv C G W hs (mainStep C s) ∧
      G.n - (done G.n (mainStep C s)).card < G.n - (done G.n s).card := by
  have hD := h
  obtain ⟨hg, hrel, hkb, hcost⟩ := h
  simp only [rootsCond] at hc
  set M := hset G.n s with hM
  have hne : M.Nonempty := ⟨_, (hg.heap.roots.list 0 (by omega)).1⟩
  obtain ⟨m1, m2, m3⟩ := hg.heap.min hne
  obtain ⟨hun, hu0, hu1⟩ := mem_hset.1 m1
  set u := s.hmin with hu
  set u' : Fin G.n := ⟨u - 1, by omega⟩ with hu'
  have hu'1 : (u' : ℕ) + 1 = u := by simp only [hu']; omega
  -- Extracting `u`.
  have hH : HeapInv C.n s M := by rw [hA.n_eq]; exact hg.heap
  obtain ⟨hH1, hk1, hc1, he1⟩ := extract_spec C hC hH hne
  rw [hA.n_eq] at hH1
  set s₁ := extract C s with hs₁
  set s₂ := setStat u 2 s₁ with hs₂
  have hst2 : ∀ x, s₂.stat x = update s.stat u 2 x := fun x => by
    change update s₁.stat u 2 x = _; rw [hk1.stat]
  have hst : ∀ x, x ≠ u → s₂.stat x = s.stat x := fun x hx => by rw [hst2, update_of_ne hx]
  have hsu : s₂.stat u = 2 := by rw [hst2, update_self]
  have hke : s₂.key = s.key := hk1.key
  have hset2 : hset G.n s₂ = M.erase u := by
    ext x; simp only [Finset.mem_erase, mem_hset, hM]
    rcases eq_or_ne x u with rfl | hx
    · rw [hsu]; simp
    · rw [hst x hx]; simp [hx]
  have hdone2 : done G.n s₂ = insert u (done G.n s) := by
    ext x; simp only [Finset.mem_insert, mem_done]
    rcases eq_or_ne x u with rfl | hx
    · rw [hsu]; simp; omega
    · rw [hst x hx]; simp [hx]
  have hund : u ∉ done G.n s := fun h => by have := (mem_done.1 h).2.2; omega
  have hI : ScanInv (C := C) (W := W) hs u' (((done G.n s).card + 1) • W)
      (s₂.time + 65 * pot s₂ (hset G.n s₂) + 325 * (C.adj ((u' : ℕ) + 1)).length) []
      s₂ (C.adj ((u' : ℕ) + 1)) := hD.scan_start hC hA hc hu'1
  obtain ⟨hI3, hst3⟩ := scan_loop hC hA hI
  set t₃ := (whileF scanCond (scanStep C) C.F (s₂, (u' : ℕ) + 1, C.adj ((u' : ℕ) + 1))).1
    with ht₃
  have hmain : mainStep C s = tick 20 t₃ := by rw [ht₃, hu'1]; rfl
  have hdone3 : done G.n t₃ = insert u (done G.n s) := by
    rw [← hdone2]; ext x; simp only [mem_done, hst3]
  rw [hmain]
  have hcard : (done G.n t₃).card = (done G.n s).card + 1 := by
    rw [hdone3, Finset.card_insert_of_notMem hund]
  refine ⟨⟨hI3.g.tick 20, hI3.relaxed hA, ?_, ?_⟩, ?_⟩
  · intro x hx
    change t₃.key x ≤ (done G.n t₃).card • W
    rw [hcard]; exact hI3.kb x hx
  · change t₃.time + 20 + 65 * pot t₃ (hset G.n t₃) ≤ 65 + (done G.n t₃).card * perVertex C +
      (∑ v ∈ done G.n t₃, (C.adj v).length) * 325
    have h3 := hI3.cost
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at h3
    rw [hcard, hdone3, Finset.sum_insert hund, Nat.add_mul, Nat.one_mul]
    have hp2 : pot s₂ (hset G.n s₂) = pot s₁ (M.erase s.hmin) := by rw [hset2]; rfl
    have ht2 : s₂.time = s₁.time := rfl
    have hlen : (C.adj ((u' : ℕ) + 1)).length = (C.adj u).length := by rw [hu'1]
    have hpv : perVertex C = 200 * (C.D + 1) + 20 := rfl
    have hc1' : s₁.time + 65 * pot s₁ (M.erase s.hmin) ≤ s.time + 65 * pot s M + 200 * (C.D + 1) :=
      hc1
    omega
  · change G.n - (done G.n t₃).card < _
    rw [hcard]; have := card_done_le G.n t₃; rw [hcard] at this; omega

/-- For natural weights, keys are at most `W` per settled vertex. -/
theorem DInv.kb {C : Ctx} {G : WGraph} {W : ℕ} {hs : src < G.n} {s : St} (h : DInv C G W hs s) :
    ∀ v, s.stat v ≠ 0 → s.key v ≤ (done G.n s).card * W :=
  fun v hv => (smul_eq_mul (done G.n s).card W) ▸ h.keyle v hv

end Formalgo.Algorithms.ShortestPaths
