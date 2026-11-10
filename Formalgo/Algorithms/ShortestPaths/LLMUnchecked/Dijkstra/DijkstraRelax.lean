import Formalgo.Algorithms.ShortestPaths.LLMUnchecked.Dijkstra.DijkstraInv

/-!
# Dijkstra's algorithm on the model: relaxing the edges of a settled vertex

LLM-generated; not checked by a human.
-/

namespace Formalgo.Algorithms.ShortestPaths

open Function St LLMUnchecked

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [CanonicallyOrderedAdd R]
  {C : CtxW R} {G : WGraphW R} {src : ℕ} {W : R}

/-- The edges in `pre` have been relaxed from `x`. -/
def Done (x : ℕ) (pre : List (ℕ × R)) (s : StW R) : Prop :=
  ∀ p ∈ pre, s.stat p.1 ≠ 0 ∧ (s.stat p.1 = 1 → s.key p.1 ≤ s.key x + p.2)

/-- The invariant while relaxing the edges of `u`. -/
structure ScanInv (hs : src < G.n) (u : Fin G.n) (K : R) (Q : ℕ) (pre : List (ℕ × R))
    (t : StW R) (l : List (ℕ × R)) : Prop where
  split : C.adj ((u : ℕ) + 1) = pre ++ l
  g : GInv hs t
  rel : Relaxed G ((u : ℕ) + 1) t
  ust : t.stat ((u : ℕ) + 1) = 2
  pre : Done ((u : ℕ) + 1) pre t
  kb : ∀ v, t.stat v ≠ 0 → t.key v ≤ K
  ku : t.key ((u : ℕ) + 1) + W ≤ K
  cost : t.time + 65 * pot t (hset G.n t) + 325 * l.length ≤ Q

omit [CanonicallyOrderedAdd R] in
theorem GInv.tick {hs : src < G.n} {t : StW R} (h : GInv hs t) (c : ℕ) : GInv hs (tick c t) :=
  ⟨h.statle, h.range, h.fresh, h.settled, h.upper, h.source,
    ⟨h.heap.range, h.heap.forest.tick c, h.heap.roots.tick c, h.heap.min, h.heap.tbl⟩, h.empty⟩

omit [CanonicallyOrderedAdd R] in
theorem ScanInv.tick {hs : src < G.n} {u : Fin G.n} {K : R} {Q : ℕ} {pre l : List (ℕ × R)}
    {t : StW R}
    (h : ScanInv (C := C) (W := W) hs u K (Q - 50) pre t l) (hQ : 50 ≤ Q) :
    ScanInv (C := C) (W := W) hs u K Q pre (tick 50 t) l :=
  ⟨h.split, h.g.tick 50, h.rel, h.ust, h.pre, h.kb, h.ku, by
    have := h.cost; change t.time + 50 + 65 * pot t (hset G.n t) + 325 * l.length ≤ Q; omega⟩

/-- Inserting a new vertex at `nk`, from a settled `u`. -/
theorem relax_new {hs : src < G.n} {u v' : Fin G.n} {K : R} {Q : ℕ} {pre l : List (ℕ × R)}
    {t : StW R}
    (_hC : CtxOK C) (hA : AdjOK C G W) (hI : ScanInv (C := C) (W := W) hs u K Q pre t
      ((((v' : ℕ) + 1), G.weight s(u, v')) :: l))
    (hadj : G.graph.Adj u v') (h0 : t.stat ((v' : ℕ) + 1) = 0) :
    ScanInv (C := C) (W := W) hs u K (Q - 50) (pre ++ [((v' : ℕ) + 1, G.weight s(u, v'))])
      (insertSt ((v' : ℕ) + 1) (t.key ((u : ℕ) + 1) + G.weight s(u, v')) 1 t) l := by
  obtain ⟨hsp, hg, hrel, hust, hpre, hkb, hku, hcost⟩ := hI
  set v := (v' : ℕ) + 1 with hv
  set nk := t.key ((u : ℕ) + 1) + G.weight s(u, v') with hnk
  have hvM : v ∉ hset G.n t := fun h => by have := (mem_hset.1 h).2.2; omega
  obtain ⟨p0, d0, m0⟩ := hg.fresh v (by omega) h0
  obtain ⟨hH, hkey, hstat, hout, htime, hpot⟩ := insert_spec hg.heap hg.empty (by omega)
    (by have := v'.2; omega) hvM p0 d0 (by omega) nk 1
  set t' := insertSt v nk 1 t with ht'
  have hst : ∀ x, x ≠ v → t'.stat x = t.stat x := fun x hx => by rw [hstat, update_of_ne hx]
  have hke : ∀ x, x ≠ v → t'.key x = t.key x := fun x hx => by rw [hkey, update_of_ne hx]
  have hsv : t'.stat v = 1 := by rw [hstat, update_self]
  have hkv : t'.key v = nk := by rw [hkey, update_self]
  have huv : (u : ℕ) + 1 ≠ v := by intro h; rw [h] at hust; omega
  have hset' : hset G.n t' = insert v (hset G.n t) := by
    ext x; simp only [Finset.mem_insert, mem_hset]
    rcases eq_or_ne x v with rfl | hx
    · rw [hsv]; have := v'.2; simp; omega
    · rw [hst x hx]; simp [hx]
  have hdu : ∃ p : G.graph.Walk ⟨src, hs⟩ v', wlen G p ≤ nk := by
    obtain ⟨⟨p, hp⟩, -⟩ := hg.settled u hust
    exact ⟨p.concat hadj, le_of_eq (by rw [wlen_concat]; exact congrArg (· + _) hp)⟩
  refine ⟨by rw [hsp]; simp, ⟨fun x => ?_, fun x hx => ?_, fun x hx0 hx => ?_, fun x hx => ?_,
    fun x hx => ?_, ?_, by rw [hset']; exact hH, fun h => absurd h (by rw [hset']; simp)⟩,
    fun a b hab ha hadj' => ?_, by rw [hst _ huv]; exact hust, fun p hp => ?_, fun x hx => ?_,
    by rw [hke _ huv]; exact hku, ?_⟩
  · rcases eq_or_ne x v with rfl | hx
    · rw [hsv]; omega
    · rw [hst x hx]; exact hg.statle x
  · rcases eq_or_ne x v with rfl | hx'
    · have := v'.2; omega
    · rw [hst x hx'] at hx; exact hg.range x hx
  · have hxv : x ≠ v := by rintro rfl; rw [hsv] at hx; omega
    rw [hst x hxv] at hx
    obtain ⟨a, b, c⟩ := hg.fresh x hx0 hx
    obtain ⟨a', b', c'⟩ := hout x hxv hx0
    exact ⟨c'.trans a, a'.trans b, b'.trans c⟩
  · have hxv : (x : ℕ) + 1 ≠ v := by intro h; rw [h, hsv] at hx; omega
    rw [hst _ hxv] at hx; rw [hke _ hxv]; exact hg.settled x hx
  · rcases eq_or_ne ((x : ℕ) + 1) v with h | hxv
    · have hx' : x = v' := Fin.ext (by omega)
      subst hx'; rw [hkv]; exact hdu
    · rw [hst _ hxv] at hx; rw [hke _ hxv]; exact hg.upper x hx
  · have hsv' : src + 1 ≠ v := fun h => by
      have := hg.source.1; rw [h] at this; exact this h0
    rw [hst _ hsv', hke _ hsv']; exact hg.source
  · -- Settled vertices other than `u`.
    have hav : (a : ℕ) + 1 ≠ v := by intro h; rw [h, hsv] at ha; omega
    rw [hst _ hav] at ha
    obtain ⟨h1, h2⟩ := hrel a b hab ha hadj'
    have hbv : (b : ℕ) + 1 ≠ v := by intro h; rw [h] at h1; exact h1 h0
    rw [hst _ hbv, hke _ hbv, hke _ hav]; exact ⟨h1, h2⟩
  · rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨h1, h2⟩ := hpre p hp
      have hpv : p.1 ≠ v := by intro h; rw [h] at h1; exact h1 h0
      rw [hst _ hpv, hke _ hpv, hke _ huv]; exact ⟨h1, h2⟩
    · simp only [List.mem_singleton] at hp; subst hp
      simp only; rw [hsv, hkv, hke _ huv]; exact ⟨one_ne_zero, fun _ => le_rfl⟩
  · rcases eq_or_ne x v with rfl | hxv
    · rw [hkv]
      have := hA.wmax ((u : ℕ) + 1) (v, G.weight s(u, v')) (by rw [hsp]; simp)
      exact (add_le_add le_rfl this).trans hku
    · rw [hst x hxv] at hx; rw [hke x hxv]; exact hkb x hx
  · rw [hset', hpot, htime]; simp only [List.length_cons] at hcost; omega

/-- Lowering the key of a vertex in the heap to `nk`, from a settled `u`. -/
theorem relax_dec {hs : src < G.n} {u v' : Fin G.n} {K : R} {Q : ℕ} {pre l : List (ℕ × R)}
    {t : StW R}
    (hC : CtxOK C) (hA : AdjOK C G W) (hI : ScanInv (C := C) (W := W) hs u K Q pre t
      ((((v' : ℕ) + 1), G.weight s(u, v')) :: l))
    (hadj : G.graph.Adj u v') (h1 : t.stat ((v' : ℕ) + 1) = 1)
    (hlt : t.key ((u : ℕ) + 1) + G.weight s(u, v') < t.key ((v' : ℕ) + 1)) :
    ScanInv (C := C) (W := W) hs u K (Q - 50) (pre ++ [((v' : ℕ) + 1, G.weight s(u, v'))])
      (decKey C ((v' : ℕ) + 1) (t.key ((u : ℕ) + 1) + G.weight s(u, v')) t) l := by
  obtain ⟨hsp, hg, hrel, hust, hpre, hkb, hku, hcost⟩ := hI
  set v := (v' : ℕ) + 1 with hv
  set nk := t.key ((u : ℕ) + 1) + G.weight s(u, v') with hnk
  have hvM : v ∈ hset G.n t := mem_hset.2 ⟨by have := v'.2; omega, by omega, h1⟩
  have hFM : (hset G.n t).card ≤ C.F := by
    have := card_hset_le G.n t; have := hC.fuel; rw [hA.n_eq] at this; omega
  have hH0 : HeapInv C.n t (hset G.n t) := by rw [hA.n_eq]; exact hg.heap
  obtain ⟨hH, hkey, hstat, hout, hc⟩ := decKey_spec C hH0 hvM hlt hFM
  rw [hA.n_eq] at hH
  set t' := decKey C v nk t with ht'
  have hke : ∀ x, x ≠ v → t'.key x = t.key x := fun x hx => by rw [hkey, update_of_ne hx]
  have hkv : t'.key v = nk := by rw [hkey, update_self]
  have huv : (u : ℕ) + 1 ≠ v := by intro h; rw [h] at hust; omega
  have hset' : hset G.n t' = hset G.n t := by simp only [hset, hstat]
  have hdu : ∃ p : G.graph.Walk ⟨src, hs⟩ v', wlen G p ≤ nk := by
    obtain ⟨⟨p, hp⟩, -⟩ := hg.settled u hust
    exact ⟨p.concat hadj, le_of_eq (by rw [wlen_concat]; exact congrArg (· + _) hp)⟩
  refine ⟨by rw [hsp]; simp, ⟨fun x => by rw [hstat]; exact hg.statle x,
    fun x hx => by rw [hstat] at hx; exact hg.range x hx, fun x hx0 hx => ?_, fun x hx => ?_,
    fun x hx => ?_, ?_, by rw [hset']; exact hH,
    fun h => absurd h (by rw [hset']; exact Finset.ne_empty_of_mem hvM)⟩,
    fun a b hab ha hadj' => ?_, by rw [hstat]; exact hust, fun p hp => ?_, fun x hx => ?_,
    by rw [hke _ huv]; exact hku, ?_⟩
  · rw [hstat] at hx
    have hxM : x ∉ hset G.n t := fun h => by have := (mem_hset.1 h).2.2; omega
    obtain ⟨a, b, c⟩ := hg.fresh x hx0 hx
    obtain ⟨a', b', c'⟩ := hout x hxM hx0
    exact ⟨c'.trans a, a'.trans b, b'.trans c⟩
  · rw [hstat] at hx
    have hxv : (x : ℕ) + 1 ≠ v := by intro h; rw [h] at hx; omega
    rw [hke _ hxv]; exact hg.settled x hx
  · rw [hstat] at hx
    rcases eq_or_ne ((x : ℕ) + 1) v with h | hxv
    · have hx' : x = v' := Fin.ext (by omega)
      subst hx'; rw [hkv]; exact hdu
    · rw [hke _ hxv]; exact hg.upper x hx
  · have hsv' : src + 1 ≠ v := by
      intro h; have := hg.source.2; rw [h] at this; rw [this] at hlt
      exact lt_irrefl _ (zero_le.trans_lt hlt)
    rw [hstat, hke _ hsv']; exact hg.source
  · rw [hstat] at ha ⊢
    obtain ⟨h1', h2⟩ := hrel a b hab ha hadj'
    have hav : (a : ℕ) + 1 ≠ v := by intro h; rw [h] at ha; omega
    refine ⟨h1', fun hb => ?_⟩
    rw [hke _ hav]
    rcases eq_or_ne ((b : ℕ) + 1) v with h | hbv
    · rw [h, hkv]; have := h2 hb; rw [h] at this; exact (hlt.trans_le this).le
    · rw [hke _ hbv]; exact h2 hb
  · rw [hstat]
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨h1', h2⟩ := hpre p hp
      refine ⟨h1', fun hb => ?_⟩
      rw [hke _ huv]
      rcases eq_or_ne p.1 v with h | hpv
      · rw [h, hkv]; have := h2 hb; rw [h] at this; exact (hlt.trans_le this).le
      · rw [hke _ hpv]; exact h2 hb
    · simp only [List.mem_singleton] at hp; subst hp
      simp only; rw [hkv, hke _ huv]; exact ⟨by omega, fun _ => le_rfl⟩
  · rw [hstat] at hx
    rcases eq_or_ne x v with rfl | hxv
    · rw [hkv]
      have := hA.wmax ((u : ℕ) + 1) (v, G.weight s(u, v')) (by rw [hsp]; simp)
      exact (add_le_add le_rfl this).trans hku
    · rw [hke x hxv]; exact hkb x hx
  · rw [hset']; simp only [List.length_cons] at hcost; omega

omit [CanonicallyOrderedAdd R] in
/-- No change to the state: the edge is already relaxed. -/
theorem relax_keep {hs : src < G.n} {u : Fin G.n} {K : R} {Q : ℕ} {pre l : List (ℕ × R)}
    {t : StW R} {p : ℕ × R} (hI : ScanInv (C := C) (W := W) hs u K Q pre t (p :: l))
    (hp : t.stat p.1 ≠ 0 ∧ (t.stat p.1 = 1 → t.key p.1 ≤ t.key ((u : ℕ) + 1) + p.2)) :
    ScanInv (C := C) (W := W) hs u K (Q - 50) (pre ++ [p]) t l := by
  obtain ⟨hsp, hg, hrel, hust, hpre, hkb, hku, hcost⟩ := hI
  refine ⟨by rw [hsp]; simp, hg, hrel, hust, fun q hq => ?_, hkb, hku, ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · exact hpre q hq
    · simp only [List.mem_singleton] at hq; subst hq; exact hp
  · simp only [List.length_cons] at hcost; omega

end Formalgo.Algorithms.ShortestPaths
