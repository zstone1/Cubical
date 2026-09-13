import CubeChains.Concurrency.Merge.Atom
import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Merge/CubeFaces — a chain of a cube is an ordered partition of its axes

The normal form `cross_eq_of_sort`: a coarsening re-sorts the source's word inside each bead, so
naming the sorting permutation names the coarsening's `cross`.  Its two inputs are
`cross_eq_of_sorted` (a chain's word is the only order sorted by bead then coordinate) and
`beadOf_cross` (the bead a coarsening puts the letter fired at step `s` in is the block of `s`),
both in `Concurrency/Merge/CubeCrossing`.

Two coarsenings meet in one (`exists_meet`); the meet of two atoms out of a run deletes exactly
their two junctions (`boundaries_of_meet`), so the sorting permutation there is the product of the
two swaps — `cross_of_meet_far`, `cross_of_meet_braid`, on the nose.

Bead-sharing is stated throughout as **junction membership**: two adjacent ranks lie in one bead of
`c` exactly when `c` has dropped the junction between them, `(i : ℕ) + 1 ∉ boundaries c.dims`.
-/

open CategoryTheory Equiv BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## The runs of a cube are its permutations

A run's `cross` *is* the word it spells (`runWordEquiv`, which is `cross` on runs): `cross` is the
firing order inverted, and on a run the firing order is its step order. -/

@[simp] theorem cross_wordRun (σ : Equiv.Perm (Fin n)) : cross (wordRun σ).chain = σ :=
  (cross_eq_flatten_inv (wordRun σ).chain).trans ((runWordEquiv n).apply_symm_apply σ)

@[simp] theorem weakClass_wordRun (σ : Equiv.Perm (Fin n)) :
    weakClass (wordRun σ).chain = WeakOrder.of σ := by
  rw [weakClass, cross_wordRun]

/-! ## Beads and the junctions that separate them -/

/-- **A junction the shape has dropped is one of the excluded set**, when the shape's junctions are
all of `0 … n` but `S`.  Reading which junction is missing is how every construction below
recognises the cut it is standing at. -/
theorem mem_of_notMem_boundaries {d : List ℕ+} {S : Finset ℕ}
    (hS : boundaries d = Finset.range (n + 1) \ S) {i : Fin (n - 1)}
    (h : (i : ℕ) + 1 ∉ boundaries d) : (i : ℕ) + 1 ∈ S := by
  have hi := i.isLt
  rw [hS] at h
  simp only [Finset.mem_sdiff, Finset.mem_range, not_and, not_not] at h
  exact h (by omega)

/-- **An adjacent swap across a deleted junction stays inside its bead.** -/
theorem beadAt_adjT_of_notMem {d : List ℕ+} {i : Fin (n - 1)} (hi : (i : ℕ) + 1 ∉ boundaries d)
    (x : Fin n) : beadAt d (adjT i x) = beadAt d x := by
  have hstep : beadAt d (adjLo i : Fin n) = beadAt d (adjHi i : Fin n) := by
    simpa [adjLo_val, adjHi_val] using (beadAt_succ_eq_iff d (i : ℕ)).mpr hi
  rcases eq_or_ne (x : ℕ) (i : ℕ) with hx | hx
  · rw [show x = adjLo i from Fin.ext (by simpa using hx), adjT_lo]; exact hstep.symm
  rcases eq_or_ne (x : ℕ) ((i : ℕ) + 1) with hx' | hx'
  · rw [show x = adjHi i from Fin.ext (by simpa using hx'), adjT_hi]; exact hstep
  · rw [adjT_of_ne _ hx hx']

/-! ## The normal form: a coarsening re-sorts the firing order inside each bead

`cross_eq_of_sort` is `flatten_apply` with the bead computed by `beadOf_of_hom`.  Every crossing
permutation below is read off it, by naming the permutation that sorts the beads. -/

/-- Chaining a rise along a bead: a bead is a stretch of consecutive coordinates, so every interior
step of it lies in the same bead (`beadAt_mono` sandwiches it) and the rises compose. -/
private theorem lt_of_rise_adj {c : List ℕ+} {σ g : Equiv.Perm (Fin n)}
    (hadj : ∀ i : Fin (n - 1), (i : ℕ) + 1 ∉ boundaries c →
      σ (g (adjLo i)) < σ (g (adjHi i))) {x y : Fin n} (hxy : (x : ℕ) < (y : ℕ))
    (hidx : beadAt c x = beadAt c y) : σ (g x) < σ (g y) :=
  rel_of_span (P := fun t => beadAt c (t - 1) = beadAt c t)
    (R := fun p q => σ (g p) < σ (g q)) (fun _ _ _ => lt_trans)
    (fun k hk => hadj k ((beadAt_succ_eq_iff c (k : ℕ)).mp (by simpa using hk))) x y hxy
    fun t h1 h2 => by
      have a1 := beadAt_mono c (show (x : ℕ) ≤ t - 1 by omega)
      have a2 := beadAt_mono c (show t - 1 ≤ t by omega)
      have a3 := beadAt_mono c (show t ≤ (y : ℕ) from h2)
      omega

/-- **A coarsening re-sorts its source's word inside each bead.**  `g` permutes each bead of `c`
(`hblk`) into `σ`-increasing order, and adjacent pairs suffice (`hadj`) because a bead is a stretch
of consecutive coordinates; then `σ * g` is `c`'s crossing permutation. -/
theorem cross_eq_of_sort {r c : Ch (□n)} {σ : Equiv.Perm (Fin n)} (hr : cross r = σ) (f : r ⟶ c)
    (g : Equiv.Perm (Fin n)) (hblk : ∀ x : Fin n, beadAt c.dims (g x) = beadAt c.dims x)
    (hadj : ∀ i : Fin (n - 1), (i : ℕ) + 1 ∉ boundaries c.dims →
      σ (g (adjLo i)) < σ (g (adjHi i))) :
    cross c = σ * g := by
  have hb : ∀ z : Fin n, (beadOf c ((σ * g) z) : ℕ)
      = ((dimComp c.dims (dimSum_dims_cube c)).index (g z) : ℕ) := fun z => by
    rw [show (σ * g) z = cross r (g z) from by rw [hr]; exact Equiv.Perm.mul_apply σ g z]
    exact beadOf_cross f (g z)
  refine cross_eq_of_sorted c (σ * g) fun x y hxy => ?_
  have e1 := beadAt_eq_index_succ (dimSum_dims_cube c) (g x)
  have e2 := beadAt_eq_index_succ (dimSum_dims_cube c) (g y)
  rw [hblk] at e1 e2
  rcases lt_or_eq_of_le (beadAt_mono c.dims (Fin.le_def.mp hxy.le)) with hlt | heq
  · exact Or.inl (by rw [hb x, hb y]; omega)
  · refine Or.inr ⟨Fin.ext (by rw [hb x, hb y]; omega), ?_⟩
    simpa only [Equiv.Perm.mul_apply] using
      lt_of_rise_adj hadj (Fin.lt_def.mp hxy) heq

/-- **A coarsening fires in its source's order exactly when nothing falls across a junction it has
deleted** — `cross_eq_of_sort` at `g = 1`, and the only way a coarsening can cross anything. -/
theorem cross_eq_of_rise {r c : Ch (□n)} {σ : Equiv.Perm (Fin n)} (hr : cross r = σ) (f : r ⟶ c)
    (hadj : ∀ i : Fin (n - 1), (i : ℕ) + 1 ∉ boundaries c.dims →
      σ (adjLo i) < σ (adjHi i)) :
    cross c = σ := by
  conv_rhs => rw [← mul_one σ]
  exact cross_eq_of_sort hr f 1 (fun x => by rw [Equiv.Perm.one_apply])
    (by simpa only [Equiv.Perm.one_apply] using hadj)

/-! ## A step at one cut

A step whose crossing permutation is a single adjacent swap `adjT i` faces off a *descent* of the
source's firing order and deletes the junction between the two ranks it names.  Those are the two
inputs `cross_eq_of_sort` needs at every atom below. -/

/-- The step's crossing permutation, transported to the target. -/
private theorem cross_mul_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) : cross b = cross a * adjT i := by
  have h := cross_eq_mul f
  rw [hf] at h
  rw [h, mul_adjT_adjT]

/-- **Only a descent shortens**: a step crossing one adjacent pair faces off a descent. -/
theorem cross_descent_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) :
    cross a (adjHi i) < cross a (adjLo i) := by
  have hadd := crossLen_eq_add f
  simp only [crossLen, hf, permLen_adjT, cross_mul_adjT f hf] at hadd
  rcases lt_trichotomy (cross a (adjHi i)) (cross a (adjLo i)) with h | h | h
  · exact h
  · exact absurd (congrArg Fin.val ((cross a).injective h))
      (by simp only [adjHi_val, adjLo_val]; omega)
  · have := permLen_mul_adjT h
    omega

/-- **…and it deletes the junction between the two ranks it names**: were the junction still there,
the target would fire the two coordinates in the order the swap has just reversed. -/
theorem notMem_boundaries_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) : (i : ℕ) + 1 ∉ boundaries b.dims := by
  intro hmem
  have hcb : cross b = cross a * adjT i := cross_mul_adjT f hf
  have hlo : cross b (adjHi i) = cross a (adjLo i) := by
    rw [hcb, Equiv.Perm.mul_apply, adjT_hi]
  have hhi : cross b (adjLo i) = cross a (adjHi i) := by
    rw [hcb, Equiv.Perm.mul_apply, adjT_lo]
  have hlt : (beadOf b (cross b (adjHi i)) : ℕ) < (beadOf b (cross b (adjLo i)) : ℕ) := by
    rw [hlo, hhi, beadOf_cross f, beadOf_cross f]
    have e1 := beadAt_eq_index_succ (dimSum_dims_cube b) (adjLo i)
    have e2 := beadAt_eq_index_succ (dimSum_dims_cube b) (adjHi i)
    have := (beadAt_lt_iff b.dims (adjLo i : ℕ) (adjHi i : ℕ)).mpr
      ⟨(i : ℕ) + 1, hmem, by simp, by simp⟩
    omega
  exact absurd (Fin.lt_def.mp ((lt_iff_cross b).mpr (Or.inl hlt)))
    (by simp only [adjHi_val, adjLo_val]; omega)

/-! ## The meet of two coarsenings

A shape on `n` events *is* its junction set (`boundaries_injective`, `exists_boundaries_eq`), so
the meet of two shapes is the intersection of their junction sets, with nothing to construct. -/

theorem boundaries_topDims_subset (N : ℕ) : boundaries (topDims N) ⊆ {0, N} := by
  cases N with
  | zero =>
    intro x hx
    have := le_dimSum_of_mem_boundaries hx
    rw [dimSum_topDims] at this
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  | succ k =>
    rw [show topDims (k + 1) = [⟨k + 1, k.succ_pos⟩] from rfl, boundaries_singleton]
    exact fun x hx => hx

/-- **A coarsening with a prescribed shape.**  Every shape whose junctions `a` has is realised by
a coarsening of `a` — the one-bead chain is below it for free, its junctions being `0` and `n`. -/
theorem exists_coarsening {a : Ch (□n)} {m : List ℕ+} (hm : dimSum m = n)
    (hsub : boundaries m ⊆ boundaries a.dims) : ∃ (d : Ch (□n)) (_ : a ⟶ d), d.dims = m := by
  obtain ⟨d, hd, ⟨f⟩, -⟩ := exists_mid_chain (toCubeTop a) hm hsub
    (subset_trans (boundaries_topDims_subset n) fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact zero_mem_boundaries m
      · rw [Finset.mem_singleton.mp hx', ← hm]; exact dimSum_mem_boundaries m)
  exact ⟨d, f, hd⟩

/-- **Two shapes over the same events have a meet** — the shape of the intersected junction sets,
which `exists_boundaries_eq` realises. -/
theorem exists_meet_shape {N : ℕ} {d₁ d₂ : List ℕ+} (h₁ : dimSum d₁ = N) (h₂ : dimSum d₂ = N) :
    ∃ m : List ℕ+, dimSum m = N ∧ boundaries m = boundaries d₁ ∩ boundaries d₂ :=
  exists_boundaries_eq
    (fun _ ht => h₁ ▸ le_dimSum_of_mem_boundaries (Finset.mem_inter.mp ht).1)
    (Finset.mem_inter.mpr ⟨zero_mem_boundaries _, zero_mem_boundaries _⟩)
    (Finset.mem_inter.mpr ⟨h₁ ▸ dimSum_mem_boundaries _, h₂ ▸ dimSum_mem_boundaries _⟩)

/-- **Two coarsenings of a chain meet in one**, carrying the junctions of both. -/
theorem exists_meet {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧
      boundaries e.dims = boundaries d₁.dims ∩ boundaries d₂.dims := by
  obtain ⟨m, hm, hbm⟩ := exists_meet_shape (dimSum_dims_cube d₁) (dimSum_dims_cube d₂)
  obtain ⟨e, v₁, hed⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_left)
  obtain ⟨e', v₂, hed'⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_right)
  obtain rfl : e = e' := chain_ext_of_dims (u₁ ≫ v₁) (u₂ ≫ v₂) (hed.trans hed'.symm)
  exact ⟨e, ⟨v₁⟩, ⟨v₂⟩, by rw [hed, hbm]⟩

/-! ## `W` is closed under meets

Two refinements that cross nothing have the same firing order, so a junction one of them lacks is
one across which the coordinates rise.  Chaining that along a bead of their meet keeps the whole
bead rising — which says exactly that the meet fires in that same order, so it crosses nothing
either. -/

/-- Consecutive events in one bead of a chain have rising coordinates. -/
private theorem lt_of_beadAt_eq {d : Ch (□n)} {ψ : Equiv.Perm (Fin n)} (hd : cross d = ψ)
    {z y : Fin n} (hzy : (z : ℕ) < (y : ℕ)) (hidx : beadAt d.dims z = beadAt d.dims y) :
    ψ z < ψ y := by
  rcases (lt_iff_cross d).mp (Fin.lt_def.mpr hzy) with hb | ⟨-, hgz⟩
  · rw [beadOf_cross_self, beadOf_cross_self] at hb
    have e1 := beadAt_eq_index_succ (dimSum_dims_cube d) z
    have e2 := beadAt_eq_index_succ (dimSum_dims_cube d) y
    omega
  · rwa [hd] at hgz

/-- **`W` is closed under meets**: two refinements of a chain that cross nothing have a common
coarsening that crosses nothing. -/
theorem exists_meet_cross_eq {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h : cross d₁ = cross d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧ cross e = cross d₁ := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  refine ⟨e, ⟨v₁⟩, ⟨v₂⟩, ?_⟩
  refine cross_eq_of_rise rfl v₁ (fun i hi => ?_)
  -- across a junction `e` lacks, one of `d₁`, `d₂` lacks it too, and there the coordinates rise
  have hzy : ((adjHi i : Fin n) : ℕ) = ((adjLo i : Fin n) : ℕ) + 1 := by
    simp only [adjLo_val, adjHi_val]
  rw [hb, Finset.mem_inter] at hi
  rcases not_and_or.mp hi with hm | hm
  · exact lt_of_beadAt_eq rfl (by omega)
      (by simpa only [adjLo_val, adjHi_val] using (beadAt_succ_eq_iff d₁.dims (i : ℕ)).mpr hm)
  · exact lt_of_beadAt_eq h.symm (by omega)
      (by simpa only [adjLo_val, adjHi_val] using (beadAt_succ_eq_iff d₂.dims (i : ℕ)).mpr hm)

/-- **`W` is closed under meets**, on the nose.  Every chain in a `W`-class is a coarsening of the
class's run, so this is confluence *inside* a class — no terminal object of the class is needed. -/
theorem exists_meet_W {a d₁ d₂ : Ch (□n)} {u₁ : a ⟶ d₁} {u₂ : a ⟶ d₂}
    (h₁ : W (□n) u₁) (h₂ : W (□n) u₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), W (□n) v₁ ∧ W (□n) v₂ := by
  have hc₁ : cross a = cross d₁ := WeakOrder.of_injective (weakClass_eq_of_W h₁)
  have hc₂ : cross a = cross d₂ := WeakOrder.of_injective (weakClass_eq_of_W h₂)
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hce⟩ := exists_meet_cross_eq u₁ u₂ (hc₁.symm.trans hc₂)
  exact ⟨e, v₁, v₂, W_of_cross_eq v₁ hce.symm,
    W_of_cross_eq v₂ (hc₂.symm.trans (hc₁.trans hce.symm))⟩

/-! ## The atom out of a run -/

/-- **The atom out of a run.**  A descent of the run's crossing permutation is realised by merging
the two events it names: the face has one two-event bead, and crosses that pair less. -/
theorem exists_atom_face {r : Ch (□n)} (hr : ∀ x ∈ r.dims, x = 1) {i : Fin (n - 1)}
    (hi : cross r (adjHi i) < cross r (adjLo i)) :
    ∃ (d : Ch (□n)) (_ : r ⟶ d), cross d = cross r * adjT i ∧ d.dims = atomComp n i := by
  have hi2 := i.isLt
  obtain ⟨d, h, hdd⟩ := exists_coarsening (dimSum_atomComp n i) (a := r) (by
    rw [boundaries_atomComp, ones_dims_eq hr (wedgeDimSum_eq r.map), boundaries_ones]
    exact Finset.sdiff_subset)
  refine ⟨d, h, ?_, hdd⟩
  have hS : boundaries d.dims = Finset.range (n + 1) \ {(i : ℕ) + 1} := by
    rw [hdd, boundaries_atomComp]
  refine cross_eq_of_sort rfl h (adjT i)
    (beadAt_adjT_of_notMem (by rw [hS]; simp)) (fun j hj => ?_)
  obtain rfl : j = i := Fin.ext (by
    have := Finset.mem_singleton.mp (mem_of_notMem_boundaries hS hj); omega)
  rw [adjT_lo, adjT_hi]
  exact hi

/-- **A fraction that crosses something factors through an atom.**  A coarsening that crosses
anything falls across one of the junctions it has deleted (`cross_eq_of_rise`), and that adjacent
descent's atom face lands under the target — the junction being deleted is exactly what puts it
there. -/
theorem exists_atom_factor {σ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (hne : cross d ≠ σ) :
    ∃ (i : Fin (n - 1)) (e : Ch (□n)), σ (adjHi i) < σ (adjLo i) ∧
      Nonempty ((wordRun σ).chain ⟶ e) ∧ Nonempty (e ⟶ d)
      ∧ cross e = σ * adjT i := by
  set r : Ch (□n) := (wordRun σ).chain with hr
  have hcr : cross r = σ := cross_wordRun σ
  have hrd : ∀ x ∈ r.dims, x = 1 := (wordRun σ).ones
  -- were `σ` to rise across every junction `d` deletes, `d` would fire in `σ`'s own order
  obtain ⟨i, hnotmem, hdesc⟩ : ∃ i : Fin (n - 1),
      (i : ℕ) + 1 ∉ boundaries d.dims ∧ σ (adjHi i) < σ (adjLo i) := by
    by_contra hc
    push Not at hc
    exact hne (cross_eq_of_rise hcr u fun i hi =>
      lt_of_le_of_ne (hc i hi) fun hz => adjLo_ne_adjHi i (σ.injective hz))
  obtain ⟨e, v, hce, hde⟩ := exists_atom_face hrd (hcr ▸ hdesc)
  refine ⟨i, e, hdesc, ⟨v⟩, ?_, by rw [hce, hcr]⟩
  -- the atom's one junction is one `d` lacks, so the atom face lands under `d`
  have hsub : boundaries d.dims ⊆ boundaries e.dims := by
    rw [hde, boundaries_atomComp]
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have := boundaries_subset_of_hom u ht
      rwa [ones_dims_eq hrd (wedgeDimSum_eq r.map), boundaries_ones] at this
    · simp only [Finset.mem_singleton]
      rintro rfl
      exact hnotmem ht
  obtain ⟨M, w, hMd⟩ := exists_coarsening (dimSum_dims_cube d) hsub
  exact ⟨(chain_ext_of_dims (v ≫ w) u hMd) ▸ w⟩

/-! ## Codimension-one faces meet one step up -/

/-- **Two codimension-one refinements of a chain meet in one face**, one further step up from each:
the meet deletes both junctions, and they are distinct. -/
theorem exists_join {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h₁ : codim u₁ = 1) (h₂ : codim u₂ = 1) (hne : d₁ ≠ d₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), codim v₁ = 1 ∧ codim v₂ = 1 := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp ((codim_eq_card_sdiff u₁).symm.trans h₁)
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp ((codim_eq_card_sdiff u₂).symm.trans h₂)
  have hsa : s ∈ boundaries a.dims :=
    (Finset.mem_sdiff.mp (hs ▸ Finset.mem_singleton_self s)).1
  have hta : t ∈ boundaries a.dims :=
    (Finset.mem_sdiff.mp (ht ▸ Finset.mem_singleton_self t)).1
  have hB₁ : boundaries d₁.dims = boundaries a.dims \ {s} := by
    rw [← hs, Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom u₁)]
  have hB₂ : boundaries d₂.dims = boundaries a.dims \ {t} := by
    rw [← ht, Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom u₂)]
  have hst : s ≠ t := fun hc =>
    hne (chain_ext_of_dims u₁ u₂ (boundaries_injective (by rw [hB₁, hB₂, hc])))
  -- deleting `s` and deleting `t` differ in exactly the other cut
  have hcut : ∀ {x y : ℕ}, x ≠ y → y ∈ boundaries a.dims →
      (boundaries a.dims \ {x}) \ (boundaries a.dims \ {y}) = {y} := by
    intro x y hxy hy
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not]
    exact ⟨fun h => h.2 h.1.1,
      fun h => ⟨⟨h ▸ hy, fun hc => hxy (hc.symm.trans h)⟩, fun _ => h⟩⟩
  refine ⟨e, v₁, v₂, ?_, ?_⟩
  · rw [codim_eq_card_sdiff, hb, Finset.sdiff_inter_self_left, hB₁, hB₂, hcut hst hta,
      Finset.card_singleton]
  · rw [codim_eq_card_sdiff, hb, Finset.inter_comm, Finset.sdiff_inter_self_left, hB₂, hB₁,
      hcut (Ne.symm hst) hsa, Finset.card_singleton]

/-! ## What the face two atoms meet in crosses

The two steps delete two junctions and the meet is a codimension-two face, so its junctions are
*exactly* the run's minus those two (`boundaries_of_meet`).  That pins its blocks, hence the
permutation that sorts them, hence its `cross`. -/

/-- **Two codimension-one steps out of a run delete exactly two junctions**, which is the room the
computation below runs on. -/
theorem length_of_two_steps {r d e : Ch (□n)} (hr : ∀ x ∈ r.dims, x = 1)
    (u : r ⟶ d) (v : d ⟶ e) (hu : codim u = 1) (hv : codim v = 1) :
    e.dims.length + 2 = n := by
  have h0 : degree r = 0 := (degree_eq_zero_iff r).mpr hr
  have h1 := degree_le_of_hom u
  have h2 := degree_le_of_hom v
  rw [codim] at hu hv
  have hd := degree_add_length e
  have hn := dimSum_dims_cube e
  omega

/-- **The face two atoms meet in has exactly their two junctions deleted.**  Each leg deletes its
own, and a codimension-two face has no room for a third. -/
theorem boundaries_of_meet {r d₁ d₂ e : Ch (□n)} {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    boundaries e.dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
  have hi := i.isLt
  have hj := j.isLt
  have hsub : boundaries e.dims ⊆ Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hle := le_dimSum_of_mem_boundaries ht
      rw [dimSum_dims_cube] at hle
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact notMem_boundaries_of_crossPerm_adjT u₁ hf₁ (boundaries_subset_of_hom v₁ ht)
      · exact notMem_boundaries_of_crossPerm_adjT u₂ hf₂ (boundaries_subset_of_hom v₂ ht)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hcut : ({(i : ℕ) + 1, (j : ℕ) + 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_range]
    omega
  have hcard2 : ({(i : ℕ) + 1, (j : ℕ) + 1} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hce := card_boundaries e.dims
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcut, Finset.card_range, hcard2]
  omega

/-- **The meet's crossing permutation, given the permutation `g` that sorts its beads.**  Only the
two deleted junctions can join an adjacent pair, so `cross_eq_of_sort`'s rise condition is just
`σ ∘ g` rising across each of them. -/
private theorem cross_of_meet {σ : Equiv.Perm (Fin n)} {r e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)}
    (hS : boundaries e.dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1})
    (w : r ⟶ e) (g : Equiv.Perm (Fin n))
    (hblk : ∀ x : Fin n, beadAt e.dims (g x) = beadAt e.dims x)
    (hgi : σ (g (adjLo i)) < σ (g (adjHi i))) (hgj : σ (g (adjLo j)) < σ (g (adjHi j))) :
    cross e = σ * g := by
  refine cross_eq_of_sort hr w g hblk fun k hk => ?_
  have hk' := mem_of_notMem_boundaries hS hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
  rcases hk' with hk' | hk'
  · obtain rfl : k = i := Fin.ext (by omega); exact hgi
  · obtain rfl : k = j := Fin.ext (by omega); exact hgj

/-- **Far cuts**: two atoms at distant cuts meet in the doubly sorted permutation. -/
theorem cross_of_meet_far {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 < (j : ℕ))
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hS := boundaries_of_meet (by omega : (i : ℕ) ≠ (j : ℕ)) hf₁ hf₂ v₁ v₂ hlen
  have hi' := i.isLt
  have hj' := j.isLt
  rw [mul_assoc]
  refine cross_of_meet hr hS (u₁ ≫ v₁) (adjT i * adjT j)
    (fun x => by
      rw [Equiv.Perm.mul_apply, beadAt_adjT_of_notMem (by rw [hS]; simp),
        beadAt_adjT_of_notMem (by rw [hS]; simp)]) ?_ ?_
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      adjT_adjLo_of_ne (by omega) (by omega), adjT_lo,
      adjT_adjHi_of_ne (by omega) (by omega), adjT_hi]
    exact hi
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_lo,
      adjT_adjHi_of_ne (by omega) (by omega), adjT_hi,
      adjT_adjLo_of_ne (by omega) (by omega)]
    exact hj

/-- **Consecutive cuts**: two atoms at adjacent cuts meet in the sorted three-window. -/
theorem cross_of_meet_braid {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1)
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j * adjT i := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hji : adjLo j = adjHi i := adjLo_eq_adjHi hij
  have hi' := i.isLt
  have hj' := j.isLt
  have hS := boundaries_of_meet (by omega : (i : ℕ) ≠ (j : ℕ)) hf₁ hf₂ v₁ v₂ hlen
  -- the three-window, reversed
  have gLoI : (adjT i * adjT j * adjT i) (adjLo i) = adjHi j := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_lo, ← hji, adjT_lo,
      adjT_adjHi_of_ne (k := i) (l := j) (by omega) (by omega)]
  have gHiI : (adjT i * adjT j * adjT i) (adjHi i) = adjHi i := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_hi,
      adjT_adjLo_of_ne (k := j) (l := i) (by omega) (by omega), adjT_lo]
  have gHiJ : (adjT i * adjT j * adjT i) (adjHi j) = adjLo i := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      adjT_adjHi_of_ne (k := i) (l := j) (by omega) (by omega), adjT_hi, hji, adjT_hi]
  rw [show σ * adjT i * adjT j * adjT i = σ * (adjT i * adjT j * adjT i) from by
    simp only [mul_assoc]]
  refine cross_of_meet hr hS (u₁ ≫ v₁) (adjT i * adjT j * adjT i)
    (fun x => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, beadAt_adjT_of_notMem (by rw [hS]; simp),
        beadAt_adjT_of_notMem (by rw [hS]; simp), beadAt_adjT_of_notMem (by rw [hS]; simp)])
    (by rw [gLoI, gHiI]; exact hji ▸ hj) (by rw [hji, gHiI, gHiJ]; exact hi)

end ChainCat
