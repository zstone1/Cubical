import CubeChains.Concurrency.Grading.ShuffleHom

/-!
# Concurrency/Grading/Coarser — a hom-set of serial wedges is an inclusion of boundary sets

Every refinement deletes boundaries and nothing else (`boundaries_subset_of_hom`,
`Concurrency/Grading/Degree`); conversely every deletion is realised, by merging one junction at a
time.  So `coarser_iff` and `nonempty_hom_iff` reduce the whole hom-set question to an inclusion of
`Finset ℕ`.

Once a hom-set is inhabited, factorisation through it is **unique** (`exists_factor`,
`factor_ext`), which pins the middle hom-set between the two extreme ones
(`exists_crossPerm_mid`).
-/

open CategoryTheory Equiv BPSet CubeChain

namespace CubeChains

/-- **Merging one junction at a time.**  Induct on the boundaries still to be removed. -/
private theorem nonempty_wedgeHom_aux : ∀ (k : ℕ) (d d' : List ℕ+), dimSum d = dimSum d' →
    boundaries d' ⊆ boundaries d → (boundaries d).card ≤ (boundaries d').card + k →
    Nonempty (⋁d ⟶ ⋁d') := by
  intro k
  induction k with
  | zero =>
      intro d d' _ hsub hk
      obtain rfl := boundaries_injective (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      exact ⟨𝟙 _⟩
  | succ k ih =>
      intro d d' hdim hsub hk
      by_cases heq : boundaries d = boundaries d'
      · obtain rfl := boundaries_injective heq
        exact ⟨𝟙 _⟩
      obtain ⟨t, htd, htd'⟩ :=
        Finset.exists_of_ssubset (hsub.ssubset_of_ne fun h => heq h.symm)
      have h0 : t ≠ 0 := fun h => htd' (h ▸ zero_mem_boundaries d')
      have hlast : t ≠ dimSum d := fun h =>
        htd' (by rw [h, hdim]; exact dimSum_mem_boundaries d')
      obtain ⟨l, r, p, q, rfl, rfl⟩ := exists_split_of_mem_boundaries d htd h0 hlast
      have hcut := boundaries_cut l r p q
      have hnm := notMem_boundaries_cut l r p q
      have hcard : (boundaries (l ++ p :: q :: r)).card
          = (boundaries (l ++ (p + q) :: r)).card + 1 := by
        rw [hcut, Finset.card_insert_of_notMem hnm]
      refine (ih (l ++ (p + q) :: r) d' ((dimSum_cut l r p q).symm.trans hdim) ?_ (by omega)).map
        fun ψ => ChainCat.Hom.φ (ChainCat.mergeHom l r p q) ≫ ψ
      intro x hx
      rcases Finset.mem_insert.mp (hcut ▸ hsub hx) with rfl | hx'
      · exact absurd hx htd'
      · exact hx'

end CubeChains

namespace ChainCat

open CubeChains

/-- **A coarsening is an inclusion of boundary sets.** -/
theorem coarser_iff {d d' : List ℕ+} :
    Coarser d d' ↔ dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d := by
  refine ⟨fun h => ?_, fun ⟨hdim, hsub⟩ => nonempty_wedgeHom_iff_coarser.mp
    (nonempty_wedgeHom_aux (boundaries d).card d d' hdim hsub (by omega))⟩
  obtain ⟨φ, -⟩ := coarser_iff_exists_pos.mp h
  exact ⟨serialWedge_dimSum_eq φ, boundaries_subset_of_wedgeHom φ⟩

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings**: a morphism exists precisely when the
target's boundaries are among the source's. -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ boundaries b.dims ⊆ boundaries a.dims :=
  ⟨fun ⟨f⟩ => ⟨strandsEq f, boundaries_subset_of_hom f⟩,
   fun h => (nonempty_wedgeHom_iff_coarser.mpr (coarser_iff.mpr h)).map
     fun φ => ⟨φ, Subsingleton.elim _ _⟩⟩

/-- **Comparable at all is comparable without braiding**: an inhabited hom-set holds the merge. -/
theorem exists_crossPerm_eq_one {a b : Ch Zbp} {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) : ∃ f : a ⟶ b, crossPerm h f = 1 := by
  obtain ⟨φ, hφ⟩ := coarser_iff_exists_pos.mp (nonempty_wedgeHom_iff_coarser.mp (hab.map Hom.φ))
  refine ⟨⟨φ, Subsingleton.elim _ _⟩, Equiv.ext fun i => ?_⟩
  obtain ⟨e, rfl⟩ := (strand a h).surjective i
  exact Fin.ext (by
    rw [Equiv.Perm.one_apply, crossPerm_strand, strand_val, strand_val]; exact hφ e)

/-- **A hom-set is inhabited exactly at a `blockOfPos`-coarsening** — `blockOfPos_pos` names the
bead of a strand, and only the bead clause is at stake. -/
theorem nonempty_hom_of_blockOfPos {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N)
    (hb : ∀ x y : Fin N, blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
        = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (y : ℕ) →
      blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
        = blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) (y : ℕ)) :
    Nonempty (zObj d ⟶ zObj d') := by
  refine (nonempty_wedgeHom_iff_coarser.mpr
    ⟨h.trans h'.symm, fun x y hxy => Fin.ext ?_⟩).map fun φ => ⟨φ, Subsingleton.elim _ _⟩
  rw [← blockOfPos_pos d' (flatEquiv (h.trans h'.symm) x),
    ← blockOfPos_pos d' (flatEquiv (h.trans h'.symm) y), pos_flatEquiv, pos_flatEquiv]
  exact hb (strand (zObj d) h x) (strand (zObj d) h y)
    (by rw [show ((strand (zObj d) h x : Fin N) : ℕ) = (pos x : ℕ) from rfl,
      show ((strand (zObj d) h y : Fin N) : ℕ) = (pos y : ℕ) from rfl,
      blockOfPos_pos d x, blockOfPos_pos d y, hxy])

/-! ### The two extremes

The run `1ᴺ` refines every shape on `N` events and one bead coarsens every one — the boundary
inclusions are `⊆ range (N+1)` and `{0, N} ⊆ ·`. -/

/-- **The run refines every shape on its event count.** -/
theorem nonempty_hom_ones {d : List ℕ+} {N : ℕ} (h : dimSum d = N) :
    Nonempty (zObj (𝟙^N) ⟶ zObj d) := by
  refine nonempty_hom_iff.mpr ⟨(dimSum_replicate N).trans h.symm, fun t ht => ?_⟩
  have hle : t ≤ N := h ▸ le_dimSum_of_mem_boundaries ht
  refine mem_boundaries_iff.mpr ⟨𝟙^t, 𝟙^(N - t), ?_, dimSum_replicate t⟩
  rw [show (zObj (𝟙^N)).dims = 𝟙^N from rfl, ← List.replicate_add,
    show t + (N - t) = N by omega]

/-- **One bead coarsens every shape on its event count.** -/
theorem nonempty_hom_single {d : List ℕ+} {m : ℕ+} (h : dimSum d = (m : ℕ)) :
    Nonempty (zObj d ⟶ zObj [m]) := by
  refine nonempty_hom_iff.mpr ⟨h.trans (dimSum_single m).symm, fun t ht => ?_⟩
  rw [show (zObj [m]).dims = [m] from rfl, boundaries_singleton] at ht
  rcases Finset.mem_insert.mp ht with rfl | ht'
  · exact zero_mem_boundaries d
  · rw [show (zObj d).dims = d from rfl, Finset.mem_singleton.mp ht', ← h]
    exact dimSum_mem_boundaries d

/-! ## Unique factorisation through an intermediate shape

Inside a bead of `m` the second factor preserves the event order, so the order the first factor
imposes on the source is read off the composite; across beads it is the bead order.  Two first
factors therefore differ by a monotone bijection of `beadEvent m.dims`, which is the identity. -/

variable {a m b : Ch Zbp}

/-- **The relative order inside a bead of `m` is read off the composite.** -/
private theorem pos_lt_of_factor {f : a ⟶ b} (u : a ⟶ m) (v : m ⟶ b) (huv : u ≫ v = f)
    {p q : beadEvent a.dims} (hb : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1)
    (hlt : pos (coordMap (Hom.φ u) p) < pos (coordMap (Hom.φ u) q)) :
    pos (coordMap (Hom.φ f) p) < pos (coordMap (Hom.φ f) q) := by
  have hcomp : ∀ w, coordMap (Hom.φ f) w = coordMap (Hom.φ v) (coordMap (Hom.φ u) w) := fun w => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  rw [hcomp, hcomp]
  exact coordMap_pos_lt_of_fst_eq (Hom.φ v) hb hlt

/-- **Two factorisations impose the same order on the source.** -/
private theorem lt_of_factor_of_factor {f : a ⟶ b} {u u' : a ⟶ m} {v v' : m ⟶ b}
    (huv : u ≫ v = f) (hu'v' : u' ≫ v' = f) {p q : beadEvent a.dims}
    (hlt : coordMap (Hom.φ u) p < coordMap (Hom.φ u) q) :
    coordMap (Hom.φ u') p < coordMap (Hom.φ u') q := by
  have hp := coordMap_fst_congr (Hom.φ u') (Hom.φ u) p
  have hq := coordMap_fst_congr (Hom.φ u') (Hom.φ u) q
  by_cases hbead : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1
  · have hf := pos_lt_of_factor u v huv hbead hlt
    rcases lt_trichotomy (coordMap (Hom.φ u') p) (coordMap (Hom.φ u') q) with h | h | h
    · exact h
    · exact absurd (congrArg (coordMap (Hom.φ u)) ((coordMapEquiv (Hom.φ u')).injective h))
        (ne_of_lt hlt)
    · exact absurd (pos_lt_of_factor u' v' hu'v' (by rw [hp, hq, hbead]) h) (asymm hf)
  · refine pos_lt_of_fst_lt ?_
    rw [hp, hq]
    exact lt_of_le_of_ne (fst_le_of_pos_lt hlt) fun hc => hbead (Fin.ext hc)

/-- **The two factors are determined.**  A bijection of events monotone for the event order
preserves the flattening (`pos_eq_of_monotone`), hence is the identity. -/
theorem factor_ext {f : a ⟶ b} {g g' : a ⟶ m} {e e' : m ⟶ b}
    (h : g ≫ e = f) (h' : g' ≫ e' = f) : g = g' ∧ e = e' := by
  have hmono : Monotone ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))) := by
    intro x y hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · have hx : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm x) = x :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply x
      have hy : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm y) = y :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply y
      exact le_of_lt (lt_of_factor_of_factor h h' (by rw [hx, hy]; exact hlt))
  have hGG : coordMapEquiv (Hom.φ g) = coordMapEquiv (Hom.φ g') := by
    refine Equiv.ext fun p => ?_
    have hp := pos_eq_of_monotone hmono
      ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))).bijective
      (coordMapEquiv (Hom.φ g) p)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hp
    exact (pos.injective (Fin.ext hp)).symm
  have hgg : ∀ p, coordMap (Hom.φ g) p = coordMap (Hom.φ g') p := Equiv.ext_iff.mp hGG
  have hv : ∀ (u : a ⟶ m) (v : m ⟶ b), u ≫ v = f → ∀ p,
      coordMap (Hom.φ v) (coordMap (Hom.φ u) p) = coordMap (Hom.φ f) p := fun u v huv p => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  refine ⟨hom_ext' (wedgeHom_ext hGG), hom_ext' (wedgeHom_ext (Equiv.ext fun y => ?_))⟩
  obtain ⟨p, rfl⟩ := (coordMapEquiv (Hom.φ g)).surjective y
  change coordMap (Hom.φ e) (coordMap (Hom.φ g) p) = coordMap (Hom.φ e') (coordMap (Hom.φ g) p)
  rw [hv g e h, hgg p, hv g' e' h']

/-- **Factorisation through an intermediate shape.**  Once `a ⟶ m ⟶ b` is possible at all, every
refinement `a ⟶ b` factors through `m` — in exactly one way, by `factor_ext`.  The second factor
sends the `k`-th event of the bead `j` of `m` to the `k`-th smallest event of `b` in the image,
under the composite, of the events sitting in that bead. -/
theorem exists_factor (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b)) (f : a ⟶ b) :
    ∃ (g : a ⟶ m) (e : m ⟶ b), g ≫ e = f := by
  obtain ⟨h₁, hb₁⟩ := nonempty_wedgeHom_iff_coarser.mp (ham.map Hom.φ)
  obtain ⟨h₂, hb₂⟩ := nonempty_wedgeHom_iff_coarser.mp (hmb.map Hom.φ)
  obtain ⟨u, v, hu, hv, huv⟩ :=
    exists_isShuffle_factor hb₁ hb₂ (isShuffle_coordMapEquiv (Hom.φ f))
  obtain ⟨γ, hγ⟩ := exists_coordMapEquiv_eq hu
  obtain ⟨ε, hε⟩ := exists_coordMapEquiv_eq hv
  refine ⟨Hom.mk γ (Subsingleton.elim _ _), Hom.mk ε (Subsingleton.elim _ _), ?_⟩
  refine hom_ext' (wedgeHom_ext (Equiv.ext fun p => ?_))
  change coordMap (γ ≫ ε) p = coordMap (Hom.φ f) p
  rw [coordMap_comp, Function.comp_apply,
    show coordMap γ p = u p from Equiv.ext_iff.mp hγ p,
    show coordMap ε (u p) = v (u p) from Equiv.ext_iff.mp hε (u p)]
  exact huv p

/-! ## The middle hom-set, from the two extremes

`o ⟶ a ⟶ b ⟶ z` with the outer legs crossing nothing.  Uniqueness of the factorisation of
`o ⟶ z` through `b` forces the leg out of `b` to be the merge, so the crossing permutation of
`a ⟶ b` is the one the outer legs already carry. -/

/-- **Interpolation**: a permutation realised at both extremes is realised in the middle.  This is
`Ch Zbp`'s hom-set classification with no coordinates in sight — a composite of cuts is what
`exists_factor` produces, and `factor_ext` is what makes it unique. -/
theorem exists_crossPerm_mid {o z : Ch Zbp} {N : ℕ} {ho : dimSum o.dims = N}
    {ha : dimSum a.dims = N} {hb : dimSum b.dims = N} {σ : Equiv.Perm (Fin N)}
    {t : o ⟶ a} (ht : crossPerm ho t = 1) {s : b ⟶ z} (hs : crossPerm hb s = 1)
    (hab : Nonempty (a ⟶ b)) {u : o ⟶ b} (hu : crossPerm ho u = σ)
    {g : a ⟶ z} (hg : crossPerm ha g = σ) :
    ∃ f : a ⟶ b, crossPerm ha f = σ := by
  obtain ⟨f, v, hfv⟩ := exists_factor hab ⟨s⟩ g
  have hv : v = s :=
    (factor_ext (g := t ≫ f) (e := v) (f := u ≫ s)
      (hom_ext_of_crossPerm (h := ho) (by
        rw [Category.assoc, hfv, crossPerm_comp ho t g, crossPerm_comp ho u s, ht, hs, hu, hg,
          mul_one, one_mul])) rfl).2
  refine ⟨f, ?_⟩
  have h := crossPerm_comp ha f v
  rw [hfv, hg, hv, hs, one_mul] at h
  exact h.symm

end ChainCat
