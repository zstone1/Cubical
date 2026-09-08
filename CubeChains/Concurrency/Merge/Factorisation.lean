import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/Factorisation — a factorisation is its middle shape

The two-step factorisations of a refinement `f : a ⟶ b` are the shapes whose junctions lie between
the two ends': `factorisationEquiv`.  Both halves are already in `Concurrency/Grading/Coarser` —
`exists_factor` for existence and `factor_ext` for uniqueness of the legs — and the point of
packaging them as an equivalence is that *counting* factorisations becomes counting shapes in an
interval of the junction lattice.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace ChainCat

variable {a b : Ch Zbp}

/-- A two-step factorisation of a refinement. -/
structure Factorisation (f : a ⟶ b) where
  /-- The intermediate shape. -/
  mid : Ch Zbp
  /-- The first leg. -/
  fst : a ⟶ mid
  /-- The second leg. -/
  snd : mid ⟶ b
  /-- …and they compose to `f`. -/
  comp : fst ≫ snd = f

/-- **A factorisation is pinned by its middle shape** — the legs are forced (`factor_ext`). -/
theorem Factorisation.ext {f : a ⟶ b} : ∀ {F G : Factorisation f}, F.mid = G.mid → F = G := by
  rintro ⟨m, g, e, hge⟩ ⟨m', g', e', hge'⟩ (rfl : m = m')
  obtain ⟨hg, he⟩ := factor_ext hge hge'
  subst hg
  subst he
  rfl

/-- The shapes that can sit in the middle: the interval between the two ends' junctions. -/
abbrev MidShape (a b : Ch Zbp) : Type :=
  {m : Ch Zbp // boundaries b.dims ⊆ boundaries m.dims ∧ boundaries m.dims ⊆ boundaries a.dims}

theorem dimSum_of_midShape (f : a ⟶ b) (m : MidShape a b) : dimSum m.1.dims = dimSum a.dims := by
  have hab : dimSum a.dims = dimSum b.dims := dimSum_eq_of_hom f
  have h1 : dimSum m.1.dims ≤ dimSum a.dims :=
    le_dimSum_of_mem_boundaries (m.2.2 (dimSum_mem_boundaries m.1.dims))
  have h2 : dimSum a.dims ≤ dimSum m.1.dims := by
    refine le_dimSum_of_mem_boundaries (m.2.1 ?_)
    rw [hab]
    exact dimSum_mem_boundaries b.dims
  omega

theorem nonempty_hom_midShape_left (f : a ⟶ b) (m : MidShape a b) : Nonempty (a ⟶ m.1) :=
  nonempty_hom_iff.mpr ⟨(dimSum_of_midShape f m).symm, m.2.2⟩

theorem nonempty_hom_midShape_right (f : a ⟶ b) (m : MidShape a b) : Nonempty (m.1 ⟶ b) :=
  nonempty_hom_iff.mpr ⟨(dimSum_of_midShape f m).trans (dimSum_eq_of_hom f), m.2.1⟩

/-- **The two-step factorisations of `f` are the interval `boundaries b ⊆ · ⊆ boundaries a`.**
Every shape in the interval carries a factorisation (`exists_factor`, through `nonempty_hom_iff`)
and the legs are forced (`factor_ext`), so counting factorisations is counting shapes. -/
noncomputable def factorisationEquiv (f : a ⟶ b) : Factorisation f ≃ MidShape a b where
  toFun F := ⟨F.mid, boundaries_subset_of_hom F.snd, boundaries_subset_of_hom F.fst⟩
  invFun m :=
    ⟨m.1,
      (exists_factor (nonempty_hom_midShape_left f m) (nonempty_hom_midShape_right f m) f).choose,
      (exists_factor (nonempty_hom_midShape_left f m)
        (nonempty_hom_midShape_right f m) f).choose_spec.choose,
      (exists_factor (nonempty_hom_midShape_left f m)
        (nonempty_hom_midShape_right f m) f).choose_spec.choose_spec⟩
  left_inv _ := Factorisation.ext rfl
  right_inv _ := rfl

end ChainCat
