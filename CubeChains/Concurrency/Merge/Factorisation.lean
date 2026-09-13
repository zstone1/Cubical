import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/Factorisation — a factorisation is its middle shape

The two-step factorisations of a refinement `f : a ⟶ b` are the shapes whose junctions lie between
the two ends': `factorisationEquiv`.  Both halves are already in `Concurrency/Grading/Coarser` —
`exists_factor` for existence and `factor_ext` for uniqueness of the legs — and the point of
packaging them as an equivalence is that *counting* factorisations becomes counting shapes in an
interval of the junction lattice.

The middle is a chain of `K`, but only its **shape** is free: the chain over that shape is the
cartesian lift of the second leg (`Factorisation.ext_dims`), so the count does not see `K`.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace ChainCat

variable {K : BPSet} {a b : Ch K}

/-- A two-step factorisation of a refinement. -/
structure Factorisation (f : a ⟶ b) where
  /-- The intermediate chain. -/
  mid : Ch K
  /-- The first leg. -/
  fst : a ⟶ mid
  /-- The second leg. -/
  snd : mid ⟶ b
  /-- …and they compose to `f`. -/
  comp : fst ≫ snd = f

/-- **A factorisation is pinned by its middle** — the legs are forced (`factor_ext`). -/
theorem Factorisation.ext {f : a ⟶ b} : ∀ {F G : Factorisation f}, F.mid = G.mid → F = G := by
  rintro ⟨m, g, e, hge⟩ ⟨m', g', e', hge'⟩ (rfl : m = m')
  obtain ⟨hg, he⟩ := factor_ext hge hge'
  subst hg
  subst he
  rfl

/-- **…and in fact by its middle *shape*** — the two second legs agree, and a second leg carries
the chain over the shape (`eq_of_join_of_dims_eq`). -/
theorem Factorisation.ext_dims {f : a ⟶ b} {F G : Factorisation f} (h : F.mid.dims = G.mid.dims) :
    F = G :=
  Factorisation.ext (eq_of_join_of_dims_eq h (F.comp.trans G.comp.symm))

/-- The shapes that can sit in the middle: the interval between the two ends' junctions. -/
abbrev MidShape (a b : Ch K) : Type :=
  {m : Ch Zbp // boundaries b.dims ⊆ boundaries m.dims ∧ boundaries m.dims ⊆ boundaries a.dims}

/-- **A middle shape is comparable to both ends** — each end's junctions sit on the right side of
the interval, and both totals are pinned by the outermost junction. -/
theorem nonempty_hom_midShape (f : a ⟶ b) (m : MidShape a b) :
    Nonempty (zObj a.dims ⟶ m.1) ∧ Nonempty (m.1 ⟶ zObj b.dims) := by
  have hab : dimSum a.dims = dimSum b.dims := dimSum_eq_of_hom f
  have hm : dimSum m.1.dims = dimSum a.dims := by
    have h1 := le_dimSum_of_mem_boundaries (m.2.2 (dimSum_mem_boundaries m.1.dims))
    have h2 := le_dimSum_of_mem_boundaries (m.2.1 (hab ▸ dimSum_mem_boundaries b.dims))
    omega
  exact ⟨nonempty_hom_iff.mpr ⟨hm.symm, m.2.2⟩, nonempty_hom_iff.mpr ⟨hm.trans hab, m.2.1⟩⟩

/-- The second leg of the shape's own factorisation downstairs, with its square — the one
`Classical.choice` in sight, and the lift along the fibration is then forced. -/
private noncomputable def midSnd (f : a ⟶ b) (m : MidShape a b) :
    {g : m.1 ⟶ zObj b.dims // ∃ e : zObj a.dims ⟶ m.1, e ≫ g = baseMap f} :=
  ⟨(exists_factor (nonempty_hom_midShape f m).1 (nonempty_hom_midShape f m).2
      (baseMap f)).choose_spec.choose,
   _, (exists_factor (nonempty_hom_midShape f m).1 (nonempty_hom_midShape f m).2
      (baseMap f)).choose_spec.choose_spec⟩

/-- **The two-step factorisations of `f` are the interval `boundaries b ⊆ · ⊆ boundaries a`.**
Every shape in the interval carries a factorisation (`exists_factor` downstairs, lifted) and the
factorisation is pinned by that shape, so counting factorisations is counting shapes. -/
noncomputable def factorisationEquiv (f : a ⟶ b) : Factorisation f ≃ MidShape a b where
  toFun F := ⟨zObj F.mid.dims, boundaries_subset_of_hom F.snd, boundaries_subset_of_hom F.fst⟩
  invFun m := ⟨liftChain b (midSnd f m).1, liftFst (midSnd f m).2.choose_spec,
    liftSnd b (midSnd f m).1, liftFst_comp_liftSnd (midSnd f m).2.choose_spec⟩
  left_inv _ := Factorisation.ext_dims rfl
  right_inv _ := Subtype.ext (Obj.eq_of_dims rfl)

end ChainCat
