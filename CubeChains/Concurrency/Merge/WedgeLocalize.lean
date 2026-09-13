import CubeChains.Concurrency.Merge.WedgeSlice
import CubeChains.Concurrency.Merge.WedgeSplit
import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Concurrency/Merge/WedgeLocalize — a localized slice splits off its first bead

`⋁(n :: rest)` *is* `□n ∨ ⋁rest` (`serialWedge_cons` is `rfl`), so the wedge splitting already is
the recursion on a dimension list — no reindexing, no transport, no `eqToHom`.

Both equivalences are **named lifts**, not `Localization.uniq`: the concatenation is
`Localization.prodLift` of `chConcat ⋙ Q`, the slice comparison is `Construction.lift` of
`wedgeChainsToOver ⋙ Q`, and `isEquivalence_of_fac` turns each into an equivalence without
disturbing its object map.  So both act on a `Q`-object by `rfl`, which is what a presentation
transported along either of them needs.
-/

open CategoryTheory CategoryTheory.MonoidalCategory BPSet CubeChains

namespace ChainCat

/-! ## The binary splitting, localized -/

section Binary

variable {X Y : BPSet}

/-- **`chConcat` followed by the localization is itself a localization**, at the product class. -/
theorem isLocalization_chConcat (h : (X ∨ Y).AdmitsAltitude) :
    (chConcat X Y ⋙ (W (X ∨ Y)).Q).IsLocalization ((W X).prod (W Y)) :=
  haveI := chConcat_isEquivalence h
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_prod_eq_inverseImage_chConcat X Y)

/-- **Concatenation, on the two localizations** — the `Q`-image of a pair of chains is the
`Q`-image of their concatenation, on the nose. -/
noncomputable def locChConcatFunctor (X Y : BPSet) :
    (W X).Localization × (W Y).Localization ⥤ (W (X ∨ Y)).Localization :=
  Localization.StrictUniversalPropertyFixedTarget.prodLift
    (W₁ := W X) (W₂ := W Y) (chConcat X Y ⋙ (W (X ∨ Y)).Q)
    fun _ _ fg hfg => Localization.inverts (W (X ∨ Y)).Q (W (X ∨ Y)) _
      ((W_chConcat_iff fg).mpr hfg)

/-- **`Ch X[W⁻¹] × Ch Y[W⁻¹] ≌ Ch (X ∨ Y)[W⁻¹]`** — `locChConcatFunctor`, which both localizations
make an equivalence. -/
noncomputable def locChConcatEquiv (h : (X ∨ Y).AdmitsAltitude) :
    (W X).Localization × (W Y).Localization ≌ (W (X ∨ Y)).Localization :=
  haveI := isLocalization_chConcat h
  haveI := Localization.Construction.prodIsLocalization (W X) (W Y)
  haveI := Localization.isEquivalence_of_fac ((W X).Q.prod (W Y).Q)
    (chConcat X Y ⋙ (W (X ∨ Y)).Q) ((W X).prod (W Y)) (locChConcatFunctor X Y)
    (Localization.StrictUniversalPropertyFixedTarget.prod_fac _ _)
  (locChConcatFunctor X Y).asEquivalence

end Binary

/-! ## The recursion on a dimension list -/

/-- **The first bead splits off**, with nothing to transport: `⋁(n :: rest)` is `□n ∨ ⋁rest`. -/
noncomputable def locChConsEquiv (n : ℕ+) (rest : List ℕ+) :
    (W (□(n : ℕ))).Localization × (W (⋁rest)).Localization
      ≌ (W (⋁(n :: rest))).Localization :=
  locChConcatEquiv (wedge2_admitsAltitude (cube_admitsAltitude (n : ℕ))
    (serialWedge_admitsAltitude rest))

/-! ## Read on the slices of `Ch Zbp`

`Over d` is `Ch (⋁d.dims)` and `W/d` is `W`, so the two localizations agree. -/

theorem isLocalization_wedgeChainsToOver (d : Ch Zbp) :
    (wedgeChainsToOver d ⋙ ((W Zbp).over (X := d)).Q).IsLocalization (W (⋁d.dims)) :=
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_eq_inverseImage_wedgeChainsToOver d)

/-- **`Ch(⋁d.dims)[W⁻¹] ≌ (Ch(Z)/d)[W/d⁻¹]`** — a chain of the wedge names the slice object it is,
so the comparison computes. -/
noncomputable def locWedgeEquivOver (d : Ch Zbp) :
    (W (⋁d.dims)).Localization ≌ ((W Zbp).over (X := d)).Localization :=
  haveI := isLocalization_wedgeChainsToOver d
  haveI := Localization.isEquivalence_of_fac (W (⋁d.dims)).Q
    (wedgeChainsToOver d ⋙ ((W Zbp).over (X := d)).Q) (W (⋁d.dims))
    (Localization.Construction.lift _ (Localization.inverts _ _))
    (Localization.Construction.fac _ _)
  (Localization.Construction.lift (wedgeChainsToOver d ⋙ ((W Zbp).over (X := d)).Q)
    (Localization.inverts _ _)).asEquivalence

/-- **`(Ch(Z)/d)[W/d⁻¹] ≌ Ch(⋁d.dims)[W⁻¹]`.** -/
noncomputable def locOverEquivWedge (d : Ch Zbp) :
    ((W Zbp).over (X := d)).Localization ≌ (W (⋁d.dims)).Localization :=
  (locWedgeEquivOver d).symm

end ChainCat
