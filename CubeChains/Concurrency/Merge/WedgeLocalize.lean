import CubeChains.Concurrency.Merge.WedgeSlice
import CubeChains.Concurrency.Merge.WedgeSplit
import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Concurrency/Merge/WedgeLocalize — a localized slice splits off its first bead

`⋁(n :: rest)` *is* `□n ∨ ⋁rest` (`serialWedge_cons` is `rfl`), so the wedge splitting already is
the recursion on a dimension list — no reindexing, no transport, no `eqToHom`.  Localizing it needs
only the **binary** `IsLocalization.prod`: `chConcat` is an equivalence carrying `(W X).prod (W Y)`
to `W (X ∨ Y)`, so `chConcat ⋙ Q` *is* a localization of `Ch X × Ch Y`, and `Localization.uniq`
compares it with the product of the two localizations.

The recursion is on the cons rather than over `Fin a.length` because `Presents.prod` is binary and
there is no `Presents.pi`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory BPSet CubeChains

namespace ChainCat

/-! ## The binary splitting, localized -/

section Binary

variable {X Y : BPSet}

/-- **`chConcat` followed by the localization is itself a localization**, at the product class.
Everything below is `Localization.uniq` applied to it. -/
theorem isLocalization_chConcat (h : (X ∨ Y).AdmitsAltitude) :
    (chConcat X Y ⋙ (W (X ∨ Y)).Q).IsLocalization ((W X).prod (W Y)) :=
  haveI := chConcat_isEquivalence h
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_prod_eq_inverseImage_chConcat X Y)

/-- **`Ch (X ∨ Y)[W⁻¹] ≌ Ch X[W⁻¹] × Ch Y[W⁻¹]`** — `IsLocalization.prod` on the left,
`isLocalization_chConcat` on the right, compared by `Localization.uniq`. -/
noncomputable def locChConcatEquiv (h : (X ∨ Y).AdmitsAltitude) :
    (W X).Localization × (W Y).Localization ≌ (W (X ∨ Y)).Localization :=
  haveI := isLocalization_chConcat h
  Localization.uniq ((W X).Q.prod (W Y).Q) (chConcat X Y ⋙ (W (X ∨ Y)).Q) ((W X).prod (W Y))

end Binary

/-! ## The recursion on a dimension list -/

/-- **The first bead splits off**, with nothing to transport: `⋁(n :: rest)` is `□n ∨ ⋁rest`. -/
noncomputable def locChConsEquiv (n : ℕ+) (rest : List ℕ+) :
    (W (□(n : ℕ))).Localization × (W (⋁rest)).Localization
      ≌ (W (⋁(n :: rest))).Localization :=
  locChConcatEquiv (wedge2_admitsAltitude (cube_admitsAltitude (n : ℕ))
    (serialWedge_admitsAltitude rest))

/-! ## Read on the slices of `Ch Zbp`

`Over (zObj d)` is `Ch (⋁d)` and `W/d` is `W`, so the two localizations agree. -/

theorem isLocalization_overToWedgeChains (d : List ℕ+) :
    (overToWedgeChains d ⋙ (W (⋁d)).Q).IsLocalization ((W Zbp).over (X := zObj d)) :=
  Functor.IsLocalization.of_inverseImage _ _ _ _ (over_W_eq_inverseImage d)

/-- **`(Ch(Z)/d)[W/d⁻¹] ≌ Ch(⋁d)[W⁻¹]`.** -/
noncomputable def locOverEquivWedge (d : List ℕ+) :
    ((W Zbp).over (X := zObj d)).Localization ≌ (W (⋁d)).Localization :=
  haveI := isLocalization_overToWedgeChains d
  Localization.uniq ((W Zbp).over (X := zObj d)).Q (overToWedgeChains d ⋙ (W (⋁d)).Q)
    ((W Zbp).over (X := zObj d))

end ChainCat
