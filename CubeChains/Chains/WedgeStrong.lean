import CubeChains.Chains.WedgeMonoidal
import CubeChains.Chains.WedgeLaxMonoidal
import CubeChains.Chains.SegalProd
import CubeChains.Chains.SegalAltitude
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Chains/WedgeStrong — where the wedge tensor is *strong* for `Ch`

Strict `Functor.Monoidal chFunctor` is unavailable: the tensorator `μ = chConcat` is an
*equivalence* (`chSegal`), never an isomorphism in `Cat` (a chain of `X ∨ Y` splits as an append
only up to iso).  Equivalence ≠ iso 1-categorically, so `IsIso μ` is false and mathlib's
`Monoidal.ofLaxMonoidal` cannot fire — strong monoidality here is bicategorical.

The honest home for "strong": the **altitude-admitting** objects form a monoidal full subcategory
`AltBP` (closed under `∨` by `wedge2_admitsAltitude`, containing the unit `□0` by
`cube_admitsAltitude`), and there `chConcat` is a genuine equivalence — the Segal splitting, stated
exactly where it holds.
-/

open CategoryTheory MonoidalCategory ChainCat BPSet

namespace ChainCat

/-- Admitting an altitude, as a property of the wedge-monoidal `WedgeBP`. -/
def AdmitsAlt : ObjectProperty WedgeBP := fun X => BPSet.AdmitsAltitude X

instance : AdmitsAlt.ContainsUnit := ⟨cube_admitsAltitude 0⟩

instance : AdmitsAlt.TensorLE AdmitsAlt AdmitsAlt :=
  ⟨fun _ _ hX hY => wedge2_admitsAltitude hX hY⟩

instance : AdmitsAlt.IsMonoidal where

/-- **The altitude-admitting monoidal subcategory.**  A full subcategory of `WedgeBP`, monoidal
(closed under `∨`, contains `□0`) via `ObjectProperty.fullMonoidalSubcategory`. -/
abbrev AltBP := AdmitsAlt.FullSubcategory

/-- **The Segal equivalence, stated where it holds.**  On altitude-admitting objects the wedge
tensorator `chConcat` (= the lax `μ` of `chFunctor`) is a genuine equivalence of chain
categories.  This is "strong monoidality up to equivalence" for the wedge. -/
noncomputable def chConcatEquiv (X Y : AltBP) :
    Ch X.1 × Ch Y.1 ≌ Ch (wedge2 X.1 Y.1) :=
  chSegal X.1 Y.1 (wedge2_admitsAltitude X.2 Y.2)

@[simp] theorem chConcatEquiv_functor (X Y : AltBP) :
    (chConcatEquiv X Y).functor = chConcat X.1 Y.1 := rfl

/-- **The strong sense, tied to the lax functor.**  The lax tensorator `μ` of `chFunctor`, on
altitude-admitting objects, *is* the underlying functor of the Segal equivalence `chConcatEquiv` —
i.e. `μ` is an equivalence there (though not an iso in `Cat`, so no strict `Functor.Monoidal`). -/
theorem laxμ_eq_chConcatEquiv (X Y : AltBP) :
    Functor.LaxMonoidal.μ chFunctorW X.1 Y.1 = (chConcatEquiv X Y).functor.toCatHom := rfl

end ChainCat
