import CubeChains.Cobordisms.Cobordism
import Mathlib.CategoryTheory.Category.Cat

/-!
# Future/Profunctor — the cobordism profunctor (statement-only stubs)

**Out of scope for the current build** (spec §"Out of scope"): statements only, no proofs.

## The program

A directed cobordism `W : X ⇒ Y` should induce a **profunctor**
`Φ_W : π₁(X)ᵒᵖ × π₁(Y) ⟶ Set`, where `π₁(-)` is the fundamental category (the localisation
of the d-path category of a precubical set).  Concretely `Φ_W(x, y)` is the set of directed
homotopy classes of d-paths `x ⇝ y` through `W.mid` rel endpoints, and composition of
cobordisms (the pushout) corresponds to the **coend** composition of profunctors:
`Φ_{W₂ ∘ W₁} ≅ Φ_{W₁} ⊗_{π₁(Y)} Φ_{W₂}`.

This assembles into a (lax) functor `dCob ⟶ Prof` into the bicategory of profunctors,
the directed analogue of the "cobordism ↦ linear map" of a TQFT.  The fundamental-category
construction connects to the repo's existing d-path machinery
(`Cylinder/PointedFunctor.lean`'s `DPathGrpdR := FreeGroupoid (RefineObj K)`).

See `Cobordisms/Cobordism.lean` (`DirectedCobordism`, `comp`).
-/

namespace PrecubicalSet.Future.Profunctor

open CategoryTheory

/-- Placeholder for the **fundamental category** `π₁(X)` of a precubical set (the d-path
category / its localisation).  To be defined via the repo's d-path machinery. -/
def FundamentalCat (_X : PrecubicalSet) : Type := PUnit

instance (X : PrecubicalSet) : Category (FundamentalCat X) := inferInstanceAs (Category PUnit)

/-- **The cobordism profunctor** `Φ_W : π₁(X)ᵒᵖ × π₁(Y) ⟶ Set` — d-homotopy classes of
directed paths through `W.mid` rel endpoints. -/
def cobProfunctor {X Y : PrecubicalSet} (_W : DirectedCobordism X Y) :
    (FundamentalCat X)ᵒᵖ × FundamentalCat Y ⥤ Type :=
  -- TODO(dCob): Future stub — the genuine profunctor of directed homotopy classes.
  sorry

/-- **Composition ↦ coend.**  The profunctor of a pushout-composite is the coend
(profunctor) composite of the factors. -/
theorem cobProfunctor_comp {X Y Z : PrecubicalSet}
    (_W₁ : DirectedCobordism X Y) (_W₂ : DirectedCobordism Y Z) :
    True := by
  -- TODO(dCob): Future stub — `Φ_{W₁.comp W₂} ≅ Φ_{W₁} ⊗_{π₁ Y} Φ_{W₂}`.
  trivial

end PrecubicalSet.Future.Profunctor
