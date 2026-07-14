import CubeChains.Salvetti.ConcGroupoid
import Mathlib.CategoryTheory.Localization.Prod

/-!
# Salvetti/FreeGroupoidProd — groupoidification preserves binary products

`FreeGroupoid C` is the localization of `C` at *all* its morphisms, and a product of localization
functors is a localization functor (`Functor.IsLocalization.prod`).  Since `⊤ ×ₚ ⊤ = ⊤`, both

    of (C × D) : C × D ⥤ FreeGroupoid (C × D)
    of C ×ᶠ of D : C × D ⥤ FreeGroupoid C × FreeGroupoid D

localize `C × D` at `⊤`, so `Localization.uniq` identifies their targets:

    FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D.

Applied to `salSumEquiv`, this splits the concurrency braid groupoid of a wedge into one factor per
bead: `ConcGrpd (⋁dims) ≌ ∏ᵢ FreeGroupoid (Sal (braidCOM dᵢ))` — a product of pure braid groupoids.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

namespace FreeGroupoid

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The morphism property `⊤` on a product is the product of the `⊤`s. -/
theorem top_prod_top :
    (⊤ : MorphismProperty C).prod (⊤ : MorphismProperty D) = (⊤ : MorphismProperty (C × D)) := by
  ext X Y f
  simp [MorphismProperty.prod]

/-- Groupoidifying both factors separately localizes `C × D` at all of its morphisms. -/
instance ofProdIsLocalization :
    ((of C).prod (of D)).IsLocalization (⊤ : MorphismProperty (C × D)) :=
  top_prod_top C D ▸
    (inferInstance : ((of C).prod (of D)).IsLocalization
      ((⊤ : MorphismProperty C).prod (⊤ : MorphismProperty D)))

end FreeGroupoid

/-- **Groupoidification preserves binary products.** -/
noncomputable def freeGroupoidProdEquiv (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] :
    FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D :=
  Localization.uniq (FreeGroupoid.of (C × D))
    ((FreeGroupoid.of C).prod (FreeGroupoid.of D)) ⊤

/-- `freeGroupoidProdEquiv` is the expected map: it sends `mk (X, Y)` to `(mk X, mk Y)`.

    C × D ------ of (C × D) -----> FreeGroupoid (C × D)
      ‖                                     |
      ‖                                (equiv).functor
      ‖                                     v
    C × D -- of C ×ᶠ of D --> FreeGroupoid C × FreeGroupoid D
-/
noncomputable def freeGroupoidProdEquivComp (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] :
    FreeGroupoid.of (C × D) ⋙ (freeGroupoidProdEquiv C D).functor ≅
      (FreeGroupoid.of C).prod (FreeGroupoid.of D) :=
  Localization.compUniqFunctor _ _ _

end CategoryTheory

namespace CubeChains

open CategoryTheory

/-- **The concurrency braid groupoid of a direct sum splits.**  With `salSumEquiv`, this is the
groupoid shadow of the wedge decomposition: independent beads contribute independent braidings. -/
noncomputable def concSumEquiv {E₁ E₂ : Type*} (L₁ : COM E₁) (L₂ : COM E₂) :
    FreeGroupoid (Sal (L₁.directSum L₂)) ≌ FreeGroupoid (Sal L₁) × FreeGroupoid (Sal L₂) :=
  (freeGroupoidCongr (COM.salSumEquiv L₁ L₂)).trans (freeGroupoidProdEquiv (Sal L₁) (Sal L₂))

/-- The per-bead product of braid groupoids of a serial wedge, folded like `braidDirectSum`. -/
def SerialConcGrpd : List ℕ+ → Type
  | [] => FreeGroupoid (Sal (braidCOM 0))
  | n :: rest => FreeGroupoid (Sal (braidCOM (n : ℕ))) × SerialConcGrpd rest

instance instCategorySerialConcGrpd : (dims : List ℕ+) → Category (SerialConcGrpd dims)
  | [] => inferInstanceAs (Category (FreeGroupoid (Sal (braidCOM 0))))
  | n :: rest =>
      letI := instCategorySerialConcGrpd rest
      inferInstanceAs (Category (FreeGroupoid (Sal (braidCOM (n : ℕ))) × SerialConcGrpd rest))

/-- **The concurrency braid groupoid of a serial wedge is the product of its beads' braid
groupoids.**  Each bead `dᵢ` contributes `FreeGroupoid (Sal (braidCOM dᵢ))`, whose vertex groups are
the pure braid groups `P dᵢ`. -/
noncomputable def concSerialEquiv : (dims : List ℕ+) →
    FreeGroupoid (Sal (braidDirectSum dims)) ≌ SerialConcGrpd dims
  | [] => CategoryTheory.Equivalence.refl
  | n :: rest =>
      (concSumEquiv (braidCOM (n : ℕ)) (braidDirectSum rest)).trans
        (CategoryTheory.Equivalence.prod CategoryTheory.Equivalence.refl
          (concSerialEquiv rest))

/-- The wedge form of `concSerialEquiv`: the concurrency braid groupoid of `⋁dims`. -/
noncomputable def concWedgeSerialEquiv (dims : List ℕ+) :
    ConcGrpd (⋁dims) ≌ SerialConcGrpd dims :=
  (concWedgeEquiv dims).symm.trans (concSerialEquiv dims)

end CubeChains
