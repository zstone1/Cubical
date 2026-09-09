import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Machinery/Localization/ElementsProd — the external product of two `Type`-valued functors

For `F : C ⥤ Type` and `G : D ⥤ Type`, the external product `F ⊠ G : C × D ⥤ Type`,
`(F ⊠ G)(c,d) = F c × G d` — what `BPSet.prod` is the diagonal of.
-/

open CategoryTheory MonoidalCategory

namespace CategoryTheory.CategoryOfElements

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The **external product** of `F : C ⥤ Type` and `G : D ⥤ Type`: the cartesian monoidal
structure on `Type` makes `(F ⊠ G)(c,d) = F c × G d` hold definitionally. -/
def extProd (F : C ⥤ Type w) (G : D ⥤ Type w) : C × D ⥤ Type w := externalProduct F G

end CategoryTheory.CategoryOfElements
