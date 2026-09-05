import CubeChains.Machinery.Presentation.Glue
import Mathlib.CategoryTheory.Category.Cat.Colimit

/-!
# Machinery/Presentation/SliceColimit — a colimit on both sides

`overLocFunctor W : C ⥤ Cat` is the diagram of localized slices — a strict functor, because
`overMapLoc` is — and `C[W⁻¹]` is its colimit: `overCoconeLocEquiv` *is* that universal property.
Read with `presentsSliceColimit`, the colimit of the slice presentations presents the colimit of
the localized slices.

That last is a corollary of `presentsSliceColimit` and of nothing more general: levelwise
equivalent diagrams need **not** have equivalent strict colimits (`1 ⇉ SingleObj ℤ` against
`1 ⇉ 1`), and a strict section does not repair it, since `colim` is a 1-functor and cannot
transport the other composite's natural iso.
-/

universe u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

/-! ## `C[W⁻¹]` is the colimit of its localized slices -/

/-- The localized slices as a diagram of categories. -/
noncomputable def overLocFunctor : C ⥤ Cat.{u, u} where
  obj c := Cat.of ((W.over (X := c)).Localization)
  map u := (overMapLoc W u).toCatHom
  map_id c := Cat.ext (overMapLoc_id W c)
  map_comp u v := Cat.ext (overMapLoc_comp W u v)

/-- The localization functor, restricted to the slice over `c`. -/
noncomputable def overLocLeg (c : C) : (W.over (X := c)).Localization ⥤ W.Localization :=
  (overCoconeLocEquiv W (𝟭 W.Localization)).obj c

/-- **A functor on `C[W⁻¹]` postcomposes the legs** — `overCoconeLocEquiv` is natural in its
target, which is what makes the legs a *colimiting* cocone and not merely a cocone. -/
theorem overLocLeg_comp {E : Type u} [Category.{u} E] (Φ : W.Localization ⥤ E) (c : C) :
    overLocLeg W c ⋙ Φ = (overCoconeLocEquiv W Φ).obj c :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overLocLeg, overCoconeLocEquiv_apply W (𝟭 W.Localization) c,
      overCoconeLocEquiv_apply W Φ c, Functor.comp_id, Functor.assoc])

/-- The legs, as a cocone on the localized slices. -/
noncomputable def overLocCocone : Cocone (overLocFunctor W) where
  pt := Cat.of W.Localization
  ι :=
    { app := fun c => (overLocLeg W c).toCatHom
      naturality := fun _ _ u =>
        Cat.ext (((overCoconeLocEquiv W (𝟭 W.Localization)).w u).trans
          (Functor.comp_id _).symm) }

/-- **`C[W⁻¹]` is the colimit of its localized slices.** -/
noncomputable def isColimitOverLocCocone : IsColimit (overLocCocone W) where
  desc s := Cat.Hom.ofFunctor ((overCoconeLocEquiv W).symm
    { obj := fun c => (s.ι.app c).toFunctor
      w := fun {_ _} u => congrArg Cat.Hom.toFunctor (s.w u) })
  fac s c := Cat.ext ((overLocLeg_comp W _ c).trans
    (congrArg (fun G : OverCoconeLoc W ↥s.pt => G.obj c)
      ((overCoconeLocEquiv W).apply_symm_apply _)))
  uniq _s m h := Cat.ext ((Equiv.eq_symm_apply _).2 (OverCoconeLoc.ext W fun c =>
    (overLocLeg_comp W m.toFunctor c).symm.trans (congrArg Cat.Hom.toFunctor (h c))))

/-! ## The colimit of the slice presentations, against the colimit of the localized slices -/

namespace Polygraph

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (V : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
  (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f)
  (hthin : ∀ d : D, Quiver.IsThin ((V.over (X := d)).Localization))
  (R : SliceSkeleton V p)

include hP hthin R in
/-- **The colimit of the slice presentations presents the colimit of the localized slices** — a
corollary of `presentsSliceColimit`, read through `isColimitOverLocCocone`. -/
noncomputable def presentsColimitOfLocalizedSlices :
    Presents (colimit (elementsPoly X P))
      ↥(colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  (presentsSliceColimit X V p hP hthin R).transport
    (Cat.equivOfIso ((isColimitOverLocCocone _).coconePointUniqueUpToIso (colimit.isColimit _)))

include hP hthin R in
/-- **…so the colimit of the presented slices is the colimit of the localized ones**, the same
statement with the presentation cancelled on the left by `presentsColimit`. -/
noncomputable def colimitPresentedEquivColimitLoc :
    ↥(colimit (elementsPoly X P ⋙ presentedFunctor.{u, u})) ≌
      ↥(colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  (presentsColimit (elementsPoly X P)).equiv.symm.trans
    (presentsColimitOfLocalizedSlices X V p hP hthin R).equiv

end Polygraph

end CategoryTheory
