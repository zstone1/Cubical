import CubeChains.Chains.Correspondence
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Salvetti/Elements — `Elements`/Grothendieck scaffolding for `Int(Lines) = ∫Lines`

Bookkeeping for `Int(Lines(□ⁿ)) = (Lines □ⁿ).Elements`: a mathlib `Elements` API over an abstract
`P : C ⥤ Type w` (`Functor.elements_isThin`, `CategoryOfElements.mapEquivalence`,
`CategoryOfElements.pre`/`preEquivalenceComp`), plus the thinness of `Ch (□ⁿ)` that feeds it.
-/

open CategoryTheory Opposite BPSet

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ## Part B.1 — the category of elements of a thin category is thin -/

/-- If the base category `C` is thin, then so is the category of elements of any
`P : C ⥤ Type w`. -/
instance Functor.elements_isThin [Quiver.IsThin C] (P : C ⥤ Type w) :
    Quiver.IsThin P.Elements := fun p q => by
  have : Subsingleton (p.1 ⟶ q.1) := ‹Quiver.IsThin C› p.1 q.1
  exact ⟨fun f g => CategoryOfElements.ext P f g (Subsingleton.elim _ _)⟩

namespace CategoryOfElements

/-! ## Part B.2 — a natural iso of presheaves gives an equivalence of elements -/

/-- A natural isomorphism `F ≅ G` between functors `C ⥤ Type w` induces an equivalence of
their categories of elements. -/
def mapEquivalence {F G : C ⥤ Type w} (e : F ≅ G) :
    F.Elements ≌ G.Elements :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso e)

/-! ## Part B.3 — base transport along a functor `G : D ⥤ C` -/

/-- **Base transport** (the `Elements`-level `Grothendieck.pre`): a functor `G : D ⥤ C` sends
the category of elements of `G ⋙ P` to that of `P`, `⟨d, x⟩ ↦ ⟨G.obj d, x⟩`. -/
def pre (P : C ⥤ Type w) (G : D ⥤ C) : (G ⋙ P).Elements ⥤ P.Elements where
  obj X := ⟨G.obj X.1, X.2⟩
  map f := ⟨G.map f.1, f.2⟩
  map_id X := CategoryOfElements.ext P _ _ (G.map_id X.1)
  map_comp f g := CategoryOfElements.ext P _ _ (G.map_comp f.1 g.1)

/-! ## Part B.4 — the inverse, written out so the equivalence computes -/

/-- The explicit inverse of `pre P e.functor`: an element `x` of `P` at `X` is carried to the
element of `e.functor ⋙ P` at `e.inverse.obj X` obtained by transporting `x` along the counit
`X ≅ e.functor.obj (e.inverse.obj X)`. -/
def preInv (P : C ⥤ Type w) (e : D ≌ C) : P.Elements ⥤ (e.functor ⋙ P).Elements where
  obj X := ⟨e.inverse.obj X.1, P.map (e.counitIso.inv.app X.1) X.2⟩
  map {X Y} k := ⟨e.inverse.map k.1, by
    have hn : e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)
        = k.1 ≫ e.counitIso.inv.app Y.1 := (e.counitIso.inv.naturality k.1).symm
    change P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app Y.1) Y.2
    calc P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)) X.2 :=
          (P.map_comp_apply _ _ _).symm
      _ = P.map (k.1 ≫ e.counitIso.inv.app Y.1) X.2 := by rw [hn]; rfl
      _ = P.map (e.counitIso.inv.app Y.1) (P.map k.1 X.2) := P.map_comp_apply _ _ _
      _ = P.map (e.counitIso.inv.app Y.1) Y.2 := by rw [k.2]⟩
  map_id X := CategoryOfElements.ext _ _ _ (e.inverse.map_id X.1)
  map_comp f g := CategoryOfElements.ext _ _ _ (e.inverse.map_comp f.1 g.1)

/-- **Base transport is an equivalence** when the base functor is: for `e : D ≌ C`,
`pre P e.functor : (e.functor ⋙ P).Elements ≌ P.Elements`.  (Analogue of
`Grothendieck.preEquivalence`.)  The inverse is `preInv`, spelled out rather than obtained from
`EssSurj`, so that the equivalence computes. -/
def preEquivalenceComp (P : C ⥤ Type w) (e : D ≌ C) :
    (e.functor ⋙ P).Elements ≌ P.Elements where
  functor := pre P e.functor
  inverse := preInv P e
  unitIso := NatIso.ofComponents
    (fun Z => CategoryOfElements.isoMk _ _ (e.unitIso.app Z.1) (by
      change P.map (e.functor.map (e.unitIso.hom.app Z.1)) Z.2
          = P.map (e.counitIso.inv.app (e.functor.obj Z.1)) Z.2
      rw [← e.counitInv_app_functor]
      rfl))
    (fun k => CategoryOfElements.ext _ _ _ (e.unit_naturality k.1).symm)
  counitIso := NatIso.ofComponents
    (fun Z => CategoryOfElements.isoMk _ _ (e.counitIso.app Z.1) (by
      change P.map (e.counitIso.hom.app Z.1) (P.map (e.counitIso.inv.app Z.1) Z.2) = Z.2
      rw [← P.map_comp_apply, e.counitIso.inv_hom_id_app, P.map_id_apply]))
    (fun k => CategoryOfElements.ext _ _ _ (e.counit_naturality k.1))
  functor_unitIso_comp Z := CategoryOfElements.ext _ _ _ (e.functor_unit_comp Z.1)

end CategoryOfElements

end CategoryTheory

namespace CubeChain

open CategoryTheory

/-! ## Part A — cube reuse layer -/

/-- The cube-chain category of a standard cube is thin. -/
instance cube_chainCat_isThin (n : ℕ) :
    Quiver.IsThin (Ch (□n)) :=
  chainCat_hom_subsingleton (cube_nonSelfLinked n) (cube_admitsAltitude n)

end CubeChain
