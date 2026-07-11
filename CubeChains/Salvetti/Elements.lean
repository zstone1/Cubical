import CubeChains.Chains.Correspondence
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Salvetti/Elements — reuse + `Elements`/Grothendieck scaffolding for `Int(Lines) = ∫Lines`

Bookkeeping for `Int(Lines(□ⁿ)) = (Lines □ⁿ).Elements`, split from the mathematical content in
`Lines.lean` (`Sal` itself is the COM Salvetti poset in `Sal.lean`).
Provides the cube specialisations `cubeChainRefineEquiv n : RefineObj (cube n) ≌
ChainCat.Obj (cube n)` and `Quiver.IsThin` instances for both cube categories, plus a mathlib
`Elements` API over an abstract `P : C ⥤ Type w`: `Functor.elements_isThin`,
`CategoryOfElements.mapEquivalence`, and `CategoryOfElements.pre`/`preEquivalence`.

-/

open CategoryTheory Opposite

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
noncomputable def mapEquivalence {F G : C ⥤ Type w} (e : F ≅ G) :
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

/-- `pre P G` is faithful whenever `G` is. -/
instance pre_faithful (P : C ⥤ Type w) (G : D ⥤ C) [G.Faithful] :
    (pre P G).Faithful where
  map_injective {X Y} {f g} h := by
    apply CategoryOfElements.ext (G ⋙ P)
    apply G.map_injective
    exact congrArg (fun m => m.1) h

/-- `pre P G` is full whenever `G` is. -/
instance pre_full (P : C ⥤ Type w) (G : D ⥤ C) [G.Full] :
    (pre P G).Full where
  map_surjective {X Y} k :=
    ⟨⟨G.preimage k.1, by
        show (G ⋙ P).map (G.preimage k.1) X.2 = Y.2
        rw [Functor.comp_map, G.map_preimage]
        exact k.2⟩,
      CategoryOfElements.ext P _ _ (G.map_preimage k.1)⟩

/-- `pre P G` is essentially surjective whenever `G` is. -/
instance pre_essSurj (P : C ⥤ Type w) (G : D ⥤ C) [G.EssSurj] :
    (pre P G).EssSurj where
  mem_essImage Z :=
    ⟨⟨G.objPreimage Z.1, P.map (G.objObjPreimageIso Z.1).inv Z.2⟩,
      ⟨CategoryOfElements.isoMk _ _ (G.objObjPreimageIso Z.1) (by
        change P.map (G.objObjPreimageIso Z.1).hom
            (P.map (G.objObjPreimageIso Z.1).inv Z.2) = Z.2
        rw [← types_comp_apply (P.map _) (P.map _), ← P.map_comp, Iso.inv_hom_id, P.map_id,
          types_id_apply])⟩⟩

/-- **Base transport is an equivalence** when the base functor is: for `e : D ≌ C`,
`pre P e.functor : (e.functor ⋙ P).Elements ≌ P.Elements`.  (Analogue of
`Grothendieck.preEquivalence`.) -/
noncomputable def preEquivalence (P : C ⥤ Type w) (e : D ≌ C) :
    (e.functor ⋙ P).Elements ≌ P.Elements :=
  haveI : (pre P e.functor).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  (pre P e.functor).asEquivalence

end CategoryOfElements

end CategoryTheory

namespace CubeChain

open CategoryTheory

/-! ## Part A — cube reuse layer -/

/-- **`Ch(□ⁿ) ≌ RefineObj(□ⁿ)`:** `equivWedgeCat` specialised to the standard cube. -/
noncomputable def cubeChainRefineEquiv (n : ℕ) :
    RefineObj (BPSet.cube n).init (BPSet.cube n).final ≌ ChainCat.Obj (BPSet.cube n) :=
  equivWedgeCat (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)

/-- The refinement category of a standard cube is thin. -/
instance cube_refineObj_isThin (n : ℕ) :
    Quiver.IsThin (RefineObj (BPSet.cube n).init (BPSet.cube n).final) :=
  refineObj_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)

/-- The cube-chain category of a standard cube is thin. -/
instance cube_chainCat_isThin (n : ℕ) :
    Quiver.IsThin (ChainCat.Obj (BPSet.cube n)) :=
  chainCat_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)

end CubeChain
