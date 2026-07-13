import CubeChains.Arrangements.SalSum
import CubeChains.Arrangements.ElementsProd
import CubeChains.Salvetti.SalWedge
import CubeChains.Salvetti.BraidIso
import CubeChains.Salvetti.LinesWedge
import CubeChains.Chains.SegalProd
import CubeChains.Chains.ChainSlice
import CubeChains.Salvetti.LinesSlice
import CubeChains.Salvetti.SalBraidPartition

/-!
# Salvetti/SerialSalLines — the serial-wedge Salvetti comparison at the presheaf level

The presheaf-level (pre-`∫`) form of `braidSerialSalEquiv` (`Salvetti/SalWedge.lean`): the
per-fibre iso is kept as a natural iso of presheaves, only the base equivalences are fused.

      Lines (⋁dims)  ≅  (serialSalBaseEquiv dims).functor ⋙ salFunctor (⊕ᵢ A_{dᵢ−1})

      (Ch ⋁dims)ᵒᵖ  ≌  Face (braidDirectSum dims)          (serialSalBaseEquiv)

Built from the leaf `leafIso` (a single cube) by the binary combinator `salLinesWedgeIso`
(the presheaf-level `salWedgeEquiv`) and the `dims`-recursion `serialSalLinesIso`.  The
slice corollary `salFunctorSlice f` transports this over `Ch(K)/f = Over f` for an
arbitrary chain `f`.

The base is packaged as an equivalence `(Ch P)ᵒᵖ ≌ Face L` (not a bare functor): the
recursion composes equivalences and the slice corollary needs the base inverted.
-/

open CategoryTheory Opposite BPSet

/-! ## Congruence of the external product `extProd` in both functor arguments -/

namespace CategoryTheory.CategoryOfElements

universe w v₁ u₁ v₂ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Functoriality of `extProd` on morphisms: a pair of natural transformations induces one of the
external products, coordinatewise. -/
def extProdMap {F₁ F₁' : C ⥤ Type w} {F₂ F₂' : D ⥤ Type w}
    (α : F₁ ⟶ F₁') (β : F₂ ⟶ F₂') : extProd F₁ F₂ ⟶ extProd F₁' F₂' where
  app cd := TypeCat.ofHom (fun p => (α.app cd.1 p.1, β.app cd.2 p.2))
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro p
    simp only [types_comp_apply, extProd_map_apply, TypeCat.ofHom_apply]
    refine Prod.ext ?_ ?_
    · rw [← types_comp_apply (F₁.map f.1) (α.app Y.1), α.naturality f.1, types_comp_apply]
    · rw [← types_comp_apply (F₂.map f.2) (β.app Y.2), β.naturality f.2, types_comp_apply]

@[simp] theorem extProdMap_app {F₁ F₁' : C ⥤ Type w} {F₂ F₂' : D ⥤ Type w}
    (α : F₁ ⟶ F₁') (β : F₂ ⟶ F₂') (cd : C × D) :
    (extProdMap α β).app cd = TypeCat.ofHom (fun p => (α.app cd.1 p.1, β.app cd.2 p.2)) := rfl

theorem extProdMap_id (F₁ : C ⥤ Type w) (F₂ : D ⥤ Type w) :
    extProdMap (𝟙 F₁) (𝟙 F₂) = 𝟙 (extProd F₁ F₂) := by
  apply NatTrans.ext; funext cd
  apply ConcreteCategory.hom_ext; intro p
  rfl

theorem extProdMap_comp {F₁ F₁' F₁'' : C ⥤ Type w} {F₂ F₂' F₂'' : D ⥤ Type w}
    (α₁ : F₁ ⟶ F₁') (α₂ : F₁' ⟶ F₁'') (β₁ : F₂ ⟶ F₂') (β₂ : F₂' ⟶ F₂'') :
    extProdMap α₁ β₁ ≫ extProdMap α₂ β₂ = extProdMap (α₁ ≫ α₂) (β₁ ≫ β₂) := by
  apply NatTrans.ext; funext cd
  apply ConcreteCategory.hom_ext; intro p
  rfl

/-- Congruence of `extProd` in both functor arguments: two natural isomorphisms induce one of the
external products. -/
def extProdCongr {F₁ F₁' : C ⥤ Type w} {F₂ F₂' : D ⥤ Type w}
    (ια : F₁ ≅ F₁') (ιβ : F₂ ≅ F₂') : extProd F₁ F₂ ≅ extProd F₁' F₂' where
  hom := extProdMap ια.hom ιβ.hom
  inv := extProdMap ια.inv ιβ.inv
  hom_inv_id := by rw [extProdMap_comp, ια.hom_inv_id, ιβ.hom_inv_id, extProdMap_id]
  inv_hom_id := by rw [extProdMap_comp, ια.inv_hom_id, ιβ.inv_hom_id, extProdMap_id]

end CategoryTheory.CategoryOfElements

namespace CubeChains

/-! ## A generic presheaf-transport helper

Transport a fibre iso `E.functor ⋙ F ≅ K` along a base equivalence `E : A ≌ B` to a fibre iso
`F ≅ E.inverse ⋙ K` on the other base (the presheaf-level analogue of
`CategoryOfElements.preEquivalence`). -/

universe w

section Transport
variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- Transport a fibre iso along a base equivalence (left-whisker by the inverse). -/
noncomputable def transportBase (E : A ≌ B) {F : B ⥤ Type w} {K : A ⥤ Type w}
    (α : E.functor ⋙ F ≅ K) : F ≅ E.inverse ⋙ K :=
  (Functor.leftUnitor F).symm ≪≫ (Functor.isoWhiskerRight E.counitIso F).symm ≪≫
    Functor.associator E.inverse E.functor F ≪≫ Functor.isoWhiskerLeft E.inverse α

end Transport

/-! ## The leaf: the per-cube fibre iso transported onto `(Ch □ⁿ)ᵒᵖ` -/

/-- The base equivalence for a single cube: `(Ch □ⁿ)ᵒᵖ ≌ Face (braidCOM n)`, assembled from the
refinement dictionary `cubeChainRefineEquiv`/`refineOpToFace`. -/
noncomputable def leafBaseEquiv (n : ℕ) :
    (Ch (□n))ᵒᵖ ≌ COM.Face (braidCOM n) :=
  haveI : (refineOpToFace n).IsEquivalence := { }
  (CubeChain.cubeChainRefineEquiv n).op.symm.trans (refineOpToFace n).asEquivalence

/-- The per-cube fibre iso `salLinesIso n`, transported off `(RefineObj □ⁿ)ᵒᵖ` onto `(Ch □ⁿ)ᵒᵖ`. -/
noncomputable def leafIso (n : ℕ) :
    Lines (□n) ≅ (leafBaseEquiv n).functor ⋙ COM.salFunctor (braidCOM n) :=
  transportBase (CubeChain.cubeChainRefineEquiv n).op (salLinesIso n)

/-! ## The binary combinator: the presheaf-level `salWedgeEquiv` -/

section Wedge

variable {E₁ E₂ : Type} (L₁ : COM E₁) (L₂ : COM E₂) {P Q : BPSet}
  (e₁ : (Ch P)ᵒᵖ ≌ COM.Face L₁) (e₂ : (Ch Q)ᵒᵖ ≌ COM.Face L₂)

/-- `extProd (salFunctor L₁) (salFunctor L₂) ≅ (faceSumEquiv).inverse ⋙ salFunctor (L₁ ⊕ L₂)`:
`salFunctorSumIso` solved for the external product. -/
noncomputable def salSumBack :
    CategoryOfElements.extProd (COM.salFunctor L₁) (COM.salFunctor L₂)
      ≅ (COM.faceSumEquiv L₁ L₂).inverse ⋙ COM.salFunctor (L₁.directSum L₂) :=
  transportBase (COM.faceSumEquiv L₁ L₂) (COM.salFunctorSumIso L₁ L₂).symm

/-- The product-side fibre iso over `(Ch P)ᵒᵖ × (Ch Q)ᵒᵖ`:
`extProd (Lines P) (Lines Q) ≅ Bprod ⋙ salFunctor (L₁ ⊕ L₂)`, where
`Bprod = (e₁.functor ⊠ e₂.functor) ⋙ (faceSumEquiv).inverse`. -/
noncomputable def prodIso
    (ι₁ : Lines P ≅ e₁.functor ⋙ COM.salFunctor L₁)
    (ι₂ : Lines Q ≅ e₂.functor ⋙ COM.salFunctor L₂) :
    CategoryOfElements.extProd (Lines P) (Lines Q)
      ≅ (e₁.functor.prod e₂.functor ⋙ (COM.faceSumEquiv L₁ L₂).inverse)
          ⋙ COM.salFunctor (L₁.directSum L₂) :=
  CategoryOfElements.extProdCongr ι₁ ι₂ ≪≫
    Functor.isoWhiskerLeft (e₁.functor.prod e₂.functor) (salSumBack L₁ L₂)

/-- The base equivalence for a wedge, assembled from `chSegal`, `prodOpEquiv`, the two summand
bases, and `faceSumEquiv`. -/
noncomputable def salLinesWedgeBaseEquiv (hP : P.AdmitsAltitude) (hQ : Q.AdmitsAltitude) :
    (Ch (wedge2 P Q))ᵒᵖ ≌ COM.Face (L₁.directSum L₂) :=
  (ChainCat.chSegal P Q (wedge2_admitsAltitude hP hQ)).op.symm.trans
    ((prodOpEquiv (C := Ch P) (D := Ch Q)).trans
      ((e₁.prod e₂).trans (COM.faceSumEquiv L₁ L₂).symm))

/-- The presheaf-level `salWedgeEquiv`: from base equivalences and fibre isos for `P`, `Q`,
the fibre iso `Lines (wedge2 P Q) ≅ (salLinesWedgeBaseEquiv ..).functor ⋙ salFunctor (L₁ ⊕ L₂)`.
Split by `multIso`, rewrite each fibre by `ι₁, ι₂`, recombine via `salSumBack`, transport the
base along `chSegal.op`. -/
noncomputable def salLinesWedgeIso (hP : P.AdmitsAltitude) (hQ : Q.AdmitsAltitude)
    (ι₁ : Lines P ≅ e₁.functor ⋙ COM.salFunctor L₁)
    (ι₂ : Lines Q ≅ e₂.functor ⋙ COM.salFunctor L₂) :
    Lines (wedge2 P Q)
      ≅ (salLinesWedgeBaseEquiv L₁ L₂ e₁ e₂ hP hQ).functor
          ⋙ COM.salFunctor (L₁.directSum L₂) :=
  transportBase (ChainCat.chSegal P Q (wedge2_admitsAltitude hP hQ)).op
    (multIso P Q ≪≫ Functor.isoWhiskerLeft
      (prodOpEquiv (C := Ch P) (D := Ch Q)).functor
      (prodIso L₁ L₂ e₁ e₂ ι₁ ι₂))

end Wedge

/-! ## The n-ary recursion, mirroring `braidSerialSalEquiv` -/

/-- The base equivalence for the serial wedge `⋁dims`, by recursion on `dims`. -/
noncomputable def serialSalBaseEquiv : (dims : List ℕ+) →
    (Ch (⋁dims))ᵒᵖ ≌ COM.Face (braidDirectSum dims)
  | [] => leafBaseEquiv 0
  | n :: rest =>
      salLinesWedgeBaseEquiv (braidCOM (n : ℕ)) (braidDirectSum rest)
        (leafBaseEquiv (n : ℕ)) (serialSalBaseEquiv rest)
        (cube_admitsAltitude (n : ℕ)) (serialWedge_admitsAltitude rest)

/-- The serial-wedge fibre iso: `Lines (⋁dims) ≅ (serialSalBaseEquiv dims).functor ⋙
salFunctor (⊕ᵢ A_{dᵢ−1})`.  Base `[]` is the leaf; step `n :: rest` glues the head cube via
`salLinesWedgeIso`. -/
noncomputable def serialSalLinesIso : (dims : List ℕ+) →
    Lines (⋁dims)
      ≅ (serialSalBaseEquiv dims).functor ⋙ COM.salFunctor (braidDirectSum dims)
  | [] => leafIso 0
  | n :: rest =>
      salLinesWedgeIso (braidCOM (n : ℕ)) (braidDirectSum rest)
        (leafBaseEquiv (n : ℕ)) (serialSalBaseEquiv rest)
        (cube_admitsAltitude (n : ℕ)) (serialWedge_admitsAltitude rest)
        (leafIso (n : ℕ)) (serialSalLinesIso rest)

/-! ## The slice corollary -/

variable {K : BPSet}

/-- `Lines` reads only `dims`/`φ`, both preserved by the slice forgetful functor, so pulling
`Lines K` back along `(Over.forget f).op` agrees on the nose with pulling
`Lines (⋁f.dims)` back along `(sliceForward f).op` (components `Iso.refl`). -/
noncomputable def forgetSliceIso (f : Ch K) :
    (Over.forget f).op ⋙ Lines K
      ≅ (ChainCat.sliceForward f).op ⋙ Lines (⋁f.dims) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The slice corollary: for an arbitrary chain `f : Ch K`, the Salvetti presheaf of
`⊕ᵢ A_{(f.dims)ᵢ−1}` is `Lines K` pulled back over the slice `Ch(K)/f = Over f`, with base
`G_f = (serialSalBaseEquiv f.dims).inverse ⋙ (sliceEquiv f).op.inverse` — the serial base
equivalence inverted and its codomain moved along `(sliceEquiv f).symm`. -/
noncomputable def salFunctorSlice (f : Ch K) :
    COM.salFunctor (braidDirectSum f.dims)
      ≅ ((serialSalBaseEquiv f.dims).inverse ⋙ (ChainCat.sliceEquiv f).op.inverse)
          ⋙ (Over.forget f).op ⋙ Lines K :=
  transportBase (serialSalBaseEquiv f.dims) (serialSalLinesIso f.dims).symm ≪≫
    Functor.isoWhiskerLeft (serialSalBaseEquiv f.dims).inverse
      (transportBase (ChainCat.sliceEquiv f).op
        (Iso.refl ((ChainCat.sliceEquiv f).op.functor ⋙ Lines (⋁f.dims)))) ≪≫
    Functor.isoWhiskerLeft (serialSalBaseEquiv f.dims).inverse
      (Functor.isoWhiskerLeft (ChainCat.sliceEquiv f).op.inverse (forgetSliceIso f).symm)

end CubeChains
