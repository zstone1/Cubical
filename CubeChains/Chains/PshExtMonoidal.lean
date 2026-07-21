import CubeChains.Chains.WedgeExtend
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Whiskering

/-!
# Chains/PshExtMonoidal — the contravariant lift `F↑ = pshExt F` is oplax monoidal

`pshExtFunctor F : BPSetᵒᵖ ⥤ Type`, `op X ↦ (X.toPsh ⟶ F)`, is **oplax** monoidal into the
cartesian `(Type, ×)`: the cotensorator `δ` is the always-defined restrict map `pshExtWedge2.toFun`
(the two wedge inclusions), `η` the unique map to `PUnit`.  Under single-vertexness (`pt`/`hF`) both
are isos, upgrading to strong monoidal.  The dual of `WedgeExtend`'s covariant
`cotensorLift.LaxMonoidal` — a different functor (hom vs coend), not an `op` of it.
-/

open CategoryTheory Opposite BPSet MonoidalCategory

namespace ChainCat

/-- The contravariant lift as a functor `BPSetᵒᵖ ⥤ Type` — `Hom(-, F)` restricted along the
underlying-presheaf functor. -/
def pshExtFunctor (F : PrecubicalSet) : BPSetᵒᵖ ⥤ Type := BPSet.toPshFunctor.op ⋙ yoneda.obj F

@[simp] theorem pshExtFunctor_obj (F : PrecubicalSet) (X : BPSet) :
    (pshExtFunctor F).obj (op X) = pshExt F X := rfl

@[simp] theorem pshExtFunctor_map (F : PrecubicalSet) {X Y : BPSetᵒᵖ} (f : X ⟶ Y)
    (φ : (pshExtFunctor F).obj X) : (pshExtFunctor F).map f φ = f.unop.hom ≫ φ := rfl

/-- The bundled form, functorial in the coefficient `F`: `Hom(-, F)` is functorial in `F`
(`yoneda`), whiskered by the underlying-presheaf functor.  Free — no new coherence. -/
def pshExtFunctorFunctor : PrecubicalSet ⥤ (BPSetᵒᵖ ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj BPSet.toPshFunctor.op

@[simp] theorem pshExtFunctorFunctor_obj (F : PrecubicalSet) :
    pshExtFunctorFunctor.obj F = pshExtFunctor F := rfl

/-- The cotensorator: restrict along the two wedge inclusions (`pshExtWedge2.toFun`, no `hF`). -/
def pshExtδ (F : PrecubicalSet) (X Y : BPSetᵒᵖ) :
    (pshExtFunctor F).obj (X ⊗ Y) ⟶ (pshExtFunctor F).obj X ⊗ (pshExtFunctor F).obj Y :=
  TypeCat.ofHom (fun φ => (wedgeInl X.unop Y.unop ≫ φ, wedgeInr X.unop Y.unop ≫ φ))

/-- The counit: the unique map to `PUnit`. -/
def pshExtη (F : PrecubicalSet) : (pshExtFunctor F).obj (𝟙_ BPSetᵒᵖ) ⟶ 𝟙_ Type :=
  TypeCat.ofHom (fun _ => PUnit.unit)

@[simp] theorem pshExtδ_apply (F : PrecubicalSet) (X Y : BPSetᵒᵖ)
    (φ : (pshExtFunctor F).obj (X ⊗ Y)) :
    pshExtδ F X Y φ = (wedgeInl X.unop Y.unop ≫ φ, wedgeInr X.unop Y.unop ≫ φ) := rfl

@[simp] theorem pshExtη_apply (F : PrecubicalSet) (φ : (pshExtFunctor F).obj (𝟙_ BPSetᵒᵖ)) :
    pshExtη F φ = PUnit.unit := rfl

/-- `.inv` of the wedge associator (the `BPSetᵒᵖ` `α_.hom` unops to this). -/
@[simp] theorem associator_bpset_inv_hom (X Y Z : BPSet) :
    (α_ X Y Z).inv.hom = wedge2AssocBwd X Y Z := rfl

/-- **`pshExtFunctor F` is oplax monoidal** `(BPSetᵒᵖ, ∨ᵒᵖ) → (Type, ×)`.  The cotensorator is the
restrict map (two wedge inclusions); each coherence is `Prod.ext` down to the summand, then the
`WedgeMonoidal` restriction lemma — the same lemmas as the covariant lax structure. -/
instance (F : PrecubicalSet) : (pshExtFunctor F).OplaxMonoidal where
  η := pshExtη F
  δ := pshExtδ F
  δ_natural_left {X Y} f X' := by
    apply ConcreteCategory.hom_ext; intro φ
    change (f.unop.hom ≫ wedgeInl X.unop X'.unop ≫ φ, wedgeInr X.unop X'.unop ≫ φ)
      = (wedgeInl Y.unop X'.unop ≫ wedge2MapPsh f.unop (𝟙 X'.unop) ≫ φ,
         wedgeInr Y.unop X'.unop ≫ wedge2MapPsh f.unop (𝟙 X'.unop) ≫ φ)
    rw [wedge2MapPsh_inl_assoc, wedge2MapPsh_inr_assoc, id_hom, Category.id_comp]
  δ_natural_right {X Y} X' f := by
    apply ConcreteCategory.hom_ext; intro φ
    change (wedgeInl X'.unop X.unop ≫ φ, f.unop.hom ≫ wedgeInr X'.unop X.unop ≫ φ)
      = (wedgeInl X'.unop Y.unop ≫ wedge2MapPsh (𝟙 X'.unop) f.unop ≫ φ,
         wedgeInr X'.unop Y.unop ≫ wedge2MapPsh (𝟙 X'.unop) f.unop ≫ φ)
    rw [wedge2MapPsh_inl_assoc, wedge2MapPsh_inr_assoc, id_hom, Category.id_comp]
  oplax_associativity X Y Z := by
    apply ConcreteCategory.hom_ext; intro φ
    change (wedgeInl X.unop Y.unop ≫ wedgeInl (X.unop ∨ Y.unop) Z.unop ≫ φ,
        (wedgeInr X.unop Y.unop ≫ wedgeInl (X.unop ∨ Y.unop) Z.unop ≫ φ,
         wedgeInr (X.unop ∨ Y.unop) Z.unop ≫ φ))
      = (wedgeInl X.unop (Y.unop ∨ Z.unop) ≫ wedge2AssocBwd X.unop Y.unop Z.unop ≫ φ,
        (wedgeInl Y.unop Z.unop ≫ wedgeInr X.unop (Y.unop ∨ Z.unop)
            ≫ wedge2AssocBwd X.unop Y.unop Z.unop ≫ φ,
         wedgeInr Y.unop Z.unop ≫ wedgeInr X.unop (Y.unop ∨ Z.unop)
            ≫ wedge2AssocBwd X.unop Y.unop Z.unop ≫ φ))
    rw [wedge2AssocBwd_inl_assoc, wedge2AssocBwd_inl_inr_assoc, wedge2AssocBwd_inr_inr_assoc]
  oplax_left_unitality X := by
    apply ConcreteCategory.hom_ext; intro φ
    refine Prod.ext rfl ?_
    change φ = wedgeInr (□0) X.unop ≫ wedge2LeftUnitPsh X.unop ≫ φ
    rw [wedge2LeftUnitPsh_inr_assoc]
  oplax_right_unitality X := by
    apply ConcreteCategory.hom_ext; intro φ
    refine Prod.ext ?_ rfl
    change φ = wedgeInl X.unop (□0) ≫ wedge2RightUnitPsh X.unop ≫ φ
    rw [wedge2RightUnitPsh_inl_assoc]

/-! ### Strong monoidal under single-vertexness

`δ` is `pshExtWedge2.toFun` — an `Equiv` under `hF` — and `η` a map between the singleton `pshExt
F □0` (`pt`/`hF`) and `PUnit`; both are isos, so the oplax functor upgrades to strong monoidal. -/

/-- `δ` is an iso: it is `pshExtWedge2`'s forward map, an equivalence under `hF`. -/
theorem pshExtδ_isIso (F : PrecubicalSet) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) (X Y : BPSetᵒᵖ) :
    IsIso (pshExtδ F X Y) :=
  let e := pshExtWedge2 F hF X.unop Y.unop
  ⟨TypeCat.ofHom e.invFun,
    ConcreteCategory.hom_ext _ _ fun φ => e.left_inv φ,
    ConcreteCategory.hom_ext _ _ fun p => e.right_inv p⟩

/-- `η` is an iso: with a `0`-cell `pt` and `hF`, `pshExt F □0` is a singleton, like `PUnit`. -/
theorem pshExtη_isIso (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F)
    (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) : IsIso (pshExtη F) :=
  haveI : Subsingleton (𝟙_ Type) := inferInstanceAs (Subsingleton PUnit)
  ⟨TypeCat.ofHom (fun _ => pt),
    ConcreteCategory.hom_ext _ _ fun φ => hF pt φ,
    ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _⟩

/-- The `CoreMonoidal` core with **explicit computable** isos — `μIso`/`εIso` carry the assemble
maps (`pshExtWedge2.symm`, `fun _ => pt`) as data, their `.inv` being `pshExtδ`/`pshExtη`, so the
oplax coherences already proved above discharge the `mk'` fields. -/
def pshExtCoreMonoidal (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F)
    (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) : (pshExtFunctor F).CoreMonoidal :=
  haveI : Subsingleton (𝟙_ Type) := inferInstanceAs (Subsingleton PUnit)
  Functor.CoreMonoidal.mk'
    { hom := TypeCat.ofHom (fun _ => pt), inv := pshExtη F
      hom_inv_id := ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _
      inv_hom_id := ConcreteCategory.hom_ext _ _ fun φ => hF pt φ }
    (fun X Y =>
      { hom := TypeCat.ofHom (pshExtWedge2 F hF X.unop Y.unop).invFun, inv := pshExtδ F X Y
        hom_inv_id :=
          ConcreteCategory.hom_ext _ _ fun p => (pshExtWedge2 F hF X.unop Y.unop).right_inv p
        inv_hom_id :=
          ConcreteCategory.hom_ext _ _ fun φ => (pshExtWedge2 F hF X.unop Y.unop).left_inv φ })
    (μIso_inv_natural_left := Functor.OplaxMonoidal.δ_natural_left (pshExtFunctor F))
    (μIso_inv_natural_right := Functor.OplaxMonoidal.δ_natural_right (pshExtFunctor F))
    (oplax_associativity := Functor.OplaxMonoidal.oplax_associativity (pshExtFunctor F))
    (oplax_left_unitality := Functor.OplaxMonoidal.oplax_left_unitality (pshExtFunctor F))
    (oplax_right_unitality := Functor.OplaxMonoidal.oplax_right_unitality (pshExtFunctor F))

/-- **`pshExtFunctor F` is strong monoidal** when `F` has a unique `0`-cell (`pt`/`hF`).
Computable: the tensorator/unit isos assemble via `pshExtWedge2.symm` and `pt`. -/
@[reducible] def pshExtMonoidal (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F)
    (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) : (pshExtFunctor F).Monoidal :=
  (pshExtCoreMonoidal F pt hF).toMonoidal

end ChainCat
