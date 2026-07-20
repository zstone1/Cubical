import CubeChains.Salvetti.RunMonoidal
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Functor.Hom

open CategoryTheory Opposite MonoidalCategory

open ChainCat CubeChains
open scoped CubeChains

namespace Scratch

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
/-- The two-variable hom functor of a monoidal category is lax monoidal: `μ` is `⊗ₘ`. -/
instance homLaxMonoidal (C : Type*) [Category C] [MonoidalCategory C] :
    (Functor.hom C).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ↾fun _ ↦ 𝟙 (𝟙_ C))
    (μ := fun _ _ ↦ ↾fun p ↦ p.1 ⊗ₘ p.2)
    (μ_natural := by cat_disch)
    (associativity := by cat_disch)
    (left_unitality := by cat_disch)
    (right_unitality := by cat_disch)

/-- `Cᵒᵖ` does not reverse the tensor, so a strong monoidal `F` opposes to a strong monoidal
`F.op`, whose lax structure is `F`'s oplax structure, opped. -/
instance opMonoidal {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] : F.op.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (Functor.Monoidal.εIso F).op.symm
      μIso := fun X Y => (Functor.Monoidal.μIso F X.unop Y.unop).op.symm
      μIso_hom_natural_left := by intros; apply Quiver.Hom.unop_inj; simp
      μIso_hom_natural_right := by intros; apply Quiver.Hom.unop_inj; simp
      associativity := by intros; apply Quiver.Hom.unop_inj; simp
      left_unitality := by intros; apply Quiver.Hom.unop_inj; simp
      right_unitality := by intros; apply Quiver.Hom.unop_inj; simp }

/-- A discrete category is its own opposite, monoidally (all coherence is thin). -/
def discreteOp (M : Type*) [Monoid M] : Discrete M ⥤ (Discrete M)ᵒᵖ :=
  Discrete.functor (fun m => op (Discrete.mk m))

instance (M : Type*) [Monoid M] : (discreteOp M).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

/-- Total dimension, as a monoid hom to the additive-in-disguise `Multiplicative ℕ`. -/
def dimSumHom : FreeMonoid ℕ+ →* Multiplicative ℕ :=
  FreeMonoid.lift (fun d : ℕ+ => Multiplicative.ofAdd (d : ℕ))

/-- The source of a run, indexed by the target word: `k ↦ runObj (dimSum k)`. -/
def Src : DimList ⥤ BPSet := Discrete.monoidalFunctor dimSumHom ⋙ CubeChains.OneD

instance : Src.Monoidal := inferInstanceAs ((Discrete.monoidalFunctor dimSumHom ⋙ CubeChains.OneD).Monoidal)

/-- `k ↦ (runObj (dimSum k) ⟶ ⋁k)`, lax monoidal purely by composition of mathlib instances. -/
def RunF : DimList ⥤ Type :=
  Functor.prod' (discreteOp _ ⋙ Src.op) ChainCat.serialWedgeFunctor ⋙ Functor.hom BPSet

instance : RunF.LaxMonoidal := inferInstanceAs
  ((Functor.prod' (discreteOp _ ⋙ Src.op) ChainCat.serialWedgeFunctor ⋙ Functor.hom BPSet).LaxMonoidal)

/-- The objects are what we want, definitionally. -/
example (k : List ℕ+) :
    RunF.obj (Discrete.mk (FreeMonoid.ofList k)) = (Src.obj (Discrete.mk (FreeMonoid.ofList k)) ⟶ ⋁ k) :=
  rfl

/-- …and `μ` is exactly `Run.append`'s formula: split the source, tensor, glue the target. -/
example (a b : DimList) (f : RunF.obj a) (g : RunF.obj b) :
    Functor.LaxMonoidal.μ RunF a b (f, g)
      = Functor.OplaxMonoidal.δ Src a b ≫ (f ⊗ₘ g)
          ≫ Functor.LaxMonoidal.μ ChainCat.serialWedgeFunctor a b := by
  rfl

end Scratch

namespace Scratch
-- the source really is `runObj (dimSum k)`

namespace Scratch
-- the source really is `runObj (dimSum k)`
example (k : List ℕ+) : Src.obj (Discrete.mk (FreeMonoid.ofList k)) = runObj (BPSet.dimSum k) := by simp [Src, runObj, dimSumHom, BPSet.dimSum, CubeChains.OneD, FreeMonoid.lift, FreeMonoid.prodAux_eq, Function.comp_def]

-- the three laws now exist for RunF, stated with unitors/associator: no transports, no HEq
#check @Functor.LaxMonoidal.associativity _ _ _ _ _ _ RunF _
#check @Functor.LaxMonoidal.left_unitality _ _ _ _ _ _ RunF _
#check @Functor.LaxMonoidal.right_unitality _ _ _ _ _ _ RunF _
end Scratch
