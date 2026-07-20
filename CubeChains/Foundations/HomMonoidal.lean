import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# Foundations/HomMonoidal — hom functors and opposites, monoidally

Three instances mathlib lacks.  Together with `Functor.prod'` and `LaxMonoidal.comp` they let a
functor `k ↦ (A k ⟶ B k)`, for monoidal `A B : D ⥤ C`, inherit its lax monoidal structure as

```
D --prod'(Aᵒᵖ, B)--> Cᵒᵖ × C --Functor.hom--> Type
```

rather than carrying hand-written coherence.  `Monoidal/Types/Coyoneda.lean` has only the unit
case `(𝟙_ C ⟶ -)`.
-/

namespace CategoryTheory

open Opposite MonoidalCategory

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
/-- The two-variable hom functor is lax monoidal, with `μ = (· ⊗ₘ ·)`. -/
instance homLaxMonoidal (C : Type*) [Category C] [MonoidalCategory C] :
    (Functor.hom C).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := ↾fun _ ↦ 𝟙 (𝟙_ C))
    (μ := fun _ _ ↦ ↾fun p ↦ p.1 ⊗ₘ p.2)
    (μ_natural := by cat_disch)
    (associativity := by cat_disch)
    (left_unitality := by cat_disch)
    (right_unitality := by cat_disch)

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]

/-- `Cᵒᵖ` reverses the arrows but *not* the tensor, so `F.op` is strong monoidal whenever `F` is —
its lax structure being `F`'s oplax structure, opped. -/
instance opMonoidal (F : C ⥤ D) [F.Monoidal] : F.op.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (Functor.Monoidal.εIso F).op.symm
      μIso := fun X Y => (Functor.Monoidal.μIso F X.unop Y.unop).op.symm
      μIso_hom_natural_left := by intros; apply Quiver.Hom.unop_inj; simp
      μIso_hom_natural_right := by intros; apply Quiver.Hom.unop_inj; simp
      associativity := by intros; apply Quiver.Hom.unop_inj; simp
      left_unitality := by intros; apply Quiver.Hom.unop_inj; simp
      right_unitality := by intros; apply Quiver.Hom.unop_inj; simp }

/-- A discrete category as its own opposite — the first leg of `prod'` when the index category is
discrete.  `Discrete.opposite` is the same equivalence without the monoidal structure. -/
def discreteOp (M : Type*) [Monoid M] : Discrete M ⥤ (Discrete M)ᵒᵖ :=
  Discrete.functor (fun m => op (Discrete.mk m))

/-- Strong monoidal: `(Discrete M)ᵒᵖ` is thin, so every coherence square is `Subsingleton.elim`. -/
instance (M : Type*) [Monoid M] : (discreteOp M).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

end CategoryTheory
