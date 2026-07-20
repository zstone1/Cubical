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

/-! ### Discrete source: a lax monoidal functor to `Type` *is* a graded monoid

On a discrete source there is no naturality to satisfy, so `F.LaxMonoidal` carries exactly the data
of a monoid on `Σ m, F m`.  Stating the laws there is `GradedMonoid`'s idiom: the index arithmetic
sits in the first component, so each is an `Eq`, not a `HEq`.  Combined with `Equiv.monoid` this is
how a *different* presentation of the same family inherits its multiplication — cheaper than
transporting a monoidal structure, which mathlib only supports for strong functors. -/

section Graded

universe u v
variable {M : Type u} [Monoid M] (F : Discrete M ⥤ Type v) [F.LaxMonoidal]

omit [Monoid M] [F.LaxMonoidal] in
/-- Every map of a discrete category is an identity up to transport, so `F.map` moves nothing. -/
theorem Functor.LaxMonoidal.heq_map {X Y : Discrete M} (f : X ⟶ Y) (x : F.obj X) :
    F.map f x ≍ x := by
  obtain rfl : X = Y := Discrete.ext (Discrete.eq_of_hom f)
  rw [Subsingleton.elim f (𝟙 X)]
  simp

/-- The total space `Σ m, F m`. -/
def Functor.LaxMonoidal.Graded : Type max u v := Σ m : M, F.obj (Discrete.mk m)

namespace Functor.LaxMonoidal.Graded

instance : Mul (Graded F) :=
  ⟨fun x y => (⟨x.1 * y.1, μ F _ _ (x.2, y.2)⟩ : Σ m : M, F.obj (Discrete.mk m))⟩

instance : One (Graded F) := ⟨(⟨1, ε F PUnit.unit⟩ : Σ m : M, F.obj (Discrete.mk m))⟩

instance : Monoid (Graded F) where
  mul_assoc := by
    rintro ⟨m₁, x⟩ ⟨m₂, y⟩ ⟨m₃, z⟩
    refine Sigma.ext (mul_assoc m₁ m₂ m₃) ?_
    have h := congrArg (fun t => t ((x, y), z))
      (associativity (F := F) (Discrete.mk m₁) (Discrete.mk m₂) (Discrete.mk m₃))
    simp only [types_comp_apply] at h
    exact (heq_map F _ _).symm.trans (heq_of_eq h)
  one_mul := by
    rintro ⟨m, x⟩
    refine Sigma.ext (one_mul m) ?_
    have h := congrArg (fun t => t (PUnit.unit, x)) (left_unitality (F := F) (Discrete.mk m))
    simp only [types_comp_apply] at h
    exact (heq_map F _ _).symm.trans (heq_of_eq h.symm)
  mul_one := by
    rintro ⟨m, x⟩
    refine Sigma.ext (mul_one m) ?_
    have h := congrArg (fun t => t (x, PUnit.unit)) (right_unitality (F := F) (Discrete.mk m))
    simp only [types_comp_apply] at h
    exact (heq_map F _ _).symm.trans (heq_of_eq h.symm)

end Functor.LaxMonoidal.Graded

end Graded

end CategoryTheory
