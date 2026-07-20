import CubeChains.Arrangements.BraidSymmetry
import CubeChains.Arrangements.Sal

/-!
# Arrangements/SalSymmetry — the `Sₙ` action on the Salvetti poset of the braid COM

`reorient` is a COM-automorphism of `braidCOM n` (`Arrangements/BraidSymmetry.lean`), so it acts
cellwise on Salvetti cells `(X, T)`.  It also commutes with wall crossing (`reorient_comp`), which
is what makes the action *order*-preserving for the Salvetti/Paris order.

This is the model of the action; the executions it is transported to are `Salvetti/CubeSymmetry`.
-/

open SignType CategoryTheory

namespace CubeChains

variable {n : ℕ}

/-! ### Reorientation commutes with wall crossing -/

/-- The antisymmetric extension of a composite is the composite of the extensions. -/
theorem signAt_comp (X T : SignVec (BraidGround n)) (p q : Fin n) :
    signAt (X ⊙ T) p q = if signAt X p q = 0 then signAt T p q else signAt X p q := by
  rcases lt_trichotomy p q with h | h | h
  · rw [signAt_lt _ h, signAt_lt X h, signAt_lt T h]; rfl
  · subst h; rw [signAt_self, signAt_self, if_pos rfl, signAt_self]
  · rw [signAt_gt _ h, signAt_gt X h, signAt_gt T h]
    change -(if X ⟨(q, p), h⟩ = 0 then T ⟨(q, p), h⟩ else X ⟨(q, p), h⟩)
        = if -X ⟨(q, p), h⟩ = 0 then _ else _
    by_cases h0 : X ⟨(q, p), h⟩ = 0
    · rw [if_pos h0, if_pos (SignType.neg_eq_zero_iff.mpr h0)]
    · rw [if_neg h0, if_neg (fun hc => h0 (SignType.neg_eq_zero_iff.mp hc))]

/-- Reorientation is a homomorphism for wall crossing. -/
theorem reorient_comp (σ : Equiv.Perm (Fin n)) (X T : SignVec (BraidGround n)) :
    reorient σ (X ⊙ T) = reorient σ X ⊙ reorient σ T := by
  funext e
  rw [reorient_apply, signAt_comp]
  simp only [SignVec.comp, reorient_apply]

/-! ### The action on Salvetti cells -/

/-- Reorientation of a Salvetti cell, componentwise. -/
def salReorient (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) : Sal (braidCOM n) :=
  ⟨(reorient σ a.face, reorient σ a.tope),
    reorient_mem_covectors σ a.2.1,
    reorient_isTope σ a.2.2.1,
    reorient_faceLE σ a.2.2.2⟩

instance : MulAction (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  smul := salReorient
  one_smul _ := Subtype.ext (Prod.ext (reorient_one _) (reorient_one _))
  mul_smul _ _ _ := Subtype.ext (Prod.ext (reorient_mul _ _ _) (reorient_mul _ _ _))

theorem salReorient_smul (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    σ • a = salReorient σ a := rfl

@[simp] theorem smul_face (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (σ • a).face = reorient σ a.face := rfl

@[simp] theorem smul_tope (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (σ • a).tope = reorient σ a.tope := rfl

/-! ### Order preservation -/

/-- Reorientation preserves the Salvetti/Paris order: the face part is `reorient_faceLE`, the
tope part is `reorient_comp`. -/
theorem salReorient_monotone (σ : Equiv.Perm (Fin n)) :
    Monotone (fun a : Sal (braidCOM n) => σ • a) := by
  intro a b hab
  exact ⟨reorient_faceLE σ hab.1, by
    rw [smul_tope, smul_tope, smul_face, hab.2, reorient_comp]⟩

/-- Reorientation as an endofunctor of the Salvetti poset, with `obj` defeq to `σ • ·` — the
form `chStarReorient` conjugates across `braidSalEquiv`. -/
def salReorientFunctor (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) ⥤ Sal (braidCOM n) :=
  (salReorient_monotone σ).functor

@[simp] theorem salReorientFunctor_obj (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (salReorientFunctor σ).obj a = σ • a := rfl

end CubeChains
