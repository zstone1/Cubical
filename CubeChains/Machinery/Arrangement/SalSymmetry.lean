import CubeChains.Machinery.Arrangement.BraidSymmetry
import CubeChains.Machinery.Arrangement.Sal

/-!
# Machinery/Arrangement/SalSymmetry — the `Sₙ` action on the Salvetti poset of the braid COM

`reorient` is a COM-automorphism of `braidCOM n` (`Machinery/Arrangement/BraidSymmetry.lean`), so
it acts cellwise on Salvetti cells `(X, T)`.  It also commutes with wall crossing
(`reorient_comp`), which is what makes the action *order*-preserving for the Salvetti/Paris order.

The chains it transports to are `Ch (Hbp □ⁿ)`, across `hbpBraidSalEquiv`
(`Concurrency/Complexification/SymReorient`).
-/

open SignType CategoryTheory

namespace CubeChains

variable {n : ℕ}

/-! ### Reorientation commutes with wall crossing -/

/-- Reorientation is a homomorphism for wall crossing. -/
theorem reorient_comp (σ : Equiv.Perm (Fin n)) (X T : SignVec (BraidGround n)) :
    reorient σ (X ⊙ T) = reorient σ X ⊙ reorient σ T := by
  funext e
  rw [reorient_apply, signAt_comp]
  simp only [SignVec.comp, reorient_apply]

/-! ### The action on Salvetti cells -/

/-- Reorientation acts on a Salvetti cell componentwise. -/
instance : MulAction (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  smul σ a := ⟨(reorient σ a.face, reorient σ a.tope),
    reorient_mem_covectors σ a.2.1, reorient_isTope σ a.2.2.1, reorient_faceLE σ a.2.2.2⟩
  one_smul _ := Subtype.ext (Prod.ext (reorient_one _) (reorient_one _))
  mul_smul _ _ _ := Subtype.ext (Prod.ext (reorient_mul _ _ _) (reorient_mul _ _ _))

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
form the chain-side reorientation conjugates across `hbpBraidSalEquiv`. -/
def salReorientFunctor (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) ⥤ Sal (braidCOM n) :=
  (salReorient_monotone σ).functor

@[simp] theorem salReorientFunctor_obj (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (salReorientFunctor σ).obj a = σ • a := rfl

end CubeChains
