import CubeChains.Machinery.Arrangement.Braid
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Action.Defs

/-!
# Machinery/Arrangement/BraidSymmetry — the `Sₙ` reorientation action on the braid COM

The symmetric group `Sₙ = Equiv.Perm (Fin n)` acts on heights by precomposition `x ↦ x ∘ σ⁻¹`.
On sign vectors this is the **reorientation** `reorient σ V {i,j} = signAt V (σ⁻¹ i) (σ⁻¹ j)`:
a signed relabeling of the ground set `{i < j}`, read through the antisymmetric extension
`signAt` (`Machinery/Arrangement/Braid.lean`), which supplies the sign flip when the relabeled pair
comes out inverted.  It is equivariant with `braidSign` (`reorient_braidSign`), a left `MulAction`,
and a COM-automorphism of `braidCOM n` (preserves covectors, the face order, and topes).
-/

open SignType

namespace CubeChains

variable {n : ℕ}

/-! ### The reorientation -/

/-- The reorientation of `σ`: signed relabeling of the ground set by `σ⁻¹`. -/
def reorient (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) : SignVec (BraidGround n) :=
  fun e => signAt V (σ⁻¹ e.1.1) (σ⁻¹ e.1.2)

theorem reorient_apply (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) (e : BraidGround n) :
    reorient σ V e = signAt V (σ⁻¹ e.1.1) (σ⁻¹ e.1.2) := rfl

/-- Reorienting inside the extension is precomposition of the indices by `τ⁻¹`. -/
theorem signAt_reorient (τ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) (p q : Fin n) :
    signAt (reorient τ V) p q = signAt V (τ⁻¹ p) (τ⁻¹ q) :=
  signAt_ext (G := fun p q => signAt V (τ⁻¹ p) (τ⁻¹ q))
    (fun p q => signAt_antisymm V (τ⁻¹ p) (τ⁻¹ q)) (fun _ => rfl) p q

/-! ### Group action -/

theorem reorient_one (V : SignVec (BraidGround n)) : reorient (1 : Equiv.Perm (Fin n)) V = V := by
  funext e
  rw [reorient_apply]
  simp only [inv_one, Equiv.Perm.one_apply]
  exact signAt_of_pair V e

/-- Left action: `reorient (σ * τ) = reorient σ ∘ reorient τ`. -/
theorem reorient_mul (σ τ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) :
    reorient (σ * τ) V = reorient σ (reorient τ V) := by
  funext e
  rw [reorient_apply, reorient_apply, signAt_reorient, mul_inv_rev, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]

instance : MulAction (Equiv.Perm (Fin n)) (SignVec (BraidGround n)) where
  smul := reorient
  one_smul := reorient_one
  mul_smul := reorient_mul

theorem reorient_inv_left (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) :
    reorient σ⁻¹ (reorient σ V) = V := inv_smul_smul σ V

theorem reorient_inv_right (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) :
    reorient σ (reorient σ⁻¹ V) = V := smul_inv_smul σ V

/-! ### Equivariance with `braidSign` -/

/-- **Equivariance:** `reorient σ (braidSign x) = braidSign (x ∘ σ⁻¹)`. -/
theorem reorient_braidSign (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) :
    reorient σ (braidSign x) = braidSign (fun i => x (σ⁻¹ i)) := by
  funext e
  rw [reorient_apply, signAt_braidSign, braidSign_apply]

/-! ### COM-automorphism of the braid arrangement -/

theorem reorient_mem_covectors (σ : Equiv.Perm (Fin n)) {V : SignVec (BraidGround n)}
    (hV : V ∈ braidCovectors n) : reorient σ V ∈ braidCovectors n := by
  obtain ⟨x, rfl⟩ := hV
  rw [reorient_braidSign]
  exact ⟨_, rfl⟩

/-- Reorientation preserves the face order. -/
theorem reorient_faceLE (σ : Equiv.Perm (Fin n)) {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) :
    reorient σ X ⊑ reorient σ Y := by
  intro e
  rw [reorient_apply, reorient_apply]
  exact faceLE_iff_signAt.mp h _ _

/-- Reorientation preserves topes (chambers). -/
theorem reorient_isTope (σ : Equiv.Perm (Fin n)) {T : SignVec (BraidGround n)}
    (h : (braidCOM n).IsTope T) : (braidCOM n).IsTope (reorient σ T) := by
  obtain ⟨hmem, hmax⟩ := h
  refine ⟨reorient_mem_covectors σ hmem, ?_⟩
  intro X hX hle
  have hX' : reorient σ⁻¹ X ∈ (braidCOM n).covectors := reorient_mem_covectors σ⁻¹ hX
  have hle' : T ⊑ reorient σ⁻¹ X := by
    have := reorient_faceLE σ⁻¹ hle
    rwa [reorient_inv_left] at this
  have hTeq : reorient σ⁻¹ X = T := hmax _ hX' hle'
  calc X = reorient σ (reorient σ⁻¹ X) := (reorient_inv_right σ X).symm
    _ = reorient σ T := by rw [hTeq]

end CubeChains
