import CubeChains.Arrangements.Braid
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Action.Defs

/-!
# Arrangements/BraidSymmetry — the `Sₙ` reorientation action on the braid COM

The symmetric group `Sₙ = Equiv.Perm (Fin n)` acts on heights by precomposition `x ↦ x ∘ σ⁻¹`.
On sign vectors this is the **reorientation** `reorient σ`: a signed relabeling of the ground set
`{i < j}` that reads off `σ⁻¹`'s image and flips sign when the relabeled pair is inverted.  It is
equivariant with `braidSign` (`reorient_braidSign`), a left `MulAction`, and a COM-automorphism of
`braidCOM n` (preserves covectors, the face order, and topes).

Internally a covector `V` is extended antisymmetrically to all ordered pairs by `signAt V p q`
(`= V{p,q}` if `p<q`, its negation if `p>q`, `0` on the diagonal), and
`reorient σ V {i,j} = signAt V (σ⁻¹ i) (σ⁻¹ j)`.
-/

open SignType

namespace CubeChains

variable {n : ℕ}

/-! ### The antisymmetric extension of a covector to all ordered pairs -/

/-- Antisymmetric extension: `V{p,q}` for `p<q`, `-V{q,p}` for `q<p`, `0` on the diagonal. -/
def signAt (V : SignVec (BraidGround n)) (p q : Fin n) : SignType :=
  if h : p < q then V ⟨(p, q), h⟩
  else if h' : q < p then - V ⟨(q, p), h'⟩
  else 0

theorem signAt_lt (V : SignVec (BraidGround n)) {p q : Fin n} (h : p < q) :
    signAt V p q = V ⟨(p, q), h⟩ := by
  unfold signAt; rw [dif_pos h]

theorem signAt_gt (V : SignVec (BraidGround n)) {p q : Fin n} (h : q < p) :
    signAt V p q = - V ⟨(q, p), h⟩ := by
  unfold signAt; rw [dif_neg (not_lt.mpr h.le), dif_pos h]

theorem signAt_self (V : SignVec (BraidGround n)) (p : Fin n) : signAt V p p = 0 := by
  unfold signAt; rw [dif_neg (lt_irrefl p), dif_neg (lt_irrefl p)]

/-- `signAt` is antisymmetric in its two indices. -/
theorem signAt_antisymm (V : SignVec (BraidGround n)) (p q : Fin n) :
    signAt V q p = - signAt V p q := by
  rcases lt_trichotomy p q with h | h | h
  · rw [signAt_gt V h, signAt_lt V h]
  · subst h; rw [signAt_self, neg_zero]
  · rw [signAt_lt V h, signAt_gt V h, neg_neg]

/-- On an actual ground element (where `i<j`) the extension returns the coordinate itself. -/
theorem signAt_of_pair (V : SignVec (BraidGround n)) (e : BraidGround n) :
    signAt V e.1.1 e.1.2 = V e := by
  rw [signAt_lt V e.2]; congr 1

/-! ### The reorientation -/

/-- The reorientation of `σ`: signed relabeling of the ground set by `σ⁻¹`. -/
def reorient (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) : SignVec (BraidGround n) :=
  fun e => signAt V (σ⁻¹ e.1.1) (σ⁻¹ e.1.2)

theorem reorient_apply (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) (e : BraidGround n) :
    reorient σ V e = signAt V (σ⁻¹ e.1.1) (σ⁻¹ e.1.2) := rfl

/-- Reorienting inside the extension is precomposition of the indices by `τ⁻¹`. -/
theorem signAt_reorient (τ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) (p q : Fin n) :
    signAt (reorient τ V) p q = signAt V (τ⁻¹ p) (τ⁻¹ q) := by
  rcases lt_trichotomy p q with h | h | h
  · exact (signAt_lt _ h).trans rfl
  · subst h; simp only [signAt_self]
  · rw [signAt_gt _ h]
    change - signAt V (τ⁻¹ q) (τ⁻¹ p) = signAt V (τ⁻¹ p) (τ⁻¹ q)
    rw [signAt_antisymm V (τ⁻¹ p) (τ⁻¹ q), neg_neg]

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
    reorient σ⁻¹ (reorient σ V) = V := by
  rw [← reorient_mul, inv_mul_cancel, reorient_one]

theorem reorient_inv_right (σ : Equiv.Perm (Fin n)) (V : SignVec (BraidGround n)) :
    reorient σ (reorient σ⁻¹ V) = V := by
  rw [← reorient_mul, mul_inv_cancel, reorient_one]

/-! ### Equivariance with `braidSign` -/

theorem signAt_braidSign (x : Fin n → ℤ) (p q : Fin n) :
    signAt (braidSign x) p q = sign (x p - x q) := by
  rcases lt_trichotomy p q with h | h | h
  · rw [signAt_lt _ h, braidSign_apply]
  · subst h; rw [signAt_self, sub_self, sign_zero]
  · rw [signAt_gt _ h, braidSign_apply, ← Left.sign_neg, neg_sub]

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

/-- The disjunction defining `⊑` is preserved coordinatewise by the antisymmetric extension. -/
theorem signAt_faceLE {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) (p q : Fin n) :
    signAt X p q = 0 ∨ signAt X p q = signAt Y p q := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · rw [signAt_lt X hpq, signAt_lt Y hpq]; exact h _
  · subst hpq; left; exact signAt_self _ _
  · rw [signAt_gt X hpq, signAt_gt Y hpq]
    rcases h ⟨(q, p), hpq⟩ with h0 | he
    · left; rw [h0, neg_zero]
    · right; rw [he]

/-- Reorientation preserves the face order. -/
theorem reorient_faceLE (σ : Equiv.Perm (Fin n)) {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) :
    reorient σ X ⊑ reorient σ Y := by
  intro e
  rw [reorient_apply, reorient_apply]
  exact signAt_faceLE h _ _

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
