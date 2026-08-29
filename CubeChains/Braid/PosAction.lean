import CubeChains.Braid.PosGerm
import Mathlib.CategoryTheory.Action

/-!
# Braid/PosAction — the positive braids acting on the orderings

`PosBraidAction n` is `Perm (Fin n)` made a category by `PosBraid n`: an arrow `x ⟶ y` is a
positive braid whose permutation carries `x` to `y`.  The action has to be **left** multiplication
through `posPermHom` — `x * posPermHom β` is a right action.  Every endomorphism monoid is
`PosPureBraid n`, and `PosBraid n` has no non-trivial units, so the only isomorphisms are the
identities: a category, where `BraidAction n` is a connected groupoid.

⚠ `SingleObj` hom types defeat elaboration: `f.val = 1` needs the numeral ascribed, and `End x`
its category (`@End (PosBraidAction n) _ x`).
-/

open CategoryTheory Equiv MulAction

namespace CubeChains

variable {n : ℕ}

/-! ### The action -/

/-- The positive braids act on the orderings through their permutation. -/
instance : MulAction (PosBraid n) (Perm (Fin n)) :=
  MulAction.compHom _ (posPermHom n)

@[simp] theorem posBraid_smul (β : PosBraid n) (x : Perm (Fin n)) :
    β • x = posPermHom n β * x := rfl

/-- **The positive braids acting on the orderings**: objects the orderings of the strands, arrows
the positive braids realising the change of ordering. -/
abbrev PosBraidAction (n : ℕ) : Type := ActionCategory (PosBraid n) (Perm (Fin n))

/-- Multiplication is free, so a braid fixing one ordering fixes every ordering. -/
theorem stabilizerSubmonoid_eq_posPureBraid (x : Perm (Fin n)) :
    stabilizerSubmonoid (PosBraid n) x = PosPureBraid n := by
  ext β
  rw [mem_stabilizerSubmonoid_iff, posBraid_smul, mem_posPureBraid, mul_eq_right]

/-- **The loops at any ordering are the positive pure braids.** -/
def endEquivPosPure (p : PosBraidAction n) :
    @End (PosBraidAction n) _ p ≃* PosPureBraid n :=
  (ActionCategory.stabilizerIsoEnd (PosBraid n) p.back).symm.trans
    (MulEquiv.submonoidCongr (stabilizerSubmonoid_eq_posPureBraid p.back))

/-! ### No units, hence no isomorphisms -/

theorem val_eq_one_of_isIso {p q : PosBraidAction n} (f : p ⟶ q) [IsIso f] :
    f.val = (1 : PosBraid n) := by
  have h := congrArg Subtype.val (IsIso.inv_hom_id (f := f))
  rw [ActionCategory.comp_val, ActionCategory.id_val] at h
  exact eq_one_of_mul_eq_one h

/-- **Distinct orderings are non-isomorphic.** -/
theorem eq_of_isIso {p q : PosBraidAction n} (f : p ⟶ q) [IsIso f] : p = q := by
  have h2 : posPermHom n f.val * p.back = q.back := f.2
  rw [val_eq_one_of_isIso f, map_one, one_mul] at h2
  exact (ActionCategory.back_coe p).symm.trans (by rw [h2]; exact ActionCategory.back_coe q)

/-- **The only isomorphisms of `PosBraidAction n` are the identities.** -/
theorem isIso_iff_eq_id {p : PosBraidAction n} (f : @End (PosBraidAction n) _ p) :
    IsIso f ↔ f = 𝟙 p :=
  ⟨fun _ => Subtype.ext ((val_eq_one_of_isIso f).trans (ActionCategory.id_val p).symm),
    fun h => h ▸ inferInstance⟩

/-! ### The contrast with the group

`permHom` is onto, so `Braid n` acts transitively and its action groupoid is connected: every
ordering is reachable from every other, reversibly. -/

instance : MulAction (Braid n) (Perm (Fin n)) := MulAction.compHom _ (permHom n)

@[simp] theorem braid_smul (b : Braid n) (x : Perm (Fin n)) : b • x = permHom n b * x := rfl

/-- **The braid group acting on the orderings** — a groupoid, `Braid n` being a group. -/
abbrev BraidAction (n : ℕ) : Type := ActionCategory (Braid n) (Perm (Fin n))

instance : IsPretransitive (Braid n) (Perm (Fin n)) :=
  ⟨fun x y => ⟨ofPerm (y * x⁻¹), by simp⟩⟩

theorem isConnected_braidAction : IsConnected (BraidAction n) := inferInstance

end CubeChains
