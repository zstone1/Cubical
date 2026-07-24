import CubeChains.Braid.Germ
import Mathlib.CategoryTheory.Groupoid

/-!
# Braid/Full — the union of all braid groups as one groupoid

`FullBraid` has a strand count for each object and `End n = Braid n`; there are no morphisms between
different counts.  A morphism carries its braid on the **source** count, so the strand-count
transport lives once, in composition — a functor *into* `FullBraid` maps each arrow to its braid with
no `eqToHom` bookkeeping.  (Contrast `Braid/Category`'s `Braids = Σ n, SingleObj (Braid n)`, whose
`SigmaHom` encoding pushes that transport onto every client.)
-/

open CategoryTheory

namespace CubeChains

/-- A morphism of `FullBraid`: the (forced) equality of strand counts, and a braid on the source
count. -/
@[ext]
structure FullBraidHom (m n : ℕ) where
  /-- Source and target strand counts agree — `FullBraid` has no cross-count morphisms. -/
  strandsEq : m = n
  /-- The braid, on the source count. -/
  braid : Braid m

/-- **The full braid groupoid**: strand counts as objects, braids as (endo)morphisms. -/
def FullBraid : Type := ℕ

namespace FullBraid

instance : Category FullBraid where
  Hom m n := FullBraidHom m n
  id _ := ⟨rfl, 1⟩
  comp f g := ⟨f.strandsEq.trans g.strandsEq, (f.strandsEq.symm ▸ g.braid) * f.braid⟩
  id_comp f := by obtain ⟨h, b⟩ := f; subst h; simp
  comp_id f := by obtain ⟨h, b⟩ := f; subst h; simp
  assoc f g k := by
    obtain ⟨hf, bf⟩ := f; obtain ⟨hg, bg⟩ := g; obtain ⟨hk, bk⟩ := k
    subst hf; subst hg; subst hk; simp [mul_assoc]

instance : Groupoid FullBraid where
  inv f := ⟨f.strandsEq.symm, f.strandsEq ▸ f.braid⁻¹⟩
  inv_comp f := by obtain ⟨h, b⟩ := f; subst h; exact FullBraidHom.ext (mul_inv_cancel b)
  comp_inv f := by obtain ⟨h, b⟩ := f; subst h; exact FullBraidHom.ext (inv_mul_cancel b)

/-- A braid, read as an endomorphism of its strand count. -/
def ofBraid {n : ℕ} (b : Braid n) : @Quiver.Hom FullBraid _ n n := ⟨rfl, b⟩

@[simp] theorem ofBraid_one (n : ℕ) :
    ofBraid (1 : Braid n) = @CategoryStruct.id FullBraid _ n := rfl

/-- `ofBraid` is multiplicative in the concurrency convention `p (f ≫ g) = p g * p f`. -/
@[simp] theorem ofBraid_comp {n : ℕ} (a b : Braid n) :
    ofBraid a ≫ ofBraid b = ofBraid (b * a) := rfl

end FullBraid

end CubeChains
