import CubeChains.Braid.JuxAssoc
import Mathlib.CategoryTheory.Bicategory.CatEnriched

/-!
# Braid/Deloop — coherence of the braid tensor, for the delooping

The delooping is `EnrichedCategory Cat` on one object, hom-object `Braids`, composition
`braidsTensor` (juxtaposition, so `n ⊗ m = n + m`).  Its `assoc`/`id_comp`/`comp_id` axioms need
`braidsTensor` to be associative and unital as a *functor* — on objects (`Nat.add_assoc`) and on
morphisms (`juxHom_assoc`, `Braid/JuxAssoc`).  This file supplies those inputs.

Not `Salvetti/BraidDeloop`'s version: that composed through `freeGroupoidProdEquiv = Localization.uniq`,
pinned only up to natural iso, so it could never satisfy the enriched `assoc` — an *equality* of
functors.  Here composition is `braidsTensor`, and the coherence is strict.
-/

open CategoryTheory

namespace CubeChains

/-! ## `braidCast` cancels its inverse, and `eqToHom`-conjugation of a braid -/

theorem braidCast_braidCast {n m : ℕ} (h : n = m) (x : Braid n) :
    braidCast h.symm (braidCast h x) = x := by
  subst h; rfl

theorem strands_inj {p q : ℕ} (h : strands p = strands q) : p = q :=
  congrArg Sigma.fst h

/-- Conjugating a braid by an `eqToHom` recast, proof-irrelevantly (`h` is any proof of the object
equation).  This is what dodges the mismatch between the `eqToHom` produced by `Functor.ext`'s object
half and the one `braidHom` lemmas expect. -/
theorem eqToHom_braidHom_eqToHom {p q : ℕ} (h : strands p = strands q) (b : Braid q) :
    eqToHom h ≫ braidHom b ≫ eqToHom h.symm = braidHom (braidCast (strands_inj h).symm b) := by
  obtain rfl : p = q := strands_inj h
  simp [braidCast]

/-! ## `braidsTensor` is associative and unital, on objects and on morphisms

The strand count adds, so associativity is `Nat.add_assoc` on objects and `juxHom_assoc` on
morphisms; the unit `strands 0` contributes no strand. -/

theorem braidsTensor_obj_assoc (n m k : ℕ) :
    braidsTensor.obj (braidsTensor.obj (strands n, strands m), strands k)
      = braidsTensor.obj (strands n, braidsTensor.obj (strands m, strands k)) := by
  simp only [braidsTensor_obj]
  rw [Nat.add_assoc]

theorem braidsTensor_obj_id_left (n : ℕ) :
    braidsTensor.obj (braidsUnit, strands n) = strands n := by
  simp only [braidsUnit, braidsTensor_obj, Nat.zero_add]

theorem braidsTensor_obj_id_right (n : ℕ) :
    braidsTensor.obj (strands n, braidsUnit) = strands n := rfl

/-- **Juxtaposition is associative on morphisms**, in braid form — the input the delooping's `assoc`
axiom needs, one `eqToHom`-transport short of the enriched shape.  The remaining step is matching the
`eqToHom` produced by `Functor.ext`'s object half (implicit args `braidsTensor.obj (…)`) against the
one `braidHom` lemmas expect (implicit args `strands (…)`); they are defeq but not syntactic. -/
theorem braidsTensor_map_assoc {n m k : ℕ} (a : Braid n) (b : Braid m) (c : Braid k) :
    braidsTensor.map (X := (strands (n + m), strands k)) (Y := (strands (n + m), strands k))
        (braidsTensor.map (X := (strands n, strands m)) (Y := (strands n, strands m))
          (braidHom a, braidHom b), braidHom c)
      = braidHom (juxHom (n + m) k (juxHom n m (a, b), c)) := by
  rw [braidsTensor_map, braidsTensor_map]

end CubeChains
