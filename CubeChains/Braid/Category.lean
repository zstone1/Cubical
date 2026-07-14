import CubeChains.Braid.Germ
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Braid/Category — the braid category `𝔅`

An object is a **strand count** and nothing more; `Hom(n,n) = Braid n`; there are no morphisms
between different counts.  This is the target of the braid grading `braidGrpd` (`Braid/Grading`): a
groupoid, because braids are invertible, which is what lets `FreeGroupoid.lift` land in it.
-/

namespace CubeChains

open CategoryTheory CategoryTheory.Sigma

/-- The fibre of `𝔅` over a strand count: one object, and the braids on `n` strands. -/
abbrev BraidFib (n : ℕ) : Type := SingleObj (Braid n)

/-- **The braid category**: objects are strand counts, morphisms are braids. -/
abbrev Braids : Type := Σ n : ℕ, BraidFib n

/-- The width-`n` fibre, included into `𝔅`. -/
abbrev braidIncl (n : ℕ) : BraidFib n ⥤ Braids := Sigma.incl (C := BraidFib) n

/-- The object on `n` strands. -/
abbrev strands (n : ℕ) : Braids := ⟨n, SingleObj.star (Braid n)⟩

/-- A braid, read as a morphism of `𝔅`. -/
abbrev braidHom {n : ℕ} (b : Braid n) : strands n ⟶ strands n := SigmaHom.mk b

/-- Braids are invertible, so `𝔅` is a groupoid — which is what lets `FreeGroupoid.lift` land
in it. -/
instance : Groupoid Braids where
  inv := fun {_ _} f => match f with
    | SigmaHom.mk g => SigmaHom.mk (Groupoid.inv g)
  inv_comp := fun {_ _} f => match f with
    | SigmaHom.mk g => congrArg SigmaHom.mk (Groupoid.inv_comp g)
  comp_inv := fun {_ _} f => match f with
    | SigmaHom.mk g => congrArg SigmaHom.mk (Groupoid.comp_inv g)

end CubeChains
