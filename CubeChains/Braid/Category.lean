import CubeChains.Braid.Jux
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Braid/Category — the braid category `𝔅` and its tensor

An object is a **strand count** and nothing more; `Hom(n,n) = Braid n`; there are no morphisms
between different counts.  The tensor is juxtaposition, so `n ⊗ m = n + m`.

Objects carrying no data is the whole point: associativity of `⊗` is `Nat.add_assoc`, not a `HEq`
across Salvetti cells.

Gotcha (inherited from `Salvetti/BraidDeloop`): a direct pattern-match on a *pair* of `SigmaHom`s
makes the equation compiler diverge — the index `?i + ?j` is not a unification pattern.  Hence the
`Sigma.desc`/`curryObj` detour in `braidsTensor`.
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

/-! ## The tensor -/

/-- Juxtaposition at fixed strand counts.  Functoriality *is* `juxHom` being a homomorphism. -/
def juxFunctor (n m : ℕ) : BraidFib n × BraidFib m ⥤ BraidFib (n + m) where
  obj _ := SingleObj.star _
  map {_ _} f := juxHom n m ((f.1, f.2) : Braid n × Braid m)
  map_id _ := map_one (juxHom n m)
  map_comp {_ _ _} f g := by
    rw [SingleObj.comp_as_mul]
    exact map_mul (juxHom n m) ((g.1, g.2) : Braid n × Braid m) ((f.1, f.2) : Braid n × Braid m)

/-- Juxtaposing `x` (on `i` strands) with the `j`-strand braids. -/
def juxFam (i j : ℕ) (x : BraidFib i) : BraidFib j ⥤ Braids :=
  (Functor.curryObj (juxFunctor i j)).obj x ⋙ braidIncl (i + j)

/-- Juxtaposition with a fixed left-hand braid. -/
def juxCurry (i : ℕ) : BraidFib i ⥤ (Braids ⥤ Braids) where
  obj x := Sigma.desc fun j => juxFam i j x
  map {x y} f := Sigma.natTrans fun j =>
    (Sigma.inclDesc (fun j => juxFam i j x) j).hom ≫
      Functor.whiskerRight ((Functor.curryObj (juxFunctor i j)).map f) (braidIncl (i + j)) ≫
      (Sigma.inclDesc (fun j => juxFam i j y) j).inv
  map_id x := by
    ext ⟨j, y⟩
    simp [Functor.curryObj, juxFam]
  map_comp f g := by
    ext ⟨j, y⟩
    simp [Functor.curryObj, juxFam]

/-- **The tensor of the braid category**: juxtapose, and strand counts add. -/
def braidsTensor : Braids × Braids ⥤ Braids :=
  Functor.uncurry.obj (Sigma.desc juxCurry)

@[simp] theorem braidsTensor_obj (n m : ℕ) :
    braidsTensor.obj (strands n, strands m) = strands (n + m) := rfl

/-- **Composition maps to juxtaposition** — the equation the braid 2-functor has to satisfy. -/
@[simp] theorem braidsTensor_map {n m : ℕ} (a : Braid n) (b : Braid m) :
    braidsTensor.map (X := (strands n, strands m)) (Y := (strands n, strands m))
      (braidHom a, braidHom b) = braidHom (juxHom n m (a, b)) := by
  suffices h : (braidHom (juxL n m a) ≫ braidHom (juxR n m b) :
      strands (n + m) ⟶ strands (n + m)) = braidHom (juxHom n m (a, b)) by
    simpa [braidsTensor, Functor.uncurry, juxCurry, juxFam, Functor.curryObj, juxFunctor, braidHom,
      SingleObj.id_as_one] using h
  rw [juxHom_eq]
  exact congrArg SigmaHom.mk
    ((SingleObj.comp_as_mul (M := Braid (n + m)) (f := juxL n m a) (g := juxR n m b)).trans
      (juxL_commute_juxR a b).symm)

/-- The unit: the empty braid on no strands.  An identity execution has no events. -/
abbrev braidsUnit : Braids := strands 0

end CubeChains
