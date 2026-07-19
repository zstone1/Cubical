import CubeChains.Chains.Segal
import CubeChains.Foundations.WedgeMonoidal
import CubeChains.Chains.SerialWedgeFunctor
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Salvetti/RunMonoidal — the all-edges runs and `run` as a monoidal functor

`run n = ⋁(1ⁿ)` is the finest chain shape; `runPlus`/`runSl`/`runSr` are its wedge-splitting isos,
and `run` is packaged as a (strong) monoidal functor `(ℕ,+) ⥤ (WedgeBP, ∨)` with tensorator
`runPlus`.  The retraction machinery (`Run`, `runRetract`, `Chains/Salvetti/Lines`) builds on this.
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet MonoidalCategory

namespace CubeChains

attribute [local instance] ChainCat.wedgeMonoidal

/-- `n ↦ 1ⁿ`, the all-edges word; `Multiplicative` so that `⊗` on the source is `ℕ`'s `+`. -/
def runDimsObj (n : Multiplicative ℕ) : FreeMonoid ℕ+ :=
  FreeMonoid.ofList (List.replicate n.toAdd 1)

/-- The tensorator's content: concatenating all-edges words adds their lengths. -/
theorem runDimsObj_mul (m n : Multiplicative ℕ) :
    runDimsObj m * runDimsObj n = runDimsObj (m * n) :=
  congrArg FreeMonoid.ofList (List.replicate_append_replicate ..)

def RunDims : Discrete (Multiplicative ℕ) ⥤ DimList :=
  Discrete.functor (fun n => (Discrete.mk (runDimsObj n)))

/-- Strong monoidal: the coherence squares are equations in the thin category `DimList`. -/
instance : RunDims.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Discrete.eqToIso rfl
      μIso := fun X Y => Discrete.eqToIso (runDimsObj_mul X.as Y.as)
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

def Run : Discrete (Multiplicative ℕ) ⥤ BPSet := RunDims ⋙ serialWedgeFunctor

instance : Run.LaxMonoidal := inferInstance


--def runSl (n : ℕ) : wedge2 (□ (↑ 1)) (run n) ≅ run (n + 1) := Iso.refl _
--
--def runSr (n : ℕ) : wedge2 (run n) (□ (↑ 1)) ≅ run (n + 1) := by
--  refine calc wedge2 (run n) (□ (↑ 1))
--      ≅ wedge2 (run n) (⋁[1])   := whiskerLeftIso _ (serialWedge1 1).symm
--    _ ≅ ⋁(runDims n ++ [1])     := serialWedgeAppend (runDims n) [1]
--    _ ≅ run (n + 1)             := eqToIso (congrArg BPSet.serialWedge ?_)
--  -- ⊢ runDims n ++ [1] = runDims (n + 1)
--  simp only [runDims_replicate]
--  rw [show ([1] : List ℕ+) = List.replicate 1 1 from rfl, List.replicate_append_replicate]
--
--def runPlus : (m n : ℕ)  → (run (n + m)) ≅ wedge2 (run n) (run m)
--  | 0, _ => (ρ_ _).symm
--  | m + 1 , n =>
--      calc run (n + (m + 1))
--          ≅ wedge2 (run (n + m)) (□ (↑ 1))              := (runSr (n + m)).symm
--        _ ≅ wedge2 (wedge2 (run n) (run m)) (□ (↑ 1))   := whiskerRightIso (runPlus m n) _
--        _ ≅ wedge2 (run n) (wedge2 (run m) (□ (↑ 1)))   := α_ _ _ _
--        _ ≅ wedge2 (run n) (run (m + 1))                := whiskerLeftIso _ (runSr m)
--
--/-- `run` as a functor from the discrete `+`-monoidal category on `ℕ`. -/
--def runFunctor : Discrete ℕ ⥤ WedgeBP := Discrete.functor run
--
--@[simp] theorem runFunctor_obj (n : ℕ) : runFunctor.obj ⟨n⟩ = run n := rfl
--
--/-- The tensorator `run m ∨ run n ⟶ run (m + n)`, from `runPlus`; unit `run 0 = □0`. -/
--instance : runFunctor.LaxMonoidal where
--  ε := 𝟙 _
--  μ m n := (runPlus n.as m.as).inv
--  μ_natural_left := by
--    rintro ⟨m⟩ ⟨n⟩ f ⟨k⟩
--    obtain rfl : m = n := Discrete.eq_of_hom f
--    rw [Subsingleton.elim f (𝟙 _)]; simp
--  μ_natural_right := by
--    rintro ⟨m⟩ ⟨n⟩ ⟨k⟩ f
--    obtain rfl : m = n := Discrete.eq_of_hom f
--    rw [Subsingleton.elim f (𝟙 _)]; simp
--  associativity := by
--    intro x y z
--    rw [← Iso.inv_comp_eq]
--    rw [Iso.eq_comp_inv]
--
--    sorry
--  left_unitality := sorry
--  right_unitality := sorry
--
end CubeChains
