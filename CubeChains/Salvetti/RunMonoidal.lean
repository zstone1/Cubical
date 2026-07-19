import CubeChains.Chains.Segal
import CubeChains.Foundations.WedgeMonoidal
import Mathlib.CategoryTheory.Monoidal.Discrete

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

/-- A length n sequence of 1s -/
def runDims (n : ℕ) : List ℕ+ := List.replicate n 1
@[simp]
theorem runDims_replicate (n : ℕ) : runDims n = List.replicate n 1 := rfl

def run (n : ℕ) : BPSet := ⋁ (runDims n)

def runSl (n : ℕ) : wedge2 (□ (↑ 1)) (run n) ≅ run (n + 1) := Iso.refl _

def runSr (n : ℕ) : wedge2 (run n) (□ (↑ 1)) ≅ run (n + 1) := by
  refine calc wedge2 (run n) (□ (↑ 1))
      ≅ wedge2 (run n) (⋁[1])   := whiskerLeftIso _ (serialWedge1 1).symm
    _ ≅ ⋁(runDims n ++ [1])     := serialWedgeAppend (runDims n) [1]
    _ ≅ run (n + 1)             := eqToIso (congrArg BPSet.serialWedge ?_)
  -- ⊢ runDims n ++ [1] = runDims (n + 1)
  simp only [runDims_replicate]
  rw [show ([1] : List ℕ+) = List.replicate 1 1 from rfl, List.replicate_append_replicate]

def runPlus : (m n : ℕ)  → (run (n + m)) ≅ wedge2 (run n) (run m)
  | 0, _ => (ρ_ _).symm
  | m + 1 , n =>
      calc run (n + (m + 1))
          ≅ wedge2 (run (n + m)) (□ (↑ 1))              := (runSr (n + m)).symm
        _ ≅ wedge2 (wedge2 (run n) (run m)) (□ (↑ 1))   := whiskerRightIso (runPlus m n) _
        _ ≅ wedge2 (run n) (wedge2 (run m) (□ (↑ 1)))   := α_ _ _ _
        _ ≅ wedge2 (run n) (run (m + 1))                := whiskerLeftIso _ (runSr m)

/-- `run` as a functor from the discrete `+`-monoidal category on `ℕ`. -/
def runFunctor : Discrete ℕ ⥤ WedgeBP := Discrete.functor run

@[simp] theorem runFunctor_obj (n : ℕ) : runFunctor.obj ⟨n⟩ = run n := rfl

/-- The tensorator `run m ∨ run n ⟶ run (m + n)`, from `runPlus`; unit `run 0 = □0`. -/
instance : runFunctor.LaxMonoidal where
  ε := 𝟙 _
  μ m n := (runPlus n.as m.as).inv
  μ_natural_left := by
    rintro ⟨m⟩ ⟨n⟩ f ⟨k⟩
    obtain rfl : m = n := Discrete.eq_of_hom f
    rw [Subsingleton.elim f (𝟙 _)]; simp
  μ_natural_right := by
    rintro ⟨m⟩ ⟨n⟩ ⟨k⟩ f
    obtain rfl : m = n := Discrete.eq_of_hom f
    rw [Subsingleton.elim f (𝟙 _)]; simp
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

end CubeChains
