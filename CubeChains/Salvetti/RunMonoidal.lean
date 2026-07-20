import CubeChains.Foundations.HomMonoidal
import CubeChains.Chains.ChainSkeletal
import CubeChains.Chains.SerialWedgeFunctor
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Salvetti/RunMonoidal — runs as a lax monoidal functor of their shape

`OneD : (ℕ,+) ⥤ BPSet` sends `n` to the all-edges wedge `⋁(1ⁿ)`; `Src = OneD ∘ dimSum` reindexes it
by the target shape, so that

```
RunF k = (Src k ⟶ ⋁k) = (runObj (dimSum k) ⟶ ⋁k)
```

is `Functor.hom BPSet` composed with a `Functor.prod'` of two monoidal functors.  Its `μ` is
concatenation of runs and its coherence is inherited, not written: see `Foundations/HomMonoidal`.
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet MonoidalCategory

namespace CubeChains

/-- `n ↦ 1ⁿ`, the all-edges word; `Multiplicative` so that `⊗` on the source is `ℕ`'s `+`. -/
def onesObj (n : Multiplicative ℕ) : FreeMonoid ℕ+ :=
  FreeMonoid.ofList (List.replicate n.toAdd 1)

/-- The tensorator's content: concatenating all-edges words adds their lengths. -/
theorem onesObj_mul (m n : Multiplicative ℕ) :
    onesObj m * onesObj n = onesObj (m * n) :=
  congrArg FreeMonoid.ofList (List.replicate_append_replicate ..)

def Ones : Discrete (Multiplicative ℕ) ⥤ DimList :=
  Discrete.functor (fun n => (Discrete.mk (onesObj n)))

/-- Strong monoidal: the coherence squares are equations in the thin category `DimList`. -/
instance : Ones.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Discrete.eqToIso rfl
      μIso := fun X Y => Discrete.eqToIso (onesObj_mul X.as Y.as)
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

def OneD : Discrete (Multiplicative ℕ) ⥤ BPSet := Ones ⋙ serialWedgeFunctor

/-- **Strong**, not merely lax: concatenating runs needs the tensorator's *inverse* to split the
source `runObj (m₁ + m₂)` into `runObj m₁ ∨ runObj m₂`. -/
instance : OneD.Monoidal := inferInstanceAs ((Ones ⋙ serialWedgeFunctor).Monoidal)

/-- `□^∨(1ᵐ)` — the all-edges chain shape.  Going through `OneD` (rather than spelling `⋁(1ᵐ)`) is
what makes its tensorator available. -/
abbrev runObj (m : ℕ) : BPSet := OneD.obj (Discrete.mk (Multiplicative.ofAdd m))

/-- `runObj m` is the wedge of `m` edges — the bridge `simp` needs to see through `OneD`. -/
@[simp] theorem toList_ones (m : ℕ) :
    FreeMonoid.toList (Ones.obj (Discrete.mk (Multiplicative.ofAdd m))).as
      = List.replicate m (1 : ℕ+) := rfl

/-- **A run into `□ⁿ` has exactly `n` edges.**  `□ⁿ` is the one-bead wedge, so
`serialWedge_dimSum_eq` pins the length; no need to argue that a run meets each direction once. -/
theorem runObj_dim_eq {m n : ℕ} (x : runObj m ⟶ cube n) : m = n := by
  have hm : dimSum (List.replicate m (1 : ℕ+)) = m := by
    simp [dimSum, List.map_replicate, List.sum_replicate]
  cases n with
  | zero => simpa [hm] using serialWedge_dimSum_eq (cd := []) x
  | succ k =>
      have hx := serialWedge_dimSum_eq
        (x ≫ (serialWedge1 (⟨k + 1, Nat.succ_pos k⟩ : ℕ+)).inv)
      simpa [hm, dimSum] using hx

/-! ### The shape-indexed run functor

`Hom(runObj n, ⋁k)` is empty unless `n = dimSum k`, so reindexing `OneD` along `dimSum` gives a
functor whose value at `k` is *the* type of runs of shape `k`. -/

/-- Total dimension as a monoid hom — `dimSum` on lists, valued in `Multiplicative ℕ`. -/
def dimSumHom : FreeMonoid ℕ+ →* Multiplicative ℕ :=
  FreeMonoid.lift (fun d : ℕ+ => Multiplicative.ofAdd (d : ℕ))

@[simp] theorem dimSumHom_ofList (k : List ℕ+) :
    dimSumHom (FreeMonoid.ofList k) = Multiplicative.ofAdd (dimSum k) := by
  simp [dimSumHom, dimSum, FreeMonoid.lift, FreeMonoid.prodAux_eq, Function.comp_def]

/-- The source of a run, indexed by the target shape: `k ↦ runObj (dimSum k)`. -/
def Src : DimList ⥤ BPSet := Discrete.monoidalFunctor dimSumHom ⋙ OneD

instance : Src.Monoidal :=
  inferInstanceAs ((Discrete.monoidalFunctor dimSumHom ⋙ OneD).Monoidal)

@[simp] theorem Src_obj (k : List ℕ+) :
    Src.obj (Discrete.mk (FreeMonoid.ofList k)) = runObj (dimSum k) := by
  simp [Src, runObj, OneD]

/-- **Runs of a given shape**, as a functor of the shape:
`RunF k = (runObj (dimSum k) ⟶ ⋁k)`. -/
def RunF : DimList ⥤ Type :=
  Functor.prod' (discreteOp _ ⋙ Src.op) serialWedgeFunctor ⋙ Functor.hom BPSet

/-- Concatenation of runs, with all three coherence laws — inherited from `Src`'s tensorator and
`serialWedgeFunctor`'s, so they are stated with the associator and unitors rather than as
transports along `List.append` identities. -/
instance : RunF.LaxMonoidal := inferInstanceAs
  ((Functor.prod' (discreteOp _ ⋙ Src.op) serialWedgeFunctor ⋙ Functor.hom BPSet).LaxMonoidal)

theorem RunF_obj (X : DimList) : RunF.obj X = (Src.obj X ⟶ serialWedgeFunctor.obj X) := rfl

/-- `μ RunF` splits the source, tensors, and glues the target. -/
theorem RunF_μ (a b : DimList) (f : RunF.obj a) (g : RunF.obj b) :
    Functor.LaxMonoidal.μ RunF a b (f, g)
      = Functor.OplaxMonoidal.δ Src a b ≫ (f ⊗ₘ g)
          ≫ Functor.LaxMonoidal.μ serialWedgeFunctor a b := rfl

end CubeChains
