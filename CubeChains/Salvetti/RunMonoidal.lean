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

instance : OneD.LaxMonoidal := inferInstanceAs ((Ones ⋙ serialWedgeFunctor).LaxMonoidal)

def Run (k : List ℕ+) : Type :=
  BPSet.Hom (OneD.obj (Discrete.mk (BPSet.dimSum k))) (⋁ k)

def runConsL (x : Run (a :: b)) : Run [a] := sorry
def runConsR (x : Run (a :: b)) : Run b := sorry

--def runRetractFace {b n : ℕ} (face : (cube n).toPsh ⟶ (cube b).toPsh)
--    (x : run b ⟶ cube b) : run n ⟶ cube n := sorry
--
--def runRetractCube {b : ℕ} : (a : List ℕ+) → (f : (⋁a).toPsh ⟶ (cube b).toPsh) →
--    (x : run b ⟶ cube b) → Run a
--  | [],      _, _ => 𝟙 _
--  | a :: as, f, x => by
--      -- head bead `□↑a` and tail `⋁as` include (as presheaf maps) into `⋁(a :: as)`;
--      -- restrict the run onto the head face, recurse on the tail, concatenate.
--      have l := runRetractFace (Glue.inl (cube ↑a).finalVertex (⋁as).initVertex ≫ f) x
--      have r := runRetractCube as (Glue.inr (cube ↑a).finalVertex (⋁as).initVertex ≫ f) x
--      refine eqToHom (congrArg BPSet.serialWedge ?_) ≫ concatChainMap _ _
--        {dims := _, map := l} {dims := _, map := r}
--      -- ⊢ runDims (dimSum (a :: as)) = runDims ↑a ++ runDims (dimSum as)
--      simp only [dimSum_sum, List.map_cons, List.sum_cons, runDims_replicate,
--        List.replicate_append_replicate]
--
--def runRetract : (b : List ℕ+) → (a : List ℕ+) → (f : ⋁ a ⟶ ⋁ b) → (x : Run b) → Run a
--  | [], a, f, x => by
--      suffices h : a = [] by subst h; exact x
--      apply dimSum0_nil
--      rw [show 0 = dimSum [] from (by simp)]
--      exact serialWedge_dimSum_eq f
--  | b0 :: bs , a, f, x => by
--     simp only [serialWedge] at f
--     simp only [Run_eq] at x
--     have alt : ((□↑b0).wedge2 ⋁bs).AdmitsAltitude :=
--       wedge2_admitsAltitude (cube_admitsAltitude b0) (serialWedge_admitsAltitude bs)
--     let eqv := ChainCat.chSegal (cube ↑b0) (⋁bs) alt
--     let pq := eqv.inverse.obj {dims := a, map := f}
--     let κ := eqv.counitIso.app {dims := a, map := f}      -- the Segal counit: ⋁(pq₁ ++ pq₂) ≅ ⋁a
--     let recursed := runRetract bs pq.2.dims pq.2.map (runConsR x)
--     let cubef := runRetractCube pq.1.dims pq.1.map.hom (runConsL x ≫ (serialWedge1 b0).hom)
--     let foo := concatChainMap _ _ {dims := _, map := cubef} {dims := _, map := recursed}
--     -- glue the two retracts, re-append the halves, transport back along the counit
--     refine eqToHom (congrArg BPSet.serialWedge ?_) ≫ foo
--       ≫ (serialWedgeAppend pq.1.dims pq.2.dims).hom ≫ ChainCat.Hom.φ κ.hom
--     -- ⊢ runDims (dimSum a) = runDims (dimSum pq.1.dims) ++ runDims (dimSum pq.2.dims)
--     simp only [dimSum_sum, runDims_replicate, List.replicate_append_replicate,
--       List.replicate_inj, or_true, and_true]
--     rw [← List.sum_append_nat, ← List.map_append, ← dimSum_sum, ← dimSum_sum]
--     apply serialWedge_dimSum_eq
--     exact ChainCat.Hom.φ κ.inv


end CubeChains
