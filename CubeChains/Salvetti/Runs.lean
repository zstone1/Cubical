import CubeChains.Salvetti.RunMonoidal
import CubeChains.Chains.ChainRestrictions
import CubeChains.Chains.Correspondence

/-!
# Salvetti/Runs — runs with the length existentially quantified, and their restriction

`Run k = Σ n, (runObj n ⟶ ⋁k)` is `RunF k` with the length bundled instead of computed.  The `Σ`
is contractible (`Run.equivHom`), and it is what makes *constructions* transport-free: you pair
whatever length came out with the map and never rewrite the source object.  `RunF` is the same
data with the monoidal structure attached; cross over with `Run.equivRunF`.

`runRestrict` pulls a run back along a wedge map, in three layers:

```
runRestrictFace  : (□a ⟶ □b) → Run [b] → Run [a]    -- cube to cube, via ChainRestrictions
runRestrictWedge : (⋁a ⟶ □b) → Run [b] → Run a      -- recursion on the source list
runRestrict      : (⋁a ⟶ ⋁b) → Run b   → Run a      -- recursion on the target list
```
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet MonoidalCategory

namespace CubeChains

/-- **The length of a run is forced.**  `serialWedge_dimSum_eq`, directly. -/
theorem runObj_hom_dim {n : ℕ} {k : List ℕ+} (x : runObj n ⟶ ⋁k) : n = dimSum k := by
  have h := serialWedge_dimSum_eq x
  simpa [dimSum, List.map_replicate, List.sum_replicate] using h

/-- A **run** of shape `k`: a bi-pointed map into `⋁k` out of *some* all-edges wedge. -/
def Run (k : List ℕ+) : Type := Σ n : ℕ, (runObj n ⟶ ⋁k)

theorem Run.dim {k : List ℕ+} (r : Run k) : r.1 = dimSum k := runObj_hom_dim r.2

/-- The `Σ` is contractible: a run is exactly a map out of `runObj (dimSum k)`. -/
def Run.equivHom (k : List ℕ+) : Run k ≃ (runObj (dimSum k) ⟶ ⋁k) where
  toFun r := eqToHom (congrArg runObj r.dim.symm) ≫ r.2
  invFun f := ⟨dimSum k, f⟩
  left_inv := by rintro ⟨n, x⟩; obtain rfl : n = dimSum k := runObj_hom_dim x; simp
  right_inv := by intro f; simp

/-- …and that hom is `RunF`'s value, so the monoidal structure transfers.  This equivalence is
where the length transport lives; everything on either side of it is transport-free. -/
def Run.equivRunF (k : List ℕ+) : Run k ≃ RunF.obj (Discrete.mk (FreeMonoid.ofList k)) :=
  (Run.equivHom k).trans (Equiv.cast (by rw [RunF_obj, Src_obj]; rfl))

/-! ### All-edges chains and runs are the same thing

`EdgeChain` keeps the length out of the type; `Run` bundles it.  These two convert. -/

/-- A run of `□ⁿ` has exactly `n` edges — a theorem about the subtype, not part of its type. -/
theorem EdgeChain.length {n : ℕ} (r : EdgeChain (cube n)) : r.1.cubes.length = n := by
  have hdims : r.1.dims = List.replicate r.1.cubes.length 1 := dims_eq_replicate _ r.2
  exact runObj_dim_eq
    (eqToHom (congrArg BPSet.serialWedge hdims.symm) ≫ (wedgeOfChain r.1).2)

/-- The chain read off a run is all edges. -/
theorem chainOfWedge_dim_one {K : BPSet} {n : ℕ} (x : runObj n ⟶ K) :
    ∀ c ∈ (chainOfWedge (⟨List.replicate n (1 : ℕ+), x⟩ :
        Σ dims : List ℕ+, (⋁dims ⟶ K))).cubes, (c.1 : ℕ) = 1 := by
  intro c hc
  have hd : (chainOfWedge (⟨List.replicate n (1 : ℕ+), x⟩ :
      Σ dims : List ℕ+, (⋁dims ⟶ K))).cubes.map (·.1) = List.replicate n (1 : ℕ+) :=
    wedgeToCubes_dims _ _
  have hmem : c.1 ∈ List.replicate n (1 : ℕ+) := hd ▸ List.mem_map_of_mem hc
  simpa using congrArg (fun d : ℕ+ => (d : ℕ)) (List.eq_of_mem_replicate hmem)

/-- A one-bead run as an all-edges chain of the cube (`serialWedge1` is the only iso involved). -/
def Run.toEdgeChain {b : ℕ+} (r : Run [b]) : EdgeChain (cube (b : ℕ)) :=
  ⟨chainOfWedge ⟨List.replicate r.1 (1 : ℕ+), r.2 ≫ (serialWedge1 b).hom⟩,
    chainOfWedge_dim_one _⟩

/-- …and back.  The `Σ` in `Run` absorbs the length, so this is the only transport. -/
def EdgeChain.toRun {a : ℕ+} (e : EdgeChain (cube (a : ℕ))) : Run [a] :=
  ⟨e.1.cubes.length,
    eqToHom (congrArg BPSet.serialWedge (dims_eq_replicate _ e.2).symm)
      ≫ (wedgeOfChain e.1).2 ≫ (serialWedge1 a).inv⟩

/-! ### The restriction, in three layers -/

/-- **Cube to cube.**  `(□a).toPsh = yoneda.obj ▫a`, so Yoneda turns the presheaf map back into a
site map, which is what `EdgeChain.restrict` consumes. -/
def runRestrictFace {a b : ℕ+} (f : (cube (a : ℕ)).toPsh ⟶ (cube (b : ℕ)).toPsh) (r : Run [b]) :
    Run [a] :=
  (EdgeChain.restrict (yonedaEquiv f) r.toEdgeChain).toRun

/-- **Wedge to cube.**  Recursion on the source list: restrict each bead, concatenate. -/
def runRestrictWedge : {b : ℕ+} → (a : List ℕ+) → (⋁a ⟶ cube (b : ℕ)) →
    Run [b] → Run a := sorry

/-- **The general restriction.**  Recursion on the target list, splitting the run by Segal. -/
def runRestrict : (b a : List ℕ+) → (f : ⋁a ⟶ ⋁b) → Run b → Run a := sorry

end CubeChains
