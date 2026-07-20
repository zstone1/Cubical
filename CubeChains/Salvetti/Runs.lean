import CubeChains.Foundations.HomMonoidal
import Mathlib.Algebra.Group.TransferInstance
import CubeChains.Chains.ChainRestrictions
import CubeChains.Chains.ChainSkeletal
import CubeChains.Chains.SerialWedgeFunctor
import CubeChains.Chains.Correspondence
import CubeChains.Chains.WedgeSplitHom
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Salvetti/Runs — all-edges chains, their monoidal structure, and their restriction

`OneD : (ℕ,+) ⥤ BPSet` sends `n` to the all-edges wedge `⋁(1ⁿ)`; reindexing it along `dimSum`
gives `RunF k = (runObj (dimSum k) ⟶ ⋁k)`, lax monoidal by inheritance (`Foundations/HomMonoidal`).

`Run k = Σ n, (runObj n ⟶ ⋁k)` is the same data with the length bundled rather than computed.  The
`Σ` is contractible (`Run.equivHom`) and is what keeps *constructions* transport-free.  Its laws
are stated on the total space `Σ k, Run k`, where the shape identity lives in the first component
and so is an honest `Eq` — mathlib's `GradedMonoid` idiom.

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

/-! ### The all-edges wedge as a monoidal functor -/

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

/-- A list that appends to a replicate is a replicate on both sides — how a split run is seen
again to be all edges. -/
theorem replicate_split {α : Type*} {x : α} {n : ℕ} {s t : List α}
    (h : List.replicate n x = s ++ t) :
    s = List.replicate s.length x ∧ t = List.replicate t.length x :=
  ⟨List.eq_replicate_of_mem fun y hy => List.eq_of_mem_replicate (by rw [h]; simp [hy]),
   List.eq_replicate_of_mem fun y hy => List.eq_of_mem_replicate (by rw [h]; simp [hy])⟩

/-- `dimSum` of an all-edges shape is its length. -/
@[simp] theorem dimSum_replicate (n : ℕ) : dimSum (List.replicate n (1 : ℕ+)) = n := by
  simp [dimSum, List.map_replicate, List.sum_replicate]

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

/-! ### Runs of a given shape, as a functor of the shape -/

/-- Total dimension as a monoid hom.  Spelled by hand rather than via `FreeMonoid.lift`, whose
`prodAux` normal form would make `dimSumHom_ofList` propositional; here it is `rfl`, which is what
keeps `Src_obj` — and hence `Run.equivRunF`'s cast — definitional. -/
def dimSumHom : FreeMonoid ℕ+ →* Multiplicative ℕ where
  toFun l := Multiplicative.ofAdd (dimSum (FreeMonoid.toList l))
  map_one' := rfl
  map_mul' a b := by
    simp [dimSum, FreeMonoid.toList_mul, List.map_append, List.sum_append, ofAdd_add]

@[simp] theorem dimSumHom_ofList (k : List ℕ+) :
    dimSumHom (FreeMonoid.ofList k) = Multiplicative.ofAdd (dimSum k) := rfl

/-- The source of a run, indexed by the target shape: `k ↦ runObj (dimSum k)`. -/
def Src : DimList ⥤ BPSet := Discrete.monoidalFunctor dimSumHom ⋙ OneD

instance : Src.Monoidal :=
  inferInstanceAs ((Discrete.monoidalFunctor dimSumHom ⋙ OneD).Monoidal)

@[simp] theorem Src_obj (k : List ℕ+) :
    Src.obj (Discrete.mk (FreeMonoid.ofList k)) = runObj (dimSum k) := rfl

/-- **Runs of a given shape**, as a functor of the shape:
`RunF k = (runObj (dimSum k) ⟶ ⋁k)`. -/
def RunF : DimList ⥤ Type :=
  Functor.prod' (discreteOp _ ⋙ Src.op) serialWedgeFunctor ⋙ Functor.hom BPSet

abbrev Run (k : List ℕ+) : Type := RunF.obj (Discrete.mk (FreeMonoid.ofList k))

/-- Concatenation of runs, with all three coherence laws — inherited from `Src`'s tensorator and
`serialWedgeFunctor`'s, so they are stated with the associator and unitors rather than as
transports along `List.append` identities. -/
instance : RunF.LaxMonoidal := inferInstanceAs
  ((Functor.prod' (discreteOp _ ⋙ Src.op) serialWedgeFunctor ⋙ Functor.hom BPSet).LaxMonoidal)


/-! ### Runs with the length bundled -/

/-- **The length of a run is forced.**  `serialWedge_dimSum_eq`, directly. -/
theorem runObj_hom_dim {n : ℕ} {k : List ℕ+} (x : runObj n ⟶ ⋁k) : n = dimSum k := by
  have h := serialWedge_dimSum_eq x
  simpa [dimSum, List.map_replicate, List.sum_replicate] using h


/-! ### All-edges chains and runs are the same thing -/

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
  ⟨chainOfWedge ⟨List.replicate (dimSum [b]) (1 : ℕ+), r ≫ (serialWedge1 b).hom⟩,
    chainOfWedge_dim_one _⟩

/-- …and back.  The only transport is the one identifying the chain's own length with `dimSum`. -/
def EdgeChain.toRun {a : ℕ+} (e : EdgeChain (cube (a : ℕ))) : Run [a] :=
  eqToHom (congrArg BPSet.serialWedge
      (show List.replicate (dimSum [a]) (1 : ℕ+) = e.1.dims by
        rw [CubeChain.dims, dims_eq_replicate _ e.2, EdgeChain.length e]; simp [dimSum]))
    ≫ (wedgeOfChain e.1).2 ≫ (serialWedge1 a).inv

/-! ### Splitting a run

The Segal split, read at the level of a single run.  `splitWedgeMorphism` breaks the underlying
wedge map; `replicate_split` sees that both halves are again all edges; `serialWedge_dimSum_eq`
pins their lengths.  This is the inverse of `μ RunF` in the only form the recursion needs — no
`IsIso` required. -/

/-- An all-edges shape whose `dimSum` is forced is the replicate of that length. -/
theorem split_dims {s d : List ℕ+} (hrep : s = List.replicate s.length 1)
    (hN : dimSum s = dimSum d) : s = List.replicate (dimSum d) (1 : ℕ+) := by
  rw [hrep] at hN ⊢
  rw [dimSum_replicate] at hN
  rw [hN]

/-- **Split a run at the head bead.**  `⋁(c :: rest)` is `□c ∨ ⋁rest` definitionally, so this is
`splitWedgeMorphism` plus the two length bookkeeping facts. -/
def Run.split {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest)) :
    Run [c] × Run rest := by
  obtain ⟨l, m, heq, -⟩ := ChainCat.splitWedgeMorphism
    (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest))
    (List.replicate (dimSum (c :: rest)) (1 : ℕ+)) r
  obtain ⟨hl, hm⟩ := replicate_split heq
  refine ⟨eqToHom (congrArg BPSet.serialWedge (split_dims (d := [c]) hl ?_).symm)
            ≫ l.map ≫ (serialWedge1 c).inv,
          eqToHom (congrArg BPSet.serialWedge (split_dims (d := rest) hm ?_).symm) ≫ m.map⟩
  · exact serialWedge_dimSum_eq (l.map ≫ (serialWedge1 c).inv)
  · exact serialWedge_dimSum_eq m.map

/-! ### The restriction, in three layers -/

/-- **Cube to cube.**  `(□a).toPsh = yoneda.obj ▫a`, so Yoneda turns the presheaf map back into a
site map, which is what `EdgeChain.restrict` consumes. -/
def runRestrictFace {a b : ℕ+} (f : (cube (a : ℕ)).toPsh ⟶ (cube (b : ℕ)).toPsh) (r : Run [b]) :
    Run [a] :=
  (EdgeChain.restrict (yonedaEquiv f) r.toEdgeChain).toRun

/-- **Wedge to cube.**  Recursion on the source list: restrict each bead along its own face and
concatenate with `μ RunF`.

At *presheaf* level, deliberately.  `X ⟶ X ∨ Y` is not bi-pointed — it moves the final vertex to
the junction — so a `BPSet` recursion would have to carry a re-pointing at every step.  The
restriction never looks at basepoints (it factors through `faceEmb`), and each restricted bead is
init-to-final in its own cube by `restrictVertex_init`/`_final`, so the output is a genuine run
regardless. -/
def runRestrictWedge : {b : ℕ+} → (a : List ℕ+) → ((⋁a).toPsh ⟶ (cube (b : ℕ)).toPsh) →
    Run [b] → Run a
  | _, [], _, _ => Functor.LaxMonoidal.ε RunF PUnit.unit
  | _, c :: rest, f, r =>
      Functor.LaxMonoidal.μ RunF (Discrete.mk (FreeMonoid.ofList [c]))
          (Discrete.mk (FreeMonoid.ofList rest))
        (runRestrictFace ((serialWedge1 c).inv.hom ≫ wedgeInclL [c] rest ≫ f) r,
         runRestrictWedge rest (wedgeInclR [c] rest ≫ f) r)

/-- `dimSum` vanishes only on the empty shape — every bead is positive. -/
theorem eq_nil_of_dimSum_zero : ∀ {a : List ℕ+}, dimSum a = 0 → a = []
  | [], _ => rfl
  | c :: rest, h => by simp [dimSum] at h

/-- **The general restriction.**  Recursion on the target list: `splitWedgeMorphism` cuts the
source shape at the junction, `Run.split` cuts the run there, the head goes through
`runRestrictWedge` and the tail recurses; `μ RunF` glues the two halves back. -/
def runRestrict : (b a : List ℕ+) → (⋁a ⟶ ⋁b) → Run b → Run a
  | [], _, f, r => cast (congrArg Run (eq_nil_of_dimSum_zero (serialWedge_dimSum_eq f)).symm) r
  | c :: rest, a, f, r =>
      let s := ChainCat.splitWedgeMorphism
        (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest)) a f
      cast (congrArg Run s.2.2.1.symm)
        (Functor.LaxMonoidal.μ RunF (Discrete.mk (FreeMonoid.ofList s.1.dims))
            (Discrete.mk (FreeMonoid.ofList s.2.1.dims))
          (runRestrictWedge s.1.dims s.1.map.hom (Run.split r).1,
           runRestrict rest s.2.1.dims s.2.1.map (Run.split r).2))

end CubeChains
