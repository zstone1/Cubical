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

/-- `𝟙^n` — the all-edges shape of length `n`.  *Notation*, not a definition, so the elaborated
term is still `List.replicate n 1` and mathlib's `List.replicate` lemmas keep firing. -/
notation:max "𝟙^" n:max => List.replicate n (1 : ℕ+)

/-- `⋁≡h` — lift an equality of shapes to the induced map of wedges.  *Notation*, so the term is
still `eqToHom (congrArg …)` and `eqToHom` simp lemmas fire through it. -/
notation:max "⋁≡" h:max => eqToHom (congrArg BPSet.serialWedge h)

/-- `n ↦ 1ⁿ`, the all-edges word; `Multiplicative` so that `⊗` on the source is `ℕ`'s `+`. -/
def onesObj (n : Multiplicative ℕ) : FreeMonoid ℕ+ :=
  FreeMonoid.ofList (𝟙^n.toAdd)

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
      = 𝟙^m := rfl

/-- A list that appends to a replicate is a replicate on both sides — how a split run is seen
again to be all edges. -/
theorem replicate_split {α : Type*} {x : α} {n : ℕ} {s t : List α}
    (h : List.replicate n x = s ++ t) :
    s = List.replicate s.length x ∧ t = List.replicate t.length x :=
  ⟨List.eq_replicate_of_mem fun y hy => List.eq_of_mem_replicate (by rw [h]; simp [hy]),
   List.eq_replicate_of_mem fun y hy => List.eq_of_mem_replicate (by rw [h]; simp [hy])⟩

/-- `dimSum` of an all-edges shape is its length. -/
@[simp] theorem dimSum_replicate (n : ℕ) : dimSum (𝟙^n) = n := by
  simp [dimSum, List.map_replicate, List.sum_replicate]

/-- **A run into `□ⁿ` has exactly `n` edges.**  `□ⁿ` is the one-bead wedge, so
`serialWedge_dimSum_eq` pins the length; no need to argue that a run meets each direction once. -/
theorem runObj_dim_eq {m n : ℕ} (x : runObj m ⟶ cube n) : m = n := by
  have hm : dimSum (𝟙^m) = m := by
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

/-- A **run** of shape `k`.  Spelled as the hom-type directly rather than as `RunF.obj _`: the
unifier meets `Run k =?= Run k'` constantly, and going through `Functor.prod'`/`Functor.hom` makes
it unfold the whole composite instead of doing congruence on `k`.  `RunF.obj ⟨ofList k⟩ = Run k`
holds by `rfl` (that is what `Src_obj` buys), so `RunF`'s monoidal structure still applies. -/
abbrev Run (k : List ℕ+) : Type := runObj (dimSum k) ⟶ ⋁k

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
  have hdims : r.1.dims = 𝟙^r.1.cubes.length := dims_eq_replicate _ r.2
  exact runObj_dim_eq
    (eqToHom (congrArg BPSet.serialWedge hdims.symm) ≫ (wedgeOfChain r.1).2)

/-- The chain read off a run is all edges. -/
theorem chainOfWedge_dim_one {K : BPSet} {n : ℕ} (x : runObj n ⟶ K) :
    ∀ c ∈ (chainOfWedge (⟨𝟙^n, x⟩ :
        Σ dims : List ℕ+, (⋁dims ⟶ K))).cubes, (c.1 : ℕ) = 1 := by
  intro c hc
  have hd : (chainOfWedge (⟨𝟙^n, x⟩ :
      Σ dims : List ℕ+, (⋁dims ⟶ K))).cubes.map (·.1) = 𝟙^n :=
    wedgeToCubes_dims _ _
  have hmem : c.1 ∈ 𝟙^n := hd ▸ List.mem_map_of_mem hc
  simpa using congrArg (fun d : ℕ+ => (d : ℕ)) (List.eq_of_mem_replicate hmem)

/-- A one-bead run as an all-edges chain of the cube (`serialWedge1` is the only iso involved). -/
def Run.toEdgeChain {b : ℕ+} (r : Run [b]) : EdgeChain (cube (b : ℕ)) :=
  ⟨chainOfWedge ⟨𝟙^(dimSum [b]), r ≫ (serialWedge1 b).hom⟩,
    chainOfWedge_dim_one _⟩

/-- …and back.  The only transport is the one identifying the chain's own length with `dimSum`. -/
def EdgeChain.toRun {a : ℕ+} (e : EdgeChain (cube (a : ℕ))) : Run [a] :=
  eqToHom (congrArg BPSet.serialWedge
      (show 𝟙^(dimSum [a]) = e.1.dims by
        rw [CubeChain.dims, dims_eq_replicate _ e.2, EdgeChain.length e]; simp [dimSum]))
    ≫ (wedgeOfChain e.1).2 ≫ (serialWedge1 a).inv

/-! ### Splitting a run

The Segal split, read at the level of a single run.  `splitWedgeMorphism` breaks the underlying
wedge map; `replicate_split` sees that both halves are again all edges; `serialWedge_dimSum_eq`
pins their lengths.  This is the inverse of `μ RunF` in the only form the recursion needs — no
`IsIso` required. -/

/-- An all-edges shape whose `dimSum` is forced is the replicate of that length. -/
theorem split_dims {s d : List ℕ+} (hrep : s = 𝟙^s.length)
    (hN : dimSum s = dimSum d) : s = 𝟙^(dimSum d) := by
  rw [hrep] at hN ⊢
  rw [dimSum_replicate] at hN
  rw [hN]

/-- **Split a run at the head bead.**  `⋁(c :: rest)` is `□c ∨ ⋁rest` definitionally, so this is
`splitWedgeMorphism` plus the two length bookkeeping facts. -/
def Run.split {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest)) :
    Run [c] × Run rest := by
  obtain ⟨l, m, heq, -⟩ := ChainCat.splitWedgeMorphism
    (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest))
    (𝟙^(dimSum (c :: rest))) r
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

/-! ### `Lines` — runs as a presheaf on chains

A chain `a` has a set of runs refining it, and a chain map pulls runs back.  That is exactly a
presheaf `(Ch K)ᵒᵖ ⥤ Type`, with `runRestrict` as the restriction map — the variance is already
right, since `f : a ⟶ b` carries `f.φ : ⋁a.dims ⟶ ⋁b.dims`. -/

/-- `RunF`'s value at a list shape *is* `Run`; the two presentations never diverge. -/
theorem RunF_obj_run (k : List ℕ+) :
    RunF.obj (Discrete.mk (FreeMonoid.ofList k)) = Run k := rfl

/-- Concatenation of runs.  Not a new operation — this is `μ RunF`, named only so the statements
below don't repeat `Discrete.mk (FreeMonoid.ofList _)` four times each.  Its laws come from
`RunF.LaxMonoidal`, not from anything proved here. -/
def runAppend {b₁ b₂ : List ℕ+} (s₁ : Run b₁) (s₂ : Run b₂) : Run (b₁ ++ b₂) :=
  Functor.LaxMonoidal.μ RunF (Discrete.mk (FreeMonoid.ofList b₁))
    (Discrete.mk (FreeMonoid.ofList b₂)) (s₁, s₂)

/-- The tensor of two wedge maps, read on concatenated shapes. -/
def wedgeTensor {a₁ a₂ b₁ b₂ : List ℕ+} (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂) :
    ⋁(a₁ ++ a₂) ⟶ ⋁(b₁ ++ b₂) :=
  (serialWedgeAppend a₁ a₂).inv ≫ (f₁ ⊗ₘ f₂) ≫ serialWedgeAppendHom b₁ b₂

@[simp] theorem dimSum_append (a b : List ℕ+) : dimSum (a ++ b) = dimSum a + dimSum b := by
  simp [dimSum, List.map_append, List.sum_append]

/-- The all-edges shape of a concatenation splits — the source-side counterpart of
`serialWedgeAppend`. -/
theorem replicate_dimSum_append (b₁ b₂ : List ℕ+) :
    𝟙^(dimSum (b₁ ++ b₂))
      = 𝟙^(dimSum b₁) ++ 𝟙^(dimSum b₂) := by
  rw [dimSum_append, List.replicate_add]

/-- `μ RunF` splits the source, tensors, and glues the target. -/
theorem RunF_μ (a b : DimList) (f : RunF.obj a) (g : RunF.obj b) :
    Functor.LaxMonoidal.μ RunF a b (f, g)
      = Functor.OplaxMonoidal.δ Src a b ≫ (f ⊗ₘ g)
          ≫ Functor.LaxMonoidal.μ serialWedgeFunctor a b := rfl

/-- `DimList` is thin, so `serialWedgeFunctor` sends every structure map to the `eqToHom` of the
underlying shape identity.  This is what collapses the discrete factors of `δ Src`. -/
theorem serialWedgeFunctor_map_eqToHom {X Y : DimList} (g : X ⟶ Y) :
    serialWedgeFunctor.map g
      = eqToHom (congrArg serialWedgeFunctor.obj (Discrete.ext (Discrete.eq_of_hom g))) := by
  obtain rfl : X = Y := Discrete.ext (Discrete.eq_of_hom g)
  rw [Subsingleton.elim g (𝟙 X)]
  simp

/-- The counterpart of `serialWedgeFunctor_μ` for the cotensorator. -/
@[simp] theorem serialWedgeFunctor_δ (X Y : DimList) :
    Functor.OplaxMonoidal.δ serialWedgeFunctor X Y
      = (serialWedgeAppend X.as Y.as).inv := rfl

/-- `Src`'s cotensorator is the wedge-append iso, up to the shape identity.  `Src` is
`Discrete.monoidalFunctor dimSumHom ⋙ Ones ⋙ serialWedgeFunctor`, and only the last factor
contributes anything: the two discrete factors are `eqToHom`s. -/
theorem delta_Src (b₁ b₂ : List ℕ+) :
    Functor.OplaxMonoidal.δ Src (Discrete.mk (FreeMonoid.ofList b₁))
        (Discrete.mk (FreeMonoid.ofList b₂))
      = ⋁≡(replicate_dimSum_append b₁ b₂)
          ≫ (serialWedgeAppend (𝟙^(dimSum b₁)) (𝟙^(dimSum b₂))).inv := by
  show Functor.OplaxMonoidal.δ (Discrete.monoidalFunctor dimSumHom ⋙ OneD) _ _ = _
  show Functor.OplaxMonoidal.δ
      (Discrete.monoidalFunctor dimSumHom ⋙ Ones ⋙ serialWedgeFunctor) _ _ = _
  simp [Functor.OplaxMonoidal.comp_δ, serialWedgeFunctor_map_eqToHom]
  rfl

/-- **The crux comparison.**  `runAppend` (built from `μ RunF`, i.e. `δ Src ≫ (· ⊗ₘ ·) ≫ μ swF`)
and `concatChainMap` (built as `(serialWedgeAppend).inv ≫ (· ⊗ₘ ·)`) are the same tensor sandwiched
between the same iso with opposite variance.  Everything about splitting runs reduces to this. -/
theorem runAppend_eq_concatChainMap {b₁ b₂ : List ℕ+} (s₁ : Run b₁) (s₂ : Run b₂) :
    runAppend s₁ s₂
      = eqToHom (congrArg BPSet.serialWedge
            (replicate_dimSum_append b₁ b₂))
          ≫ concatChainMap (⋁b₁) (⋁b₂)
              ⟨𝟙^(dimSum b₁), s₁⟩ ⟨𝟙^(dimSum b₂), s₂⟩
          ≫ serialWedgeAppendHom b₁ b₂ := by
  simp only [runAppend, concatChainMap, RunF_μ, serialWedgeFunctor_μ, delta_Src, Category.assoc]
  rfl

/-! ### The Segal round trips -/

/-- `And.casesOn` at a constant motive: theorems are never delta-unfolded, so an `obtain` on a
`theorem`-valued conjunction inside a `def` has to be reduced propositionally. -/
theorem and_casesOn_const {A B : Prop} {α : Sort*} (h : A ∧ B) (f : A → B → α) :
    (And.casesOn h f : α) = f h.1 h.2 := by cases h; rfl

/-- The altitude witness for `⋁(c :: rest) = □c ∨ ⋁rest`, spelled once. -/
def consAltitude (c : ℕ+) (rest : List ℕ+) : (wedge2 (□(c : ℕ)) (⋁rest)).AdmitsAltitude :=
  wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest)

/-- The head chain-object of a split run. -/
abbrev splitHead {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest)) : Ch (□(c : ℕ)) :=
  (splitObj (consAltitude c rest)
    (⟨𝟙^(dimSum (c :: rest)), r⟩ : Ch (wedge2 (□(c : ℕ)) (⋁rest)))).1

/-- The tail chain-object of a split run. -/
abbrev splitTail {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest)) : Ch (⋁rest) :=
  (splitObj (consAltitude c rest)
    (⟨𝟙^(dimSum (c :: rest)), r⟩ : Ch (wedge2 (□(c : ℕ)) (⋁rest)))).2

/-- `Run.split` with its two reindexings named; the proofs are irrelevant, so any pair does. -/
theorem Run.split_eq {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest))
    (p₁ : 𝟙^(dimSum [c]) = (splitHead r).dims) (p₂ : 𝟙^(dimSum rest) = (splitTail r).dims) :
    Run.split r
      = (⋁≡p₁ ≫ (splitHead r).map ≫ (serialWedge1 c).inv, ⋁≡p₂ ≫ (splitTail r).map) := by
  conv_lhs => rw [Run.split]; simp only [and_casesOn_const]
  rfl

/-- `⋁[c] ≅ □c` is the right unitor, so a one-bead append iso is that unitor whiskered — the
triangle identity, in the wedge monoidal structure. -/
theorem serialWedgeAppendHom_singleton (c : ℕ+) (rest : List ℕ+) :
    serialWedgeAppendHom [c] rest = (serialWedge1 c).hom ▷ (⋁rest) := by
  rw [serialWedgeAppendHom_cons', serialWedgeAppendHom_nil']
  exact MonoidalCategory.triangle _ _

/-- The all-edges shape of `c :: rest`, split at the head bead. -/
theorem replicate_dimSum_cons (c : ℕ+) (rest : List ℕ+) :
    𝟙^(dimSum (c :: rest)) = 𝟙^(dimSum [c]) ++ 𝟙^(dimSum rest) :=
  replicate_dimSum_append [c] rest

/-- `runAppend` at a one-bead head, read as a `concatChainMap` into `□c ∨ ⋁rest` — the form
`splitObj` consumes. -/
theorem runAppend_cons {c : ℕ+} {rest : List ℕ+} (s₁ : Run [c]) (s₂ : Run rest) :
    (runAppend s₁ s₂ : Run (c :: rest))
      = ⋁≡(replicate_dimSum_cons c rest)
          ≫ concatChainMap (□(c : ℕ)) (⋁rest)
              ⟨𝟙^(dimSum [c]), s₁ ≫ (serialWedge1 c).hom⟩ ⟨𝟙^(dimSum rest), s₂⟩ := by
  rw [runAppend_eq_concatChainMap]
  congr 1
  rw [serialWedgeAppendHom_singleton, concatChainMap, concatChainMap, Category.assoc]
  congr 1
  show (s₁ ⊗ₘ s₂) ≫ ((serialWedge1 c).hom ▷ (⋁rest)) = (s₁ ≫ (serialWedge1 c).hom) ⊗ₘ s₂
  rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id]

/-- Transport of `concatChainMap` along equalities of the two chain-objects. -/
theorem concatChainMap_congr {X Y : BPSet} {d₁ d₂ : List ℕ+} {mA : ⋁d₁ ⟶ X} {mB : ⋁d₂ ⟶ Y}
    {a : Ch X} {b : Ch Y} (hA : (⟨d₁, mA⟩ : Ch X) = a) (hB : (⟨d₂, mB⟩ : Ch Y) = b)
    (q : d₁ ++ d₂ = a.dims ++ b.dims) :
    concatChainMap X Y ⟨d₁, mA⟩ ⟨d₂, mB⟩ = ⋁≡q ≫ concatChainMap X Y a b := by
  subst hA; subst hB
  have hid : (⋁≡q) = 𝟙 (⋁(d₁ ++ d₂)) := eqToHom_refl _ _
  rw [hid, Category.id_comp]

set_option maxHeartbeats 400000 in
-- the round trip forces `splitObj` and `chConcat` open on both sides of a `concatChainMap`
/-- Appending after splitting is the identity: `splitObj` is a section of `chConcat`. -/
theorem split_runAppend {c : ℕ+} {rest : List ℕ+} (s₁ : Run [c]) (s₂ : Run rest) :
    Run.split (show Run (c :: rest) from runAppend s₁ s₂) = (s₁, s₂) := by
  have hobj : (⟨𝟙^(dimSum (c :: rest)), (runAppend s₁ s₂ : Run (c :: rest))⟩ :
      Ch (wedge2 (□(c : ℕ)) (⋁rest)))
      = (chConcat (□(c : ℕ)) (⋁rest)).obj
          (⟨𝟙^(dimSum [c]), s₁ ≫ (serialWedge1 c).hom⟩, ⟨𝟙^(dimSum rest), s₂⟩) :=
    Obj.mk_eq_mk (replicate_dimSum_cons c rest) (runAppend_cons s₁ s₂)
  have hs := congrArg (splitObj (consAltitude c rest)) hobj
  rw [splitObj_chConcat_obj] at hs
  obtain ⟨e₁, hm₁⟩ := Obj.eq_mk_iff (congrArg Prod.fst hs)
  obtain ⟨e₂, hm₂⟩ := Obj.eq_mk_iff (congrArg Prod.snd hs)
  rw [Run.split_eq _ e₁.symm e₂.symm, hm₁, hm₂]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

set_option maxHeartbeats 400000 in
-- the round trip forces `splitObj` and `chConcat` open on both sides of a `concatChainMap`
/-- Splitting after appending is the identity: `splitObj` is a retraction of `chConcat`. -/
theorem runAppend_split {c : ℕ+} {rest : List ℕ+} (r : Run (c :: rest)) :
    runAppend (Run.split r).1 (Run.split r).2 = r := by
  revert r
  -- Spell the run's codomain as `□c ∨ ⋁rest` rather than `⋁(c :: rest)`: the two are `rfl`, but
  -- `eqToHom_trans_assoc` matches syntactically and every other composite here uses `wedge2`.
  suffices h : ∀ r : ⋁(𝟙^(dimSum (c :: rest))) ⟶ wedge2 (□(c : ℕ)) (⋁rest),
      (show Run (c :: rest) from runAppend (Run.split r).1 (Run.split r).2) = r from h
  intro r
  obtain ⟨hd, hmap⟩ := Obj.eq_mk_iff (chConcat_obj_splitObj (consAltitude c rest)
    (⟨𝟙^(dimSum (c :: rest)), r⟩ : Ch (wedge2 (□(c : ℕ)) (⋁rest))))
  obtain ⟨hl, hm⟩ := replicate_split hd.symm
  have e₁ : (splitHead r).dims = 𝟙^(dimSum [c]) :=
    split_dims hl (serialWedge_dimSum_eq ((splitHead r).map ≫ (serialWedge1 c).inv))
  have e₂ : (splitTail r).dims = 𝟙^(dimSum rest) :=
    split_dims hm (serialWedge_dimSum_eq (splitTail r).map)
  have hA : (⟨𝟙^(dimSum [c]),
      (⋁≡e₁.symm ≫ (splitHead r).map ≫ (serialWedge1 c).inv) ≫ (serialWedge1 c).hom⟩ :
      Ch (□(c : ℕ))) = splitHead r := by
    refine Obj.mk_eq_mk (d' := (splitHead r).dims) (m' := (splitHead r).map) e₁.symm ?_
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hB : (⟨𝟙^(dimSum rest), ⋁≡e₂.symm ≫ (splitTail r).map⟩ : Ch (⋁rest)) = splitTail r :=
    Obj.mk_eq_mk (d' := (splitTail r).dims) (m' := (splitTail r).map) e₂.symm rfl
  have hmap' : concatChainMap (□(c : ℕ)) (⋁rest) (splitHead r) (splitTail r)
      = ⋁≡(show (splitHead r).dims ++ (splitTail r).dims = 𝟙^(dimSum (c :: rest)) from hd)
        ≫ r := hmap
  rw [Run.split_eq r e₁.symm e₂.symm, runAppend_cons,
    concatChainMap_congr hA hB
      (show 𝟙^(dimSum [c]) ++ 𝟙^(dimSum rest) = (splitHead r).dims ++ (splitTail r).dims by
        rw [e₁, e₂]),
    hmap']
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Segal for runs.**  A run of `⋁(c :: rest)` *is* a run of the head bead together with a run
of the tail — `Run.split` and `runAppend` are mutually inverse.  This is what licenses reasoning
about runs bead-locally, and hence the whole propagation principle below. -/
def Run.splitEquiv (c : ℕ+) (rest : List ℕ+) : Run (c :: rest) ≃ Run [c] × Run rest where
  toFun := Run.split
  invFun s := show Run (c :: rest) from runAppend s.1 s.2
  left_inv := runAppend_split
  right_inv := by rintro ⟨s₁, s₂⟩; exact split_runAppend s₁ s₂

/-! ### The empty shape, and transport of runs -/

/-- `▫0` has a single endomorphism. -/
instance : Subsingleton (▫0 ⟶ ▫0) := by
  constructor
  intro f g
  apply Box.hom_ext
  apply Subtype.ext
  exact funext (fun i => absurd i.2 (Nat.not_lt_zero _))

/-- `⋁[]` is the point, so it carries exactly one run. -/
instance runNilSubsingleton : Subsingleton (Run ([] : List ℕ+)) := by
  constructor
  intro s t
  apply BPSet.hom_ext
  apply yonedaEquiv.injective
  exact Subsingleton.elim (α := (▫0 ⟶ ▫0)) _ _

/-- `⋁[]` is the monoidal unit, and it is rigid. -/
theorem wedge_nil_hom_id (f : ⋁([] : List ℕ+) ⟶ ⋁([] : List ℕ+)) : f = 𝟙 _ :=
  Subsingleton.elim (α := Run ([] : List ℕ+)) _ _

/-- Left unit for `runAppend`.  `𝟙_ DimList ⊗ X = X` on the nose (`[] ++ l = l` is `rfl` in
`FreeMonoid`), so `RunF`'s left unitor is the identity and `left_unitality` reads directly. -/
theorem runAppend_nil_left {b : List ℕ+} (t : Run ([] : List ℕ+)) (u : Run b) :
    runAppend t u = u := by
  have ht : t = Functor.LaxMonoidal.ε RunF PUnit.unit := Subsingleton.elim _ _
  subst ht
  have h := congrArg (fun f => f (PUnit.unit, u))
    (Functor.LaxMonoidal.left_unitality (F := RunF) (Discrete.mk (FreeMonoid.ofList b)))
  simp only [types_comp_apply] at h
  exact h.symm

/-- Transport a run along an equality of shapes.  Spelled as `cast` so that it is *definitionally*
the identity whenever the two shapes are already defeq (`[c] ++ []` vs `[c]`). -/
def runMap {a b : List ℕ+} (h : a = b) (r : Run a) : Run b := cast (congrArg Run h) r

/-- `RunF`'s action on the (unique) structure map of a shape identity *is* the transport. -/
theorem RunF_map_apply {a b : List ℕ+} (h : a = b)
    (g : (Discrete.mk (FreeMonoid.ofList a) : DimList) ⟶ Discrete.mk (FreeMonoid.ofList b))
    (r : Run a) : (RunF.map g) r = runMap h r := by
  subst h
  rw [Subsingleton.elim g (𝟙 _), RunF.map_id]
  rfl

/-- Right unit for `runAppend`, with the `b ++ []` transport made explicit. -/
theorem runAppend_nil_right {b : List ℕ+} (x : Run b) (y : Run ([] : List ℕ+)) :
    runMap (List.append_nil b) (runAppend x y) = x := by
  have hy : y = Functor.LaxMonoidal.ε RunF PUnit.unit := Subsingleton.elim _ _
  subst hy
  have h := congrArg (fun f => f (x, PUnit.unit))
    (Functor.LaxMonoidal.right_unitality (F := RunF) (Discrete.mk (FreeMonoid.ofList b)))
  simp only [types_comp_apply] at h
  have h2 : ∀ z : RunF.obj (Discrete.mk (FreeMonoid.ofList b) ⊗ 𝟙_ DimList),
      (RunF.map (ρ_ (Discrete.mk (FreeMonoid.ofList b))).hom) z
        = runMap (List.append_nil b) z := fun z => RunF_map_apply _ _ _
  rw [h2] at h
  exact h.symm

/-- **Associativity of `runAppend`**, with the (unavoidable) transport along `List.append_assoc`;
`RunF`'s `associativity`, read on elements. -/
theorem runAppend_assoc {p q r : List ℕ+} (x : Run p) (y : Run q) (z : Run r) :
    runAppend (runAppend x y) z
      = runMap (List.append_assoc p q r).symm (runAppend x (runAppend y z)) := by
  have h := Functor.LaxMonoidal.associativity RunF
    (Discrete.mk (FreeMonoid.ofList p)) (Discrete.mk (FreeMonoid.ofList q))
    (Discrete.mk (FreeMonoid.ofList r))
  have key : RunF.map (α_ (Discrete.mk (FreeMonoid.ofList p)) (Discrete.mk (FreeMonoid.ofList q))
      (Discrete.mk (FreeMonoid.ofList r))).hom (runAppend (runAppend x y) z)
      = runAppend x (runAppend y z) := congrArg (fun f => f ((x, y), z)) h
  have hcast : RunF.map (α_ (Discrete.mk (FreeMonoid.ofList p))
        (Discrete.mk (FreeMonoid.ofList q)) (Discrete.mk (FreeMonoid.ofList r))).hom
        (runAppend (runAppend x y) z)
      = runMap (List.append_assoc p q r) (runAppend (runAppend x y) z) :=
    RunF_map_apply (List.append_assoc p q r) _ _
  rw [hcast] at key
  rw [← key]
  simp [runMap]

/-- Associativity at a one-bead head: `([c] ++ rest) ++ b₂` and `[c] ++ (rest ++ b₂)` are `rfl`, so
the transport disappears — the spelling `rw [← ·]` needs. -/
theorem runAppend_assoc_cons {c : ℕ+} {rest b₂ : List ℕ+}
    (x : Run [c]) (y : Run rest) (z : Run b₂) :
    runAppend (runAppend x y) z = runAppend x (runAppend y z) :=
  runAppend_assoc x y z

/-- `runAppend_assoc_cons` with the outer shape spelled `c :: rest` — the form `rw` needs when the
outer factor came from `runRestrictWedge`. -/
theorem runAppend_assoc_cons' {c : ℕ+} {rest b₂ : List ℕ+}
    (x : Run [c]) (y : Run rest) (z : Run b₂) :
    runAppend (b₁ := c :: rest) (b₂ := b₂) (runAppend x y) z = runAppend x (runAppend y z) :=
  runAppend_assoc_cons x y z

/-- Splitting an append at the head bead peels the head of the *first* factor. -/
theorem split_runAppend_cons {c : ℕ+} {rest b₂ : List ℕ+}
    (s₁ : Run (c :: rest)) (s₂ : Run b₂) :
    Run.split (runAppend s₁ s₂) = ((Run.split s₁).1, runAppend (Run.split s₁).2 s₂) := by
  have key : runAppend s₁ s₂
      = runAppend (Run.split s₁).1 (runAppend (Run.split s₁).2 s₂) := by
    rw [← runAppend_assoc_cons, runAppend_split]
    rfl
  rw [key]
  exact split_runAppend _ _

/-! ### `wedgeTensor` as a bifunctor -/

/-- `serialWedgeAppend`'s hom/inv cancellation.  Stated with `wedge2` rather than `⊗`: `rw`'s
keyed matching sees the two spellings of the object as distinct, and it is the `wedge2` one that
sits in the middle of a `wedgeTensor` composite. -/
theorem serialWedgeAppendHom_inv (x y : List ℕ+) :
    serialWedgeAppendHom x y ≫ (serialWedgeAppend x y).inv = 𝟙 (wedge2 (⋁x) (⋁y)) :=
  (serialWedgeAppend x y).hom_inv_id

theorem wedgeTensor_id (a₁ a₂ : List ℕ+) :
    wedgeTensor (𝟙 (⋁a₁)) (𝟙 (⋁a₂)) = 𝟙 (⋁(a₁ ++ a₂)) := by
  have h : (𝟙 (⋁a₁) ⊗ₘ 𝟙 (⋁a₂)) = 𝟙 (wedge2 (⋁a₁) (⋁a₂)) :=
    MonoidalCategory.id_tensorHom_id _ _
  rw [wedgeTensor, serialWedgeAppendHom, h, Category.id_comp, Iso.inv_hom_id]

theorem wedgeTensor_comp {a₁ a₂ b₁ b₂ c₁ c₂ : List ℕ+}
    (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂) (g₁ : ⋁b₁ ⟶ ⋁c₁) (g₂ : ⋁b₂ ⟶ ⋁c₂) :
    wedgeTensor f₁ f₂ ≫ wedgeTensor g₁ g₂ = wedgeTensor (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  rw [wedgeTensor, wedgeTensor, wedgeTensor, Category.assoc, Category.assoc,
    ← Category.assoc (serialWedgeAppendHom b₁ b₂), serialWedgeAppendHom_inv,
    Category.id_comp, ← Category.assoc (f₁ ⊗ₘ f₂),
    MonoidalCategory.tensorHom_comp_tensorHom]

/-- Tensoring with the empty shape on the left is the identity: `serialWedgeAppendHom [] y` is the
left unitor (`rfl`), so this is unitor naturality. -/
theorem wedgeTensor_nil_left {a₂ b₂ : List ℕ+}
    (f₁ : ⋁([] : List ℕ+) ⟶ ⋁([] : List ℕ+)) (f₂ : ⋁a₂ ⟶ ⋁b₂) :
    wedgeTensor f₁ f₂ = f₂ := by
  rw [wedge_nil_hom_id f₁]
  show (serialWedgeAppend [] a₂).inv ≫ (𝟙 _ ⊗ₘ f₂) ≫ serialWedgeAppendHom [] b₂ = f₂
  rw [show serialWedgeAppendHom ([] : List ℕ+) b₂ = (λ_ (⋁b₂)).hom from rfl,
      show (serialWedgeAppend ([] : List ℕ+) a₂).inv = (λ_ (⋁a₂)).inv from rfl]
  rw [id_tensorHom]
  show (λ_ (⋁a₂)).inv ≫ (𝟙_ BPSet ◁ f₂) ≫ (λ_ (⋁b₂)).hom = f₂
  rw [MonoidalCategory.leftUnitor_naturality]
  simp

/-- `wedgeTensor` distributes over a `concatChainMap` on the left factor: tensoring with `f₂`
turns the split `(l, m)` of `f₁` into the split `(l, m ⊗ f₂)`.  Pure coherence — the content is
`serialWedgeAppendIso_assoc`. -/
theorem wedgeTensor_concatChainMap {c : ℕ+} {rest₁ a₂ b₂ : List ℕ+}
    (l : Ch (□(c : ℕ))) (m : Ch (⋁rest₁)) (f₂ : ⋁a₂ ⟶ ⋁b₂) :
    wedgeTensor (a₁ := l.dims ++ m.dims) (b₁ := c :: rest₁)
        (concatChainMap (□(c : ℕ)) (⋁rest₁) l m) f₂
      = eqToHom (congrArg BPSet.serialWedge (List.append_assoc l.dims m.dims a₂))
          ≫ concatChainMap (□(c : ℕ)) (⋁(rest₁ ++ b₂)) l
              ⟨m.dims ++ a₂, wedgeTensor m.map f₂⟩ := by
  simp only [wedgeTensor, concatChainMap,
    show serialWedgeAppendHom (c :: rest₁) b₂
        = (α_ (□(c:ℕ)) (⋁rest₁) (⋁b₂)).hom ≫ (□(c:ℕ)) ◁ serialWedgeAppendHom rest₁ b₂ from rfl]
  have key : ((serialWedgeAppend l.dims m.dims).hom ▷ (⋁a₂))
        ≫ (serialWedgeAppend (l.dims ++ m.dims) a₂).hom
        ≫ eqToHom (congrArg BPSet.serialWedge (List.append_assoc l.dims m.dims a₂))
      = (α_ (⋁l.dims) (⋁m.dims) (⋁a₂)).hom
        ≫ ((⋁l.dims) ◁ (serialWedgeAppend m.dims a₂).hom)
        ≫ (serialWedgeAppend l.dims (m.dims ++ a₂)).hom :=
    ChainCat.serialWedgeAppendIso_assoc l.dims m.dims a₂
  have hE : eqToHom (congrArg BPSet.serialWedge (List.append_assoc l.dims m.dims a₂))
        ≫ (serialWedgeAppend l.dims (m.dims ++ a₂)).inv
      = (serialWedgeAppend (l.dims ++ m.dims) a₂).inv
          ≫ ((serialWedgeAppend l.dims m.dims).inv ▷ (⋁a₂))
          ≫ (α_ (⋁l.dims) (⋁m.dims) (⋁a₂)).hom
          ≫ ((⋁l.dims) ◁ (serialWedgeAppend m.dims a₂).hom) := by
    rw [Iso.comp_inv_eq]
    simp only [Category.assoc]
    rw [← key]
    simp
  rw [reassoc_of% hE]
  refine (cancel_epi ((serialWedgeAppend (l.dims ++ m.dims) a₂).inv)).mpr ?_
  exact tensor_reassoc_aux _ l.map m.map f₂ (serialWedgeAppend m.dims a₂) _

/-! ### Evaluating `runRestrict` at a known split -/

/-- **Uniqueness of the wedge split.**  `splitObj` is a two-sided inverse to `chConcat`, so any
presentation of `f` as a `concatChainMap` *is* the one `splitWedgeMorphism` finds. -/
theorem splitWedgeMorphism_eq {X Y : BPSet} (h : (wedge2 X Y).AdmitsAltitude) (as : List ℕ+)
    (l : Ch X) (m : Ch Y) (heq : as = l.dims ++ m.dims)
    (f : ⋁as ⟶ wedge2 X Y)
    (hf : f = eqToHom (congrArg BPSet.serialWedge heq) ≫ concatChainMap X Y l m) :
    (splitWedgeMorphism h as f).1 = l ∧ (splitWedgeMorphism h as f).2.1 = m := by
  subst heq
  have hobj : (⟨l.dims ++ m.dims, f⟩ : Ch (wedge2 X Y)) = (chConcat X Y).obj (l, m) := by
    refine ChainCat.Obj.mk_eq_mk rfl ?_
    simpa using hf
  have hsp := splitObj_chConcat_obj h l m
  rw [← hobj] at hsp
  exact ⟨congrArg Prod.fst hsp, congrArg Prod.snd hsp⟩

/-- Equation lemma for `runRestrict` at a cons target — the shape the induction consumes. -/
theorem runRestrict_cons {c : ℕ+} {rest a : List ℕ+}
    (f : ⋁a ⟶ ⋁(c :: rest)) (r : Run (c :: rest)) :
    runRestrict (c :: rest) a f r =
      (let s := ChainCat.splitWedgeMorphism
        (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest)) a f
      cast (congrArg Run s.2.2.1.symm)
        (runAppend (runRestrictWedge s.1.dims s.1.map.hom (Run.split r).1)
           (runRestrict rest s.2.1.dims s.2.1.map (Run.split r).2))) := rfl

/-- Equation lemma for `runRestrict` at the empty target. -/
theorem runRestrict_nil {a : List ℕ+} (f : ⋁a ⟶ ⋁([] : List ℕ+)) (r : Run ([] : List ℕ+)) :
    runRestrict [] a f r
      = cast (congrArg Run (eq_nil_of_dimSum_zero (serialWedge_dimSum_eq f)).symm) r := rfl

/-- **`runRestrict` at a cons target, read off *any* presentation of `f` as a `concatChainMap`.**
Uniqueness of the split means the recursion does not care which presentation you hand it. -/
theorem runRestrict_cons_of_split {c : ℕ+} {rest a : List ℕ+}
    (f : ⋁a ⟶ ⋁(c :: rest)) (l : Ch (□(c : ℕ))) (m : Ch (⋁rest))
    (heq : a = l.dims ++ m.dims)
    (hf : f = eqToHom (congrArg BPSet.serialWedge heq) ≫ concatChainMap (□(c : ℕ)) (⋁rest) l m)
    (r : Run (c :: rest)) :
    runRestrict (c :: rest) a f r
      = runMap heq.symm (runAppend (runRestrictWedge l.dims l.map.hom (Run.split r).1)
          (runRestrict rest m.dims m.map (Run.split r).2)) := by
  obtain ⟨h1, h2⟩ := splitWedgeMorphism_eq
    (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest))
    a l m heq f hf
  rw [runRestrict_cons]
  subst h1
  subst h2
  rfl

/-- The transport-free reading, when the source shape is already presented as the append. -/
theorem runRestrict_cons_of_split_rfl {c : ℕ+} {rest : List ℕ+}
    (l : Ch (□(c : ℕ))) (m : Ch (⋁rest))
    (f : ⋁(l.dims ++ m.dims) ⟶ ⋁(c :: rest)) (r : Run (c :: rest))
    (hf : f = concatChainMap (□(c : ℕ)) (⋁rest) l m) :
    runRestrict (c :: rest) (l.dims ++ m.dims) f r
      = runAppend (runRestrictWedge l.dims l.map.hom (Run.split r).1)
          (runRestrict rest m.dims m.map (Run.split r).2) := by
  rw [runRestrict_cons_of_split f l m rfl (by simpa using hf) r]
  rfl

/-- **Base case of tensoriality**: an empty left target forces an empty left source, and both
sides collapse by the left unit laws. -/
theorem runRestrict_tensor_nil {a₁ a₂ b₂ : List ℕ+}
    (f₁ : ⋁a₁ ⟶ ⋁([] : List ℕ+)) (f₂ : ⋁a₂ ⟶ ⋁b₂)
    (s₁ : Run ([] : List ℕ+)) (s₂ : Run b₂) :
    runRestrict ([] ++ b₂) (a₁ ++ a₂) (wedgeTensor f₁ f₂) (runAppend s₁ s₂)
      = runAppend (runRestrict [] a₁ f₁ s₁) (runRestrict b₂ a₂ f₂ s₂) := by
  obtain rfl : a₁ = [] := eq_nil_of_dimSum_zero (serialWedge_dimSum_eq f₁)
  rw [runAppend_nil_left (runRestrict [] [] f₁ s₁), runAppend_nil_left s₁,
    wedgeTensor_nil_left]
  rfl

/-- **`runRestrict` is monoidal** — the general result.  Restriction commutes with concatenation,
so any statement that holds on one-bead targets and is preserved by `runAppend` propagates to
every wedge map.  `runRestrict_id` and `runRestrict_comp` are the first two consumers. -/
theorem runRestrict_tensor {a₁ a₂ b₁ b₂ : List ℕ+}
    (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂) (s₁ : Run b₁) (s₂ : Run b₂) :
    runRestrict (b₁ ++ b₂) (a₁ ++ a₂) (wedgeTensor f₁ f₂) (runAppend s₁ s₂)
      = runAppend (runRestrict b₁ a₁ f₁ s₁) (runRestrict b₂ a₂ f₂ s₂) := by
  induction b₁ generalizing a₁ with
  | nil => exact runRestrict_tensor_nil f₁ f₂ s₁ s₂
  | cons c rest₁ ih =>
    obtain ⟨l, m, heq, hf⟩ := ChainCat.splitWedgeMorphism
      (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ))
        (serialWedge_admitsAltitude rest₁)) a₁ f₁
    subst heq
    have hf' : f₁ = concatChainMap (□(c : ℕ)) (⋁rest₁) l m := by simpa using hf
    subst hf'
    simp only [List.cons_append]
    rw [runRestrict_cons_of_split _ l ⟨m.dims ++ a₂, wedgeTensor m.map f₂⟩
        (List.append_assoc l.dims m.dims a₂) (wedgeTensor_concatChainMap l m f₂) _,
      runRestrict_cons_of_split_rfl l m _ _ rfl,
      split_runAppend_cons]
    dsimp only
    rw [ih m.map (Run.split s₁).2]
    exact (runAppend_assoc _ _ _).symm

/-! ### `Run` and `EdgeChain` are the same thing, functorially -/

/-- Reading a chain off its own descent map, up to a shape identification. -/
theorem chainOfWedge_eqToHom_wedgeOfChain {K : BPSet} (C : CubeChain K) {d : List ℕ+}
    (hd : d = C.dims) :
    chainOfWedge ⟨d, ⋁≡hd ≫ (wedgeOfChain C).2⟩ = C := by
  subst hd
  simpa only [eqToHom_refl, Category.id_comp] using chainOfWedge_wedgeOfChain C

theorem toEdgeChain_toRun {a : ℕ+} (e : EdgeChain (cube (a : ℕ))) :
    (EdgeChain.toRun e).toEdgeChain = e := by
  have hd : 𝟙^(dimSum [a]) = e.1.dims := by
    rw [CubeChain.dims, dims_eq_replicate _ e.2, EdgeChain.length e]; simp [dimSum]
  have hcomp : EdgeChain.toRun e ≫ (serialWedge1 a).hom = ⋁≡hd ≫ (wedgeOfChain e.1).2 := by
    rw [EdgeChain.toRun, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have h := chainOfWedge_eqToHom_wedgeOfChain e.1 hd
  rw [← hcomp] at h
  exact Subtype.ext h

theorem toRun_toEdgeChain {b : ℕ+} (r : Run [b]) : EdgeChain.toRun r.toEdgeChain = r := by
  set C : CubeChain (cube (b : ℕ)) :=
    chainOfWedge ⟨𝟙^(dimSum [b]), r ≫ (serialWedge1 b).hom⟩ with hC
  have hd : 𝟙^(dimSum [b]) = C.dims := by
    rw [CubeChain.dims, dims_eq_replicate _ (chainOfWedge_dim_one _),
      EdgeChain.length (⟨C, chainOfWedge_dim_one _⟩ : EdgeChain (cube (b : ℕ)))]
    simp [dimSum]
  have key : (⋁≡hd) ≫ (wedgeOfChain C).2 = r ≫ (serialWedge1 b).hom := by
    have h := chainOfWedge_injective (K := cube (b : ℕ))
      (show chainOfWedge ⟨𝟙^(dimSum [b]), (⋁≡hd) ≫ (wedgeOfChain C).2⟩
          = chainOfWedge ⟨𝟙^(dimSum [b]), r ≫ (serialWedge1 b).hom⟩ from
        (chainOfWedge_eqToHom_wedgeOfChain C hd).trans hC)
    exact eq_of_heq ((Sigma.mk.injEq ..).mp h).2
  show (⋁≡hd) ≫ (wedgeOfChain C).2 ≫ (serialWedge1 b).inv = r
  rw [← Category.assoc, Iso.comp_inv_eq]
  exact key

theorem runRestrictFace_id {a : ℕ+} (r : Run [a]) :
    runRestrictFace (𝟙 ((cube (a : ℕ)).toPsh)) r = r := by
  rw [runRestrictFace]
  refine Eq.trans (congrArg EdgeChain.toRun ?_) (toRun_toEdgeChain r)
  exact Eq.trans (congrArg (fun u => EdgeChain.restrict u r.toEdgeChain) (rfl : _ = 𝟙 (▫(a : ℕ))))
    (EdgeChain.restrict_id _)

theorem runRestrictFace_comp {a b c : ℕ+}
    (f : (cube (a : ℕ)).toPsh ⟶ (cube (b : ℕ)).toPsh)
    (g : (cube (b : ℕ)).toPsh ⟶ (cube (c : ℕ)).toPsh) (r : Run [c]) :
    runRestrictFace (f ≫ g) r = runRestrictFace f (runRestrictFace g r) := by
  rw [runRestrictFace, runRestrictFace, runRestrictFace, toEdgeChain_toRun,
    ← EdgeChain.restrict_comp]
  congr 1
  refine congrArg (fun u => EdgeChain.restrict u r.toEdgeChain) ?_
  exact (map_yonedaEquiv g (yonedaEquiv f)).symm

/-! ### The one-bead target -/

/-- Splitting a one-bead run is trivial: `[c] ++ [] = [c]` is `rfl`, so no transport appears. -/
theorem split_singleton_fst {d : ℕ+} (r : Run [d]) : (Run.split r).1 = r := by
  have h := runAppend_nil_right (Run.split r).1 (Run.split r).2
  rw [runAppend_split] at h
  exact h.symm

/-- The canonical presentation of a map into a one-bead wedge as a `concatChainMap`: the whole
map is the head chain, and the tail is the point. -/
theorem concat_singleton_presentation {d : ℕ+} {a : List ℕ+} (f : ⋁a ⟶ ⋁[d]) :
    f = eqToHom (congrArg BPSet.serialWedge ((List.append_nil a).symm : a = a ++ []))
        ≫ concatChainMap (□(d : ℕ)) (⋁([] : List ℕ+))
            ⟨a, f ≫ (serialWedge1 d).hom⟩ ⟨[], 𝟙 (⋁([] : List ℕ+))⟩ := by
  have h : serialWedgeAppendHom a ([] : List ℕ+)
        ≫ eqToHom (congrArg BPSet.serialWedge (List.append_nil a))
      = (wedge2RightUnit (⋁a)).hom := serialWedgeAppendIso_right_unitality a
  have hswa : (serialWedgeAppend a ([] : List ℕ+)).inv ≫ (wedge2RightUnit (⋁a)).hom
      = eqToHom (congrArg BPSet.serialWedge (List.append_nil a)) := by
    rw [← h, show serialWedgeAppendHom a ([] : List ℕ+)
        = (serialWedgeAppend a ([] : List ℕ+)).hom from rfl,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hswa' : ∀ {Z : BPSet} (u : ⋁a ⟶ Z),
      (serialWedgeAppend a ([] : List ℕ+)).inv ≫ (wedge2RightUnit (⋁a)).hom ≫ u
        = eqToHom (congrArg BPSet.serialWedge (List.append_nil a)) ≫ u := by
    intro Z u; rw [← Category.assoc, hswa]
  have hn := wedge2RightUnit_naturality (f ≫ (wedge2RightUnit (□(d : ℕ))).hom)
  rw [← Category.assoc] at hn
  have hnat0 := (Iso.cancel_iso_hom_right _ _ (wedge2RightUnit (□(d : ℕ)))).mp hn
  have hnat : wedge2Map (f ≫ (serialWedge1 d).hom) (𝟙 (⋁([] : List ℕ+)))
      = (wedge2RightUnit (⋁a)).hom ≫ f := hnat0
  have key : concatChainMap (□(d : ℕ)) (⋁([] : List ℕ+))
        ⟨a, f ≫ (serialWedge1 d).hom⟩ ⟨[], 𝟙 (⋁([] : List ℕ+))⟩
      = eqToHom (congrArg BPSet.serialWedge (List.append_nil a)) ≫ f := by
    show (serialWedgeAppend a ([] : List ℕ+)).inv
        ≫ wedge2Map (f ≫ (serialWedge1 d).hom) (𝟙 (⋁([] : List ℕ+)))
      = eqToHom (congrArg BPSet.serialWedge (List.append_nil a)) ≫ f
    rw [hnat]
    exact hswa' f
  have fin : eqToHom (congrArg BPSet.serialWedge ((List.append_nil a).symm : a = a ++ []))
      ≫ eqToHom (congrArg BPSet.serialWedge (List.append_nil a)) ≫ f = f := by
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [key]
  exact fin.symm

/-- **`runRestrict` at a one-bead target is `runRestrictWedge`.** -/
theorem runRestrict_singleton {d : ℕ+} {a : List ℕ+} (f : ⋁a ⟶ ⋁[d]) (r : Run [d]) :
    runRestrict [d] a f r = runRestrictWedge a (f ≫ (serialWedge1 d).hom).hom r := by
  rw [runRestrict_cons_of_split f ⟨a, f ≫ (serialWedge1 d).hom⟩ ⟨[], 𝟙 (⋁([] : List ℕ+))⟩
      ((List.append_nil a).symm) (concat_singleton_presentation f) r,
    split_singleton_fst]
  exact runAppend_nil_right _ _

/-! ### `runRestrictWedge`: equation lemmas and functoriality in the cube -/

theorem runRestrictWedge_nil {b : ℕ+}
    (g : (⋁([] : List ℕ+)).toPsh ⟶ (□(b : ℕ)).toPsh) (r : Run [b]) :
    runRestrictWedge [] g r = Functor.LaxMonoidal.ε RunF PUnit.unit := rfl

theorem runRestrictWedge_cons {b c : ℕ+} {rest : List ℕ+}
    (g : (⋁(c :: rest)).toPsh ⟶ (□(b : ℕ)).toPsh) (r : Run [b]) :
    runRestrictWedge (c :: rest) g r
      = runAppend (runRestrictFace ((serialWedge1 c).inv.hom ≫ wedgeInclL [c] rest ≫ g) r)
          (runRestrictWedge rest (wedgeInclR [c] rest ≫ g) r) := rfl

theorem serialWedgeAppendHom_singleton_nil (e : ℕ+) :
    serialWedgeAppendHom [e] ([] : List ℕ+) = (wedge2RightUnit (⋁[e])).hom := by
  have h : serialWedgeAppendHom [e] ([] : List ℕ+) ≫ 𝟙 (⋁([e] ++ ([] : List ℕ+)))
      = (wedge2RightUnit (⋁[e])).hom := serialWedgeAppendIso_right_unitality [e]
  rwa [Category.comp_id] at h

theorem wedgeInclL_singleton_nil (e : ℕ+) :
    wedgeInclL [e] ([] : List ℕ+) = 𝟙 ((⋁[e]).toPsh) := by
  rw [← inl_comp_appendHom, serialWedgeAppendHom_singleton_nil, wedge2RightUnit_hom_hom]
  exact wedge2RightUnitPsh_inl (⋁[e])

/-- **One-bead source**: restricting along a map out of a single bead is a single face
restriction. -/
theorem runRestrictWedge_singleton {e d : ℕ+}
    (g : (⋁[e]).toPsh ⟶ (□(d : ℕ)).toPsh) (r : Run [d]) :
    runRestrictWedge [e] g r = runRestrictFace ((serialWedge1 e).inv.hom ≫ g) r := by
  have hg : wedgeInclL [e] ([] : List ℕ+) ≫ g = g := by
    rw [wedgeInclL_singleton_nil]; exact Category.id_comp g
  rw [runRestrictWedge_cons, hg]
  exact runAppend_nil_right _ _

/-- **Functoriality of `runRestrictWedge` in the target cube.**  Induction on the source list;
the head leg is `runRestrictFace_comp`. -/
theorem runRestrictWedge_face_comp : ∀ (a : List ℕ+) {e d : ℕ+}
    (h : (⋁a).toPsh ⟶ (□(e : ℕ)).toPsh) (k : (□(e : ℕ)).toPsh ⟶ (□(d : ℕ)).toPsh) (r : Run [d]),
    runRestrictWedge a (h ≫ k) r = runRestrictWedge a h (runRestrictFace k r)
  | [], _, _, _, _, _ => Subsingleton.elim _ _
  | c :: rest, e, d, h, k, r => by
      rw [runRestrictWedge_cons, runRestrictWedge_cons]
      congr 1
      · exact runRestrictFace_comp
          ((serialWedge1 c).inv.hom ≫ wedgeInclL [c] rest ≫ h) k r
      · exact runRestrictWedge_face_comp rest (wedgeInclR [c] rest ≫ h) k r

/-! ### Cocycle identities for the half-inclusions at a one-bead head -/

theorem wedgeInclR_singleton (c : ℕ+) (rest : List ℕ+) :
    wedgeInclR [c] rest = wedgeInr (□(c : ℕ)) (⋁rest) := by
  rw [wedgeInclR_cons, wedgeInclR_nil_left]
  exact Category.id_comp _

theorem wedgeInclL_assoc_singleton (c : ℕ+) (rest a₂ : List ℕ+) :
    wedgeInclL [c] (rest ++ a₂) = wedgeInclL [c] rest ≫ wedgeInclL (c :: rest) a₂ := by
  have h1 := wedgeInclL_cons_inr c rest a₂
  have h3 := wedgeInclL_initVertex rest a₂
  have h2 : wedgeInr (□(c : ℕ)) (⋁([] : List ℕ+)) ≫ wedgeInclL [c] rest
      = (⋁rest).initVertex ≫ wedgeInr (□(c : ℕ)) (⋁rest) := by
    rw [wedgeInclL_cons_inr, wedgeInclL_nil_left]; rfl
  have e1 : wedgeInr (□(c : ℕ)) (⋁([] : List ℕ+)) ≫ wedgeInclL [c] (rest ++ a₂)
      = (⋁(rest ++ a₂)).initVertex ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) := by
    rw [wedgeInclL_cons_inr, wedgeInclL_nil_left]; rfl
  have s1 : wedgeInr (□(c : ℕ)) (⋁([] : List ℕ+))
        ≫ wedgeInclL [c] rest ≫ wedgeInclL (c :: rest) a₂
      = ((⋁rest).initVertex ≫ wedgeInr (□(c : ℕ)) (⋁rest)) ≫ wedgeInclL (c :: rest) a₂ :=
    congrArg (fun u => u ≫ wedgeInclL (c :: rest) a₂) h2
  have s2 : ((⋁rest).initVertex ≫ wedgeInr (□(c : ℕ)) (⋁rest)) ≫ wedgeInclL (c :: rest) a₂
      = (⋁rest).initVertex ≫ wedgeInclL rest a₂ ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) :=
    congrArg (fun u => (⋁rest).initVertex ≫ u) h1
  have s3 : (⋁rest).initVertex ≫ wedgeInclL rest a₂ ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂))
      = (⋁(rest ++ a₂)).initVertex ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) :=
    congrArg (fun u => u ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂))) h3
  refine wedge2_hom_ext ?_ (e1.trans (s1.trans (s2.trans s3)).symm)
  exact (wedgeInclL_cons_inl c [] (rest ++ a₂)).trans
    ((wedgeInclL_cons_inl_assoc c [] rest (wedgeInclL (c :: rest) a₂)).trans
      (wedgeInclL_cons_inl c rest a₂)).symm

theorem wedgeInclR_L_singleton (c : ℕ+) (rest a₂ : List ℕ+) :
    wedgeInclR [c] rest ≫ wedgeInclL (c :: rest) a₂
      = wedgeInclL rest a₂ ≫ wedgeInclR [c] (rest ++ a₂) := by
  rw [wedgeInclR_singleton, wedgeInclR_singleton]
  exact wedgeInclL_cons_inr c rest a₂

theorem wedgeInclR_R_singleton (c : ℕ+) (rest a₂ : List ℕ+) :
    wedgeInclR rest a₂ ≫ wedgeInclR [c] (rest ++ a₂) = wedgeInclR (c :: rest) a₂ := by
  rw [wedgeInclR_singleton]
  exact (wedgeInclR_cons c rest a₂).symm

/-- **`runRestrictWedge` splits over a concatenated source.**  Induction on the first block; the
content is the three inclusion cocycles above plus `runAppend`'s associativity. -/
theorem runRestrictWedge_append : ∀ (a₁ : List ℕ+) {a₂ : List ℕ+} {d : ℕ+}
    (g : (⋁(a₁ ++ a₂)).toPsh ⟶ (□(d : ℕ)).toPsh) (r : Run [d]),
    runRestrictWedge (a₁ ++ a₂) g r
      = runAppend (runRestrictWedge a₁ (wedgeInclL a₁ a₂ ≫ g) r)
          (runRestrictWedge a₂ (wedgeInclR a₁ a₂ ≫ g) r)
  | [], a₂, d, g, r => by
      have h : wedgeInclR ([] : List ℕ+) a₂ ≫ g = g := by
        rw [wedgeInclR_nil_left]; exact Category.id_comp g
      rw [runAppend_nil_left, h]
      rfl
  | c :: rest, a₂, d, g, r => by
      have hL : (serialWedge1 c).inv.hom ≫ wedgeInclL [c] (rest ++ a₂) ≫ g
          = (serialWedge1 c).inv.hom ≫ wedgeInclL [c] rest ≫ wedgeInclL (c :: rest) a₂ ≫ g :=
        congrArg (fun u => (serialWedge1 c).inv.hom ≫ u ≫ g)
          (wedgeInclL_assoc_singleton c rest a₂)
      have hM : wedgeInclL rest a₂ ≫ wedgeInclR [c] (rest ++ a₂) ≫ g
          = wedgeInclR [c] rest ≫ wedgeInclL (c :: rest) a₂ ≫ g :=
        congrArg (fun u => u ≫ g) (wedgeInclR_L_singleton c rest a₂).symm
      have hR : wedgeInclR rest a₂ ≫ wedgeInclR [c] (rest ++ a₂) ≫ g
          = wedgeInclR (c :: rest) a₂ ≫ g :=
        congrArg (fun u => u ≫ g) (wedgeInclR_R_singleton c rest a₂)
      show runAppend (runRestrictFace ((serialWedge1 c).inv.hom
              ≫ wedgeInclL [c] (rest ++ a₂) ≫ g) r)
            (runRestrictWedge (rest ++ a₂) (wedgeInclR [c] (rest ++ a₂) ≫ g) r)
          = runAppend (runRestrictWedge (c :: rest) (wedgeInclL (c :: rest) a₂ ≫ g) r)
              (runRestrictWedge a₂ (wedgeInclR (c :: rest) a₂ ≫ g) r)
      rw [runRestrictWedge_cons (wedgeInclL (c :: rest) a₂ ≫ g) r,
        runAppend_assoc_cons',
        runRestrictWedge_append rest (wedgeInclR [c] (rest ++ a₂) ≫ g) r,
        hL, hM, hR]
      rfl

/-! ### Splitting a wedge map over a concatenated target -/

theorem wedgeTensor_inclL {a₁ a₂ b₁ b₂ : List ℕ+} (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂) :
    wedgeInclL a₁ a₂ ≫ (wedgeTensor f₁ f₂).hom = f₁.hom ≫ wedgeInclL b₁ b₂ := by
  show wedgeInclL a₁ a₂ ≫ (serialWedgeAppend a₁ a₂).inv.hom
      ≫ wedge2MapPsh f₁ f₂ ≫ (serialWedgeAppendHom b₁ b₂).hom
    = f₁.hom ≫ wedgeInclL b₁ b₂
  rw [wedgeInclL_appendInv_assoc, wedge2MapPsh_inl_assoc, inl_comp_appendHom]

theorem wedgeTensor_inclR {a₁ a₂ b₁ b₂ : List ℕ+} (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂) :
    wedgeInclR a₁ a₂ ≫ (wedgeTensor f₁ f₂).hom = f₂.hom ≫ wedgeInclR b₁ b₂ := by
  show wedgeInclR a₁ a₂ ≫ (serialWedgeAppend a₁ a₂).inv.hom
      ≫ wedge2MapPsh f₁ f₂ ≫ (serialWedgeAppendHom b₁ b₂).hom
    = f₂.hom ≫ wedgeInclR b₁ b₂
  rw [wedgeInclR_appendInv_assoc, wedge2MapPsh_inr_assoc, inr_comp_appendHom]

/-- **Every map into a concatenated wedge is a `wedgeTensor`**, after cutting the source at the
matching junction — `splitWedgeMorphism` transported along the append iso. -/
theorem wedge_split_tensor {a : List ℕ+} (b₁ b₂ : List ℕ+) (f : ⋁a ⟶ ⋁(b₁ ++ b₂)) :
    ∃ (a₁ a₂ : List ℕ+) (ha : a = a₁ ++ a₂) (f₁ : ⋁a₁ ⟶ ⋁b₁) (f₂ : ⋁a₂ ⟶ ⋁b₂),
      f = eqToHom (congrArg BPSet.serialWedge ha) ≫ wedgeTensor f₁ f₂ := by
  obtain ⟨l, m, heq, hf⟩ := ChainCat.splitWedgeMorphism
    (wedge2_admitsAltitude (serialWedge_admitsAltitude b₁) (serialWedge_admitsAltitude b₂))
    a (f ≫ (serialWedgeAppend b₁ b₂).inv)
  refine ⟨l.dims, m.dims, heq, l.map, m.map, ?_⟩
  calc f = (f ≫ (serialWedgeAppend b₁ b₂).inv) ≫ (serialWedgeAppend b₁ b₂).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (eqToHom (congrArg BPSet.serialWedge heq)
          ≫ concatChainMap (⋁b₁) (⋁b₂) l m) ≫ (serialWedgeAppend b₁ b₂).hom := by rw [hf]
    _ = eqToHom (congrArg BPSet.serialWedge heq) ≫ wedgeTensor l.map m.map := rfl

/-- `runRestrict_tensor` with the head bead of the target spelled `e :: b₂` — the form the
recursion on the target produces. -/
theorem runRestrict_tensor' {a₁ a₂ b₂ : List ℕ+} {e : ℕ+}
    (f₁ : ⋁a₁ ⟶ ⋁[e]) (f₂ : ⋁a₂ ⟶ ⋁b₂) (s₁ : Run [e]) (s₂ : Run b₂) :
    runRestrict (e :: b₂) (a₁ ++ a₂) (wedgeTensor f₁ f₂) (runAppend s₁ s₂)
      = runAppend (runRestrict [e] a₁ f₁ s₁) (runRestrict b₂ a₂ f₂ s₂) :=
  runRestrict_tensor f₁ f₂ s₁ s₂

/-! ### `runRestrictWedge` versus `runRestrict` -/

/-- One-bead target: pulling a wedge-to-cube restriction back along `p` is restricting along
`p` afterwards. -/
theorem runRestrictWedge_comp_singleton {a : List ℕ+} {e d : ℕ+}
    (p : ⋁a ⟶ ⋁[e]) (g : (⋁[e]).toPsh ⟶ (□(d : ℕ)).toPsh) (r : Run [d]) :
    runRestrictWedge a (p.hom ≫ g) r = runRestrict [e] a p (runRestrictWedge [e] g r) := by
  have hcancel : ((serialWedge1 e).hom.hom ≫ (serialWedge1 e).inv.hom) = 𝟙 ((⋁[e]).toPsh) :=
    congrArg BPSet.Hom.hom (serialWedge1 e).hom_inv_id
  have h2 : (serialWedge1 e).hom.hom ≫ (serialWedge1 e).inv.hom ≫ g = g := by
    rw [← Category.assoc, hcancel]; exact Category.id_comp g
  have h3 : (p ≫ (serialWedge1 e).hom).hom ≫ (serialWedge1 e).inv.hom ≫ g = p.hom ≫ g :=
    congrArg (fun u => p.hom ≫ u) h2
  rw [runRestrict_singleton, runRestrictWedge_singleton,
    ← runRestrictWedge_face_comp a ((p ≫ (serialWedge1 e).hom).hom)
      ((serialWedge1 e).inv.hom ≫ g) r, h3]

/-- **`runRestrictWedge` is natural in the source.**  Induction on the target list of `p`; the
head leg is the one-bead case, the tail is the induction hypothesis. -/
theorem runRestrictWedge_comp : ∀ (b : List ℕ+) {a : List ℕ+} {d : ℕ+}
    (p : ⋁a ⟶ ⋁b) (g : (⋁b).toPsh ⟶ (□(d : ℕ)).toPsh) (r : Run [d]),
    runRestrictWedge a (p.hom ≫ g) r = runRestrict b a p (runRestrictWedge b g r)
  | [], a, d, p, g, r => by
      obtain rfl : a = [] := eq_nil_of_dimSum_zero (serialWedge_dimSum_eq p)
      exact Subsingleton.elim _ _
  | e :: rest, a, d, p, g, r => by
      obtain ⟨a₁, a₂, ha, p₁, p₂, hp⟩ := wedge_split_tensor [e] rest p
      subst ha
      have hp' : p = wedgeTensor p₁ p₂ := hp.trans (Category.id_comp _)
      subst hp'
      show runRestrictWedge (a₁ ++ a₂) ((wedgeTensor p₁ p₂).hom ≫ g) r
          = runRestrict (e :: rest) (a₁ ++ a₂) (wedgeTensor p₁ p₂)
              (runRestrictWedge (e :: rest) g r)
      have hL : wedgeInclL a₁ a₂ ≫ (wedgeTensor p₁ p₂).hom ≫ g
          = p₁.hom ≫ wedgeInclL [e] rest ≫ g :=
        congrArg (fun u => u ≫ g) (wedgeTensor_inclL p₁ p₂)
      have hR : wedgeInclR a₁ a₂ ≫ (wedgeTensor p₁ p₂).hom ≫ g
          = p₂.hom ≫ wedgeInclR [e] rest ≫ g :=
        congrArg (fun u => u ≫ g) (wedgeTensor_inclR p₁ p₂)
      rw [runRestrictWedge_append a₁ ((wedgeTensor p₁ p₂).hom ≫ g) r, hL, hR,
        runRestrictWedge_comp_singleton p₁ (wedgeInclL [e] rest ≫ g) r,
        runRestrictWedge_comp rest p₂ (wedgeInclR [e] rest ≫ g) r,
        runRestrictWedge_cons g r,
        ← runRestrictWedge_singleton (wedgeInclL [e] rest ≫ g) r,
        runRestrict_tensor']

/-! ### The two functoriality laws -/

/-- Composition at a one-bead target — the base case the recursion on the target cannot reach by
induction (`[d]` is not a sub-list of `d :: rest`). -/
theorem runRestrict_comp_singleton {a b : List ℕ+} {d : ℕ+}
    (p : ⋁a ⟶ ⋁b) (q : ⋁b ⟶ ⋁[d]) (r : Run [d]) :
    runRestrict [d] a (p ≫ q) r = runRestrict b a p (runRestrict [d] b q r) := by
  rw [runRestrict_singleton (p ≫ q) r, runRestrict_singleton q r]
  exact runRestrictWedge_comp b p ((q ≫ (serialWedge1 d).hom).hom) r

set_option maxHeartbeats 1000000 in
-- each recursion step re-elaborates two nested `wedgeTensor` splits of the same wedge map
theorem runRestrict_comp_aux : ∀ (c : List ℕ+) {a b : List ℕ+} (p : ⋁a ⟶ ⋁b) (q : ⋁b ⟶ ⋁c),
    runRestrict c a (p ≫ q) = runRestrict b a p ∘ runRestrict c b q
  | [], a, b, p, q => by
      obtain rfl : a = [] := eq_nil_of_dimSum_zero (serialWedge_dimSum_eq (p ≫ q))
      exact funext fun r => Subsingleton.elim _ _
  | d :: rest, a, b, p, q => by
      obtain ⟨b₁, b₂, hb, q₁, q₂, hq⟩ := wedge_split_tensor [d] rest q
      subst hb
      have hq' : q = wedgeTensor q₁ q₂ := hq.trans (Category.id_comp _)
      subst hq'
      obtain ⟨a₁, a₂, ha, p₁, p₂, hp⟩ := wedge_split_tensor b₁ b₂ p
      subst ha
      have hp' : p = wedgeTensor p₁ p₂ := hp.trans (Category.id_comp _)
      subst hp'
      have key : ∀ (t : Run [d]) (u : Run rest),
          runRestrict (d :: rest) (a₁ ++ a₂) (wedgeTensor p₁ p₂ ≫ wedgeTensor q₁ q₂)
              (runAppend t u)
            = runRestrict (b₁ ++ b₂) (a₁ ++ a₂) (wedgeTensor p₁ p₂)
                (runRestrict (d :: rest) (b₁ ++ b₂) (wedgeTensor q₁ q₂) (runAppend t u)) := by
        intro t u
        have ih : runRestrict rest a₂ (p₂ ≫ q₂) u
            = runRestrict b₂ a₂ p₂ (runRestrict rest b₂ q₂ u) :=
          congrFun (runRestrict_comp_aux rest p₂ q₂) u
        have hcomp : (wedgeTensor p₁ p₂ ≫ wedgeTensor q₁ q₂ : ⋁(a₁ ++ a₂) ⟶ ⋁(d :: rest))
            = wedgeTensor (p₁ ≫ q₁) (p₂ ≫ q₂) := wedgeTensor_comp p₁ p₂ q₁ q₂
        rw [hcomp, runRestrict_tensor' (p₁ ≫ q₁) (p₂ ≫ q₂) t u,
          runRestrict_tensor' q₁ q₂ t u,
          runRestrict_tensor p₁ p₂ (runRestrict [d] b₁ q₁ t) (runRestrict rest b₂ q₂ u),
          runRestrict_comp_singleton p₁ q₁ t, ih]
      funext r
      have h := key (Run.split r).1 (Run.split r).2
      rw [runAppend_split] at h
      exact h

theorem runRestrict_comp {a b c : List ℕ+} (p : ⋁a ⟶ ⋁b) (q : ⋁b ⟶ ⋁c) :
    runRestrict c a (p ≫ q) = runRestrict b a p ∘ runRestrict c b q :=
  runRestrict_comp_aux c p q

theorem runRestrict_one_id {c : ℕ+} : runRestrict [c] [c] (𝟙 (⋁[c])) = id := by
  funext r
  have hcancel : (serialWedge1 c).inv.hom ≫ (serialWedge1 c).hom.hom
      = 𝟙 ((□(c : ℕ)).toPsh) := congrArg BPSet.Hom.hom (serialWedge1 c).inv_hom_id
  have h : (serialWedge1 c).inv.hom ≫ ((𝟙 (⋁[c])) ≫ (serialWedge1 c).hom).hom
      = 𝟙 ((□(c : ℕ)).toPsh) := hcancel
  rw [runRestrict_singleton, runRestrictWedge_singleton, h]
  exact runRestrictFace_id r

theorem runRestrict_id : ∀ (a : List ℕ+), runRestrict a a (𝟙 (⋁a)) = id
  | [] => funext fun _ => Subsingleton.elim _ _
  | c :: rest => by
      have ih := runRestrict_id rest
      have key : ∀ (t : Run [c]) (u : Run rest),
          runRestrict (c :: rest) (c :: rest) (𝟙 (⋁(c :: rest))) (runAppend t u)
            = runAppend t u := by
        intro t u
        have h := runRestrict_tensor' (𝟙 (⋁[c])) (𝟙 (⋁rest)) t u
        rw [wedgeTensor_id] at h
        simp only [runRestrict_one_id, ih, id_eq] at h
        exact h
      funext r
      have h := key (Run.split r).1 (Run.split r).2
      rw [runAppend_split] at h
      exact h

/-- **The run presheaf.**  `Lines K a` is the set of runs refining the chain `a`. -/
def Lines (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type where
  obj a := Run a.unop.dims
  map f := ↾(runRestrict _ _ f.unop.φ)
  map_id a := by
    show ↾(runRestrict _ _ (𝟙 (⋁(unop a).dims))) = _
    rw [runRestrict_id]; rfl
  map_comp f g := by
    show ↾(runRestrict _ _ (g.unop.φ ≫ f.unop.φ)) = _
    rw [runRestrict_comp]; rfl

end CubeChains
