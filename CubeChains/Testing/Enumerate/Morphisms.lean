import CubeChains.Testing.Enumerate.Enumerate
import CubeChains.Concurrency.Executions.Elements
import CubeChains.Concurrency.Salvetti.EventBraid

/-!
# Testing/Enumerate/Morphisms — verified finite enumeration of the morphisms of `Ch⋆(□n)`

`Ch (□n)` is thin (`cube_chainCat_isThin`), so a hom `a ⟶ b` is either absent or unique; and the
`refine ≌ wedge` equivalence (`equivWedgeCat`, computable) presents that hom as the finite
combinatorial datum `ChainRefine` — a monotone reindexing plus, per cube, a `Box` face inclusion
`▫k ⟶ ▫m` (itself a `Cell m k`).  Hence `Fintype (a ⟶ b)`.

Morphisms of `Ch⋆(□n) = (Lines □n).Elements` then need no run `DecidableEq`: the projection
`π : Ch⋆ ⥤ (Ch)ᵒᵖ` is a discrete opfibration, so a base morphism `g : c₂ ⟶ c₁` and a source run
`r₁` *force* the target `⟨op c₂, (Lines _).map g.op r₁⟩`, the fibre condition holding by `rfl`.
Enumerating base morphisms out of each object thus enumerates every morphism.

Not built by `lake build CubeChains`.
-/

set_option linter.style.nativeDecide false

open CategoryTheory Opposite BPSet CubeChain

namespace CubeChain

/-! ## `Box` face inclusions `▫k ⟶ ▫m` are finite (cube Yoneda: they are `Cell m k`) -/

instance instFintypeBoxHom (k m : ℕ) : Fintype (▫k ⟶ ▫m) :=
  inferInstanceAs (Fintype ((cube m).cells k))

instance instDecidableEqBoxHom (k m : ℕ) : DecidableEq (▫k ⟶ ▫m) :=
  inferInstanceAs (DecidableEq ((cube m).cells k))

/-! ## `ChainRefine a b x y` is finite combinatorial data -/

/-- The data of a `ChainRefine`, unbundled from its `Prop` fields: a reindexing together with a
`Box` face inclusion for each `x`-cube. -/
def RefineData {K : BPSet} (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) : Type :=
  Σ r : Fin x.length → Fin y.length,
    ∀ i : Fin x.length, (▫((x.get i).1 : ℕ) ⟶ ▫((y.get (r i)).1 : ℕ))

instance instFintypeRefineData {K : BPSet} (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) :
    Fintype (RefineData x y) := by unfold RefineData; infer_instance

instance instDecidableEqRefineData {K : BPSet} (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) :
    DecidableEq (RefineData x y) := by unfold RefineData; infer_instance

/-- The `Prop` content of a `ChainRefine`, as a decidable predicate on `RefineData`. -/
def IsRefineData {K : BPSet} (a b : K.cells 0)
    (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) (d : RefineData x y) : Prop :=
  IsCubeChain a x b ∧ IsCubeChain a y b ∧
    (∀ i j : Fin x.length, i ≤ j → d.1 i ≤ d.1 j) ∧
    (∀ i : Fin x.length, (x.get i).2 = K.toPsh.map (d.2 i).op (y.get (d.1 i)).2)

instance instDecidableIsRefineData {K : BPSet} [DecidableEq (K.cells 0)]
    [∀ k, DecidableEq (K.cells k)] (a b : K.cells 0)
    (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) (d : RefineData x y) :
    Decidable (IsRefineData a b x y d) := by unfold IsRefineData; infer_instance

/-- `ChainRefine` is its data cut out by the decidable predicate `IsRefineData`. -/
def chainRefineEquiv {K : BPSet} (a b : K.cells 0)
    (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) :
    ChainRefine a b x y ≃ {d : RefineData x y // IsRefineData a b x y d} where
  toFun f := ⟨⟨f.refinement, f.incl⟩, f.chainx, f.chainy, f.refinementMono, f.inclSpec⟩
  invFun d := { chainx := d.2.1, chainy := d.2.2.1, refinement := d.1.1,
                refinementMono := d.2.2.2.1, incl := d.1.2, inclSpec := d.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeChainRefine {K : BPSet} [DecidableEq (K.cells 0)]
    [∀ k, DecidableEq (K.cells k)] (a b : K.cells 0)
    (x y : List (Σ n : ℕ+, K.cells (n : ℕ))) : Fintype (ChainRefine a b x y) :=
  Fintype.ofEquiv _ (chainRefineEquiv a b x y).symm

/-! ## `Fintype (a ⟶ b)` for `Ch K` — thinness carries the finite `ChainRefine` across `≌` -/

/-- A `Ch K` hom is its refinement datum: `wedgeToRefine` one way, `refineToWedge` back, with both
round-trips free from thinness (`Subsingleton.elim`). -/
def chHomEquivRefine {K : BPSet} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (a b : Ch K) :
    (a ⟶ b) ≃ (wedgeToRefineObj a ⟶ wedgeToRefineObj b) :=
  haveI : Quiver.IsThin (Ch K) := chainCat_hom_subsingleton h₁ h₂
  haveI : Quiver.IsThin (RefineObj K.init K.final) := refineObj_hom_subsingleton h₁ h₂
  { toFun := wedgeToRefineMap
    invFun := fun g => eqToHom (refineToWedgeObj_wedgeToRefineObj a).symm ≫
      (refineToWedge h₁ h₂).map g ≫ eqToHom (refineToWedgeObj_wedgeToRefineObj b)
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

/-- The cube's cells are decidable at every dimension at once
(the `Pi` bundle `instFintypeChainRefine`
asks for). -/
instance instDecidableEqCubeCellsPi (n : ℕ) : ∀ k, DecidableEq ((cube n).cells k) :=
  fun k => instDecidableEqCubeCells n k

/-- **A hom-set of `Ch (□n)` is finite** — via `chHomEquivRefine` and `Fintype (ChainRefine)`. -/
instance instFintypeChHom (n : ℕ) (a b : Ch (cube n)) : Fintype (a ⟶ b) :=
  haveI : Fintype (wedgeToRefineObj a ⟶ wedgeToRefineObj b) :=
    instFintypeChainRefine (cube n).init (cube n).final _ _
  Fintype.ofEquiv _ (chHomEquivRefine (cube_nonSelfLinked n) (cube_admitsAltitude n) a b).symm

end CubeChain

/-! ## Morphisms of `Ch⋆(□n)` — the discrete opfibration forces each target

A base morphism `g : c₂ ⟶ p.chain` in `Ch` and a source run `p.2` determine a unique morphism of
`Ch⋆ K` out of `p`, landing at the forced target `⟨op c₂, (Lines K).map g.op p.2⟩` (fibre condition
by `rfl`).  So enumerating base morphisms out of each object enumerates every morphism. -/

open CubeChain CubeChains

/-- The `Ch⋆`-morphism a base `Ch`-morphism `g : c₂ ⟶ p.chain` induces out of `p`, with its (forced)
target.  This *is* the discrete-opfibration lift of `g.op` at `p`. -/
def morphOut {K : BPSet} (p : Ch⋆ K) {c₂ : Ch K} (g : c₂ ⟶ p.chain) :
    Σ q : Ch⋆ K, (p ⟶ q) :=
  ⟨⟨op c₂, (Lines K).map g.op p.2⟩, ⟨g.op, rfl⟩⟩

/-- **Every morphism of `Ch⋆(□n)`**, as `⟨source, target, hom⟩` triples — the verified
enumeration of
the arrows of the execution category (as the computable underlying multiset). -/
def allChStarMorph (n : ℕ) : Multiset (Σ p q : Ch⋆ (cube n), (p ⟶ q)) :=
  (Finset.univ : Finset (Ch⋆ (cube n))).val.bind fun p =>
    (Finset.univ : Finset (Ch (cube n))).val.bind fun c₂ =>
      (Finset.univ : Finset (c₂ ⟶ p.chain)).val.map fun g => ⟨p, morphOut p g⟩

/-! ## The `ConcPos` label, by definition

This route reduces `permOf` through the `Glue` quotients, so it costs minutes at `n = 3` —
its use is
as an independent oracle against the fast model of `Testing/Enumerate/FastExec`. -/

open RunWedge in
/-- The permutation `ConcPos` assigns a morphism — the `Sₙ`-image of
its braid, `[perm 0, perm 1, …]`. -/
def concPosPerm {n : ℕ} (m : Σ p q : Ch⋆ (cube n), (p ⟶ q)) : List ℕ :=
  (List.finRange (dimSum ((proj (cube n)).obj m.1).dims)).map
    fun i => (permOf ((proj (cube n)).map m.2.2) i : ℕ)
