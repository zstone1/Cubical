import CubeChains.Testing.Enumerate
import CubeChains.Salvetti.Elements
import CubeChains.Salvetti.EventBraid

/-!
# Testing/Morphisms — verified finite enumeration of the morphisms of `Ch⋆(□n)`

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

/-! ## The crossing permutation, combinatorially — no wedge map, no `Glue`

`permOf` reads its wedge map only through `blockIdx`/`blockFace`, ordered by the run-free flattening
`pos` (`eventEquiv_mk`).  Along `wedgeToRefineMap` those *are* a `ChainRefine`'s `refinement` and
`faceEmb ∘ incl`.  So the permutation is a pure `ℕ`-arithmetic read-off of the combinatorial data —
the ~100× win over reducing `refineToWedge`/`coordMap` through `Glue.gluePsh` quotients. -/

/-- The flattened position at which coarser bead `j` starts (prefix sum of bead dimensions). -/
def dimPrefix {K : BPSet} (l : List (Σ n : ℕ+, K.cells (n : ℕ))) (j : ℕ) : ℕ :=
  ((l.take j).map fun c => (c.1 : ℕ)).sum

/-- **The crossing permutation of a refinement, as its shadow** `[image 0, image 1, …]` on the
canonically flattened events (finer position ↦ coarser position).  Read straight off `ChainRefine`:
finer event `⟨i, k⟩` lands in coarser bead `refinement i` at within-bead offset `faceEmb (incl i) k`.
This is the underlying `Sₙ`-permutation of the braid `ConcPos` assigns (`eventEquiv_mk`). -/
def permShadow {K : BPSet} {a b : K.cells 0} {x y : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (cr : ChainRefine a b x y) : List ℕ :=
  (List.finRange x.length).flatMap fun i =>
    (List.finRange ((x.get i).1 : ℕ)).map fun k =>
      dimPrefix y (cr.refinement i) + (faceEmb (cr.incl i) k).val

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

/-- The cube's cells are decidable at every dimension at once (the `Pi` bundle `instFintypeChainRefine`
asks for). -/
instance instDecidableEqCubeCellsPi (n : ℕ) : ∀ k, DecidableEq ((cube n).cells k) :=
  fun k => instDecidableEqCubeCells n k

/-- **A hom-set of `Ch (□n)` is finite** — via `chHomEquivRefine` and `Fintype (ChainRefine)`. -/
instance instFintypeChHom (n : ℕ) (a b : Ch (cube n)) : Fintype (a ⟶ b) :=
  haveI : Fintype (wedgeToRefineObj a ⟶ wedgeToRefineObj b) :=
    instFintypeChainRefine (cube n).init (cube n).final _ _
  Fintype.ofEquiv _ (chHomEquivRefine (cube_nonSelfLinked n) (cube_admitsAltitude n) a b).symm

end CubeChain

open CubeChain in
/-- Total number of morphisms of `Ch (□n)` (a smoke test for the hom `Fintype`). -/
def chHomCount (n : ℕ) : ℕ :=
  ∑ a : Ch (cube n), ∑ b : Ch (cube n), Fintype.card (a ⟶ b)

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

/-- **Every morphism of `Ch⋆(□n)`**, as `⟨source, target, hom⟩` triples — the verified enumeration of
the arrows of the execution category (as the computable underlying multiset). -/
def allChStarMorph (n : ℕ) : Multiset (Σ p q : Ch⋆ (cube n), (p ⟶ q)) :=
  (Finset.univ : Finset (Ch⋆ (cube n))).val.bind fun p =>
    (Finset.univ : Finset (Ch (cube n))).val.bind fun c₂ =>
      (Finset.univ : Finset (c₂ ⟶ p.chain)).val.map fun g => ⟨p, morphOut p g⟩

/-- The signed Artin braid word `ConcPos` assigns to each enumerated morphism. -/
def allBraidWords (n : ℕ) : Multiset (List ℤ) :=
  (allChStarMorph n).map fun m => RunWedge.braidWordZ ((proj (cube n)).map m.2.2)

/-! ## The boundary filter: `Ch⋆(∂□n) ↪ Ch⋆(□n)` as chains avoiding the top cell

`∂□ⁿ ↪ □ⁿ` is the sub-precubical set omitting the single `n`-cell (every lower cell survives).  So a
chain factors through `∂□ⁿ` exactly when it uses no `n`-cube — the decidable filter below.  It is
refinement-closed (a finer chain's cubes are faces, of dimension `≤`), so filtering the *source*
of each morphism carves out the full subcategory `Ch⋆(∂□n)`. -/

/-- A `Ch⋆(□n)` object lies in `∂□ⁿ`: its chain uses no top (`n`-dimensional) cube. -/
def IsBoundaryObj (n : ℕ) (p : Ch⋆ (cube n)) : Prop := ∀ d ∈ p.chain.dims, (d : ℕ) ≠ n

instance (n : ℕ) (p : Ch⋆ (cube n)) : Decidable (IsBoundaryObj n p) :=
  inferInstanceAs (Decidable (∀ d ∈ p.chain.dims, (d : ℕ) ≠ n))

/-- Morphisms of `Ch⋆(∂□n)` — those of `Ch⋆(□n)` whose (coarser) source avoids the top cell. -/
def boundaryMorph (n : ℕ) : Multiset (Σ p q : Ch⋆ (cube n), (p ⟶ q)) :=
  (allChStarMorph n).filter fun m => IsBoundaryObj n m.1

/-- **The braids of the 3-cube minus its top cell** — the signed Artin word of every morphism of
`Ch⋆(∂□³)`. -/
def boundaryBraidWords (n : ℕ) : Multiset (List ℤ) :=
  (boundaryMorph n).map fun m => RunWedge.braidWordZ ((proj (cube n)).map m.2.2)

/-! ## Fast: the crossing permutations combinatorially, straight off `ChainRefine`

`permShadow` computes each refinement's permutation from `ChainRefine` data alone — no wedge map, no
`Glue` reduction — so it is instant where the `braidWordZ` route above took minutes. -/

/-- The non-identity crossing permutations of all refinements of `Ch(□n)`, combinatorially. -/
def allChainPerms (n : ℕ) : Multiset (List ℕ) :=
  (Finset.univ : Finset (CubeChain (cube n))).val.bind fun Cx =>
    (Finset.univ : Finset (CubeChain (cube n))).val.bind fun Cy =>
      (Finset.univ :
          Finset (ChainRefine (cube n).init (cube n).final Cx.cubes Cy.cubes)).val.map permShadow

/-! ## Wiring the combinatorial label to `ConcPos`

`concPosPerm m` is the honest permutation `ConcPos` assigns `m` — the `Sₙ`-image of `braidFunctor`'s
braid, `permOf ((proj K).map m)`.  `combPerm m` is the fast combinatorial shadow `permShadow` off the
base refinement.

⚠ `permShadow` reads the **run-free** flattening, whereas `permOf` orders events by the **run**
(`runOrd`); the two diverge (`Testing/Demo` shows it).  Re-deriving `permShadow` on the run order —
so the graph/loop tooling computes the real `ConcPos` — is the follow-up to `eventCross_run`. -/

open RunWedge in
/-- The permutation `ConcPos` assigns a morphism — the `Sₙ`-image of its braid, `[perm 0, perm 1, …]`. -/
def concPosPerm {n : ℕ} (m : Σ p q : Ch⋆ (cube n), (p ⟶ q)) : List ℕ :=
  (List.finRange (Sev ((proj (cube n)).obj m.1))).map
    fun i => (permOf ((proj (cube n)).map m.2.2) i : ℕ)

/-- The same permutation, combinatorially, off the base refinement `wedgeToRefineMap`. -/
def combPerm {n : ℕ} (m : Σ p q : Ch⋆ (cube n), (p ⟶ q)) : List ℕ :=
  permShadow (wedgeToRefineMap m.2.2.1.unop)
