import CubeChains.Chains.Category
import CubeChains.Chains.Basic
import CubeChains.Chains.Segal
import CubeChains.Chains.SegalAltitude
import CubeChains.Foundations.Altitude
import Mathlib.CategoryTheory.Products.Bifunctor

/-!
# Research/Conjectures

The lowering lemma and the poset conjectures (ClaudeSetup.md §7).
This file collects the statements that remain open: the structural (poset) lemmas
(Lemma 2.11 of arXiv:2103.05336) and the Segal-splitting halves.  Per ClaudeSetup.md
§0 this is the only place `sorry` is allowed for mathematical content (besides the
deferred cube Yoneda lemma `StdCube.canonicalMap`).

The **lowering lemma** (the converse of lifting) is now settled negatively: its
*uniqueness* half is **proved** (faithfulness of the lift, `liftToCh_injective`, via
`Aut.liftToCh_injective_of_jointlySurjective` in `Chains/Category.lean`), reduced to
the single geometric input `chainsJointlySurjective_of_accessible`; but the deep
*existence* reconstruction is **refuted** under its own hypotheses (the `□²`
counterexample, see `Testing/Examples.lean` and `DESIGN.md`), so the lowering lemma
as a whole is false and has been removed.

The lifting lemma, `OrientationPreserving`, the unconditional fact that lifts are
orientation-preserving (`Aut.liftToCh_orientationPreserving`), and the
faithfulness criterion are proved/defined in `Chains/Category.lean`.

**Layer:** Research (the only `sorry`-bearing file).  **Imports:** `Chains/Category`,
`Chains/Basic`, `Chains/Segal`(+`SegalAltitude`), `Foundations/Altitude`.
-/

open CategoryTheory Opposite

namespace ChainCat

/-- The (finite multi)set of cubes of a cube chain, as a multiset over cells of
all dimensions.  Used to state the altitude extensionality lemma (b). -/
def cubes {K : BPSet} (c : CubeChain K) : Multiset (Σ n, K.toPsh.cells n) :=
  (c.cubes.map (fun x => ⟨(x.1 : ℕ), x.2⟩) : List (Σ n, K.toPsh.cells n))

/-- `x` is a face of `y` (an iterated face, in either orientation): the relation
used to state the facewise criterion (c). -/
inductive IsFace (K : BPSet) : (Σ n, K.toPsh.cells n) → (Σ n, K.toPsh.cells n) → Prop
  | refl (x) : IsFace K x x
  | step {n} (ε : Bool) (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) {x} :
      IsFace K x ⟨n, K.toPsh.faceMap ε i c⟩ → IsFace K x ⟨n + 1, c⟩

end ChainCat

namespace Conjectures

variable {K : BPSet}

/-! ## The lowering lemma (the converse direction)

The lowering lemma splits into **existence** (the deep reconstruction of an
automorphism of `K` from one of `Ch K`) and **uniqueness** (faithfulness of the
lift, now proved).  The existence half is **refuted** under its own hypotheses (the
`□²` counterexample), so the lemma is false and only uniqueness survives, below.
Faithfulness is reduced to the geometric statement that chains' classifying maps are
jointly surjective on cells (`ChainsJointlySurjective`, in `Chains/Category.lean`),
which is the only remaining open input on the uniqueness side. -/

/-- **Joint surjectivity from accessibility ([RESEARCH]).**  Every cell of an
accessible `K` lies on a chain from `init` to `final`, so the chains' classifying
maps are jointly surjective on cells.  This is the geometric content behind
faithfulness of the lift; only this combinatorial step (building a chain through a
given cell out of the reachability relation) remains open here. -/
theorem chainsJointlySurjective_of_accessible (h : K.Accessible) :
    ChainsJointlySurjective K := by
  sorry -- [RESEARCH]

/-- **(d) Faithfulness of the lift.**  For accessible `K`, the lift
`Aut K →* Aut (Ch K)` is injective.  This is now *proved* from joint surjectivity
(`Aut.liftToCh_injective_of_jointlySurjective`); the only open input is
`chainsJointlySurjective_of_accessible`. -/
theorem liftToCh_injective (h : K.Accessible) :
    Function.Injective (Aut.liftToCh K) :=
  Aut.liftToCh_injective_of_jointlySurjective (chainsJointlySurjective_of_accessible h)

-- exists_lower_orientationPreserving is REFUTED under its own hypotheses (□²
-- counterexample, see Testing/Examples.lean and DESIGN.md). Removed 2026.
-- (`lower_orientationPreserving`, which derived its existence half from it, was
-- removed with it; faithfulness/uniqueness survives as `liftToCh_injective`.)

/-- **(a) [RESEARCH].** `Ch K` is a poset when `K` is non-self-linked: hom-sets
are subsingletons. -/
theorem hom_subsingleton (h : K.NonSelfLinked) (a b : ChainCat.Obj K) :
    Subsingleton (a ⟶ b) := by
  sorry -- [RESEARCH]

/-- **(b) [RESEARCH].** When `K` admits an altitude function, a cube chain is
determined by its multiset of cubes (an `ext`-style lemma). -/
theorem chain_ext_of_altitude (h : K.AdmitsAltitude) :
    Function.Injective (ChainCat.cubes (K := K)) := by
  sorry -- [RESEARCH]

/-- The cubes of a `Ch K` object, extracted from its classifying wedge map.
**[RESEARCH/DEFERRED]** depends on the map↔chain equivalence (§3); admitted here
so the facewise criterion (c) can be stated. -/
noncomputable def objCubes (a : ChainCat.Obj K) : Multiset (Σ n, K.toPsh.cells n) :=
  sorry

/-- **(c) [RESEARCH].** For non-self-linked `K` admitting an altitude function,
a morphism `a ⟶ b` exists iff every cube of `a` is a face of some cube of `b`. -/
theorem hom_iff_facewise (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b : ChainCat.Obj K) :
    Nonempty (a ⟶ b) ↔
      ∀ x ∈ objCubes a, ∃ y ∈ objCubes b, ChainCat.IsFace K x y := by
  sorry -- [RESEARCH]

/-! ## The Segal property of `Ch` (the hard direction)

`Chains/Segal.lean` builds the **concatenation functor** `chConcat X Y : Ch X × Ch Y ⥤
Ch (X ∨ Y)` and proves it **faithful** (sorry-free, via the mono structure of the
wedge inclusions).  The two remaining halves of the equivalence — **fullness** and
**essential surjectivity** — are the genuinely combinatorial *Segal splitting*: a
chain (resp. a refinement of chains) in `X ∨ Y` must split as an `X`-prefix followed
by a `Y`-suffix through the junction vertex.

Both reduce to the single geometric fact that a wedge map `□^∨(dims) ⟶ X ∨ Y` is a
concatenation: each positive block lands in exactly one of `X`, `Y` (`wedge2_cell_cases`,
`wedge2_inl_ne_inr`), and on a genuine chain `init → final` those blocks are *monotone*
(the `X`-blocks precede the `Y`-blocks).  Discharging the monotonicity — in particular
ruling out a chain that re-crosses the junction (which would only be isomorphic, not
equal, to a split chain) — is the open combinatorial step, staged here.  Everything
downstream (`chSegal`, the n-ary product decomposition) is built on these two Props. -/

open ChainCat

/-- **Essential surjectivity of `chConcat` ([RESEARCH] — Segal splitting).**  Every
chain in `X ∨ Y` is isomorphic to a concatenation of a chain in `X` and a chain in
`Y`.  This is the "splitting" half of the Segal property; the open content is the
monotonicity of the `X`/`Y` blocks along a chain.

**Hypothesis.**  `(wedge2 X Y).AdmitsAltitude` rules out a chain that *re-crosses*
the junction vertex `v`: along a chain the junction vertices have strictly
increasing altitude, so `v` is visited at most once, forcing the `X`-blocks into a
prefix and the `Y`-blocks into a suffix.  Without it (e.g. when `X`/`Y` have a
positive cube looping at `v`) the statement is **false** — a re-crossing chain need
not even be isomorphic to a split chain. -/
theorem chConcat_essSurj (X Y : BPSet) (h : (BPSet.wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).EssSurj where
  mem_essImage c := by
    sorry -- [RESEARCH] Segal splitting: c ≅ chConcat.obj of an X-prefix and a Y-suffix

/-- **Fullness of `chConcat` ([RESEARCH] — Segal splitting).**  A refinement between
two concatenated chains in `X ∨ Y` itself splits into a refinement of the `X`-halves
and one of the `Y`-halves.  Same combinatorial core (and same altitude hypothesis)
as `chConcat_essSurj`. -/
theorem chConcat_full (X Y : BPSet) (h : (BPSet.wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).Full where
  map_surjective {ab ab'} hh := by
    sorry -- [RESEARCH] Segal splitting on morphisms: h.φ splits along wedgeInclL/wedgeInclR

/-- `chConcat X Y` is an equivalence: it is faithful (proved in `Chains/Segal.lean`),
full and essentially surjective (the two staged Segal-splitting Props above, under
the altitude hypothesis ruling out junction re-crossing). -/
theorem chConcat_isEquivalence (X Y : BPSet) (h : (BPSet.wedge2 X Y).AdmitsAltitude) :
    (chConcat X Y).IsEquivalence :=
  haveI := chConcat_full X Y h
  haveI := chConcat_essSurj X Y h
  Functor.IsEquivalence.mk

/-- **The Segal monoidality of `Ch` (binary).**  `Ch(X ∨ Y) ≌ Ch X × Ch Y`: a chain
through the wedge splits canonically at the junction vertex.  Built from
`chConcat X Y` once it is shown to be an equivalence (under the altitude hypothesis
that rules out junction re-crossing). -/
noncomputable def chSegal (X Y : BPSet) (h : (BPSet.wedge2 X Y).AdmitsAltitude) :
    ChainCat.Obj X × ChainCat.Obj Y ≌ ChainCat.Obj (BPSet.wedge2 X Y) :=
  haveI := chConcat_isEquivalence X Y h
  (chConcat X Y).asEquivalence

/-! ### The n-ary Segal decomposition

By recursion on the dimension sequence, `Ch(□^∨(dims))` is the product of the
`Ch(□^{dimᵢ})`.  The base case is the monoidal unit `chUnit : Ch(□⁰) ≌ Discrete PUnit`
(proved sorry-free in `Chains/Segal.lean`); the step glues one more cube with `chSegal`. -/

/-- The product of the chain categories of the individual cubes in a dimension
sequence (right-folded, matching `serialWedge`). -/
def chainProd : List ℕ+ → Type
  | [] => Discrete PUnit.{1}
  | n :: rest => ChainCat.Obj (BPSet.cube (n : ℕ)) × chainProd rest

noncomputable instance instCategoryChainProd : ∀ dims : List ℕ+, Category (chainProd dims)
  | [] => inferInstanceAs (Category (Discrete PUnit))
  | n :: rest =>
      letI := instCategoryChainProd rest
      inferInstanceAs (Category (ChainCat.Obj (BPSet.cube (n : ℕ)) × chainProd rest))

/-- **The n-ary Segal decomposition.**  `Ch(□^∨(dims)) ≌ ∏ᵢ Ch(□^{dimᵢ})`.  Recursion
on `dims`: `[]` is the unit `chUnit`, and `n :: rest` glues the head cube via
`chSegal (cube n) (serialWedge rest)` and recurses on the tail. -/
noncomputable def chSegalProd : ∀ dims : List ℕ+,
    chainProd dims ≌ ChainCat.Obj (BPSet.serialWedge dims)
  | [] => chUnit.{0}.symm
  | n :: rest =>
      letI := instCategoryChainProd rest
      ((CategoryTheory.Equivalence.refl :
          ChainCat.Obj (BPSet.cube (n : ℕ)) ≌ ChainCat.Obj (BPSet.cube (n : ℕ))).prod
        (chSegalProd rest)).trans
        (chSegal (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest)
          (BPSet.wedge2_admitsAltitude (BPSet.cube_admitsAltitude (n : ℕ))
            (BPSet.serialWedge_admitsAltitude rest)))

end Conjectures
