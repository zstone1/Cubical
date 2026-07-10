import CubeChains.Chains.Category
import CubeChains.Chains.Basic
import CubeChains.Foundations.Altitude
import CubeChains.Cobordisms.Composition

/-!
# Research/Conjectures

The lowering lemma and the poset conjectures (ClaudeSetup.md §7).
This file collects the statements that remain open: the structural (poset) lemmas
(Lemma 2.11 of arXiv:2103.05336) and the directed-cobordism π₀ van-Kampen statements.
Per ClaudeSetup.md §0 this is the only place `sorry` is allowed for mathematical
content (besides the deferred cube Yoneda lemma `StdCube.canonicalMap`).

The **Segal-splitting halves** used to be staged here; they are now **proved**
(sorry-free) and have moved to `Chains/SegalProd.lean` (`chSegal`, `chSegalProd`, …),
built on the sorry-free `Chains/SegalSplit.lean`.

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
`Chains/Basic`, `Foundations/Altitude`, `Cobordisms/Composition`.
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

namespace PrecubicalSet

/-! ## Directed-cobordism source-leg π₀ van-Kampen ([RESEARCH])

The pushout associator of `DirectedCobordism.comp` (the M5 coherence iso, mathlib
`pushoutAssoc`) is **no longer here**: it is now a first-class, sorry-free theorem
`PrecubicalSet.dcob_pushout_associator` in `Cobordisms/Associativity.lean` (consumed
by `Cobordisms/DCob.lean`).  What remains open in this section are the genuinely
research-level π₀ van-Kampen statements for the source leg under the rel-∂ moves.

### π₀ van-Kampen for the source leg under the unit moves ([RESEARCH])

Prepending (`unitL`) or appending (`unitR`) a cylinder to a cobordism `W` is a
`π₀`-equivalence of the middle objects that commutes with the source leg, so the
source-leg `π₀`-injectivity invariant is unchanged.  These are the **unit-move**
halves of the rel-∂ invariance of `srcLegπ₀Injective`; the *iso* half is already
proved in `Cobordisms/NonTriviality.lean` (`srcLegπ₀Injective_cobIso_iff`).  Stated
rawly here (only `π₀.map`, `comp`, `idCob`, `.inl`, `Function.Injective`) so they
carry no dependency on the `srcLegπ₀Injective`/`cobordismRel` bundles that consume
them in `NonTriviality.lean`. -/

/-- **Source-leg π₀-injectivity is invariant under prepending a cylinder ([RESEARCH]).**
The `unitL` move `W ↦ (idCob X).comp W` is a π₀-equivalence of middles commuting with
the source leg. -/
theorem dcob_unitL_srcInj_iff {X Y : PrecubicalSet} (W : X ⇒c Y) :
    Function.Injective (π₀.map W.inl)
      ↔ Function.Injective (π₀.map ((idCob X).comp W).inl) := by
  -- TODO(dCob): π₀ van-Kampen — prepending/appending a cylinder is a π₀-equivalence
  -- of middles commuting with the source leg
  sorry -- [RESEARCH]

/-- **Source-leg π₀-injectivity is invariant under appending a cylinder ([RESEARCH]).**
The `unitR` move `W ↦ W.comp (idCob Y)` is a π₀-equivalence of middles commuting with
the source leg. -/
theorem dcob_unitR_srcInj_iff {X Y : PrecubicalSet} (W : X ⇒c Y) :
    Function.Injective (π₀.map W.inl)
      ↔ Function.Injective (π₀.map (W.comp (idCob Y)).inl) := by
  -- TODO(dCob): π₀ van-Kampen — prepending/appending a cylinder is a π₀-equivalence
  -- of middles commuting with the source leg
  sorry -- [RESEARCH]

/-- **Source-leg π₀-injectivity is invariant under the junction move ([RESEARCH]).**
The **junction** move `U.comp ((idCob M).comp W) ↦ U.comp W` (cancelling a cylinder
collar inserted at the shared `M`) is a π₀-equivalence of the middle objects commuting
with the source leg: inserting the middle collar does not change the source factor `U`
(both source legs are `U.inl ≫ pushout.inl …`), so source-leg π₀-injectivity is
preserved.  Stated rawly here (only `π₀.map`, `comp`, `idCob`, `.inl`,
`Function.Injective`) so it carries no dependency on the
`srcLegπ₀Injective`/`cobordismRel` bundles that consume it in `NonTriviality.lean`. -/
theorem dcob_junction_srcInj_iff {X M Y : PrecubicalSet} (U : X ⇒c M) (W : M ⇒c Y) :
    Function.Injective (π₀.map (U.comp ((idCob M).comp W)).inl)
      ↔ Function.Injective (π₀.map (U.comp W).inl) := by
  -- TODO(dCob): π₀ van-Kampen — inserting/removing a middle cylinder collar is a
  -- π₀-equivalence of middles commuting with the source leg
  sorry -- [RESEARCH]

end PrecubicalSet

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

/-! ## The Segal property of `Ch` — MOVED (now proved, `Chains/SegalProd.lean`)

The Segal monoidality of `Ch` used to be staged here.  It is now **proved sorry-free**
and lives in the `Chains` layer: `ChainCat.chConcat_essSurj`, `chConcat_full`,
`chConcat_isEquivalence`, `chSegal`, and the n-ary `chSegalProd` are all in
`Chains/SegalProd.lean`, built on the sorry-free splitting lemmas
`ChainCat.chain_split` / `chConcat_map_surjective` (`Chains/SegalSplit.lean`).  Only the
side condition `(wedge2 X Y).AdmitsAltitude` is needed, discharged by
`Chains/SegalAltitude.lean`. -/

end Conjectures
