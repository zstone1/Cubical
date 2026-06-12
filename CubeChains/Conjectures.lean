import CubeChains.Chains.Category
import CubeChains.Chains.Basic
import CubeChains.Altitude

/-!
# The two lemmas and the poset conjectures (ClaudeSetup.md §7)

This file collects the statements that are *not* proved here: the lowering lemma
and the structural (poset) lemmas (Lemma 2.11 of arXiv:2103.05336).  Per
ClaudeSetup.md §0 this is the only place `sorry` is allowed for mathematical
content (besides the deferred cube Yoneda lemma `StdCube.canonicalMap`).

The lifting lemma and `OrientationPreserving` are proved/defined elsewhere
(`Aut.liftToCh`, here `OrientationPreserving`).
-/

open CategoryTheory

namespace ChainCat

/-- The (finite multi)set of cubes of a cube chain, as a multiset over cells of
all dimensions.  Used to state the altitude extensionality lemma (b). -/
def cubes {K : BPSet} (c : CubeChain K) : Multiset (Σ n, K.toPsh.cells n) :=
  (Finset.univ : Finset (Fin c.dims.length)).val.map
    (fun i => ⟨(c.dims.get i : ℕ), c.cube i⟩)

/-- `x` is a face of `y` (an iterated face, in either orientation): the relation
used to state the facewise criterion (c). -/
inductive IsFace (K : BPSet) : (Σ n, K.toPsh.cells n) → (Σ n, K.toPsh.cells n) → Prop
  | refl (x) : IsFace K x x
  | step {n} (ε : Bool) (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) {x} :
      IsFace K x ⟨n, K.toPsh.faceMap ε i c⟩ → IsFace K x ⟨n + 1, c⟩

end ChainCat

/-- **Orientation-preserving** (ClaudeSetup.md §7).  An automorphism of `Ch K`
preserves dimension sequences.

**[RESEARCH] this definition is provisional and may need strengthening** (e.g.
compatibility with altitude); it is isolated here so it is easy to revise. -/
def OrientationPreserving {K : BPSet} (Φ : Aut (Ch.obj K)) : Prop :=
  ∀ a : ChainCat.Obj K, (Φ.hom.toFunctor.obj a).dims = a.dims

namespace Conjectures

variable {K : BPSet}

/-- **Lowering (STATE ONLY — [RESEARCH]).** Under the side conditions, every
orientation-preserving automorphism of `Ch K` is induced by a unique automorphism
of `K`. -/
theorem lower_orientationPreserving
    (K : BPSet) (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (h₃ : K.Accessible)
    (Φ : Aut (Ch.obj K)) (hΦ : OrientationPreserving Φ) :
    ∃! σ : Aut K, Aut.liftToCh K σ = Φ := by
  sorry -- [RESEARCH]

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

/-- **(d) [RESEARCH].** The lift `Aut K →* Aut (Ch K)` is injective for
accessible `K` (faithfulness of the lift). -/
theorem liftToCh_injective (h : K.Accessible) :
    Function.Injective (Aut.liftToCh K) := by
  sorry -- [RESEARCH]

end Conjectures
