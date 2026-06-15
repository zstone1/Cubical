import CubeChains.Chains.Category
import CubeChains.Chains.Basic
import CubeChains.Altitude

/-!
# The lowering lemma and the poset conjectures (ClaudeSetup.md §7)

This file collects the statements that remain open: the *existence* half of the
lowering lemma and the structural (poset) lemmas (Lemma 2.11 of arXiv:2103.05336).
Per ClaudeSetup.md §0 this is the only place `sorry` is allowed for mathematical
content (besides the deferred cube Yoneda lemma `StdCube.canonicalMap`).

The **lowering lemma** (the converse of lifting) is now split: its *uniqueness*
half is **proved** (faithfulness of the lift, `liftToCh_injective`, via
`Aut.liftToCh_injective_of_jointlySurjective` in `Chains/Category.lean`), reduced to
the single geometric input `chainsJointlySurjective_of_accessible`; only the deep
*existence* reconstruction `exists_lower_orientationPreserving` stays open.

The lifting lemma, `OrientationPreserving`, the unconditional fact that lifts are
orientation-preserving (`Aut.liftToCh_orientationPreserving`), and the
faithfulness criterion are proved/defined in `Chains/Category.lean`.
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

We split the lowering lemma `lower_orientationPreserving` into **existence** (the
deep reconstruction of an automorphism of `K` from one of `Ch K`, still open) and
**uniqueness** (faithfulness of the lift, now proved).  Faithfulness is reduced to
the geometric statement that chains' classifying maps are jointly surjective on
cells (`ChainsJointlySurjective`, in `Chains/Category.lean`), which is the only
remaining open input on the uniqueness side. -/

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

/-- **Existence of the lowering ([RESEARCH]).**  Under the side conditions, every
orientation-preserving automorphism of `Ch K` is induced by *some* automorphism of
`K`.  This is the deep reconstruction step; it remains open. -/
theorem exists_lower_orientationPreserving
    (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (h₃ : K.Accessible)
    (Φ : Aut (Ch.obj K)) (hΦ : OrientationPreserving Φ) :
    ∃ σ : Aut K, Aut.liftToCh K σ = Φ := by
  sorry -- [RESEARCH]

/-- **Lowering.**  Under the side conditions, every orientation-preserving
automorphism of `Ch K` is induced by a *unique* automorphism of `K`.  Uniqueness is
proved here from faithfulness of the lift (`liftToCh_injective`); only existence
(`exists_lower_orientationPreserving`) remains open. -/
theorem lower_orientationPreserving
    (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (h₃ : K.Accessible)
    (Φ : Aut (Ch.obj K)) (hΦ : OrientationPreserving Φ) :
    ∃! σ : Aut K, Aut.liftToCh K σ = Φ := by
  obtain ⟨σ, hσ⟩ := exists_lower_orientationPreserving h₁ h₂ h₃ Φ hΦ
  exact ⟨σ, hσ, fun τ hτ => liftToCh_injective h₃ (hτ.trans hσ.symm)⟩

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

end Conjectures
