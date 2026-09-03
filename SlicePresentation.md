# Task: present Ch(K)[W⁻¹] by gluing presentations of localized slices
Context

This repository formalizes, in Lean 4 / Mathlib, a category Ch(K) attached to a (bipointed) precubical set K, together with a functor F : Ch(K) ⥤ Ch(Z) which is a discrete fibration (Ch(K) is the category of elements of a presheaf X on Ch(Z)). These proofs exist. Both categories carry a class of morphisms (the "inert" morphisms, call it W), with W_K := F⁻¹ W_Z. Localization uses Mathlib's CategoryTheory.Localization with MorphismProperty. This all exists in the repo.

## Ch(Z), its slices, the discrete fibration theorem for F.

Presentation already exists, and is equivalent to a 2-polygraph.
We already have a presentation for Ch(Z)[W_Z⁻¹] in terms of PosBraid, using the garside presentation. The Garside generators corresponding to the maps 1^n → [n]. But we will
want to use others as well, such as the artin presentation.

Goal. A theorem producing a presentation of Ch(K)[W_K⁻¹] from a presentation of Ch(Z)[W_Z⁻¹].
Both the Artin and Garside presentations must lift through the same mechanism; the mechanism must never mention braids. The trick will be to separate the logic. 

We already have some machinery now to build presentations of Ch(Z)[W_K⁻¹]. 
The next big thing is to take any such presentation, cut it up into a functorial family of presentations of the localized slices (Ch(Z)/d)[W_Z⁻¹]. Turn those into presentations of
(Ch(K)/c)[W_K⁻¹], and then reassemble them into a presentation of (Ch(K))[W_K⁻¹].

The mathematics (what you are formalizing)
1. Slices agree. Since F is a discrete fibration, for every object c of Ch(K) the induced functor Ch(K)/c ⥤ Ch(Z)/F(c) is an isomorphism of categories, and it identifies W_K/c with W_Z/F(c). Hence (Ch(K)/c)[W_K⁻¹] ≅ (Ch(Z)/F(c))[W_Z⁻¹].
Localization is the colimit of localized slices. For any category C and class W (containing identities), C[W⁻¹] is the colimit over c ∈ C of (C/c)[W⁻¹], the transition maps being postcomposition. Equivalently, and this is the form to formalize: a functor C[W⁻¹] ⥤ E is the same thing as a family of functors (C/c)[W⁻¹] ⥤ E compatible with postcomposition.
2. Gluing presentations. Given a functor P : D ⥤ Pres (see the design note on Pres below) with natural isomorphisms presented (P d) ≅ (D/d)[W_D⁻¹], define the glued presentation Glue X P for the discrete fibration ∫X → D:
objects: objects of ∫X;
generators: pairs (x ∈ X d, g ∈ (P d).gens), i.e. a copy of P d for each element over d;
relations: the relations of each copy, plus for each f : d' → d, each x ∈ X d, each generator g of P d', the relation (f^* x, g) = (x, P f g) (right side is a path, since P f sends generators to paths). Theorem: Glue X P presents (∫X)[W⁻¹]. Proof via 1 + 2: functors out of presented (Glue X P) are compatible families out of the presented (P (F c)), i.e. out of the (C/c)[W⁻¹], i.e. functors out of C[W⁻¹].
3. Reduction to a generating set. A set S of objects of C = ∫X is generating if every object has an arrow into some object of S (∀ c, ∃ s ∈ S, Nonempty (c ⟶ s)). Then Glue_S X P, defined with copies of P (F s) only for s ∈ S and with overlap relations (s_i, P a g) = (s_j, P b g) for every span s_i ← e → s_j in C (over a, b in D) and every generator g of P (F e), including i = j, still presents C[W⁻¹]. Same proof shape: a compatible family is determined by its values on S, and the overlap relations are exactly what makes an assignment on S extend to a compatible family. Further reduction: if a span factors through a larger span (e → e' with both legs factoring), its overlap relations are consequences of those at e'; so overlap relations at maximal spans suffice when maximal spans generate.
4. Instantiation. For Ch(K) with K finite and acyclic, the maximal chains (objects with no non-identity outgoing arrow) form a generating set. The functor P is built on the Ch(Z) side from the braid presentations using that slices over wedges are products of slices over cubes.

## Design constraints (read carefully)
- Generality. Phases A and B below must be stated for an arbitrary category D, presheaf X : Dᵒᵖ ⥤ Type, and MorphismProperty W_D, with C := ∫X (use Mathlib's category of elements, or the repo's discrete-fibration API if it is more convenient; do not duplicate). Ch(K), Ch(Z), braids and wedges appear only in Phase C/D.
- Morphisms of presentations. If Presentation has no morphism notion, add one: a map on objects, a map from generators to paths of the free category on the target, such that each relation of the source is derivable in the target. Generators must be allowed to go to paths, not just generators — the maps between slices over wedges will send braid generators to words. If a morphism notion already exists, check whether it allows this; if not, generalize it.
- No general colimits of presentations. Do not try to construct colimits in the category of presentations or use CategoryTheory.Limits for them. Glue is defined by explicit data, and its correctness is proved through the universal property of presented, as in item 3 above.
- Avoid colimits in Cat. Item 2 should be proved as the stated bijection of functors (via Localization.StrictUniversalPropertyFixedTarget / the universal property of MorphismProperty.Q), not by constructing a colimit cocone in Cat.
- Do not modify the existing Ch(Z), discrete-fibration, or braid-presentation theorems except to add exports/lemmas. If an existing definition genuinely obstructs the plan, stop and report rather than refactoring.
- Statements first. For each phase, write all theorem statements with sorry, get the file compiling, and only then fill proofs in dependency order. A compiling set of statements is a valid checkpoint to report at.
- Keep everything sorry-free at the end of each phase before moving on. Report precisely which statement blocked you and why if one does.

## Phase 0 — Survey
Locate and record in a beads structure: the names and signatures of Ch(K), Ch(Z), the discrete fibration and its category-of-elements description, the W we are using for merges, the Presentation structure, etc. Consider what mathlib constructions apply: Over, IsLocalization, etc.

Please make sure that everyone who is picking up a bead here knows what the relevant files names and whatnot are. The goal should be to reduce the amount of start-up time and duplicate searching across agents.

### Phase A — General gluing theory (arbitrary D, X, W_D)

Notation: C := ∫X, F : C ⥤ D the projection, W_C := W_D.inverseImage F.

A1. sliceIso (c : C) : Over c ≌ Over (F c) (an isomorphism; an equivalence is acceptable if the repo's slices make iso awkward), and W_C.over c corresponds to W_D.over (F c) under it.
A2. Natural iso (Over c)[W_C⁻¹] ≅ (Over (F c))[W_D⁻¹], natural in c (postcomposition on both sides).
A3. For any category C, class W containing identities, and target E: functors C[W⁻¹] ⥤ E correspond bijectively to families G c : (Over c)[W⁻¹] ⥤ E with G c' = G c ∘ (postcompose u)[W⁻¹] for every u : c' → c. Prove the direction "family ↦ functor" first: since Over c has a terminal object, the family is determined by its values at (c, 𝟙 c) and on arrows; check that inverting W/c for all c is inverting W.
A4. Definition of Glue X P for P : D ⥤ Pres (with the morphism notion above), and theorem presents (Glue X P) (C[W_C⁻¹]) assuming ∀ d, presents (P d) ((Over d)[W_D⁻¹]) naturally in d. Proof through A2, A3, and the universal property of presented.
A5. Generating (S : Set C) := ∀ c, ∃ s ∈ S, Nonempty (c ⟶ s). Definition of GlueOn S X P (copies over S, overlap relations for spans between elements of S, including self-spans), and theorem Generating S → presents (GlueOn S X P) (C[W_C⁻¹]). Prove it directly with the same universal-property argument, not by comparing with Glue.
A6 (optional, do after Phase D if time permits). Overlap relations at maximal spans suffice, under a well-foundedness hypothesis on spans.
A7 (optional). If X w is a bijection for all w ∈ W_D, then X descends to X̄ on D[W_D⁻¹], C[W_C⁻¹] ≅ ∫X̄, and Glue X P is isomorphic to the pullback of Glue 1 P (the glued presentation of D[W_D⁻¹]) along ∫X̄ → D[W_D⁻¹] provided every generator of P d is the pushforward of a generator over its own target. State this; prove only if cheap.

### Phase B — Products and wedges
B1. For categories E, E' and classes W, W' containing identities, (E × E')[(W × W')⁻¹] ≅ E[W⁻¹] × E'[W'⁻¹]. Prove via universal properties.
B2. Product of presentations presents the product of presented categories.
B3. In Ch(Z): Over (A ∨ B) ≅ Over A × Over B, from the decomposition of morphisms into a wedge (state the exact hom-set decomposition you use as its own lemma). Together with the fact that inert morphisms into a wedge are exactly products of inert morphisms into the components.
B4. Hence (Over (∨ a))[W_Z⁻¹] ≅ ∏ᵢ (Over [aᵢ])[W_Z⁻¹], natural in maps of wedges. Naturality is the hard part: a map of wedges induces a map between products of localized cube-slices, and you must show it corresponds to a morphism of presentations (generators to paths).

### Phase C — The functor P : Ch(Z) ⥤ Pres, for each braid presentation
C1. From an existing presentation of Ch(Z)[W_Z⁻¹] (Artin or Garside), extract presentations P_cube n of (Over [n])[W_Z⁻¹] and the morphisms induced by maps [m] → [n]. Do this once as a construction parametrized by the presentation, not twice.
C2. Extend to wedges by P (∨ a) := ∏ᵢ P_cube aᵢ, functorial via B4.
C3. Theorem: ∀ d, presents (P d) ((Over d)[W_Z⁻¹]), naturally.
Instantiate for Garside; the instantiation should be a few lines each. If it isn't, the parametrization in C1 is wrong.
### Phase D — Ch(K)
D1. Main theorem: for any P satisfying C3, presents (GlueOn (MaximalChains K) X_K P) (Ch(K)[W_K⁻¹]).
D2. Corollaries for Garside.
D3. Sanity check: for K = □ⁿ, MaximalChains K is a singleton and the glued presentation is P_cube n with no overlap relations; the theorem should reduce to the existing cube case up to a presentation isomorphism.
Reporting

