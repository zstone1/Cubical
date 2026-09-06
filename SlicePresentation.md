# Task: present Ch(K)[W⁻¹] by gluing presentations of localized slices

**Outcome.** `ChainCat.presentsChainsColimit K p hP R` presents `Ch(K)[W⁻¹]` for every `K`, with no
hypothesis on `K` — a colimit of the slice polygraphs, one copy per chain, glued along the arrows
of `Ch K`. The slice family it consumes is **inherited from the base**
(`slicePolyFunctor p` / `slicePresentationOf p`), so `presentsChainsSliceColimit K p hp` is
parametric in a presentation `p` of `Ch(Z)[W⁻¹]` and `presentsChainsGarsideColimit` /
`presentsChainsArtinColimit` are that one lemma at two `p`s.

The route below is the record of the plan, not open work, and the plan changed twice while it ran:
the **generating-set** layer (`GlueOn.lean`, `presentsGlueOn`, `presentsChainsRunGlue`) was retired
in favour of a colimit over the whole elements category, and the **bead-product** layer
(`beadPresentation`, `slicePoly`, `cubeLocPresentation`) was retired in favour of inheritance from
the base. Both are marked below. The board (`bd ready`) is the status.

Context

This repository formalizes, in Lean 4 / Mathlib, a category Ch(K) attached to a (bipointed) precubical set K, together with a functor F : Ch(K) ⥤ Ch(Z) which is a discrete fibration (Ch(K) is the category of elements of a presheaf X on Ch(Z)). These proofs exist. Both categories carry a class of morphisms (the "inert" morphisms, call it W), with W_K = F⁻¹ W_Z. Localization uses Mathlib's CategoryTheory.Localization with MorphismProperty. This all exists in the repo.

## Ch(Z), its slices, the discrete fibration theorem for F.

Polygraphs already exists, and they are the main mechanism for doing presentations.
Ch(Z)[W_Z⁻¹] is understood in terms of PosBraid, using the garside presentation: each strand
component is one object with endomorphism monoid PosBraid N, and the Garside generators correspond
to the maps 1^n → [n]. The polygraph for it is assembled — `zLocPresentation`/`zLocArtinPresentation`
(`Concurrency/Presentation/BasePresentation.lean:60`, `:65`); that was Phase Z. We will want
other presentations as well, such as the artin one.

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

## Design constraints (read carefully)
- Generality. Phases A and B below must be stated for an arbitrary category D, presheaf X : Dᵒᵖ ⥤ Type, and MorphismProperty W_D, with C := ∫X (use Mathlib's category of elements, or the repo's discrete-fibration API if it is more convenient; do not duplicate). Ch(K), Ch(Z), braids and wedges appear only in Phase C/D.
- Pres means `Polygraph`, and a morphism of presentations means `Polygraph.Hom`. Both already exist in `Machinery/Presentation/Basic.lean`; do not build a second notion. `Polygraph` is a `Category` and `Hom.functor` is functorial, so `P : D ⥤ Polygraph` typechecks as written. Phrase "naturally in d" as a compatibility square, not by building `Polygraph ⥤ Cat`.
- No general colimits of presentations. Do not try to construct colimits in the category of presentations or use CategoryTheory.Limits for them. Glue is defined by explicit data, and its correctness is proved through the universal property of presented, as in item 3 above.
- Avoid colimits in Cat. Item 2 should be proved as the stated bijection of functors (via Localization.StrictUniversalPropertyFixedTarget / the universal property of MorphismProperty.Q), not by constructing a colimit cocone in Cat.
- Do not adjoin formal inverses. The point of the exercise is that Ch(K)[W⁻¹] is *smaller* than Ch(K); a presentation obtained by adding formal-inverse generators to a presentation of Ch(K) defeats the goal even though it is correct. The generators come from the braid side, through Ch(Z)[W⁻¹].
- Do not modify the existing Ch(Z), discrete-fibration, or braid-presentation theorems except to add exports/lemmas. If an existing definition genuinely obstructs the plan, stop and report rather than refactoring.
- Statements first. For each phase, write all theorem statements with sorry, get the file compiling, and only then fill proofs in dependency order. A compiling set of statements is a valid checkpoint to report at.
- Keep everything sorry-free at the end of each phase before moving on. Report precisely which statement blocked you and why if one does.

---

# Repo dictionary

Everything below was read off the source. **Read this instead of searching**, but grep the *name*:
the `file:line` numbers drift on every edit and a sixth of them already have. Anything marked
**ABSENT** genuinely does not exist — do not go looking for it.

## The two categories, and the fibration

| what | name | where |
|---|---|---|
| chains of `K` | `ChainCat.Obj K`, notation `Ch K` | `Precubical/Chains/Category.lean:23`, notation `:51` |
| an object | `⟨dims : List ℕ+, map : ⋁dims ⟶ K⟩` | `.../Category.lean:23` |
| a morphism | `⟨φ : ⋁a.dims ⟶ ⋁b.dims, w : φ ≫ b.map = a.map⟩` | `.../Category.lean:31` |
| the terminal `BPSet` | `CubeChains.Zbp`, `isTerminalZbp` | `Precubical/Basic/Terminal.lean:35`, `:56` |
| **F, the projection** | `ChainCat.toChZ (X : BPSet) : Ch X ⥤ Ch Zbp` | `Concurrency/Merge/MergeClass.lean:28` |
| **X, the presheaf** | `ChainCat.wedgeHoms K : (Ch Zbp)ᵒᵖ ⥤ Type` | `Concurrency/Presentation/ElementsFibration.lean:36` |
| … acts by precomposition | `wedgeHoms_map : (wedgeHoms K).map f.op m = f.φ ≫ m` | `.../ElementsFibration.lean:38` |
| the elements description | `toElements K : Ch K ⥤ ((wedgeHoms K).Elements)ᵒᵖ` | `.../ElementsFibration.lean:44` |
| … as an equivalence | `chEquivElements K : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ` | `.../ElementsFibration.lean:79` |
| … op'd | `chOpEquivElements K : (Ch K)ᵒᵖ ≌ (wedgeHoms K).Elements` | `.../ElementsFibration.lean:83` |
| shapes as chains of `Zbp` | `zObj (d : List ℕ+) : Ch Zbp`, `zHom` | `Concurrency/Merge/TotalMerge.lean:19`, `:24` |
| a morphism of `Ch Zbp` is a bare wedge map | `serialWedgeFullyFaithful` | `Concurrency/Merge/MergeClass.lean:46` |

**Op placement — the single biggest hazard.** `wedgeHoms K` carries its `ᵒᵖ` on the *source*
(a presheaf on `Ch Zbp`). `toElements`/`chEquivElements` carry it on the *whole* `Elements`
category, with `Ch K` bare on the left. `chOpEquivElements` moves it to the left instead. Inside
`toElements.obj` both `op`s are explicit: `op ⟨op (zObj a.dims), a.map⟩`. Net effect: `Ch K ⥤ Ch Zbp`
is a discrete **fibration** (slices *over* an object agree), even though mathlib's `Elements` is the
opfibration convention. Do not re-derive this; use the table.

`toElements K ⋙ (CategoryOfElements.π (wedgeHoms K)).leftOp = toChZ K` — **not `rfl`**, contrary to
what this line said until the instance was actually built.  The projection sends `a` to
`zObj a.dims`, whose map to `Zbp` is `isTerminalZbp.from (⋁a.dims)` on the nose; `toChZ` sends it to
`a.map ≫ isTerminalZbp.from K`.  Those agree only because `Zbp` is terminal, so the equation is
`Obj.eq_of_dims`, and it is `toElements_comp_π` (`ElementsFibration.lean`).  `Functor.ext`'s
morphism obligation there wants **`hom_ext' rfl`**: `simp` leaves `x.φ = eqToHom _ ≫ x.φ ≫ eqToHom _`
whose `eqToHom`s are identities definitionally but not at `simp`'s reducible transparency, so
`simp only [eqToHom_refl, …]` reports *no progress*.  The instance
`(toChZ K).IsDiscreteFibration` is that equation transported.

**ABSENT in mathlib:** any discrete-fibration predicate. `CategoryTheory/FiberedCategory/` has
`Functor.IsPreFibered`/`IsFibered` only, and this repo does not import it.

## Discrete fibrations (`Machinery/Slice.lean`)

| what | name | where |
|---|---|---|
| the predicate | `Functor.IsDiscreteFibration F`: `Over.post F : Over c ⥤ Over (F.obj c)` is an equivalence for every `c` | `Machinery/Slice.lean:28` |
| closure | equivalences are; composites are; `IsDiscreteFibration.of_natIso` | `.../Slice.lean:43` |
| `W` on the two slices | `MorphismProperty.over_inverseImage : (W.inverseImage F).over = W.over.inverseImage (Over.post F)` — `rfl`, no hypothesis on `F` | `.../Slice.lean:61` |
| **the example** | `CategoryOfElements.π_leftOp_isDiscreteFibration : ((π X).leftOp).IsDiscreteFibration` for `X : Cᵒᵖ ⥤ Type w` | `.../Slice.lean:69` |

`Slice.lean` is the one place the `op`-juggling lives.  Its client is `toElements_comp_π`
(`ElementsFibration.lean`), which makes `toChZ K` a discrete fibration for **every** `K`, so A2
applies to the slices of `Ch K` and `locOverEquivBase` follows.  `Glue.lean` does *not* use
it: it works concretely with `(π X).leftOp` and `elementsLiftOver` rather than taking
`IsDiscreteFibration` as a hypothesis.

## The localized slices (`Machinery/Localization/SliceLocalize.lean`)

| what | name | where |
|---|---|---|
| localization pulls back along an equivalence | `Functor.IsLocalization.of_inverseImage (G) [G.IsEquivalence] (L) (V) [V.RespectsIso] [L.IsLocalization V] (U) (hU : U = V.inverseImage G) : (G ⋙ L).IsLocalization U` | `SliceLocalize.lean:27` |
| postcomposition, localized | `overMapLoc W u` — a `Construction.lift`, hence **strict**: `overMapLocFac`, `overMapLoc_id`, `overMapLoc_comp` are equalities | `.../SliceLocalize.lean:56`, `:63`, `:72`, `:75` |
| `W.over` respects isos | `respectsIso_over`; at the base, `(W Zbp).RespectsIso` is `respectsIso_W` (`Merge/MergeGenerate.lean:180`) and needs no discharging | `.../SliceLocalize.lean:43` |
| any localization below is one above | `isLocalization_post_comp` | `.../SliceLocalize.lean:91` |
| **A2, the slices agree** | `sliceLocEquiv F W c : ((W.inverseImage F).over c)ᴸ ≌ (W.over (F.obj c))ᴸ` | `.../SliceLocalize.lean:101` |

**A2 is existence only, and that is the whole lesson of it.** It was deleted once as unconsumed and
restored when the slices of `Ch K` needed it, so: `sliceLocEquiv` is `Localization.uniq`, which is
**opaque on objects**. `Presents.ofDesc` takes a *prefunctor*, so anything that has to interpret
cells needs a comparison strict on objects, and A2 is not one — `elementsLift` (`Glue.lean:245`)
writes that inverse down instead. Use A2 to know the categories agree; never to compute in them.
Its naturality in the base (A2b, the `Over.map`/`Over.post` square) and the `Lifting` instances
around it were never restored, and nothing needs them.


## Slice cocones (`Machinery/Localization/SliceFamily.lean`)

No hypothesis on `W` at all — not even `ContainsIdentities`.

| what | name | where |
|---|---|---|
| a compatible family | `OverCocone C E`: `obj c : Over c ⥤ E`, `w u : Over.map u ⋙ obj c = obj c'` | `SliceFamily.lean:24` |
| its two directions | `OverCocone.ofFunctor Φ` (`Over.forget c ⋙ Φ`), `OverCocone.desc` (read at `Over.mk (𝟙 c)`) | `.../SliceFamily.lean:36`, `:58` |
| **unlocalized** | `overCoconeEquiv : (C ⥤ E) ≃ OverCocone C E` | `.../SliceFamily.lean:113` |
| a strict universal property is a bijection | `Localization.StrictUniversalPropertyFixedTarget.functorEquiv : (D ⥤ E) ≃ {F : C ⥤ E // W.IsInvertedBy F}` | `.../SliceFamily.lean:235` |
| a localized family | `OverCoconeLoc W E`: `obj c : (W.over c).Localization ⥤ E`, `w u : overMapLoc W u ⋙ obj c = obj c'` | `.../SliceFamily.lean:249` |
| the two halves | `isInvertedBy_iff_over`, `coconeLocEquiv` | `.../SliceFamily.lean:263`, `:272` |
| **A3** | `overCoconeLocEquiv W : (W.Localization ⥤ E) ≃ OverCoconeLoc W E` | `.../SliceFamily.lean:407` |
| … its characterisation | `overCoconeLocEquiv_apply`, `overCoconeLocEquiv_symm_apply`: `(W.over c).Q ⋙ G.obj c = Over.forget c ⋙ W.Q ⋙ Φ` | `.../SliceFamily.lean:412`, `:417` |

## The glued polygraph (`Machinery/Presentation/Glue.lean`)

The glued polygraph **is** `Limits.colimit (elementsPoly X P)` — no bespoke `V`/`Gen`/`rel`, no
label structure, no copy-inclusion soundness lemma.  `elementsPoly X P = (π X).leftOp ⋙ P` is the
slice diagram, `Polygraph` has every colimit (`Coequalizer.lean`, `ColimitCells.lean`), and the
universal property on *presented* categories comes straight from `catHomEquiv`.

| what | name |
|---|---|
| the base of a copy, and the diagram | `eltBase X c = (π X).leftOp.obj c`, `elementsPoly X P` |
| the copy inclusion, on presented categories | `glueInclFun X P c`, `glueInclFun_naturality` |
| **the universal property** | `glueLift` (a compatible family of functors out of the copies), `glueInclFun_lift`, `glue_functor_ext` |
| **the cartesian lift** | `elementsLift X d x : Over d ⥤ (X.Elements)ᵒᵖ` with `elementsLift_comp_π` (`rfl`), `elementsLift_post` (a strict **equality**, from `elements_snd_map`), and `elementsLift_inverts` |
| … on slices | `elementsLiftOver X c : Over (F c) ⥤ Over c`, the strict inverse of `Over.post F`: `elementsLiftOver_forget`, `elementsLiftOver_post`, both `rfl` |
| … localized | `glueSliceEval X W d x`, `glueSliceEval_fac` |
| **the lift is functorial in the base** | `elementsLift_over_map : Over.map f ⋙ elementsLift X d x = elementsLift X d' (X.map f.op x)`, and localized `overMapLoc_comp_glueSliceEval` |
| `overMapLoc` on objects | `overMapLoc_obj` |
| **the one hypothesis** | `SliceSkeleton W p` — a single field `entry`: exactly one 0-cell of `P d` names an object isomorphic to each `y : Over d`.  `ret`, `iso`, `eq_ret`, `fix`, `at_injective`, `presented_isThin` and `ret_push` all derive from it |
| **inverting a slice presentation** | `slInv`, `comp_slInv` (an **equality**), `slInv_square` — `hP` inverted, where a mere equivalence would give a mate — and `slInvIso` for the other side |
| **Φ** | `glueLeg`, `glueLeg_naturality`, `glueDesc` |
| **a copy, read by Φ** | `glueIncl_desc : glueInclFun X P c ⋙ glueDesc = (p (eltBase X c)).E ⋙ glueSliceEval X W (eltBase X c) c.unop.2` — the bridge every spelling argument runs through |
| **the retraction Ψ** | `glueRetractPre`, `glueStep`, `glueRetractPre_inverts`, `glueRetractCocone`, `glueRetract` (a `Construction.lift`) with `glueRetract_fac`, `glueRetract_forget` |
| **η**, and faithfulness | `glueSliceEval_retract` (the mirror of `glueIncl_desc`), `glueUnit : glueDesc ⋙ glueRetract = 𝟭` on the nose, `glueDesc_faithful` |
| **ε** | `slInvComp_square`, `slInvArrow`, `slInvArrow_square`, `glueCounitStep`, `glueCounitCocone`, `glueCounit` — only an *isomorphism*, assembled slice by slice through `OverPseudoCocone.descIso` |
| **`colimit (elementsPoly X P)` presents `(∫X)[W⁻¹]`** | `presentsSliceColimit X W p hP hthin R` |
| … read on the colimit of the localized slices | `overLocFunctor`, `overLocCocone`, `isColimitOverLocCocone`, `presentsColimitOfLocalizedSlices`, `colimitPresentedEquivColimitLoc` (`SliceColimit.lean`) |
| **the skeleton hypothesis is sufficient, not necessary** | `presentsGlue₂` (`GlueRefutation.lean`): `P₂` has two 0-cells where the localized slice has one object, so `SliceSkeleton.at_injective` fails — and the colimit still presents, because `∫X₂` is a point.  The moral is that the colimit's 0-cells are the *copies'*, never their image in `∫X`: a construction that flattened them onto `∫X` would identify the two here and invent a loop |

**The word problem is a retraction, not a normal form.** The target is not thin, so there is nothing
to rewrite words *to*: `Ψ` is an honest cocone on the slices and `Φ ⋙ Ψ = 𝟭` is an equality checked
on generators.  The counit is genuinely only an isomorphism — a localized slice is thin but never
skeletal, since a `W`-arrow makes distinct objects isomorphic.

**State each step as an equality of *functors*, then descend once.** Functor equations have no
implicit object arguments, so `rw` works on them normally; the landmine below only bites once the
objects are pinned.  Attempting the same proofs morphism-first does not work at all: `rw` *and*
`simp only` both fail to fire on a `Functor.map`-headed pattern that is printed verbatim in the goal.

**Landmine: `rw`/`simp` cannot apply `Category.assoc` in `W.Localization`.** When a composite's
middle object is spelled two ways, the two are defeq but `kabstract`'s keyed matching runs at
`instances` transparency and fails.  `simp only [Category.assoc]` then makes *no progress* and
reports no unused-argument warning, which reads like the lemma fired.  Marking the offending def
`@[reducible]` does **not** help: the mismatch is in the `≫`'s implicit *object* argument, not in a
head symbol.  The cure is term mode, which elaborates at default transparency; `eqToHom_conj_id`
(`SliceFamily.lean`) is the one sandwich combinator that survived the rewrite, for crusts that are
identities *up to defeq*, which `eqToHom_refl` cannot see.

**A definition built inside a tactic block can be correct and useless.** `Localization.Lifting`
witnesses supplied as `letI` inside a `by` block make the definition's components unnameable from
outside, so `Localization.liftNatTrans_app` cannot be applied to it *at all* — and the symptom is the
familiar one, a lemma that visibly ought to apply refusing to. This is **not** the transparency
hazard above; the cause and the cure are unrelated. The cure is to hoist the witnesses to `instance`s
and write the definition in term mode. Prefer term mode for any definition whose components later
proofs will need to compute with.

**The overlap identifications are sound because the cartesian lift is functorial in the base.**
`elementsLift_over_map` is the whole content: lifting at `x` after postcomposing with `f` is
lifting at `f* x`. Both it and its localized form are *equalities* of functors, so the colimit's own
`colimit.w` carries them with no transport argument.

**`sliceLocEquiv` (A2) cannot be used to interpret the cells.** The comparison has to be strict on
objects; `sliceLocEquiv` is an abstract `IsEquivalence` built from `Localization.uniq`, and its
inverse computes nothing. `elementsLift` writes that inverse down instead — it is a genuine functor,
`elementsLift ⋙ π.leftOp = Over.forget d` holds by `rfl`, and `glueSliceEval` is its
`Construction.lift`. That left A2 with nothing to do at all, which is why it has been deleted:
`elementsLift_inverts` supplies the *is-a-localization* half directly.

## Copies over a generating set — **retired** (`Machinery/Presentation/GlueOn.lean`)

A5 built the copies over a *generating set* `S` of `∫X`, with overlap 2-cells indexed by spans, on
the hypothesis `Generating X S : ∀ c, ∃ s ∈ S, Nonempty (c ⟶ elt X s)`.  It worked and it is gone:
`presentsSliceColimit` puts a copy over **every** object instead, and then the overlaps are the
arrows of `∫X` and the colimit's own naturality supplies them, so the generating set, the base
0-cell `glueOnBase` and its copy-independence, and the span bookkeeping all disappear.  Nothing in
the tree carries `GlueOn`, `glueOn`, `presentsGlueOn`, `Generating` or `SliceRetract` any more; do
not go looking for them.

Two autopsies worth keeping.  **`CoversUpToW` was tried and is wrong**: choosing a covering
`W`-arrow per object by `Classical.choice` fails at the `Q.map f` obligation, which has to put both
endpoints *and* the arrow into a single slice — two objects can be covered out of different copies,
and then nothing compares them.  And **the copies could not sit at every 0-cell in A4's sense**:
that route needed `(p d).E` bijective on objects, which fails because objects of
`((W Zbp).over (zObj d))ᴸ` are all of `Over (zObj d)` on the nose (`Construction.objEquiv`) while a
slice polygraph has one 0-cell per *iso-class*.  `Presents.restrict` cannot repair it either —
`Convex.respectsIso` (`Machinery/Presentation/Partial.lean`) shows a convex property is closed
under isomorphism, so it can never cut a category down to a skeleton.  What the colimit route does
instead is ask for the skeleton directly, as a single field: `SliceSkeleton.entry`.

## Strictness (A3b)

**Which cocone.** Reach for `OverCocone` when the compatibility really is an equality — that is the
stronger statement and a genuine `Equiv`. Reach for `OverPseudoCocone` when the legs come from
**inverting an equivalence**: `Functor.inv` is a choice, so such a family is compatible only up to
iso, and `Functor.ext` cannot repair it (a `Presents` gives an essentially surjective comparison,
not a bijective-on-objects one).

The colimit route needs the strict one: `hP` is an *equality* of functors, and `Ψ` is an honest
cocone on the slices (`glueRetract`) with `Φ ⋙ Ψ = 𝟭` on the nose (`glueUnit`), so
`glueRetractCocone` is a plain `OverCocone`. The pseudo layer survives for the counit, which is
genuinely only an isomorphism — a localized slice is thin but never skeletal — assembled slice by
slice through `OverPseudoCocone.descIso`.

| what | name | where |
|---|---|---|
| unlocalized | `OverPseudoCocone` (`obj`, `iso`, `iso_id`, `iso_comp`), `.desc` | `SliceFamily.lean:129`, `:147` |
| localized | `OverPseudoCoconeLoc`, `toPseudoCocone`, `descLoc`, `descLoc_fac` (**strict**) | `.../SliceFamily.lean:292`, `:314`, `:339`, `:342` |
| **descending is functorial** | `OverPseudoCocone.descMap`, `.descIso`, `OverPseudoCoconeLoc.descLocIso`: leg isos commuting with the comparison isos descend to an iso of the descended functors | `.../SliceFamily.lean:190`, `:213`, `:356` |
| `desc` on morphisms | `OverPseudoCocone.desc_map` (`rfl`), mirroring `OverCocone.desc_map` | `.../SliceFamily.lean:181` |
| reading a cocone through a functor | `OverPseudoCoconeLoc.postcomp`, `descLoc_postcomp` (**strict**) | `.../SliceFamily.lean:382`, `:389` |
| a functor as a cocone, so `𝟭` is a `descLoc` | `OverCoconeLoc.toPseudo`, `OverPseudoCoconeLoc.ofFunctor`, `descLoc_ofFunctor` (**strict**) | `.../SliceFamily.lean:399`, `:423`, `:427` |
| **a functor is determined by its slices** | `OverCocone.functor_ext` — the injectivity half of `overCoconeEquiv`, read on functors | `.../SliceFamily.lean:92` |
| **a fully faithful functor bijective on objects is invertible** | `strictInv`, with `comp_strictInv` and `strictInv_comp` both **equalities**; `comp_right_injective` cancels it, and `strictInv_square` inverts a commuting square to a commuting square, where a mere equivalence would give a mate | `Machinery/StrictInverse.lean:20`, `:29`, `:34`, `:41`, `:49` |
| a transformation at two spellings of one object | `natTrans_app_congr` | `Machinery/Slice.lean:55` |

The coherences are plain `eqToIso`s of `Over.mapId_eq`/`Over.mapComp_eq` and
`overMapLoc_id`/`overMapLoc_comp` — **not** isos of isos — because all four are strict equalities.

**Why a bijection and not an equivalence of categories.** `Over.map` is strictly functorial
(`Over.mapId_eq`, `Over.mapComp_eq`) and `overMapLoc` inherits that from `Construction.lift`, so
the compatibility is an *equality* of functors and both round trips are equalities. The only
`eqToHom` in the file is inside `OverCocone.desc`, where `(Over.map u).obj (Over.mk (𝟙 c'))` is
`Over.mk (𝟙 c' ≫ u)` rather than `Over.mk u`.

## The class W

| what | name | where |
|---|---|---|
| a single bead merge | `ChainCat.merge (X : BPSet) : MorphismProperty (Ch X)` | `Concurrency/Merge/MergeClass.lean:61` |
| the class | `ChainCat.W (X : BPSet) : MorphismProperty (Ch X)` = `(merge X).multiplicativeClosure` | `.../MergeClass.lean:71` |
| multiplicative | `instance : (W X).IsMultiplicative` | `.../MergeClass.lean:73` |
| **W_K = F⁻¹W_Z is a THEOREM** | `W_eq_inverseImage_toChZ (X) : W X = (W Zbp).inverseImage (toChZ X)` | `Concurrency/Merge/MergeGenerate.lean:157` |
| … on the elements side | `W_eq_inverseImage_toElements` | `.../ElementsFibration.lean:101` |
| combinatorial test | `W_iff_crossPerm_eq_one (h) (f) : W K f ↔ crossPerm h f = 1` | `.../MergeGenerate.lean:100` |
| merges = codim-1 W-maps | `merge_iff (f) : merge K f ↔ W K f ∧ codim f = 1` | `.../MergeGenerate.lean:161` |
| **W-arrows are unique** | `eq_of_W : W K f → W K g → f = g` | `Concurrency/Grading/TopBead.lean:26` |

## Collapse of the localized base — why the slices are small

| what | name | where |
|---|---|---|
| the coarsest shape on `n` events | `ChainCat.topDims n : List ℕ+` (`= [n]` for `n>0`) | `Concurrency/Grading/TopBead.lean:32` |
| every shape merges to the top | `exists_W_to_top` | `.../TopBead.lean:60` |
| **every shape is merged onto by the run** | `exists_W_from_ones (b) (h : dimSum b = N) : ∃ u : zObj (𝟙^N) ⟶ zObj b, W Zbp u` | `.../TopBead.lean:76` |
| runs of the `n`-cube are `Sₙ` | `onesTopEquiv n : (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Perm (Fin n)` | `.../TopBead.lean:98` |
| homs exist iff coarser | `nonempty_hom_iff : Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ boundaries b.dims ⊆ boundaries a.dims` | `Concurrency/Grading/ChartHom.lean:499` |

**Arrows in `Ch Zbp` run finer ⟶ coarser.** `Over d` is therefore the category of *refinements* of
`d`, and a refinement of a concatenation respects the junction — which is what makes B3 true.

`exists_W_from_ones` is the fact that makes the *slice* collapse: the W-arrow `1ⁿ ⟶ c` it produces
is automatically a triangle over any `u : c ⟶ d`, so every object of `Ch(Z)/[n]` is W-isomorphic to
one of the form `(1ⁿ, σ)` with `σ : 1ⁿ ⟶ [n]`, i.e. to a run. No `IsSegal` hypothesis is involved
anywhere in this argument.

## The localized base

| what | name | where |
|---|---|---|
| objects at a strand count | `AtStrands (N : ℕ) : ObjectProperty ((W Zbp).op.Localization)` | `Concurrency/Presentation/BaseComponent.lean:59` |
| the run object | `runBase N : (SingleObj (PosBraid N))ᵒᵖ ⥤ (W Zbp).op.Localization` | `.../BaseComponent.lean:19` |
| **each component is one object** | `strandComponentGarside N : (SingleObj (PosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory` | `.../BaseComponent.lean:85` |
| … Artin spelling | `strandComponentArtin N` | `.../BaseComponent.lean:92` |
| **no homs across strand counts** | `isEmpty_loc_hom (h : dimSum a.dims ≠ dimSum b.dims)` | `Concurrency/Presentation/Retraction.lean:97` |
| every hom is a positive braid | `homEquivPosBraid`, `_comp`, `_id`, `_Q` | `.../Retraction.lean:324`, `:338`, `:351`, `:358` |
| loops at the run | `RunLoops N`, `runBraidEquiv N : PosBraid N ≃* RunLoops N` | `.../Retraction.lean:103`, `:297` |
| **the base is the disjoint union** | `strandDecomposition : (W Zbp).op.Localization ≌ Σ N : ℕ, (AtStrands N).FullSubcategory` | `Concurrency/Presentation/BaseDecomposition.lean:32` |
| … its two inputs | `exists_atStrands`, `atStrands_eq_of_hom` | `.../BaseDecomposition.lean:17`, `:24` |
| … the general fact it instantiates | `ObjectProperty.sigmaEquiv` (a hom-disjoint cover splits a category) | `Machinery/SigmaComponents.lean:52` |

The polygraph over those components is `zLocPresentation`, in the next table.

## Presentations that exist

| what | name | where |
|---|---|---|
| the cut polygraph | `ChainCat.Cut.poly : Polygraph` | `Concurrency/Presentation/CutPresentation.lean:101` |
| **`Ch Zbp` presented (UNLOCALIZED)** | `zCutPresentation : Presents Cut.poly ((Ch Zbp)ᵒᵖ)` | `.../CutPresentation.lean:201` |
| lifted to `Ch K` | `chPresentation`, `chCutPoly`, `chCutPresentation` | `Concurrency/Presentation/LiftPresentation.lean:37`, `:48`, `:52` |
| the Garside germ, presented | `germPresentation n : Presents (monoidPoly (PosGermRel n)) ((SingleObj (PosBraid n))ᵒᵖ)` | `Concurrency/Presentation/BasePresentation.lean:26` |
| … Artin spelling | `artinPresentation n` | `.../BasePresentation.lean:30` |
| **`Ch Zbp[W⁻¹]` presented** | `zLocPresentation : Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N)) ((W Zbp).op.Localization)` | `.../BasePresentation.lean:60` |
| … Artin spelling | `zLocArtinPresentation` (same, with `ArtinRel`) | `.../BasePresentation.lean:65` |
| … the assembly both go through | `zLocOfComponents (p : ∀ N, Presents (P N) ((AtStrands N).FullSubcategory))` | `.../BasePresentation.lean:41` |
| a presented monoid presents `SingleObj` | `presentedMonoidPresentation`, `monoidPoly` | `Machinery/Presentation/Monoid.lean` |
| the Segal/descent route (needs `IsSegal`) | `chLocPoly`, `chLocPresentation`, `hLocPoly`, `hLocPresentation`, `hLocActionPresentation` | `.../HAction.lean:64`, `:72`, `:293`, `:298`, `:314` |

`hLocActionPresentation n : Presents (hLocPoly n) ((PosBraidAction n)ᵒᵖ)` is about `Hbp □n`, the
**decorated** cube, and is **not** the shape the slice presentations take. `Ch(□n)[W⁻¹]` is *not*
equivalent to `PosBraidAction n`: at `n = 2` both have two objects, but `End` in `PosBraidAction 2`
is `PosPureBraid 2` (`endEquivPosPure`, `Machinery/Braid/PosAction.lean:43`), which contains `σ₁² ≠ 1`,
while `Ch(□²)[W⁻¹]` has trivial endomorphisms — its three objects are `t = ([2], 𝟙)`,
`r₁ = ([1,1], cubeMerge)` and `r₂ = ([1,1], cubeReorder)`, with `r₁ ⟶ t` and `r₂ ⟶ t` and nothing
else, so inverting the one merge `r₁ ⟶ t` adds `t ⟶ r₁` and creates no loop. Nothing maps *into*
`r₁` or `r₂`.

Nor is the descent shape available: `Ch(□n)[W⁻¹] = ∫` of a `PosBraid n`-set, compatibly with the
projection, requires `wedgeHoms (□n)` to invert merges, and at `n = 2` that map sends one element
to two. Consistently, `not_isSegal_cube_two` (`Concurrency/Merge/SegalCondition.lean:499`) proves
`□²` is not Segal. Do not route Phase C through `IsSegal`, `Hbp` or `chDescent`.

**`Ch(□n)[W⁻¹]` is thin, and it is the weak order.** `locCube_isThin`
(`Concurrency/Merge/CubeThin.lean:494`) says the localization is a poset, and `locCubeWeakOrder n :
(W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ` (`Concurrency/Merge/CubeWeakEquiv.lean:45`) names which
poset: the right weak (Bruhat) order on `Perm (Fin n)`, read backwards. A hom exists exactly when
the two chains' crossing permutations compare, and is then unique (`nonempty_loc_hom_iff`,
`.../CubeWeakEquiv.lean:50`).

Thinness is not automatic, and the worry that makes the opposite guess tempting is real:
localization does not preserve thinness in general, because a zigzag `c → x ← y → …` is a new
morphism. What kills the zigzags here is `crossLen`. It drops by `permLen (crossPerm f)` along `f`
(`crossLen_eq_add`, `Concurrency/Merge/CubeCrossing.lean:66`) and is preserved by `W`, so in any
loop every forward arrow lies in `W`: **every endomorphism of `Ch(□n)[W⁻¹]` is a zigzag of
merges.** That much the grading gives alone, and it is where this project locates the braiding —
but π₁ of the merge order turns out to be *trivial*, which is the content of `CubeThin.lean`. Every
chain is entered from its class's run by a merge (`classRunIso`, `:115`), so a morphism is read
between runs (`conjRun`, `:123`), where a merge becomes the identity and a refinement becomes the
fraction its target names (`conjRun_map_eq`, `:166`); hence every morphism is a word in the atom
steps (`exists_word_of_hom`, `:326`), and `word_unique` (`:434`) — an induction on `permLen`, a
shared first cut reducing and distinct cuts closing by the codimension-two diamond
`hasDiamonds_cube` (`Concurrency/Merge/CubeFaces.lean:981`) — says two words with the same
endpoints agree.

**`n = 2` is therefore not the degenerate case it looks like**, and may be extrapolated from.
`WeakOrder 2` is the two-element chain, and the computation above *is* `(WeakOrder 2)ᵒᵖ`: inverting
the one merge makes `r₁ ≅ t`, leaving `[r₂] ⟶ [t]` and nothing else. What is special at `n = 2` is
only that no atom composes with another.

The consequence for Phase C is that a cube slice presentation carries no word problem at all:
`Presents.ofThin` (`Machinery/Presentation/Basic.lean`) presents a thin category from a spanning
family of generators on a covering family of 0-cells and nothing else, and `cubePresentation n`
(`Concurrency/Presentation/CubePresentation.lean:66`) is that — 0-cells the runs, generators the
atom steps, one per descent.

## The polygraph machinery (`Machinery/Presentation/`)

`Polygraph` (`Basic.lean:75`) is `V`, `Gen : V → V → Type`, `rel : HomRel (Paths (GenObj Gen))`;
`presented := Quotient rel`; `Word := Paths (GenObj Gen)`; `quot`. `Polygraph.Hom P Q` sends a
1-cell to a *word* of `Q`, `Polygraph` is a `Category` (**homogeneous** in the two universes, so a
morphism into something a universe up must be spelled `Hom`, not `⟶`), and
`Hom.functor`/`functor_id`/`functor_comp` give functoriality of `presented`. `Hom.ofPre`
(`Basic.lean:141`) builds a morphism from a map of generating quivers that kills the 2-cells — every
morphism below is built that way. `Polygraph.comap` reads `P`'s 2-cells on a quiver over `P`'s;
`comapIncl`, `comapHom`, `comapIncl_faithful`, `comapIncl_full` (`Basic.lean:235`, star-surjective +
0-cells injective), `quot_mapPath_congr` (`Basic.lean:351`, `Hom.ofPre`'s hypothesis upgraded from
`rel` to the congruence it generates) support it.
`Presents P C` (`Basic.lean:369`) is `E : P.presented ⥤ C` plus `E.IsEquivalence`; `ofDesc`
(`Basic.lean:462`) is the constructor; `transport` composes with an equivalence;
`eval`/`at'`/`arrow`/`evalPre`/`sound`/`eval_map_eq_lift`/`eval_mapPath`/`lift_evalPre_comp`
(`Basic.lean:386`, a copy of `P` interpreted through a functor) are the accessors, and
`Polygraph.lift_map_eq_of_quot_eq` (`Basic.lean:455`) is `sound`'s converse: two words with the
same interpretation are already equal in the quotient. It is **not** a normal-form device — the
word problem here is discharged by a retraction (`presentsSliceColimit` builds `Ψ` with
`Φ ⋙ Ψ = 𝟭`), because the target is not thin and there is no normal form to carry. `Presents.elements`
(`Elements.lean:241`) presents `∫F`.
`Polygraph.coproduct` (`Coproduct.lean:45`) is the coproduct and `Presents.coproduct`
(`Coproduct.lean:152`) presents `Σ i, C i`; `coproductPre i`, `coproductIncl i` (the injection),
`coproduct_exists_mapPath` are its API. Its 1-cells are the **indexed inductive** `CoproductGen`,
not a `Σ'`-transport, so `Gen` lands in `Type (max t u' w)` — a universe bump the callers have to
carry (nil for a `ℕ`-indexed family of `Type 0` polygraphs). Nothing here is named `sigma`:
mathlib's `Sigma` is the *category* side, and `Σ i, (P i).V` is only how the 0-cells happen to be
spelled.
`Polygraph.prod` (`Product.lean:66`) and `Presents.prod` (`Product.lean:253`) are B2, with 1-cells
the indexed inductive `ProdGen` (one factor's, the other coordinate frozen) and 2-cells
`ProdRel.left`/`.right`/**`.interchange`**; `exists_normalForm` (`Product.lean:126`) — every word is
a `P`-word then a `Q`-word — is what interchange buys and the whole of completeness.
**A bare `Quiver.Path` does not say which category its `≫` is in**, and `(prod P Q).Gen` and
`ProdGen P Q` are two defeq spellings of one thing, so a `Functor.map_comp` pins the middle 0-cell
to one of them and nothing matches afterwards. `Product.lean` keeps whole words inside one
`quot.map` and moves through `quot_comp_congr` (`:93`), whose 0-cells are variables; `prodLeft` and
`prodRight` are `abbrev` so the two spellings unify at `rw`'s transparency. Expect the same in any
further polygraph construction.
`Presents.restrict`, `partialElements` and `partialActionFunctor` are in `Partial.lean`.

## Slices

`Machinery/Slice.lean` (above) is the only slice-theoretic file. **ABSENT elsewhere:** `Under`,
`Comma`, `CostructuredArrow` — zero occurrences. (`StructuredArrow` appears on six lines, all
inside Kan-extension proofs, none slice-theoretic.)

| what | name | where |
|---|---|---|
| **`Ch(Z)/d` is `Ch (⋁d)`** | `overToWedgeChains d : Over (zObj d) ⥤ Ch (⋁d)`, fully faithful and bijective on objects | `Concurrency/Merge/WedgeSlice.lean:21` |
| … as an equivalence | `overEquivWedgeChains d : Over (zObj d) ≌ Ch (⋁d)` | `.../WedgeSlice.lean:53` |
| … and it carries `W/d` to `W` | `over_W_eq_inverseImage : (W Zbp).over = (W ⋁d).inverseImage (overToWedgeChains d)` | `.../WedgeSlice.lean:58` |
| **`Ch (X ∨ Y) ≌ Ch X × Ch Y`** | `chConcatEquiv (h : (X ∨ Y).AdmitsAltitude)`, from `chConcat_full` + `chConcat_essSurj` (`Faithful` was already there, `Segal.lean:582`) | `Concurrency/Merge/WedgeSplit.lean:57`, `:31`, `:52` |
| … hypothesis-free for serial wedges | `serialChConcatEquiv (d e : List ℕ+)` | `.../WedgeSplit.lean:64` |
| **`W` splits with it** | `W_prod_eq_inverseImage_chConcat : (W X).prod (W Y) = (W (X ∨ Y)).inverseImage (chConcat X Y)`, from `W_chConcat_iff` | `.../WedgeSplit.lean:79`, `:72` |
| … the arithmetic under it | `permSum_eq_one_iff` | `Machinery/Braid/Sum.lean:57` |

`chConcat_full` is the one new piece of mathematics: `splitTarget` (`Degree.lean:145`, itself
hypothesis-free) splits the *source* of a wedge map wherever the target splits, and `splitObj` says
a chain of `X ∨ Y` splits in only one way, so the two splittings agree and the map is a
concatenation. `AdmitsAltitude` enters only through `splitObj`.

### Localized (B4) — `Concurrency/Merge/WedgeLocalize.lean`

| what | name | where |
|---|---|---|
| **the engine** | `isLocalization_chConcat : (chConcat X Y ⋙ Q).IsLocalization ((W X).prod (W Y))` | `:30` |
| … as an equivalence | `locChConcatEquiv (h) : (W X)ᴸ × (W Y)ᴸ ≌ (W (X ∨ Y))ᴸ` | `:38` |
| **the cons step** | `locChConsEquiv n rest : (W □n)ᴸ × (W ⋁rest)ᴸ ≌ (W ⋁(n :: rest))ᴸ` — hypothesis-free | `:48` |
| the slice reading | `isLocalization_overToWedgeChains`, `locOverEquivWedge d : ((W Zbp).over)ᴸ ≌ (W ⋁d)ᴸ` | `:57`, `:62` |

Older orientation, still useful:
- `chartHomEquiv (χ : ⋁b ⟶ □N) : (⋁a ⟶ ⋁b) ≃ {x : ⋁a ⟶ □N // Nonempty (⟨a,x⟩ ⟶ ⟨b,χ⟩)}` — `Concurrency/Grading/ChartHom.lean:53`
- `Coarser d d' := dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d` — `.../ChartHom.lean:335`
- `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` — `Precubical/Segal/Segal.lean:512`; `splitObj (h : (X ∨ Y).AdmitsAltitude) : Ch (X ∨ Y) ≃ Ch X × Ch Y` — `Split.lean:525`, with `chConcat_obj_splitObj` `:528`, `splitObj_chConcat_obj` `:534`
- `splitWedgeMorphism` — `Split.lean:542`; `splitTarget`, `splitAt` — `Concurrency/Grading/Degree.lean:145`, `:158`

In particular `Ch(Z)/[n] ≅ Ch(□n)`. That coincidence is a description, not a tool: `□n` is not
Segal, so the descent machinery neither applies nor is needed.

## Acyclicity, for the generating-set argument

| what | name | where |
|---|---|---|
| every endomorphism is the identity, **every K** | `ChainCat.endo_eq_id` | `Precubical/Chains/ChainSkeletal.lean:106` |
| bead count never increases | `ChainCat.dims_length_le_of_hom` | `.../ChainSkeletal.lean:113` |
| **a non-iso strictly drops the bead count** | `ChainCat.lt_dims_length_of_not_isIso` | `.../ChainSkeletal.lean:161` |
| `Ch K` is skeletal | `ChainCat.eq_of_hom_hom`, `le_antisymm` | `.../ChainSkeletal.lean:144`, `:153` |
| the grading | `codim`, `codim_comp`, `codim_eq_zero_iff`, `codim_eq_length_sub` | `Concurrency/Grading/Degree.lean:46`, `:76`, `:130`, `:58` |
| factorisation engine (`Ch Zbp` only) | `factor_ext`, `exists_factor`, `exists_first`, `exists_diamond` | `Concurrency/Grading/Coarser.lean:364`, `:388`, `:447`, `:456` |

| **maximal chains, and that coarsening terminates** | `ChainCat.MaximalChains K : Set (Ch K)` (no non-identity outgoing arrow) and `ChainCat.exists_hom_maximal c : ∃ s ∈ MaximalChains K, Nonempty (c ⟶ s)` — induction on bead count, no finiteness and no acyclicity hypothesis | `.../ChainSkeletal.lean:173`, `:179` |
| **nothing coarsens onto a run** | `CubeChains.eq_of_hom_isRun (f : a ⟶ b) (hb : IsRun K b) : a = b` — a run's bead count already equals its `dimSum`, which no arrow changes | `Concurrency/Executions/Runs.lean:84` |

## Mathlib pieces that do the work for us

| what | name | where |
|---|---|---|
| slices | `Over`, `Over.forget`, `Over.map f` (postcomposition), `Over.post F : Over X ⥤ Over (F.obj X)` (`post_comp` is `rfl`) | `CategoryTheory/Comma/Over/Basic.lean:176`, `:197`, `:405` |
| `W` on a slice | `MorphismProperty.over W {X} : MorphismProperty (Over X)` | `CategoryTheory/MorphismProperty/Comma.lean:104` |
| `F⁻¹W` | `MorphismProperty.inverseImage` | `CategoryTheory/MorphismProperty/Basic.lean:122` |
| **B1, for free** | `Functor.IsLocalization.prod` — `(L₁.prod L₂).IsLocalization (W₁.prod W₂)`, needs `ContainsIdentities` | `CategoryTheory/Localization/Prod.lean:139` |
| localization uniqueness | `Localization.uniq L₁ L₂ W : D₁ ≌ D₂`, `compUniqFunctor`, `liftNatIso`, `Localization.lift`/`fac` | `CategoryTheory/Localization/Predicate.lean:434`, `:443`, `:353`, `:299`, `:307` |
| universal property | `StrictUniversalPropertyFixedTarget`, `IsLocalization.mk'` | `CategoryTheory/Localization/Predicate.lean:75`, `:116` |
| lifting and uniqueness | `Localization.lift`, `liftNatIso`, `natTrans_ext`, `Localization.uniq : D₁ ≌ D₂` | `.../Predicate.lean:299`, `:353`, `:434` |
| `C[W⁻¹]` is itself a quotient of a path category | `MorphismProperty.Localization := Quotient (Localization.Construction.relations W)`, `LocQuiver`, `Q`, `wIso`, `wInv`, `objEquiv`, `morphismProperty_eq_top` | `CategoryTheory/Localization/Construction.lean:63`, `:79`, `:96`, `:101` |
| **disjoint union of categories** | `CategoryTheory.Sigma` — `incl`, `desc`, `descUniq`, `natIso`, `Functor.sigma` | `CategoryTheory/Sigma/Basic.lean:69`, `:76`, `:122`, `:154`, `:174`, `:228` |
| uniqueness of functors out of a quotient | `Quotient.lift_unique'`, `natTrans_ext` | `CategoryTheory/Quotient.lean` |

`Localization.Construction` is already used in this repo (`Retraction.lean` uses `objEquiv`, `wIso`,
`wInv`, `morphismProperty_eq_top`), so it is an established idiom here.

---

## Phase 0 — Survey

The Repo dictionary above. Do not redo it. If you find it wrong, fix it in the same change as the
code.

## Phase Z — Assemble the polygraph for Ch(Z)[W_Z⁻¹]

Z1. `Polygraph.coproduct (P : ι → Polygraph) : Polygraph` — the disjoint union: 0-cells
`Σ i, (P i).V`, 1-cells only within a fibre, 2-cells those of each fibre. With
`Presents.coproduct : (∀ i, Presents (P i) (C i)) → Presents (Polygraph.coproduct P) (Σ i, C i)`,
using `CategoryTheory.Sigma`. The fibrewise `Gen` avoids a transport altogether by being an indexed
inductive (`CoproductGen`, after mathlib's `Sigma.SigmaHom`), so `ofDesc` needs no `erw`; see
`Machinery/Presentation/Coproduct.lean`.

Z2. `(W Zbp).op.Localization ≌ Σ N : ℕ, (AtStrands N).FullSubcategory`. Objects of the localization
are objects of `(Ch Zbp)ᵒᵖ` on the nose (`Construction.objEquiv`), so the index is `dimSum ∘ dims`;
`isEmpty_loc_hom` gives no cross-component homs and `atStrands_run` gives the object.

Z3. `zLocPresentation : Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N)) ((W Zbp).op.Localization)`,
from Z1 + Z2 + `germPresentation` + `strandComponentGarside`, with `zLocArtinPresentation` the same
statement in `ArtinRel`/`strandComponentArtin`. Both go through `zLocOfComponents`: transport each
component's presentation into its `FullSubcategory` *first*, then take the coproduct, then transport
along `strandDecomposition.symm`. Doing it that way needs no `Functor.sigma`.

### Phase A — General gluing theory (arbitrary D, X, W_D)

Notation: C := ∫X, F : C ⥤ D the projection, W_C := W_D.inverseImage F.

A1. `Functor.IsDiscreteFibration F := ∀ c, (Over.post F : Over c ⥤ Over (F.obj c)).IsEquivalence`,
the proof that the projection of a category of elements satisfies it, and the fact that `W_C.over c`
corresponds to `W_D.over (F.obj c)` under the equivalence. A2 through A5 take `IsDiscreteFibration`
as their only hypothesis and never mention elements or `ᵒᵖ`; A1 is the one place the op-juggling
lives, and that boundary is the point of stating it this way.

A2. Natural iso (Over c)[W_C⁻¹] ≅ (Over (F c))[W_D⁻¹], natural in c (postcomposition on both sides,
`Over.map`, with `Over.mapId`/`Over.mapComp` for the coherence). Get it from
`Functor.IsLocalization.of_equivalence_source`/`of_equivalence_target` rather than by hand.

A3. For any category C, class W containing identities, and target E: functors C[W⁻¹] ⥤ E correspond bijectively to families G c : (Over c)[W⁻¹] ⥤ E with G c' = G c ∘ (postcompose u)[W⁻¹] for every u : c' → c. Prove the direction "family ↦ functor" first: since Over c has a terminal object, the family is determined by its values at (c, 𝟙 c) and on arrows; check that inverting W/c for all c is inverting W. The unlocalized statement first is the cheapest route: forwards is `Over.forget c ⋙ G`, backwards sends `c` to `(G c).obj (𝟙 c)` and `u : c' ⟶ c` to `(G c).map u` read as an arrow `u ⟶ 𝟙 c` of `Over c`. For the localized step, `w : a ⟶ b` in `W` is an arrow `(a,w) ⟶ (b,𝟙 b)` of `Over b` lying in `W.over b`.

A4. **Superseded** — the bespoke `glue`/`SliceLabels` construction is gone; the glued polygraph is a
`colimit` and the bijectivity demand below is replaced by `SliceSkeleton`.  The refutations are what
is worth keeping, and they are why `SliceSkeleton` is not optional.

A4 (as attempted). Definition of `Glue X P L` for `P : D ⥤ Polygraph`, and
`Presents (glue X L) (C[W_C⁻¹])` assuming ∀ d, `Presents (P d) ((Over d)[W_D⁻¹])` naturally in d.

**`Glue X P` alone is not definable.** A glued 1-cell runs between objects of `∫X`, so a 1-cell of
`P d` has to know *which* arrow of `Over d` each of its endpoints names — and `Polygraph.V` only
indexes, it names nothing. Hence the third argument `L : SliceLabels P` (`ob` plus `map_ob`).
`labelsOf` builds `L` from the presentations, but `glue` takes `L` rather than a presentation, so
that `glue` stays a construction on polygraphs and its interpretation stays a theorem. The
naturality hypothesis is a *strict* equality `(P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f`;
an iso would give only an iso of objects and `GlueRel.overlap` would not typecheck.
`Presents` wants a functor `presented (Glue) ⥤ C[W⁻¹]` that is an equivalence, and building the
comparison *into* `presented (Glue)` is circular, so: build `Φ : (Glue X P).presented ⥤ C[W_C⁻¹]` by
`Presents.ofDesc`; build `Ψ` the other way out of A3, its per-slice component being the
copy-inclusion `Polygraph.Hom` `P d ⟶ Glue X P` composed with the inverse of `P d`'s presentation;
then `Ψ ⋙ Φ ≅ 𝟭` by `Localization.natTrans_ext` (check after precomposing with `Q`) and
`Φ ⋙ Ψ ≅ 𝟭` by `Quotient.lift_unique'` (check on generators), and `IsEquivalence` from the two isos.

**A4 as stated above is false; `L.ob d` has to be a bijection onto the objects of `Over d`.**
`hL` makes `L.ob d` the object map of `(p d).E` read through the bijection
`Construction.objEquiv`, and `Presents` asks only that `(p d).E` be an equivalence — so `L.ob d`
may be neither injective nor surjective, and each failure breaks the theorem on its own.

*Not surjective onto `𝟙 d`* — then the 0-cell `(d, x)` of `glue` lies in no copy, so `Φ` misses
morphisms. Take `D = {0 →ʷ 1}`, `W = {w}`, `X` terminal; `Over 1` is the walking arrow and
`(W.over 1)⁻¹` inverts it, so a single 0-cell labelled `Over.mk w` and **no** generators presents
it, and likewise over `0`. Then `GlueGen` is empty, `presented (glue X L)` is discrete on two
objects, and `(∫X)[W⁻¹]` is the contractible groupoid on two objects.

*Not injective* — then two 0-cells of `P d` collapse to one 0-cell of `glue` while their 1-cells
do not, so words that were not composable become composable and `Φ` stops being faithful.  This is
what killed the flattened construction, and it is why the colimit keeps the copies' own 0-cells:
`GlueRefutation.lean` builds exactly that data (`D = Discrete PUnit`, `W = ⊥`, `X` terminal, `P₂`
the polygraph `a ⇄ a'` with a *total* 2-cell relation, `Over d` a single object) and shows the
**colimit** presents it anyway (`presentsGlue₂`) — so the failure was the flattening, not the
hypothesis.

**What replaced it.** `SliceSkeleton` asks exactly what the two refutations show is missing, and no
more: one 0-cell per **iso-class** of `Over d`, rather than one per object.  From it `slInv` inverts
`(p d).E` up to a canonical iso, `slInv_square` inverts `hP`, `glueRetractCocone` is a plain
`OverCocone`, and `glueUnit : glueDesc ⋙ glueRetract = 𝟭` is an equality checked on generators;
only the counit stays an isomorphism, which is all `Presents` asks.

A5. **Superseded.** `presentsSliceColimit X V p hP hthin R` (`Glue.lean`) puts a copy over *every*
object of `∫X` and returns `Presents (colimit (elementsPoly X P)) ((∫X)[W⁻¹])`;
`presentsColimitOfLocalizedSlices` (`SliceColimit.lean`) is the same read on
`colimit (overLocFunctor W)`, and `ChainCat.presentsChainsColimitLoc` is it at `Ch K`.
There is no generating set
and no span bookkeeping: the copies are indexed by `(∫X)ᵒᵖ` and the overlaps *are* the arrows of
`∫X`, supplied by `colimit.w`.

The one hypothesis left is `R : SliceSkeleton W p`, a **single field**: exactly one 0-cell of `P d`
names an object isomorphic to each `y : Over d` (`entry`).  It is what replaces the discarded
bijectivity demand `∀ d, Bijective (L.ob d)`, and the discarded demand was genuinely unmeetable —
objects of `((W Zbp).over (zObj d))ᴸ` are all of `Over (zObj d)` on the nose
(`Construction.objEquiv`) while a slice polygraph has one 0-cell per **iso-class**, and
`Presents.restrict` cannot cut the difference away (`Convex.respectsIso`, `Partial.lean`: a convex
property is closed under isomorphism, so it can never carve out a skeleton).  At `Ch K` the
skeleton is `RunOver.eq_of_locIso`: two runs isomorphic in the localized slice are *equal*, the
weak order being a grading the localization keeps.

A6 (optional, do after Phase D if time permits). Overlap relations at maximal spans suffice, under a well-foundedness hypothesis on spans.

A7 (optional). If X w is a bijection for all w ∈ W_D, then X descends to X̄ on D[W_D⁻¹], C[W_C⁻¹] ≅ ∫X̄, and Glue X P is isomorphic to the pullback of Glue 1 P (the glued presentation of D[W_D⁻¹]) along ∫X̄ → D[W_D⁻¹] provided every generator of P d is the pushforward of a generator over its own target. State this; prove only if cheap. The hypothesis is exactly `InvertsMerges K` (`ElementsFibration.lean:116`), which `IsSegal` implies (`invertsMerges_of_isSegal`, `:145`), and the descent exists as `wedgeHomsDescend` (`:305`) with `isLocalization_chDescent` (`:314`).

### Phase B — Products and wedges

**Retired as a route, kept as results.**  B2 and B4 are true and stay in the tree
(`Presents.prod`, `locChConsEquiv`), but "the slice is a product of cube slices" is a description of
the *category*, not a way to build its presentation: it produced a second presentation chain beside
the inherited one, and the second chain is gone.  Read B2/B4 below as statements about `Ch(⋁d)`, and
Phase C as the route that actually runs.

B1. `(E × E')[(W × W')⁻¹] ≅ E[W⁻¹] × E'[W'⁻¹]` is `Functor.IsLocalization.prod`, and it is an
`instance`: `(W X).IsMultiplicative` gives `ContainsIdentities` through the parent projection, so
`inferInstance` finds `(L₁.prod L₂).IsLocalization ((W X).prod (W Y))` with nothing written. The
only thing B1 needed was for `Mathlib.CategoryTheory.Localization.Prod` to be *imported* — it was
not — which `Concurrency/Merge/WedgeSplit.lean` now does. **No wrapper exists; do not add one.**

B2. `Polygraph.prod P Q` and `Presents.prod : Presents P A → Presents Q B → Presents (Polygraph.prod P Q) (A × B)`.
Besides the two copies' relations the product polygraph carries the **interchange squares**
`(g,1)·(1,h) = (1,h)·(g,1)` for every 1-cell `g` of `P` and `h` of `Q`; without them the result
presents a free product, not a product. That is the content of this phase, and it makes B2 *not* a
mirror of Z1: the coproduct's words are each one fibre's, so `comapIncl_full` does them, while the
product's interleave and need `exists_normalForm` instead. What the two do share —
`Hom.ofPre`, `comapIncl_full`, `quot_mapPath_congr`, `lift_evalPre_comp`,
`lift_map_eq_of_quot_eq` — lives in `Basic.lean`.

B3. Both statements are in the Slices table above: `overEquivWedgeChains` (with
`over_W_eq_inverseImage`, which is what Phase C actually consumes) and `chConcatEquiv` (with
`W_prod_eq_inverseImage_chConcat`, which is what B4 consumes). `AdmitsAltitude` is a genuine
hypothesis of `chConcatEquiv` at general `X`, `Y` — `splitObj` needs it — and is discharged once
and for all for wedges of serial wedges by `serialChConcatEquiv`.

B4 is **binary and recursive, not `Fin`-indexed**, and `Functor.IsLocalization.pi` is never used.
`⋁(n :: rest) = □n ∨ ⋁rest` is **definitional** (`serialWedge_cons` is `rfl`), so the cons splitting
carries no reindexing and no `eqToHom`, whereas `⋁a ≌ ∏ᵢ □aᵢ` is not definitional and would drag
`Fin a.length` through everything; and `IsLocalization.prod` (B1) then suffices.

The engine is `isLocalization_chConcat`: `chConcat ⋙ Q` *is* a localization of `Ch X × Ch Y` at
`(W X).prod (W Y)`, so every equivalence below is `Localization.uniq` applied to it.

A naturality square would have to be stated for an **append**, not a cons: `splitTarget` splits a
wedge map at an append of the target, so a general map of shapes `⋁a ⟶ ⋁b` regroups the beads of
`a` into consecutive blocks, one per bead of `b`, and does **not** respect a cons splitting.

### Phase C — The functor P : Ch(Z) ⥤ Pres, for each braid presentation

**Landed at `slicePolyFunctor` / `slicePresentationOf`, in one step and not bead by bead.**  The
plan below went through the cube: present `(Over [n])[W_Z⁻¹]` first (C1), then extend to a wedge by
one cube factor per bead (C2).  That works and is gone.  What replaced it does not decompose the
shape at all: the runs over `d` are a downward-closed set of permutations for the right weak order
(the exchange `exists_runOver_mul_adjT`, iterated), so `PosBraid N` acts on them **partially**
(`weakActionOn`), `sliceFibre d` is the presheaf that action gives on the localized base, and its
defined part *is* the localized slice, reversed (`definedSliceLoc`).  So
`slicePolyFunctor p := (p.elements (sliceFibre ·)).restrictPoly (defined ·) ⋙ opFunctor` is the
base's own cells lifted — a 1-cell is a generator of `p` acting on a run, a 2-cell a relation of `p`
holding there — parametric in `p` by construction, with the shape of `d` never taken apart.

C1 (superseded). Presentations of `(Over [n])[W_Z⁻¹]`, and the morphisms induced by maps
`[m] ⟶ [n]`, as one construction parametrized by the input presentation, not written twice.
The slice collapses, which is what makes this tractable: `exists_W_from_ones` gives a W-arrow
`1ⁿ ⟶ c` for every shape `c` with `dimSum c = n`, and that arrow is automatically a triangle over
any `u : c ⟶ [n]`, so every object of `Ch(Z)/[n]` is W-isomorphic to some `(1ⁿ, σ)`; `onesTopEquiv n`
says those `σ` are exactly `Perm (Fin n)`.  `cubePresentation n` survives as the *thin* instance —
the statement that the cube slice is presented by its atom steps.

C2 (superseded). Extend to wedges by one cube factor per bead, functorial via B4, as a functor
`Ch Zbp ⥤ Polygraph`.

C3. Theorem: ∀ d, presents (P d) ((Over d)[W_Z⁻¹]), naturally — exactly the hypothesis A5 consumes.
It is `slicePresentationOf p d` with `slicePoly_hP p f` for the naturality, and the naturality is
free: the 0-cells name their own slice objects (`sliceCellOver`), pushing them is `Over.map`, and
`locOver_isThin` settles the morphism half by `Subsingleton.elim`.  Functoriality of the family is
**lax and not natural** — a step undefined over `d'` can be defined over `d` — which is exactly what
`PartialFam`/`partialElementsMap` consume.

### Phase D — Ch(K)

D1. Everything is in `Concurrency/Presentation/SlicePresentation.lean` and
`Concurrency/Presentation/SliceInherit.lean`, for every `K` and with no hypothesis on it:

| what | name |
|---|---|
| `W K` on the elements side | `ChainCat.W_eq_inverseImage_elements` |
| **the transport** | `ChainCat.locEquivElements K : (W K)ᴸ ≌ ((W Zbp)⁻¹π)ᴸ` — `presentsSliceColimit` lands on the elements side, and this is what brings it back |
| a chain's slice is its shape's | `ChainCat.locOverEquivBase K c` |
| **the theorem** | `ChainCat.presentsChainsColimit K p hP R` |
| …with the inherited family supplied | `ChainCat.presentsChainsSliceColimit K p hp` |
| the cells of the colimit, read on a leg | `glueV`, `glueE`, `glueV_leg`, `glueE_leg`, `at_glueV`, `arrow_glueE` |

`presentsChainsColimit`'s remaining arguments are exactly `P` and `hP` (C3) together with a
`SliceSkeleton`; the slices being posets is discharged there by `locOver_isThin`.  Supplied at
`slicePolyFunctor p` / `slicePresentationOf p` / `sliceSkeleton p hp`, those arguments give
`presentsChainsSliceColimit K p hp`, whose one hypothesis on the *base* is
`StrandSeparated p` — one 0-cell per strand count — and none on `K`.

D2. Corollaries for Garside and for Artin, both through the same mechanism:
`presentsChainsGarsideColimit K` and `presentsChainsArtinColimit K`, hypothesis-free, since
`strandSeparated_zLocOfBraidMonoids` holds for every monoid presentation of the braid monoids.
`posBraid_equiv_artinPos` (`Machinery/Braid/Matsumoto.lean`) is the comparison — call it.

D3. Sanity check: `Testing/Pi1/GlueCount.lean` counts the colimit at `Hbp □ⁿ` in an independent
model.  The 1- and 2-cells must **move with `p`** — `(2, 12, 72)` / `(0, 6, 72)` Artin against
`(4, 48)` / `(8, 144)` germ, where a thin family would give `(4, 54, 9888)` at every `p`.  If Artin
and germ ever agree, the family has stopped being inherited.
