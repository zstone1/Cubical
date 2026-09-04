# Task: present Ch(K)[W⁻¹] by gluing presentations of localized slices

Context

This repository formalizes, in Lean 4 / Mathlib, a category Ch(K) attached to a (bipointed) precubical set K, together with a functor F : Ch(K) ⥤ Ch(Z) which is a discrete fibration (Ch(K) is the category of elements of a presheaf X on Ch(Z)). These proofs exist. Both categories carry a class of morphisms (the "inert" morphisms, call it W), with W_K = F⁻¹ W_Z. Localization uses Mathlib's CategoryTheory.Localization with MorphismProperty. This all exists in the repo.

## Ch(Z), its slices, the discrete fibration theorem for F.

Polygraphs already exists, and they are the main mechanism for doing presentations.
Ch(Z)[W_Z⁻¹] is understood in terms of PosBraid, using the garside presentation: each strand
component is one object with endomorphism monoid PosBraid N, and the Garside generators correspond
to the maps 1^n → [n]. The polygraph for it has not been assembled — that is Phase Z. We will want
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

Everything below was read off the source; `file:line` is exact. **Read this instead of searching.**
Anything marked **ABSENT** genuinely does not exist — do not go looking for it.

## The two categories, and the fibration

| what | name | where |
|---|---|---|
| chains of `K` | `ChainCat.Obj K`, notation `Ch K` | `Precubical/Chains/Category.lean:23`, notation `:51` |
| an object | `⟨dims : List ℕ+, map : ⋁dims ⟶ K⟩` | `.../Category.lean:23` |
| a morphism | `⟨φ : ⋁a.dims ⟶ ⋁b.dims, w : φ ≫ b.map = a.map⟩` | `.../Category.lean:31` |
| the terminal `BPSet` | `CubeChains.Zbp`, `isTerminalZbp` | `Precubical/Basic/Terminal.lean:35`, `:56` |
| **F, the projection** | `ChainCat.toChZ (X : BPSet) : Ch X ⥤ Ch Zbp` | `Concurrency/Merge/MergeClass.lean:28` |
| **X, the presheaf** | `ChainCat.wedgeHoms K : (Ch Zbp)ᵒᵖ ⥤ Type` | `Concurrency/Presentation/ElementsFibration.lean:34` |
| … acts by precomposition | `wedgeHoms_map : (wedgeHoms K).map f.op m = f.φ ≫ m` | `.../ElementsFibration.lean:36` |
| the elements description | `toElements K : Ch K ⥤ ((wedgeHoms K).Elements)ᵒᵖ` | `.../ElementsFibration.lean:42` |
| … as an equivalence | `chEquivElements K : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ` | `.../ElementsFibration.lean:77` |
| … op'd | `chOpEquivElements K : (Ch K)ᵒᵖ ≌ (wedgeHoms K).Elements` | `.../ElementsFibration.lean:81` |
| shapes as chains of `Zbp` | `zObj (d : List ℕ+) : Ch Zbp`, `zHom` | `Concurrency/Merge/TotalMerge.lean:19`, `:24` |
| a morphism of `Ch Zbp` is a bare wedge map | `serialWedgeFullyFaithful` | `Concurrency/Merge/MergeClass.lean:46` |

**Op placement — the single biggest hazard.** `wedgeHoms K` carries its `ᵒᵖ` on the *source*
(a presheaf on `Ch Zbp`). `toElements`/`chEquivElements` carry it on the *whole* `Elements`
category, with `Ch K` bare on the left. `chOpEquivElements` moves it to the left instead. Inside
`toElements.obj` both `op`s are explicit: `op ⟨op (zObj a.dims), a.map⟩`. Net effect: `Ch K ⥤ Ch Zbp`
is a discrete **fibration** (slices *over* an object agree), even though mathlib's `Elements` is the
opfibration convention. Do not re-derive this; use the table.

`toElements K ⋙ (CategoryOfElements.π (wedgeHoms K)).leftOp = toChZ K` is `rfl`, so
`(toChZ K).IsDiscreteFibration` needs no transport.

**ABSENT in mathlib:** any discrete-fibration predicate. `CategoryTheory/FiberedCategory/` has
`Functor.IsPreFibered`/`IsFibered` only, and this repo does not import it.

## Discrete fibrations (`Machinery/Slice.lean`)

| what | name | where |
|---|---|---|
| the predicate | `Functor.IsDiscreteFibration F`: `Over.post F : Over c ⥤ Over (F.obj c)` is an equivalence for every `c` | `Machinery/Slice.lean:28` |
| closure | equivalences are; composites are; `IsDiscreteFibration.of_natIso` | `.../Slice.lean:43` |
| `W` on the two slices | `MorphismProperty.over_inverseImage : (W.inverseImage F).over = W.over.inverseImage (Over.post F)` — `rfl`, no hypothesis on `F` | `.../Slice.lean:53` |
| **the example** | `CategoryOfElements.π_leftOp_isDiscreteFibration : ((π X).leftOp).IsDiscreteFibration` for `X : Cᵒᵖ ⥤ Type w` | `.../Slice.lean:61` |

`Slice.lean` is the one place the `op`-juggling lives.  **Nothing consumes it any more**: A2 was
deleted (below), and `Glue.lean` works concretely with `(π X).leftOp` and `elementsLiftOver` rather
than taking `IsDiscreteFibration` as a hypothesis.  It is kept as A1's statement, not as
infrastructure — if A5 wants the abstract hypothesis, this is where it already is.

## The localized slices (`Machinery/Localization/SliceLocalize.lean`)

| what | name | where |
|---|---|---|
| localization pulls back along an equivalence | `Functor.IsLocalization.of_inverseImage (G) [G.IsEquivalence] (L) (V) [V.RespectsIso] [L.IsLocalization V] (U) (hU : U = V.inverseImage G) : (G ⋙ L).IsLocalization U` | `SliceLocalize.lean:23` |
| postcomposition, localized | `overMapLoc W u` — a `Construction.lift`, hence **strict**: `overMapLocFac`, `overMapLoc_id`, `overMapLoc_comp` are equalities | `.../SliceLocalize.lean:48`, `:55`, `:64`, `:67` |

**A2 was built and then deleted; do not rebuild it.** The comparison
`sliceLocEquiv F W c : ((W.inverseImage F).over c)ᴸ ≌ (W.over (F.obj c))ᴸ`, its `Over.mapPost`
naturality and the `[F.IsDiscreteFibration]`/`[W.RespectsIso]` scaffolding around them existed,
were correct, and were consumed by nothing: `Presents.ofDesc` takes a *prefunctor*, so the
comparison has to be strict on objects, and `Localization.uniq` computes nothing. `elementsLift`
(`Glue.lean:234`) writes that inverse down instead. See the note under Phase A4.


## Slice cocones (`Machinery/Localization/SliceFamily.lean`)

No hypothesis on `W` at all — not even `ContainsIdentities`.

| what | name | where |
|---|---|---|
| a compatible family | `OverCocone C E`: `obj c : Over c ⥤ E`, `w u : Over.map u ⋙ obj c = obj c'` | `SliceFamily.lean:24` |
| its two directions | `OverCocone.ofFunctor Φ` (`Over.forget c ⋙ Φ`), `OverCocone.desc` (read at `Over.mk (𝟙 c)`) | `.../SliceFamily.lean:36`, `:58` |
| **unlocalized** | `overCoconeEquiv : (C ⥤ E) ≃ OverCocone C E` | `.../SliceFamily.lean:113` |
| a strict universal property is a bijection | `Localization.StrictUniversalPropertyFixedTarget.functorEquiv : (D ⥤ E) ≃ {F : C ⥤ E // W.IsInvertedBy F}` | `.../SliceFamily.lean:122` |
| a localized family | `OverCoconeLoc W E`: `obj c : (W.over c).Localization ⥤ E`, `w u : overMapLoc W u ⋙ obj c = obj c'` | `.../SliceFamily.lean:136` |
| the two halves | `isInvertedBy_iff_over`, `coconeLocEquiv` | `.../SliceFamily.lean:150`, `:159` |
| **A3** | `overCoconeLocEquiv W : (W.Localization ⥤ E) ≃ OverCoconeLoc W E` | `.../SliceFamily.lean:179` |
| … its characterisation | `overCoconeLocEquiv_apply`, `overCoconeLocEquiv_symm_apply`: `(W.over c).Q ⋙ G.obj c = Over.forget c ⋙ W.Q ⋙ Φ` | `.../SliceFamily.lean:184`, `:189` |

## The glued polygraph (`Machinery/Presentation/Glue.lean`)

| what | name | where |
|---|---|---|
| **the missing input** | `Polygraph.SliceLabels P`: `ob d : (P.obj d).V → Over d` plus `map_ob f a : ob d ((P.map f).cells.obj a).as = (Over.map f).obj (ob d' a.as)` | `Glue.lean:71` |
| 0-cells | `GlueV X = Σ d : D, X.obj (op d)` | `.../Glue.lean:81` |
| the 0-cell a copy's 0-cell names | `gluePt X L d x a = ⟨(L.ob d a).left, X.map (L.ob d a).hom.op x⟩` | `.../Glue.lean:84` |
| the overlap identification | `gluePt_map`, `gluePre_obj_map` | `.../Glue.lean:88`, `:107` |
| 1-cells, copy inclusion, 2-cells | `GlueGen`, `gluePre`, `GlueRel` (`copy` and `overlap`) | `.../Glue.lean:96`, `:101`, `:112` |
| **the polygraph** | `Polygraph.glue X L` | `.../Glue.lean:124` |
| the copy inclusion | `Polygraph.glueIncl X L d x : Hom (P.obj d) (glue X L)` | `.../Glue.lean:137` |
| `overMapLoc` on objects | `overMapLoc_obj` | `.../Glue.lean:187` |
| the labels a family of presentations gives | `labelsOf W p hP`, `labelsOf_ob` | `.../Glue.lean:197`, `:205` |
| **…and when they are bijective** | `presentedVEquiv` (a polygraph's 0-cells **are** the objects it presents) and `labelsOf_ob_bijective_iff`: `L.ob d` is bijective exactly when `(p d).E` is bijective on objects. `Presents` does not give that, so it is a hypothesis on `p`; without it `Presents.glue` is **false** (`GlueRefutation`) | `.../Glue.lean:62`, `:214` |
| **the cartesian lift** | `elementsLift X d x : Over d ⥤ (X.Elements)ᵒᵖ`, with `elementsLift ⋙ π.leftOp = Over.forget d` by `rfl` | `.../Glue.lean:234`, `:242` |
| **…and it is a section of the projection** | `elementsLift_post : Over.post π.leftOp ⋙ elementsLift X (π.leftOp.obj c) c.unop.2 = Over.forget c` — a strict **equality**, from `elements_snd_map` | `.../Glue.lean:257` |
| … on slices | `elementsLiftOver X c : Over (F c) ⥤ Over c`, the **strict inverse** of `Over.post F`: `elementsLiftOver_forget` and `elementsLiftOver_post` are both `rfl`, so the slice over `c` cancels | `.../Glue.lean:638`, `:653`, `:657` |
| … localized | `glueSliceEval X W d x`, `glueSliceEval_fac`, `glueSliceEval_obj` | `.../Glue.lean:276`, `:281`, `:286` |
| **the lift is functorial in the base** | `elementsLift_over_map : Over.map f ⋙ elementsLift X d x = elementsLift X d' (X.map f.op x)` | `.../Glue.lean:293` |
| … localized | `overMapLoc_comp_glueSliceEval : overMapLoc W f ⋙ glueSliceEval X W d x = glueSliceEval X W d' (X.map f.op x)` | `.../Glue.lean:303` |
| **the relations are sufficient** | `glueIncl_naturality : (P.map f).functor ⋙ (glueIncl X L d x).functor = (glueIncl X L d' (X.map f.op x)).functor` — a strict **equality**, by `Paths.ext_functor` from one `GlueRel.overlap` per generator | `.../Glue.lean:145` |
| the sandwich combinators | `eqToHom_conj_comp` (composing two sandwiches merges the two facing crusts), `eqToHom_conj_conj`, `eqToHom_conj_congr`, `eqToHom_conj_map` (a functor carries a sandwich to a sandwich) | `.../Glue.lean:30`, `:37`, `:45`, `:51` |
| strict facts for *this* `F` | `elementsPost_map` (`Over.map u ⋙ Over.post F = Over.post F ⋙ Over.map (F.map u)` is `rfl` here), `elementsPost_map_comp`, `elementsPost_map_id`, `elements_snd_map` | `.../Glue.lean:472`, `:479`, `:485`, `:246` |
| the interpretation of the cells | `glueAt`, `glueAt_gluePt`, `glueArrow`, `glueEval` | `.../Glue.lean:322`, `:327`, `:334`, `:342` |
| a copy's word, evaluated | `glueEval_map_gluePre`, `glueEval_mapPath` | `.../Glue.lean:348`, `:357` |
| **the compatibility square, on functors** | `glueBridge`, `glueBridge'`, `glueSliceEval_bridge` | `.../Glue.lean:384`, `:391`, `:401` |
| **soundness** | `glue_sound_copy`, `glue_sound_overlap`, `glue_sound` | `.../Glue.lean:409`, `:418`, `:437` |
| **Φ** | `glueDesc : (glue X L).presented ⥤ (W.inverseImage (π X).leftOp).Localization` | `.../Glue.lean:445` |
| **a copy, read by Φ** | `glueIncl_desc : (glueIncl X L d x).functor ⋙ glueDesc = (p d).E ⋙ glueSliceEval X W d x` — a strict **equality**, because `glueAt_gluePt` is one | `.../Glue.lean:452` |
| **inverting a slice presentation on the nose** | `pInv W p hb d := strictInv (p d).E (hb d)`, and `glueBase` — the 0-cell naming `𝟙 d`, with `glueBase_ob`, `gluePt_base` (`gluePt d x (base d) = (d, x)`) and `glueIncl_base` | `.../Glue.lean:498`, `:503`, `:507`, `:515`, `:523` |
| **the comparison on the base slice** | `glueStep : overMapLoc W (F u) ⋙ pInv ⋙ glueIncl = pInv ⋙ glueIncl` — `hP` inverted by `strictInv_square`, an **equality** where a mere equivalence would give a mate | `.../Glue.lean:540` |
| **the retraction** | `glueRetractPre` (`Over.post F ⋙ Q ⋙ pInv ⋙ glueIncl`), `glueRetractPre_map` (**strict**, so the cocone is an `OverCocone`), `glueRetractPre_inverts`, `glueRetractCocone`, `glueRetractDesc` (a `Construction.lift`) with `_fac` and `glueRetract_forget` | `.../Glue.lean:555`, `:563`, `:569`, `:584`, `:598`, `:603`, `:609` |
| **Ψ then Φ, one slice at a time** | `glueRetractPre_desc : glueRetractPre c ⋙ glueDesc = Over.forget c ⋙ Q` — four rewrites, because `glueIncl_desc`, `strictInv_comp`, `glueSliceEval_fac` and `elementsLift_post` are all equalities | `.../Glue.lean:617` |
| **ε** | `glueCounit : glueRetractDesc ⋙ glueDesc = 𝟭`, by `Construction.uniq` and `OverCocone.functor_ext` | `.../Glue.lean:629` |
| **a slice, read through Ψ** | `glueSliceEval_retract : glueSliceEval X W (F c) c.unop.2 ⋙ glueRetractDesc = pInv ⋙ glueIncl` — the mirror of `glueIncl_desc`, and what makes the unit computable on generators | `.../Glue.lean:664` |
| **η** | `glueUnit : glueDesc ⋙ glueRetractDesc = 𝟭`, by `Quotient.lift_unique'` then `Paths.ext_functor`: objects by `glueRetract_glueAt`, generators by `glueSliceEval_retract` and `comp_strictInv`. No rewrite reaches under a `Quotient` lift's `.map`, so the chain runs through `exact` | `.../Glue.lean:685`, `:677` |
| **`glue X L` presents `(∫X)[W⁻¹]`** | `presentsGlue` (`Equivalence.mk` adjointifies, so the two equalities are all that is asked) and `presentsGlueOf` for `labelsOf` | `.../Glue.lean:714`, `:723` |
| **`glue` needs bijective labels** | `not_nonempty_presents_glue`: every hypothesis holds and `glueDesc` is still not faithful, because two 0-cells of `P d` with one label become one 0-cell of `glue` while their 1-cells do not; `presents₂_not_bijective` is exactly the hypothesis `presentsGlue` adds | `.../GlueRefutation.lean:245`, `:236` |
| … what makes that counterexample cheap | a **total** 2-cell relation (`P₂`) so the presented category is codiscrete with no word problem; `W = ⊥` so every `≤ isomorphisms` side condition is `h.elim` and `equivLocalizationOfLeIso` computes both localizations; a hand-rolled `Wind` rather than `SingleObj`, which carries two `Quiver` instances | `.../GlueRefutation.lean:69`, `:89`, `:34`, `:135` |
| a 1-cell's word is the 1-cell | `Paths.lift_toPath` (`@[simp]`); `Presents.ofDesc_arrow` is the same fact one level up | `PathCategory/Basic.lean:135`, `Presentation/Basic.lean:380` |

**State each step as an equality of *functors*, then descend once.** Functor equations have no
implicit object arguments, so `rw` works on them normally; the landmine below only bites once the
objects are pinned. `glueSliceEval_bridge : (p d').eval ⋙ glueSliceEval X W d' (f* x)
= (P.map f).words ⋙ (p d).eval ⋙ glueSliceEval X W d x` is the whole overlap identification in that
form — three rewrites — and `glue_sound_overlap` is then one `Functor.congr_hom` plus the sandwich
combinators. Attempting the same proof morphism-first does not work at all: `rw` *and* `simp only`
both fail to fire on a `Functor.map`-headed pattern that is printed verbatim in the goal.

**Landmine: `rw`/`simp` cannot apply `Category.assoc` in `W.Localization`.** When a composite's
middle object is spelled two ways — `(Paths.lift E).obj (gluePre.obj a)` from `Paths.lift_cons`
versus `glueAt …` from the rewritten factor — the two are defeq but `kabstract`'s keyed matching
runs at `instances` transparency and fails. `simp only [Category.assoc]` then makes *no progress*
and reports no unused-argument warning, which reads like the lemma fired. Marking the offending def
`@[reducible]` does **not** help: the mismatch is in the `≫`'s implicit *object* argument, not in a
head symbol. The cure is term mode, which elaborates at default transparency — and rather than
repeat the dance, everything in `Glue.lean` goes through one combinator:
`eqToHom_conj_comp : (eqToHom hA ≫ f ≫ eqToHom hB) ≫ (eqToHom hB.symm ≫ g ≫ eqToHom hC)
= eqToHom hA ≫ (f ≫ g) ≫ eqToHom hC`, proved by `subst` and used by `exact`.

**A definition built inside a tactic block can be correct and useless.** `Localization.Lifting`
witnesses supplied as `letI` inside a `by` block make the definition's components unnameable from
outside, so `Localization.liftNatTrans_app` cannot be applied to it *at all* — and the symptom is the
familiar one, a lemma that visibly ought to apply refusing to. This is **not** the transparency
hazard below; the cause and the cure are unrelated. The cure is to hoist the witnesses to `instance`s
and write the definition in term mode. Prefer term mode for any definition whose components later
proofs will need to compute with.

**The overlap 2-cells are sound because the cartesian lift is functorial in the base.**
`elementsLift_over_map` is the whole content: lifting at `x` after postcomposing with `f` is
lifting at `f* x`. Both it and its localized form are *equalities* of functors, so the overlap
soundness proof will be a rewrite rather than a transport argument.

**`complete` is not an obligation here.** `Presents` needs only *some* equivalence
`(glue X L).presented ⥤ C[W_C⁻¹]`, so `Φ := Polygraph.desc φ sound` plus the retraction `Ψ` and the
two isos gives `IsEquivalence` without `Presents.ofDesc`'s `complete`/`full`/`essSurj`. Hence
`Elements.lean`'s `gen_pullbackRel` does not apply and is not needed: it reflects a congruence along
a *fully faithful* functor, and the copy inclusions `gluePre` are neither faithful nor injective on
0-cells — that is exactly what gluing means.

**`sliceLocEquiv` (A2) cannot be used to interpret the cells.** `Presents.ofDesc` takes a
*prefunctor*, so the comparison has to be strict on objects; `sliceLocEquiv` is an abstract
`IsEquivalence` built from `Localization.uniq`, and its inverse computes nothing. `elementsLift`
writes that inverse down instead — it is a genuine functor, `elementsLift ⋙ π.leftOp = Over.forget d`
holds by `rfl`, and `glueSliceEval` is its `Construction.lift`, so `glueSliceEval_obj` pins the
0-cells on the nose. That left A2 with nothing to do at all, which is why it has been deleted:
`elementsLift_inverts` supplies the *is-a-localization* half directly.

**`glue` is not a `coproduct`, and `glueIncl` is not `coproductIncl`** — only the same shape
(`Hom.ofPre` of a fibre inclusion plus a soundness lemma). `coproduct`'s 0-cells are `Σ i, (P i).V`,
so `coproductPre` is injective on 0-cells and words cannot leave their fibre; `glue`'s 0-cells are
the objects of `∫X`, so distinct 0-cells of one copy can collapse and distinct copies share 0-cells.
`coproductPre_obj_injective`, `coproduct_path_fst` and `coproduct_exists_mapPath` are all **false**
for `glue`, so `Coproduct.lean` is not reusable for the completeness half.

**`SliceLabels` is forced, and `Glue` depends on it.** A 1-cell `g : a ⟶ b` of `P d` has to know
which arrows of `Over d` its endpoints name before one can say which objects of `∫X` the glued
1-cell runs between, and a `Polygraph` alone does not carry that. `Construction.objEquiv` recovers
it from a presentation (`ob d a := (objEquiv _).symm ((p d).at' ⟨a⟩)`), and `map_ob` then follows
from a *strict* compatibility square `(P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f`.
The endpoints of the `overlap` 2-cell match only propositionally, which is why that constructor
carries `eqToHom (gluePre_obj_map …)` on both sides.

## Strictness (A3b)

**A3b was pseudo-cocones, and they are gone.** `OverPseudoCocone`, `OverPseudoCoconeLoc`, their
`desc`/`descLoc`/`descMap`/`descIso`/`descLocIso`/`postcomp`/`toPseudo`/`ofFunctor` were built for
the reading of A4 in which the per-slice comparison comes from **inverting an equivalence** —
`Functor.inv` is a choice, so such a family is compatible only up to iso. A4 does not have that
shape: `L.ob d` bijective makes each `(p d).E` an isomorphism of categories, `strictInv` inverts it
on the nose, and `glueRetractCocone` is a plain `OverCocone`. The pseudo layer was consumed by
nothing and has been deleted; **do not rebuild it** — if a comparison looks like it needs one, the
bijective-labels hypothesis is missing instead.

| what | name | where |
|---|---|---|
| **a functor is determined by its slices** | `OverCocone.functor_ext` — the injectivity half of `overCoconeEquiv`, read on functors | `SliceFamily.lean:92` |
| **a fully faithful functor bijective on objects is invertible** | `strictInv`, with `comp_strictInv` and `strictInv_comp` both **equalities**; `comp_right_injective` cancels it, and `strictInv_square` inverts a commuting square to a commuting square, where a mere equivalence would give a mate | `Machinery/StrictInverse.lean:20`, `:29`, `:34`, `:41`, `:49` |

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
| … on the elements side | `W_eq_inverseImage_toElements` | `.../ElementsFibration.lean:87` |
| combinatorial test | `W_iff_crossPerm_eq_one (h) (f) : W K f ↔ crossPerm h f = 1` | `.../MergeGenerate.lean:100` |
| merges = codim-1 W-maps | `merge_iff (f) : merge K f ↔ W K f ∧ codim f = 1` | `.../MergeGenerate.lean:161` |
| **W-arrows are unique** | `eq_of_W : W K f → W K g → f = g` | `Concurrency/Grading/TopBead.lean:26` |

## Collapse of the localized base — why the slices are small

| what | name | where |
|---|---|---|
| the coarsest shape on `n` events | `ChainCat.topDims n : List ℕ+` (`= [n]` for `n>0`) | `Concurrency/Grading/TopBead.lean:32` |
| every shape merges to the top | `exists_W_to_top`, `totalTo`, `W_totalTo` | `.../TopBead.lean:60`, `:66`, `:69` |
| **every shape is merged onto by the run** | `exists_W_from_ones (b) (h : dimSum b = N) : ∃ u : zObj (𝟙^N) ⟶ zObj b, W Zbp u` | `.../TopBead.lean:76` |
| runs of the `n`-cube are `Sₙ` | `onesTopEquiv n : (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Perm (Fin n)` | `.../TopBead.lean:98` |
| homs exist iff coarser | `nonempty_hom_iff : Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ boundaries b.dims ⊆ boundaries a.dims` | `Concurrency/Grading/ChartHom.lean:505` |

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
| … the general fact it instantiates | `ObjectProperty.sigmaEquiv` (a hom-disjoint cover splits a category) | `Machinery/SigmaComponents.lean:44` |

The polygraph over those components is `zLocPresentation`, in the next table.

## Presentations that exist

| what | name | where |
|---|---|---|
| the cut polygraph | `ChainCat.Cut.poly : Polygraph` | `Concurrency/Presentation/CutPresentation.lean:101` |
| **`Ch Zbp` presented (UNLOCALIZED)** | `zCutPresentation : Presents Cut.poly ((Ch Zbp)ᵒᵖ)` | `.../CutPresentation.lean:201` |
| lifted to `Ch K` | `chPresentation`, `chCutPoly`, `chCutPresentation` | `Concurrency/Presentation/LiftPresentation.lean:37`, `:48`, `:52` |
| the Garside germ, presented | `germPresentation n : Presents (monoidPoly (PosGermRel n)) ((SingleObj (PosBraid n))ᵒᵖ)` | `Concurrency/Presentation/BasePresentation.lean:22` |
| … Artin spelling | `artinPresentation n` | `.../BasePresentation.lean:26` |
| **`Ch Zbp[W⁻¹]` presented** | `zLocPresentation : Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N)) ((W Zbp).op.Localization)` | `.../BasePresentation.lean:37` |
| … Artin spelling | `zLocArtinPresentation` (same, with `ArtinRel`) | `.../BasePresentation.lean:42` |
| … the assembly both go through | `zLocOfComponents (p : ∀ N, Presents (P N) ((AtStrands N).FullSubcategory))` | `.../BasePresentation.lean:31` |
| a presented monoid presents `SingleObj` | `presentedMonoidPresentation`, `monoidPoly` | `Machinery/Presentation/Monoid.lean` |
| the Segal/descent route (needs `IsSegal`) | `chLocPoly`, `chLocPresentation`, `hLocPoly`, `hLocPresentation`, `hLocActionPresentation` | `.../HAction.lean:62`, `:69`, `:278`, `:283`, `:289` |

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
`hasDiamonds_cube` (`Concurrency/Merge/CubeFaces.lean:984`) — says two words with the same
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

`Polygraph` (`Basic.lean:70`) is `V`, `Gen : V → V → Type`, `rel : HomRel (Paths (GenObj Gen))`;
`presented := Quotient rel`; `Word := Paths (GenObj Gen)`; `quot`. `Polygraph.Hom P Q` sends a
1-cell to a *word* of `Q`, `Polygraph` is a `Category` (**homogeneous** in the two universes, so a
morphism into something a universe up must be spelled `Hom`, not `⟶`), and
`Hom.functor`/`functor_id`/`functor_comp` give functoriality of `presented`. `Hom.ofPre`
(`Basic.lean:137`) builds a morphism from a map of generating quivers that kills the 2-cells — every
morphism below is built that way. `Polygraph.comap` reads `P`'s 2-cells on a quiver over `P`'s;
`comapIncl`, `comapHom`, `comapIncl_faithful`, `comapIncl_full` (`Basic.lean:235`, star-surjective +
0-cells injective), `quot_mapPath_congr` (`Basic.lean:247`, `Hom.ofPre`'s hypothesis upgraded from
`rel` to the congruence it generates) support it.
`Presents P C` (`Basic.lean:264`) is `E : P.presented ⥤ C` plus `E.IsEquivalence`; `ofDesc`
(`Basic.lean:358`) is the constructor; `transport` composes with an equivalence;
`eval`/`at'`/`arrow`/`evalPre`/`sound`/`eval_map_eq_lift`/`eval_mapPath`/`lift_evalPre_comp`
(`Basic.lean:310`, a copy of `P` interpreted through a functor) are the accessors, and
`Polygraph.lift_map_eq_of_quot_eq` (`Basic.lean:351`) is `sound`'s converse — how a completeness
proof carries a normal form across. `Presents.elements` (`Elements.lean:241`) presents `∫F`.
`Polygraph.coproduct` (`Coproduct.lean:44`) is the coproduct and `Presents.coproduct`
(`Coproduct.lean:151`) presents `Σ i, C i`; `coproductPre i`, `coproductIncl i` (the injection),
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
`Presents.restrict` and `Polygraph.Action` are in `Partial.lean`.

## Slices

`Machinery/Slice.lean` (above) is the only slice-theoretic file. **ABSENT elsewhere:** `Under`,
`Comma`, `CostructuredArrow` — zero occurrences. (`StructuredArrow` appears on six lines, all
inside Kan-extension proofs, none slice-theoretic.)

| what | name | where |
|---|---|---|
| **`Ch(Z)/d` is `Ch (⋁d)`** | `overToWedgeChains d : Over (zObj d) ⥤ Ch (⋁d)`, fully faithful and bijective on objects | `Concurrency/Merge/WedgeSlice.lean:20` |
| … as an equivalence | `overEquivWedgeChains d : Over (zObj d) ≌ Ch (⋁d)` | `.../WedgeSlice.lean:53` |
| … and it carries `W/d` to `W` | `over_W_eq_inverseImage : (W Zbp).over = (W ⋁d).inverseImage (overToWedgeChains d)` | `.../WedgeSlice.lean:58` |
| **`Ch (X ∨ Y) ≌ Ch X × Ch Y`** | `chConcatEquiv (h : (X ∨ Y).AdmitsAltitude)`, from `chConcat_full` + `chConcat_essSurj` (`Faithful` was already there, `Segal.lean:582`) | `Concurrency/Merge/WedgeSplit.lean:54`, `:24`, `:48` |
| … hypothesis-free for serial wedges | `serialChConcatEquiv (d e : List ℕ+)` | `.../WedgeSplit.lean:62` |
| **`W` splits with it** | `W_prod_eq_inverseImage_chConcat : (W X).prod (W Y) = (W (X ∨ Y)).inverseImage (chConcat X Y)`, from `W_chConcat_iff` | `.../WedgeSplit.lean:79`, `:72` |
| … the arithmetic under it | `permSum_eq_one_iff` | `Machinery/Braid/Sum.lean:57` |

`chConcat_full` is the one new piece of mathematics: `splitTarget` (`Degree.lean:144`, itself
hypothesis-free) splits the *source* of a wedge map wherever the target splits, and `splitObj` says
a chain of `X ∨ Y` splits in only one way, so the two splittings agree and the map is a
concatenation. `AdmitsAltitude` enters only through `splitObj`.

### Localized (B4) — `Concurrency/Merge/WedgeLocalize.lean`

| what | name | where |
|---|---|---|
| **the engine** | `isLocalization_chConcat : (chConcat X Y ⋙ Q).IsLocalization ((W X).prod (W Y))` | `:80` |
| … as an equivalence | `locChConcatEquiv (h) : (W X)ᴸ × (W Y)ᴸ ≌ (W (X ∨ Y))ᴸ` | `:89` |
| **the cons step** | `locChConsEquiv n rest : (W □n)ᴸ × (W ⋁rest)ᴸ ≌ (W ⋁(n :: rest))ᴸ` — hypothesis-free | `:99` |
| the slice reading | `isLocalization_overToWedgeChains`, `locOverEquivWedge d : ((W Zbp).over)ᴸ ≌ (W ⋁d)ᴸ` | `:109`, `:114` |
| **what C3 inducts on** | `locOverConsEquiv n rest` | `:122` |
| a one-bead slice is the cube | `locOverSingleton n : ((W Zbp).over (zObj [n]))ᴸ ≌ (W □n)ᴸ` (the right unitor `⋁[n] = □n ∨ □0`) | `:131` |
| pushing forward, localized | `locPushforward φ`, `locPushforwardFac`, `locPushforwardEquiv` | `:47`, `:53`, `:65` |
| **naturality, strict** | `chConcat_pushforward`, `chAppend_pushforward` | `:142`, `:190` |
| **naturality, localized** | `locChAppend_natural` | `:200` |
| the append splitting | `chAppend x y : Ch (⋁x) × Ch (⋁y) ⥤ Ch (⋁(x ++ y))`, `isLocalization_chAppend`, `locChAppendEquiv` | `:161`, `:176`, `:181` |

`pushforward` along an *iso* is an equivalence (`pushforward_isEquivalence`, `:39`) — the file's one
piece of general infrastructure, and what makes `chAppend` and the unitor work.

Older orientation, still useful:
- `chartHomEquiv (χ : ⋁b ⟶ □N) : (⋁a ⟶ ⋁b) ≃ {x : ⋁a ⟶ □N // Nonempty (⟨a,x⟩ ⟶ ⟨b,χ⟩)}` — `Concurrency/Grading/ChartHom.lean:53`
- `Coarser d d' := dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d` — `.../ChartHom.lean:335`
- `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` — `Precubical/Segal/Segal.lean:512`; `splitObj (h : (X ∨ Y).AdmitsAltitude) : Ch (X ∨ Y) ≃ Ch X × Ch Y` — `Split.lean:587`, with `chConcat_obj_splitObj` `:590`, `splitObj_chConcat_obj` `:596`
- `splitWedgeMorphism` — `Split.lean:604`; `splitTarget`, `splitAt` — `Concurrency/Grading/Degree.lean:144`, `:157`

In particular `Ch(Z)/[n] ≅ Ch(□n)`. That coincidence is a description, not a tool: `□n` is not
Segal, so the descent machinery neither applies nor is needed.

## Acyclicity, for the generating-set argument

| what | name | where |
|---|---|---|
| every endomorphism is the identity, **every K** | `ChainCat.endo_eq_id` | `Precubical/Chains/ChainSkeletal.lean:105` |
| bead count never increases | `ChainCat.dims_length_le_of_hom` | `.../ChainSkeletal.lean:112` |
| **a non-iso strictly drops the bead count** | `ChainCat.lt_dims_length_of_not_isIso` | `.../ChainSkeletal.lean:160` |
| `Ch K` is skeletal | `ChainCat.eq_of_hom_hom`, `le_antisymm` | `.../ChainSkeletal.lean:143`, `:152` |
| the grading | `codim`, `codim_comp`, `codim_eq_zero_iff`, `codim_eq_length_sub` | `Concurrency/Grading/Degree.lean:46`, `:75`, `:129`, `:53` |
| factorisation engine (`Ch Zbp` only) | `factor_ext`, `exists_factor`, `exists_first`, `exists_diamond` | `Concurrency/Grading/Coarser.lean:364`, `:388`, `:447`, `:456` |

These give `Generating (MaximalChains K)` by induction on bead count for every `K`, with no
finiteness and no acyclicity hypothesis. **ABSENT:** `MaximalChains` itself; it must be defined.

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

A4. Definition of `Glue X P L` for `P : D ⥤ Polygraph`, and `Presents (glue X L) (C[W_C⁻¹])`
assuming ∀ d, `Presents (P d) ((Over d)[W_D⁻¹])` naturally in d.

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
do not, so words that were not composable become composable and `Φ` stops being faithful. This
half is **formalized**: `not_nonempty_presents_glue` (`Machinery/Presentation/GlueRefutation.lean`),
with `D = Discrete PUnit`, `W = ⊥`, `X` terminal and `P` the polygraph `a ⇄ a'` whose 2-cell
relation is *total*. `Over d` has one object, so both 0-cells carry the same label
(`gluePt_false_eq_true` is `rfl`), and the winding number `windDesc` sends the glued loop to `1`
and the identity to `0` while the localization is thin.

Under `L.ob d` bijective, `(p d).E` is fully faithful **and** bijective on objects, so it is an
isomorphism of categories and `strictInv` inverts it on the nose (`Machinery/StrictInverse`).
Then the whole comparison is strict: `glueStep` is `hP` inverted by `strictInv_square` rather than
conjugated by a mate, `glueRetractCocone` is an `OverCocone` rather than a pseudo-cocone (which is
why the pseudo layer no longer exists), and both identities are **equalities** — `glueCounit` by
`OverCocone.functor_ext`, `glueUnit` by `Quotient.lift_unique'` checked on generators, where
`pInv` cancels `(p d).E`.  `presentsGlue` is then `Equivalence.mk` of the two.

A5. Generating (S : Set C) := ∀ c, ∃ s ∈ S, Nonempty (c ⟶ s). Definition of GlueOn S X P (copies over S, overlap relations for spans between elements of S, including self-spans), and theorem Generating S → presents (GlueOn S X P) (C[W_C⁻¹]). Prove it directly with the same universal-property argument, not by comparing with Glue. The content is that an assignment on S extends to a compatible family exactly when the overlap relations hold; spans always exist with apex `c` itself, which is what makes the extension well defined.

A6 (optional, do after Phase D if time permits). Overlap relations at maximal spans suffice, under a well-foundedness hypothesis on spans.

A7 (optional). If X w is a bijection for all w ∈ W_D, then X descends to X̄ on D[W_D⁻¹], C[W_C⁻¹] ≅ ∫X̄, and Glue X P is isomorphic to the pullback of Glue 1 P (the glued presentation of D[W_D⁻¹]) along ∫X̄ → D[W_D⁻¹] provided every generator of P d is the pushforward of a generator over its own target. State this; prove only if cheap. The hypothesis is exactly `InvertsMerges K` (`ElementsFibration.lean:102`), which `IsSegal` implies (`invertsMerges_of_isSegal`, `:131`), and the descent exists as `wedgeHomsDescend` (`:211`) with `isLocalization_chDescent` (`:220`).

### Phase B — Products and wedges

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
Three reasons, in order of weight: `Presents.prod` (B2) is binary and there is no `Presents.pi`, so
a `Fin`-indexed decomposition would strand C3, which has to combine per-bead presentations;
`⋁(n :: rest) = □n ∨ ⋁rest` is **definitional** (`serialWedge_cons` is `rfl`), so the cons splitting
carries no reindexing and no `eqToHom`, whereas `⋁a ≌ ∏ᵢ □aᵢ` is not definitional and would drag
`Fin a.length` through everything; and `IsLocalization.prod` (B1) then suffices.

The engine is `isLocalization_chConcat`: `chConcat ⋙ Q` *is* a localization of `Ch X × Ch Y` at
`(W X).prod (W Y)`, so every equivalence below is `Localization.uniq` applied to it and every
naturality square is `Localization.liftNatIso`.

**Naturality is stated for `chAppend`, not `chConcat`, and this is forced**: `splitTarget` splits a
wedge map at an *append* of the target, so a general map of shapes `⋁a ⟶ ⋁b` regroups the beads of
`a` into consecutive blocks, one per bead of `b` — it does **not** respect a cons splitting. The
strict square is `chAppend_pushforward`; `locChAppend_natural` is its localization. Turning that
into a `Polygraph.Hom` is **C2's** job, not B4's: B4 contains no polygraphs, and the 1-cells to be
sent to words are `P_cube`'s, which C1 has not built yet.

### Phase C — The functor P : Ch(Z) ⥤ Pres, for each braid presentation

C1. Presentations `P_cube n` of `(Over [n])[W_Z⁻¹]`, and the morphisms induced by maps `[m] ⟶ [n]`,
as one construction parametrized by the input presentation, not written twice.
The slice collapses, which is what makes this tractable: `exists_W_from_ones` gives a W-arrow
`1ⁿ ⟶ c` for every shape `c` with `dimSum c = n`, and that arrow is automatically a triangle over
any `u : c ⟶ [n]`, so every object of `Ch(Z)/[n]` is W-isomorphic to some `(1ⁿ, σ)`; `onesTopEquiv n`
says those `σ` are exactly `Perm (Fin n)`. Expect the answer to have the shape of
`hLocActionPresentation n` — the Garside simples acting on `Sₙ` — and compare against it as a check.

C2. Extend to wedges by P (∨ a) := ∏ᵢ P_cube aᵢ, functorial via B4, as a functor `Ch Zbp ⥤ Polygraph`.

C3. Theorem: ∀ d, presents (P d) ((Over d)[W_Z⁻¹]), naturally — exactly the hypothesis A4 and A5
consume. Instantiate for Garside; the instantiation should be a few lines each. If it isn't, the
parametrization in C1 is wrong, and C1 is what to fix.

### Phase D — Ch(K)

D1. `MaximalChains K : Set (Ch K)`, the chains with no non-identity outgoing arrow (it does not
exist yet); `Generating (MaximalChains K)` for every `K`, by induction on bead count via
`lt_dims_length_of_not_isIso` and `endo_eq_id`; and the main theorem, that for any P satisfying C3,
`Presents (GlueOn (MaximalChains K) (wedgeHoms K) P) (Ch(K)[W_K⁻¹])`.

D2. Corollaries for Garside and for Artin, both through the same mechanism.
`posBraid_equiv_artinPos` (`Machinery/Braid/Matsumoto.lean:243`) is the comparison — call it.

D3. Sanity check: for K = □ⁿ, MaximalChains K is a singleton and the glued presentation is P_cube n with no overlap relations; the theorem should reduce to the existing cube case up to a presentation isomorphism. If it does not reduce, say precisely where it fails rather than adjusting the statement to fit.
