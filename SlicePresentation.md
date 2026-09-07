# Presenting `Ch(K)[W⁻¹]` by gluing presentations of localized slices

**This is an executed brief.** The route it set out is finished and its plan changed twice while it
ran, so what survives here is the *dictionary* — where the machinery lives, and the landmines it
cost — not a plan. `ARCHITECTURE.md` is the map; `bd ready` is the status.

Names below are given without `file:line`: **grep the name**. Anything the tree does not carry has
been deleted from this file rather than repointed at its nearest surviving relative.

## The outcome

`BraidPresentation.presentsBr K : Presents (p.Br K) ((W K).Localization)` presents `Ch(K)[W⁻¹]` for
every `K`, with **no hypothesis on `K`**, where

```
p.Br K := Limits.colimit (Polygraph.elementsPoly (wedgeHoms K) p.fam)
```

is one copy of the slice polygraph per chain of `K`, glued along the arrows of `Ch K`. The slice
family is **inherited from the base** (`slicePolyFunctor` / `slicePresentationOf`), so the whole
construction is parametric in a presentation of the braid monoids, and `germBP` / `artinBP` are two
values of one argument rather than two constructions.

Underneath it, hypothesis-free in `K` and stated for an arbitrary `∫X`:
`Polygraph.presentsSliceColimit X V p hP hthin R` (`Machinery/Presentation/Glue.lean`).

## The setting

`Ch(K) ⥤ Ch(Z)` is a discrete fibration — `Ch K` is the category of elements of a presheaf
`wedgeHoms K` on `Ch Z` — and both categories carry the bead merges, with `W K` the inverse image of
`W Zbp`. Localization is mathlib's `CategoryTheory.Localization` at a `MorphismProperty`.

The two mathematical facts the route rests on:

1. **Slices agree.** For every `c`, the induced `Ch(K)/c ⥤ Ch(Z)/F(c)` is an isomorphism of
   categories carrying `W K /c` to `W Zbp /F(c)`, so the localized slices agree.
2. **A localization is the colimit of its localized slices** — equivalently, and this is the form
   that is formalized, a functor `C[W⁻¹] ⥤ E` *is* a family of functors `(C/c)[W⁻¹] ⥤ E`
   compatible with postcomposition (`overCoconeLocEquiv`).

Gluing then puts a copy of `P d` over every object of `∫X`, with the arrows of `∫X` supplying the
overlaps. That is exactly a colimit, and it is built as one.

---

# Repo dictionary

## The two categories, and the fibration

| what | name | where |
|---|---|---|
| chains of `K` | `ChainCat.Obj K`, notation `Ch K` | `Precubical/Chains/Category.lean` |
| an object | `⟨dims : List ℕ+, map : ⋁dims ⟶ K⟩` | ” |
| a morphism | `⟨φ : ⋁a.dims ⟶ ⋁b.dims, w : φ ≫ b.map = a.map⟩` | ” |
| the terminal `BPSet` | `CubeChains.Zbp`, `isTerminalZbp` | `Precubical/Basic/Terminal.lean` |
| **F, the projection** | `ChainCat.toChZ (X : BPSet) : Ch X ⥤ Ch Zbp` | `Concurrency/Merge/MergeClass.lean` |
| **X, the presheaf** | `ChainCat.wedgeHoms K : (Ch Zbp)ᵒᵖ ⥤ Type`, acting by precomposition (`wedgeHoms_map`) | `Concurrency/Presentation/ElementsFibration.lean` |
| the elements description | `toElements K`, `chEquivElements K : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ`, `chOpEquivElements K` | ” |
| shapes as chains of `Zbp` | `zObj (d : List ℕ+) : Ch Zbp`, `zHom` | `Concurrency/Merge/TotalMerge.lean` |
| a morphism of `Ch Zbp` is a bare wedge map | `serialWedgeFullyFaithful` | `Concurrency/Merge/MergeClass.lean` |

**Op placement — the single biggest hazard.** `wedgeHoms K` carries its `ᵒᵖ` on the *source* (it is a
presheaf on `Ch Zbp`). `toElements`/`chEquivElements` carry it on the *whole* `Elements` category,
with `Ch K` bare on the left; `chOpEquivElements` moves it to the left instead. Inside
`toElements.obj` both `op`s are explicit: `op ⟨op (zObj a.dims), a.map⟩`. Net effect: `Ch K ⥤ Ch Zbp`
is a discrete **fibration** (slices *over* an object agree), even though mathlib's `Elements` is the
opfibration convention. Do not re-derive this; use the table.

`toElements K ⋙ (CategoryOfElements.π (wedgeHoms K)).leftOp = toChZ K` is **not `rfl`**. The
projection sends `a` to `zObj a.dims`, whose map to `Zbp` is `isTerminalZbp.from (⋁a.dims)` on the
nose, while `toChZ` sends it to `a.map ≫ isTerminalZbp.from K`; those agree only because `Zbp` is
terminal, so the equation is `Obj.eq_of_dims` and it is `toElements_comp_π`. `Functor.ext`'s
morphism obligation there wants **`hom_ext' rfl`**: `simp` leaves
`x.φ = eqToHom _ ≫ x.φ ≫ eqToHom _`, whose `eqToHom`s are identities definitionally but not at
`simp`'s reducible transparency, so `simp only [eqToHom_refl, …]` reports *no progress*. The instance
`(toChZ K).IsDiscreteFibration` is that equation transported.

**ABSENT in mathlib:** any discrete-fibration predicate. `CategoryTheory/FiberedCategory/` has
`Functor.IsPreFibered`/`IsFibered` only, and this repo does not import it.

## Discrete fibrations (`Machinery/Slice.lean`)

| what | name |
|---|---|
| the predicate | `Functor.IsDiscreteFibration F`: `Over.post F : Over c ⥤ Over (F.obj c)` is an equivalence for every `c` |
| closure | equivalences are; composites are |
| `W` on the two slices | `MorphismProperty.over_inverseImage` — `rfl`, and no hypothesis on `F` |
| **the example** | `CategoryOfElements.π_leftOp_isDiscreteFibration` for `X : Cᵒᵖ ⥤ Type w` |

This is the one place the `op`-juggling lives. Its client is `toElements_comp_π`, which makes
`toChZ K` a discrete fibration for **every** `K`, whence `locOverEquivBase`. `Glue.lean` does *not*
use the predicate: it works concretely with `(π X).leftOp` and `elementsLiftOver`.

## The localized slices (`Machinery/Localization/SliceLocalize.lean`)

| what | name |
|---|---|
| localization pulls back along an equivalence | `Functor.IsLocalization.of_inverseImage` |
| postcomposition, localized | `overMapLoc W u` — a `Construction.lift`, hence **strict**: `overMapLocFac`, `overMapLoc_id`, `overMapLoc_comp` are equalities |
| `W.over` respects isos | `respectsIso_over`; at the base, `respectsIso_W` (`Merge/MergeGenerate.lean`) needs no discharging |
| any localization below is one above | `isLocalization_post_comp` |
| **the slices agree** | `sliceLocEquiv F W c : ((W.inverseImage F).over c)ᴸ ≌ (W.over (F.obj c))ᴸ` |

**`sliceLocEquiv` is existence only, and that is the whole lesson of it.** It is
`Localization.uniq`, which is **opaque on objects**, while `Presents.ofDesc` takes a *prefunctor*, so
anything that has to interpret cells needs a comparison that is strict on objects. `elementsLift`
(`Glue.lean`) writes that inverse down instead: it is a genuine functor,
`elementsLift ⋙ π.leftOp = Over.forget d` holds by `rfl`, `glueSliceEval` is its
`Construction.lift`, and `elementsLift_inverts` supplies the is-a-localization half directly. Use
`sliceLocEquiv` to know the categories agree; never to compute in them.

## Slice cocones (`Machinery/Localization/SliceFamily.lean`)

No hypothesis on `W` at all — not even `ContainsIdentities`.

| what | name |
|---|---|
| a compatible family | `OverCocone C E`: `obj c : Over c ⥤ E`, `w u : Over.map u ⋙ obj c = obj c'` |
| its two directions | `OverCocone.ofFunctor Φ` (`Over.forget c ⋙ Φ`), `OverCocone.desc` (read at `Over.mk (𝟙 c)`) |
| **unlocalized** | `overCoconeEquiv : (C ⥤ E) ≃ OverCocone C E` |
| a strict universal property is a bijection | `Localization.StrictUniversalPropertyFixedTarget.functorEquiv` |
| a localized family | `OverCoconeLoc W E` |
| the two halves | `isInvertedBy_iff_over`, `coconeLocEquiv` |
| **the correspondence** | `overCoconeLocEquiv W : (W.Localization ⥤ E) ≃ OverCoconeLoc W E`, with `overCoconeLocEquiv_apply` |
| **a functor is determined by its slices** | `OverCocone.functor_ext` — the injectivity half, read on functors |
| a 2-cell carried as a 1-cell | `NatTrans.toArrow`, `Arrow.isThin`, `Arrow.mk_eq_mk_of_thin`, `Functor.mapArrow_comp` |

**Why a bijection and not an equivalence of categories.** `Over.map` is strictly functorial
(`Over.mapId_eq`, `Over.mapComp_eq`) and `overMapLoc` inherits that from `Construction.lift`, so the
compatibility is an *equality* of functors and both round trips are equalities. The only `eqToHom`
in the file is inside `OverCocone.desc`, where `(Over.map u).obj (Over.mk (𝟙 c'))` is
`Over.mk (𝟙 c' ≫ u)` rather than `Over.mk u`.

**There is no pseudo-cocone, and none is needed.** A comparison that is only an *isomorphism* is
read as a cocone valued in `Arrow E` (`NatTrans.toArrow`), whose two projections are the functors
being compared; carrying the 2-cell as a 1-cell keeps every compatibility an equality. That is how
the counit of the glue comparison is assembled.

## The glued polygraph (`Machinery/Presentation/Glue.lean`)

The glued polygraph **is** `Limits.colimit (elementsPoly X P)` — no bespoke `V`/`Gen`/`rel`, no label
structure, no copy-inclusion soundness lemma. `elementsPoly X P = (π X).leftOp ⋙ P` is the slice
diagram, `Polygraph` has every colimit (`Coequalizer.lean`, `ColimitCells.lean`), and the universal
property on *presented* categories comes straight from `catHomEquiv`. The polygraphs are the
standard ones — generators to generators, 2-cells a `Type` with a source and a target word — so
results about them in the literature are citations, not analogies.

| what | name |
|---|---|
| the base of a copy, and the diagram | `eltBase X c = (π X).leftOp.obj c`, `elementsPoly X P` |
| the copy inclusion, on presented categories | `glueInclFun X P c`, `glueInclFun_naturality` |
| **the universal property** | `glueLift`, `glueInclFun_lift`, `glue_functor_ext` |
| **the cartesian lift** | `elementsLift X d x : Over d ⥤ (X.Elements)ᵒᵖ`, with `elementsLift_comp_π` (`rfl`), `elementsLift_post` (a strict **equality**, from `elements_snd_map`), and `elementsLift_inverts` |
| … on slices | `elementsLiftOver X c : Over (F c) ⥤ Over c`, the strict inverse of `Over.post F`: `elementsLiftOver_forget`, `elementsLiftOver_post`, both `rfl` |
| … localized | `glueSliceEval X W d x`, `glueSliceEval_fac` |
| **the lift is functorial in the base** | `elementsLift_over_map`, and localized `overMapLoc_comp_glueSliceEval` |
| `overMapLoc` on objects | `overMapLoc_obj` |
| **the entry, chosen without uniqueness** | `sliceTop` (a 0-cell naming `Q (𝟙 d)`, from `EssSurj` alone) and `sliceTopIso`; `sliceRetObj y = (P.map y.hom).functor.obj (sliceTop y.left)`, with `sliceRetObj_push` — `P`'s functoriality — and `sliceRetObjIso` from `hP` and `overMapLoc_top` |
| **inverting a slice presentation** | `sliceRet`, `sliceRet_square` (an **equality**, and free), `sliceRetIso` for one composite, `sliceUnitIso` for the other |
| **Φ** | `glueLeg`, `glueLeg_naturality`, `glueDesc` |
| **a copy, read by Φ** | `glueIncl_desc` — the bridge every spelling argument runs through |
| **the retraction Ψ** | `glueRetractPre`, `glueStep`, `glueRetractPre_inverts`, `glueRetractCocone`, `glueRetract` (a `Construction.lift`) with `glueRetract_fac`, `glueRetract_forget` |
| **η** | `glueSliceEval_retract` (the mirror of `glueIncl_desc`), `sliceUnitArrow`, `sliceUnitArrow_square`, `glueUnitLeg`, `glueUnitArrow`, `glueUnitArrow_left`/`_right`, `glueUnitArrow_isIso`, `glueUnit` — only an *isomorphism*, descended along the colimit as an `Arrow`-valued functor |
| **ε** | `sliceRetComp_square`, `sliceRetArrow`, `sliceRetArrow_square`, `glueCounitStep`, `glueCounitCocone`, `glueCounitDesc_left`/`_right`, `glueCounitArrow_isIso`, `glueCounit` — only an *isomorphism*, carried as an `Arrow`-valued cocone |
| **`colimit (elementsPoly X P)` presents `(∫X)[W⁻¹]`** | `presentsSliceColimit X W p hP hthin` |
| … read on the colimit of the localized slices | `overLocFunctor`, `overLocCocone`, `isColimitOverLocCocone`, `presentsColimitOfLocalizedSlices`, `colimitPresentedEquivColimitLoc` (`SliceColimit.lean`) |
| **two 0-cells naming one slice object, and the colimit presenting anyway** | `presents₂_not_injective`, `presentsGlue₂` (`GlueRefutation.lean`) |

**The word problem is a retraction, not a normal form.** The target is not thin, so there is nothing
to rewrite words *to*: `Ψ` is an honest cocone on the slices, and both comparisons are checked one
copy at a time. Neither is an equality — a localized slice is thin but never skeletal, since a
`W`-arrow makes distinct objects isomorphic, and a `Presents` may name one object with several
0-cells.

**`presented` is a left adjoint (`presentedAdj`), and that does not give the theorem.** Strict
colimits do not respect levelwise equivalence: `1 ⇉ walking-iso` and `1 ⇉ 1` have levelwise
equivalent diagrams and inequivalent strict colimits, `colim` being a 1-functor that cannot see a
natural isomorphism. `Glue` gets past this only because its target is a *fixed* category, so both
isomorphisms can be carried as `Arrow`-valued functors rather than transported through a colimit.

**Nothing is asked of the 0-cells, and nothing may be.** `hP` is an equality of *objects*, and that
is already enough: it pins what each pushed 0-cell names, so `sliceRetObj` — the identity of a
slice object's own domain, pushed along it — enters every object without a choice being made twice.

*Why no strict unit.* Several 0-cells may name one slice object, and they need not be glued.
`GlueRefutation.lean` builds that data (`D = Discrete PUnit`, `W = ⊥`, `X` terminal, `P₂` the
polygraph `a ⇄ a'` with a *total* 2-cell relation, `Over d` a single object): `false` and `true`
name the one object (`presents₂_not_injective`) and stay distinct in the colimit, so `Ψ ∘ Φ` sends
both to whichever `sliceTop` chose and can only be *isomorphic* to `𝟭`. The colimit presents all the
same (`presentsGlue₂`).

*Why the copies' 0-cells, not their image.* Flattening them onto `∫X` would identify `false` with
`true` in that same data, making words that were not composable composable and inventing a loop.
`Presents.restrict` cannot repair that either — `Convex.respectsIso` (`Partial.lean`) says a convex
property is closed under isomorphism, so it can never cut a category down to a skeleton.

**State each step as an equality of *functors*, then descend once.** Functor equations have no
implicit object arguments, so `rw` works on them normally; the landmine below only bites once the
objects are pinned. Attempting the same proofs morphism-first does not work at all: `rw` *and*
`simp only` both fail to fire on a `Functor.map`-headed pattern that is printed verbatim in the goal.

**Landmine: `rw`/`simp` cannot apply `Category.assoc` in `W.Localization`.** When a composite's
middle object is spelled two ways, the two are defeq but `kabstract`'s keyed matching runs at
`instances` transparency and fails. `simp only [Category.assoc]` then makes *no progress* and reports
no unused-argument warning, which reads like the lemma fired. Marking the offending def
`@[reducible]` does **not** help: the mismatch is in the `≫`'s implicit *object* argument, not in a
head symbol. The cure is term mode, which elaborates at default transparency; `eqToHom_conj_id`
(`SliceFamily.lean`) is the one sandwich combinator that survived, for crusts that are identities
*up to defeq*, which `eqToHom_refl` cannot see.

**A definition built inside a tactic block can be correct and useless.** `Localization.Lifting`
witnesses supplied as `letI` inside a `by` block make the definition's components unnameable from
outside, so `Localization.liftNatTrans_app` cannot be applied to it *at all* — and the symptom is the
familiar one, a lemma that visibly ought to apply refusing to. This is **not** the transparency
hazard above; the cause and the cure are unrelated. The cure is to hoist the witnesses to `instance`s
and write the definition in term mode. Prefer term mode for any definition whose components later
proofs will need to compute with.

**The overlap identifications are sound because the cartesian lift is functorial in the base.**
`elementsLift_over_map` is the whole content: lifting at `x` after postcomposing with `f` is lifting
at `f* x`. Both it and its localized form are *equalities* of functors, so the colimit's own
`colimit.w` carries them with no transport argument.

## The class W

| what | name | where |
|---|---|---|
| a single bead merge | `ChainCat.merge (X : BPSet) : MorphismProperty (Ch X)` | `Concurrency/Merge/MergeClass.lean` |
| the class | `ChainCat.W X = (merge X).multiplicativeClosure` | ” |
| multiplicative | `instance : (W X).IsMultiplicative` | ” |
| **`W K = F⁻¹ (W Zbp)` is a THEOREM** | `W_eq_inverseImage_toChZ` | `Concurrency/Merge/MergeGenerate.lean` |
| … on the elements side | `W_eq_inverseImage_toElements`, `W_eq_inverseImage_elements` | `.../ElementsFibration.lean`, `.../SlicePresentation.lean` |
| combinatorial test | `W_iff_crossPerm_eq_one`, `W_iff_monotone_coordMap` | `.../MergeGenerate.lean` |
| merges = codim-1 W-maps | `merge_iff` | ” |
| **W-arrows are unique** | `eq_of_W` | `Concurrency/Grading/TopBead.lean` |

## Collapse of the localized base — why the slices are small

| what | name | where |
|---|---|---|
| the coarsest shape on `n` events | `ChainCat.topDims n` (`= [n]` for `n>0`) | `Concurrency/Grading/TopBead.lean` |
| every shape merges to the top | `exists_W_to_top` | ” |
| **every shape is merged onto by the run** | `exists_W_from_ones (b) (h : dimSum b = N) : ∃ u : zObj (𝟙^N) ⟶ zObj b, W Zbp u` | ” |
| runs of the `n`-cube are `Sₙ` | `onesTopEquiv n` | ” |
| homs exist iff coarser | `nonempty_hom_iff` | `Concurrency/Grading/ChartHom.lean` |

**Arrows in `Ch Zbp` run finer ⟶ coarser.** `Over d` is therefore the category of *refinements* of
`d`, and a refinement of a concatenation respects the junction.

`exists_W_from_ones` is the fact that makes the *slice* collapse: the `W`-arrow `1ⁿ ⟶ c` it produces
is automatically a triangle over any `u : c ⟶ d`, so every object of `Ch(Z)/[n]` is `W`-isomorphic to
one of the form `(1ⁿ, σ)` with `σ : 1ⁿ ⟶ [n]`, i.e. to a run. No `IsSegal` hypothesis is involved
anywhere in this argument.

## The localized base

| what | name | where |
|---|---|---|
| objects at a strand count | `AtStrands (N : ℕ) : ObjectProperty ((W Zbp).op.Localization)` | `Concurrency/Presentation/BaseComponent.lean` |
| the run object | `runBase N : (SingleObj (PosBraid N))ᵒᵖ ⥤ (W Zbp).op.Localization` | ” |
| **each component is one object** | `strandComponentGarside N`, `strandComponentArtin N` | ” |
| **no homs across strand counts** | `isEmpty_loc_hom` | `Concurrency/Presentation/Retraction.lean` |
| every hom is a positive braid | `homEquivPosBraid` (+ `_comp`, `_id`, `_Q`) | ” |
| loops at the run | `RunLoops N`, `runBraidEquiv N : PosBraid N ≃* RunLoops N` | ” |
| **the base is the disjoint union** | `strandDecomposition`, from `exists_atStrands` + `atStrands_eq_of_hom` | `.../BaseDecomposition.lean` |
| … the general fact it instantiates | `ObjectProperty.sigmaEquiv` | `Machinery/SigmaComponents.lean` |

## Presentations that exist

| what | name | where |
|---|---|---|
| the cut polygraph, and `Ch Zbp` presented (UNLOCALIZED) | `Cut.poly`, `zCutPresentation` | `Concurrency/Presentation/CutPresentation.lean` |
| lifted to `Ch K` | `chPresentation`, `chCutPoly`, `chCutPresentation` | `.../LiftPresentation.lean` |
| the Garside germ, presented | `germPresentation n`, and `artinPresentation n` | `.../BasePresentation.lean` |
| **the input bundle** | `BraidPresentation` (`P`, `comp`, `vertex`), `ofMonoids`, `germBP`, `artinBP`, `BySimples` | ” |
| **`Ch Zbp[W⁻¹]` presented** | `BraidPresentation.base`, assembled by `zLocOfComponents` | ” |
| … and the converse cut | `zLocComponent` — an arbitrary base presentation restricted to one strand component | ” |
| a presented monoid presents `SingleObj` | `presentedMonoidPresentation`, `monoidPoly` | `Machinery/Presentation/Monoid.lean` |
| the Segal/descent route (needs `IsSegal`) | `chLocPoly`, `chLocPresentation`, `hLocPoly`, `hLocPresentation`, `hLocActionPresentation` | `.../HAction.lean` |

`hLocActionPresentation n : Presents (hLocPoly n) ((PosBraidAction n)ᵒᵖ)` is about `Hbp □n`, the
**decorated** cube. `Ch(□n)[W⁻¹]` is *not* equivalent to `PosBraidAction n`: at `n = 2` both have two
objects, but `End` in `PosBraidAction 2` is `PosPureBraid 2` (`endEquivPosPure`), which contains
`σ₁² ≠ 1`, while `Ch(□²)[W⁻¹]` has trivial endomorphisms — its three objects are `t = ([2], 𝟙)`,
`r₁ = ([1,1], cubeMerge)` and `r₂ = ([1,1], cubeReorder)`, with `r₁ ⟶ t` and `r₂ ⟶ t` and nothing
else, so inverting the one merge `r₁ ⟶ t` adds `t ⟶ r₁` and creates no loop. Nothing maps *into* `r₁`
or `r₂`. `not_nonempty_equiv_posBraidAction` is that statement.

Nor is the descent shape available at the undecorated cube: `Ch(□n)[W⁻¹] = ∫` of a `PosBraid n`-set,
compatibly with the projection, requires `wedgeHoms (□n)` to invert merges, and at `n = 2` that map
sends one element to two. Consistently, `not_isSegal_cube_two` proves `□²` is not Segal.

**`Ch(□n)[W⁻¹]` is thin, and it is the weak order.** `locCube_isThin` says the localization is a
poset, and `locCubeWeakOrder n : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ` names which poset: the
right weak (Bruhat) order on `Perm (Fin n)`, read backwards. A hom exists exactly when the two
chains' crossing permutations compare, and is then unique (`nonempty_loc_hom_iff`).

Thinness is not automatic, and the worry that makes the opposite guess tempting is real:
localization does not preserve thinness in general, because a zigzag `c → x ← y → …` is a new
morphism. What kills the zigzags here is `crossLen`. It drops by `permLen (crossPerm f)` along `f`
(`crossLen_eq_add`, `Concurrency/Merge/CubeCrossing.lean`) and is preserved by `W`, so in any loop
every forward arrow lies in `W`: **every endomorphism of `Ch(□n)[W⁻¹]` is a zigzag of merges.** That
much the grading gives alone, and it is where this project locates the braiding — but the merge order
is simply connected, which is the content of `CubeThin.lean`. Every chain is entered from its class's
run by a merge (`classRunIso`), so a morphism is read between runs (`conjRun`), where a merge becomes
the identity and a refinement becomes the fraction its target names (`conjRun_map_eq`); hence every
morphism is a word in the atom steps (`exists_word_of_hom`), and `word_unique` — an induction on
`permLen`, a shared first cut reducing and distinct cuts closing by the codimension-two diamond
`hasDiamonds_cube` — says two words with the same endpoints agree.

**`n = 2` is therefore not the degenerate case it looks like**, and may be extrapolated from.
`WeakOrder 2` is the two-element chain, and the computation above *is* `(WeakOrder 2)ᵒᵖ`: inverting
the one merge makes `r₁ ≅ t`, leaving `[r₂] ⟶ [t]` and nothing else. What is special at `n = 2` is
only that no atom composes with another.

The consequence is that a cube slice presentation carries no word problem at all: `Presents.ofThin`
presents a thin category from a spanning family of generators on a covering family of 0-cells and
nothing else, and `cubePresentation n` is that — 0-cells the runs, generators the atom steps, one per
descent.

## The polygraph machinery (`Machinery/Presentation/`)

`Polygraph` (`Basic.lean`) is `V`, `Gen : V → V → Type`, `rel : HomRel (Paths (GenObj Gen))`;
`presented := Quotient rel`; `Word := Paths (GenObj Gen)`; `quot`.

`Polygraph.Hom P Q` sends a cell to a cell in **every** dimension — a 1-cell to a 1-cell, a 2-cell to
a 2-cell with the pushed-forward boundary, both boundary conditions equations of *words* on the nose.
`Polygraph` is a `Category` (**homogeneous** in the two universes, so a morphism into something a
universe up must be spelled `Hom`, not `⟶`), and `Hom.functor`/`functor_id`/`functor_comp` give
functoriality of `presented`. `Polygraph.Spelling` is the strictly weaker gadget a *comparison* needs
and a `Hom` cannot give: a 1-cell of `P` spells a whole **word** of `Q` — an Artin generator as a
product of Garside atoms. It induces a functor and nothing more; there is no category of spellings.

`Polygraph.comap` reads `P`'s 2-cells on a quiver over `P`'s (`ComapRel`, `comap_homRel_iff`,
`Hom.quot_map_congr`), which is what both `elements` and `restrict` are.

`Presents P C` (`Basic.lean`) is `E : P.presented ⥤ C` plus `E.IsEquivalence`; `ofDesc` is the
constructor; `transport` composes with an equivalence;
`eval`/`at'`/`arrow`/`evalPre`/`sound`/`eval_map_eq_lift`/`eval_mapPath`/`lift_evalPre_comp` are the
accessors, and `Polygraph.lift_map_eq_of_quot_eq` is `sound`'s converse: two words with the same
interpretation are already equal in the quotient. It is **not** a normal-form device — the word
problem here is discharged by a retraction. `Presents.elements` (`Elements.lean`) presents `∫F`;
`Presents.ofThin` is the thin case, where there is no word problem to discharge.

`Polygraph.coproduct` (`Coproduct.lean`) is the coproduct and `Presents.coproduct` presents
`Σ i, C i`; `coproductPre i`, `coproductIncl i`, `coproduct_exists_mapPath` are its API. Its 1-cells
are the **indexed inductive** `CoproductGen`, not a `Σ'`-transport, so `Gen` lands in
`Type (max t u' w)` — a universe bump the callers have to carry (nil for a `ℕ`-indexed family of
`Type 0` polygraphs). Nothing here is named `sigma`: mathlib's `Sigma` is the *category* side, and
`Σ i, (P i).V` is only how the 0-cells happen to be spelled.

`Polygraph.prod` and `Presents.prod` (`Product.lean`) have 1-cells the indexed inductive `ProdGen`
(one factor's, the other coordinate frozen) and 2-cells `ProdRel.left`/`.right`/**`.interchange`**;
`exists_normalForm` — every word is a `P`-word then a `Q`-word — is what interchange buys and the
whole of completeness. Without the interchange squares the words present a free *product*.
**A bare `Quiver.Path` does not say which category its `≫` is in**, and `(prod P Q).Gen` and
`ProdGen P Q` are two defeq spellings of one thing, so a `Functor.map_comp` pins the middle 0-cell to
one of them and nothing matches afterwards. `Product.lean` keeps whole words inside one `quot.map`
and moves through `quot_comp_congr`, whose 0-cells are variables; `prodLeft` and `prodRight` are
`abbrev` so the two spellings unify at `rw`'s transparency. Expect the same in any further polygraph
construction.

`Presents.restrict`, `partialElements`, `PartialFam`/`partialElementsMap` and `partialActionFunctor`
are in `Partial.lean`; `Polygraph.op`/`Presents.op` in `Opposite.lean`; `Presents.Map` in
`Comparison.lean`; `colimitCells` and the joint surjectivity of the colimit legs in
`ColimitCells.lean`.

## Slices of the base

`Machinery/Slice.lean` (above) is the only slice-theoretic file. **ABSENT elsewhere:** `Under`,
`Comma`, `CostructuredArrow` — zero occurrences. (`StructuredArrow` appears only inside
Kan-extension proofs.)

| what | name | where |
|---|---|---|
| **`Ch(Z)/d` is `Ch (⋁d)`** | `overToWedgeChains d`, fully faithful and bijective on objects, hence an `IsEquivalence` | `Concurrency/Merge/WedgeSlice.lean` |
| … and it carries `W/d` to `W` | `over_W_eq_inverseImage` | ” |
| **`Ch (X ∨ Y) ≌ Ch X × Ch Y`** | `chConcat_isEquivalence (h : (X ∨ Y).AdmitsAltitude)`, from `chConcat_full` + `chConcat_essSurj` | `Concurrency/Merge/WedgeSplit.lean` |
| **`W` splits with it** | `W_prod_eq_inverseImage_chConcat`, from `W_chConcat_iff` | ” |
| … the arithmetic under it | `permSum_eq_one_iff` | `Machinery/Braid/Sum.lean` |
| **the engine** | `isLocalization_chConcat : (chConcat X Y ⋙ Q).IsLocalization ((W X).prod (W Y))` | `Concurrency/Merge/WedgeLocalize.lean` |
| … as an equivalence | `locChConcatEquiv`, and the hypothesis-free cons step `locChConsEquiv n rest` | ” |
| the slice reading | `isLocalization_overToWedgeChains`, `locOverEquivWedge d` | ” |

`chConcat_full` is the one new piece of mathematics: `splitTarget` (`Grading/Degree.lean`, itself
hypothesis-free) splits the *source* of a wedge map wherever the target splits, and `splitObj` says a
chain of `X ∨ Y` splits in only one way, so the two splittings agree and the map is a concatenation.
`AdmitsAltitude` enters only through `splitObj`.

The cons splitting is **binary and recursive, not `Fin`-indexed**, and `Functor.IsLocalization.pi` is
never used: `⋁(n :: rest) = □n ∨ ⋁rest` is **definitional** (`serialWedge_cons` is `rfl`), so it
carries no reindexing and no `eqToHom`, whereas `⋁a ≌ ∏ᵢ □aᵢ` is not definitional and would drag
`Fin a.length` through everything. A naturality square would have to be stated for an **append**, not
a cons: `splitTarget` splits at an append of the target, so a general `⋁a ⟶ ⋁b` regroups the beads of
`a` into consecutive blocks, one per bead of `b`, and does **not** respect a cons splitting.

> **"The slice is a product of cube slices" is a description of the category, not a construction
> step.** Treating it as one produced a second presentation chain beside the inherited one, and that
> chain has been deleted. `locChConsEquiv` and `Presents.prod` stay in the tree as results.

## The slice family that is actually used

Inherited from the base, in one step and with the shape of `d` never taken apart. The runs over `d`
are a downward-closed set of permutations for the right weak order (the exchange
`exists_runOver_mul_adjT`, iterated), so `PosBraid N` acts on them **partially** (`weakActionOn`),
`sliceFibre d` is the presheaf that action gives on the localized base, and its defined part *is* the
localized slice, reversed (`definedSliceLoc`). Hence

```
slicePolyFunctor p := (p.elements (sliceFibre ·)).restrictPoly (defined ·) ⋙ opFunctor
```

is the base's own cells lifted — a 1-cell is a generator of `p` acting on a run, a 2-cell a relation
of `p` holding there — parametric in `p` by construction.

| what | name |
|---|---|
| the family, and its presentations | `slicePolyFunctor p`, `slicePresentationOf p` |
| the naturality `hP` | `slicePoly_hP` — free, since the 0-cells name their own slice objects (`sliceCellOver`), pushing them is `Over.map`, and `locOver_isThin` settles the morphism half by `Subsingleton.elim` |
| **the theorem** | `presentsChainsSliceColimit K p`, and `BraidPresentation.Br` / `.presentsBr` with the base bundled |
| the transport to `Ch K` | `locEquivElements K`, `locOverEquivBase K c` |
| the cells of the colimit, read on a leg | `glueV`, `glueE`, `glueV_leg`, `glueE_leg`, `at_glueV`, `arrow_glueE` |
| the two named values | `presentsChainsGarsideColimit K`, `presentsChainsArtinColimit K` |

Functoriality of the family is **lax and not natural** — a step undefined over `d'` can be defined
over `d` (over `𝟙²` the atom is undefined; over `[2]` it is) — which is exactly what a morphism of
polygraphs asks for and what `PartialFam` / `partialElementsMap` consume.

**The presentation does not present the vertex monoids.** `End` at a chain is a stabilizer
(`endEquivStabilizer`), and `end_not_generated_by_simples` says a stabilizer need not be spanned by
the generators sitting at its object: in `PosBraidAction n` the only generator that is a loop is the
identity, while the loops are `PosPureBraid n`. The pure braids are a computed invariant of the
presented category, not a sub-presentation of it.

## Acyclicity

| what | name | where |
|---|---|---|
| every endomorphism is the identity, **every K** | `ChainCat.endo_eq_id` | `Precubical/Chains/ChainSkeletal.lean` |
| bead count never increases | `ChainCat.dims_length_le_of_hom` | ” |
| **a non-iso strictly drops the bead count** | `ChainCat.lt_dims_length_of_not_isIso` | ” |
| `Ch K` is skeletal | `ChainCat.eq_of_hom_hom` | ” |
| **maximal chains, and that coarsening terminates** | `ChainCat.MaximalChains K` and `ChainCat.exists_hom_maximal` — induction on bead count, no finiteness and no acyclicity hypothesis | ” |
| the grading | `codim`, `codim_comp`, `codim_eq_zero_iff`, `codim_eq_length_sub` | `Concurrency/Grading/Degree.lean` |
| factorisation engine (`Ch Zbp` only) | `factor_ext`, `exists_factor`, `exists_first`, `exists_diamond` | `Concurrency/Grading/Coarser.lean` |
| **nothing coarsens onto a run** | `CubeChains.eq_of_hom_isRun` — a run's bead count already equals its `dimSum`, which no arrow changes | `Concurrency/Executions/Runs.lean` |

## Mathlib pieces that do the work for us

| what | name |
|---|---|
| slices | `Over`, `Over.forget`, `Over.map f`, `Over.post F` (`post_comp` is `rfl`) |
| `W` on a slice | `MorphismProperty.over W {X}` |
| `F⁻¹W` | `MorphismProperty.inverseImage` |
| **products of localizations, for free** | `Functor.IsLocalization.prod` — needs `ContainsIdentities`, which `(W X).IsMultiplicative` supplies through the parent projection, so `inferInstance` finds it with nothing written |
| localization uniqueness | `Localization.uniq`, `compUniqFunctor`, `liftNatIso`, `Localization.lift`/`fac` |
| universal property | `StrictUniversalPropertyFixedTarget`, `IsLocalization.mk'` |
| `C[W⁻¹]` is itself a quotient of a path category | `MorphismProperty.Localization`, `Q`, `wIso`, `wInv`, `objEquiv`, `morphismProperty_eq_top` |
| **disjoint union of categories** | `CategoryTheory.Sigma` — `incl`, `desc`, `Functor.sigma` |
| uniqueness of functors out of a quotient | `Quotient.lift_unique'` |

`Localization.Construction` is an established idiom here (`Retraction.lean` uses `objEquiv`, `wIso`,
`wInv`, `morphismProperty_eq_top`), and `Machinery/Localization/HomInduction.lean`'s `hom_induction`
pays its bookkeeping once.

## Sanity check

`Testing/Pi1/GlueCount.lean` counts the colimit at `Hbp □ⁿ` in an independent model. The 0-cells come
out at `n!` whatever the base presentation is; the 1- and 2-cells must **move with `p`** — Artin
`(2, 12, 72)` 1-cells and `(0, 6, 72)` 2-cells against germ `(4, 48)` and `(8, 144)`, where a thin
family would give `(4, 54, 9888)` at every `p`. If Artin and germ ever agree, the family has stopped
being inherited.
