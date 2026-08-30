# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a
precubical set: the executions of a cube chain, made into a groupoid, and the comparison of that
groupoid with the braid group. **Read this first to find the right file**, then open that one file
(+ its module docstring) — you should never need the whole tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and the **topos** one
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). The topos model is the default everywhere downstream.

**Why braids.** `(GeoBP, ⊗ᵍ)` is monoidal but has **no swap** — `Box` is rigid (`Aut ▫k = {id}`,
the symmetry-free convention), so no block transposition `▫(m+n) ⟶ ▫(n+m)` exists. The braiding
is *created* by the passage to executions, not inherited: two interleavings of independent events
are isomorphic, not equal, and the iso has a winding number. Independent actions do not commute —
they braid.

## The headline results

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`,
`Ch⋆ K = (Lines K).Elements`, `Run K` = the all-edges full subcategory of `Ch K`,
`RunWedge` = a wedge with a chosen run.

| Result | Statement | Lives in |
|---|---|---|
| **Salvetti = executions** | `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)` — a cell is a face below a tope, i.e. a chain plus a word linearizing it; the wall crossing `T' = X' ⊙ T` is the arrow rule | `Salvetti/SalExec.lean` |
| **The reorientation lives on `H`, not on the product** | `reorientCh_comp_hbpBraidSalEquiv` — across `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` the `Sₙ`-action on the decorated cube *is* `salReorientFunctor`; `not_reorientCh_of_over_base` — no endomorphism of `□ⁿ × run` over the base induces it, `□ⁿ` being rigid | `Salvetti/SymReorient.lean` |
| **`H` lies over the runs and over nothing else** | `HOverRun : H ⟶ const runPresheaf` from `H` of the terminal map; `isEmpty_cubeHom` — for `n ≥ 2` there is no map `H(□ⁿ) ⟶ □ⁿ`, hence none `H(□²) ⟶ □² × runBp`, so the product model's `prodFst` has no counterpart on `H` | `Salvetti/SymOverRun.lean` |
| **`H` is a twist, not a product** | `not_desym_natural` — the `desym` bijection `(⋁d ⟶ Hbp K) ≃ (⋁d ⟶ K) × (⋁d ⟶ runBp)` does not commute with restriction along the merge `⋁[2,1] ⟶ ⋁[3]`; `not_invertsMerges_runBp`/`not_invertsMerges_Hbp_Zbp` — the run factor takes the square's two orders to its edges' one order, so any natural product splitting would refute `InvertsMerges (Hbp K)` (`not_invertsMerges_of_splitting`) | `Salvetti/RunClassifier.lean` |
| **The merges act bijectively exactly when the wedge is the tensor** | `IsSegal K` — `K` inverts the comparison `wedgeToTensor : X ∨ Y ⟶ X ⊗ᵍ Y` at every pair of cubes, i.e. (`isSegal_iff_existsUnique`) a `p`-cell and a `q`-cell meeting at a vertex are the front and back faces of exactly one `(p+q)`-cell.  `isLocal_cubeMerge_iff_invertsMerges_repoint` — on the positive blocks this *is* `InvertsMerges` at every choice of base points.  The one comparison map fails in two opposite ways: `□²` has too few cells and the missing filler is the reordering staircase (`not_surjective_faceComparison_cube_two`, from `cubeMerge_ne_cubeReorder`), `H Z` has too many (`not_injective_faceComparison_H_Z`) | `Chains/SegalCondition.lean` |
| **`H` closes the gap** | `sbox_existsUnique` — `▪(p+q)` **is** the wedge `▪p ∨ ▪q` in the symmetric box category, so `isSegal_H_of_symFree_repr`: `H K` is Segal as soon as `symFree K` is representable.  Hence `isSegal_H_cube` and `invertsMerges_Hbp_cube : InvertsMerges (Hbp □ⁿ)`, which is what `localizationEquivPosBraidAction` runs on | `Salvetti/HSegal.lean` |
| **`H` supplies the arrows, the cube supplies the objects** | `costarOnesH` — `Hbp Zbp` has one all-edges chain per degree, so the merge out of it is initial and `Ch (Hbp Zbp)[W⁻¹]` collapses degreewise to a single object (`nonempty_locIso`); whereas `runHbpCubeEquivPerm : Run (Hbp □ⁿ) ≃ Perm (Fin n)` gives `n!` rigid all-edges chains, so `not_exists_hom_to_all_cube`/`isEmpty_costar_cube` — no costar there | `Salvetti/RunClassifier.lean` |
| **`Conc` is well defined** | `permOf_noDoubleCross` — crossing permutations are length-additive, hence `braidFunctor : RunWedge ⥤ FullBraid`, `ConcPos K = proj K ⋙ braidFunctor`, `Conc K = FreeGroupoid.lift (ConcPos K)` | `Salvetti/EventBraid.lean` |
| **Germ = Artin** | `garside_equiv_artin n : GarsideBraid n ≃* ArtinBraid n` and `posBraid_equiv_artinPos n : PosBraid n ≃* ArtinPosBraid n`, group and monoid.  The positive lift `σ ↦ σ̂` is `matsuLift`: peel adjacent descents, confluent by `matsuLift_mul_adjT` — **Matsumoto's theorem for `Sₙ`**, which mathlib lacks | `Braid/Matsumoto.lean` |
| **Chains are braid faces** | `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)`, `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face` — a chain of `□ⁿ` is an ordered set partition of `Fin n`; `reflectHom` is the computable converse | `Salvetti/ChainBraidFace.lean` |
| **Executions are word + composition** | `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` — a chain together with a run word refining it; `fexecChStarEquiv` is the enumerable model | `Salvetti/ExecData.lean`, `Testing/FastEquiv.lean` |
| **The crossing permutation is the word change** | `stepPerm_eq : stepPerm f = (runWord x).trans (runWord y).symm` — `ConcPos`'s label is "position in the source's run word ↦ position in the target's" | `Salvetti/RunWord.lean` |
| **The two gradings agree** | `crossPerm_eq_stepPerm` across `braidSalEquiv`, so `crossPerm_noDoubleCross` *is* `permOf_noDoubleCross` and `salvettiGrading` is `ConcPos` read on cells | `Salvetti/SalBraid.lean` |
| **The terminal object carries the full braid group** | `runWedgeEquivChStarZbp : Ch⋆ Zbp ≌ RunWedge` — `Z`'s events have no axis names, so nothing forces purity | `Salvetti/RunWedgeZ.lean` |
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Chains/Correspondence.lean` |
| **A wedge map is its coordinate bijection** | `wedgeHomEquiv : (⋁a ⟶ ⋁b) ≃ {e : beadEvent a ≃ beadEvent b // IsShuffle e}` — bead-monotone, order-preserving inside each source bead; hence `chBraid K` is faithful, `⋁a ⟶ ⋁[n]` is the Young-coset representatives, and `⋁1ᴺ ⟶ ⋁b` is the parabolic `S_{b₁}×⋯×S_{b_k}` | `Chains/ShuffleHom.lean` |
| **The merges are what the grading kills** | `Winf_isInvertedBy_chGerm` — a bead merge crosses nothing, so every germ grading (`chBraid`, `chPos`) inverts `Winf` | `Chains/MergeBraid.lean` |
| **The merges are exactly what does not braid** | `Winf_eq_nonBraiding : Winf K = fun _ _ f => ∀ e, pos (coordMap f.φ e) = pos e`, equivalently `Winf_iff_crossPerm_eq_one` — the converse of `crossPerm_eq_one_of_Winf`: a refinement that moves no event is a composite of canonical bead merges, and `merge_iff` says the generators are its codimension-one members | `Chains/MergeGenerate.lean` |
| **A chain morphism is its permutation** | `crossPermAt_injective` — merges into the coarsest chain exist out of every chain (`exists_Winf_to_top`) and are pinned by their endpoints (`eq_of_Winf`), and out of the run every permutation is realised exactly once (`arrowOnes`) | `Chains/ShuffleHom.lean`, `Chains/TopBead.lean` |
| **Into the group it is not full** | `not_surjective_posToBraid` — a positive braid's writhe never goes negative, so no `σᵢ⁻¹` is in the image of `PosBraid n →* Braid n` | `Braid/PosGerm.lean` |
| **`ConcPos` reads the cell structure** | `outLabels_eq_parabolic` — the crossing permutations out of an execution are exactly the parabolic `S_{d₁}×⋯×S_{d_k}` of its bead dimensions | `Testing/Parabolic.lean` |
| **Vertex group of a free groupoid, presented** | `presentationEquiv (S : Spanning C x) : End (mk x : FreeGroupoid C) ≃* Pres S` — for a **general** category: no thinness, finiteness or acyclicity | `Foundations/FreeGroupoidPresentation.lean` |
| **A localization is presented by its own arrows** | `endEquiv (S : Star W x) : LocMonoid W ≃* End (W.Q.obj x)` — `LocMonoid W` is one generator per arrow modulo functoriality and `⟨w⟩ = 1`; a `Star W x` is terminality of `x` in the wide subcategory `W`. The monoid analogue of the row above, and it mentions no permutations | `Foundations/LocalizationMonoid.lean` |
| **A star and a costar cut it down to an interval** | `locEquivGarside (S : Star W x) (T : Costar W y) : LocMonoid W ≃* GarsideMonoid W y x` — generators the **simples** `y ⟶ x`, relations one per factorisation `y ⟶ b ⟶ x` (a simple times a simple is a simple) together with `⟨w⟩ = 1` on the `W`-simple. Garside's "the lengths add" side condition is replaced by the existence of the factorisation | `Foundations/GarsidePresentation.lean` |
| **The chains' interval is `Sₙ`, and its monoid is the germ** | `simpleEquivPerm n : (onesObj n ⟶ topObj n) ≃ Perm (Fin n)` and `garsideEquivPosBraid n : GarsideMonoid (WinfN n) (onesObj n) (topObj n) ≃* PosBraid n` — the run of edges is a `Costar` (`costarOnes`) against the `Star` at the coarsest chain, so the localized component is the interval; a factorisation of simples is a length-additive product (`permLen_crossPermN_comp`) and conversely (`exists_atom_pairN`). Hence `endEquivPosBraid n` and `locEquivPosBraid n` | `Chains/GarsideChains.lean` |
| **The Garside element** | `garsideDelta n : onesObj n ⟶ topObj n`, the simple reversing the run; `garOf_mul_rightComplement` and `garOf_leftComplement_mul` divide it by an arbitrary simple on either side, the complements being `σ⁻¹Δ` and `Δσ⁻¹` | `Chains/GarsideChains.lean` |
| **The codimension-two species are the Artin relations** | `endEquivArtinPos m : End ((WinfN m).Q.obj (topObj m)) ≃* ArtinPosBraid m` — generators the `m−1` codimension-one atoms, relations the two codimension-two species: the disjoint double cut is `atomLoc_comm`, the bead cut in three is `atomLoc_braid`. `codim_eq_two_ones_iff` is the dichotomy; `artinPosToLoc_bijective` says the presentation map is an isomorphism | `Chains/ArtinRelations.lean` |
| **The grading is the localization** | `chPos_isLocalization : (chPos Zbp).IsLocalization (Winf Zbp)`, hence `localizationEquivGarside : (Winf Zbp).Localization ≌ Graded fun n => GarsideMonoid (WinfN n) (onesObj n) (topObj n)` (and `localizationEquivFullPosBraid` at `FullPosBraid`) — the bead merges are *exactly* what the positive braid grading kills, at every strand count at once | `Chains/PosLocalization.lean` |

| **A discrete fibration localizes fibrewise** | `isLocalization_elementsDescent : ∫P` localized at the cartesian lifts of `W` is `∫P̄` over `B[W⁻¹]`, for any `W`-inverting `P : B ⥤ Type` — proved by turning the (presentation-free) universal property of `∫P̄` into that of `B[W⁻¹]`, a functor `∫G ⥤ E` being the same as a functor `D ⥤ Fam E` lifting `G` | `Foundations/FibrationLocalize.lean` |
| **A chain is its dimension sequence plus its classifying map** | `chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ` for `wedgeHoms K = ⋁- ⟶ K` on `(Ch Zbp)ᵒᵖ`, and `Winf K` is its `Winf Zbp`; hence `isLocalization_chDescent` — once `wedgeHoms K` inverts the merges, localizing `Ch K` only localizes the base | `Chains/ElementsFibration.lean` |
| **A presented base presents the total category** | `elementsPresentation : Quotient (totalRel r P) ≌ ∫P` for `P` a presheaf on `Quotient r` — generators the base's, indexed by fibre elements (`Total`, a quiver whose projection is a covering, so `Paths (Total G) ≅ ∫G`), relations the base's on projected paths (`gen_onElements`, and its converse `gen_val`: nothing more is imposed) | `Foundations/ElementsPresentation.lean` |
| **`Ch Zbp` is presented by its bead cuts** | `zPresentation` / `zPresentationOp : Quotient (CutGraded.rel cutDataOp) ≌ (Ch Zbp)ᵒᵖ` — generators the codimension-one refinements, relations the codimension-two ones.  The engine is `existsUnique_factorisation`: a refinement factors through any intermediate shape in exactly one way, which read on `Fin N` is the tower of parabolic coset representatives, the second factor a `Tuple.sort` by the middle shape's beads.  `heights d` (the boundary set of a dimension list) turns the shapes into a lattice — `nonempty_hom_iff` says `a ⟶ b` exists exactly when `heights b ⊆ heights a` — and `CutGraded.presentation` sorts a generating path by the height its last step cuts | `Chains/CutPresentation.lean`, `Chains/Heights.lean`, `Foundations/CutGradedPresentation.lean` |
| **The localized serial wedges are presented by the germ relations** | `germPresentation : Quotient germRel ≌ FullPosBraidᵒᵖ` — one vertex per event count, a generator per permutation, `σ` then `τ` equal to `στ` at every length-additive product — read on the localization as `locGermPresentation : Quotient germRel ≌ ((Winf Zbp).op).Localization`.  It is assembled from three generic facts: a presented monoid is a presented one-object category, presentations add up over a coproduct, and `Graded M` is the coproduct of its degrees | `Braid/GermPresentation.lean`, `Foundations/MonoidPresentation.lean`, `Foundations/SigmaPresentation.lean` |
| **…and hence presents `Ch K`, but not its vertex monoids** | `chPresentation` / `chLocPresentation` transport a presentation of `(Ch Zbp)ᵒᵖ`, resp. of `((Winf Zbp).op).Localization`, to `Ch K`, resp. `Ch K[Winf⁻¹]`; `chCutPresentation` and `chLocGermPresentation` are those two with the base presentation supplied — the second under `InvertsMerges K`. `End` does **not** follow: `endEquivStabilizer` says it is a stabilizer, and `end_not_generated_by_simples` — in `PosBraidAction n` the only generator that is a loop is the identity, while the loops are `PosPureBraid n` — says a stabilizer is not spanned by the generators sitting at it. `invertsMerges_iff_uniqueComposites` puts the hypothesis in checkable form: a merged bead has exactly one filler | `Chains/LiftPresentation.lean` |
| **The localization is the positive braid category** | `localizationEquivPosBraidAction : (Winf (Hbp □ⁿ)).Localization ≌ PosBraidAction n` — objects the orderings of the strands, arrows the *positive* braids realising the change of ordering.  The fibre is `fibrePerm`, the step at which each axis is performed, and `fibrePerm_comp` says a refinement shifts it by its crossing permutation — so `degreeInclFibreIso` identifies the descended fibre with the `PosBraid n`-set of orderings.  The loops are `PosPureBraid n` and, `PosBraid n` having no units, the only isomorphisms are identities | `Salvetti/HPosAction.lean`, `Braid/PosAction.lean` |

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗ᵍ` — a computable `MonoidalCategory` on `PrecubicalSet` and on the
  alias `GeoBP := BPSet` (`Foundations/GeoTensor/`), plus the abstract Day-convolution version
  and their comparison (`DayTensor.lean`, `CubeTensor.lean`);
- the **nerve bridge** `realize ⊣ Nerve` between the concrete and topos models
  (`Foundations/Nerve.lean`, `Reachability.lean`);
- the **regular-covering toolkit** (`QuotientCat` → `DeckExact`) and the non-abelian short five
  lemma, for reading a group off a quotient of the execution poset.

## Layered layout (folders = areas; deeper layer imports shallower)

`Foundations` → `Chains` → `Salvetti` is the spine. `Arrangements/` (COMs, the braid arrangement) is
a **second root** — it imports nothing else in the tree — and feeds `Braid/`; the two join the spine
at `Salvetti/ChainBraidFace` and `Salvetti/EventBraid`. `CubeChains.lean` imports the results and
the retained infrastructure; only `Testing/` sits outside its cone.

### `Foundations/` — stable math fundamentals

*Precubical sets, two models.*
- `PrecubicalConstructions/Basic.lean` — the concrete/computable model: graded cells, `face ε i`,
  the precubical identity, the `Category` instance, extremal vertices.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (sign-vector cells `Fin N → Option
  Bool`, `none = ∗`), `faceCell`, `nones`.
- `Box.lean` — the box category `Box` (objects = dimensions, maps inherited from the concrete
  model) and the topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`HasPushouts` free).
- `SortPerm.lean` — `Tuple.eq_sort_inv`: an injective tuple is put in order by exactly one
  permutation, so `Monotone (f ∘ σ⁻¹)` forces `σ = (Tuple.sort f)⁻¹`.
- `SymBox.lean` — the **symmetric box category** `SBox` (`▪n`): the injections `Fin m ↪ Fin n` plus
  signs, so `Aut ▪n = Perm (Fin n)`.  `J : Box ⥤ SBox` is the monotone wide subcategory, and
  `sHomEquiv : (▪m ⟶ ▪n) ≃ Perm (Fin m) × (▫m ⟶ ▫n)` is the sorting factorization.
- `SymPresheaf.lean` — the round trip `H = J* ∘ J₍!₎` on `PrecubicalSet`: `symFree.obj K` at `▪n` is
  `Perm (Fin n) × K.cells n`, restricted by the sorting factorization of `u ≫ symHom σ`; `symUnit`
  exhibits it as the left Kan extension along `J.op`, and `symFreeIsoLan`/`HIsoLan` identify it with
  mathlib's `J.op.lan`.  `symFreeAdj : symFree ⊣ symRestrict` is that universal property read as
  an adjunction, with `symUnit` for its unit.
- `SymRepresentable.lean` — **`symFree (□ⁿ) ≅ y(▪n)`** (`symFreeCube`, the sorting factorization
  made natural), hence `HCube : H(□ⁿ) ≅ J*y(▪n)` and the faithful `reorientH : Sₙ →* Aut (H □ⁿ)`,
  which is left multiplication of orders on the top cell and permutes every face's axes.
  `cellDir` — the axis a cell performs at step `j`, i.e. the `SBox` map's own `pos` — is the form
  the action is cleanest in: `cellDir_reorientH` says `σ` relabels every step.  The same rigidity
  gives `isEmpty_cubeHom`: for `n ≥ 2` there is **no** map `H(□ⁿ) ⟶ □ⁿ`.
- `Representable.lean` — **cube Yoneda**: `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`; `canonicalMap`,
  `trueCount`, `coface`.
- `Bipointed.lean` — `BPSet` (a presheaf with two chosen `0`-cells) + `Hom` + category; `cells`,
  `vertex₀/₁`, `faceMap`/`cubeMap`, `IsAltitude`, and `comp_app_cell` (the `ConcreteCategory`
  bundling that defeats `rfl` on a composite application).
- `BipointedProd.lean` — the levelwise product with paired base points, as the binary product:
  `BPSet.prod` with `prodFst`/`prodSnd`/`prodLift` (computable, both legs `rfl`), shown to be the
  binary product by `prodFanIsLimit`, so `instance : HasBinaryProducts BPSet` and mathlib's `⨯`
  API apply.  Downstream spells `X.prod Y`; mathlib's chosen `X ⨯ Y` is `noncomputable`.
- `Wedge.lean` — `cube n` (representable, bi-pointed), `wedge2 X Y` = `X ∨ Y` (pushout of a point),
  `vertexMap`, `serialWedge` = `⋁d` (the fold `List.foldr (□· ∨ ·) (□0)`).
- `WedgeMonoidal.lean` — the wedge as the **default** `instance : MonoidalCategory BPSet`
  (tensor `∨`, unit `□0`, associator `wedge2Assoc`, unitors, pentagon + triangle).
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
  all `PrecubicalSet`-level, + the `alt_*` lemmas.
- `HomMonoidal.lean` — the three instances mathlib lacks (the two-variable `Functor.hom` is lax
  monoidal; `F.op` is monoidal when `F` is; `discreteOp`), so a functor `k ↦ (A k ⟶ B k)`
  *inherits* its lax monoidal structure through `D ⥤ Cᵒᵖ × C ⥤ Type` instead of carrying
  hand-written coherence; plus `LaxMonoidal.Graded F`, the total monoid `Σ m, F m`.
- `MonoidalTransport.lean` — transporting `⊗ₘ` along a tensorator `μ : A ⊗ B ≅ P`, stated in an
  arbitrary monoidal category so that `rw`/`simp`/`monoidal` behave where they would not at `BPSet`.
- `SkeletalEquiv.lean` — an equivalence of skeletal categories is a bijection on objects, with
  `toFun` *definitionally* `e.functor.obj` (so a transported group action still computes).
- `LocalizationSigma.lean` — localization of a **coproduct** of categories (mathlib has products
  only): `MorphismProperty.sigma`, `IsLocalization.sigma`, and a graded category as `Σ` of fibres.
- `FibrationLocalize.lean` — localizing a discrete fibration `∫P → B` fibrewise.  `Fam E` is the
  free coproduct completion and `Fam.pack`/`Fam.unpack` is the bijection between functors
  `∫G ⥤ E` and functors `D ⥤ Fam E` lifting `G` — the device that gives `∫P̄` a universal
  property.  Also the generic `Elements` toolkit — base transport `CategoryOfElements.pre`, its
  inverse `preInv`, `preEquivalenceComp`, `mapEquivalence` — and `endEquivStabilizer`
  (loops = stabilizer).
- `ElementsAction.lean` — a functor on a one-object category is an action.  `SingleObj M`'s
  `f ≫ g = g * f` already reverses, so a **covariant** `F : SingleObj M ⥤ Type` is a left `M`-set —
  no `ᵐᵒᵖ`.  The twist lives in the contravariant reading: `invActionPresheaf` (a `Γ`-set pulled
  back along `φ : M →* Γ`, restricting by `φ β⁻¹`) has `(∫ -)ᵒᵖ ≌ ActionCategory M`.  Also
  `isEquivalence_pre`: base transport is an equivalence when the base functor is fully faithful
  and covers everything carrying an element.
- `MonoidPresentation.lean` — a **presented monoid is a presented one-object category**:
  `presentedMonoidPresentation : Quotient (pathRel rel) ≌ (SingleObj (PresentedMonoid rel))ᵒᵖ`.
  `pathWord` reads a path in path order (mathlib's `pathToList` reads it backwards), and the `ᵒᵖ`
  is that reversal: path composition runs left to right, `SingleObj` multiplies `g * f`.
  Faithfulness is `PresentedMonoid.lift` applied to the loops the letters name — no induction on
  the congruence.
- `SigmaPresentation.lean` — presentations add up over a **coproduct**.  `Sigma.Quiv` is the
  coproduct quiver (a type synonym, since a summand may carry a category of its own);
  `pathsEquiv : (Σ i, Paths (V i)) ≌ Paths (Quiv V)` and `quotientEquiv` are inverse pairs of
  functors, each round trip an equality by the universal properties, so `presentation :
  Quotient (Sigma.pathRel r) ≌ Σ i, Quotient (r i)`.  `opEquiv` commutes `ᵒᵖ` with `Σ`.

*The geometric tensor.*
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `GeoTensor.lean` + `GeoTensor/{Hom,Unit,Assoc,Monoidal}.lean` — the **computable** geometric
  tensor on `PrecubicalSet`, from the closed form of the Day coend:
  `(X ⊗ Y)(▫n) = Σ p q, (p + q = n) × X(▫p) × Y(▫q)`, restriction = split the cell and restrict
  each half. `GeoTensor/Cube.lean` is `□m ⊗ □n ≅ □(m+n)` at the representable level.
- `GeoTensor/BP.lean` — the same on bi-pointed sets, written `X ⊗ᵍ Y`, carried by the alias
  `GeoBP := BPSet`; `cubeTensorIsoBP`. It lives on its own alias because bare `⊗` on `BPSet` is
  the **wedge**. Unit is `□0` on the nose.
- `DayTensor.lean` — the abstract alternative: Day convolution on `Boxᵒᵖ ⊛⥤ Type` (mathlib's
  `DayFunctor`), with the Yoneda-strong-monoidality `cubeDayIso` mathlib lacks. `noncomputable`.
- `CubeTensor.lean` — the computable universal property of `□m ⊗ □n = □(m+n)`
  (`cubeTensorPair`/`cubeTensorDesc`/`cubeTensor_hom_ext`), bypassing the Day wrapper.

*The model bridge.*
- `Nerve.lean` — `realize : PrecubicalSet ⥤ PrecubicalConstructions`, the nerve
  `Nerve : PrecubicalConstructions ⥤ PrecubicalSet`, `nerveCellEquiv`, `nerveRealizeIso`.
- `Reachability.lean` — `PrecubicalSet`-level reachability and connected components `π₀`.

*Terminal object and computable pushouts.*
- `Terminal.lean` — the terminal precubical set `Z` (one cell per dimension), `Zbp`.
- `GluePushout.lean` — a **computable** pushout of presheaves (mathlib's is `Classical.choice`-opaque).

*The regular-covering / free-groupoid toolkit.*
- `QuotientCat.lean` — the quotient category `P // G` of an order-free group action on a poset.
- `QuotientCovering.lean` — `quotFunctor : P ⥤ P // G` is a covering of quivers.
- `NerveQuot.lean` — the nerve of `P // G` is the levelwise `G`-quotient of `nerve P`.
- `DeckSequence.lean` — the deck-transformation sequence of the covering (monodromy endpoint,
  middle exactness, injectivity).
- `DeckExact.lean` — packages it as a full short exact sequence with the deck map `deck : Aut → G`.
- `FreeGroupoidLift.lean` — `FreeGroupoid.lift` is **strict** (`lift_spec`/`lift_unique` are
  equalities); `lift₂` lifts one variable at a time to keep that strictness.
- `FreeGroupoidPresentation.lean` — `presentationEquiv` / `autPresentationEquiv` for a general
  category, with `Spanning` (a transversal) and `Spanning.ofInitial`. Imports nothing from
  `CubeChains`.
- `LocalizationMonoid.lean` — the **monoid** analogue: `LocMonoid W` (one generator per arrow,
  functoriality, `⟨w⟩ = 1`), `Star W x` (terminality of `x` in mathlib's `WideSubcategory W`, whence
  the arrow `Star.t` and its two laws `step`/`root` for free), `locToEnd` for any functor inverting
  `W`, and `endEquiv : LocMonoid W ≃* End (W.Q.obj x)`.  Surjectivity is the retraction `starNat`
  carried off `W.Q` by `natTransExtension`; `Star.root` is what makes the loop at `x` come back as
  itself.
- `GarsidePresentation.lean` — cuts that generating set down to an interval. `Costar W y` is
  initiality of `y` in `WideSubcategory W` (the mirror of `Star`, with `s`/`step`/`root` from
  `IsInitial.to_comp`/`to_self`), and `GarsideMonoid W y x` is presented by the simples `y ⟶ x`.
  `pad` sends an arrow to `T.s a ≫ f ≫ S.t b`; the pads are `W`, so the class is unchanged, and at
  the two ends they are identities. The `W`-simple must be declared trivial — the factorisation
  relations alone are satisfied by sending every generator to one idempotent.  No length function
  appears: the factorisation *is* the side condition Garside imposes by hand.
- `ShortFive.lean` — the **non-abelian** short five lemma (`ShortFive.bijective_middle`); mathlib's
  abelian four/five lemma does not apply.
- `ElementsProd.lean` — the external product `F ⊠ G` and `extProdEquiv` on categories of elements.

### `Chains/` — the cube-chain category and its theory
- `Basic.lean` — `CubeChain` (a list of cubes satisfying the folded `IsCubeChain`; the junction
  vertices are forced, not stored), `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ cube-list data; `wedgeDesc … :
  ⋁(cubes.map (·.1)) ⟶ K.repoint a b` (re-pointing the target is what makes the endpoint
  conditions the morphism's own `app_init`/`app_final`), `wedgeToCubes`, `serialWedge_hom_ext`,
  the `glue0_*` pushout/mono cores.
- `Correspondence.lean` — **`equivWedgeCat`**; the chain↔wedge-map bijection; thinness.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category. The face inclusion is
  carried as *data*, not as a `Prop`.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube cells.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`),
  and its numerics from the serial wedge's own altitude: a source bead sits inside its target block
  (`serialWedge_beadStart_blockIdx`), so `blockIdx` is monotone and `∑ ad = ∑ cd`.
  Shared by `Salvetti/`.
- `ChainRestrictions.lean` — `restrictCubeChain face C` projects a chain of `□ᵇ` onto the directions
  a face uses, dropping the cubes that collapse. Not a precubical map (`Box` has no degeneracies)
  and **not** natural in `face` as a cube map — it factors through `faceEmb`, so there is no
  universal property over `Box` to look for. `EdgeChain K` and `EdgeChain.restrict` (+ `_id`/`_comp`)
  are the all-edges subpresheaf this cuts out.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms); `blockIdx_surjective` — a refinement never drops a target bead.
- `Degree.lean` — the grading `degree = Σ (dim − 1)` on `Ch K` and the **codimension** of a
  refinement (beads lost).  `codimNat : chFunctor ⟶ gradeFunctor` is a *monoidal* transformation, so
  codimension is additive along the tensorator; `codimOneWedge`/`CutData` locate the single merge,
  and `codim_eq_two_iff` says codimension two has exactly two species — one bead cut in three, or
  two distinct beads each cut in two.
- `Segal.lean` — the append iso `serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)`, built **structurally**
  from `λ_`/`α_`/whiskering (so its coherence is monoidal, not a pushout chase); `⋁` as a **strong
  monoidal** functor `serialWedgeFunctor : DimList ⥤ BPSet` where `abbrev DimList := Discrete
  (FreeMonoid ℕ+)`; the concatenation `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` and its
  faithfulness; `chUnit : Ch(□⁰) ≌ Discrete PUnit`.
- `SegalAltitude.lean` — `cube_admitsAltitude` / `wedge2_admitsAltitude` /
  `serialWedge_admitsAltitude`, which is what makes the n-ary decomposition hypothesis-free.
- `WedgeLaxMonoidal.lean` — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`; each coherence
  square is the matching `MonoidalTransport` lemma fed the append iso's own coherence.
- `Split.lean` — the **choice-free** inverse of `chConcat`, in three layers: `Split Z A B` ("`Z` is
  `A ∨ B`" as data, on the computable `Glue.cellSide`), `Split.chainSplit` (the *order* — the only
  place altitude is used), and the interface `chObjEquiv : Ch Z ≃ Ch A × Ch B`. Also
  `splitWedgeMorphism`, the same split for a bare map `⋁as ⟶ X ∨ Y`, which is the form
  `Salvetti/Runs.lean` consumes.
- `WedgeExtend.lean` — lifting a (co)presheaf on `Box` to serial wedges, in both variances:
  contravariant `F↑ X = (X.toPsh ⟶ F)` (precomposition) and covariant `F↓ X = X.toPsh ⊗_Box F`
  (the cubical coend as a plain computable `Quot`, not `Functor.lan`).
- `PshExtMonoidal.lean` — `pshExtFunctor F = BPSet.toPshFunctor.op ⋙ yoneda.obj F` is oplax
  monoidal, strong under single-vertexness — so `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf`
  literally, with its splitting for free.
- `CubeVtx.lean` — vertices of cube faces (`cubeVtx`), the monotonicity the coordinate coend needs
  (`cubeVtxOfCell_bot_le_top`).
- `CoordFunctor.lean` — the **coordinate coend**: `coordFlip χ : beadEvent a ≃ Fin m` for
  `χ : ⋁a ⟶ □m`, `coordMap`/`coordMapEquiv` for wedge maps, `coordFlip_comp` (the engine behind the
  label theorem), `coordMap_eq` (its `blockIdx`/`blockFace` form), the run-free lexicographic
  flattening `pos = finSigmaFinEquiv` with its order laws, and the **monoidality of `coordMap` over
  `++`**: `eventInl`/`eventInr` split `beadEvent (a ++ b)` (`eventAppendCases`), and
  `coordMap_inclL`/`coordMap_inclR` say a wedge map restricting along the half-inclusions moves each
  block by its own restriction — the coordinate content of `chConcat`'s tensorator.
- `WedgeBraid.lean` — the **braid grading of `Ch K` from the wedge map alone**: `crossPerm g` is
  `coordMap g.φ` read through `pos`, length-additive (`permLen_crossPerm_comp`, from
  `coordMap_noDoubleCross`) and **monoidal over the wedge** (`crossPerm_chConcat`: on the tensorator
  it is the block sum `permSum`, so crossings add — `permLen_crossPerm_chConcat`).  `crossPermAt`
  reads it at a fixed strand count, absorbing the `dimSum` transports so the cocycle law becomes a
  plain anti-homomorphism (`crossPermAt_comp`) — the one spelling used downstream.
  `chGerm G K : Ch K ⥤ Graded M` is that cocycle read in any germ family
  (`Braid/Graded`); `chBraid` is it at `Braid`, `chPos` at the positive monoid `PosBraid`. It
  factors through the serial-wedge category `Ch Zbp` (`chBraid_eq_pushforward`); no run, no nerve.
- `ShuffleHom.lean` — **a wedge map is its coordinate bijection**: `wedgeHomEquiv` identifies
  `(⋁a ⟶ ⋁b)` with the *shuffles* (bead-monotone, order-preserving inside each source bead), via
  the classification of wedge maps into a cube by their charts (`exists_coordFlip_eq`). Hence
  `chBraid K` is faithful, `crossPermAt_injective` (a chain morphism is its permutation),
  `⋁a ⟶ ⋁[n]` is the Young-coset representatives, and `⋁1ᴺ ⟶ ⋁b` is the parabolic.
- `AtomPair.lean` — the atom relations of `Braid/PosGerm`, realised in `Ch Zbp`:
  `exists_atom_pair` factors every length-additive
  `β * adjT i` through `atomComp n i = 1ⁱ 2 1^{n-2-i}`. The first step is *geometric*: splicing the
  other staircase of a square, `cubeReorder 1 1`, at the cut exchanges exactly the two strands there
  (`exists_crossPermAt_swap`), which is `adjT i`; the second step sorts across the double bead.
- `TotalMerge.lean` — `zObj`/`zHom` (an object of `Ch Zbp` *is* its dimension list), the splice
  `𝟙 ∨ w ∨ 𝟙` read as a **double concatenation** (`splicePhi_eq_concat`, `spliceNil_eq_concat`), so
  `coordMap_inclL`/`_inclR` reduce its coordinate map to the middle staircase `pairMerge p q w`
  alone: `pos_coordMap_splicePhi` says a splice moves only the beads it merges, by whatever
  permutation of `[0, p+q)` the staircase performs.
- `TopBead.lean` — **the coarsest chain on `n` events (`topDims`: one bead, or none), and the
  arrows into it**. `eq_of_Winf`: a merge moves no event, and a wedge map *is* its coordinate
  bijection, so a merge is pinned by its endpoints. A merge is an arrow with trivial crossing
  permutation (`Winf_eq_nonBraiding`), so `totalTo` (the total merge out of every chain) and
  `exists_Winf_from_ones` (the run of `N` edges merges *onto* every shape of strand count `N`) are
  the identity case of the `Chains/AtomPair` classification, and `arrowOnes` realises every
  permutation out of the run.
- `MergeBraid.lean` — monoidality confines a cut to its two merged beads, and there the staircase
  `cubeMerge` sends them to consecutive coordinate blocks in order; so a merge preserves `pos` and
  `crossPerm = 1` on all of `Winf`. Hence `Winf_isInvertedBy_chGerm`: every germ grading —
  `chBraid`, `chPos` — inverts the bead merges.
- `MergeGenerate.lean` — the **converse**: `Winf_eq_nonBraiding`. A dimension list is *coarsened* by
  summing consecutive beads, and `coarser_iff_exists_pos` says a coarsening is realised by exactly
  one wedge map — the `pos`-preserving one (`ShuffleHom`). So a refinement that moves no event and
  loses a bead factors through the merge at any junction its target does not separate
  (`exists_merge_factor`), and induction on the bead count exhausts it. At codimension one the
  middle map is forced: `merge_of_pos_of_codim_one`, whence `merge_iff_of_codim_one`.
- `Heights.lean` — a dimension list **is** its boundary set `heights d`, and `heights_injective`
  says nothing else. `heights_succ_iff` is the bridge to `blockOfPos`, so the coarsening relation
  reads either as `heights b ⊆ heights a` or as "beads of `a` sit inside beads of `b`". On the
  categorical side `crossPermAt_mem_parabolic` and `crossPermAt_lt` are the converse of
  `exists_crossPermAt_blocks`, giving `nonempty_hom_iff`: `a ⟶ b` exists exactly at a coarsening.
- `CutPresentation.lean` — `existsUnique_factorisation`, and the presentation it feeds. The second
  factor of a factorisation through `m` is the permutation sorting the strands by `m`'s beads
  (`Tuple.sort`), the first is what is left; uniqueness is that a permutation preserving each bead
  of `m` and rising inside them is the identity. `cutsOf f = heights a \ heights b` then makes
  `Ch Zbp` and its opposite `CutGraded.Data`s.
- `ChainLocMonoid.lean` — the strand-`n` component `ChZn n` (full in `Ch Zbp`, the fibre of the
  strand grading) with the merges `WinfN n` restricted to it: the coarsest chain `topObj n` is
  terminal among the merges — a `Star` — so `Foundations/LocalizationMonoid`
  gives `endEquivWinfN : LocMonoid (WinfN n) ≃* End ((WinfN n).Q.obj (topObj n))` — the localized
  endomorphisms presented by the chain morphisms themselves, with no permutation in sight.
- `GarsideChains.lean` — that monoid, presented by the **interval** `1ⁿ ⟶ [n]`. `costarOnes` makes
  the run of edges initial among the merges (`exists_WinfN_from_ones` for existence, `eq_of_Winf`
  for uniqueness), so `Foundations/GarsidePresentation` applies; `crossPermN` is `crossPermAt` at
  the component's strand count and `simpleEquivPerm` (`crossPermN` against `onesToTop`) identifies
  the interval with `Sₙ`.  `garsideEquivPosBraid` matches the two presentations relation for
  relation — `permLen_crossPermN_comp` says a factorisation is length-additive, `exists_atom_pairN`
  says every length-additive product is a factorisation — and `locEquivPosBraid`,
  `endEquivGarsideZ`, `endEquivPosBraid` are its corollaries.  `garsideDelta` is the Garside
  element, divisible by every simple on both sides.
- `ArtinRelations.lean` — the same monoid in **Artin** shape. `atomArrow m i` is the codimension-one
  refinement of the run merging the edge beads `i, i+1` along the *crossing* staircase, with
  `crossPermN = adjT i`; `codim_eq_one_ones_iff` / `codim_eq_two_ones_iff` say the targets out of the
  run are exactly `atomComp`, and `tripleComp`/`doubleComp`.  Each codimension-two arrow factors two
  ways: the disjoint double cut gives `atomLoc_comm` outright, while the triple cut's second factor
  merges a square with an edge, and rewriting it into two atoms (`germ_of_atom`, through
  `locEquivPosBraid`) is what turns a two-letter identity into `atomLoc_braid`.  `ArtinPosBraid`
  presents the monoid: `artinPosToLoc_bijective`.
- `PosLocalization.lean` — upgrades that monoid statement to a functor one: `chPos Zbp` is a
  localization at `Winf Zbp`, so `localizationEquivGarside` presents `(Winf Zbp).Localization` by
  the intervals degree by degree (`localizationEquivFullPosBraid` is the same at `FullPosBraid`).
  Generically, a `Star` collapses a localization onto its basepoint (`starEquivalence`), so
  `toLocMonoid W` is itself a localization; the strand components are then localized one at a time
  (`chPosN`) and glued by `Foundations/LocalizationSigma`, `Ch Zbp` being the coproduct of its
  strand components and `Graded M` the coproduct of its degrees.  `locFullOpEquiv` is the same
  equivalence on the opposite — the variance `Ch K` sits in over `Ch Zbp` — and
  `locGermPresentation` composes it with `Braid/GermPresentation` to present the localization by
  the germ relations.
- `ElementsFibration.lean` — `toChZ : Ch K ⥤ Ch Zbp` presented as a category of elements:
  `wedgeHoms K = ⋁- ⟶ K` on `(Ch Zbp)ᵒᵖ` and `chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ`
  (the `ᵒᵖ` is mathlib's opfibration convention).  `Winf_eq_inverseImage_toElements` puts the
  merges on the base, so `Foundations/FibrationLocalize` gives `isLocalization_chDescent`: all of
  the `K`-dependence of the localization sits in `wedgeHoms K`.
- `SegalCondition.lean` — **for `K` the wedge is the tensor** [RESULT].  `IsLocal K w` (restriction
  along `w` is a bijection on maps into `K`) is closed under isomorphism (`isLocal_congr`) and
  under whiskering (`IsLocal.tensor_id`/`id_tensor`, from `wedge2Desc` + `wedge2_hom_ext`), and
  base points are free in both directions (`isLocal_iff_bijective_repoint`).  A merge *is*
  `𝟙 ∨ cubeMerge ∨ 𝟙` up to isomorphism (`CutData`), so the cube statement propagates to every bead
  merge of every serial wedge — no bead computation for `splicePhi` is needed, which is what makes
  the reduction cheap.  `wedgeCubeHomEquiv` reads the target on cells, giving `faceComparison` and
  the `∃!` form.

### `Arrangements/` — COMs, the braid arrangement, Salvetti posets
See `Arrangements/README.md`.
- `COM.lean` — complexes of oriented matroids (sign vectors, composition `⊙`, `faceLE`), the BCK axioms.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM (cells `(X, T)` with `X ⊑ T`).
- `SalElements.lean` — `Sal L` as a category of elements of the "topes above" presheaf.
- `COMSum.lean` — the direct sum `L₁ ⊕ L₂` and `salSumEquiv : Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `Braid.lean`, `BraidPreorder.lean`, `BraidCovector.lean` — the braid arrangement `braidCOM n`
  (ground set = ordered pairs of `Fin n`) and its `Fin n` dictionary (`braidSign`, heights,
  ordered set partitions).
- `BraidSymmetry.lean` / `SalSymmetry.lean` — the `Sₙ` reorientation action on `braidCOM n`
  (`reorient σ`) and the induced action on `Sal`.

### `Salvetti/` — executions
See `Salvetti/README.md` and `Salvetti/BRAID.md`.
- `Runs.lean` — the **run presheaf** `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims`. A *run* is an
  all-edges cube chain: `Run K` is the full subcategory of `Ch K` cut out by `IsRun`, and it is
  discrete. Runs of a cube assemble into `runPresheaf : Boxᵒᵖ ⥤ Type`, so by `Chains/PshExtMonoidal`
  a run of `⋁a` *is* a map `(⋁a).toPsh ⟶ runPresheaf` (`runPshEquiv`), and `runRestrict` along a
  wedge map is transpose–precompose–assemble. `runFunctor : BPSet ⥤ Cat` is lax monoidal, by
  restricting `chFunctor`'s structure to runs.
- `Elements.lean` — thinness for `Ch⋆ K = (Lines K).Elements`: `Functor.elements_isThin` and the
  thinness of `Ch (□ⁿ)`.
- `Covering.lean` — `proj`/`π` are discrete opfibrations, so a `Ch⋆` morphism out of `p` is *forced*
  by a base `Ch` morphism. Neither is a covering — the fibres vary, which is what lets the total
  space be non-contractible over a contractible base.
- `EventPerm.lean` — the event relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)`, and
  `eventEquiv_mk` (its `blockIdx` / `blockFace` form) — the computational handle on everything
  downstream.
- `RunSegal.lean` — **the Segal decomposition of a linearization**: a run performs bead `i` at
  exactly the prefix-sum interval, in that bead's own order (`coordMap_fst_run_iff` as an *iff*,
  `coordFlip_run_concat`), so `runProj` gets a computational characterization and the sealed
  `runSplit`/`runSegalProd` stay sealed.
- `RunRestrict.lean` — **face restriction preserves the run order**: `EdgeChain.restrict` is a
  `List.filterMap`, which keeps survivors in order (`exists_strictMono_filterMap`), hence
  `localStep_restrict{,_lt_iff,_rank}`.
- `RunPerm.lean` — **a run of `□ⁿ` is a permutation of its axes**: `runPermEquiv : Run (□ⁿ) ≃
  Perm (Fin n)`, whose `toFun` is `localStep` on the nose and whose inverse `runOfPerm` is the
  singleton-bead `blockChain`. Restriction along a face is *sorting*: `runPermEquiv_restrict`
  reads `runPresheaf.map g.op` as the inverse of `Tuple.sort (localStep r ∘ faceEmb g)` — the
  permutation form of `localStep_restrict_rank`.
- `SymRun.lean` — **`H Z ≅ runPresheaf`** (`HZIsoRun`): a cell of the symmetric round trip of the
  terminal precubical set at `▫n` is an order on its axes, hence a run of `□ⁿ` (`symRunEquiv`), and
  both sides restrict by `Tuple.sort`.
- `SymOverRun.lean` — the **asymmetry of `H`**: `HOverRun`/`HbpOverRun` send `H K` to `runBp`
  naturally (`H` of the terminal map, then `HZIsoRun`), while `H(□²) ⟶ □²` and hence
  `H(□²) ⟶ □² × runBp` are empty. `□ⁿ × runBp` lies over both factors, `H(□ⁿ)` over `runBp` only,
  and the missing `prodFst` is the room `H` has for a reorientation.
- `EventBraid.lean` — the **run order** `runOrd`, the crossing permutation `permOf`, and
  `permOf_noDoubleCross` [RESULT]. Events are ordered by the run linearizing the execution, *not*
  by the run-free `pos` — ordering by `pos` makes `permOf` a function of the chain morphism alone,
  which trivializes every loop. The two leaves are `runOrd_within_localStep` (from `RunSegal`) and
  `localStep_restrict_lt_iff` (from `RunRestrict`). Then `braidFunctor`,
  `ConcPos K = proj K ⋙ braidFunctor`, and `Conc K = FreeGroupoid.lift (ConcPos K)`.
- `ChainBraidFace.lean` — the **base comparison** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` and
  `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face`. `beadOf b q` is the bead flipping coordinate `q`;
  `ofBlockMap` rebuilds a chain from its block map; `reflectHom` is the **computable** converse
  (`chFace b ⊑ chFace a` reconstructs `a ⟶ b`).
- `RunWord.lean` — the **run word** `runWord x : Perm (Fin n)` (which direction fires at each step),
  `stepPerm_eq` [RESULT], and the **arrow rule** `runWord_group` / `runWord_within`: across beads the
  finer execution runs in its own bead order, inside a bead it inherits the coarser one's. The route
  factors `permOf` through `coordFlip` of the *total* run map, so it needs neither the Segal
  decomposition nor `coordMapEquiv`'s inverse.
- `ExecData.lean` — `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` [RESULT], a chain plus a linearization
  refining it. `ofWord` builds one from `reflectHom`, so it computes; `ext_runWord` (thinness of
  `Ch (□ⁿ)`) is what makes an enumeration of words complete.
- `SalExec.lean` — `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)` [RESULT], `salCompare` at
  `□ⁿ`. `wordTopeEquiv` reads topes as run words (a tope's chain has injective `beadOf`, hence one
  direction per bead); `linesTopeIso` bundles that fibrewise, and its naturality square is
  `wordTope_runWord` — the wall crossing `T' = X' ⊙ T`, whose two branches are the arrow rule's
  two clauses.
- `SalCompare.lean` — `salCompare : ((Ch K)ᵒᵖ ≌ Face L) → (Lines K ≅ e.functor ⋙ salFunctor L) →
  (Ch⋆ K ≌ Sal L)` [RESULT]: both sides are categories of elements, so the comparison is one of
  bases plus one of presheaves; `hbpSalEquiv` chains it with `chSymChStarEquiv` for
  `Ch (Hbp K) ≌ (Sal L)ᵒᵖ` — "`H` is the complexification".
- `SalBraid.lean` — `crossPerm = stepPerm` across `braidSalEquiv` (`topeRank` of a run word is the
  step at which the coordinate fires), so `crossPerm_noDoubleCross` **is** `permOf_noDoubleCross`;
  then `salvettiGrading` / `salvettiConstruction`.
- `RunWedgeZ.lean` — `Ch⋆ Zbp ≌ RunWedge`, with a hand-built inverse so it computes; and the
  decomplexification `toChainZ : Ch⋆ K ⥤ (Ch Zbp)ᵒᵖ`.
- `ChStarProduct.lean` — `Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ`, an **isomorphism** of categories: `runBp` is
  `runPresheaf` bi-pointed at its unique vertex, and a run is the second leg of `prodLift`.  Both
  round trips are `rfl` — the cone's universal property is definitional.
  Side-condition-free — the wedge never has to be split.
- `ChStarSym.lean` — **`Ch (Hbp K) ≌ Ch (K.prod runBp) ≌ (Ch⋆ K)ᵒᵖ`** [RESULT], for every `K`, with
  no side condition. There is no map `Hbp K ⟶ K`, so this is not a pushforward: a symmetry fixes a
  cube's extremal vertices (`Hbp_vertex₀/₁`), so bead-wise symmetries glue (`symOf`), every
  decorated chain factors uniquely as one followed by an ordinary chain (`symOf_und`), and a
  morphism is carried across by the *twist* `φ ↦ und (φ ≫ symOf ρ)`, whose functoriality is
  associativity plus that uniqueness. The run and the order are inverse to each other
  (`symCell`); `SHom.sortPerm_sortFace_inv` is what makes that consistent, and it is the only
  place blocks are looked at.  Both legs restrict bead by bead through *any* factorization of a
  source bead through a target bead (`bead_of_factor`, `bead_comp_of_factor`), of which
  `blockIdx`/`blockFace` is the canonical one; that is what
  `runPermEquiv_bead_comp`/`runPermEquiv_bead_twistRun` are stated at.
- `SymReorient.lean` — **the symmetry the equivalence above cannot see, and what it is**:
  `reorientBp : Sₙ →* Aut (Hbp □ⁿ)` is faithful, and across
  `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` it *is* `salReorientFunctor`
  (`reorientCh_comp_hbpBraidSalEquiv`) [RESULT]. The engine is `beadDir`, the direction bead `i`
  performs at step `j`: `σ` relabels every step, which moves the Salvetti face (`chFace` of the
  chain) and the tope (`chFace` of `runLine`, the chain the run performs) together —
  `coordFlip_runLine` is `coordFlip_run_concat` with the local run order cancelled against the
  decoration. Whereas `□ⁿ` is rigid (`cube_endo_eq_id`, `Subsingleton (Aut □ⁿ)`), so an
  endomorphism of `□ⁿ × runBp` over the base leaves underlying chains alone and induces no
  reorientation (`not_reorientCh_of_over_base`).
- `HSegal.lean` — **`H` makes the wedge the tensor** [RESULT].  An `SBox` map is a
  `coord : Fin n → Bool ⊕ Fin m`, so composability of `f : ▪p ⟶ ▪n` with `g : ▪q ⟶ ▪n` reads off
  coordinatewise (disjoint images; `g ≡ 1` on `f`'s image, `f ≡ 0` on `g`'s, signs agreeing off
  both) and `SHom.merge` is the unique filler: `▪(p+q)` is the wedge `▪p ∨ ▪q`.  Through
  `symFreeCube`/`HCube` this is `isSegal_H_cube` and `invertsMerges_Hbp_cube`.  The contrast is
  the same map failing the other way at `H Z` (`not_injective_faceComparison_H_Z`).
- `RunClassifier.lean` — **the run object, and why `Hbp` is not a product** [RESULT].
  `HbpZIsoRun : Hbp Zbp ≅ runBp` is the runs classifier; over a one-vertex target a wedge map *is*
  its beads (`ofCells`/`oneBeadEquivCell`), so `Hom(⋁[2], runBp)` has two elements and
  `Hom(⋁[1,1], runBp)` one — `not_invertsMerges_runBp`.  The undecorated `□²` fails the same
  condition the other way round — one 2-cell, two runs to hit (`not_invertsMerges_cube_two`) —
  which is why `H` is in the picture at all.  Hence any *natural* splitting
  `Hom(⋁d, Hbp K) ≃ Hom(⋁d, K) × Hom(⋁d, runBp)` would refute `InvertsMerges (Hbp K)`
  (`not_invertsMerges_of_splitting`), and `desym` is not one: `not_desym_natural`, from the
  explicit merge `⋁[2,1] ⟶ ⋁[3]` and the cyclic run, where the twisted restriction sorts the
  *inverse* order and inverts (`runPermEquiv_bead_twistRun`) while the plain one sorts the order
  (`runPermEquiv_bead_comp`) — and sorting does not commute with inverting.  The tower
  `Ch (Hbp K) ⥤ Ch (Hbp Zbp) ⥤ Ch Zbp` (`forgetLabels`/`forgetRun`) is what survives.
  `onesHomEquivRunClassifier` — the maps out of the all-edges chain are the runs of the target,
  so the simples are the cells of `Hbp Zbp` (`simplesEquivCells`), with no `Perm` in the
  description; the two sides have opposite variance, so it is a bijection of fibres only.
  Then the **collapse and its failure** [RESULT]: an edge of `Hbp Zbp` carries no order, so
  `subsingleton_homHbpZbp_of_ones` makes `Hom(⋁𝟙ⁿ, Hbp Zbp)` a point; the base merge out of the
  all-edges chain therefore lifts with nothing to check (`exists_Winf_from_onesH` — the
  compatibility condition lives in that one-element hom-set, so the twist above is never
  consulted), and with `eq_of_Winf` it is a `Costar (WinfHn n) (onesObjH n)` (`costarOnesH`),
  whence `Ch (Hbp Zbp)[W⁻¹]` is degreewise a single object (`nonempty_locIso`).  For the cube the
  contrast is exact: `runHbpEquiv : Run (Hbp K) ≃ Run K` (the order on an edge is no data), so
  `Run (Hbp □ⁿ) ≃ Perm (Fin n)`, and `isRun_of_hom_to_run` plus discreteness of `Run` give
  `not_exists_hom_to_all_cube` / `isEmpty_costar_cube`.
- `HPosAction.lean` — the localization identified.  A decorated chain of `□ⁿ` has `dimSum = n`
  (`und` reads its underlying chain), so only the degree-`n` component `degreeIncl n` of the
  localized base carries a fibre.  What the fibre *is* there: `cellDir` reads an `H`-cell as an
  `SBox` map and restriction along a face is precomposition there (`cellDir_Hbp_map`), so
  `eventDirEquiv` — each bead's order followed by `coordFlip` — is a bijection between the events
  of a decorated chain and the axes, natural in the shape (`eventDirEquiv_comp`).  Inverting it
  against the lexicographic `strand` gives `fibrePerm`, the step at which each axis is performed,
  and `fibrePerm_comp` says a refinement shifts it by its crossing permutation.  On the run of
  edges `fibrePerm` *is* `runHbpCubeEquivPerm`, so the merge out of the run (invertible on the
  fibre, crossing nothing) makes it bijective everywhere.  Uniqueness of lifts along `chPosN n`
  then descends that to `degreeInclFibreIso`, and
  `localizationEquivPosBraidAction : (Winf (Hbp □ⁿ)).Localization ≌ PosBraidAction n`.

### `Braid/` — the braid group itself
- `Blocks.lean` — `blockOfPos` (the consecutive block of a composition a position falls in) and its
  Young subgroup `parabolic n ds`.
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `PosGerm.lean` — `PosBraid n`, the same germ presentation read as a **monoid** (`[1] = 1` must be
  imposed: without it every generator may go to one idempotent). `germ_of_atom` cuts the relations
  down to those whose right factor is an adjacent transposition — the only shape the geometry
  realises. `posToBraid` is not surjective (`writhe_nonneg`). `posPermHom` is `permHom` read on the
  monoid, `PosPureBraid n = mker (posPermHom n)` its positive pure braids, and `posPureToPure`
  compares them with `PureBraid n ≤ Braid n` — injective exactly as far as `posToBraid n` is,
  Garside's theorem, carried as a hypothesis.
- `PosAction.lean` — `PosBraidAction n = ActionCategory (PosBraid n) (Perm (Fin n))`: the orderings
  of the strands, with the positive braids realising the changes of ordering.  The action must be
  **left** multiplication through `posPermHom` (`x * posPermHom β` is a right action); the
  endomorphism monoid at every ordering is `PosPureBraid n`.  `eq_one_of_mul_eq_one` — the writhe
  is additive and non-negative, so there are no non-trivial units — makes `isIso_iff_eq_id`: a
  category, not a groupoid, against `BraidAction n`, which is connected.
- `Artin.lean` — the adjacent transpositions `adjT k` and the Artin relations they satisfy.
  `IsArtinFamily g` is the pair of relations on a family; `isArtinFamily_of_atom` says **every**
  germ has one, multiplicativity across an ascent being the only input, so `ofPerm ∘ adjT`,
  `posPerm ∘ adjT` and `artinGen` are all instances.  `ArtinRel` states the two relations once, as
  words: `artinRels` reads them in the free group for `ArtinBraid n`, and
  `Braid/Matsumoto`'s `ArtinPosBraid n` reads the same inductive as a monoid presentation.  Hence
  the comparison `garsideOfArtin : ArtinBraid n →* GarsideBraid n`.
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `Matsumoto.lean` — **Matsumoto's theorem for `Sₙ`** [RESULT].  `matsuLift g σ` peels an arbitrary
  adjacent descent off `σ` and recurses; `matsuLift_mul_adjT` is the local confluence — two descents
  are far apart (`hg.comm`) or consecutive (`hg.braid`) — and `permLen` is the termination.  Hence
  `PosBraid.liftArtin`, `posBraid_equiv_artinPos` and `garside_equiv_artin`, with no hypothesis.
- `PermWord.lean` — the Artin-word emitter `permWord σ`, and the signed `schreierWordZ`.
- `Kernel.lean` — Schreier for a group with a set-section `t` of `φ : G →* Q`:
  `ker φ = ⟨t q · t s · t (q·s)⁻¹⟩`. Here the transversal `ofPerm` *is* the generating set, so
  `pureBraid_le` asks only for the conjugated cocycles — the words a zigzag of refinements reads.
- `Sum.lean` — juxtaposition `braidSum : Braid m × Braid n →* Braid (m+n)`, on the block-diagonal
  `permSum`; the crossing count adds because the blocks never interact.
- `Graded.lean` — `Graded M`, the total category of a family of monoids indexed by `ℕ`: degrees as
  objects, `End n = M n`, the degree transport living once in composition. `FullPosBraid` is it at
  `PosBraid` and `FullBraid` — the groupoid `braidFunctor` maps into — at `Braid`; `Graded.Germ` is
  what a target must supply for a permutation cocycle to compose, and `Germ.hom_comp` discharges
  that law once for every germ family.  `Graded.single n` is the degree-`n` component, fully
  faithful for every family; `Graded.congr` moves a degreewise `≃*` to the total categories, and
  `Graded.sigmaEquivalence : (Σ n, SingleObj (M n)) ≌ Graded M` is the coproduct decomposition
  (there are no cross-degree morphisms).
- `GermPresentation.lean` — `germPresentation : Quotient germRel ≌ FullPosBraidᵒᵖ`, the germ
  relations read on the coproduct quiver `GermQuiver` (one vertex per strand count, a loop per
  permutation).  Nothing braid-specific happens here: `PosBraid n` is a `PresentedMonoid`, and the
  two `Foundations` bridges plus `Graded.sigmaEquivalence` do the rest.
- `SalvettiConstruction.lean` — the **computable** reading of a tope as a linear order (`topeBefore`,
  `topeRank`, `topePerm`) and the crossing cocycle `crossPerm`, plus `permBraidFunctor`, the shared
  "length-additive cocycle ⟹ braid-valued functor" builder. Its length-additivity is transported
  from the run side in `Salvetti/SalBraid.lean`.

### `Testing/` — the fast execution model, and computing `π₁`

Strictly downstream: nothing outside `Testing/` imports it, and it is the only part of the tree
`lake build CubeChains` does not build.

An execution of `□ⁿ` is a **linear order on the `n` directions plus a composition of `n`** — the run
linearizes each bead, and beads are consecutive blocks of that word. So `Ch⋆(□ⁿ)` has `n!·2^{n−1}`
objects (192 for `n = 4`), enumerable in output-linear time.

- `Cells.lean` — cells of `□ⁿ` as sign vectors; `SubCube n` (a face-closed `Bool` predicate),
  `full`/`boundary`/`skeleton`, `beadCell`. `(cube n).init` is `some false`, so `some false` = a
  direction not yet performed.
- `Boundary.lean` — `∂□ⁿ ↪ □ⁿ` as a genuine subfunctor (cells of dimension `< n`), so `Ch⋆(∂□ⁿ)`
  is `ChStar` of an actual `BPSet`.
- `FastExec.lean` — `FExec n` (nonempty blocks whose concatenation is a permutation), `Refines`
  (decidable), `fperm`, the DFS `execs` with `mem_execs_iff` (sound **and** complete), `buildPoset`.
- `FastEquiv.lean` — the bridge `fexecChStarEquiv : FExec n ≃ Ch⋆ (□ⁿ)` between the enumerable
  block-list model and `Salvetti/ExecData`, plus `fperm_eq_stepPerm`.
- `Parabolic.lean` — `outLabels_eq_parabolic`, `dims_eq_of_outLabels_eq`, `outLabels_eq_top_iff`.
- `Presentation.lean` — `PosetData ↦ Presentation`: spanning forest, cover generators, 3-chain
  relations, `homology` (bespoke Smith normal form — mathlib's is noncomputable), GAP rendering.
  `thenW w v = v ++ w`, because `Conc (f ≫ g) = Conc g * Conc f` while `wordZToBraid` sends `++` to `*`.
- `Pi1.lean` — the pipeline `SubCube n ↦ concPi1`, plus `concSummary`, `linkVec`, `concPure`.
- `Demo.lean` — the live numbers. `Enumerate`/`Morphisms` are the **slow oracle**: the
  by-definition route through the `Glue` quotients, kept to check the fast model against.

## Where do I find…?

- **the box / precubical-set definition** → `Foundations/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Foundations/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Foundations/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Foundations/Wedge.lean` (+ `Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Foundations/Altitude.lean`
- **the geometric tensor `⊗ᵍ`, computably** → `Foundations/GeoTensor/` (`BP.lean` for the `BPSet`
  version and `cubeTensorIsoBP`); the Day-convolution version is `Foundations/DayTensor.lean`
- **the wedge as the default monoidal product on `BPSet`** → `Foundations/WedgeMonoidal.lean`
- **`⋁` as a strong monoidal functor (`serialWedgeAppend` as tensorator)** →
  `Chains/Segal.lean` (`serialWedgeFunctor : DimList ⥤ BPSet`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **chains-are-wedge-maps** → `Chains/Correspondence.lean` (`equivWedgeCat`)
- **concatenation `chConcat` and its inverse** → `Chains/Segal.lean` / `Chains/Split.lean`
- **`chFunctor` lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`** → `Chains/WedgeLaxMonoidal.lean`
- **generic monoidal helpers (transport, associativity juggling)** → `Foundations/MonoidalTransport.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Arrangements/Braid.lean`, `Arrangements/COM.lean`
- **runs, the run presheaf `Lines`, `runPresheaf`, `runRestrict`** → `Salvetti/Runs.lean`; the
  wedge-map split it rests on is `splitWedgeMorphism` in `Chains/Split.lean`
- **`runBp`, `K.prod runBp`, and `Ch⋆` as a chain category** → `Salvetti/ChStarProduct.lean`
  (`chStarProdIso`/`chStarProdEquiv`); products of `BPSet` → `Foundations/BipointedProd.lean`
- **a chain of `□ⁿ` as an ordered set partition (`beadOf`, `ofBlockMap`)** →
  `Salvetti/ChainBraidFace.lean` (`chFaceEquiv`, `chFaceCatEquiv`, `reflectHom`)
- **the run order `runOrd`, `permOf`, no-double-crossing** → `Salvetti/EventBraid.lean`; its two
  inputs are `Salvetti/RunSegal.lean` (Segal) and `Salvetti/RunRestrict.lean` (face restriction)
- **`Conc` / `ConcPos` themselves** → `Salvetti/EventBraid.lean`
- **the run-free braid grading of `Ch K` (wedge maps only)** → `Chains/WedgeBraid.lean`
  (`crossPerm`, `permLen_crossPerm_comp`, `crossPerm_chConcat`, `chBraid`)
- **the two staircases `□m ∨ □n ⟶ □(m+n)` and their coordinate blocks** →
  `Foundations/WedgeTensor.lean` (`cubeMerge`/`cubeReorder`, `faceEmb_cubeMerge_*`,
  `faceEmb_cubeReorder_*`)
- **which permutations a hom-set of `Ch Zbp` realises** → `Chains/ShuffleHom.lean`
  (`IsShuffle`, `wedgeHomEquiv`, `toSingleHomEquiv`, `onesHomEquivParabolic`)
- **when a refinement is a composite of bead merges** → `Chains/MergeGenerate.lean`
  (`Winf_eq_nonBraiding`, `Winf_iff_crossPerm_eq_one`, `merge_iff`, `Coarser`)
- **when `K` inverts the bead merges, as a condition on cells** → `Chains/SegalCondition.lean`
  (`IsSegal`, `faceComparison`, `isSegal_iff_existsUnique`, `invertsMerges_of_isSegal`); for
  `Hbp □ⁿ` → `Salvetti/HSegal.lean` (`sbox_existsUnique`, `invertsMerges_Hbp_cube`)
- **when a hom-set of `Ch Zbp` is nonempty, and how a refinement factors** → `Chains/Heights.lean`
  (`heights`, `nonempty_hom_iff`), `Chains/CutPresentation.lean` (`existsUnique_factorisation`)
- **the Salvetti comparison** → `Salvetti/SalExec.lean` (`braidSalEquiv`), graded in `SalBraid.lean`
- **an execution as a word + composition, and enumerating them** → `Testing/FastExec.lean`
  (`FExec`, `execs`, `mem_execs_iff`), identified with `Ch⋆` in `Testing/FastEquiv.lean`
- **computing `π₁` of a `SubCube`, with braid words** → `Testing/Pi1.lean` (`concPi1`), on
  `Testing/Presentation.lean`; the theorem that it *is* a presentation →
  `Foundations/FreeGroupoidPresentation.lean`
- **restricting a chain along a face / `EdgeChain`** → `Chains/ChainRestrictions.lean`
- **hom functors and opposites, monoidally** → `Foundations/HomMonoidal.lean`
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Braid/Germ.lean`
- **the Artin presentation** → `Braid/Artin.lean`; **Matsumoto's theorem** → `Braid/Matsumoto.lean`
- **the braid groupoid `FullBraid` (the target of `Conc`)** → `Braid/Graded.lean`
- **the deck-covering short exact sequence** → `Foundations/DeckExact.lean` (built on `DeckSequence`,
  `QuotientCovering`, `QuotientCat`, `NerveQuot`)
- **the non-abelian short five lemma** → `Foundations/ShortFive.lean`
- **the strict free-groupoid universal property** → `Foundations/FreeGroupoidLift.lean`

## Build & conventions

- `lake build CubeChains` builds the results and the retained infrastructure — everything except
  `Testing/`. To gate the whole tree including `Testing/`, sweep every module:
  `lake build $(find CubeChains -name '*.lean' | sed 's#/#.#g; s#\.lean$##')`.
  **No file sets `maxHeartbeats`**; if you find yourself needing one, you have hit a spelling
  mismatch (see below), not a hard proof.
- The tree is **`sorry`-free and axiom-free**: every result reduces to
  `[propext, Classical.choice, Quot.sound]`.  An unproved input enters as a *hypothesis* on a
  definition, never as an `axiom`.
- **`FreeGroupoid` is mathlib's *localization*** (`Groupoid/FreeGroupoidOfCategory.lean`), so
  composition relations are imposed and the vertex group of `Conc K` is `π₁` of the **nerve** — not
  the free group on the graph. `E − V + components` is right only for posets of height 1.
- **`End`/`Aut`/`SingleObj` multiply flipped** (`u * v = v ≫ u`) while `Groupoid.vertexGroup` does
  not. `End` is the one that pairs with `SingleObj`, which is why braid words compose with the
  *later* arrow first — the `thenW` convention in `Testing/Presentation.lean`. Getting it backwards
  leaves every group count unchanged and shows up only as loops failing to be pure braids.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- **Foundational machinery proves the strongest `BPSet`-level statement available.** Never weaken a
  definition or lemma to the presheaf level (`.toPsh ⟶ .toPsh`) so a tactic will fire; callers
  project with `.hom`. `BPSet.Hom` bundles `app_init`/`app_final`, so `BPSet`-level statements carry
  the endpoint conditions for free and keep `⊗`/`▷`/`◁`/`α_`/`λ_`/`ρ_` and `monoidal` applicable.
  When a proof wants to track endpoint data beside a map, **re-point the target** (`BPSet.repoint`)
  rather than pairing value with proof by hand.
- **If you need `erw`, suspect a spelling mismatch, not a hard proof — and it is _not_ an instance
  mismatch.** Traced with `pp.explicit`: both `≫` in a failing goal use the *identical*
  `@Category.toCategoryStruct (Functor Boxᵒᵖ Type) (@Functor.category …)`. The gap is in
  `CategoryStruct.comp`'s **object argument** — the outer `≫` may carry `Y := (X ∨ Y).toPsh` while
  the inner carries `Z := Glue.gluePsh X.finalVertex Y.initVertex`. Those are `rfl`-equal but not
  syntactically equal, and `rw`'s `kabstract` key-matches at `.instances` transparency, which will
  **not** unfold a plain `def` (`wedge2`) to reach `Glue.gluePsh`; `erw`'s full transparency will.
  So `Category.assoc`'s pattern `(?f ≫ ?g) ≫ ?h` can fail on a goal that *prints as exactly that*.
  Other instances: `⋁(n::da)` vs `□n ∨ ⋁da`, and `(K.repoint a b).toPsh` vs `K.toPsh` (a type
  ascription does **not** fix that one). Cures, in order: unify the spelling with a reducible
  wrapper typed the way callers see it; or use `exact`/`.trans`, since elaboration unifies at
  default transparency where `kabstract` will not. Rewriting under `yonedaEquiv` still fails the
  motive — convert to a plain morphism equation first.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.
- **`equivWedgeCat` silently carries `NonSelfLinked` + `AdmitsAltitude`.** Routing through the
  `RefineObj ⟷ Ch` bridge imports both while the statement *looks* unconditional. `Chains/Segal.lean`'s
  `chConcat` / `wedgeInclL/R` are the unconditional replacements.
- Prefer reusing a mathlib construction (Over/comma cats, `FullSubcategory`, Kan extensions,
  `FreeGroupoid`, `Quiver.IsThin`, adhesive/pushout API) over hand-rolling.

## Other docs

- `DESIGN.md` — the conventions/decisions log (precubical identities, universe policy, the
  topos+concrete architecture), with PZ/Z paper references.
- Per-area: `Arrangements/README.md`, `Salvetti/README.md` + `Salvetti/BRAID.md` (why braids).
- `/orient` skill — fast session bootstrap (build, mathlib-reuse table, gotchas).
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
