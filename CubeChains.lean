-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Concurrency.Salvetti.SalBraid
  -- a Salvetti cell's tope is the run word it spells
import CubeChains.Concurrency.Executions.ChStarProduct
  -- Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ — a chain in a product
import CubeChains.Concurrency.Complexification.ChStarSym
  -- Ch (Hbp K) ≌ Ch (K.prod runBp) — the twist
import CubeChains.Concurrency.Salvetti.SalCompare
  -- L models K: chains are faces, runs are topes; Ch (Hbp K) ≌ (Sal L)ᵒᵖ
import CubeChains.Machinery.Arrangement.SalSymmetry
  -- the Sₙ reorientation action on Sal (braidCOM n)
import CubeChains.Concurrency.Complexification.SymReorient
  -- Sₙ acts on Hbp □ⁿ; □ⁿ is rigid, so □ⁿ × run is not
import CubeChains.Concurrency.Salvetti.WallCrossing
  -- atoms are wall crossings; codimension counts walls
import CubeChains.Concurrency.Salvetti.CrossCompare
  -- topeCross = ChainCat.crossPerm; the far leg is W
import CubeChains.Concurrency.Complexification.HPresentation
  -- …so a wall span becomes an arrow of chambers once the merges are inverted
import CubeChains.Machinery.Braid.Artin
  -- the Garside germ vs. the Artin presentation
import CubeChains.Machinery.Braid.PosGerm
  -- the positive braid monoid; PosPureBraid; atoms suffice
import CubeChains.Machinery.Braid.Matsumoto
  -- Matsumoto for Sₙ: the germ IS the Artin monoid/group
import CubeChains.Machinery.Braid.MatsumotoCat
  -- …and between distinct objects: two climbs with the same ends name one arrow
import CubeChains.Machinery.Graded
  -- Graded M: degrees as objects, End n = M n
import CubeChains.Machinery.Braid.Sum
  -- the block-diagonal permSum; permLen is block-additive

-- Retained infrastructure, off the results' path.
import CubeChains.Precubical.Basic.Nerve
  -- nerveRealizeIso : Nerve (realize X) ≅ X
import CubeChains.Precubical.Wedge.GeoTensor.BP
  -- the geometric ⊗ᵍ on BPSet, cubeTensorIsoBP
import CubeChains.Machinery.Arrangement.COMSum
  -- Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂
import CubeChains.Machinery.Cube.SymBox
  -- SBox, J : Box ⥤ SBox, and sHomEquiv
import CubeChains.Machinery.Cube.SymPresheaf
  -- H = J* ∘ J₍!₎, the left Kan extension along J.op
import CubeChains.Machinery.Cube.SymRepresentable
  -- symFree (□ⁿ) ≅ y(▪n), and Sₙ acting on H(□ⁿ)
import CubeChains.Machinery.Cube.HMonad
  -- the monad multiplication is the only H² ⟶ H, while degree 2 carries two
import CubeChains.Concurrency.Complexification.SymRun
  -- H Z ≅ runPresheaf
import CubeChains.Concurrency.Complexification.SymOverRun
  -- H K ⟶ runBp exists; H (□²) ⟶ □² does not
import CubeChains.Concurrency.Merge.MergeClass
  -- the bead merges of Ch X, and the class W they generate
import CubeChains.Concurrency.Grading.WedgeBraid
  -- crossPerm, from the coordinate map alone; crossings add
import CubeChains.Concurrency.Grading.ChainHom
  -- a wedge map is a chain refining a chain; flatten, and crossPerm read off it
import CubeChains.Concurrency.Merge.MergeBraid
  -- a merge crosses nothing: crossPerm = 1 on W
import CubeChains.Concurrency.Merge.MergeGenerate
  -- and the converse: W is the non-braiding property
import CubeChains.Concurrency.Merge.Factorisation
  -- a two-step factorisation is its middle shape; the junction interval
import CubeChains.Concurrency.Merge.Atom
  -- the atom relations of PosBraid, as composable chain maps
import CubeChains.Concurrency.Grading.TopBead
  -- merges into the coarsest chain: existence, and rigidity
import CubeChains.Concurrency.Grading.CodimTwo
  -- crossings add at a junction, so a shape's capacity bounds them; codimension two at degree zero
import CubeChains.Machinery.Localization.FibrationLocalize
  -- ∫P localized at the lifts of W is ∫P̄
import CubeChains.Machinery.Slice
  -- a discrete fibration is one whose slices are the slices of its base
import CubeChains.Machinery.Localization.SliceLocalize
  -- …and localizing them gives the same category, naturally in the base object
import CubeChains.Machinery.Localization.SliceFamily
  -- a functor on C[W⁻¹] is a cocone on the localized slices
import CubeChains.Machinery.Presentation.ChosenInverse
  -- a fully faithful functor, inverted at a chosen preimage of each object
import CubeChains.Machinery.Presentation.SliceColimit
  -- one copy of P d per element over d
import CubeChains.Machinery.Presentation.StrictUnitRefutation
  -- …and why the 0-cells cannot be their image in ∫X
import CubeChains.Machinery.Presentation.IsoComparisonRefutation
  -- …and why the naming of the 0-cells cannot be an isomorphism
import CubeChains.Concurrency.Merge.WedgeSlice
  -- Ch(Z)/d is Ch (⋁d), and W/d is W there
import CubeChains.Concurrency.Merge.WedgeSplit
  -- Ch (X ∨ Y) ≌ Ch X × Ch Y, and W splits with it
import CubeChains.Concurrency.Merge.WedgeLocalize
  -- …localized: a slice over a shape splits off its first bead, naturally
import CubeChains.Concurrency.Merge.SegalCondition
  -- for K the wedge of two cubes is their tensor
import CubeChains.Concurrency.Presentation.ElementsFibration
  -- Ch K is the category of elements of ⋁- ⟶ K
import CubeChains.Concurrency.Complexification.RunClassifier
  -- Hbp Zbp ≅ runBp classifies runs; H is a twist, not a product
import CubeChains.Concurrency.Complexification.HSegal
  -- and for H(□ⁿ) it is: ▪(p+q) is the wedge ▪p ∨ ▪q
import CubeChains.Machinery.Braid.PosAction
  -- PosBraid n acting on the orderings; no units, hence no isos
import CubeChains.Concurrency.Merge.CubeCrossing
  -- …and Ch(□n)[W⁻¹] is NOT that action: the undecorated slice is disconnected
import CubeChains.Concurrency.Presentation.SliceRuns
  -- the runs over a chain, and the exchange: every descent of the weak order is an arrow
import CubeChains.Concurrency.Merge.CubeSpanning
  -- …and the cube's arrows are those, cubeTop being terminal and toChZ a discrete fibration
import CubeChains.Concurrency.Merge.CubeThin
  -- Ch(□n)[W⁻¹] is a poset: every morphism is a word in the atoms, and words are unique
import CubeChains.Concurrency.Merge.CubeWeakOrder
  -- crossLen refined to the permutation itself: a functor to the weak Bruhat order
import CubeChains.Concurrency.Merge.CubeFaces
  -- a chain of a cube is an ordered partition of its axes; two faces meet in one
import CubeChains.Concurrency.Merge.CubeWeakEquiv
  -- Ch(□n)[W⁻¹] IS the right weak Bruhat order on Perm (Fin n), read backwards — the slice, at □n
import CubeChains.Machinery.Localization.ElementsAction
  -- a functor on SingleObj M is an M-set
import CubeChains.Concurrency.Complexification.HPosAction
  -- the decorated chains of □ⁿ acting on the orderings of its axes
import CubeChains.Machinery.Presentation.Elements
  -- C ≌ ⟨generators | relations⟩, and a presented base presents ∫F
import CubeChains.Machinery.Presentation.Comparison
  -- a comparison of two presentations of one category is its generator data
import CubeChains.Machinery.Presentation.Opposite
  -- …and reversing words presents the opposite, which a comparison across a variance needs
import CubeChains.Machinery.Presentation.Localize
  -- …and adjoining a formal inverse to some of the generators presents the localization
import CubeChains.Machinery.Presentation.Contract
  -- …and contracting a family of invertible words keeps one 0-cell per class
import CubeChains.Machinery.Presentation.ContractMap
  -- …functorially, in any map of polygraphs reflecting the contracted family
import CubeChains.Machinery.Presentation.Reduce
  -- …and the cells that suffice — a generator its fellows spell, a relation the kept ones imply
import CubeChains.Machinery.Presentation.SpansMap
  -- …functorially, in any map of polygraphs keeping the kept cells and the chosen words
import CubeChains.Machinery.Presentation.Monoid
  -- a presented monoid presents its one-object category
import CubeChains.Machinery.Presentation.Coproduct
  -- the coproduct of polygraphs presents the disjoint union of categories
import CubeChains.Foundations.Polygraph.Presheaf
  -- 2-polygraphs are the presheaves on PolyShape (Schanuel), so (co)limits of them are cellwise
import CubeChains.Foundations.Polygraph.Day
  -- PolyShape is promonoidal: a splitting says which factor carries each direction
import CubeChains.Foundations.Polygraph.DayCoend
  -- …and the convolution over that profunctor is the coend, by co-Yoneda
import CubeChains.Foundations.Polygraph.Tensor
  -- so the tensor of polygraphs is that convolution, interchange square and all
import CubeChains.Foundations.Polygraph.Monoidal
  -- …whence its associator, its unitors, and their coherence
import CubeChains.Machinery.Presentation.Adjunction
  -- ⟨generators | relations⟩ ⊣ arrows, so a colimit of polygraphs presents the colimit
import CubeChains.Machinery.Presentation.ColimitCells
  -- …whose cells are the colimit of the cells, so the legs reach every 0-cell and every 1-cell
import CubeChains.Concurrency.Presentation.SliceThin
  -- the localized slice is a poset — the one thing that route spends thinness on
import CubeChains.Concurrency.Presentation.SlicePresentation
  -- Ch(K)[W⁻¹] is the localized elements of wedgeHoms K, so the slices glue over it
  -- downward closure in the right weak order, stated on the permutations themselves
import CubeChains.Concurrency.Presentation.SliceRunSet
  -- the runs over d are such a set — the exchange is the downward closure
import CubeChains.Concurrency.Presentation.CutPresentation
  -- Ch Zbp by its bead cuts, and Ch Zbp[W⁻¹] by those plus an inverse for each merge
import CubeChains.Concurrency.Presentation.LiftPresentation
  -- and hence Ch K; the vertex monoids do not follow
import CubeChains.Machinery.Presentation.ElementsLocalize
  -- the picked generators lift along the fibration and generate the inverse image of their class
import CubeChains.Concurrency.Presentation.LocFunctor
  -- Ch f localized, as a functor of K — the side a presentation reads
import CubeChains.Concurrency.Presentation.LiftLocalize
  -- so Ch K[W⁻¹] is presented for every K, by one functor BPSet ⥤ Polygraph
import CubeChains.Concurrency.Presentation.LocPresentation
  -- the atoms of a run, and the codimension-two cells two of them meet in
import CubeChains.Concurrency.Presentation.RunContract
  -- …so the merges contract away, leaving one 0-cell per run
import CubeChains.Concurrency.Presentation.Retraction
  -- the loops at a run are the positive braid monoid
import CubeChains.Concurrency.Presentation.BaseComponent
  -- the run of N events, as a one-object piece of the localized base
import CubeChains.Concurrency.Presentation.BasePresentation
  -- hence Ch Zbp[W⁻¹] presented: the Garside germ, one copy per strand count
import CubeChains.Concurrency.Presentation.ArtinDegreeZero
  -- the degree-zero cells out of a run are Artin's: N−1 atoms and their pairs
import CubeChains.Concurrency.Presentation.RunReduce
  -- a bead cut at a run is a braid loop, and the atoms out of a run
import CubeChains.Concurrency.Presentation.RunArrows
  -- a refinement of Ch K, read as an arrow of the localized cut polygraph
import CubeChains.Concurrency.Presentation.BeadOrder
  -- the beads' permutations in the weak order: a tuple IS a run, and a merge pushes it
import CubeChains.Concurrency.Presentation.TopRefinement
  -- the two runs a chain spans: the merge below it, and its greatest refinement
import CubeChains.Concurrency.Presentation.RunCells
  -- …and those atoms braid, so the codimension-two cuts out of a run are all the relations
import CubeChains.Concurrency.Presentation.RunCellFunctor
  -- …and that polygraph is a functor of K, lying over the contracted one on the nose
import CubeChains.Concurrency.Presentation.CellNatural
  -- …and it presents Ch(K)[W⁻¹] naturally in K, up to the localization's own isomorphism
import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Concurrency.Presentation.PaperPresents
  -- the same cells with no ∫F vocabulary: runs, the cuts out of them, and the two factorisations
import CubeChains.Concurrency.Presentation.PaperFunctor
  -- …and that polygraph is a functor of K, its presentation natural up to the same isomorphism
import CubeChains.Concurrency.Presentation.PaperArtin
  -- …and at the base its cells are Artin's, so Ch Zbp[W⁻¹] is the graded braid monoid
import CubeChains.Concurrency.Presentation.PaperAtoms
  -- …so word length grades Ch(K)[W⁻¹], and every presentation of it carries the paper's 1-cells
import CubeChains.Machinery.Presentation.Taut
  -- a thin category is presented by its own arrows; that germ splits over a product
import CubeChains.Concurrency.Presentation.Dehornoy
  -- so the Dehornoy germ of Sₙ, one per bead, presents the localized slice
import CubeChains.Concurrency.Presentation.HAction
  -- and the decorated chains of □ⁿ are the positive braid action
import CubeChains.Concurrency.Presentation.GarsideFamily
  -- one Dehornoy germ per bead, glued: `garsidePoly K` and its presentation
import CubeChains.Machinery.Rewriting.Newman
  -- Newman, unique normal forms, Hindley–Rosen, at the `Relation` level
import CubeChains.Machinery.Rewriting.Presentation
  -- a convergent orientation presents
import CubeChains.Machinery.Rewriting.Diamond
  -- graded steps closing diamonds make a category thin

/-!
# The claims

`example : T := d` states a claim and checks it against its proof — the type is the specification,
the term is the theorem — and it is a genuine reference, so a declaration reachable from nothing
below is dead rather than merely unmentioned.  `#check` would give neither.
-/

universe u u' v v' w w'

open CategoryTheory CubeChains ChainCat

noncomputable section Claims

/-! ## The goal statements

`Ch(Z)[W⁻¹]` at a fixed strand count, twice over — as a category and as the monoid of loops at the
run, each in the Garside and the Artin naming — then the lift to an arbitrary `K`, instantiated at
the decorated cube. -/

example (N : ℕ) : PosBraid N ≃* RunLoops N := runBraidEquiv N

example (N : ℕ) : ArtinPosBraid N ≃* RunLoops N := runArtinEquiv N

example (K : BPSet) (N : ℕ) (hS : IsSegal K.toPsh)
    (hK : ∀ {d : List ℕ+}, (⋁d ⟶ K) → BPSet.dimSum d = N) :
    (W K).Localization ≌ ((runBase N ⋙ wedgeHomsDescend K hS).Elements)ᵒᵖ :=
  chLocEquivElements K N hS hK

example (n : ℕ) : (W (Hbp.obj (□n))).Localization ≌ PosBraidAction n := hLocEquiv n

example (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n)) :=
  hLocArtinEquiv n

/-! ## The through-line: from the braid monoid to `Ch(K)[W⁻¹]`

Read it downwards and each link consumes the next.  `Ch(K)[W⁻¹]` is the **colimit of its slice
presentations**; a slice is a **wedge of localized cubes**, bead by bead; the localized cube **is
the weak Bruhat order** on its axes; a presentation of the localized base presents the cube; and a
**monoid presentation of the braid monoids** presents the base.  The last is the most fundamental
of the five — every hom-set of `Ch(Z)[W⁻¹]` is a braid monoid — and everything above it is a
lift. -/

example (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f) :
    Presents (Limits.colimit (Polygraph.elementsPoly (wedgeHoms K) P)) ((W K).Localization) :=
  presentsChainsColimit K p hP

example (K : BPSet) (c : Ch K) :
    ((W K).over (X := c)).Localization ≌
      ((W Zbp).over (X := zObj c.dims)).Localization :=
  locOverEquivBase K c

example (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ := locCubeWeakOrder n

example : (FullPosBraid)ᵒᵖ ≌ (((W Zbp).op).Localization) := fullBaseEquiv

example (p : BraidPresentation) : Presents p.poly (FullPosBraid)ᵒᵖ := p.braids

example (N : ℕ) : Function.Surjective (runArtinEquiv N) := (runArtinEquiv N).surjective

/-! ### One functor presents `Ch(K)[W⁻¹]` for every `K`

A presentation of the base whose picked 1-cells generate `(W Zbp).op` lifts along the discrete
fibration: the lifted picked 1-cells generate `(W K).op`, so adjoining a formal inverse to each
presents `Ch(K)[W⁻¹]` — and the polygraph doing it is the value of one functor on `BPSet`. -/

example (K : BPSet) : Presents (ChainCat.chCutLocFunctor.obj K) (((W K).op).Localization) :=
  ChainCat.chCutLocPresentation K

/-! …and naturally in `K`: the polygraph functor against the localized pushforward.  The comparison
is an isomorphism and not an equality, `presentsLocalization` reaching the localization through
`equivalenceFromModel`; nothing about it is chosen, since it is the only comparison restricting to
`cutComparison` along `chCutLocIncl`. -/

example {K K' : BPSet} (f : K ⟶ K') :
    (ChainCat.chCellFunctor.map f).functor ⋙ (ChainCat.chCellPresentation K').E
      ≅ (ChainCat.chCellPresentation K).E ⋙ ChainCat.chLocOpMap f :=
  ChainCat.chCellPresentationIso f

/-! ### …and those cells with no `∫F` vocabulary

A codimension-two refinement out of a run factors in exactly two ways (`oneCutEquivBool`, at every
`K`, the middle being pinned by its shape), and `factorWords` reads each factorisation as a word of
codimension-one cuts out of runs.  A **degree-two object** needs no refinement beside it: the merge
onto it and its greatest refinement (`topOf`, that merge's complement — run backwards inside every
bead) are both functions of the object, so `objWords` takes the object to its two words.
`Paper.poly K` is the polygraph those cells make: 0-cells the runs on the nose, 1- and 2-cells the
objects of degree one and two — and it
presents `Ch(K)[W⁻¹]`. -/

example (K : BPSet) : Run K ≃ (ChainCat.chCollapse K).V := ChainCat.Paper.runEquiv K

example (K : BPSet) {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : ChainCat.codim f = 2)
    (ε : Bool) :
    Quiver.Path (ChainCat.Paper.runPt (ChainCat.Paper.bottomRun b)) (ChainCat.Paper.runPt X) :=
  ChainCat.Paper.factorWords f hf ε

example (K : BPSet) (e : Ch K) (he : ChainCat.degree e = 2) (ε : Bool) :
    Quiver.Path (ChainCat.Paper.runPt (ChainCat.Paper.bottomRun e))
      (ChainCat.Paper.runPt (ChainCat.Paper.topOf e).1) :=
  ChainCat.Paper.objWords e he ε

example (K : BPSet) : Polygraph := ChainCat.Paper.poly K

example (K : BPSet) : Presents (ChainCat.Paper.poly K) (((W K).op).Localization) :=
  ChainCat.Paper.paperPresents K

/-! …and that polygraph is a functor of `K`, its presentation natural up to the isomorphism a
localization functor is pinned to and no more. -/

example : BPSet ⥤ Polygraph := ChainCat.Paper.polyFunctor

example (K : BPSet) : ChainCat.Paper.polyFunctor.obj K = ChainCat.Paper.poly K := rfl

example {K K' : BPSet} (f : K ⟶ K') :
    (ChainCat.Paper.polyFunctor.map f).functor ⋙ (ChainCat.Paper.paperPresents K').E
      ≅ (ChainCat.Paper.paperPresents K).E ⋙ ChainCat.chLocOpMap f :=
  ChainCat.Paper.paperPresentationIso f

example (K : BPSet) :
    ChainCat.Paper.paperPresentationIso (𝟙 K) = eqToIso (ChainCat.Paper.paperSquare_id K) :=
  ChainCat.Paper.paperPresentationIso_id K

/-! ### …and at the base its cells are Artin's

A run of `Zbp` is its strand count, so every cell is a loop and its object is the only datum.  The
two codimension-two species are **shapes**: one bead of dimension three, or two of dimension two,
and the two cuts are adjacent exactly in the first case — which is what fixes the orientation of
`oneCutEquivBool` and hence which word is a relation's source. -/

example {N : ℕ} (α : ChainCat.Paper.Cell 2 (ChainCat.Paper.zRun N) (ChainCat.Paper.zRun N)) :
    ((ChainCat.Paper.cellAtomPairEquiv N α).hi : ℕ)
        = ((ChainCat.Paper.cellAtomPairEquiv N α).lo : ℕ) + 1
      ↔ (3 : ℕ+) ∈ α.obj.dims :=
  ChainCat.Paper.cell_adj_iff α

example : ChainCat.Paper.poly Zbp ≅ artinBP.poly := ChainCat.Paper.paperArtinIso

/-! ### The polygraph tensor is a Day convolution

`PolyShape` is not monoidal — `cell m n ⊗ cell m' n'` would want a 3-cell — but it is
**promonoidal**, and that is all a convolution needs: a `Split` says which of two factors carries
each direction of a shape.  Read through `polyToPsh`, `Polygraph.prod` *is* the convolution for that
profunctor, so the interchange square is not an axiom of the tensor: it is the `Split.square`
component at `cell 2 2`, the one splitting that puts an edge in each factor. -/

example (F G : PolyShapeᵒᵖ ⥤ Type) (c : PolyShape) :
    Limits.IsColimit (Polygraph.dayCowedge F G c) :=
  Polygraph.dayIsCoend F G c

example (P Q : Polygraph.{0, 0, 0}) :
    Polygraph.dayObj (Polygraph.cellsPsh P) (Polygraph.cellsPsh Q) ≅
      Polygraph.cellsPsh (Polygraph.prod P Q) :=
  Polygraph.dayIso P Q

example (P Q : Polygraph.{0, 0, 0}) (t : Quiver.Total (GenObj P.Gen))
    (t' : Quiver.Total (GenObj Q.Gen)) :
    (Polygraph.ofDayCells P Q ⟨PolyShape.Split.square, t, t'⟩).cell
      = Polygraph.ProdRel.interchange t.hom t'.hom :=
  Polygraph.cell_ofDayCells_square P Q t t'

example : MonoidalCategory Polygraph.{0, 0, 0} := inferInstance

open MonoidalCategory in
example (P Q : Polygraph.{0, 0, 0}) : P ⊗ Q = Polygraph.prod P Q :=
  Polygraph.tensorObj_eq P Q

/-! ## `Ch(K)[W⁻¹]` is presented, for every `K`

### …by a category's own arrows

A **thin** category is presented by the germ of its own arrows: 1-cells the arrows, 2-cells
`f·g ↦ f ≫ g` and `ε ↦ 𝟙`, so that every word collapses to its composite. -/

example (C : Type) [Category.{0} C] [Quiver.IsThin C] :
    Presents (Polygraph.taut C) C :=
  Polygraph.tautPresents C

/-! A 2-cell is a word, so a pair of readings is one reading of the product's germ: the germ of a
product **is** the categorical product of the germs, the identity relation padding the shorter
word. -/

open Limits in
example (C D : Type) [Category.{0} C] [Category.{0} D] :
    Polygraph.taut (C × D) ≅ Polygraph.taut C ⨯ Polygraph.taut D :=
  Polygraph.tautProdIso C D

example : CategoryTheory.MonoidalCategory FullPosBraid := inferInstance

/-! ### …by the **braid presentation's own** cells

The strand-`N` 0-cell of a braid presentation *is* the strand count, and its generators are the
braids there. -/

example (p : BraidPresentation) (N : ℕ) : p.braids.at' (p.pt N) = Opposite.op N :=
  p.braids_at' N

example (p : BraidPresentation) {N : ℕ} (s : p.S N) :
    p.braids.arrow (p.gen s) = braidLoop N (p.braid s) :=
  p.braids_arrow s

example (p : BraidPresentation) : Function.Bijective p.pt :=
  ⟨p.pt_injective, fun x => p.exists_pt x⟩

/-! …and the two named bases are two values of one construction. -/

example {S : ℕ → Type} (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) : BraidPresentation :=
  BraidPresentation.ofMonoids rels e

example : BraidPresentation := germBP

example : BraidPresentation := artinBP

example : germBP.BySimples := germBP_bySimples

example : artinBP.BySimples := artinBP_bySimples

example (N : ℕ) : germBP.S N = Equiv.Perm (Fin N) := rfl

example (N : ℕ) : artinBP.S N = Fin (N - 1) := rfl

example (N : ℕ) (k : Fin (N - 1)) :
    artinBP.braids.arrow (artinBP.gen k) = braidLoop N (posPerm (adjT k)) :=
  artinBraids_arrow N k

/-! ### The 0-cells of the slice: one permutation per bead

`wedgeOrder l` is one right weak order per bead.  A tuple's **block sum** is the permutation of the
events it performs, and the tuple's own chain — the beads' runs, concatenated — is the run crossing
it, bijectively: the tuples over `d` *are* the runs over `d`. -/

example (l : List ℕ+) (x : wedgeOrder l) : Equiv.Perm (Fin (BPSet.dimSum l)) := blockSum l x

example (l : List ℕ+) : Function.Injective (blockSum l) := blockSum_injective l

example (l : List ℕ+) (x y : wedgeOrder l) :
    Nonempty (x ⟶ y) ↔ WeakOrder.of (blockSum l x) ≤ WeakOrder.of (blockSum l y) :=
  nonempty_hom_iff_blockSum_le l x y

example (d : Ch Zbp) {N : ℕ} (h : BPSet.dimSum d.dims = N) :
    wedgeOrder d.dims ≃ RunAt d N :=
  beadEquiv d h

/-! …so a **merge** acts by pushing that run, and on the labels it left-translates by the merge's
crossing permutation — `crossPerm f * blockSum x`, with the beads' crossings assembled by
`crossPerm_chConcat` and no bead index in sight. -/

example {d' d : Ch Zbp} (f : d' ⟶ d) {N : ℕ} (h : BPSet.dimSum d.dims = N)
    (h' : BPSet.dimSum d'.dims = N) (x : wedgeOrder d'.dims) :
    (beadEquiv d h (beadMap f x)).perm = crossPerm h' f * (beadEquiv d' h' x).perm :=
  perm_beadMap f h h' x

example {d' d : Ch Zbp} (f : d' ⟶ d) : wedgeOrder d'.dims ⥤ wedgeOrder d.dims := beadFunctor f

example (d : Ch Zbp) : beadFunctor (𝟙 d) = 𝟭 (wedgeOrder d.dims) := beadFunctor_id d

example {d'' d' d : Ch Zbp} (f : d'' ⟶ d') (g : d' ⟶ d) :
    beadFunctor (f ≫ g) = beadFunctor f ⋙ beadFunctor g :=
  beadFunctor_comp f g

/-! ### The Dehornoy germ, and one per bead

At one cube every permutation is a 0-cell, so the germ there is the Dehornoy germ of `Sₙ` and it
presents the right weak Bruhat order.  Over a junction the germ splits as the categorical
product — `tautProdIso`, because the beads' tuples already *are* a product of categories. -/

example (n : ℕ) : Presents (dehornoyPoly n) (WeakOrder n) := dehornoyPresents n

/-! …where a 1-cell *is* the simple it crosses: a rise in the weak order is a germ step at the gap,
crossed length-additively, and every such step is a rise. -/

example (n : ℕ) {x y : WeakOrder n} (e : (dehornoyPoly n).Gen x y) :
    GermStep (posPerm ((WeakOrder.perm x)⁻¹ * WeakOrder.perm y)) (WeakOrder.perm x)
      (WeakOrder.perm y) :=
  germStep_of_dehornoyGen e

example (n : ℕ) {β : PosBraid n} {x y : WeakOrder n}
    (h : GermStep β (WeakOrder.perm x) (WeakOrder.perm y)) : (dehornoyPoly n).Gen x y :=
  dehornoyGen_of_germStep h

example (n : ℕ) : Presents (dehornoyPoly n) (((W (□n)).Localization)ᵒᵖ) := dehornoyCube n

open Limits in
example (n : ℕ+) (rest : List ℕ+) :
    garsidePolyList (n :: rest) ≅ dehornoyPoly (n : ℕ) ⨯ garsidePolyList rest :=
  garsidePolyListCons n rest

open Limits in
example (l l' : List ℕ+) :
    garsidePolyList (l ++ l') ≅ garsidePolyList l ⨯ garsidePolyList l' :=
  garsidePolyListAppend l l'

/-! …and the wedge splitting reads the localized chains of `⋁l` as the beads' orders, so the beads'
germs present the localized slice over any chain. -/

example (l : List ℕ+) : wedgeOrder l ≌ ((W (⋁l)).Localization)ᵒᵖ := wedgeLocOrder l

example (d : Ch Zbp) :
    Presents (garsidePolyList d.dims) ((((W Zbp).over (X := d)).Localization)ᵒᵖ) :=
  garsideSlicePresents d

/-! …naming the beads' runs, concatenated — definitionally at every step, which is what the
comparison asks of it. -/

example (d : Ch Zbp) (x : wedgeOrder d.dims) :
    (garsideSlicePresents d).at' ⟨x⟩
      = Opposite.op (((W Zbp).over (X := d)).Q.obj (wedgeRunOver d x).1) :=
  garsideSlicePresents_at d x

example : Ch Zbp ⥤ Polygraph.{0, 0, 0} := garsideFam

example {d' d : Ch Zbp} (f : d' ⟶ d) :
    (garsideFam.map f).functor ⋙ (garsideSlicePresentation d).E
      = (garsideSlicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  garsideSlice_hP f

/-! ### …so the colimit of the copies presents `Ch(K)[W⁻¹]`

For every family of slice presentations whose comparison is an equality of functors, and hence for
the Garside one, with no hypothesis on `K`. -/

example (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f) :
    Presents (Limits.colimit (Polygraph.elementsPoly (wedgeHoms K) P)) ((W K).Localization) :=
  presentsChainsColimit K p hP

example (K : BPSet) : Presents (garsidePoly K) ((W K).Localization) :=
  garsidePresents K

/-! ### At the cube it is the weak Bruhat order -/

example (n : ℕ) : Presents (garsidePoly (□n)) ((WeakOrder n)ᵒᵖ) := garsideCube n

example {K K' : BPSet} (f : K ⟶ K') : (W K).Localization ⥤ (W K').Localization := chLocMap f

example (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ := chLocMap_id K

example {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g := chLocMap_comp f g

/-! …and the side a presentation reads is a functor to `Cat`, which is what the naturality of
`paperPresentationIso` is stated against. -/

example : BPSet ⥤ Cat := chLocOpFunctor

example {K K' : BPSet} (f : K ⟶ K') :
    chLocOpFunctor.map f = (chLocOpMap f).toCatHom := chLocOpFunctor_map f

example {P : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] (p : Presents P C) :
    Polygraph.Presents.Map p p :=
  Polygraph.Presents.Map.refl p

example {P Q R : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] {p : Presents P C}
    {q : Presents Q C} {r : Presents R C}
    (m : Polygraph.Presents.Map p q) (n : Polygraph.Presents.Map q r) :
    Polygraph.Presents.Map p r :=
  m.trans n

example : ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left := exists_not_isRun_over

example : Presents Cut.poly ((Ch Zbp)ᵒᵖ) := zCutPresentation

noncomputable example {P : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] (p : Presents P C)
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) {W : MorphismProperty C}
    (hW : W = (p.pickedArrows S).multiplicativeClosure) :
    Presents (Polygraph.invPoly P S) W.Localization :=
  p.presentsLocalization S hW

noncomputable example :
    Presents (Polygraph.invPoly Cut.poly Cut.mergeGen) ((W Zbp).op).Localization :=
  zCutLocPresentation

example (K : BPSet) {P : Polygraph.{w', u'}} (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    Presents (p.elementsPoly (wedgeHoms K)) ((Ch K)ᵒᵖ) :=
  chPresentation K p

example (K : BPSet) : Presents (chCutPoly K) ((Ch K)ᵒᵖ) := chCutPresentation K

example (n : ℕ) : Presents (hLocPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) := hLocPresentation n

example (n : ℕ) :
    Presents (hLocArtinPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) := hLocArtinPresentation n

example (n : ℕ) : Presents (hLocPoly n) ((PosBraidAction n)ᵒᵖ) := hLocActionPresentation n

/-! ## …and the two spellings of one strand component

The Garside germ presents `PosBraid N` on the nose; the Artin spelling reaches the same component
through `Artin-from-Garside`. -/

example (N : ℕ) : Presents (monoidPoly (PosGermRel N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  germPresentation N

example (N : ℕ) : Presents (monoidPoly (ArtinRel N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  artinComponent N

/-! ## Presentations, abstractly -/

example {V : Type u} {Gen : V → V → Type w} {C : Type u'} [Category.{v} C] [Quiver.IsThin C]
    (φ : GenObj Gen ⥤q C)
    (hspan : ∀ (x y : GenObj Gen) (_ : φ.obj x ⟶ φ.obj y), Nonempty (Quiver.Path x y))
    (hcover : ∀ c : C, ∃ x, Nonempty (φ.obj x ≅ c)) :
    Presents (Polygraph.thin Gen) C :=
  Presents.ofThin φ hspan hcover

example {P : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] (p : Presents P C)
    (F : C ⥤ Type w) : Presents (p.elementsPoly F) F.Elements :=
  p.elements F

example {C : Type u} [Category.{v} C] (P : C ⥤ Type w) (p : P.Elements) :
    End p ≃* CategoryOfElements.stabilizer P p :=
  CategoryOfElements.endEquivStabilizer P p

example {S : Type u} (rels : FreeMonoid S → FreeMonoid S → Prop) :
    Presents (monoidPoly rels) ((SingleObj (PresentedMonoid rels))ᵒᵖ) :=
  presentedMonoidPresentation rels

example {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})
    (A : GenObj (Limits.colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (Limits.colimit.ι D j).pre.obj x = A :=
  Polygraph.exists_colimit_ι_obj D A

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
    (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f) :
    Presents (Limits.colimit (Polygraph.elementsPoly X P))
      ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  Polygraph.presentsSliceColimit X V p hP

example {B : Type u} [Category.{v} B] (V : MorphismProperty B) (P : B ⥤ Type w)
    (hP : V.IsInvertedBy P) :
    (Localization.elementsDescent V P hP).IsLocalization
      (V.inverseImage (CategoryOfElements.π P)) :=
  Localization.isLocalization_elementsDescent V P hP

/-! ## The cube slice is the weak Bruhat order -/

example (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) := locCube_isThin n

example {n : ℕ} {c c' : Ch (□n)} :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') ↔ weakClass c' ≤ weakClass c :=
  nonempty_loc_hom_iff

/-! ## The geometry the presentations rest on -/

example (n : ℕ) : SeparatesMerges (□n) := separatesMerges_cube n

example {n : ℕ} {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h₁ : codim u₁ = 1) (h₂ : codim u₂ = 1) (hne : d₁ ≠ d₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), codim v₁ = 1 ∧ codim v₂ = 1 :=
  exists_join u₁ u₂ h₁ h₂ hne

example {K : BPSet} {A A' S S' : List ℕ+} {a d d' : Ch K}
    (u : a ⟶ d) (u' : a ⟶ d') (ha : a.dims = A ++ S) (hd : d.dims = A' ++ S)
    (hd' : d'.dims = A ++ S') :
    ∃ (e : Ch K) (v : d ⟶ e) (v' : d' ⟶ e), e.dims = A' ++ S' ∧ u ≫ v = u' ≫ v' :=
  exists_join_of_split u u' ha hd hd'

example {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    IsPushout (wedge2Map f (𝟙 Y)) (wedge2Map (𝟙 X) g)
      (wedge2Map (𝟙 X') g) (wedge2Map f (𝟙 Y')) :=
  wedge2Map_isPushout f g

example {K : BPSet} {a b : Ch K} {N : ℕ} (h : BPSet.dimSum a.dims = N) (f : a ⟶ b) :
    W K f ↔ ChainCat.crossPerm h f = 1 :=
  W_iff_crossPerm_eq_one h f

example {K : BPSet} {a b : Ch K} (f : a ⟶ b) : W K f ↔ Monotone (coordMap f.φ) :=
  W_iff_monotone_coordMap f

example {a b : List ℕ+} {N : ℕ} (χ : ⋁b ⟶ □N) :
    (⋁a ⟶ ⋁b) ≃ {x : ⋁a ⟶ □N // Nonempty ((⟨a, x⟩ : Ch (□N)) ⟶ ⟨b, χ⟩)} :=
  chainHomEquiv χ

example {d d' : List ℕ+} : Nonempty (⋁d ⟶ ⋁d') ↔ Coarser d d' := nonempty_wedgeHom_iff_coarser

example {a b : Ch Zbp} (f : a ⟶ b) : Factorisation f ≃ MidShape a b := factorisationEquiv f

/-! ### Codimension two at degree zero: two factorisations, two species, and the crossing -/

example {a b : Ch Zbp} (f : a ⟶ b) : OneCut f ≃ (cutsOf f : Finset ℕ) := oneCutEquivCuts f

example {a b : Ch Zbp} (f : a ⟶ b) (hf : codim f = 2) : OneCut f ≃ Bool := oneCutEquivBool f hf

example {a b : Ch Zbp} {f : a ⟶ b} (F : OneCut f) (hf : codim f = 2) : codim F.1.snd = 1 :=
  F.codim_snd hf

/-! **The two codimension-two species, as geometry**: the chain a pair of cuts share is one bead of
dimension three when they are consecutive, and two beads of dimension two when they are apart.
`boundaries` pins the shape, so the species is which junctions are missing — not a capacity. -/

example {n : ℕ} {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    ∃ p q : ℕ, (pairChain n i j hij).dims = 𝟙^p ++ (3 : ℕ+) :: 𝟙^q :=
  dims_pairChain_of_adj hij hadj

example {n : ℕ} {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    ∃ p m q : ℕ,
      (pairChain n i j hij).dims = 𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q) :=
  dims_pairChain_of_apart hij hfar

example {N : ℕ} {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d) (k : Fin (N - 1)) :
    Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k : ℕ) + 1 ∈ cutsOf f :=
  nonempty_hom_atomComp_iff f k

example {N : ℕ} {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d) (hcod : codim f = 2) :
    ∃ i j : Fin (N - 1), (i : ℕ) < (j : ℕ) ∧
      ∀ k : Fin (N - 1), Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k = i ∨ k = j) :=
  exists_atomPair_of_codim_two f hcod

example {N : ℕ} {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d) (hcod : codim f = 2) :
    ∃ i j : Fin (N - 1), (i : ℕ) < (j : ℕ) ∧
      (∀ k : Fin (N - 1), Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k = i ∨ k = j)) ∧
      (((j : ℕ) = (i : ℕ) + 1 ∧
          atomLoop N i ≫ atomLoop N j ≫ atomLoop N i
            = atomLoop N j ≫ atomLoop N i ≫ atomLoop N j) ∨
        ((i : ℕ) + 1 < (j : ℕ) ∧ atomLoop N i ≫ atomLoop N j = atomLoop N j ≫ atomLoop N i)) :=
  artin_of_codim_two f hcod

example {N : ℕ} {i j : Fin (N - 1)} (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomLoop N i ≫ atomLoop N j = atomLoop N j ≫ atomLoop N i :=
  atomLoop_comm hij

example {N : ℕ} {i j : Fin (N - 1)} (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomLoop N i ≫ atomLoop N j ≫ atomLoop N i
      = atomLoop N j ≫ atomLoop N i ≫ atomLoop N j :=
  atomLoop_braid hij

example {N : ℕ} {a b : Ch Zbp} (ha : BPSet.dimSum a.dims = N) (f : a ⟶ b) :
    ∃ l : List (Fin (N - 1)), l.length = permLen (ChainCat.crossPerm ha f) ∧
      conj ha f = l.foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) :=
  exists_atomWord_conj ha f

example {N : ℕ} {x : GenObj Cut.Refine} (e : x ⟶ Cut.vert (zObj (𝟙^N))) :
    ∃ k : Fin (N - 1), x.as = zObj (atomComp N k) :=
  Cut.exists_atomComp e

example {N : ℕ} {k : Fin (N - 1)} {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)} (hW : ¬ W Zbp f) :
    f = atomOnes N k :=
  eq_atomOnes hW

example (l r : List ℕ+) : ¬ W Zbp (atomHom l r) := not_W_atomHom l r

example (n : ℕ) : (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Equiv.Perm (Fin n) := onesTopEquiv n

example {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    ¬ W (Hbp.obj (□n)) (wallLeg w k) := not_W_wallLeg w k

example {n : ℕ} (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    chamberLoc w ⟶ chamberLoc (w * adjT k) := wallCrossLoc w k

example {K : BPSet} {x y : Ch K} {N : ℕ} {h : BPSet.dimSum x.dims = N} {f g : x ⟶ y}
    (hc : ChainCat.crossPerm h f = ChainCat.crossPerm h g) : f = g :=
  hom_ext_of_crossPerm hc

example {d : Ch Zbp} {N : ℕ} {c : Ch Zbp} (hd : BPSet.dimSum d.dims = N)
    (hc : BPSet.dimSum c.dims = N) (a : c ⟶ d) (r : Fin N) :
    (((CubeChains.dimComp d.dims hd).index (ChainCat.crossPerm hc a r) : ℕ))
      = ((CubeChains.dimComp d.dims hd).index r : ℕ) :=
  index_crossPerm hd hc a r

/-! ## The fibration, and the Segal condition -/

example (K : BPSet) : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ := chEquivElements K

example (K : BPSet) (hS : IsSegal K.toPsh) : (chDescent K hS).IsLocalization (W K) :=
  isLocalization_chDescent K hS

example (K : PrecubicalSet) :
    IsSegal K ↔ ∀ (p q : ℕ) (x : K.cells p) (y : K.cells q),
      K.vertexEnd true x = K.vertexEnd false y →
      ∃! c : K.cells (p + q), frontFace K p q c = x ∧ backFace K p q c = y :=
  isSegal_iff_existsUnique K

example (n : ℕ) : IsSegal (H.obj (□n).toPsh) := isSegal_H_cube n

example (K : BPSet) (h : InvertsMerges K) : SeparatesMerges K :=
  separatesMerges_of_invertsMerges K h

/-! ## `H` lies over the runs, and over nothing else -/

example : H ⟶ (Functor.const PrecubicalSet).obj runPresheaf := HOverRun

example : Hbp ⟶ (Functor.const BPSet).obj runBp := HbpOverRun

example : IsEmpty (H.obj (□2).toPsh ⟶ ((□2).prod runBp).toPsh) := isEmpty_cubeProdHom

example {r s : Run (Hbp.obj Zbp)} (h : BPSet.dimSum r.dims = BPSet.dimSum s.dims) : r = s :=
  run_HbpZbp_eq h

/-! ## The braid comparison

One datum — `L` models `K`: an equivalence of bases under which the runs refining a chain are the
topes above its face.  From it both comparisons follow, and the braid arrangement models the
cube. -/

example {E : Type} (L : COM E) (K : BPSet) (base : (Ch K)ᵒᵖ ≌ COM.Face L)
    (fibre : Lines K ≅ base.functor ⋙ COM.salFunctor L) : Models L K :=
  ⟨base, fibre⟩

example {E : Type} {L : COM E} {K : BPSet} (m : Models L K) : (Lines K).Elements ≌ Sal L :=
  m.salEquiv

example {E : Type} {L : COM E} {K : BPSet} (m : Models L K) : Ch (Hbp.obj K) ≌ (Sal L)ᵒᵖ :=
  m.hbpEquiv

example (n : ℕ) : Models (braidCOM n) (□n) := braidModels n

example (n : ℕ) : (Lines (□n)).Elements ≌ Sal (braidCOM n) := (braidModels n).salEquiv

example {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permLen (RunWedge.permOf (f ≫ g))
      = permLen (RunWedge.permOf f) + permLen (RunWedge.permOf g) :=
  RunWedge.permOf_noDoubleCross f g

example (K : BPSet) : Ch⋆ K ⥤ FullBraid := ConcPos K

example {n : ℕ} : (Ch (□n))ᵒᵖ ≌ COM.Face (braidCOM n) := chFaceCatEquiv

example {n : ℕ} : Ch⋆ (□n) ≃ ExecData n := execEquiv

example {n : ℕ} {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    ChStar.stepPerm f = (x.runWord).trans (y.runWord).symm :=
  ChStar.stepPerm_eq f

example (n : ℕ) : Ch (Hbp.obj (□n)) ≌ (Sal (braidCOM n))ᵒᵖ := hbpBraidSalEquiv n

example {n : ℕ} {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) :
    ChainCat.crossPerm (hbpCubeStrands a.map) f
      = topeCross ((hbpBraidSalEquiv n).functor.obj a).unop
          ((hbpBraidSalEquiv n).functor.obj b).unop :=
  crossPerm_eq_topeCross f

example {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (reorientCh n σ).hom.toFunctor ⋙ (hbpBraidSalEquiv n).functor
      = (hbpBraidSalEquiv n).functor ⋙ (salReorientFunctor σ).op :=
  reorientCh_comp_hbpBraidSalEquiv σ

example (n : ℕ) : Ch (Hbp.obj (□n)) ⥤ PosBraidAction n := chToAction n

example (n : ℕ) :
    Function.Surjective fun r : Run (Hbp.obj (□n)) => (chToAction n).obj r.chain :=
  chToAction_obj_surjective n

example (n : ℕ) : GarsideBraid n ≃* ArtinBraid n := garside_equiv_artin n

example (n : ℕ) : PosBraid n ≃* ArtinPosBraid n := posBraid_equiv_artinPos n

/-! ## The refutations -/

example : Presents (Limits.colimit (Polygraph.elementsPoly X₂ P₂F))
    ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  presentsColim₂

example :
    (∀ {d' d : Loop} (f : d' ⟶ d), Nonempty ((PLoop.map f).functor ⋙ (presentsLoop d).E
        ≅ (presentsLoop d').E ⋙ overMapLoc WLoop f))
      ∧ (¬ ∀ {d' d : Loop} (f : d' ⟶ d), (PLoop.map f).functor ⋙ (presentsLoop d).E
        = (presentsLoop d').E ⋙ overMapLoc WLoop f)
      ∧ IsEmpty (Presents (Limits.colimit (Polygraph.elementsPoly XLoop PLoop))
        ((WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization)) :=
  isoComparison_not_enough

example : W Zbp (runMerge (zObj ([2] : List ℕ+)) dimSum_two) ∧
    IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) ∧ Nonempty (zObj (𝟙^2) ⟶ zObj (𝟙^2)) :=
  merge_fibres_clash

example {n : ℕ} (i : Fin (n - 1)) : ¬ Function.Surjective (posToBraid n) :=
  not_surjective_posToBraid i

example {n : ℕ} (hn : 2 ≤ n) (p : PosBraidAction n) :
    Submonoid.closure {f : @End (PosBraidAction n) _ p | ∃ σ : Equiv.Perm (Fin n),
      f.val = posPerm σ} ≠ ⊤ :=
  end_not_generated_by_simples hn p

example : ¬ ∀ (K : BPSet) (a b : List ℕ+) (φ : ⋁a ⟶ ⋁b) (β : ⋁b ⟶ Hbp.obj K),
    desym K (φ ≫ β) = φ ≫ desym K β :=
  not_desym_natural

example : ¬ InvertsMerges runBp := not_invertsMerges_runBp

example : ¬ InvertsMerges (Hbp.obj Zbp) := not_invertsMerges_Hbp_Zbp

example {n : ℕ} (hn : 2 ≤ n) : IsEmpty (H.obj (□n).toPsh ⟶ (□n).toPsh) := isEmpty_cubeHom hn

example {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ y : Ch (Hbp.obj (□n)), ∀ A : Ch (Hbp.obj (□n)), Nonempty (y ⟶ A) :=
  not_exists_hom_to_all_cube hn

example {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1)
    {Θ : (□n).prod runBp ⟶ (□n).prod runBp} {c : □n ⟶ □n}
    (hover : Θ ≫ BPSet.prodFst (□n) runBp = BPSet.prodFst (□n) runBp ≫ c) :
    (chSymEquiv (□n)).functor ⋙ ChainCat.pushforward Θ
      ≠ (reorientCh n σ).hom.toFunctor ⋙ (chSymEquiv (□n)).functor :=
  not_reorientCh_of_over_base hσ hover

example : ¬ Function.Surjective (faceComparison (□(1 + 1)).toPsh 1 1) :=
  not_surjective_faceComparison_cube_two

example : ¬ Function.Injective (faceComparison (H.obj Z) 1 1) := not_injective_faceComparison_H_Z

example : ¬ IsSegal (□(1 + 1)).toPsh := not_isSegal_cube_two

example {L K : BPSet} (S : ProductSplitting L K) (c : ⋁[1 + 1] ⟶ K) : ¬ InvertsMerges L :=
  not_invertsMerges_of_splitting S c

example : ¬ Nonempty ((W (□2)).Localization ≌ PosBraidAction 2) :=
  not_nonempty_equiv_posBraidAction

/-! ## Retained infrastructure -/

example : MonoidalCategory PrecubicalSet := GeoTensor.geoMonoidal

example {E₁ : Type u} {E₂ : Type u'} (L₁ : COM E₁) (L₂ : COM E₂) :
    Sal (L₁.directSum L₂) ≌ Sal L₁ × Sal L₂ :=
  COM.salSumEquiv L₁ L₂

example (X : PrecubicalSet) : PrecubicalSet.Nerve.obj (PrecubicalSet.realize.obj X) ≅ X :=
  PrecubicalSet.nerveRealizeIso X

example (m n : ℕ) : □m ⊗ᵍ □n ≅ □(m + n) := GeoTensor.cubeTensorIsoBP m n

example {K : BPSet} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    CubeChain.RefineObj K.init K.final ≌ Ch K :=
  CubeChain.equivWedgeCat h₁ h₂

/-! ## What a colimit presentation's cells evaluate to

A 0-cell of the colimit is a slice 0-cell in its own copy, and a word there evaluates to that
slice's evaluation, transported. -/

example (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)
    (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (P.obj (Polygraph.eltBase (wedgeHoms K) c)).V) :
    (presentsChainsColimit K p hP).at' (ιV K P c a)
      = (locEquivElements K).inverse.obj
          ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp)
            (Polygraph.eltBase (wedgeHoms K) c) c.unop.2).obj
              ((p (Polygraph.eltBase (wedgeHoms K) c)).at' ⟨a⟩)) :=
  at_ιV K P p hP c a

example (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f)
    (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : GenObj (P.obj (Polygraph.eltBase (wedgeHoms K) c)).Gen} (w : Quiver.Path a b) :
    (presentsChainsColimit K p hP).eval.map
        ((Limits.colimit.ι (Polygraph.elementsPoly (wedgeHoms K) P) c).words.map w)
      = eqToHom (at_ιV K P p hP c a.as) ≫ (locEquivElements K).inverse.map
            ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp)
              (Polygraph.eltBase (wedgeHoms K) c) c.unop.2).map
                ((p (Polygraph.eltBase (wedgeHoms K) c)).eval.map w))
          ≫ eqToHom (at_ιV K P p hP c b.as).symm :=
  eval_ιWord K P p hP c w


/-! ## Abstract rewriting

Newman, unique normal forms and Hindley–Rosen at the `Relation` level, and the bridge from a
convergent orientation of a polygraph's 2-cells to `Presents.ofDesc`'s completeness obligation. -/

example {α : Type u} {r : α → α → Prop} (hwf : Relation.Terminating r)
    (h : Relation.LocallyConfluent r) : Relation.Confluent r :=
  h.confluent hwf

example {α : Type u} {r : α → α → Prop} (hc : Relation.Confluent r)
    (hwf : Relation.Terminating r) (a : α) :
    ∃! b, Relation.ReflTransGen r a b ∧ Relation.Normal r b :=
  hc.existsUnique_normal hwf a

example {α : Type u} {r s : α → α → Prop} (hr : Relation.Confluent r) (hs : Relation.Confluent s)
    (hc : Relation.Commutes r s) : Relation.Confluent fun a b => r a b ∨ s a b :=
  hr.union hs hc

example {P : Polygraph.{w, u, w'}} {C : Type u'} [Category.{v} C] (o : P.Orientation)
    (φ : GenObj P.Gen ⥤q C)
    (sound : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
      (Paths.lift φ).map (P.src α) = (Paths.lift φ).map (P.tgt α))
    (sep : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      Relation.Normal (Polygraph.step o.rule x y) u →
      Relation.Normal (Polygraph.step o.rule x y) v →
      (Paths.lift φ).map u = (Paths.lift φ).map v → u = v)
    {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : (Paths.lift φ).map u = (Paths.lift φ).map v) : P.quot.map u = P.quot.map v :=
  o.complete φ sound sep h

/-! A shortening rule set needs only local confluence: word length is the measure. -/

example {P : Polygraph.{w, u, w'}}
    (shorter : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), (P.tgt α).length < (P.src α).length)
    (loc : ∀ x y : GenObj P.Gen,
      Relation.LocallyConfluent (Polygraph.step P.homRel x y)) : P.Orientation :=
  Polygraph.Orientation.ofShortening P shorter loc

/-! …and then two normal forms answer the word problem. -/

example {P : Polygraph.{w, u, w'}} (o : P.Orientation) {x y : GenObj P.Gen}
    {u v n m : Quiver.Path x y}
    (hun : Relation.ReflTransGen (Polygraph.step o.rule x y) u n)
    (hn : Relation.Normal (Polygraph.step o.rule x y) n)
    (hvm : Relation.ReflTransGen (Polygraph.step o.rule x y) v m)
    (hm : Relation.Normal (Polygraph.step o.rule x y) m) :
    P.quot.map u = P.quot.map v ↔ n = m :=
  o.quot_eq_iff_normal_eq hun hn hvm hm

end Claims
