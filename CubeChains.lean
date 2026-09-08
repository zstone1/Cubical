-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Concurrency.Salvetti.SalBraid
  -- a Salvetti cell's permutation is its run word, inverted
import CubeChains.Concurrency.Executions.ChStarProduct
  -- Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ — a chain in a product
import CubeChains.Concurrency.Complexification.ChStarSym
  -- Ch (Hbp K) ≌ Ch (K.prod runBp) — the twist
import CubeChains.Concurrency.Salvetti.SalCompare
  -- Ch⋆ K ≌ Sal L from bases + presheaves
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
import CubeChains.Machinery.Graded
  -- Graded M: degrees as objects, End n = M n
import CubeChains.Machinery.Braid.Sum
  -- the block-diagonal permSum; permLen is block-additive

-- Retained infrastructure, off the results' path.
import CubeChains.Precubical.Basic.Nerve
  -- nerveRealizeIso : Nerve (realize X) ≅ X
import CubeChains.Precubical.Wedge.GeoTensor.BP
  -- the geometric ⊗ᵍ on BPSet, cubeTensorIsoBP
import CubeChains.Machinery.Localization.ElementsProd
  -- F ⊠ G, the external product of two Type-valued functors
import CubeChains.Machinery.Arrangement.COMSum
  -- Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂
import CubeChains.Machinery.Cube.SymBox
  -- SBox, J : Box ⥤ SBox, and sHomEquiv
import CubeChains.Machinery.Cube.SymPresheaf
  -- H = J* ∘ J₍!₎, the left Kan extension along J.op
import CubeChains.Machinery.Cube.SymRepresentable
  -- symFree (□ⁿ) ≅ y(▪n), and Sₙ acting on H(□ⁿ)
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
import CubeChains.Concurrency.Merge.AtomPair
  -- the atom relations of PosBraid, as composable chain maps
import CubeChains.Concurrency.Grading.TopBead
  -- merges into the coarsest chain: existence, and rigidity
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
  -- one copy of P d per element over d; C[W⁻¹] is the colimit of its localized slices
import CubeChains.Machinery.Presentation.StrictUnitRefutation
  -- …and why the 0-cells cannot be their image in ∫X
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
import CubeChains.Machinery.Presentation.Partial
  -- …and the *defined* part of ∫F, when lifting is only partial
import CubeChains.Machinery.Presentation.Monoid
  -- a presented monoid presents its one-object category
import CubeChains.Machinery.Presentation.Coproduct
  -- the coproduct of polygraphs presents the disjoint union of categories
import CubeChains.Machinery.Presentation.Adjunction
  -- ⟨generators | relations⟩ ⊣ arrows, so a colimit of polygraphs presents the colimit
import CubeChains.Machinery.Presentation.Coequalizer
  -- …and polygraphs have every colimit: levelwise coequalizers, plus the cofans
import CubeChains.Machinery.Presentation.ColimitCells
  -- …whose cells are the colimit of the cells, so the legs reach every 0-cell and every 1-cell
import CubeChains.Machinery.Presentation.Product
  -- and the product presents the product, once the interchange squares are imposed
import CubeChains.Machinery.Presentation.Pi
  -- …read as a tensor, whose strictly associative model is the tuple over a finite index
import CubeChains.Concurrency.Presentation.SlicePresentation
  -- Ch(K)[W⁻¹] is the localized elements of wedgeHoms K, so the slices glue over it
import CubeChains.Concurrency.Presentation.SliceExchange
  -- …assembled: the localized slice IS the weak order, for every d whose runs are total
import CubeChains.Machinery.Braid.WeakAction
  -- a downward-closed set of permutations carries a partial action of the braid monoid
import CubeChains.Concurrency.Presentation.ChartFibre
  -- a partial action per strand count is a presheaf on the localized base
import CubeChains.Concurrency.Presentation.SliceFibre
  -- the runs over d are such a set — the exchange is the downward closure — and they are the slice
import CubeChains.Concurrency.Presentation.SliceInherit
  -- so the slice family is the BASE's cells, lifted: parametric and functorial
import CubeChains.Concurrency.Presentation.CutPresentation
  -- Ch Zbp presented by its bead cuts
import CubeChains.Concurrency.Presentation.LiftPresentation
  -- and hence Ch K; the vertex monoids do not follow
import CubeChains.Concurrency.Presentation.LocPresentation
  -- the atoms of a run, and the codimension-two cells two of them meet in
import CubeChains.Concurrency.Presentation.Retraction
  -- the loops at a run are the positive braid monoid
import CubeChains.Concurrency.Presentation.BaseComponent
  -- each strand component is one object carrying the Artin monoid
import CubeChains.Concurrency.Presentation.BaseDecomposition
  -- …and the base is their disjoint union, indexed by the strand count
import CubeChains.Concurrency.Presentation.BasePresentation
  -- hence Ch Zbp[W⁻¹] presented: the Garside germ, one copy per strand count
import CubeChains.Concurrency.Presentation.HAction
  -- and the decorated chains of □ⁿ are the positive braid action
import CubeChains.Concurrency.Presentation.ChBraid
  -- the positive braid an arrow of Ch(K)[W⁻¹] performs, read faithfully in the base
import CubeChains.Concurrency.Presentation.RouteComparison
  -- the colimit route and the fibration route name the same 0-cells, and its 1-cells name atoms
import CubeChains.Concurrency.Presentation.ArtinCells
  -- …and each Artin generator is one colimit 1-cell, in the copy its atom's cell names
import CubeChains.Concurrency.Presentation.ArtinChains
  -- the hand-written Artin presentation: runs, codimension-one chains, codimension-two chains
import CubeChains.Concurrency.Presentation.SimpleSupport
  -- a generator acts inside the beads of its chart, so a mixing one pins the chart to one bead
import CubeChains.Concurrency.Presentation.GarsideCells
  -- the hand-written Garside presentation, and the simple that names two colimit 1-cells
import CubeChains.Concurrency.Presentation.RunCells
  -- every 0-cell of Br p K is a run's, in the run's own copy
import CubeChains.Concurrency.Presentation.BrBase
  -- Br p Zbp is p's own polygraph, generator by generator
import CubeChains.Concurrency.Presentation.BrCube
  -- Br p (□n) is the weak order; Br p (Hbp □ⁿ) is the positive braid action
import CubeChains.Concurrency.Presentation.BrFunctor
  -- Br p is a functor on BPSet, and on the runs it is Ch f
import CubeChains.Concurrency.Presentation.BrMap
  -- a map of braid presentations spells a generator's step by a word of the slice

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

example (N : ℕ) : (SingleObj (PosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory :=
  strandComponentGarside N

example (N : ℕ) : (SingleObj (ArtinPosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory :=
  strandComponentArtin N

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

example {P : ℕ → Polygraph} (p : ∀ N, Presents (P N) ((AtStrands N).FullSubcategory)) :
    Presents (Polygraph.coproduct P) (((W Zbp).op).Localization) :=
  zLocOfComponents p

example {S : ℕ → Type} (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) :
    Presents (Polygraph.coproduct fun N => monoidPoly (rels N)) (((W Zbp).op).Localization) :=
  (BraidPresentation.ofMonoids rels e).base

/-! ### The polygraph tensor, in its strictly associative model

`Polygraph.prod` is a **tensor**, not a categorical product: it carries the interchange squares
precisely so that `presented` takes it to `×`.  `Polygraph.pi` is the same tensor over a finite
index, where `(P ⊗ Q) ⊗ R` and `P ⊗ (Q ⊗ R)` are one object rather than two — the associator that
a consumer would otherwise carry becomes an identity, and reindexing is strictly functorial. -/

example {ι : Type} [DecidableEq ι] [Fintype ι] {P : ι → Polygraph.{0, 0, 0}} {C : ι → Type}
    [∀ i, Category.{0} (C i)] (p : ∀ i, Presents (P i) (C i)) :
    Presents (Polygraph.pi P) (∀ i, C i) :=
  Presents.pi p

example {ι : Type} [DecidableEq ι] (P : ι → Polygraph.{0, 0, 0}) :
    Polygraph.piMap P (fun i => 𝟙 (P i)) = 𝟙 (Polygraph.pi P) :=
  Polygraph.piMap_id P

example {ι : Type} [DecidableEq ι] (P Q R : ι → Polygraph.{0, 0, 0}) (φ : ∀ i, P i ⟶ Q i)
    (ψ : ∀ i, Q i ⟶ R i) :
    Polygraph.piMap P (fun i => φ i ≫ ψ i) = Polygraph.piMap P φ ≫ Polygraph.piMap Q ψ :=
  Polygraph.piMap_comp P φ ψ

/-! ## `Ch(K)[W⁻¹]` is presented, for every `K`

### …by the **base's own** cells

The slice over `d` is the base's presentation lifted along the runs over `d`: 0-cells the runs,
1-cells the base's generators where they act, 2-cells its relations there.  So the family is
parametric in the presentation of the base, and the colimit's 1- and 2-cells move with it —
`artinChainPoly` and `germActionPoly` are the same colimit read at the Artin and at the Garside
base. -/

example {P : Polygraph.{0, 0, 0}} (p : Presents P (((W Zbp).op).Localization)) (d : Ch Zbp) :
    Presents ((slicePolyFunctor p).obj d) (((W Zbp).over (X := d)).Localization) :=
  slicePresentationOf p d

/-! …and its cells are the base's, read at a run: the strand-`N` 0-cell of a braid presentation
*is* the run, and its generators are the loops there. -/

example (p : BraidPresentation) {N : ℕ} {x y : (p.P N).V} (s : (p.P N).Gen x y) :
    p.base.arrow (Polygraph.CoproductGen.mk s :
        (p.poly.pt ⟨N, x⟩ : GenObj p.poly.Gen) ⟶ p.poly.pt ⟨N, y⟩)
      = (runBase N).map (posArrow N (p.braid s)) :=
  p.base_arrow s

example (N : ℕ) (k : Fin (N - 1)) :
    artinBP.base.arrow (artinBP.gen k) = atomLoop N k :=
  artinBase_arrow_atom N k

example (p : BraidPresentation) (d : Ch Zbp) :
    RunAt d (BPSet.dimSum d.dims) ≃ (slicePolyRaw p.base d).V :=
  p.runPtEquiv d

example (p : BraidPresentation) {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (s : p.S N)
    (h : (sliceActionAt d N (p.braid s)).unop.val (some u) = some v) :
    (⟨p.runPt u⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨p.runPt v⟩ :=
  p.runGen s h

example (p : BraidPresentation) {d : Ch Zbp} {N : ℕ} {u v : RunAt d N}
    (g : (⟨p.runPt u⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨p.runPt v⟩) :
    ∃ (s : p.S N) (h : (sliceActionAt d N (p.braid s)).unop.val (some u) = some v),
      g = p.runGen s h :=
  p.gen_action g

example (K : BPSet) :
    Presents (Limits.colimit (Polygraph.elementsPoly (wedgeHoms K)
      (slicePolyFunctor germBP.base))) ((W K).Localization) :=
  presentsChainsGarsideColimit K

example (K : BPSet) :
    Presents (Limits.colimit (Polygraph.elementsPoly (wedgeHoms K)
      (slicePolyFunctor artinBP.base))) ((W K).Localization) :=
  presentsChainsArtinColimit K

/-! ### `Br p K`: the presentation a presentation of the braid monoids induces

A `BraidPresentation` is the whole input — a presentation of each braid monoid as a one-object
category, with one 0-cell per strand count — and `Br p K` is what it induces on `Ch(K)[W⁻¹]`.
There is no side hypothesis: `presentsSliceColimit` asks nothing of the 0-cells, and `vertex` is
only what names `pt N`.  The germ and the Artin spellings are two values of the same construction,
built from monoid presentations by `ofMonoids`. -/

example {P : ℕ → Polygraph.{0, 0, 0}} (comp : ∀ N, Presents (P N) ((SingleObj (PosBraid N))ᵒᵖ))
    (vertex : ∀ N, Unique (P N).V) : BraidPresentation :=
  ⟨P, comp, vertex⟩

example {S : ℕ → Type} (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) : BraidPresentation :=
  BraidPresentation.ofMonoids rels e

example : BraidPresentation := germBP

example : BraidPresentation := artinBP

example (p : BraidPresentation) (K : BPSet) : Presents (p.Br K) ((W K).Localization) :=
  p.presentsBr K

example (K : BPSet) : Presents (germBP.Br K) ((W K).Localization) :=
  presentsChainsGarsideColimit K

example (K : BPSet) : Presents (artinBP.Br K) ((W K).Localization) :=
  presentsChainsArtinColimit K

/-! **(1) At the base, `Br p Zbp` is `p`'s own polygraph** — generator to generator, and no word is
chosen.  `BySimples` is not a convenience: the braid monoid acts on the runs by *length-additive*
multiplication, so a letter longer than its permutation acts on no run and names no 1-cell.  The
0-cells are the strand counts unconditionally. -/

example : germBP.BySimples := germBP_bySimples

example : artinBP.BySimples := artinBP_bySimples

example (p : BraidPresentation) (hp : p.BySimples) :
    Polygraph.Presents.Map p.base.op ((p.presentsBr Zbp).transport zLocOpEquiv) :=
  p.brZMap hp

example (p : BraidPresentation) (hp : p.BySimples) {x y : GenObj (p.poly.op).Gen} (e : x ⟶ y) :
    (p.brZMap hp).hom.cells.map e = (p.brZGen hp e).toPath :=
  p.brZMap_cells hp e

example (p : BraidPresentation) (hp : p.BySimples) :
    (p.poly.op).presented ≌ (p.Br Zbp).presented :=
  p.brZEquiv hp

example (p : BraidPresentation) : Function.Bijective p.brZPt := p.bijective_brZPt

/-! **(2) At the cube, `Br p (□n)` is the weak Bruhat order.** -/

example (p : BraidPresentation) (n : ℕ) : Presents (p.Br (□n)) ((WeakOrder n)ᵒᵖ) :=
  p.presentsBrCube n

/-! **(3) At the decorated cube, `Br p (Hbp □ⁿ)` is the positive braid action** — whose loops at
*every* object are `PosPureBraid n`, the kernel of `posPermHom n`.  The presentation does not
present that monoid: `end_not_generated_by_simples` says the loops it generates are only the
identity, so the pure braids are a computed invariant of the presented category, not a
sub-presentation. -/

example (p : BraidPresentation) (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (PosBraidAction n) :=
  p.presentsBrAction n

example (p : BraidPresentation) (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n))) :=
  p.presentsBrArtinAction n

example (p : BraidPresentation) (n : ℕ) :
    Presents ((p.Br (Hbp.obj (□n))).op) ((PosBraidAction n)ᵒᵖ) :=
  p.presentsBrActionOp n

example (p : BraidPresentation) (n : ℕ) (x : GenObj (p.Br (Hbp.obj (□n))).Gen) :
    @End (PosBraidAction n) _ ((p.presentsBrAction n).at' x) ≃* PosPureBraid n :=
  p.endBrAction n x

/-! …and the generators of `Br p K` are `p`'s own, crossed above a run: no word is chosen, so
**Garside in gives Garside out** (the simples, acting on the chambers at `Hbp □ⁿ`) and **Artin in
gives the codimension-one chains** (the atoms). -/

example (p : BraidPresentation) (K : BPSet) {A B : GenObj (p.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (s : p.S N)
      (u v : RunAt (Polygraph.eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (Polygraph.eltBase (wedgeHoms K) c) N (p.braid s)).unop.val (some u)
        = some v)
      (hA : ιV K p.fam c (p.runPt v) = A) (hB : ιV K p.fam c (p.runPt u) = B),
      Quiver.homOfEq (ιE K p.fam c (p.runGen s hact)) hA hB = e :=
  p.exists_runGen K e

example (K : BPSet) {A B : GenObj (germBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (σ : Equiv.Perm (Fin N))
      (u v : RunAt (Polygraph.eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (Polygraph.eltBase (wedgeHoms K) c) N (posPerm σ)).unop.val (some u)
        = some v)
      (hA : ιV K germBP.fam c (germBP.runPt v) = A)
      (hB : ιV K germBP.fam c (germBP.runPt u) = B),
      v.perm = u.perm * σ ∧ permLen u.perm + permLen σ = permLen v.perm ∧
        Quiver.homOfEq (ιE K germBP.fam c (germBP.runGen σ hact)) hA hB = e :=
  germBr_gen K e

example (K : BPSet) {A B : GenObj (artinBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (k : Fin (N - 1))
      (u v : RunAt (Polygraph.eltBase (wedgeHoms K) c) N)
      (hact : (sliceActionAt (Polygraph.eltBase (wedgeHoms K) c) N (posPerm (adjT k))).unop.val
        (some u) = some v)
      (hA : ιV K artinBP.fam c (artinBP.runPt v) = A)
      (hB : ιV K artinBP.fam c (artinBP.runPt u) = B),
      v.perm = u.perm * adjT k ∧ permLen u.perm + 1 = permLen v.perm ∧
        Quiver.homOfEq (ιE K artinBP.fam c (artinBP.runGen k hact)) hA hB = e :=
  artinBr_gen K e

/-! **(4) `Br p` is a functor on `BPSet`**, and what it does is `Ch f` on the runs. -/

example (p : BraidPresentation) : BPSet ⥤ Polygraph.{0, 0, 0} := p.brFunctor

example (p : BraidPresentation) {K K' : BPSet} (f : K ⟶ K')
    (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    Limits.colimit.ι (Polygraph.elementsPoly (wedgeHoms K) p.fam) c ≫ p.brMap f
      = Limits.colimit.ι (Polygraph.elementsPoly (wedgeHoms K') p.fam) ((brElt f).obj c) :=
  p.ι_brMap f c

example (p : BraidPresentation) {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.brMap f).pre.obj (p.ιRun K z) = p.ιRun K' (z ≫ f) :=
  p.brMap_ιRun f z

example {K K' : BPSet} (f : K ⟶ K') : (W K).Localization ⥤ (W K').Localization := chLocMap f

example (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ := chLocMap_id K

example {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g := chLocMap_comp f g

example (p : BraidPresentation) {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.presentsBr K').at' ((p.brMap f).pre.obj (p.ιRun K z))
      ≅ (chLocMap f).obj ((p.presentsBr K).at' (p.ιRun K z)) :=
  p.brMapRunNat f z

example {P : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] (p : Presents P C) :
    Polygraph.Presents.Map p p :=
  Polygraph.Presents.Map.refl p

example {P Q R : Polygraph.{w', u'}} {C : Type u} [Category.{v} C] {p : Presents P C}
    {q : Presents Q C} {r : Presents R C}
    (m : Polygraph.Presents.Map p q) (n : Polygraph.Presents.Map q r) :
    Polygraph.Presents.Map p r :=
  m.trans n

/-! **(5) Maps of braid presentations.**  A map is a comparison at each strand count — a *spelling*,
so a generator goes to a **word** — and that word performs the generator's own braid, `PosBraid N`
having no non-trivial units.  Above a chain that word lifts uniquely through defined runs, and the
lift is strictly natural in the chain; so the colimit descends it, and `Br p K` is spelled in
`Br q K`, naturally in `K`, by a comparison naming the same arrows. -/

example (p : BraidPresentation) : BraidPresentation.Map p p := BraidPresentation.Map.refl p

example {p q r : BraidPresentation} (m : BraidPresentation.Map p q)
    (n : BraidPresentation.Map q r) : BraidPresentation.Map p r := m.trans n

example {p q : BraidPresentation} (m : BraidPresentation.Map p q) (N : ℕ) {x y : (p.P N).V}
    (s : (p.P N).Gen x y) : ((q.comp N).eval.map (m.word s)).unop = p.braid s :=
  m.braid_word s

example {p q : BraidPresentation} (m : BraidPresentation.Map p q) {d' d : Ch Zbp} (f : d' ⟶ d) :
    (p.fam.map f).pre ⋙q m.famCells d
      = m.famCells d' ⋙q (q.fam.map f).pre.pathsFunctor.toPrefunctor :=
  m.famCells_push f

example {p q : BraidPresentation} (m : BraidPresentation.Map p q) (K : BPSet) :
    GenObj (p.Br K).Gen ⥤q (q.Br K).Word :=
  m.brCells K

example {p q : BraidPresentation} (m : BraidPresentation.Map p q) (K : BPSet) :
    Polygraph.Presents.Map (p.presentsBr K) (q.presentsBr K) :=
  m.presentsMap K

example {p q : BraidPresentation} (m : BraidPresentation.Map p q) {K K' : BPSet} (f : K ⟶ K') :
    (p.brMap f).pre ⋙q m.brCells K' = m.brCells K ⋙q (q.brMap f).words.toPrefunctor :=
  m.brCells_brMap f

example (K : BPSet) {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (hP : ∀ {d' d : Ch Zbp} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc (W Zbp) f) :
    Presents (Limits.colimit (Polygraph.elementsPoly (wedgeHoms K) P))
      ↥(Limits.colimit (overLocFunctor (W K))) :=
  presentsChainsColimitLoc K p hP

example : ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left := exists_not_isRun_over

example : Presents Cut.poly ((Ch Zbp)ᵒᵖ) := zCutPresentation

example (K : BPSet) {P : Polygraph.{w', u'}} (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    Presents (p.elementsPoly (wedgeHoms K)) ((Ch K)ᵒᵖ) :=
  chPresentation K p

example (K : BPSet) : Presents (chCutPoly K) ((Ch K)ᵒᵖ) := chCutPresentation K

example (n : ℕ) : Presents (hLocPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) := hLocPresentation n

example (n : ℕ) : Presents (hLocPoly n) ((PosBraidAction n)ᵒᵖ) := hLocActionPresentation n

/-! ## …parametrically in a presentation of the base -/

example :
    Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N))
      (((W Zbp).op).Localization) :=
  germBP.base

example :
    Presents (Polygraph.coproduct fun N => monoidPoly (ArtinRel N)) (((W Zbp).op).Localization) :=
  artinBP.base

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

example {C : Type u} [Category.{v} C] (G : C ⥤ Type w) (bot : ∀ c, G.obj c)
    (hbot : ∀ {c c' : C} (g : c ⟶ c'), (ConcreteCategory.hom (G.map g)) (bot c) = bot c')
    {P : Polygraph.{w', u'}} (p : Presents P C) :
    Presents ((p.elements G).restrictPoly (Presents.defined G bot))
      (Presents.defined G bot).FullSubcategory :=
  Presents.partialElements G bot hbot p

example {C : Type u} [Category.{v} C] (G : C ⥤ Type w) (bot : ∀ c, G.obj c)
    (htot : ∀ {c c' : C} (g : c ⟶ c') (x : G.obj c), x ≠ bot c →
      (ConcreteCategory.hom (G.map g)) x ≠ bot c') :
    (Presents.defined G bot).FullSubcategory ≌ (Presents.definedFunctor G bot htot).Elements :=
  Presents.definedEquiv G bot htot

example {C : Type u} [Category.{v} C] (P : C ⥤ Type w) (p : P.Elements) :
    End p ≃* CategoryOfElements.stabilizer P p :=
  CategoryOfElements.endEquivStabilizer P p

example {P Q : Polygraph.{w', u'}} {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (p : Presents P A) (q : Presents Q B) : Presents (P.prod Q) (A × B) :=
  p.prod q

example {S : Type u} (rels : FreeMonoid S → FreeMonoid S → Prop) :
    Presents (monoidPoly rels) ((SingleObj (PresentedMonoid rels))ᵒᵖ) :=
  presentedMonoidPresentation rels

example {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})
    {V' : Type u} {Gen' : V' → V' → Type u}
    (ψ : ∀ j : J, GenObj (D.obj j).Gen ⥤q GenObj Gen')
    (hψ : ∀ {i j : J} (u : i ⟶ j), (D.map u).pre ⋙q ψ j = ψ i) (j : J) :
    (Limits.colimit.ι D j).pre ⋙q Polygraph.colimitCells D ψ hψ = ψ j :=
  Polygraph.ι_pre_comp_colimitCells D ψ hψ j

example {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})
    (A : GenObj (Limits.colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (Limits.colimit.ι D j).pre.obj x = A :=
  Polygraph.exists_colimit_ι_obj D A

example {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})
    {A B : GenObj (Limits.colimit D).Gen} (e : A ⟶ B) :
    ∃ (j : J) (x y : GenObj (D.obj j).Gen) (g : x ⟶ y)
      (hx : (Limits.colimit.ι D j).pre.obj x = A) (hy : (Limits.colimit.ι D j).pre.obj y = B),
      Quiver.homOfEq ((Limits.colimit.ι D j).pre.map g) hx hy = e :=
  Polygraph.exists_colimit_ι_map D e

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
    (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f) :
    Presents (Limits.colimit (Polygraph.elementsPoly X P))
      ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  Polygraph.presentsSliceColimit X V p hP

example {A : Type u} [Category.{u} A] (V : MorphismProperty A) :
    Limits.IsColimit (overLocCocone V) :=
  isColimitOverLocCocone V

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
    (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f) :
    Presents (Limits.colimit (Polygraph.elementsPoly X P))
      ↥(Limits.colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  Polygraph.presentsColimitOfLocalizedSlices X V p hP

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
    (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f) :
    ↥(Limits.colimit (Polygraph.elementsPoly X P ⋙ Polygraph.presentedFunctor.{u, u})) ≌
      ↥(Limits.colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  Polygraph.colimitPresentedEquivColimitLoc X V p hP

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) (P : D ⥤ Polygraph.{u, u, u})
    (c : (X.Elements)ᵒᵖ) :
    (P.obj (Polygraph.eltBase X c)).presented ⥤
      (Limits.colimit (Polygraph.elementsPoly X P)).presented :=
  Polygraph.colimInclFun X P c

example {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
    {C : Type u} [Category.{u} C]
    {F G : (Limits.colimit (Polygraph.elementsPoly X P)).presented ⥤ C}
    (h : ∀ c, Polygraph.colimInclFun X P c ⋙ F = Polygraph.colimInclFun X P c ⋙ G) : F = G :=
  Polygraph.colim_functor_ext h

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

example (n : ℕ) : HasDiamonds (□n) := hasDiamonds_cube n

example {K : BPSet} {a d d' : Ch K} {u : a ⟶ d} {u' : a ⟶ d'}
    (c : CutData u) (c' : CutData u') (hsep : c.l ++ [c.p, c.q] <+: c'.l) :
    ∃ (e : Ch K) (v : d ⟶ e) (v' : d' ⟶ e),
      codim v = 1 ∧ codim v' = 1 ∧ u ≫ v = u' ≫ v' :=
  hasDiamonds_disjoint c c' hsep

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

example {N : ℕ} {x : GenObj Cut.Refine} (e : x ⟶ Cut.vert (zObj (𝟙^N)))
    (hW : ¬ W Zbp (Cut.genHom e)) :
    ∃ k : Fin (N - 1), ∃ h : x.as = zObj (atomComp N k),
      Cut.genHom e ≫ eqToHom h = atomOnes N k :=
  Cut.exists_eq_atom e hW

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

/-! ## The braid comparison -/

example (n : ℕ) : Ch⋆ (□n) ≌ Sal (braidCOM n) := salCompare chFaceCatEquiv linesTopeIso

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

/-! ## The colimit route against the fibration route

The 0-cells agree by a theorem, not by unfolding; the 1-cells agree because both routes' generators
perform the same atom, and a parallel pair performing one braid is one arrow.  The two polygraphs
present *opposite* categories, so a comparison needs `Presents.op` before it can be stated at
all. -/

example {d : Ch Zbp} {a b : RunOver d} (h : RunStep a b) :
    ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d)
      (k : Fin (BPSet.dimSum a.1.left.dims - 1)),
      ChainCat.crossPerm rfl t = adjT k ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom :=
  runStep_exists_adjT h

example (K : BPSet) (hS : IsSegal K.toPsh) : (chLocBase K).Faithful :=
  faithful_chLocBase K hS

example (K : BPSet) (hS : IsSegal K.toPsh) {N : ℕ} {X Y : (W K).Localization} {f g : X ⟶ Y}
    (hX : BPSet.dimSum (chOf X).dims = N) (hY : BPSet.dimSum (chOf Y).dims = N)
    (h : chBraid f hX hY = chBraid g hX hY) : f = g :=
  eq_of_chBraid_eq hS hX hY h

example (n : ℕ) {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid ((hLocArtinPresentation n).arrow e).unop
        (hbpStrands (chOf ((hLocArtinPresentation n).at' y).unop))
        (hbpStrands (chOf ((hLocArtinPresentation n).at' x).unop))
      = posPerm (adjT e.1) :=
  chBraid_hLocArtinPresentation_arrow n e

example (K : BPSet) {N : ℕ} (d : Ch Zbp) (x : (wedgeHoms K).obj (Opposite.op d)) {a b : Over d}
    (φ : ((W Zbp).over (X := d)).Q.obj a ⟶ ((W Zbp).over (X := d)).Q.obj b)
    {e : Ch Zbp} {t : a.left ⟶ e} {m : b.left ⟶ e} {z : e ⟶ d} (hm : W Zbp m)
    (hta : t ≫ z = a.hom) (hmb : m ≫ z = b.hom)
    (ha : BPSet.dimSum a.left.dims = N) (hb : BPSet.dimSum b.left.dims = N)
    (he : BPSet.dimSum e.dims = N)
    (hA : BPSet.dimSum (chOf ((locEquivElements K).inverse.obj
      ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (((W Zbp).over (X := d)).Q.obj a)))).dims = N)
    (hB : BPSet.dimSum (chOf ((locEquivElements K).inverse.obj
      ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (((W Zbp).over (X := d)).Q.obj b)))).dims = N) :
    chBraid ((locEquivElements K).inverse.map
        ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp) d x).map φ)) hA hB
      = posPerm (ChainCat.crossPerm ha t) :=
  chBraid_colimSliceEval K d x φ hm hta hmb ha hb he hA hB

/-! ## The two presentations, compared

Generator to generator: a 0-cell of the fibration route is a run read in its own copy, and its
`k`-th Artin generator is the single crossing of the copy at `atomComp n k`. -/

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
    {a b : (P.obj (Polygraph.eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (P.obj (Polygraph.eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (presentsChainsColimit K p hP).arrow (ιE K P c g)
      = eqToHom (at_ιV K P p hP c a) ≫ (locEquivElements K).inverse.map
            ((Polygraph.colimSliceEval (wedgeHoms K) (W Zbp)
              (Polygraph.eltBase (wedgeHoms K) c) c.unop.2).map
                ((p (Polygraph.eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (at_ιV K P p hP c b).symm :=
  arrow_ιE K P p hP c g

example {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((presentsChainsArtinColimit (Hbp.obj (□n))).op).at' (obCell x)
      ≅ (hLocArtinPresentation n).at' x :=
  thetaCell x

example {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    ((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)
      = (thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv :=
  hgenCell e

example {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (artinColimMap n).hom.cells.map e = (genCell e).toPath :=
  artinColimMap_cells e

example (n : ℕ) :
    Polygraph.Presents.Map (hLocArtinPresentation n)
      ((presentsChainsArtinColimit (Hbp.obj (□n))).op) :=
  artinColimMap n

/-! ## Artin's presentation, hand-written in chains

`artinChainPoly n` names no colimit and no localization: its 0-cells are the runs of `H(□ⁿ)`, its
1-cells the **codimension-one chains** — one 2-bead, read from the crossing leg to the merge leg —
and its 2-cells the **codimension-two chains**, a square where the cuts are far apart and a hexagon
where they are adjacent.  `artinChainMap` matches it with `Br artinBP (H □ⁿ)` cell for cell in all
three dimensions. -/

example (n : ℕ) : artinChainPoly n ⟶ artinBP.Br (Hbp.obj (□n)) := artinChainMap n

example (n : ℕ) :
    Function.Bijective (artinChainMap n).pre.obj ∧
      (∀ A B : GenObj (artinChainPoly n).Gen,
        Function.Bijective ((artinChainMap n).pre.map : (A ⟶ B) → _)) ∧
      ∀ A B : GenObj (artinChainPoly n).Gen,
        Function.Bijective ((artinChainMap n).two : (artinChainPoly n).Rel A B → _) :=
  bijective_artinChainMap n

/-- The codimension-two chain of a pair of cuts sits below **every** chain where both act, merge
run to run — the span the 2-cells travel along. -/
example {n : ℕ} {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) {d : Ch Zbp}
    (hd : BPSet.dimSum d.dims = n) {u vi vj : RunAt d n}
    (hi : (sliceActionAt d n (posPerm (adjT i))).unop.val (some u) = some vi)
    (hj : (sliceActionAt d n (posPerm (adjT j))).unop.val (some u) = some vj) :
    ∃ t : pairChain n i j hij ⟶ d, RunAt.push t (pairMergeRun hij) = u :=
  exists_pairRunLeg hij hd hi hj

example (n : ℕ) :
    (hLocArtinPoly n).presented ≌
      ((Limits.colimit (Polygraph.elementsPoly (wedgeHoms (Hbp.obj (□n)))
        (slicePolyFunctor artinBP.base))).op).presented :=
  artinColimEquiv n

/-! …and the dictionary is an isomorphism of the generating data. -/

example (p : BraidPresentation) (K : BPSet) {n : ℕ} (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (hc : BPSet.dimSum (Polygraph.eltBase (wedgeHoms K) c).dims = n)
    (a : (slicePolyRaw p.base (Polygraph.eltBase (wedgeHoms K) c)).V) :
    ∃ z : ⋁(𝟙^n) ⟶ K, ιV K p.fam c a = p.ιRun K z :=
  p.exists_ιRun K c hc a

example {n : ℕ} {d : Ch Zbp} (hd : BPSet.dimSum d.dims = n) {k : Fin (n - 1)}
    {u v : RunAt d n}
    (h : (sliceActionAt d n (posPerm (adjT k))).unop.val (some u) = some v) :
    ∃ w : zObj (atomComp n k) ⟶ d,
      RunAt.push w (atomRunAt k) = v ∧ RunAt.push w (mergeRunAt k) = u :=
  exists_atomComp_leg hd h

example (n : ℕ) : Function.Bijective (obCell (n := n)) := bijective_obCell n

example {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} :
    Function.Bijective (genCell : (x ⟶ y) → (obCell x ⟶ obCell y)) := bijective_genCell

example (n : ℕ) :
    Function.Bijective (genQuiver n).obj ∧
      ∀ x y : GenObj (hLocArtinPoly n).Gen,
        Function.Bijective ((genQuiver n).map : (x ⟶ y) → _) :=
  bijective_genQuiver n

/-! ## The Garside case: the same simple names two generators

The hand-written Garside presentation of `Ch(H□ⁿ)[W⁻¹]` is the germ presentation of the braid
monoid acting on the runs — 0-cells the runs, 1-cells ⟨run, simple⟩, 2-cells the germ relations.
`Br germBP (Hbp □ⁿ)` presents the same category with a **larger** generating set: a simple is
crossed in the one-bead chart, and there the run it was crossed above is remembered, which for the
atoms cannot happen. -/

example (n : ℕ) : Presents (germActionPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) :=
  germActionPresentation n

example (p : BraidPresentation) (n : ℕ) :
    Function.Bijective (p.ιRun (Hbp.obj (□n)) (n := n)) := ιRun_bijective p n

example (n : ℕ) : (germActionPoly n).V ≃ GenObj (germBP.Br (Hbp.obj (□n))).Gen :=
  germObEquiv n

example (n : ℕ) (z z' : (germActionPoly n).V) :
    Function.Injective (germActionSimple (n := n) (z := z) (z' := z')) :=
  germActionSimple_injective n z z'

example (n : ℕ) (z : (germActionPoly n).V) (σ : Equiv.Perm (Fin n)) :
    ∃ (z' : (germActionPoly n).V) (e : (germActionPoly n).Gen z z'), germActionSimple e = σ :=
  germActionSimple_surjective n z σ

/-! …and the geometry behind the difference: a generator acts only inside the beads of its chart,
so a simple whose powers reach every event is crossed in the one-bead chart alone. -/

example {n : ℕ} {d : Ch Zbp} (hd : BPSet.dimSum d.dims = n) (x y : Over d)
    {σ : Equiv.Perm (Fin n)}
    (hσ : (crossOver hd y)⁻¹ * crossOver hd x = σ) (hmix : Mixes σ) :
    d.dims = topDims n :=
  dims_eq_topDims_of_mixes hd x y hσ hmix

example (K : BPSet) {n : ℕ} (X : ⋁(topDims n) ⟶ K) (ρ σ : Equiv.Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) (hmix : Mixes σ) :
    (sepCells K germBP σ hmix).map (germTopCell K X ρ σ h) = some ρ :=
  sepCells_germTopCell K X ρ σ h hmix

/-! **The refutation.**  At `n = 3` the three-cycle names two 1-cells of `Br germBP (Hbp □³)`
between one pair of 0-cells, so no dictionary sends a 1-cell to its ⟨0-cells, simple⟩ and the
generating quivers are not isomorphic — contrast `bijective_genQuiver` for the atoms.  Both cells
perform that three-cycle, so they name **one arrow**: the surplus is a redundant generating set,
and the two polygraphs present the same category. -/

example : (straightCell : wSrc ⟶ wTgt) ≠ crossedCell := straightCell_ne_crossedCell

example :
    (germBP.presentsBr (Hbp.obj (□3))).arrow straightCell
      = (germBP.presentsBr (Hbp.obj (□3))).arrow crossedCell :=
  arrow_straightCell_eq_crossedCell

example (n : ℕ) : (germActionPoly n).presented ≌ ((germBP.Br (Hbp.obj (□n))).presented)ᵒᵖ :=
  germActionEquivBr n

/-! …and it is not a feature of the cube: at the base, where a copy has one chart and the whole
one-bead copy sits at the strand count's single 0-cell, the same simple already names two loops. -/

example : (straightLoopZ : germBP.ιRun Zbp (zRun 3) ⟶ germBP.ιRun Zbp (zRun 3))
    ≠ crossedLoopZ :=
  straightLoopZ_ne_crossedLoopZ

end Claims
