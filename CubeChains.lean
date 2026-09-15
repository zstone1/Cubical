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
import CubeChains.Precubical.Chains.Correspondence
  -- RefineObj K ≌ Ch K under NonSelfLinked + AdmitsAltitude
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
import CubeChains.Concurrency.Presentation.SliceRuns
  -- the runs over a chain, and the exchange: every descent of the weak order is an arrow
import CubeChains.Concurrency.Merge.CubeFaces
  -- a chain of a cube is an ordered partition of its axes; two faces meet in one
import CubeChains.Machinery.Localization.ElementsAction
  -- a functor on SingleObj M is an M-set
import CubeChains.Concurrency.Complexification.HPosAction
  -- the decorated chains of □ⁿ acting on the orderings of its axes
import CubeChains.Machinery.Presentation.Elements
  -- C ≌ ⟨generators | relations⟩, and a presented base presents ∫F
import CubeChains.Machinery.Localization.Map
  -- a functor carrying one class into another, localized
import CubeChains.Machinery.Presentation.Monoid
  -- a presented monoid presents its one-object category
import CubeChains.Machinery.Presentation.Coproduct
  -- the coproduct of polygraphs presents the disjoint union of categories
import CubeChains.Foundations.Polygraph.Presheaf
  -- 2-polygraphs are the presheaves on PolyShape (Schanuel), so (co)limits of them are cellwise
  -- the runs over d are such a set — the exchange is the downward closure
import CubeChains.Concurrency.Presentation.CutPresentation
  -- Ch Zbp by its bead cuts
import CubeChains.Concurrency.Presentation.LiftPresentation
  -- …acting on a chain of K; the vertex monoids do not follow
import CubeChains.Concurrency.Presentation.LocFunctor
  -- Ch f localized, as a functor of K — the side a presentation reads
import CubeChains.Concurrency.Presentation.LocPresentation
  -- the atoms of a run, and the codimension-two cells two of them meet in
import CubeChains.Concurrency.Presentation.Retraction
  -- the loops at a run are the positive braid monoid
import CubeChains.Concurrency.Presentation.BaseComponent
  -- the run of N events, as a one-object piece of the localized base
import CubeChains.Concurrency.Presentation.BasePresentation
  -- hence Ch Zbp[W⁻¹] presented: the Garside germ, one copy per strand count
import CubeChains.Concurrency.Presentation.ArtinDegreeZero
  -- the degree-zero cells out of a run are Artin's: N−1 atoms and their pairs
import CubeChains.Concurrency.Presentation.TopRefinement
  -- the two runs a chain spans: the merge below it, and its greatest refinement
import CubeChains.Concurrency.Presentation.RunAtoms
  -- the runs over a shape, a lower set of the weak order; over a degree-two shape, a polygon
import CubeChains.Concurrency.Presentation.PaperPoly
  -- the polygraph: runs, degree-one objects, and a degree-two object's two maximal climbs
import CubeChains.Concurrency.Presentation.ChainWeb
  -- …the runs over every chain satisfy Artin's relation, so a refinement reads as Matsumoto's arrow
import CubeChains.Concurrency.Presentation.DirectPresents
  -- …read straight in Ch(K)[W⁻¹]: the chains read back on them are a localization
import CubeChains.Concurrency.Presentation.PaperFunctor
  -- …and that polygraph is a functor of K, its presentation natural in K on the nose
import CubeChains.Concurrency.Presentation.PaperArtin
  -- …and at the base its cells are Artin's, so Ch Zbp[W⁻¹] is the graded braid monoid
import CubeChains.Concurrency.Presentation.PaperAtoms
  -- …so word length grades Ch(K)[W⁻¹], and every presentation of it carries the paper's 1-cells
import CubeChains.Concurrency.Presentation.HAction
  -- and the decorated chains of □ⁿ are the positive braid action

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

Read it downwards and each link consumes the next.  A **monoid presentation of the braid monoids**
presents the base, `Ch(Z)[W⁻¹]` — every hom-set of which is a braid monoid. -/

example : (FullPosBraid)ᵒᵖ ≌ (((W Zbp).op).Localization) := fullBaseEquiv

example (p : BraidPresentation) : Presents p.poly (FullPosBraid)ᵒᵖ := p.braids

example (N : ℕ) : Function.Surjective (runArtinEquiv N) := (runArtinEquiv N).surjective

/-! ### One functor presents `Ch(K)[W⁻¹]` for every `K`, with no `∫F` vocabulary

The runs over a chain are a lower set of the right weak order, and an ascent between two of them is
a degree-one object.  Over a **degree-two object** they are a polygon, climbed from the merge below it
alternately through its two junctions: the two maximal climbs are its two words, the one through
the lower junction first.  `Paper.poly K` is the polygraph those cells make: 0-cells the runs on the
nose, 1- and 2-cells the objects of degree one and two — and it presents `Ch(K)[W⁻¹]`. -/

example (K : BPSet) (e : Ch K) (he : ChainCat.degree (zObj e.dims) = 2) :
    Quiver.Path (ChainCat.Paper.runPt (ChainCat.Paper.bottomRun e))
      (ChainCat.Paper.runPt (ChainCat.Paper.topOf e).1) :=
  ChainCat.Paper.loWord e rfl he

/-! …because over every chain the runs satisfy Artin's relation — the pair chain placed under a
polygon's foot carries its two climbs — so Matsumoto's theorem reads a refinement as one arrow. -/

example (K : BPSet) (d : Ch K) (N : ℕ) : (ChainCat.Paper.chWeb d N).IsArtin :=
  ChainCat.Paper.isArtin_chWeb d N

example (K : BPSet) : Polygraph := ChainCat.Paper.poly K

example (K : BPSet) : Presents (ChainCat.Paper.poly K) (((W K).op).Localization) :=
  ChainCat.Paper.paperPresents K

/-! …because the chains, read back on those cells, are themselves a localization at the merges. -/

example (K : BPSet) : (ChainCat.Paper.Theta K).IsLocalization ((W K).op) := inferInstance

/-! …and that polygraph is a functor of `K`, its presentation natural in `K` on the nose: the
comparison is the transport its 0-cells force. -/

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
and the two cuts are adjacent exactly in the first case.  A 2-cell's source climbs through the lower
junction first, as Artin's relation starts at the lower generator, in both species. -/

example {N : ℕ} (α : ChainCat.Paper.Cell 2 (ChainCat.Paper.zRun N) (ChainCat.Paper.zRun N)) :
    ((ChainCat.Paper.cellAtomPairEquiv N α).hi : ℕ)
        = ((ChainCat.Paper.cellAtomPairEquiv N α).lo : ℕ) + 1
      ↔ (3 : ℕ+) ∈ α.obj.dims :=
  ChainCat.Paper.cell_adj_iff α

example : ChainCat.Paper.poly Zbp ≅ artinBP.poly := ChainCat.Paper.paperArtinIso

/-! ### 2-polygraphs are a presheaf topos

Schanuel's theorem: the free-category monad on quivers is familially representable, so a
2-polygraph is a quiver glued to a family of bigons, and the glueing has a site. -/

example : Polygraph.{0, 0, 0} ≌ (PolyShapeᵒᵖ ⥤ Type) := Polygraph.polyEquivPresheaf

/-! ## `Ch(K)[W⁻¹]` is presented, for every `K` -/

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

example : BraidData := artinBP

example : BraidPresentation := artinBraids

example : artinBraids.toBraidData = artinBP := rfl

example : germBP.BySimples := germBP_bySimples

example : artinBraids.BySimples := artinBraids_bySimples

example (N : ℕ) : germBP.S N = Equiv.Perm (Fin N) := rfl

example (N : ℕ) : artinBP.S N = Fin (N - 1) := rfl

example (N : ℕ) (k : Fin (N - 1)) :
    artinBraids.braids.arrow (artinBraids.gen k) = braidLoop N (posPerm (adjT k)) :=
  artinBraids_arrow N k

example {K K' : BPSet} (f : K ⟶ K') : (W K).Localization ⥤ (W K').Localization := chLocMap f

example (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ := chLocMap_id K

example {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g := chLocMap_comp f g

/-! …and the side a presentation reads is a functor to `Cat`, which is what the naturality of
`paperPresentationIso` is stated against. -/

example : BPSet ⥤ Cat := chLocOpFunctor

example {K K' : BPSet} (f : K ⟶ K') :
    chLocOpFunctor.map f = (chLocOpMap f).toCatHom := chLocOpFunctor_map f

example : ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left := exists_not_isRun_over

example : Presents Cut.poly ((Ch Zbp)ᵒᵖ) := zCutPresentation

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

example {B : Type u} [Category.{v} B] (V : MorphismProperty B) (P : B ⥤ Type w)
    (hP : V.IsInvertedBy P) :
    (Localization.elementsDescent V P hP).IsLocalization
      (V.inverseImage (CategoryOfElements.π P)) :=
  Localization.isLocalization_elementsDescent V P hP

/-! ## The geometry the presentations rest on -/

example (n : ℕ) : SeparatesMerges (□n) := separatesMerges_cube n

example {n : ℕ} {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h₁ : codim u₁ = 1) (h₂ : codim u₂ = 1) (hne : d₁ ≠ d₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), codim v₁ = 1 ∧ codim v₂ = 1 :=
  exists_join u₁ u₂ h₁ h₂ hne

example {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    IsPushout (wedge2Map f (𝟙 Y)) (wedge2Map (𝟙 X) g)
      (wedge2Map (𝟙 X') g) (wedge2Map f (𝟙 Y')) :=
  wedge2Map_isPushout f g

example {K : BPSet} {a b : Ch K} {N : ℕ} (h : BPSet.dimSum a.dims = N) (f : a ⟶ b) :
    W K f ↔ ChainCat.crossPerm h f = 1 :=
  W_iff_crossPerm_eq_one h f

example {K : BPSet} {a b c : Ch K} {N : ℕ} (h : BPSet.dimSum a.dims = N) (f : a ⟶ b) (g : b ⟶ c) :
    ChainCat.crossPerm h (f ≫ g) = 1 ↔
      ChainCat.crossPerm h f = 1 ∧ ChainCat.crossPerm (ChainCat.tgtStrands f h) g = 1 :=
  ChainCat.crossPerm_eq_one_comp_iff h f g

example {d d' : List ℕ+} : Nonempty (⋁d ⟶ ⋁d') ↔ Coarser d d' := nonempty_wedgeHom_iff_coarser

/-! ### Codimension two at degree zero: two factorisations, two species, and the crossing -/

example {a b : Ch Zbp} (f : a ⟶ b) : OneCut f ≃ (cutsOf f : Finset ℕ) := oneCutEquivCuts f

example {a b : Ch Zbp} (f : a ⟶ b) (hf : codim f = 2) : OneCut f ≃ Bool := oneCutEquivBool f hf

example {a b : Ch Zbp} {f : a ⟶ b} (F : OneCut f) (hf : codim f = 2) : codim F.1.π = 1 :=
  F.codim_π hf

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

example (K : BPSet) : (ChainCat.toChZ K).IsDiscreteFibration := inferInstance

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

end Claims
