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
  -- juxtaposition of braids; permLen is block-additive

-- Retained infrastructure, off the results' path.
import CubeChains.Precubical.Basic.Nerve
  -- nerveRealizeIso : Nerve (realize X) ≅ X
import CubeChains.Precubical.Wedge.GeoTensor.BP
  -- the geometric ⊗ᵍ on BPSet, cubeTensorIsoBP
import CubeChains.Precubical.Wedge.CubeTensor
  -- the cube/Day-convolution comparison
import CubeChains.Machinery.Localization.ElementsProd
  -- F ⊠ G, the external product of two Type-valued functors
import CubeChains.Machinery.Arrangement.COMSum
  -- Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂
import CubeChains.Machinery.HomMonoidal
  -- homLaxMonoidal; Graded (a monoid from a lax functor)
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
import CubeChains.Concurrency.Grading.ChartHom
  -- a wedge map is a chart refining a chart; flatten, and crossPerm read off it
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
import CubeChains.Machinery.Presentation.Glue
  -- one copy of P d for each element over d, glued along the overlap 2-cells
import CubeChains.Machinery.Presentation.GlueRefutation
  -- …and why it needs the labels to be injective
import CubeChains.Machinery.Presentation.GlueOn
  -- copies over a generating set only: fewer 0-cells, so ess-surj replaces bijectivity
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
import CubeChains.Concurrency.Merge.CubeThin
  -- Ch(□n)[W⁻¹] is a poset: every morphism is a word in the atoms, and words are unique
import CubeChains.Concurrency.Merge.CubeWeakOrder
  -- crossLen refined to the permutation itself: a functor to the weak Bruhat order
import CubeChains.Concurrency.Merge.CubeFaces
  -- a chain of a cube is an ordered partition of its axes; two faces meet in one
import CubeChains.Concurrency.Merge.CubeWeakEquiv
  -- …so Ch(□n)[W⁻¹] IS the right weak Bruhat order on Perm (Fin n), read backwards
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
import CubeChains.Machinery.Presentation.Product
  -- and the product presents the product, once the interchange squares are imposed
import CubeChains.Concurrency.Presentation.SlicePresentation
  -- Ch(⋁d)[W⁻¹] presented bead by bead: one cube factor each, commuting by interchange
import CubeChains.Concurrency.Presentation.SliceFunctor
  -- the slice polygraph, functorial in Ch Zbp: 0-cells the runs over d, 1-cells one crossing apart
import CubeChains.Concurrency.Presentation.SliceExchange
  -- the localized slice presented by its run-arrows, for every d: the exchange, and the glue family
import CubeChains.Concurrency.Presentation.CubeChartAction
  -- the cube's atoms are an Artin family: PosBraid n acting partially on the charts over the run
import CubeChains.Concurrency.Presentation.CubePresentation
  -- Ch(□n)[W⁻¹] presented: generators the atom steps, relations all of them — it is a poset
import CubeChains.Concurrency.Presentation.CubeChartWeakOrder
  -- the lifted charts are the weak order on Sₙ, hence Ch(□n)[W⁻¹] read backwards
import CubeChains.Concurrency.Presentation.CutPresentation
  -- Ch Zbp presented by its bead cuts
import CubeChains.Concurrency.Presentation.LiftPresentation
  -- and hence Ch K; the vertex monoids do not follow
import CubeChains.Concurrency.Presentation.LocPresentation
  -- the atoms of a run, and the codimension-two cells two of them meet in
import CubeChains.Concurrency.Presentation.PartialAtom
  -- …acting partially on the runs of K: flip the square at a cut, if K has one
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
import CubeChains.Concurrency.Presentation.GlueVsFibration
  -- the glue route and the fibration route name the same 0-cells, and its 1-cells name atoms

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

/-! ## `Ch(K)[W⁻¹]` is presented, for every `K` -/

example (K : BPSet) :
    Presents (Polygraph.glueOn (wedgeHoms K) runLabels (chGlueV '' MaximalChains K))
      ((W K).Localization) :=
  presentsChainsRunGlue K

example (d : Ch Zbp) : Presents (runPoly d) (((W Zbp).over (X := d)).Localization) :=
  runSlicePresentation d

example (K : BPSet) (c : Ch K) :
    Presents (slicePoly c.dims) (((W K).over (X := c)).Localization) :=
  chOverSlicePresentation K c

example (d : List ℕ+) : Presents (slicePoly d) ((W (⋁d)).Localization) := slicePresentation d

example (d : List ℕ+) : Presents (slicePoly d) (((W Zbp).over (X := zObj d)).Localization) :=
  overSlicePresentation d

example (n : ℕ) : Presents (Polygraph.thin (CubeStep n)) ((W (□n)).Localization) :=
  cubePresentation n

example : Presents Cut.poly ((Ch Zbp)ᵒᵖ) := zCutPresentation

example (K : BPSet) {P : Polygraph.{w', u'}} (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    Presents (p.elementsPoly (wedgeHoms K)) ((Ch K)ᵒᵖ) :=
  chPresentation K p

example (K : BPSet) : Presents (chCutPoly K) ((Ch K)ᵒᵖ) := chCutPresentation K

example (n : ℕ) : Presents (hLocPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) := hLocPresentation n

example (n : ℕ) : Presents (hLocPoly n) ((PosBraidAction n)ᵒᵖ) := hLocActionPresentation n

/-! ## …parametrically in a presentation of the base -/

example (n : ℕ) {P : Polygraph.{w', u'}} (p : Presents P (((W Zbp).op).Localization)) :
    Presents (cubeChartPoly n p) ((W (□n)).Localization) :=
  cubeLocPresentation n p

example {P : Polygraph.{u, u}} (p : Presents P (((W Zbp).op).Localization)) (d : List ℕ+) :
    Presents (beadPoly (fun m => cubeChartPoly m p) d) ((W (⋁d)).Localization) :=
  sliceLocPresentation p d

example :
    Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N))
      (((W Zbp).op).Localization) :=
  zLocPresentation

example :
    Presents (Polygraph.coproduct fun N => monoidPoly (ArtinRel N)) (((W Zbp).op).Localization) :=
  zLocArtinPresentation

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

example {D : Type u} [Category.{v} D] (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u'}}
    (L : Polygraph.SliceLabels P) (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hL : ∀ (d : D) (a : (P.obj d).V),
      (p d).at' ⟨a⟩ = Localization.Construction.objEquiv V.over (L.ob d a))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f)
    (hbij : ∀ d : D, Function.Bijective (p d).E.obj) :
    Presents (Polygraph.glue X L)
      ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  Polygraph.presentsGlue X L V p hL hP hbij

example {D : Type u} [Category.{v} D] (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u'}}
    (L : Polygraph.SliceLabels P) (S : Set (Polygraph.GlueV X)) (V : MorphismProperty D)
    (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
    (hL : ∀ (d : D) (a : (P.obj d).V),
      (p d).at' ⟨a⟩ = Localization.Construction.objEquiv V.over (L.ob d a))
    (hP : ∀ {d' d : D} (f : d' ⟶ d),
      (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f)
    (hthin : ∀ d : D, Quiver.IsThin ((V.over (X := d)).Localization))
    (R : Polygraph.SliceRetract L V) (hgen : Polygraph.Generating X S) :
    Presents (Polygraph.glueOn X L S)
      ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  Polygraph.presentsGlueOn X L S V p hL hP hthin R hgen

example {B : Type u} [Category.{v} B] (V : MorphismProperty B) (P : B ⥤ Type w)
    (hP : V.IsInvertedBy P) :
    (Localization.elementsDescent V P hP).IsLocalization
      (V.inverseImage (CategoryOfElements.π P)) :=
  Localization.isLocalization_elementsDescent V P hP

/-! ## The cube slice is the weak Bruhat order -/

example (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) := locCube_isThin n

example (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ := locCubeWeakOrder n

example {n : ℕ} {c c' : Ch (□n)} :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') ↔ weakClass c' ≤ weakClass c :=
  nonempty_loc_hom_iff

example (n : ℕ) : ChartCat n ≌ WeakOrder n := chartWeakEquiv n

example (n : ℕ) :
    (Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory ≌ (W (□n)).Localization :=
  definedCubeFibreLoc n

example (n : ℕ) : IsArtinFamily (cubeAtom n) := isArtinFamily_cubeAtom n

example (n : ℕ) :
    Presents (cubeChartPoly n zLocPresentation)
      ((Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory) :=
  cubeChartGarside n

example (n : ℕ) :
    Presents (cubeChartPoly n zLocArtinPresentation)
      ((Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory) :=
  cubeChartArtin n

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
  chartHomEquiv χ

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
    IsSegal K ↔ ∀ (p q : ℕ) (x : K.cells p) (y : K.cells q), K.vertex₁ x = K.vertex₀ y →
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

example : ¬ Nonempty (Presents (Polygraph.glue X₂ L₂)
    ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization)) :=
  not_nonempty_presents_glue

example : W Zbp (runMerge (zObj ([2] : List ℕ+)) dimSum_two) ∧
    IsEmpty (zObj ([2] : List ℕ+) ⟶ zObj (𝟙^2)) ∧ Nonempty (zObj (𝟙^2) ⟶ zObj (𝟙^2)) :=
  merge_fibres_clash

example : ¬ Polygraph.Generating (wedgeHoms Zbp) (chGlueV '' {a : Ch Zbp | IsRun Zbp a}) :=
  not_generating_isRun

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

example (m n : ℕ) :
    MonoidalCategory.externalProduct (yoneda.obj ▫m) (yoneda.obj ▫n)
      ⟶ MonoidalCategory.tensor Boxᵒᵖ ⋙ yoneda.obj ▫(m + n) :=
  Box.cubeTensorPair m n

example {E₁ : Type u} {E₂ : Type u'} (L₁ : COM E₁) (L₂ : COM E₂) :
    Sal (L₁.directSum L₂) ≌ Sal L₁ × Sal L₂ :=
  COM.salSumEquiv L₁ L₂

example (C : Type u) [Category.{v} C] [MonoidalCategory C] : (Functor.hom C).LaxMonoidal :=
  homLaxMonoidal C

example (X : PrecubicalSet) : PrecubicalSet.Nerve.obj (PrecubicalSet.realize.obj X) ≅ X :=
  PrecubicalSet.nerveRealizeIso X

example (m n : ℕ) : □m ⊗ᵍ □n ≅ □(m + n) := GeoTensor.cubeTensorIsoBP m n

example {K : BPSet} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    CubeChain.RefineObj K.init K.final ≌ Ch K :=
  CubeChain.equivWedgeCat h₁ h₂

/-! ## The glue route against the fibration route

The 0-cells agree by a theorem, not by unfolding; the 1-cells agree because a glue 1-cell names an
atom.  The two polygraphs present *opposite* categories, so a comparison needs `Presents.op` before
it can be stated at all. -/

example (K : BPSet) (v : Polygraph.GlueV (wedgeHoms K)) :
    Polygraph.Covered (wedgeHoms K) runLabels (chGlueV '' MaximalChains K) v ↔ IsRun Zbp v.1 :=
  covered_iff_isRun K v

example (n : ℕ) :
    Polygraph.GlueOnV (wedgeHoms (Hbp.obj (□n))) runLabels
        (chGlueV '' MaximalChains (Hbp.obj (□n))) ≃ Equiv.Perm (Fin n) :=
  glueOnVEquivPerm n

example {d : Ch Zbp} {a b : RunOver d} (h : RunStep a b) :
    ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d)
      (k : Fin (BPSet.dimSum a.1.left.dims - 1)),
      ChainCat.crossPerm rfl t = adjT k ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom :=
  runStep_exists_adjT h

example (K : BPSet) (d : Ch Zbp) (x : (wedgeHoms K).obj (Opposite.op d)) :
    Polygraph.glueSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltBraid K = overBraid d :=
  glueSliceEval_comp_eltBraid K d x

end Claims
