-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Concurrency.Salvetti.SalBraid
  -- Sal (braidCOM n) ≌ Ch⋆ (□n); topeCross = stepPerm
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
  -- realize ⊣ Nerve, nerveRealizeIso
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
