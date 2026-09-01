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
import CubeChains.Machinery.Localization.ElementsAction
  -- a functor on SingleObj M is an M-set
import CubeChains.Concurrency.Complexification.HPosAction
  -- the decorated chains of □ⁿ acting on the orderings of its axes
import CubeChains.Machinery.Localization.ElementsPresentation
  -- a presented base presents ∫P
import CubeChains.Machinery.Localization.ActionPresentation
  -- hence a presented monoid presents its action category
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
import CubeChains.Concurrency.Presentation.HAction
  -- and the decorated chains of □ⁿ are the positive braid action
