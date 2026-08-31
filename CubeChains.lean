-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Concurrency.Salvetti.SalBraid
  -- Sal (braidCOM n) ≌ Ch⋆ (□n); topeCross = stepPerm
import CubeChains.Concurrency.Executions.RunWedgeZ
  -- RunWedge ≌ Ch⋆ Zbp — Conc at the terminal object
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
import CubeChains.Concurrency.Complexification.NoMonodromy
  -- the chains of the cube carry no loops
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
import CubeChains.Machinery.Braid.Kernel
  -- Schreier generators of ker (permHom) = PureBraid n
import CubeChains.Machinery.Presentation.FreeGroupoidPresentation
  -- End (mk x : FreeGroupoid C) ≃* Pres S
import CubeChains.Machinery.Localization.LocalizationMonoid
  -- End of a localization = the category's own arrows

-- Retained infrastructure, off the results' path.
import CubeChains.Precubical.Basic.Nerve
  -- realize ⊣ Nerve, nerveRealizeIso
import CubeChains.Precubical.Wedge.GeoTensor.BP
  -- the geometric ⊗ᵍ on BPSet, cubeTensorIsoBP
import CubeChains.Precubical.Wedge.CubeTensor
  -- the cube/Day-convolution comparison
import CubeChains.Machinery.Quotient.DeckExact
  -- the short exact sequence of a regular covering
import CubeChains.Machinery.Quotient.ShortFive
  -- the non-abelian short five lemma
import CubeChains.Machinery.Localization.ElementsProd
  -- (F ⊠ G).Elements ≌ F.Elements × G.Elements
import CubeChains.Machinery.Arrangement.COMSum
  -- Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂
import CubeChains.Machinery.Presentation.FreeGroupoidLift
  -- lift₂ (the tensorator) and the terminal collapse
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
import CubeChains.Concurrency.Executions.Covering
  -- proj/π are discrete opfibrations, not coverings
import CubeChains.Machinery.Quotient.SkeletalEquiv
  -- a skeletal equivalence is a bijection on objects
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
import CubeChains.Concurrency.Merge.AtomPair
  -- the atom relations of PosBraid, as composable chain maps
import CubeChains.Concurrency.Grading.TopBead
  -- merges into the coarsest chain: existence, and rigidity
import CubeChains.Concurrency.Presentation.ChainLocMonoid
  -- End of the localized strand-n component = LocMonoid
import CubeChains.Concurrency.Presentation.GarsideChains
  -- that End, presented by the interval 1^n ⟶ [n]; and Δ
import CubeChains.Concurrency.Presentation.ArtinRelations
  -- and in Artin shape: codim-1 atoms, codim-2 relations
import CubeChains.Concurrency.Presentation.PosLocalization
  -- chPosBraid Zbp *is* the localization at W
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
  -- Ch (H □ⁿ)[merges⁻¹] ≌ PosBraidAction n
import CubeChains.Machinery.Localization.ElementsPresentation
  -- a presented base presents ∫P
import CubeChains.Machinery.Localization.MonoidPresentation
  -- a presented monoid is a one-object category
import CubeChains.Concurrency.Presentation.CutPresentation
  -- Ch Zbp presented by its bead cuts
import CubeChains.Concurrency.Presentation.LiftPresentation
  -- and hence Ch K; the vertex monoids do not follow
import CubeChains.Concurrency.Complexification.WallPresentation
  -- the codimension filtration: runs, wall spans, and the codimension-two relation
