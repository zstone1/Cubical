-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Salvetti.SalBraid          -- Sal (braidCOM n) ≌ Ch⋆ (□n); crossPerm = stepPerm
import CubeChains.Salvetti.RunWedgeZ         -- RunWedge ≌ Ch⋆ Zbp — Conc at the terminal object
import CubeChains.Salvetti.ChStarProduct     -- Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ — a chain in a product
import CubeChains.Salvetti.ChStarSym         -- Ch (Hbp K) ≌ Ch (K.prod runBp) — the twist
import CubeChains.Salvetti.SalCompare        -- Ch⋆ K ≌ Sal L from bases + presheaves
import CubeChains.Arrangements.SalSymmetry   -- the Sₙ reorientation action on Sal (braidCOM n)
import CubeChains.Salvetti.SymReorient        -- Sₙ acts on Hbp □ⁿ; □ⁿ is rigid, so □ⁿ × run is not
import CubeChains.Salvetti.WallCrossing       -- atoms are wall crossings; codimension counts walls
import CubeChains.Braid.Artin                -- the Garside germ vs. the Artin presentation
import CubeChains.Braid.PosGerm              -- the positive braid monoid; PosPureBraid; atoms suffice
import CubeChains.Braid.Matsumoto            -- Matsumoto for Sₙ: the germ IS the Artin monoid/group
import CubeChains.Braid.Graded               -- Graded M: degrees as objects, End n = M n
import CubeChains.Braid.Sum                  -- juxtaposition of braids; permLen is block-additive
import CubeChains.Braid.Kernel               -- Schreier generators of ker (permHom) = PureBraid n
import CubeChains.Foundations.FreeGroupoidPresentation  -- End (mk x : FreeGroupoid C) ≃* Pres S
import CubeChains.Foundations.LocalizationMonoid -- End of a localization = the category's own arrows
import CubeChains.Foundations.GarsidePresentation -- a star and a costar: presented by the simples

-- Retained infrastructure, off the results' path.
import CubeChains.Foundations.Nerve              -- realize ⊣ Nerve, nerveRealizeIso
import CubeChains.Foundations.GeoTensor.BP       -- the geometric ⊗ᵍ on BPSet, cubeTensorIsoBP
import CubeChains.Foundations.CubeTensor         -- the cube/Day-convolution comparison
import CubeChains.Foundations.DeckExact          -- the short exact sequence of a regular covering
import CubeChains.Foundations.ShortFive          -- the non-abelian short five lemma
import CubeChains.Foundations.ElementsProd       -- (F ⊠ G).Elements ≌ F.Elements × G.Elements
import CubeChains.Arrangements.COMSum            -- Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂
import CubeChains.Foundations.FreeGroupoidLift   -- lift₂ (the tensorator) and the terminal collapse
import CubeChains.Foundations.HomMonoidal    -- homLaxMonoidal; Graded (a monoid from a lax functor)
import CubeChains.Foundations.SymBox             -- SBox, J : Box ⥤ SBox, and sHomEquiv
import CubeChains.Foundations.SymPresheaf        -- H = J* ∘ J₍!₎, the left Kan extension along J.op
import CubeChains.Foundations.SymRepresentable    -- symFree (□ⁿ) ≅ y(▪n), and Sₙ acting on H(□ⁿ)
import CubeChains.Salvetti.SymRun                -- H Z ≅ runPresheaf
import CubeChains.Salvetti.SymOverRun            -- H K ⟶ runBp exists; H (□²) ⟶ □² does not
import CubeChains.Salvetti.Covering        -- proj/π are discrete opfibrations, not coverings
import CubeChains.Foundations.SkeletalEquiv -- a skeletal equivalence is a bijection on objects
import CubeChains.Foundations.LocalizationSigma -- a coproduct of localizations localizes Σ i, C i
import CubeChains.Chains.MergeClass -- the bead merges of Ch X, and the class Winf they generate
import CubeChains.Chains.WedgeBraid -- Ch K ⥤ FullBraid, from the coordinate map alone
import CubeChains.Chains.ShuffleHom -- a wedge map is its coordinate bijection; chBraid is faithful
import CubeChains.Chains.MergeBraid -- chBraid kills the merges: crossPerm = 1 on Winf
import CubeChains.Chains.MergeGenerate -- and the converse: Winf is the non-braiding property
import CubeChains.Chains.AtomPair   -- the atom relations of PosBraid, as composable chain maps
import CubeChains.Chains.TopBead -- merges into the coarsest chain: existence, and rigidity
import CubeChains.Chains.ChainLocMonoid -- End of the localized strand-n component = LocMonoid
import CubeChains.Chains.GarsideChains -- that End, presented by the interval 1^n ⟶ [n]; and Δ
import CubeChains.Chains.ArtinRelations -- and in Artin shape: codim-1 atoms, codim-2 relations
import CubeChains.Chains.PosLocalization -- chPos Zbp *is* the localization at Winf
import CubeChains.Foundations.FibrationLocalize -- ∫P localized at the lifts of W is ∫P̄
import CubeChains.Chains.ElementsFibration -- Ch K is the category of elements of ⋁- ⟶ K
import CubeChains.Salvetti.RunClassifier -- Hbp Zbp ≅ runBp classifies runs; H is a twist, not a product
import CubeChains.Chains.SegalCondition -- the merges act bijectively iff the wedge is the tensor
import CubeChains.Salvetti.HSegal -- and for H(□ⁿ) it is: ▪(p+q) is the wedge ▪p ∨ ▪q
import CubeChains.Braid.PosAction -- PosBraid n acting on the orderings; no units, hence no isos
import CubeChains.Foundations.ElementsAction -- a functor on SingleObj M is an M-set
import CubeChains.Salvetti.HPosAction -- Ch (H □ⁿ)[merges⁻¹] ≌ PosBraidAction n
import CubeChains.Foundations.ElementsPresentation -- a presented base presents ∫P
import CubeChains.Foundations.MonoidPresentation -- a presented monoid is a one-object category
import CubeChains.Foundations.SigmaPresentation -- presentations add up over a coproduct
import CubeChains.Braid.GermPresentation -- FullPosBraidᵒᵖ presented by the germ relations
import CubeChains.Chains.CutPresentation -- Ch Zbp presented by its bead cuts
import CubeChains.Chains.LiftPresentation -- and hence Ch K; the vertex monoids do not follow
