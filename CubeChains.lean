-- The results, and the retained infrastructure they do not use.  `lake build CubeChains` builds
-- exactly this import cone; only `Testing/` sits outside it.
import CubeChains.Salvetti.SalBraid          -- Sal (braidCOM n) ≌ Ch⋆ (□n); crossPerm = stepPerm
import CubeChains.Salvetti.RunWedgeZ         -- RunWedge ≌ Ch⋆ Zbp — Conc at the terminal object
import CubeChains.Salvetti.ChStarProduct     -- Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ — a chain in a product
import CubeChains.Arrangements.SalSymmetry   -- the Sₙ reorientation action on Sal (braidCOM n)
import CubeChains.Braid.Artin                -- the Garside germ vs. the Artin presentation
import CubeChains.Braid.Sum                  -- juxtaposition of braids; permLen is block-additive
import CubeChains.Braid.Kernel               -- Schreier generators of ker (permHom) = PureBraid n
import CubeChains.Braid.Category             -- 𝔅 = Σ n, SingleObj (Braid n)
import CubeChains.Foundations.FreeGroupoidPresentation  -- End (mk x : FreeGroupoid C) ≃* Pres S

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
import CubeChains.Salvetti.SymRun                -- H Z ≅ runPresheaf
import CubeChains.Salvetti.Covering        -- proj/π are discrete opfibrations, not coverings
import CubeChains.Foundations.SkeletalEquiv -- a skeletal equivalence is a bijection on objects
