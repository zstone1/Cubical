-- `lake build CubeChains` builds this import cone: the retained lower layers (Foundations →
-- Chains), the model bridge and the geometric product, and the executions layer up to the
-- braid-Salvetti comparison.
import CubeChains.Chains.Correspondence          -- equivWedgeCat (chains are wedge maps)
import CubeChains.Foundations.Nerve              -- realize ⊣ Nerve, nerveRealizeIso
import CubeChains.Foundations.GeoTensor.BP        -- computable geometric ⊗ on BPSet / GeoBP, cubeTensorIsoBP
import CubeChains.Foundations.DeckExact           -- the quotient/covering theory the Sₙ quotient consumes
import CubeChains.Braid.PermWord                  -- permutation ↦ braid word; Schreier generators of the pure braids
import CubeChains.Foundations.FreeGroupoidLift     -- lift₂ (the tensorator) and the terminal collapse
import CubeChains.Foundations.Terminal             -- Z, the final precubical object
import CubeChains.Arrangements.COMSum              -- direct sum of COMs, and the splitting of Sal
import CubeChains.Foundations.ElementsProd         -- (F ⊠ G).Elements ≌ F.Elements × G.Elements
import CubeChains.Foundations.ShortFive             -- bijective_middle, the engine of braidMonodromy_bijective
import CubeChains.Foundations.CubeTensor            -- the cube/Day-convolution comparison
import CubeChains.Foundations.HomMonoidal           -- homLaxMonoidal; Graded (a monoid from a lax functor)
import CubeChains.Salvetti.Runs
import CubeChains.Salvetti.ConcCube             -- [RESULT] the loops of executions of □ⁿ are the pure braids
