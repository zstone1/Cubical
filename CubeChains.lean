-- The five interesting results. Importing them transitively builds their whole cone, so
-- `lake build CubeChains` is the acceptance gate for the braid + wedge-correspondence thread.
import CubeChains.Braid.SalvettiDeckCompat      -- braidMonodromy, braidMonodromy_bijective (the 5-lemma)
import CubeChains.Braid.CubePureBraidResult     -- cube_concBraid_pureBraid (the left iso)
import CubeChains.Braid.CubeTerminalDescent      -- concToZAut_injective
import CubeChains.Salvetti.BraidIso              -- braidSalEquiv
import CubeChains.Chains.Correspondence          -- equivWedgeCat

-- Retained infrastructure not on the results' path: the model bridge and the geometric product.
import CubeChains.Foundations.Nerve              -- realize ⊣ Nerve, nerveRealizeIso (needs Reachability)
import CubeChains.Foundations.BPTensor           -- ⊗ on BPSet / PrecubicalSet (Day), cubeTensorIso
