-- `lake build CubeChains` builds this import cone: the retained lower layers (Foundations →
-- Chains) plus the model bridge and the geometric product.
import CubeChains.Chains.Correspondence          -- equivWedgeCat (chains are wedge maps)
import CubeChains.Foundations.Nerve              -- realize ⊣ Nerve, nerveRealizeIso
import CubeChains.Foundations.GeoTensor.BP        -- computable geometric ⊗ on BPSet / GeoBP, cubeTensorIsoBP
