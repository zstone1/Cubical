-- `lake build CubeChains` builds this import cone: the retained lower layers (Foundations →
-- Chains), the model bridge and the geometric product, and the executions layer up to the
-- braid-Salvetti comparison.
import CubeChains.Chains.Correspondence          -- equivWedgeCat (chains are wedge maps)
import CubeChains.Foundations.Nerve              -- realize ⊣ Nerve, nerveRealizeIso
import CubeChains.Foundations.GeoTensor.BP        -- computable geometric ⊗ on BPSet / GeoBP, cubeTensorIsoBP
import CubeChains.Salvetti.BraidIso               -- braidSalEquiv : Sal(braidCOM n) ≌ Int(Lines □ⁿ)
