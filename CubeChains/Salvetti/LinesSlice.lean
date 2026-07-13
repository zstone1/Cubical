import CubeChains.Chains.ChainSlice
import CubeChains.Salvetti.Lines

/-!
# Salvetti/LinesSlice — locality of the chamber presheaf under push-forward

`Lines` reads only a chain's `dims` and a morphism's underlying wedge map `φ`, neither of
which `ChainCat.pushforward (f : K ⟶ L)` touches (it keeps `dims`/`φ`, only post-composing
`map`).  So the pullback of `Lines K` along `(pushforward a.map).op` recovers
`Lines (⋁a.dims)` on the nose:

> `linesPushforward a : (pushforward a.map).op ⋙ Lines K ≅ Lines (⋁a.dims)`.
-/

open CategoryTheory Opposite

namespace CubeChains

variable {K : BPSet}

/-- Pulling `Lines K` back along push-forward is `Lines (⋁a.dims)`.  Components are
`Iso.refl` (both sides compute `∀ i, Chamber (a.dims.get i)`); naturality holds since
`pushforward` preserves `φ`. -/
noncomputable def linesPushforward (a : Ch K) :
    (ChainCat.pushforward a.map).op ⋙ CubeChains.Lines K
      ≅ CubeChains.Lines (⋁a.dims) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

end CubeChains
