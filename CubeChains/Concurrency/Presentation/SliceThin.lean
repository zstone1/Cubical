import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Concurrency.Merge.WedgeLocalize

/-!
# Concurrency/Presentation/SliceThin — the localized slice is a poset

The one thing the slice route spends thinness on, split out from the colimit machinery that also
wants it: a consumer needing only "the slice is a poset" should not import a presentation of
`Ch(K)[W⁻¹]` to get it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-- **The localized slice is a poset** — `locCube_isThin` bead by bead, along the splitting. -/
instance locSlice_isThin : ∀ d : List ℕ+, Quiver.IsThin ((W (⋁d)).Localization)
  | [] => locCube_isThin 0
  | n :: rest =>
      haveI := locSlice_isThin rest
      isThin_of_equiv (locChConsEquiv n rest)

/-- **…and so is the localized slice over any chain of the base** — read through
`locOverEquivWedge`. -/
instance locOver_isThin (d : Ch Zbp) :
    Quiver.IsThin (((W Zbp).over (X := d)).Localization) :=
  haveI := locSlice_isThin d.dims
  isThin_of_equiv (locOverEquivWedge d).symm

end ChainCat
