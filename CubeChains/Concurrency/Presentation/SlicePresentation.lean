import CubeChains.Concurrency.Presentation.CubePresentation
import CubeChains.Concurrency.Merge.WedgeLocalize
import CubeChains.Machinery.Presentation.Product

/-!
# Concurrency/Presentation/SlicePresentation — the localized slice over an arbitrary shape

`Ch (⋁d)[W⁻¹]` splits as a **product over the beads** (`locChConsEquiv`), each factor being the
cube's localized slice.  So the presentation is `Presents.prod` iterated: one copy of the cube's
atom-step polygraph per bead, and the product's `interchange` 2-cells saying that atoms in
different beads commute.

That is the whole file — the induction step is one line, because `Presents.prod` is
hypothesis-free.  `Presents.ofThin` would also apply (`locSlice_isThin`), but it would quotient by
*every* parallel pair, losing exactly the interchange relations that name why the beads are
independent.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

instance instIsThinProd {C D : Type*} [Category C] [Category D] [Quiver.IsThin C]
    [Quiver.IsThin D] : Quiver.IsThin (C × D) :=
  fun X Y => inferInstanceAs (Subsingleton ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))

/-- **The localized slice is a poset** — `locCube_isThin` bead by bead, along the splitting. -/
instance locSlice_isThin : ∀ d : List ℕ+, Quiver.IsThin ((W (⋁d)).Localization)
  | [] => locCube_isThin 0
  | n :: rest =>
      haveI := locSlice_isThin rest
      isThin_of_equiv (locChConsEquiv n rest)

/-- **The polygraph of a shape**: one copy of the cube's atom steps per bead, the copies commuting
by the product's `interchange`.  The trailing `□0` the recursion leaves is a one-object factor with
no generators. -/
def slicePoly : List ℕ+ → Polygraph.{0, 0}
  | [] => Polygraph.thin (CubeStep 0)
  | n :: rest => Polygraph.prod (Polygraph.thin (CubeStep (n : ℕ))) (slicePoly rest)

/-- **`Ch (⋁d)[W⁻¹]` is presented, bead by bead.**  `Presents.prod` on the polygraphs,
`locChConsEquiv` on the categories. -/
noncomputable def slicePresentation :
    ∀ d : List ℕ+, Presents (slicePoly d) ((W (⋁d)).Localization)
  | [] => cubePresentation 0
  | n :: rest =>
      ((cubePresentation (n : ℕ)).prod (slicePresentation rest)).transport
        (locChConsEquiv n rest)

/-- **…and so is the slice of the base over that shape** — `overEquivWedgeChains` is on the nose,
so this is the same polygraph read through `locOverEquivWedge`. -/
noncomputable def overSlicePresentation (d : List ℕ+) :
    Presents (slicePoly d) (((W Zbp).over (X := zObj d)).Localization) :=
  (slicePresentation d).transport (locOverEquivWedge d).symm

end ChainCat
