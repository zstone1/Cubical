import CubeChains.Precubical.Chains.Correspondence
import CubeChains.Precubical.Chains.CubeNonSelfLinked
import CubeChains.Precubical.Segal.SegalAltitude
import CubeChains.Machinery.Localization.FibrationLocalize

/-!
# Concurrency/Executions/Elements — thinness for `Ch⋆ (□ⁿ) = (Lines □ⁿ).Elements`

A category of elements is thin as soon as its base is, and `Ch (□ⁿ)` is thin.  The generic
`Elements` toolkit (`CategoryOfElements.pre`/`mapEquivalence`) is in
`Machinery/Localization/FibrationLocalize`.
-/

open CategoryTheory Opposite BPSet

namespace CategoryTheory

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- If the base category `C` is thin, then so is the category of elements of any
`P : C ⥤ Type w`. -/
instance Functor.elements_isThin [Quiver.IsThin C] (P : C ⥤ Type w) :
    Quiver.IsThin P.Elements := fun p q => by
  have : Subsingleton (p.1 ⟶ q.1) := ‹Quiver.IsThin C› p.1 q.1
  exact ⟨fun f g => CategoryOfElements.ext P f g (Subsingleton.elim _ _)⟩

end CategoryTheory

namespace CubeChain

open CategoryTheory

/-- **Chains of a cube are a poset** — a chart pins the map it came from.  The cube discharges both
hypotheses of `chainCat_hom_subsingleton`, so this is the one place they are supplied. -/
instance chCube_isThin (n : ℕ) :
    Quiver.IsThin (Ch (□n)) :=
  chainCat_hom_subsingleton (cube_nonSelfLinked n) (cube_admitsAltitude n)

end CubeChain
