import CubeChains.Chains.TopBead
import CubeChains.Foundations.LocalizationMonoid
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Chains/ChainLocMonoid — a strand component, presented by its own arrows

`ChZn n` is the full subcategory of the serial wedges `Ch Zbp` on the chains of `dimSum n` — the
fibre of the strand grading — and `WinfN n` the bead merges restricted to it.  The total merge
exists out of every object (`exists_Winf_out`) and is pinned by its endpoints (`eq_of_Winf`), so
the coarsest chain is terminal among the merges — a `Star`.  `Foundations/LocalizationMonoid` then
applies: the loops there are the monoid presented by the chain morphisms themselves.
-/

open CategoryTheory CubeChains BPSet

namespace ChainCat

variable {n : ℕ}

/-! ### The strand-`n` component -/

/-- Chains whose beads fire `n` events in total.  Reducible: it is the fibre of the strand grading
`fun a => dimSum a.dims`, and `Foundations/LocalizationSigma` must see that. -/
abbrev StrandCount (n : ℕ) : ObjectProperty (Ch Zbp) := fun a => dimSum a.dims = n

/-- `ChZn n` — the serial wedges on `n` strands, full in `Ch Zbp`. -/
abbrev ChZn (n : ℕ) := (StrandCount n).FullSubcategory

/-- The coarsest chain — the basepoint the presentation is read at. -/
def topObj (n : ℕ) : ChZn n := ⟨zObj (topDims n), dimSum_topDims n⟩

/-! ### The class -/

/-- The bead merges, restricted to the component. -/
def WinfN (n : ℕ) : MorphismProperty (ChZn n) := (Winf Zbp).inverseImage (StrandCount n).ι

instance (n : ℕ) : (WinfN n).IsMultiplicative :=
  inferInstanceAs ((Winf Zbp).inverseImage (StrandCount n).ι).IsMultiplicative

theorem winfN_iff {A B : ChZn n} (f : A ⟶ B) : WinfN n f ↔ Winf Zbp f.hom := Iff.rfl

/-! ### The star

The classifying map into the terminal `Zbp` is unique, so a chain of `Ch Zbp` **is** its dimension
list and `totalTo` already supplies the merge out of every object; `eq_of_Winf` pins it. -/

theorem exists_Winf_out {a : Ch Zbp} (h : dimSum a.dims = n) :
    ∃ f : a ⟶ zObj (topDims n), Winf Zbp f := by
  obtain ⟨d, map⟩ := a
  obtain rfl : map = (zObj d).map := Subsingleton.elim _ _
  exact ⟨totalTo d h, Winf_totalTo d h⟩

/-- **The coarsest chain is a star**: a merge out of every chain exists, and `eq_of_Winf` pins
it, so it is terminal in the wide subcategory of merges. -/
noncomputable def starZ (n : ℕ) : Star (WinfN n) (topObj n) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A => ⟨ObjectProperty.homMk (exists_Winf_out A.obj.property).choose,
      (exists_Winf_out A.obj.property).choose_spec⟩)
    fun A f => WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (eq_of_Winf f.property (exists_Winf_out A.obj.property).choose_spec))

/-! ### The presentation -/

/-- **The endomorphisms of the serial-wedge component localized at the bead merges are the monoid
presented by the chain morphisms themselves.** -/
noncomputable def endEquivWinfN (n : ℕ) :
    LocMonoid (WinfN n) ≃* End ((WinfN n).Q.obj (topObj n)) :=
  endEquiv (starZ n)

end ChainCat
