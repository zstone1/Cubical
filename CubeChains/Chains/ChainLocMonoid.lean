import CubeChains.Chains.TopBead
import CubeChains.Foundations.GarsidePresentation
import CubeChains.Foundations.LocalizationMonoid
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Chains/ChainLocMonoid — a strand component, presented by its own arrows

`ChN K n` is the full subcategory of `Ch K` on the chains of `dimSum n` — the fibre of the strand
grading — and `WinfN K n` the bead merges restricted to it.  A merge is pinned by its endpoints
(`eq_of_Winf`), so an object the merges reach from is a `Costar` and one they reach is a `Star`.
Over `Zbp` the coarsest chain is such a star, and `Foundations/LocalizationMonoid` applies: the
loops there are the monoid presented by the chain morphisms themselves.
-/

open CategoryTheory CubeChains BPSet

namespace ChainCat

variable {n : ℕ}

/-! ### The strand-`n` component -/

/-- Chains whose beads fire `n` events in total.  Reducible: it is the fibre of the strand grading
`fun a => dimSum a.dims`, and `Foundations/LocalizationSigma` must see that. -/
abbrev StrandCount (K : BPSet) (n : ℕ) : ObjectProperty (Ch K) := fun a => dimSum a.dims = n

/-- `ChN K n` — the chains of `K` on `n` events, full in `Ch K`. -/
abbrev ChN (K : BPSet) (n : ℕ) := (StrandCount K n).FullSubcategory

/-- `ChZn n` — the serial wedges on `n` strands. -/
abbrev ChZn (n : ℕ) := ChN Zbp n

/-- The coarsest chain — the basepoint the presentation is read at. -/
def topObj (n : ℕ) : ChZn n := ⟨zObj (topDims n), dimSum_topDims n⟩

/-! ### The class -/

/-- The bead merges, restricted to the component. -/
def WinfN (K : BPSet) (n : ℕ) : MorphismProperty (ChN K n) :=
  (Winf K).inverseImage (StrandCount K n).ι

instance (K : BPSet) (n : ℕ) : (WinfN K n).IsMultiplicative :=
  inferInstanceAs ((Winf K).inverseImage (StrandCount K n).ι).IsMultiplicative

theorem winfN_iff {K : BPSet} {A B : ChN K n} (f : A ⟶ B) : WinfN K n f ↔ Winf K f.hom := Iff.rfl

/-! ### The two ends

A merge is determined by its endpoints, so an object the merges reach *from* is initial among them
and one they reach *to* is terminal: `eq_of_Winf` is the whole uniqueness argument in both cases. -/

/-- **A chain that merges into every chain of its component is a costar.** -/
noncomputable def costarOfExistsMerge {K : BPSet} (o : ChN K n)
    (h : ∀ A : ChN K n, ∃ u : o ⟶ A, WinfN K n u) : Costar (WinfN K n) o :=
  Limits.IsInitial.ofUniqueHom
    (fun A => ⟨(h A.obj).choose, (h A.obj).choose_spec⟩)
    fun A f => WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (eq_of_Winf f.property (h A.obj).choose_spec))

/-! The classifying map into the terminal `Zbp` is unique, so a chain of `Ch Zbp` **is** its
dimension list and `totalTo` already supplies the merge into the coarsest chain. -/

theorem exists_Winf_out {a : Ch Zbp} (h : dimSum a.dims = n) :
    ∃ f : a ⟶ zObj (topDims n), Winf Zbp f := by
  obtain ⟨d, map⟩ := a
  obtain rfl : map = (zObj d).map := Subsingleton.elim _ _
  exact ⟨totalTo d h, Winf_totalTo d h⟩

/-- **The coarsest chain is a star**: a merge out of every chain exists, and `eq_of_Winf` pins
it, so it is terminal in the wide subcategory of merges. -/
noncomputable def starZ (n : ℕ) : Star (WinfN Zbp n) (topObj n) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A => ⟨ObjectProperty.homMk (exists_Winf_out A.obj.property).choose,
      (exists_Winf_out A.obj.property).choose_spec⟩)
    fun A f => WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (eq_of_Winf f.property (exists_Winf_out A.obj.property).choose_spec))

/-! ### The presentation -/

/-- **The endomorphisms of the serial-wedge component localized at the bead merges are the monoid
presented by the chain morphisms themselves.** -/
noncomputable def endEquivWinfN (n : ℕ) :
    LocMonoid (WinfN Zbp n) ≃* End ((WinfN Zbp n).Q.obj (topObj n)) :=
  endEquiv (starZ n)

end ChainCat
