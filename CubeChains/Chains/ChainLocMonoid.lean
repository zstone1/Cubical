import CubeChains.Chains.TopBead
import CubeChains.Foundations.GarsidePresentation
import CubeChains.Foundations.LocalizationMonoid
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Chains/ChainLocMonoid — a strand component, presented by its own arrows

`ChStrands K n` is the full subcategory of `Ch K` on the chains of `dimSum n` — the fibre of the
strand grading — and `WStrands K n` the bead merges restricted to it.  A merge is pinned by its
endpoints (`eq_of_W`), so an object the merges reach from is initial and one they reach is terminal
in the wide subcategory.  Over `Zbp` the coarsest chain is such a terminal object, and
`Foundations/LocalizationMonoid` applies: the loops there are the monoid presented by the chain
morphisms themselves.
-/

open CategoryTheory CubeChains BPSet

namespace ChainCat

variable {n : ℕ}

/-! ### The strand-`n` component -/

/-- Chains whose beads fire `n` events in total.  Reducible: it is the fibre of the strand grading
`fun a => dimSum a.dims`, and `Foundations/LocalizationSigma` must see that. -/
abbrev HasStrands (K : BPSet) (n : ℕ) : ObjectProperty (Ch K) := fun a => dimSum a.dims = n

/-- The chains of `K` on `n` strands, full in `Ch K`. -/
abbrev ChStrands (K : BPSet) (n : ℕ) := (HasStrands K n).FullSubcategory

/-- The coarsest chain — the basepoint the presentation is read at. -/
def topObj (n : ℕ) : ChStrands Zbp n := ⟨zObj (topDims n), dimSum_topDims n⟩

/-! ### The class -/

/-- The bead merges, restricted to the component. -/
def WStrands (K : BPSet) (n : ℕ) : MorphismProperty (ChStrands K n) :=
  (W K).inverseImage (HasStrands K n).ι

instance (K : BPSet) (n : ℕ) : (WStrands K n).IsMultiplicative :=
  inferInstanceAs ((W K).inverseImage (HasStrands K n).ι).IsMultiplicative

theorem wStrands_iff {K : BPSet} {A B : ChStrands K n} (f : A ⟶ B) :
    WStrands K n f ↔ W K f.hom := Iff.rfl

/-! ### The two ends

A merge is determined by its endpoints, so an object the merges reach *from* is initial among them
and one they reach *to* is terminal: `eq_of_W` is the whole uniqueness argument in both cases. -/

/-- **A chain that merges into every chain of its component is wide-initial.** -/
noncomputable def wideInitialOfExistsMerge {K : BPSet} (o : ChStrands K n)
    (h : ∀ A : ChStrands K n, ∃ u : o ⟶ A, WStrands K n u) : IsWideInitial (WStrands K n) o :=
  Limits.IsInitial.ofUniqueHom
    (fun A => ⟨(h A.obj).choose, (h A.obj).choose_spec⟩)
    fun A f => WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (eq_of_W f.property (h A.obj).choose_spec))

/-! The classifying map into the terminal `Zbp` is unique, so a chain of `Ch Zbp` **is** its
dimension list and `totalTo` already supplies the merge into the coarsest chain. -/

theorem exists_W_out {a : Ch Zbp} (h : dimSum a.dims = n) :
    ∃ f : a ⟶ zObj (topDims n), W Zbp f := by
  obtain ⟨d, map⟩ := a
  obtain rfl : map = (zObj d).map := Subsingleton.elim _ _
  exact ⟨totalTo d h, W_totalTo d h⟩

/-- **The coarsest chain is wide-terminal**: a merge out of every chain exists, and `eq_of_W` pins
it, so it is terminal in the wide subcategory of merges. -/
noncomputable def topWideTerminal (n : ℕ) : IsWideTerminal (WStrands Zbp n) (topObj n) :=
  Limits.IsTerminal.ofUniqueHom
    (fun A => ⟨ObjectProperty.homMk (exists_W_out A.obj.property).choose,
      (exists_W_out A.obj.property).choose_spec⟩)
    fun A f => WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
      (eq_of_W f.property (exists_W_out A.obj.property).choose_spec))

/-! ### The presentation -/

/-- **The endomorphisms of the serial-wedge component localized at the bead merges are the monoid
presented by the chain morphisms themselves.** -/
noncomputable def endEquivWStrands (n : ℕ) :
    LocMonoid (WStrands Zbp n) ≃* End ((WStrands Zbp n).Q.obj (topObj n)) :=
  endEquiv (topWideTerminal n)

end ChainCat
