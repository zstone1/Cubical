import CubeChains.Concurrency.Presentation.BaseDecomposition
import CubeChains.Machinery.Presentation.Partial
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Machinery.Presentation.Monoid

/-!
# Concurrency/Presentation/BasePresentation — `Ch Zbp[W⁻¹]` as a single polygraph

The localized base is the disjoint union of its strand components (`strandDecomposition`) and each
component is one object carrying a presented braid monoid, so the whole of it is the coproduct of
those one-object polygraphs.  `zLocOfComponents` is the assembly; the Garside and Artin spellings
differ only in which component equivalence they hand it.

`zLocComponent` runs the other way, by `Presents.restrict`: an *arbitrary* presentation of the
localized base restricts to one of each strand component — the shape the lift consumes.

At strand count `N` the 1-cells are `Perm (Fin N)` — the maps `1ᴺ ⟶ [N]`, by `onesTopEquiv` — and
the 2-cells are `PosGermRel N`: two simples compose when their crossing lengths add.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- The germ presentation of `PosBraid n`; the ascription is the point, `PosBraid` being a `def`. -/
def germPresentation (n : ℕ) : Presents (monoidPoly (PosGermRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (PosGermRel n)

/-- The Artin presentation of `ArtinPosBraid n`. -/
def artinPresentation (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (ArtinPosBraid n))ᵒᵖ) :=
  presentedMonoidPresentation (ArtinRel n)

/-- **…read on the positive braids**, along Artin-from-Garside — the Artin spelling of the same
component, in the shape the lift consumes. -/
noncomputable def artinComponent (n : ℕ) :
    Presents (monoidPoly (ArtinRel n)) ((SingleObj (PosBraid n))ᵒᵖ) :=
  (artinPresentation n).transport ((MulEquiv.toSingleObjEquiv (posBraid_equiv_artinPos n)).op).symm

/-- **A presentation of every strand component is a presentation of the localized base.** -/
noncomputable def zLocOfComponents {P : ℕ → Polygraph}
    (p : ∀ N, Presents (P N) ((AtStrands N).FullSubcategory)) :
    Presents (Polygraph.coproduct P) (((W Zbp).op).Localization) :=
  (Presents.coproduct p).transport strandDecomposition.symm

/-- No arrow enters or leaves a strand component, so a word between two of its objects stays
inside — the one hypothesis `Presents.restrict` takes. -/
theorem convex_atStrands (N : ℕ) : (AtStrands N).Convex :=
  ObjectProperty.convex_of_absorbing fun hx f hy =>
    hx ((ObjectProperty.prop_iff_of_hom AtStrands exists_atStrands
      (fun hX hY g => atStrands_eq_of_hom hX hY g) f).mpr hy)

/-- **…and every presentation of the localized base restricts to one of each strand component** —
`Presents.restrict` at a strand component, read through `strandComponentGarside`. -/
noncomputable def zLocComponent {P : Polygraph} (p : Presents P (((W Zbp).op).Localization))
    (N : ℕ) : Presents (p.restrictPoly (AtStrands N)) ((SingleObj (PosBraid N))ᵒᵖ) :=
  (p.restrict (AtStrands N) (convex_atStrands N)).transport (strandComponentGarside N).symm

/-- **A monoid presentation of every braid monoid presents the localized base.**  A strand
component *is* the braid monoid on that many strands (`strandComponentGarside`), so presenting
`PosBraid N` as a monoid presents the component as a category, and the coproduct over the strand
counts is the whole of `Ch Zbp[W⁻¹]`.  This is the entry point the base has: the braid monoid is
the input, and everything downstream is a lift of it. -/
noncomputable def zLocOfBraidMonoids {S : ℕ → Type}
    (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)
    (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N) :
    Presents (Polygraph.coproduct fun N => monoidPoly (rels N)) (((W Zbp).op).Localization) :=
  zLocOfComponents fun N =>
    ((presentedMonoidPresentation (rels N)).transport
      (MulEquiv.toSingleObjEquiv (e N)).op).transport (strandComponentGarside N)

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose. -/
noncomputable def zLocPresentation :
    Presents (Polygraph.coproduct fun N => monoidPoly (PosGermRel N)) (((W Zbp).op).Localization) :=
  zLocOfBraidMonoids PosGermRel fun _ => MulEquiv.refl _

/-- **…and the Artin spelling**, on `N−1` generators with the commutation and braid relations: the
same entry point, handed Artin-from-Garside instead of the identity. -/
noncomputable def zLocArtinPresentation :
    Presents (Polygraph.coproduct fun N => monoidPoly (ArtinRel N)) (((W Zbp).op).Localization) :=
  zLocOfBraidMonoids ArtinRel fun N => (posBraid_equiv_artinPos N).symm

end ChainCat
