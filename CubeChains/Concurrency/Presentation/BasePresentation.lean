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

/-! ### The cells, read at the run

A 0-cell is a strand count and a 1-cell a letter there, and both are the run's: the decomposition
is inverted by `Sigma.desc` and the component by `runBaseAt`, so the two `transport`s cancel on the
nose and only `coproduct_arrow` is needed. -/

section Cells

variable {S : ℕ → Type} (rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop)

/-- The 0-cell of the base polygraph at strand count `N`. -/
def braidBasePt (N : ℕ) : GenObj (Polygraph.coproduct fun M => monoidPoly (rels M)).Gen :=
  (Polygraph.coproduct fun M => monoidPoly (rels M)).pt
    ⟨N, SingleObj.star (PresentedMonoid (rels N))⟩

/-- …and a letter there, as a 1-cell. -/
def braidBaseGen (N : ℕ) (s : S N) : braidBasePt rels N ⟶ braidBasePt rels N :=
  Polygraph.CoproductGen.mk (MonoidPoly.edge (rels := rels N) s)

variable (e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N)

/-- The braid a letter names. -/
def letterBraid {N : ℕ} (s : S N) : PosBraid N :=
  e N (PresentedMonoid.mk (rels N) (FreeMonoid.of s))

/-- **The 0-cell at strand count `N` names the run.** -/
theorem zLocOfBraidMonoids_at' (N : ℕ) :
    (zLocOfBraidMonoids rels e).at' (braidBasePt rels N)
      = (runBase N).obj (op (SingleObj.star (PosBraid N))) := rfl

/-- **A letter names the loop at the run its braid is.** -/
theorem zLocOfBraidMonoids_arrow (N : ℕ) (s : S N) :
    (zLocOfBraidMonoids rels e).arrow (braidBaseGen rels N s)
      = (runBase N).map (posArrow N (letterBraid rels e s)) :=
  congrArg (ObjectProperty.sigmaι AtStrands).map
    (Presents.coproduct_arrow
      (fun M => ((presentedMonoidPresentation (rels M)).transport
          (MulEquiv.toSingleObjEquiv (e M)).op).transport (strandComponentGarside M))
      N (MonoidPoly.edge (rels := rels N) s))

end Cells

/-! ## The input, bundled

Everything downstream consumes exactly this: generators, relations, and the identification of the
presented monoid with `PosBraid N`. -/

/-- **A presentation of the braid monoids, one per strand count.** -/
structure BraidPresentation where
  /-- the generators -/
  S : ℕ → Type
  /-- the relations they satisfy -/
  rels : ∀ N, FreeMonoid (S N) → FreeMonoid (S N) → Prop
  /-- …presenting the positive braid monoid -/
  e : ∀ N, PresentedMonoid (rels N) ≃* PosBraid N

namespace BraidPresentation

variable (p : BraidPresentation)

/-- One copy of the monoid's polygraph per strand count. -/
def poly : Polygraph.{0, 0, 0} := Polygraph.coproduct fun N => monoidPoly (p.rels N)

/-- **…presenting `Ch Zbp[W⁻¹]`.** -/
noncomputable def base : Presents p.poly (((W Zbp).op).Localization) :=
  zLocOfBraidMonoids p.rels p.e

/-- The 0-cell at strand count `N`. -/
def pt (N : ℕ) : GenObj p.poly.Gen := braidBasePt p.rels N

/-- A letter, as a 1-cell. -/
def gen {N : ℕ} (s : p.S N) : p.pt N ⟶ p.pt N := braidBaseGen p.rels N s

/-- The braid a letter names. -/
def braid {N : ℕ} (s : p.S N) : PosBraid N := letterBraid p.rels p.e s

/-- …and its permutation. -/
def perm {N : ℕ} (s : p.S N) : Equiv.Perm (Fin N) := posPermHom N (p.braid s)

/-- **Each letter names a simple.**  Not automatic, and the lift needs it: the braid monoid acts on
the runs by length-additive multiplication, so a letter of greater length than its permutation acts
nowhere and names no 1-cell above the base. -/
def BySimples : Prop := ∀ (N : ℕ) (s : p.S N), p.braid s = posPerm (p.perm s)

theorem base_arrow {N : ℕ} (s : p.S N) :
    p.base.arrow (p.gen s) = (runBase N).map (posArrow N (p.braid s)) :=
  zLocOfBraidMonoids_arrow p.rels p.e N s

/-- **A simple letter names the loop its permutation spells.** -/
theorem base_arrow_of_simple (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    p.base.arrow (p.gen s) = runLoop N (p.perm s) :=
  (p.base_arrow s).trans (congrArg (fun β => (runBase N).map (posArrow N β)) (hp N s))

end BraidPresentation

/-- **`Ch Zbp[W⁻¹]`, presented**: one copy of the Garside germ per strand count — `PosBraid N` is
the presented monoid of `PosGermRel N` on the nose. -/
def germBP : BraidPresentation where
  S := fun N => Equiv.Perm (Fin N)
  rels := PosGermRel
  e := fun _ => MulEquiv.refl _

/-- **…and the Artin spelling**, on `N−1` generators with the commutation and braid relations: the
same input, handed Artin-from-Garside instead of the identity. -/
noncomputable def artinBP : BraidPresentation where
  S := fun N => Fin (N - 1)
  rels := ArtinRel
  e := fun N => (posBraid_equiv_artinPos N).symm

/-- **A germ letter is its own simple.** -/
@[simp] theorem germBP_braid {N : ℕ} (σ : Equiv.Perm (Fin N)) : germBP.braid σ = posPerm σ := rfl

theorem germBP_bySimples : germBP.BySimples := fun _ _ => rfl

/-- **An Artin letter is the simple of its adjacent transposition** — `posOfArtinPos` is the
inverse's underlying map, and it sends a generator to its atom on the nose. -/
@[simp] theorem artinBP_braid {N : ℕ} (k : Fin (N - 1)) : artinBP.braid k = posPerm (adjT k) := rfl

@[simp] theorem artinBP_perm {N : ℕ} (k : Fin (N - 1)) : artinBP.perm k = adjT k := by
  rw [BraidPresentation.perm, artinBP_braid, posPermHom_posPerm]

theorem artinBP_bySimples : artinBP.BySimples := fun _ k => by rw [artinBP_braid, artinBP_perm]

/-- **The `k`-th Artin generator is the `k`-th atom.** -/
theorem artinBase_arrow_atom (N : ℕ) (k : Fin (N - 1)) :
    artinBP.base.arrow (artinBP.gen k) = atomLoop N k :=
  (artinBP.base_arrow_of_simple artinBP_bySimples k).trans (by rw [artinBP_perm, runLoop_adjT])

end ChainCat
