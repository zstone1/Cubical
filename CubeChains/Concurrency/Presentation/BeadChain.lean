import CubeChains.Machinery.Presentation.CoherentColimit
import CubeChains.Concurrency.Presentation.BeadProduct
import CubeChains.Concurrency.Presentation.SliceInherit

/-!
# Concurrency/Presentation/BeadChain — the naming a bead family owes

A colimit of polygraphs is a colimit of **cells**, so a 0-cell of `colimit (elementsPoly X P)` names
one object of the target on the nose: any presentation of it induces a strictly natural naming
(`Polygraph.Presents.colimNaming_natural`).  Thinness of the localized slices buys the *morphism*
half of `hP` and nothing else, so a family reaching the slice through `Localization.uniq` — which
names objects by `objPreimage` — is not helped by weakening `hP` to an isomorphism; it must supply
the naming.

`weakNaming` is the cheap way to supply one here: `weakOverLoc` is an explicit fully faithful
functor to the weak order, so an equality of *weak-order classes* is already an isomorphism of
slice objects (`locOverIsoOfWeak`), and the obligation becomes a computation rather than a
comparison of opaque objects.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Equiv

namespace ChainCat

/-! ## Isomorphy in a localized slice is an equality of weak-order classes -/

/-- **The weak-order class decides isomorphy in a localized slice** — `weakOverLoc` is fully
faithful, so `preimageIso` reads an equality of classes downstairs. -/
noncomputable def locOverIsoOfWeak {d : Ch Zbp}
    {Y Z : ((W Zbp).over (X := d)).Localization}
    (h : (weakOverLoc (d := d) rfl).obj Y = (weakOverLoc (d := d) rfl).obj Z) : Y ≅ Z :=
  (weakOverLoc (d := d) rfl).preimageIso (eqToIso h)

variable {P : Ch Zbp ⥤ Polygraph.{0, 0, 0}}

/-- **A naming of the slices by weak-order classes.**  The 0-cell's own slice object stays opaque:
only its class is compared, and the push-forward is asked on the nose. -/
noncomputable def weakNaming
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (obj : ∀ d : Ch Zbp, (P.obj d).presented → ((W Zbp).over (X := d)).Localization)
    (hw : ∀ (d : Ch Zbp) (a : (P.obj d).presented),
      (weakOverLoc (d := d) rfl).obj ((p d).E.obj a)
        = (weakOverLoc (d := d) rfl).obj (obj d a))
    (push : ∀ {d' d : Ch Zbp} (f : d' ⟶ d) (a : (P.obj d').presented),
      obj d ((P.map f).functor.obj a) = (overMapLoc (W Zbp) f).obj (obj d' a)) :
    Polygraph.Naming (W Zbp) p :=
  Polygraph.Naming.ofFullyFaithful (fun d => weakOverLoc (d := d) rfl) obj hw
    fun {_ _} f a => push f a

/-- **`Ch(K)[W⁻¹]` is presented by the colimit of the slice presentations, given a naming** — the
entry point `hP` is traded for.  The polygraph is the same one `presentsChainsColimit` presents. -/
noncomputable def presentsChainsColimitOfNaming (K : BPSet)
    (p : ∀ d : Ch Zbp, Presents (P.obj d) (((W Zbp).over (X := d)).Localization))
    (ν : Polygraph.Naming (W Zbp) p) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) P)) ((W K).Localization) :=
  (ν.presentsColimit (wedgeHoms K)).transport (locEquivElements K).symm

/-! ## What the bead family still owes

`wedgePoly` is defined on a *dimension list*, not on `Ch Zbp`: an arrow of `Ch Zbp` merges beads,
so the map on 0-cells is `crossPerm` times a block sum and the map on 1-cells needs a generator of
one bead read at the block it merges into — `BraidPresentation.Blocks`.  That datum is prior to any
presentation and is untouched by how `hP` is stated. -/

/-- **The germ presentation has the block datum**: a simple of a block is a simple of the sum, and
`germBP_perm` reads it back. -/
noncomputable def germBlocks : germBP.Blocks where
  left a b s := permSum a b (s, 1)
  left_braid a b s := congrArg (fun σ => posPerm (permSum a b (σ, 1))) (germBP_perm s).symm
  right a b s := permSum a b (1, s)
  right_braid a b s := congrArg (fun σ => posPerm (permSum a b (1, σ))) (germBP_perm s).symm

/-! ## The shapes the bead split does not reach

The proved surplus of `Br germBP (Hbp □³)` (`straightCell_ne_crossedCell`) is a pair of 1-cells in
the copies over `zObj (topDims 3)`; `topDims` is the **one-bead** shape, where `wedgePoly` splits
nothing.  So the cell count a bead product saves — `|S a| + |S b|` for `|S a| · |S b|` — is saved at
multi-bead shapes only, and leaves that surplus where it is. -/

/-- **At a one-bead shape the bead product is the one bead**, beside the empty tail. -/
theorem wedgePoly_topDims (p : BraidPresentation) (n : ℕ) :
    wedgePoly p (topDims (n + 1)) = Polygraph.prod (beadPoly p (n + 1)) (beadPoly p 0) := rfl

end ChainCat
