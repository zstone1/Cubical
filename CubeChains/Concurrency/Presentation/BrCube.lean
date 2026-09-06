import CubeChains.Concurrency.Presentation.SliceInherit
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Concurrency.Presentation.HAction

/-!
# Concurrency/Presentation/BrCube — `Br p` at the cube and at its decoration

`Br p K` presents `Ch(K)[W⁻¹]`, so wherever that category has already been identified the
presentation transports onto the identification: the weak Bruhat order at `□ⁿ`, the positive braid
action at `Hbp □ⁿ`.  The polygraph never moves — only the category it is read in.

The action reads *covariantly* here, where the fibration route (`hLocActionPresentation`) reads it
on the opposite; `presentsBrActionOp` is the shape a comparison of the two consumes.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **`Br p (□n)` presents the right weak Bruhat order on `Sₙ`, read backwards.** -/
noncomputable def presentsBrCube (n : ℕ) : Presents (p.Br (□n)) ((WeakOrder n)ᵒᵖ) :=
  (p.presentsBr (□n)).transport (locCubeWeakOrder n)

/-- **`Br p (Hbp □ⁿ)` presents the positive braid action on the orderings of the axes.** -/
noncomputable def presentsBrAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (PosBraidAction n) :=
  (p.presentsBr (Hbp.obj (□n))).transport (hLocEquiv n)

/-- …in the Artin spelling of the acting monoid. -/
noncomputable def presentsBrArtinAction (n : ℕ) :
    Presents (p.Br (Hbp.obj (□n))) (ActionCategory (ArtinPosBraid n) (Equiv.Perm (Fin n))) :=
  (p.presentsBr (Hbp.obj (□n))).transport (hLocArtinEquiv n)

/-- **…and reversed**, where the fibration route's `hLocActionPresentation` also lives: the glue
route's words compose the other way round, so only after `Presents.op` are the two comparable. -/
noncomputable def presentsBrActionOp (n : ℕ) :
    Presents ((p.Br (Hbp.obj (□n))).op) ((PosBraidAction n)ᵒᵖ) :=
  (p.presentsBrAction n).op

/-- **The loops at every 0-cell are the positive pure braids** — `PosPureBraid n` is the kernel of
`posPermHom n`, so the stabilizer of a chamber does not depend on the chamber.  The presentation
does *not* present that monoid: its own loops are only the identity
(`end_not_generated_by_simples`), so the pure braids are read off the presented category rather
than off the polygraph. -/
noncomputable def endBrAction (n : ℕ) (x : GenObj (p.Br (Hbp.obj (□n))).Gen) :
    @End (PosBraidAction n) _ ((p.presentsBrAction n).at' x) ≃* PosPureBraid n :=
  endEquivPosPure _

end BraidPresentation

end ChainCat
