import CubeChains.Concurrency.Complexification.HPresentation
open CubeChains ChainCat CategoryTheory Equiv
#print axioms CubeChains.BraidPresentation.equiv
#print axioms CubeChains.BraidPresentation.map_gen
#print axioms CubeChains.BraidPresentation.val_gen
#print axioms CubeChains.germPresentation
#print axioms CubeChains.artinPresentation
#print axioms CubeChains.artin_comm
#print axioms CubeChains.artin_braid
#print axioms CategoryTheory.Sigma.wordPathRel_iff
#print axioms CategoryTheory.Sigma.totalRel_word_iff
#print axioms CategoryTheory.Sigma.totalEdgeEquiv
#print axioms CubeChains.BraidPresentation.chLocEquiv
#print axioms CubeChains.BraidPresentation.fibreEquiv
#print axioms CubeChains.BraidPresentation.hbpEquiv
#print axioms CubeChains.BraidPresentation.posBraidActionEquiv
#print axioms CubeChains.BraidPresentation.hbpChamberEquiv
#print axioms CubeChains.hbpSimpleEdgeEquiv
#print axioms CubeChains.wallCrossLoc

/-! The read-off stays definitional at both instances — the generic `map_gen` transports along
`monoidEquiv_gen`, which is `rfl` for each. -/

example (m : ℕ) (σ : Perm (Fin m)) :
    germPresentation.equiv.functor.map
        ((Quotient.functor germPresentation.pathRel).map (Sigma.wordPath (FreeMonoid.of σ)))
      = Quiver.Hom.op (Graded.ofVal (posPerm σ)) := rfl

example (m : ℕ) (i : Fin (m - 1)) :
    artinPresentation.equiv.functor.map
        ((Quotient.functor artinPresentation.pathRel).map (Sigma.wordPath (FreeMonoid.of i)))
      = Quiver.Hom.op (Graded.ofVal (posPerm (adjT i))) := rfl
