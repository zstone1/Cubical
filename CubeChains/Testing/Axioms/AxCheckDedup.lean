import CubeChains.Concurrency.Presentation.ArtinRelations
import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Concurrency.Complexification.RunClassifier

/-!
# Testing/Axioms/AxCheckDedup — axiom footprint of the strand component and its interval

Nothing imports `Testing/`; this only reports which axioms the component's two ends and the
Garside presentation rest on.
-/

#print axioms CategoryTheory.IsWideInitial.locIso
#print axioms CategoryTheory.IsWideInitial.nonempty_locIso
#print axioms CategoryTheory.CategoryOfElements.endOpEquivStabilizer
#print axioms ChainCat.wideInitialOfExistsMerge
#print axioms ChainCat.onesWideInitial
#print axioms ChainCat.topWideTerminal
#print axioms ChainCat.endEquivWStrands
#print axioms ChainCat.endEquivPosBraid
#print axioms ChainCat.endEquivArtinPos
#print axioms ChainCat.locEquivPosBraid
#print axioms ChainCat.locOf_mul_of_mul_eq_rev
#print axioms ChainCat.locOf_mul_rightComplement
#print axioms ChainCat.locOf_leftComplement_mul
#print axioms CubeChains.isSegal_Z
#print axioms CubeChains.wedge2HomEquiv
#print axioms CubeChains.wedgeCubeHomEquiv
#print axioms CubeChains.isSegal_iff_existsUnique
#print axioms CubeChains.onesHWideInitial
