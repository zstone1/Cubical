import CubeChains.Chains.ArtinRelations
import CubeChains.Chains.SegalCondition
import CubeChains.Salvetti.RunClassifier

/-!
# Testing/AxCheckDedup — axiom footprint of the strand component and its interval

Nothing imports `Testing/`; this only reports which axioms the component's star, its costars and
the Garside presentation rest on.
-/

#print axioms CategoryTheory.Costar.locIso
#print axioms CategoryTheory.Costar.nonempty_locIso
#print axioms CategoryTheory.CategoryOfElements.endOpEquivStabilizer
#print axioms ChainCat.costarOfExistsMerge
#print axioms ChainCat.costarOnes
#print axioms ChainCat.starZ
#print axioms ChainCat.endEquivWinfN
#print axioms ChainCat.endEquivPosBraid
#print axioms ChainCat.endEquivArtinPos
#print axioms ChainCat.garOf_mul_of_mul_eq_rev
#print axioms ChainCat.garOf_mul_rightComplement
#print axioms ChainCat.garOf_leftComplement_mul
#print axioms CubeChains.isSegal_Z
#print axioms CubeChains.wedge2HomEquiv
#print axioms CubeChains.wedgeCubeHomEquiv
#print axioms CubeChains.isSegal_iff_existsUnique
#print axioms CubeChains.costarOnesH
