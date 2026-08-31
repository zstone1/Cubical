import CubeChains.Concurrency.Presentation.LiftPresentation
import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Machinery.Localization.MonoidPresentation

/-!
# Testing/Axioms/AxiomCheckLP — axiom audit for the presentation transport
-/

open CategoryTheory CubeChains ChainCat

#print axioms CategoryTheory.elementsPresentation
#print axioms CategoryTheory.elementsQuotientEquiv
#print axioms CategoryTheory.gen_onElements
#print axioms CategoryTheory.gen_val
#print axioms CategoryTheory.quotientPullbackEquiv
#print axioms CategoryTheory.quotientEqEquiv
#print axioms CategoryTheory.totalToElements
#print axioms CategoryTheory.SingleObj.presentedMonoidPresentation
#print axioms CubeChains.boundaries_injective
#print axioms ChainCat.nonempty_hom_iff
#print axioms ChainCat.exists_factor
#print axioms ChainCat.exists_factor_first
#print axioms ChainCat.exists_swap
#print axioms ChainCat.Cut.exists_min_first
#print axioms ChainCat.zPresentationOp
#print axioms ChainCat.chPresentation
#print axioms ChainCat.chCutPresentation
#print axioms ChainCat.chLocPresentation
#print axioms ChainCat.invertsMerges_iff_bijective_mergeHom
#print axioms ChainCat.isSegal_iff_invertsMerges_repoint
#print axioms CubeChains.isSegal_Z
#print axioms ChainCat.endEquivStabilizer
#print axioms ChainCat.eq_id_of_val_eq_posPerm
#print axioms ChainCat.exists_end_ne_id
#print axioms ChainCat.end_not_generated_by_simples
#print axioms ChainCat.toElementsN
#print axioms ChainCat.isLocalization_chDescentN
