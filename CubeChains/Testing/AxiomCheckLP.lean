import CubeChains.Chains.LiftPresentation

/-!
# Testing/AxiomCheckLP — axiom audit for the presentation transport

The `#check` pins the transport at a `K` that provably inverts the merges: the presenting quiver
and the localized category must land in the same universe for the equivalence to exist at all.
-/

open CategoryTheory CubeChains ChainCat

#print axioms CategoryTheory.elementsPresentation
#print axioms CategoryTheory.elementsQuotientEquiv
#print axioms CategoryTheory.gen_onElements
#print axioms CategoryTheory.gen_val
#print axioms CategoryTheory.quotientPullbackEquiv
#print axioms CategoryTheory.totalToElements
#print axioms CategoryTheory.SingleObj.presentedMonoidPresentation
#print axioms CategoryTheory.Sigma.pathsEquiv
#print axioms CategoryTheory.Sigma.quotientEquiv
#print axioms CategoryTheory.Sigma.opEquiv
#print axioms CategoryTheory.Sigma.presentation
#print axioms CutGraded.presentation
#print axioms CubeChains.Graded.sigmaEquivalence
#print axioms CubeChains.germPresentation
#print axioms CubeChains.heights_injective
#print axioms ChainCat.nonempty_hom_iff
#print axioms ChainCat.existsUnique_factorisation
#print axioms ChainCat.existsUnique_factor_last
#print axioms ChainCat.existsUnique_factor_first
#print axioms ChainCat.zPresentation
#print axioms ChainCat.zPresentationOp
#print axioms ChainCat.locGermPresentation
#print axioms ChainCat.chPresentation
#print axioms ChainCat.chCutPresentation
#print axioms ChainCat.chLocPresentation
#print axioms ChainCat.chLocGermPresentation
#print axioms ChainCat.invertsMerges_iff_uniqueComposites
#print axioms ChainCat.invertsMerges_Zbp
#print axioms ChainCat.endEquivStabilizer
#print axioms ChainCat.eq_id_of_val_eq_posPerm
#print axioms ChainCat.exists_end_ne_id
#print axioms ChainCat.end_not_generated_by_simples

#check (chLocGermPresentation Zbp invertsMerges_Zbp :
  (Winf Zbp).Localization ≌
    (Quotient (totalRel germRel
      (locGermPresentation.functor ⋙ wedgeHomsDescend Zbp invertsMerges_Zbp)))ᵒᵖ)
