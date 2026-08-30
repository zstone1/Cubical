import CubeChains.Concurrency.Presentation.GarsideChains
import CubeChains.Concurrency.Salvetti.CrossCompare
import CubeChains.Concurrency.Merge.MergeGenerate

/-!
# Testing/Axioms/AxCross — axiom footprint of the crossing permutation

Nothing imports `Testing/`; this only reports which axioms the braid grading and the two readings
of a chain morphism's permutation rest on.
-/

#print axioms CubeChains.Graded.Germ.hom_comp
#print axioms ChainCat.crossPerm
#print axioms ChainCat.crossPerm_comp
#print axioms ChainCat.crossPerm_noDoubleCross
#print axioms ChainCat.permLen_crossPerm_comp
#print axioms ChainCat.crossPerm_chConcat
#print axioms ChainCat.chBraid
#print axioms ChainCat.chBraid_faithful
#print axioms ChainCat.hom_ext_of_crossPerm
#print axioms ChainCat.W_iff_crossPerm_eq_one
#print axioms ChainCat.W_iff_monotone
#print axioms ChainCat.merge_iff
#print axioms ChainCat.W_eq_inverseImage_toChZ
#print axioms ChainCat.merge_iff_of_codim_one
#print axioms ChainCat.crossPerm_atomHom
#print axioms ChainCat.not_W_atomHom
#print axioms ChainCat.W_isInvertedBy_chGerm
#print axioms ChainCat.exists_crossPerm_eq
#print axioms ChainCat.exists_crossPerm_eq_one
#print axioms ChainCat.exists_crossPerm_mid
#print axioms ChainCat.exists_crossPerm_blocks
#print axioms ChainCat.exists_atom_pair
#print axioms ChainCat.crossPermN
#print axioms ChainCat.simpleEquivPerm
#print axioms ChainCat.locEquivPosBraid
#print axioms CubeChains.crossPerm_eq_topeCross
#print axioms CubeChains.W_wallLegFlip
