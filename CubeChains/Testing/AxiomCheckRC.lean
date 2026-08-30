import CubeChains.Salvetti.RunClassifier

/-!
# Testing/AxiomCheckRC — axiom check for `Salvetti/RunClassifier`

Nothing imports `Testing/`; this only reports the axiom footprint of the run-classifier results.
-/

#print axioms CubeChains.not_invertsMerges_runBp
#print axioms CubeChains.not_invertsMerges_Hbp_Zbp
#print axioms CubeChains.HbpZIsoRun
#print axioms CubeChains.twistRun_merge21_ne
#print axioms CubeChains.exists_merge_twistRun_ne
#print axioms CubeChains.not_runOf_natural
#print axioms CubeChains.not_desym_natural
#print axioms CubeChains.not_invertsMerges_of_splitting
#print axioms CubeChains.isEmpty_splitting_of_invertsMerges_cube_two
#print axioms CubeChains.forgetLabels_comp_forgetRun
#print axioms CubeChains.onesHomEquivRunClassifier
#print axioms CubeChains.simplesEquivCells
#print axioms CubeChains.exists_Winf_from_onesH
#print axioms CubeChains.costarOnesH
#print axioms CategoryTheory.Costar.locIso
#print axioms CategoryTheory.Costar.nonempty_locIso
#print axioms CubeChains.runHbpEquiv
#print axioms CubeChains.runHbpCubeEquivPerm
#print axioms CubeChains.run_HbpZbp_eq
#print axioms CubeChains.eq_of_hom_to_runs
#print axioms CubeChains.not_exists_hom_to_all_cube
#print axioms CubeChains.isEmpty_costar_cube
