import CubeChains.Braid.CubeLegOne

open CategoryTheory OrderQuotient Quiver CubeChain Opposite StdCube

namespace CubeChains

variable {n : ℕ}

theorem nones_commute_propagate {ya ya' yb yb' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcova : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i))
    (hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i))
    (hlea : braidSign (covectorHeight ya) ⊑ braidSign (covectorHeight yb))
    (hlea' : braidSign (covectorHeight ya') ⊑ braidSign (covectorHeight yb'))
    (hnc_a : ∀ (J : Fin ya.cubes.length) (J' : Fin ya'.cubes.length) (hJ : J'.val = J.val)
        (c : Fin ((ya.cubes.get J).1 : ℕ)),
        nones (toStar (ya'.cubes.get J').2) (Fin.cast (beadDim_reindex σ hcova J J' hJ).symm c)
          = σ (nones (toStar (ya.cubes.get J).2) c))
    (j : Fin yb.cubes.length) (j' : Fin yb'.cubes.length) (hj : j'.val = j.val)
    (t : Fin ((yb.cubes.get j).1 : ℕ)) :
    nones (toStar (yb'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcovb j j' hj).symm t)
      = σ (nones (toStar (yb.cubes.get j).2) t) := by
  classical
  set r : Fin ya.cubes.length := blockIndex ya (blockRep yb j) with hr
  set r' : Fin ya'.cubes.length := blockIndex ya' (blockRep yb' j') with hr'
  have hrr : r'.val = r.val :=
    chainRefineOfFaceLE_refinement_reindex σ hcova hcovb hlea j' j hj
  have hsub : ∀ p, blockIndex yb p = j → blockIndex ya p = r := by
    intro p hp
    exact faceLE_eq_of_eq hlea p (blockRep yb j) (by rw [hp, blockIndex_blockRep])
  have hlt : ∀ p, blockIndex ya p ≠ r → (blockIndex yb p < j ↔ blockIndex ya p < r) := by
    intro p hne
    refine ⟨fun hpj => ?_, fun hpj => ?_⟩
    · exact lt_of_le_of_ne (faceLE_le_of_lt hlea p (blockRep yb j)
        (by rw [blockIndex_blockRep]; exact hpj)) hne
    · by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea (blockRep yb j) p
          (by rw [blockIndex_blockRep]; exact hgt)))
  have hsub' : ∀ p, blockIndex yb' p = j' → blockIndex ya' p = r' := by
    intro p hp
    exact faceLE_eq_of_eq hlea' p (blockRep yb' j') (by rw [hp, blockIndex_blockRep])
  have hlt' : ∀ p, blockIndex ya' p ≠ r' → (blockIndex yb' p < j' ↔ blockIndex ya' p < r') := by
    intro p hne
    refine ⟨fun hpj => ?_, fun hpj => ?_⟩
    · exact lt_of_le_of_ne (faceLE_le_of_lt hlea' p (blockRep yb' j')
        (by rw [blockIndex_blockRep]; exact hpj)) hne
    · by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub' p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea' (blockRep yb' j') p
          (by rw [blockIndex_blockRep]; exact hgt)))
  set hdj : ((yb'.cubes.get j').1 : ℕ) = ((yb.cubes.get j).1 : ℕ) :=
    beadDim_reindex σ hcovb j j' hj with hdjdef
  set hdr : ((ya'.cubes.get r').1 : ℕ) = ((ya.cubes.get r).1 : ℕ) :=
    beadDim_reindex σ hcova r r' hrr with hdrdef
  have hincl_j : nones (toStar (yb.cubes.get j).2) t
      = nones (toStar (ya.cubes.get r).2) (faceEmb (inclData ya yb j r hsub hlt).1 t) :=
    nones_incl (chainRefineOfFaceLE ya yb hlea) j t
  have hincl_j' : nones (toStar (yb'.cubes.get j').2) (Fin.cast hdj.symm t)
      = nones (toStar (ya'.cubes.get r').2)
          (faceEmb (inclData ya' yb' j' r' hsub' hlt').1 (Fin.cast hdj.symm t)) :=
    nones_incl (chainRefineOfFaceLE ya' yb' hlea') j' (Fin.cast hdj.symm t)
  have hbox := incl_reindex σ hsub hlt hsub' hlt' hdr hdj
    (fun c => hnc_a r r' hrr c) (fun p => toStar_get_reindex σ hcovb j j' hj p)
  have hcast : (Fin.cast hdj (Fin.cast hdj.symm t) : Fin ((yb.cubes.get j).1 : ℕ)) = t := by
    apply Fin.ext; simp
  have hface : faceEmb (inclData ya' yb' j' r' hsub' hlt').1 (Fin.cast hdj.symm t)
      = Fin.cast hdr.symm (faceEmb (inclData ya yb j r hsub hlt).1 t) := by
    rw [hbox, faceEmb_comp, faceEmb_comp, faceEmb_eqToHom, faceEmb_eqToHom, hcast]
  rw [hincl_j', hface, hnc_a r r' hrr (faceEmb (inclData ya yb j r hsub hlt).1 t), ← hincl_j]

end CubeChains
