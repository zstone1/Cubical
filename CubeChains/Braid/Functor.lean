import CubeChains.Braid.Germ
import CubeChains.Braid.Crossing
import CubeChains.Braid.Frame

/-!
# Braid/Functor — functoriality of the braid grading

The one lemma that makes `braidGrading` (`Braid/Grading`) a functor: **composable refinements never
cross the same pair of events twice**, so the inversion counts of their event permutations add
(`permLen_evPerm_comp`).  This is the germ relation `[σ][τ] = [στ]`, and it comes from the chain/line
semantics alone — the crossing criterion (`evKey_lt_iff_of_not_split`, `Braid/Crossing`) plus length
additivity (`permLen_mul_of_noDoubleCross`, `Braid/Germ`).  No `writhe`, no Salvetti cell.
-/

namespace CubeChains

open CategoryTheory Equiv

variable {K : BPSet} {n : ℕ}

/-- **No pair of events is crossed twice.**  Pull two events to the finest chain `z`.  If they keep
their `z`-order (`hij`) but flip in `y` (`hflip`, so `g` crosses them), the crossing criterion for
`g` forces them into *different* `y`-beads; the criterion for `f` — whose split needs the *same*
`y`-bead — then keeps the `x`-order equal to the `y`-order.  So `f` cannot cross a pair `g` already
crossed. -/
theorem evPerm_noDoubleCross {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z)
    (i j : Fin n) (hij : i < j) (hflip : (evPerm g)⁻¹ j < (evPerm g)⁻¹ i) :
    (evPerm f)⁻¹ ((evPerm g)⁻¹ j) < (evPerm f)⁻¹ ((evPerm g)⁻¹ i) := by
  -- the two events, viewed in the finest chain `z` and its images in `y`
  set ci : EventObj z.obj.chain := (evIdx z).symm i with hci
  set cj : EventObj z.obj.chain := (evIdx z).symm j with hcj
  -- `hij`, `hflip` as `evKey` inequalities
  have hzlt : evKey z.obj.line ci < evKey z.obj.line cj := by
    rw [← evIdx_lt_iff]; rw [hci, hcj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hij
  have hylt : evKey y.obj.line (eventMap (concRefine g) cj)
      < evKey y.obj.line (eventMap (concRefine g) ci) := by
    rw [← evIdx_lt_iff, ← evPerm_inv_apply g j, ← evPerm_inv_apply g i]; exact hflip
  -- STEP A: the flip forces the two events into the same coarse (`y`-) bead
  have hbead : (eventMap (concRefine g) ci).1 = (eventMap (concRefine g) cj).1 := by
    by_contra hcoarse
    have hcrit := evKey_lt_iff_of_not_split g.hom ci cj (Or.inr hcoarse)
    exact absurd (hcrit.mp hzlt) (asymm hylt)
  -- STEP B: same `y`-bead ⇒ the `x`-order follows the `y`-order
  have key := (evKey_lt_iff_of_not_split f.hom (eventMap (concRefine g) cj)
    (eventMap (concRefine g) ci) (Or.inl hbead.symm)).mp hylt
  -- reassemble into the `evPerm` inequality
  rw [evPerm_inv_apply g i, evPerm_inv_apply g j, evPerm_inv_apply f, evPerm_inv_apply f,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, evIdx_lt_iff, ← hci, ← hcj]
  exact key

/-- **Composable refinements never cross the same pair of events twice**: inversion counts add.
Straight from the crossing criterion (`evPerm_noDoubleCross`) via the germ additivity law — no
`writhe`, no Salvetti cell.  This is precisely the germ relation `[σ][τ] = [στ]`. -/
theorem permLen_evPerm_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (evPerm g * evPerm f) = permLen (evPerm g) + permLen (evPerm f) := by
  have h : permLen ((evPerm f)⁻¹ * (evPerm g)⁻¹)
      = permLen (evPerm g)⁻¹ + permLen (evPerm f)⁻¹ :=
    permLen_mul_of_noDoubleCross (evPerm_noDoubleCross f g)
  rwa [← mul_inv_rev, permLen_inv, permLen_inv, permLen_inv] at h

end CubeChains
