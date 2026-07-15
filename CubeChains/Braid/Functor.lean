import CubeChains.Braid.Category
import CubeChains.Braid.Crossing
import CubeChains.Braid.Frame

/-!
# Braid/Functor — the braid of an execution

An execution refines into another by reordering its events; the braid of that refinement is the
**simple** braid of its event permutation.  There is no choice here and nothing to lift: in the germ
presentation `ofPerm (evPerm f)` *is* a generator.

Functoriality is the germ relation, and it comes from the chain/line semantics alone: the crossing
criterion (`evKey_lt_iff_of_not_split`) shows **composable refinements never cross the same pair of
events twice**, so inversion counts add (`permLen_mul_of_noDoubleCross`).

    Ψ : ConcCatN K n ⥤ BraidFib n      f ↦ ofPerm (evPerm f)
    Φ = FreeGroupoid.lift Ψ            2-cells ↦ honest braids
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

/-- **The braid of a refinement**: the simple braid of its event permutation. -/
noncomputable def braidPsiGerm (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ BraidFib n where
  obj _ := SingleObj.star _
  map {_ _} f := ofPerm (evPerm f)
  map_id x := by
    change ofPerm (evPerm (𝟙 x)) = (1 : Braid n)
    rw [evPerm_id]
    exact ofPerm_one
  map_comp {_ _ _} f g := by
    rw [SingleObj.comp_as_mul]
    change ofPerm (evPerm (f ≫ g)) = ofPerm (evPerm g) * ofPerm (evPerm f)
    rw [evPerm_comp, ofPerm_mul (permLen_evPerm_comp f g)]

/-- **The braid functor**: every 2-cell of the concurrency groupoid is an honest braid.
`FreeGroupoid.lift` — no presentation theorem, no Salvetti. -/
noncomputable def braidPhi (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ BraidFib n :=
  FreeGroupoid.lift (braidPsiGerm K n)

/-- Read into the braid category, where the strand count is visible. -/
noncomputable def braidPhiCat (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ Braids :=
  braidPhi K n ⋙ braidIncl n

@[simp] theorem braidPhi_homMk {x y : ConcCatN K n} (f : x ⟶ y) :
    (braidPhi K n).map (FreeGroupoid.homMk f) = ofPerm (evPerm f) :=
  FreeGroupoid.lift_map_homMk _ f

/-- **`Φ` lifts the event monodromy**: its `Sₙ`-shadow is exactly `evPerm`. -/
@[simp] theorem permHom_braidPhi {x y : ConcCatN K n} (f : x ⟶ y) :
    permHom n ((braidPhi K n).map (FreeGroupoid.homMk f)) = evPerm f := by
  rw [braidPhi_homMk, permHom_ofPerm]

end CubeChains
