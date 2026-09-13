import CubeChains.Concurrency.Grading.TopBead

/-!
# Concurrency/Merge/CubeCrossing — how much a chain of the cube has braided

A chain of `□n` refines the one-bead chain `cubeTop n` in exactly one way, and the crossing
permutation of that refinement is an invariant, `cross`.  `flatten` is the firing order —
coordinate ↦ step — so `cross` is the **word**, step ↦ coordinate; the two are inverse because a
refinement factors the crossing permutation on the right and the firing order on the left.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## The crossing number of a chain of the cube -/

/-- **Every chain of `□n` has `n` events** — a wedge map cannot change the event count. -/
theorem dimSum_dims_cube (c : Ch (□n)) : dimSum c.dims = n := wedgeDimSum_eq c.map

/-- `□n` as a single bead — the terminal chain. -/
def cubeTop (n : ℕ) : Ch (□n) := ⟨topDims n, (topWedgeIso n).hom⟩

/-- Every chain of `□n` refines the one-bead chain, in exactly one way. -/
def toCubeTop (c : Ch (□n)) : c ⟶ cubeTop n :=
  ⟨c.map ≫ (topWedgeIso n).inv, by
    change (c.map ≫ (topWedgeIso n).inv) ≫ (topWedgeIso n).hom = c.map
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

/-- **How much a chain of `□n` has braided**: the crossing permutation of its refinement of the
one-bead chain. -/
noncomputable def cross (c : Ch (□n)) : Equiv.Perm (Fin n) :=
  crossPerm (dimSum_dims_cube c) (toCubeTop c)

/-- The one-bead chain fires in the cube's own order. -/
@[simp] theorem flatten_cubeTop (n : ℕ) : flatten (cubeTop n) = 1 := by
  have hbead : ∀ x y : Fin n, beadOf (cubeTop n) x = beadOf (cubeTop n) y := fun x y =>
    Fin.ext (by
      have hlen : (cubeTop n).dims.length ≤ 1 := length_topDims n
      have hx := (beadOf (cubeTop n) x).isLt
      have hy := (beadOf (cubeTop n) y).isLt
      omega)
  refine Equiv.ext fun q => ?_
  simpa using flatten_apply (cubeTop n) 1 (fun x y hxy => Or.inr ⟨hbead _ _, hxy⟩) q

/-- **The crossing permutation of a chain is its firing order, inverted.**  Its refinement of the
one-bead chain takes the chain's order to the cube's, and `crossPerm` compares the two chains. -/
theorem cross_eq_flatten_inv (c : Ch (□n)) : cross c = (flatten c)⁻¹ := by
  have hc : (⟨c.dims, Hom.φ (toCubeTop c) ≫ (cubeTop n).map⟩ : Ch (□n)) = c := by
    obtain ⟨d, x⟩ := c
    change (⟨d, (x ≫ (topWedgeIso n).inv) ≫ (topWedgeIso n).hom⟩ : Ch (□n)) = ⟨d, x⟩
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htop : ∀ q : Fin n,
      flatten (⟨(cubeTop n).dims, (cubeTop n).map⟩ : Ch (□n)) q = q := fun q => by
    rw [show (⟨(cubeTop n).dims, (cubeTop n).map⟩ : Ch (□n)) = cubeTop n from rfl, flatten_cubeTop]
    rfl
  refine Equiv.ext fun y => ?_
  obtain ⟨q, rfl⟩ := (flatten c).surjective y
  have h := crossPerm_flatten (dimSum_dims_cube c) (toCubeTop c) (cubeTop n).map q
  rw [hc, htop q] at h
  rw [show ((flatten c)⁻¹ : Equiv.Perm (Fin n)) ((flatten c) q) = q from by simp]
  exact h

/-- A run's `cross` *is* the word it spells (`runWordEquiv`): `cross` is the firing order inverted,
and on a run the firing order is its step order. -/
@[simp] theorem cross_wordRun (σ : Equiv.Perm (Fin n)) : cross (wordRun σ).chain = σ :=
  (cross_eq_flatten_inv (wordRun σ).chain).trans ((runWordEquiv n).apply_symm_apply σ)

end ChainCat
