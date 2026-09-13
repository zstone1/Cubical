import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Machinery.Braid.PosAction
import Mathlib.CategoryTheory.Localization.Construction

/-!
# Concurrency/Merge/CubeCrossing — how much a chain of the cube has braided

A chain of `□n` refines the one-bead chain in exactly one way, and the crossing permutation of that
refinement is an invariant, `cross`, which `W` leaves alone (`W` is `crossPerm = 1`) and which every
other refinement strictly shortens (`crossLen_lt`).  `Concurrency/Merge/CubeWeakOrder` reads it as
the weak Bruhat order; everything about the localization is said there.
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

theorem comp_toCubeTop {c c' : Ch (□n)} (f : c ⟶ c') : f ≫ toCubeTop c' = toCubeTop c :=
  hom_ext' (by
    change Hom.φ f ≫ c'.map ≫ (topWedgeIso n).inv = c.map ≫ (topWedgeIso n).inv
    rw [← Category.assoc, f.w])

@[simp] theorem toCubeTop_cubeTop : toCubeTop (cubeTop n) = 𝟙 (cubeTop n) :=
  hom_ext' (by
    change (topWedgeIso n).hom ≫ (topWedgeIso n).inv = 𝟙 _
    rw [Iso.hom_inv_id])

/-- **How much a chain of `□n` has braided**: the crossing permutation of its refinement of the
one-bead chain. -/
noncomputable def cross (c : Ch (□n)) : Equiv.Perm (Fin n) :=
  crossPerm (dimSum_dims_cube c) (toCubeTop c)

/-! ### `cross` is the word a chain fires

`flatten` is the firing order — coordinate ↦ step — so `cross` is the **word**, step ↦ coordinate.
The two are inverse because a refinement factors the crossing permutation on the right
(`cross_eq_mul`) and the firing order on the left, and the weak order in `Machinery/Braid` is the
right one.  This section is `Concurrency/Salvetti/ChainBraidFace`'s `flatten` interface read that
way round; past it no file of `Concurrency/Merge/` mentions `flatten`. -/

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

/-- The word and the firing order undo each other. -/
@[simp] theorem flatten_cross (c : Ch (□n)) (s : Fin n) : flatten c (cross c s) = s := by
  rw [cross_eq_flatten_inv]
  exact (flatten c).apply_symm_apply s

/-- **A chain fires its coordinates in bead order, and inside a bead in coordinate order** —
`flatten_lt_iff`, read on the word. -/
theorem lt_iff_cross (c : Ch (□n)) {s s' : Fin n} :
    s < s' ↔ (beadOf c (cross c s) : ℕ) < (beadOf c (cross c s') : ℕ)
      ∨ (beadOf c (cross c s) = beadOf c (cross c s') ∧ cross c s < cross c s') := by
  rw [← flatten_lt_iff c (q := cross c s) (q' := cross c s'), flatten_cross, flatten_cross]

/-- **…and no other order does** — `flatten_apply`, read on the word: a permutation sorting the
coordinates by bead and then by coordinate *is* the word. -/
theorem cross_eq_of_sorted (c : Ch (□n)) (g : Equiv.Perm (Fin n))
    (hg : ∀ x y : Fin n, x < y → (beadOf c (g x) : ℕ) < (beadOf c (g y) : ℕ) ∨
      (beadOf c (g x) = beadOf c (g y) ∧ g x < g y)) : cross c = g := by
  have h : flatten c = g⁻¹ := Equiv.ext fun x => by
    simpa using flatten_apply c g hg (g⁻¹ x)
  rw [cross_eq_flatten_inv, h, inv_inv]

/-- **The bead a coarsening puts the letter fired at step `s` in is the block of `s`** —
`beadOf_of_hom` with the source's word cancelling its firing order.  This is the one place a chain's
own bead map meets its shape's blocks. -/
theorem beadOf_cross {r c : Ch (□n)} (f : r ⟶ c) (s : Fin n) :
    (beadOf c (cross r s) : ℕ) = ((dimComp c.dims (dimSum_dims_cube c)).index s : ℕ) := by
  rw [beadOf_of_hom f, flatten_cross]

/-- …at the chain's own word. -/
theorem beadOf_cross_self (c : Ch (□n)) (s : Fin n) :
    (beadOf c (cross c s) : ℕ) = ((dimComp c.dims (dimSum_dims_cube c)).index s : ℕ) :=
  beadOf_cross (𝟙 c) s

/-- The crossing *count*, which is what descends to the localization. -/
noncomputable def crossLen (c : Ch (□n)) : ℕ := permLen (cross c)

@[simp] theorem cross_cubeTop (n : ℕ) : cross (cubeTop n) = 1 := by
  rw [cross, toCubeTop_cubeTop, crossPerm_id]

/-- **Crossings add along a refinement** — `permLen_crossPerm_comp`, read at the one-bead chain. -/
theorem crossLen_eq_add {c c' : Ch (□n)} (f : c ⟶ c') :
    crossLen c = permLen (crossPerm (dimSum_dims_cube c) f) + crossLen c' := by
  rw [crossLen, cross, ← comp_toCubeTop f, permLen_crossPerm_comp]
  rfl

/-- A refinement that braids strictly lowers the crossing count. -/
theorem crossLen_lt {c c' : Ch (□n)} {f : c ⟶ c'} (hf : ¬ W (□n) f) : crossLen c' < crossLen c := by
  have hne : crossPerm (dimSum_dims_cube c) f ≠ 1 := fun h =>
    hf ((W_iff_crossPerm_eq_one _ f).mpr h)
  have hpos : 0 < permLen (crossPerm (dimSum_dims_cube c) f) :=
    Nat.pos_of_ne_zero fun h => hne (eq_one_of_permLen_eq_zero _ h)
  rw [crossLen_eq_add f]; omega

/-- **The square has a chain that braids**: `cubeReorder` is a codimension-one refinement that is
not a merge (`not_merge_cutRefine_cubeReorder`), hence not in `W`. -/
theorem not_W_cutRefine_cubeReorder : ¬ W (□2) (cutRefine (cubeReorder 1 1)) := fun hW =>
  not_merge_cutRefine_cubeReorder ((merge_iff _).mpr ⟨hW, codim_cutRefine _⟩)

theorem crossLen_cutChain_pos : 0 < crossLen (cutChain (cubeReorder 1 1)) :=
  lt_of_le_of_lt (Nat.zero_le _) (crossLen_lt not_W_cutRefine_cubeReorder)

end ChainCat
