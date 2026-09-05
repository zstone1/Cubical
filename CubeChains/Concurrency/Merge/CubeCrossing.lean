import CubeChains.Concurrency.Merge.MergeGenerate
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

/-- **Every chain of `□n` has `n` events** — a wedge map cannot change the event count, and `□n`
*is* the coarsest chain's wedge. -/
theorem dimSum_dims_cube (c : Ch (□n)) : dimSum c.dims = n :=
  (serialWedge_dimSum_eq (c.map ≫ (topWedgeIso n).inv)).trans (dimSum_topDims n)

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

/-- The crossing *count*, which is what descends to the localization. -/
noncomputable def crossLen (c : Ch (□n)) : ℕ := permLen (cross c)

@[simp] theorem cross_cubeTop (n : ℕ) : cross (cubeTop n) = 1 := by
  rw [cross, toCubeTop_cubeTop, crossPerm_id]

@[simp] theorem crossLen_cubeTop (n : ℕ) : crossLen (cubeTop n) = 0 := by
  rw [crossLen, cross_cubeTop, permLen_one]

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
