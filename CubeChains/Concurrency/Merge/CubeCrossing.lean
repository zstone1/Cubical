import CubeChains.Concurrency.Merge.MergeGenerate
import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Machinery.Braid.PosAction
import Mathlib.CategoryTheory.Localization.Construction

/-!
# Concurrency/Merge/CubeCrossing — the localized cube slice is not the braid action

A chain of `□n` refines the one-bead chain in exactly one way, and the crossing permutation of that
refinement is an invariant, `cross`, which `W` leaves alone (`W` is `crossPerm = 1`) and which every
other refinement strictly shortens.  So `crossLen` descends to the localization, and a hom-set there
is **empty** whenever it would have to raise it.

That refutes `Ch(□n)[W⁻¹] ≌ PosBraidAction n`: the positive braids act transitively on the
orderings, so *every* hom-set of `PosBraidAction n` is inhabited.  The braiding lives in the
decoration — `hLocEquiv` is about `Hbp □n`, not `□n`.
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

theorem crossLen_le {c c' : Ch (□n)} (f : c ⟶ c') : crossLen c' ≤ crossLen c := by
  rw [crossLen_eq_add f]; omega

/-- A refinement that braids strictly lowers the crossing count. -/
theorem crossLen_lt {c c' : Ch (□n)} {f : c ⟶ c'} (hf : ¬ W (□n) f) : crossLen c' < crossLen c := by
  have hne : crossPerm (dimSum_dims_cube c) f ≠ 1 := fun h =>
    hf ((W_iff_crossPerm_eq_one _ f).mpr h)
  have hpos : 0 < permLen (crossPerm (dimSum_dims_cube c) f) :=
    Nat.pos_of_ne_zero fun h => hne (eq_one_of_permLen_eq_zero _ h)
  rw [crossLen_eq_add f]; omega

/-! ## …descends to the localization -/

/-- The crossing count as a functor to `ℕᵒᵖ`: a refinement can only lose crossings. -/
noncomputable def crossFunctor (n : ℕ) : Ch (□n) ⥤ ℕᵒᵖ where
  obj c := Opposite.op (crossLen c)
  map f := (homOfLE (crossLen_le f)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem crossFunctor_inverts : (W (□n)).IsInvertedBy (crossFunctor n) := by
  intro c c' f hf
  have hle : crossLen c ≤ crossLen c' := by
    have hadd := crossLen_eq_add f
    rw [crossPerm_eq_one_of_W _ hf, permLen_one] at hadd
    omega
  exact ⟨(homOfLE hle).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The crossing count, on the localized cube slice. -/
noncomputable def crossLoc (n : ℕ) : (W (□n)).Localization ⥤ ℕᵒᵖ :=
  Localization.Construction.lift (crossFunctor n) crossFunctor_inverts

theorem crossLen_loc {c c' : Ch (□n)}
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') : crossLen c' ≤ crossLen c :=
  leOfHom ((crossLoc n).map g).unop

/-- **A hom-set of the localized cube slice is empty** when it would have to raise the crossing
count. -/
theorem isEmpty_loc_hom_of_crossLen_lt {c c' : Ch (□n)} (h : crossLen c < crossLen c') :
    IsEmpty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :=
  ⟨fun g => absurd (crossLen_loc g) (not_le.mpr h)⟩

/-! ## The square braids, so the localization is not connected -/

/-- **The square has a chain that braids**: `cubeReorder` is a codimension-one refinement that is
not a merge (`not_merge_cutRefine_cubeReorder`), hence not in `W`. -/
theorem not_W_cutRefine_cubeReorder : ¬ W (□2) (cutRefine (cubeReorder 1 1)) := fun hW =>
  not_merge_cutRefine_cubeReorder ((merge_iff _).mpr ⟨hW, codim_cutRefine _⟩)

theorem crossLen_cutChain_pos : 0 < crossLen (cutChain (cubeReorder 1 1)) :=
  lt_of_le_of_lt (Nat.zero_le _) (crossLen_lt not_W_cutRefine_cubeReorder)

/-- **`Ch(□²)[W⁻¹]` has an empty hom-set.** -/
theorem isEmpty_loc_hom_cubeTop :
    IsEmpty ((W (□2)).Q.obj (cubeTop 2) ⟶ (W (□2)).Q.obj (cutChain (cubeReorder 1 1))) :=
  isEmpty_loc_hom_of_crossLen_lt (by rw [crossLen_cubeTop]; exact crossLen_cutChain_pos)

/-! ## …but the braid action is connected -/

/-- **The positive braids act transitively on the orderings**, so every hom-set of
`PosBraidAction n` is inhabited. -/
theorem nonempty_posBraidAction_hom (p q : PosBraidAction n) : Nonempty (p ⟶ q) :=
  ⟨⟨posPerm (q.back * p.back⁻¹), by
    change posPermHom n (posPerm (q.back * p.back⁻¹)) * p.back = q.back
    rw [posPermHom_posPerm, mul_assoc, inv_mul_cancel, mul_one]⟩⟩

theorem nonempty_posBraidAction_hom_op (p q : (PosBraidAction n)ᵒᵖ) : Nonempty (p ⟶ q) :=
  ⟨(nonempty_posBraidAction_hom q.unop p.unop).some.op⟩

/-- A category equivalent to one whose hom-sets are all inhabited has all hom-sets inhabited. -/
theorem nonempty_hom_of_equiv {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    (h : ∀ p q : D, Nonempty (p ⟶ q)) (X Y : C) : Nonempty (X ⟶ Y) :=
  ⟨e.fullyFaithfulFunctor.preimage (h _ _).some⟩

/-- **`Ch(□²)[W⁻¹]` is not the positive braid action.**  Both have `2! = 2` objects, but the
localized cube slice is not connected and the action category is. -/
theorem not_nonempty_equiv_posBraidAction :
    ¬ Nonempty ((W (□2)).Localization ≌ PosBraidAction 2) := fun ⟨e⟩ =>
  isEmpty_loc_hom_cubeTop.elim
    (nonempty_hom_of_equiv e nonempty_posBraidAction_hom _ _).some

/-- …and not its opposite either, which is the form `hLocActionPresentation` presents. -/
theorem not_nonempty_equiv_posBraidAction_op :
    ¬ Nonempty ((W (□2)).Localization ≌ (PosBraidAction 2)ᵒᵖ) := fun ⟨e⟩ =>
  isEmpty_loc_hom_cubeTop.elim
    (nonempty_hom_of_equiv e nonempty_posBraidAction_hom_op _ _).some

end ChainCat
