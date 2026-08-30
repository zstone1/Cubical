import CubeChains.Chains.TotalMerge
import CubeChains.Chains.WedgeBraid
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Chains/MergeBraid — the merges are the kernel of the braid grading

`crossPerm` is `coordMap` read at both ends by `pos`, so it is trivial exactly on the monotone
refinements: `Winf` **is** the kernel of the braid grading (`Winf_iff_crossPerm_eq_one`), and every
germ grading inverts it.

A cut exhibits `f` as `𝟙 ∨ w ∨ 𝟙`, and the coordinate map is monoidal over the wedge
(`coordMap_inclL`/`_inclR`), so only the merged pair of beads can move.  There `cubeMerge p q` runs
its first bead through the coordinate block `[0, p)` and its second through `[p, p+q)`, both
increasingly — which is why a cut with that middle map is a member.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

/-! ### `Winf` is the kernel of the crossing permutation

`crossPerm` conjugates `coordMap` by `strand = pos`, so it is the identity exactly when `coordMap`
preserves the flattening. -/

/-- **The crossing permutation is trivial when the coordinate map preserves the flattening.** -/
theorem crossPerm_eq_one_of_pos_eq {K : BPSet} {a b : Ch K} (g : a ⟶ b)
    (h : ∀ e : beadEvent a.dims, (pos (coordMap g.φ e) : ℕ) = (pos e : ℕ)) :
    crossPerm g = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (strand a).surjective i
  refine Fin.ext ?_
  rw [Equiv.Perm.one_apply, crossPerm_strand, strand_val, strand_val, h e]

theorem pos_coordMap_of_crossPerm_eq_one {K : BPSet} {a b : Ch K} {f : a ⟶ b}
    (h : crossPerm f = 1) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  have hs := crossPerm_strand f e
  rw [h, Equiv.Perm.one_apply, strand_val, strand_val] at hs
  exact hs.symm

/-- **A refinement is a merge exactly when it crosses nothing.** -/
theorem Winf_iff_crossPerm_eq_one {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    Winf K f ↔ crossPerm f = 1 :=
  (Winf_iff_pos f).trans
    ⟨crossPerm_eq_one_of_pos_eq f, pos_coordMap_of_crossPerm_eq_one⟩

@[simp] theorem crossPermAt_eq_one_of_Winf {K : BPSet} {a b : Ch K} {N : ℕ}
    (hN : dimSum a.dims = N) {f : a ⟶ b} (h : Winf K f) : crossPermAt hN f = 1 := by
  rw [crossPermAt, (Winf_iff_crossPerm_eq_one f).mp h]
  exact Equiv.permCongr_refl _

/-! ### The merge staircase keeps the coordinate order -/

/-- **The merge staircase does not braid its two beads**: the first runs the low coordinate block,
the second the high one, both increasingly. -/
theorem pos_coordMap_pairMerge_cubeMerge (p q : ℕ+) (y : beadEvent [p, q]) :
    (pos (coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y) : ℕ) = (pos y : ℕ) := by
  obtain ⟨i, k⟩ := y
  have hi : (i : ℕ) < 2 := by simp
  rcases Nat.lt_or_ge (i : ℕ) 1 with h | h
  · obtain rfl : i = 0 := Fin.ext (by simp; omega)
    rw [coordMap_pairMerge_zero, pos_cons_zero, pos_cons_zero]
    exact faceEmb_cubeMerge_inl _ _ k
  · obtain rfl : i = 1 := Fin.ext (by simp; omega)
    rw [coordMap_pairMerge_one, pos_cons_zero, pos_pair_one]
    exact faceEmb_cubeMerge_inr _ _ k

/-- **A merge preserves the event order**, whatever it is spliced between. -/
theorem pos_coordMap_splicePhi_cubeMerge (l r : List ℕ+) (p q : ℕ+)
    (e : beadEvent (l ++ p :: q :: r)) :
    (pos (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) e) : ℕ) = (pos e : ℕ) := by
  rw [pos_coordMap_splicePhi (g := fun s => s) l r p q _
    (pos_coordMap_pairMerge_cubeMerge p q) e rfl]
  split_ifs <;> omega

/-! ### A cut with the merge staircase is a member -/

/-- **A cut is the splice of its own middle map** — its identifications are the canonical ones
(`serialWedge_iso_unique`). -/
theorem pos_coordMap_of_merge {K : BPSet} {a b : Ch K} (f : a ⟶ b) (d : CutData f)
    (hw : d.w = cubeMerge (d.p : ℕ) (d.q : ℕ)) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ e ⊢
  subst hsrc
  subst htgt
  obtain rfl : e₁ = (cutSrcIso l r p q).symm := serialWedge_iso_unique _ _
  obtain rfl : e₂ = (serialWedgeAppend l ((p + q) :: r)).symm := serialWedge_iso_unique _ _
  simp only [Iso.symm_hom] at sq
  have hφ : Hom.φ f = splicePhi l r p q w :=
    calc Hom.φ f
        = (Hom.φ f ≫ (serialWedgeAppend l ((p + q) :: r)).inv)
            ≫ (serialWedgeAppend l ((p + q) :: r)).hom := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = ((cutSrcIso l r p q).inv ≫ (𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r))))
            ≫ (serialWedgeAppend l ((p + q) :: r)).hom :=
          congrArg (fun z => z ≫ (serialWedgeAppend l ((p + q) :: r)).hom) sq.symm
      _ = splicePhi l r p q w := Category.assoc _ _ _
  rw [hφ, hw]
  exact pos_coordMap_splicePhi_cubeMerge l r p q e

/-- **Every canonical merge is a member.** -/
theorem merge_le_Winf (X : BPSet) : merge X ≤ Winf X := fun _ _ f h =>
  (Winf_iff_pos f).mpr (h.elim fun d hw => pos_coordMap_of_merge f d hw)

theorem Winf_mergeHom (l r : List ℕ+) (p q : ℕ+) : Winf Zbp (mergeHom l r p q) :=
  merge_le_Winf Zbp _ (merge_mergeHom l r p q)

/-- **A merge does not braid.** -/
theorem crossPerm_eq_one_of_merge {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : merge K f) :
    crossPerm f = 1 :=
  (Winf_iff_crossPerm_eq_one f).mp (merge_le_Winf K f h)

/-- **A germ grading kills the merges**: a merge crosses nothing, so its image is the bare degree
identification.  Stated for `chGerm`, so `chBraid` and `chPos` both inherit it. -/
theorem chGerm_map_of_Winf {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : Winf K f) :
    (chGerm G K).map f = Graded.ofDeg (strandsEq f) := by
  rw [chGerm_map, (Winf_iff_crossPerm_eq_one f).mp h]
  exact G.hom_one_eq_ofDeg _

/-- **The merges are inverted.**  This is what lets a germ grading factor through the localization
at `Winf`. -/
theorem Winf_isInvertedBy_chGerm {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    (K : BPSet) : MorphismProperty.IsInvertedBy (Winf K) (chGerm G K) := by
  intro _ _ f hf
  rw [chGerm_map_of_Winf G hf]
  exact Graded.isIso_ofDeg _

end ChainCat
