import CubeChains.Chains.TotalMerge
import CubeChains.Chains.WedgeBraid
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Chains/MergeBraid — the merges are the kernel of the braid grading

`crossPerm` is `coordMap` read at both ends by `pos`, so it is trivial exactly on the monotone
refinements: `W` **is** the kernel of the braid grading (`W_iff_crossPerm_eq_one`), and every
germ grading inverts it.

A cut exhibits `f` as `𝟙 ∨ w ∨ 𝟙`, and the coordinate map is monoidal over the wedge
(`coordMap_inclL`/`_inclR`), so only the merged pair of beads can move.  There `cubeMerge p q` runs
its first bead through the coordinate block `[0, p)` and its second through `[p, p+q)`, both
increasingly — which is why a cut with that middle map is a member.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

/-! ### `W` is the kernel of the crossing permutation

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
theorem W_iff_crossPerm_eq_one {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    W K f ↔ crossPerm f = 1 :=
  (W_iff_pos f).trans
    ⟨crossPerm_eq_one_of_pos_eq f, pos_coordMap_of_crossPerm_eq_one⟩

@[simp] theorem crossPermAt_eq_one_of_W {K : BPSet} {a b : Ch K} {N : ℕ}
    (hN : dimSum a.dims = N) {f : a ⟶ b} (h : W K f) : crossPermAt hN f = 1 := by
  rw [crossPermAt, (W_iff_crossPerm_eq_one f).mp h]
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

/-- **A cut with the staircase preserves the event order** — it is the splice of that staircase
(`eq_splicePhi_of_sq`), whose coordinate map is the staircase's own. -/
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
  rw [eq_splicePhi_of_sq sq, hw]
  exact pos_coordMap_splicePhi_cubeMerge l r p q e

/-- **Every canonical merge is a member.** -/
theorem merge_le_W (X : BPSet) : merge X ≤ W X := fun _ _ f h =>
  (W_iff_pos f).mpr (h.elim fun d hw => pos_coordMap_of_merge f d hw)

theorem W_mergeHom (l r : List ℕ+) (p q : ℕ+) : W Zbp (mergeHom l r p q) :=
  merge_le_W Zbp _ (merge_mergeHom l r p q)

/-- **A merge does not braid.** -/
theorem crossPerm_eq_one_of_merge {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : merge K f) :
    crossPerm f = 1 :=
  (W_iff_crossPerm_eq_one f).mp (merge_le_W K f h)

/-- **A germ grading kills the merges**: a merge crosses nothing, so its image is the bare degree
identification.  Stated for `chGerm`, so `chBraid` and `chPosBraid` both inherit it. -/
theorem chGerm_map_of_W {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : W K f) :
    (chGerm G K).map f = Graded.ofDeg (strandsEq f) := by
  rw [chGerm_map, (W_iff_crossPerm_eq_one f).mp h]
  exact G.hom_one_eq_ofDeg _

/-- **The merges are inverted.**  This is what lets a germ grading factor through the localization
at `W`. -/
theorem W_isInvertedBy_chGerm {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    (K : BPSet) : MorphismProperty.IsInvertedBy (W K) (chGerm G K) := by
  intro _ _ f hf
  rw [chGerm_map_of_W G hf]
  exact Graded.isIso_ofDeg _

end ChainCat
