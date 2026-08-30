import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Concurrency/Merge/MergeBraid — the merges are the kernel of the braid grading

`crossPerm` is `coordMap` read at both ends by `pos`, so it is trivial exactly on the monotone
refinements: `W` **is** the kernel of the braid grading (`W_iff_crossPerm_eq_one`), and every
germ grading inverts it.

A cut exhibits `f` as `𝟙 ∨ w ∨ 𝟙` (`eq_splicePhi_of_sq`), so a cut with `w = cubeMerge p q` *is*
the spliced staircase `mergeHom`; that one runs its first bead through the coordinate block
`[0, p)` and its second through `[p, p+q)`, both increasingly, hence is a member.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

/-! ### `W` is the kernel of the crossing permutation -/

/-- **A refinement is a merge exactly when it crosses nothing** — at any strand count its source
meets, since recounting conjugates. -/
theorem W_iff_crossPerm_eq_one {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (f : a ⟶ b) : W K f ↔ crossPerm h f = 1 := by
  refine (W_iff_pos f).trans ⟨fun hp => Equiv.ext fun i => ?_, fun hone e => ?_⟩
  · obtain ⟨e, rfl⟩ := (strand a h).surjective i
    exact Fin.ext (by rw [Equiv.Perm.one_apply, crossPerm_strand, strand_val, strand_val, hp e])
  · have hs := crossPerm_strand h f e
    rw [hone, Equiv.Perm.one_apply] at hs
    exact (congrArg Fin.val hs).symm

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

/-- **The canonical bead merge is a member**, wherever it is spliced. -/
theorem W_mergeHom (l r : List ℕ+) (p q : ℕ+) : W Zbp (mergeHom l r p q) :=
  (W_iff_pos _).mpr (pos_coordMap_splicePhi_cubeMerge l r p q)

/-- **A cut with the staircase is a merge** — by `eq_splicePhi_of_sq` it *is* that splice. -/
theorem W_of_cut_cubeMerge {K : BPSet} {a b : Ch K} {f : a ⟶ b} (d : CutData f)
    (hw : d.w = cubeMerge (d.p : ℕ) (d.q : ℕ)) : W K f := by
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  change Monotone (coordMap (Hom.φ f))
  rw [eq_splicePhi_of_sq sq, hw]
  exact W_mergeHom l r p q

/-- **Every canonical merge is a member.** -/
theorem merge_le_W (X : BPSet) : merge X ≤ W X := fun _ _ _ h =>
  h.elim fun d hw => W_of_cut_cubeMerge d hw

/-- **A germ grading kills the merges**: a merge crosses nothing, so its image is the bare degree
identification.  Stated for `chGerm`, so `chBraid` and `chPosBraid` both inherit it. -/
theorem chGerm_map_of_W {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : W K f) :
    (chGerm G K).map f = Graded.ofDeg (strandsEq f) := by
  rw [chGerm_map, (W_iff_crossPerm_eq_one rfl f).mp h]
  exact G.hom_one_eq_ofDeg _

/-- **The merges are inverted.**  This is what lets a germ grading factor through the localization
at `W`. -/
theorem W_isInvertedBy_chGerm {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M)
    (K : BPSet) : MorphismProperty.IsInvertedBy (W K) (chGerm G K) := by
  intro _ _ f hf
  rw [chGerm_map_of_W G hf]
  exact Graded.isIso_ofDeg _

end ChainCat
