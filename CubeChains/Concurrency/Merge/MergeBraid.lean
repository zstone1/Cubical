import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/MergeBraid — the refinements that cross nothing

A splice `𝟙 ∨ w ∨ 𝟙` fixes every event in front of its cut and moves the rest as its staircase
does (`pos_coordMap_splicePhi`).  `cubeMerge` runs its first bead through the low coordinate block
and its second through the high one, both increasingly, so a merge crosses nothing
(`crossPerm_eq_one_of_merge`); along a composite the crossing counts add, so a composite crosses
nothing exactly when both legs do.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

variable {K : BPSet}

/-- **The crossing permutation of a concatenation is the block sum of its two halves.**  Both
strand counts are named, so the equation is between permutations of `Fin (m + n)` with no `Fin`
transport. -/
theorem crossPerm_concat {A₁ A₂ C₁ C₂ : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) {m n : ℕ} (h₁ : dimSum A₁ = m) (h₂ : dimSum A₂ = n)
    (h : dimSum (A₁ ++ A₂) = m + n) :
    crossPerm h (zHom (concatHomφ g₁ g₂)) = permSum m n (crossPerm h₁ g₁, crossPerm h₂ g₂) := by
  subst h₁
  subst h₂
  refine Eq.trans (crossPerm_eq_of_φ h (g' := (chConcat Zbp Zbp).map
    (X := (zObj A₁, zObj A₂)) (Y := (zObj C₁, zObj C₂)) (g₁, g₂)) (by rw [zHom_φ, chConcat_map_φ]))
    ?_
  exact crossPerm_chConcat (ab := (zObj A₁, zObj A₂)) (ab' := (zObj C₁, zObj C₂)) (g₁, g₂)

/-- **The crossing permutation sees only the wedge map**, so pushing a chain morphism forward to
the serial wedges leaves it alone. -/
theorem crossPerm_zHom {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    crossPerm (a := zObj a.dims) (b := zObj b.dims) h (zHom f.φ) = crossPerm h f := rfl

/-- **Crossing nothing, on coordinates**: every event keeps its rank. -/
theorem crossPerm_eq_one_iff_pos {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (u : a ⟶ b) :
    crossPerm h u = 1 ↔ ∀ e : beadEvent a.dims, (pos (coordMap (Hom.φ u) e) : ℕ) = (pos e : ℕ) := by
  refine ⟨fun h1 e => ?_, fun h1 => Equiv.ext fun x => Fin.ext ?_⟩
  · have hv := crossPerm_val h u (x := strand a.dims h e) (strand_val a.dims h e)
    rw [h1, Equiv.Perm.one_apply, strand_val] at hv
    exact hv.symm
  · have hs : (pos ((strand a.dims h).symm x) : ℕ) = (x : ℕ) :=
      (strand_val a.dims h _).symm.trans (congrArg Fin.val ((strand a.dims h).apply_symm_apply x))
    rw [Equiv.Perm.one_apply, crossPerm_val h u hs.symm, h1]
    exact hs

/-- **A composite crosses nothing exactly when both legs do** — the crossing counts add, so neither
leg can undo the other's crossings. -/
theorem crossPerm_eq_one_comp_iff {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (g : b ⟶ c) :
    crossPerm h (f ≫ g) = 1 ↔ crossPerm h f = 1 ∧ crossPerm (tgtStrands f h) g = 1 := by
  refine ⟨fun hfg => ?_, fun ⟨hf, hg⟩ => by rw [crossPerm_comp h f g, hf, hg, one_mul]⟩
  have hlen := permLen_crossPerm_comp h f g
  rw [hfg, permLen_one] at hlen
  exact ⟨eq_one_of_permLen_eq_zero _ (by omega), eq_one_of_permLen_eq_zero _ (by omega)⟩

/-- **The merge staircase keeps every event's rank** — its first bead on the head block, its
second on the tail block. -/
theorem pos_coordMap_spliceNil_cubeMerge (r : List ℕ+) (p q : ℕ+) (e : beadEvent (p :: q :: r)) :
    (pos (coordMap (spliceNil r p q (cubeMerge (p : ℕ) (q : ℕ))) e) : ℕ) = (pos e : ℕ) := by
  induction e using spliceEventCases with
  | h0 k =>
      rw [pos_coordMap_spliceNil_zero]
      exact (faceEmb_cubeMerge_inl p q k).trans (pos_cons_zero p (q :: r) k).symm
  | h1 k =>
      rw [pos_coordMap_spliceNil_one]
      exact (faceEmb_cubeMerge_inr p q k).trans ((pos_cons_succ p (q :: r) 0 k).trans
        (congrArg ((p : ℕ) + ·) (pos_cons_zero q r k))).symm
  | ht j k =>
      rw [pos_coordMap_spliceNil_tail, pos_cons_succ, pos_cons_succ, PNat.add_coe]
      exact Nat.add_assoc _ _ _

/-- **A generator crosses nothing** — by `eq_splicePhi_of_sq` it *is* a splice of the merge
staircase, which keeps every rank. -/
theorem crossPerm_eq_one_of_merge {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) {f : a ⟶ b}
    (hm : merge K f) : crossPerm h f = 1 := by
  obtain ⟨d, hw⟩ := hm
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  refine (crossPerm_eq_one_iff_pos h f).mpr fun e => ?_
  rw [show Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) from
      (eq_splicePhi_of_sq sq).trans (congrArg _ hw),
    pos_coordMap_splicePhi r p q _ id (pos_coordMap_spliceNil_cubeMerge r p q) l e]
  simp only [id]
  split_ifs <;> omega

/-- **A merge crosses nothing** — the generators do, and `crossPerm` is a cocycle. -/
theorem crossPerm_eq_one_of_W {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) {f : a ⟶ b}
    (hf : W K f) : crossPerm h f = 1 := by
  have key : ∀ {x y : Ch K} {u : x ⟶ y}, W K u → crossPerm (rfl : dimSum x.dims = _) u = 1 := by
    intro x y u hu
    induction hu with
    | of _ hm => exact crossPerm_eq_one_of_merge rfl hm
    | id z => exact crossPerm_id z rfl
    | comp_of s t _ ht ih =>
        rw [crossPerm_comp rfl s t, crossPerm_eq_one_of_merge _ ht, ih, one_mul]
  exact crossPerm_eq_one_congr (key hf)

/-- **Comparable at all is comparable without braiding** — by a composite of merges. -/
theorem exists_crossPerm_eq_one {a b : Ch Zbp} {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) : ∃ f : a ⟶ b, crossPerm h f = 1 :=
  let ⟨hd, hs⟩ := nonempty_hom_iff.mp hab
  (exists_W_of_coarser _ rfl hd hs).imp fun _ => crossPerm_eq_one_of_W h

/-- **…so a merge keeps the event order** — `crossPerm_eq_one_of_W`, read on positions. -/
theorem pos_coordMap_of_W {a b : Ch K} {f : a ⟶ b} (hf : W K f) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) :=
  (crossPerm_eq_one_iff_pos rfl f).mp (crossPerm_eq_one_of_W rfl hf) e

end ChainCat
