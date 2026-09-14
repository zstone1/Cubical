import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/MergeBraid — the crossing permutation of a splice

`crossPerm` is **monoidal over the wedge** (`crossPerm_chConcat`), and a splice `𝟙 ∨ w ∨ 𝟙` is a
concatenation twice over (`zHom_splicePhi_eq`, `zHom_spliceNil_eq`), so its crossing permutation is
the block sum `1 ⊕ crossPerm w ⊕ 1`: the beads flanking a cut keep their strand and only the merged
block moves, by the staircase's own crossing.

At `w = cubeReorder` that block sum is the Garside atom (`Concurrency/Merge/Atom`), which is the one
place a permutation is named; at `w = cubeMerge` it is trivial, which is what makes a merge a
refinement that crosses nothing.  Along a composite the crossing counts add
(`permLen_crossPerm_comp`), so a composite crosses nothing exactly when both legs do: a crossing is
never undone.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

variable {K : BPSet}

/-! ### `crossPerm` is a block sum over a concatenation

`crossPerm_chConcat` is the tensorator law; here it is read on a bare concatenation of wedge maps,
which is the shape every splice below presents. -/

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

/-! ### A splice crosses only the block it merges

`l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, so a splice is a concatenation twice over and
`crossPerm_concat` applies twice: `1` on the beads before the cut, the staircase's own crossing on
the two beads it merges, `1` on the beads after. -/

/-- **A splice is the block sum `1 ⊕ w ⊕ 1`** — `crossPerm_concat` twice, at the two junctions
`l | [p,q] | r`.  The strand count is named as the nested sum, which is what keeps the equation
free of `Fin` transports; the two readings below are its `permSum` projections. -/
theorem crossPerm_splicePhi (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ))
    (h : dimSum (l ++ p :: q :: r) = dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r)) :
    crossPerm h (zHom (splicePhi l r p q w))
      = permSum (dimSum l) (dimSum ([p, q] : List ℕ+) + dimSum r)
          (1, permSum (dimSum ([p, q] : List ℕ+)) (dimSum r)
            (crossPerm rfl (zHom (pairMerge p q w)), 1)) := by
  rw [zHom_splicePhi_eq]
  refine Eq.trans (crossPerm_concat (𝟙 (zObj l)) (zHom (spliceNil r p q w)) rfl
    (dimSum_append [p, q] r) h)
    (congrArg (permSum (dimSum l) (dimSum ([p, q] : List ℕ+) + dimSum r))
      (Prod.ext (crossPerm_id (zObj l) rfl) ?_))
  rw [zHom_spliceNil_eq]
  exact (crossPerm_concat (zHom (pairMerge p q w)) (𝟙 (zObj r)) rfl rfl
    (dimSum_append [p, q] r)).trans
    (congrArg (permSum (dimSum ([p, q] : List ℕ+)) (dimSum r))
      (Prod.ext rfl (crossPerm_id (zObj r) rfl)))

/-- **A splice moves the merged block by the staircase alone**, shifted past the beads in front. -/
theorem crossPerm_splicePhi_mid (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {N : ℕ}
    (h : dimSum (l ++ p :: q :: r) = N) {x : Fin N} {y : Fin (dimSum ([p, q] : List ℕ+))}
    (hx : (x : ℕ) = dimSum l + (y : ℕ)) :
    (crossPerm h (zHom (splicePhi l r p q w)) x : ℕ)
      = dimSum l + (crossPerm rfl (zHom (pairMerge p q w)) y : ℕ) := by
  have hN : dimSum (l ++ p :: q :: r)
      = dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r) :=
    (dimSum_append l (p :: q :: r)).trans (congrArg (dimSum l + ·) (dimSum_append [p, q] r))
  refine Eq.trans (crossPerm_val_congr h hN (zHom (splicePhi l r p q w))
    (x' := Fin.natAdd (dimSum l) (Fin.castAdd (dimSum r) y)) (by simpa using hx)) ?_
  rw [crossPerm_splicePhi l r p q w hN, permSum_apply_natAdd, permSum_apply_castAdd]
  rfl

/-- **Outside the merged block a splice keeps the strand** — the two flanking stretches are carried
by identities. -/
theorem crossPerm_splicePhi_out (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {N : ℕ}
    (h : dimSum (l ++ p :: q :: r) = N) {x : Fin N}
    (hx : (x : ℕ) < dimSum l ∨ dimSum l + dimSum ([p, q] : List ℕ+) ≤ (x : ℕ)) :
    (crossPerm h (zHom (splicePhi l r p q w)) x : ℕ) = (x : ℕ) := by
  have hN : dimSum (l ++ p :: q :: r)
      = dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r) :=
    (dimSum_append l (p :: q :: r)).trans (congrArg (dimSum l + ·) (dimSum_append [p, q] r))
  have hlt : (x : ℕ) < dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r) := by
    have := x.isLt; omega
  rcases hx with hx | hx
  · refine Eq.trans (crossPerm_val_congr h hN (zHom (splicePhi l r p q w))
      (x' := Fin.castAdd (dimSum ([p, q] : List ℕ+) + dimSum r) ⟨(x : ℕ), hx⟩) rfl) ?_
    rw [crossPerm_splicePhi l r p q w hN, permSum_apply_castAdd]
    rfl
  · have hval : (x : ℕ) = dimSum l + (dimSum ([p, q] : List ℕ+)
        + ((x : ℕ) - dimSum l - dimSum ([p, q] : List ℕ+))) := by omega
    refine Eq.trans (crossPerm_val_congr h hN (zHom (splicePhi l r p q w))
      (x' := Fin.natAdd (dimSum l) (Fin.natAdd (dimSum ([p, q] : List ℕ+))
        ⟨(x : ℕ) - dimSum l - dimSum ([p, q] : List ℕ+), by omega⟩)) (by simpa using hval)) ?_
    rw [crossPerm_splicePhi l r p q w hN, permSum_apply_natAdd, permSum_apply_natAdd]
    simp only [Equiv.Perm.one_apply, Fin.val_natAdd]
    omega

/-! ## The refinements that cross nothing

`crossPerm h u = 1`.  On coordinates that says every event keeps its rank
(`crossPerm_eq_one_iff_pos`); over the wedge it is the block sum above, trivial exactly when both
blocks are — so only the staircase in the middle of a splice has to be inspected. -/

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

/-- **A splice crosses nothing as soon as its staircase does** — a block sum is trivial exactly
when every block is. -/
theorem crossPerm_eq_one_splicePhi (l r : List ℕ+) (p q : ℕ+)
    {w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)}
    (hw : crossPerm rfl (zHom (pairMerge p q w)) = 1) {N : ℕ}
    (h : dimSum (l ++ p :: q :: r) = N) :
    crossPerm h (zHom (splicePhi l r p q w)) = 1 := by
  have hN : dimSum (l ++ p :: q :: r)
      = dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r) :=
    (dimSum_append l (p :: q :: r)).trans (congrArg (dimSum l + ·) (dimSum_append [p, q] r))
  refine crossPerm_eq_one_congr (h := hN) ?_
  rw [crossPerm_splicePhi l r p q w hN]
  exact permSum_eq_one_iff.mpr ⟨rfl, permSum_eq_one_iff.mpr ⟨hw, rfl⟩⟩

/-- **The merge staircase crosses nothing** — `pos_coordMap_pairMerge_cubeMerge`. -/
theorem crossPerm_eq_one_pairMerge_cubeMerge (p q : ℕ+) :
    crossPerm rfl (zHom (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ)))) = 1 :=
  (crossPerm_eq_one_iff_pos rfl _).mpr (pos_coordMap_pairMerge_cubeMerge p q)

/-- **A generator crosses nothing** — by `eq_splicePhi_of_sq` it *is* a splice, and its middle map
is the merge staircase. -/
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
  rw [← crossPerm_zHom h f,
    show Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) from
      (eq_splicePhi_of_sq sq).trans (congrArg _ hw)]
  exact crossPerm_eq_one_splicePhi l r p q (crossPerm_eq_one_pairMerge_cubeMerge p q) h

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

/-- **…so a merge keeps the event order** — `crossPerm_eq_one_of_W`, read on positions. -/
theorem pos_coordMap_of_W {a b : Ch K} {f : a ⟶ b} (hf : W K f) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) :=
  (crossPerm_eq_one_iff_pos rfl f).mp (crossPerm_eq_one_of_W rfl hf) e

end ChainCat
