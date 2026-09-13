import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid

/-!
# Concurrency/Merge/MergeBraid — the merges cross nothing

`crossPerm` is **monoidal over the wedge** (`crossPerm_chConcat`), and a splice `𝟙 ∨ w ∨ 𝟙` is a
concatenation twice over (`splicePhi_eq_concat`, `spliceNil_eq_concat`), so its crossing
permutation is the block sum `1 ⊕ crossPerm w ⊕ 1`: the beads flanking a cut keep their strand and
only the merged block moves.  A cut exhibits `f` as such a splice (`eq_splicePhi_of_sq`), and with
`w = cubeMerge` the merged block does not move either — so a generator crosses nothing, and the
class it generates crosses nothing because `crossPerm` is an anti-homomorphism.

The same block sum at `w = cubeReorder` is the atom (`Concurrency/Merge/Atom`); the converse — a
refinement that crosses nothing is a composite of merges — is `Concurrency/Merge/MergeGenerate`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

/-- **The crossing permutation sees only the wedge map**, so pushing a chain morphism forward to
the serial wedges leaves it alone. -/
theorem crossPerm_zHom {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    crossPerm (a := zObj a.dims) (b := zObj b.dims) h (zHom f.φ) = crossPerm h f := rfl

/-! ### `crossPerm` is a block sum over a concatenation

`crossPerm_chConcat` is the tensorator law; here it is read on a bare concatenation of wedge maps,
which is the shape every splice below presents. -/

/-- **The crossing permutation of a concatenation is the block sum of its two halves.** -/
theorem crossPerm_concat {A₁ A₂ C₁ C₂ : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) :
    crossPerm (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂))
      = permSum (dimSum A₁) (dimSum A₂) (crossPerm rfl g₁, crossPerm rfl g₂) := by
  have hcat : crossPerm (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂))
      = crossPerm (dimSum_append A₁ A₂)
          ((chConcat Zbp Zbp).map (X := (zObj A₁, zObj A₂)) (Y := (zObj C₁, zObj C₂)) (g₁, g₂)) :=
    crossPerm_eq_of_φ (dimSum_append A₁ A₂) (by rw [zHom_φ, chConcat_map_φ])
  rw [hcat]
  exact crossPerm_chConcat (ab := (zObj A₁, zObj A₂)) (ab' := (zObj C₁, zObj C₂)) (g₁, g₂)

/-- **A concatenation crosses nothing exactly when both halves do** — `permSum_one_one`. -/
theorem crossPerm_concat_eq_one {A₁ A₂ C₁ C₂ : List ℕ+} {g₁ : zObj A₁ ⟶ zObj C₁}
    {g₂ : zObj A₂ ⟶ zObj C₂} {N₁ N₂ : ℕ} {k₁ : dimSum A₁ = N₁} {k₂ : dimSum A₂ = N₂}
    (h₁ : crossPerm k₁ g₁ = 1) (h₂ : crossPerm k₂ g₂ = 1) {N : ℕ}
    (h : dimSum (A₁ ++ A₂) = N) : crossPerm h (zHom (concatHomφ g₁ g₂)) = 1 := by
  have key : crossPerm (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂)) = 1 := by
    rw [crossPerm_concat,
      show (crossPerm (N := dimSum A₁) rfl g₁, crossPerm (N := dimSum A₂) rfl g₂) = (1, 1) from
        Prod.ext (crossPerm_eq_one_congr h₁) (crossPerm_eq_one_congr h₂),
      permSum_one_one]
  exact crossPerm_eq_one_congr key

/-- **The left block of a concatenation moves by its own half** — `permSum_apply_castAdd`, read on
values so that no strand count has to be transported. -/
theorem crossPerm_concat_left {A₁ A₂ C₁ C₂ : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) {N : ℕ} (h : dimSum (A₁ ++ A₂) = N) {x : Fin N}
    {i : Fin (dimSum A₁)} (hx : (x : ℕ) = (i : ℕ)) :
    (crossPerm h (zHom (concatHomφ g₁ g₂)) x : ℕ) = (crossPerm rfl g₁ i : ℕ) := by
  refine Eq.trans (crossPerm_val_congr h (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂))
    (x' := Fin.castAdd (dimSum A₂) i) (by simpa using hx)) ?_
  rw [crossPerm_concat, permSum_apply_castAdd]
  rfl

/-- **…and the right block by the other half**, shifted past the first. -/
theorem crossPerm_concat_right {A₁ A₂ C₁ C₂ : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) {N : ℕ} (h : dimSum (A₁ ++ A₂) = N) {x : Fin N}
    {j : Fin (dimSum A₂)} (hx : (x : ℕ) = dimSum A₁ + (j : ℕ)) :
    (crossPerm h (zHom (concatHomφ g₁ g₂)) x : ℕ) = dimSum A₁ + (crossPerm rfl g₂ j : ℕ) := by
  refine Eq.trans (crossPerm_val_congr h (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂))
    (x' := Fin.natAdd (dimSum A₁) j) (by simpa using hx)) ?_
  rw [crossPerm_concat, permSum_apply_natAdd]
  rfl

/-! ### A splice crosses only the block it merges

`l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, so a splice is a concatenation twice over and
`crossPerm_concat` applies twice: `1` on the beads before the cut, the staircase's own crossing on
the two beads it merges, `1` on the beads after. -/

/-- The splice, read as the concatenation of the untouched prefix with the rest. -/
private theorem zHom_splicePhi_eq (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    zHom (splicePhi l r p q w)
      = zHom (concatHomφ (𝟙 (zObj l)) (zHom (spliceNil r p q w))) :=
  congrArg zHom (splicePhi_eq_concat l r p q w)

/-- …and the rest as the staircase concatenated with the untouched suffix. -/
private theorem zHom_spliceNil_eq (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    zHom (spliceNil r p q w)
      = zHom (concatHomφ (zHom (pairMerge p q w)) (𝟙 (zObj r))) :=
  congrArg zHom (spliceNil_eq_concat r p q w)

/-- **A splice moves the merged block by the staircase alone**, shifted past the beads in front. -/
theorem crossPerm_splicePhi_mid (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {N : ℕ}
    (h : dimSum (l ++ p :: q :: r) = N) {x : Fin N} {y : Fin (dimSum ([p, q] : List ℕ+))}
    (hx : (x : ℕ) = dimSum l + (y : ℕ)) :
    (crossPerm h (zHom (splicePhi l r p q w)) x : ℕ)
      = dimSum l + (crossPerm rfl (zHom (pairMerge p q w)) y : ℕ) := by
  have hj : (y : ℕ) < dimSum (p :: q :: r) := by
    have h1 := y.isLt
    have h2 : dimSum (p :: q :: r) = dimSum ([p, q] : List ℕ+) + dimSum r := dimSum_append [p, q] r
    omega
  rw [zHom_splicePhi_eq]
  refine Eq.trans (crossPerm_concat_right (𝟙 (zObj l)) (zHom (spliceNil r p q w)) h
    (j := ⟨(y : ℕ), hj⟩) hx) ?_
  refine congrArg (dimSum l + ·) ?_
  rw [zHom_spliceNil_eq]
  exact crossPerm_concat_left (zHom (pairMerge p q w)) (𝟙 (zObj r)) rfl rfl

/-- **Outside the merged block a splice keeps the strand** — the two flanking stretches are carried
by identities. -/
theorem crossPerm_splicePhi_out (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {N : ℕ}
    (h : dimSum (l ++ p :: q :: r) = N) {x : Fin N}
    (hx : (x : ℕ) < dimSum l ∨ dimSum l + dimSum ([p, q] : List ℕ+) ≤ (x : ℕ)) :
    (crossPerm h (zHom (splicePhi l r p q w)) x : ℕ) = (x : ℕ) := by
  have hlt : (x : ℕ) < dimSum l + (dimSum ([p, q] : List ℕ+) + dimSum r) := by
    have h1 := x.isLt
    have h2 := dimSum_append l (p :: q :: r)
    have h3 : dimSum (p :: q :: r) = dimSum ([p, q] : List ℕ+) + dimSum r := dimSum_append [p, q] r
    omega
  have hid : ∀ d : List ℕ+, crossPerm (a := zObj d) rfl (𝟙 (zObj d)) = 1 :=
    fun d => crossPerm_id (zObj d) rfl
  have hcons : dimSum (p :: q :: r) = dimSum ([p, q] : List ℕ+) + dimSum r := dimSum_append [p, q] r
  rw [zHom_splicePhi_eq]
  rcases hx with hx | hx
  · refine Eq.trans (crossPerm_concat_left (𝟙 (zObj l)) (zHom (spliceNil r p q w)) h
      (i := ⟨(x : ℕ), hx⟩) rfl) ?_
    rw [hid l]
    rfl
  · refine Eq.trans (crossPerm_concat_right (𝟙 (zObj l)) (zHom (spliceNil r p q w)) h
      (j := ⟨(x : ℕ) - dimSum l, by omega⟩)
      (show (x : ℕ) = dimSum l + ((x : ℕ) - dimSum l) by omega)) ?_
    rw [zHom_spliceNil_eq]
    refine Eq.trans (congrArg (dimSum l + ·)
      (crossPerm_concat_right (zHom (pairMerge p q w)) (𝟙 (zObj r)) rfl
        (j := ⟨(x : ℕ) - dimSum l - dimSum ([p, q] : List ℕ+), by omega⟩)
        (show (x : ℕ) - dimSum l
            = dimSum ([p, q] : List ℕ+) + ((x : ℕ) - dimSum l - dimSum ([p, q] : List ℕ+)) by
          omega))) ?_
    rw [hid r]
    simp only [Equiv.Perm.one_apply]
    omega

/-! ### The merge staircase keeps the coordinate order

The one two-bead fact the whole class rests on: `cubeMerge` runs its first bead through the low
coordinate block and its second through the high one, both increasingly. -/

/-- **The merge staircase does not braid its two beads.** -/
theorem pos_coordMap_pairMerge_cubeMerge (p q : ℕ+) (y : beadEvent [p, q]) :
    (pos (coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y) : ℕ) = (pos y : ℕ) := by
  induction y using pairEventCases with
  | h0 k =>
      rw [coordMap_pairMerge_zero, pos_cons_zero, pos_cons_zero]
      exact faceEmb_cubeMerge_inl _ _ k
  | h1 k =>
      rw [coordMap_pairMerge_one, pos_cons_zero, pos_pair_one]
      exact faceEmb_cubeMerge_inr _ _ k

/-- …in crossing coordinates. -/
theorem crossPerm_pairMerge_cubeMerge (p q : ℕ+) :
    crossPerm (a := zObj [p, q]) rfl (zHom (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ)))) = 1 :=
  Equiv.ext fun i => Fin.ext <| by
    have he : (i : ℕ) = (pos (pos.symm i : beadEvent ([p, q] : List ℕ+)) : ℕ) := by
      rw [Equiv.apply_symm_apply]
    rw [Equiv.Perm.one_apply, crossPerm_val rfl _ he, zHom_φ]
    exact (pos_coordMap_pairMerge_cubeMerge p q _).trans he.symm

/-! ### The class crosses nothing -/

/-- **A generator crosses nothing** — by `eq_splicePhi_of_sq` it *is* a splice, whose crossing is
the block sum of `1`, the staircase's own, and `1`. -/
theorem crossPerm_eq_one_of_merge {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    {f : a ⟶ b} (hm : merge K f) : crossPerm h f = 1 := by
  obtain ⟨d, hw⟩ := hm
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  rw [← crossPerm_zHom h f, show Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) from
    (eq_splicePhi_of_sq sq).trans (congrArg _ hw),
    show splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))
      = concatHomφ (𝟙 (zObj l)) (zHom (spliceNil r p q (cubeMerge (p : ℕ) (q : ℕ)))) from
    splicePhi_eq_concat l r p q _]
  have hmid : crossPerm (a := zObj (p :: q :: r)) rfl
      (zHom (spliceNil r p q (cubeMerge (p : ℕ) (q : ℕ)))) = 1 := by
    rw [show zHom (spliceNil r p q (cubeMerge (p : ℕ) (q : ℕ)))
        = zHom (concatHomφ (zHom (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ)))) (𝟙 (zObj r))) from
      congrArg zHom (spliceNil_eq_concat r p q _)]
    exact crossPerm_concat_eq_one (crossPerm_pairMerge_cubeMerge p q)
      (crossPerm_id (zObj r) rfl) rfl
  exact crossPerm_concat_eq_one (crossPerm_id (zObj l) rfl) hmid h

/-- **A merge crosses nothing** — the generators do, and `crossPerm` is an anti-homomorphism. -/
theorem crossPerm_eq_one_of_W {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    {f : a ⟶ b} (hf : W K f) : crossPerm h f = 1 := by
  suffices hone : crossPerm (a := a) rfl f = 1 by
    refine Equiv.ext fun x => Fin.ext ?_
    rw [Equiv.Perm.one_apply,
      crossPerm_val_congr h rfl f (x' := Fin.cast h.symm x) rfl, hone]
    rfl
  clear h N
  induction hf with
  | of _ hm => exact crossPerm_eq_one_of_merge rfl hm
  | id x => exact crossPerm_id x rfl
  | comp_of u v _ hv ih =>
      rw [crossPerm_comp rfl u v, ih, crossPerm_eq_one_of_merge _ hv, mul_one]

/-- **…so a merge keeps the event order** — `crossPerm_eq_one_of_W`, read on positions. -/
theorem pos_coordMap_of_W {K : BPSet} {a b : Ch K} {f : a ⟶ b} (hf : W K f)
    (e : beadEvent a.dims) : (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  have hv := crossPerm_val (a := a) rfl f (e := e) (x := strand a.dims rfl e)
    (strand_val a.dims rfl e)
  rw [crossPerm_eq_one_of_W rfl hf, Equiv.Perm.one_apply, strand_val] at hv
  exact hv.symm

end ChainCat
