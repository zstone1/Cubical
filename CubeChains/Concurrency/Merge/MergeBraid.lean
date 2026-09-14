import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid

/-!
# Concurrency/Merge/MergeBraid — the crossing permutation of a splice

`crossPerm` is **monoidal over the wedge** (`crossPerm_chConcat`), and a splice `𝟙 ∨ w ∨ 𝟙` is a
concatenation twice over (`zHom_splicePhi_eq`, `zHom_spliceNil_eq`), so its crossing permutation is
the block sum `1 ⊕ crossPerm w ⊕ 1`: the beads flanking a cut keep their strand and only the merged
block moves, by the staircase's own crossing.

At `w = cubeReorder` that block sum is the Garside atom (`Concurrency/Merge/Atom`), which is the one
place a permutation is named; at `w = cubeMerge` it is trivial, and that is read off flatness
instead (`Concurrency/Merge/Flat`).
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

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

end ChainCat
