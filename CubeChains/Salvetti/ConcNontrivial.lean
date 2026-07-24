import CubeChains.Salvetti.ConcPure

/-!
# Salvetti/ConcNontrivial — the concurrency braid is nontrivial

The coarsest execution of `□ⁿ` (`n ≥ 2`) refined by a transposition-staircase to an all-edges
execution has a nonidentity crossing permutation (`permOf_tope`: the crossing is the change of
tope, and here that is the transposition itself).  Phrased in `RunWedge` so it feeds the
`K`-generic lift along the discrete opfibration `proj`.
-/

open CategoryTheory Equiv

namespace CubeChains

variable {n : ℕ}

/-- `permCast` carries the identity permutation to the identity. -/
theorem permCast_one {m k : ℕ} (h : m = k) : permCast h 1 = 1 := by subst h; rfl

/-- **The concurrency braid is nontrivial for `Ch⋆(□n)`, `n ≥ 2`.**  The coarsest execution,
refined by a transposition-staircase, has a nonidentity crossing permutation. -/
theorem exists_permOf_ne_one (hn : 2 ≤ n) :
    ∃ (x y : Ch⋆ (□n)) (f : x ⟶ y), permOf f ≠ 1 := by
  have hn0 : 0 < n := by omega
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  refine ⟨coarseExec hn0 1, fineExec (swap a b), coarseToFine hn0 1 (swap a b), fun hc => ?_⟩
  have htope := permOf_tope (coarseToFine hn0 1 (swap a b))
  rw [hc, permCast_one, tope_fineExec, tope_coarseExec, inv_one, mul_one] at htope
  -- htope : 1 = swap a b
  apply hab
  have h2 : (swap a b) a = (1 : Equiv.Perm (Fin n)) a := by rw [← htope]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h2
  exact h2.symm

/-- **`Flips` is nontrivial**, `K`-freely: a `RunWedge` refinement with a nonidentity crossing
permutation.  This is the witness the `proj`-opfibration lifts to any `K` with such an execution. -/
theorem exists_runWedge_permOf_ne_one :
    ∃ (X Y : RunWedge) (g : X ⟶ Y), RunWedge.permOf g ≠ 1 := by
  obtain ⟨x, y, f, hf⟩ := exists_permOf_ne_one (n := 2) le_rfl
  exact ⟨_, _, (proj (□2)).map f, hf⟩

/-- The coarsest `□2` execution refined by the transposition-staircase; the witness step 3 lifts. -/
noncomputable def cubeWitness : coarseExec (show (0 : ℕ) < 2 by norm_num) 1 ⟶
    fineExec (Equiv.swap (⟨0, by norm_num⟩ : Fin 2) ⟨1, by norm_num⟩) :=
  coarseToFine _ 1 (Equiv.swap ⟨0, by norm_num⟩ ⟨1, by norm_num⟩)

theorem permOf_cubeWitness_ne_one : permOf cubeWitness ≠ 1 := by
  set a : Fin 2 := ⟨0, by norm_num⟩
  set b : Fin 2 := ⟨1, by norm_num⟩
  intro hc
  have htope := permOf_tope cubeWitness
  rw [hc, permCast_one, cubeWitness, tope_fineExec, tope_coarseExec, inv_one, mul_one] at htope
  apply (show a ≠ b by simp [a, b, Fin.ext_iff])
  have h2 : (Equiv.swap a b) a = (1 : Equiv.Perm (Fin 2)) a := by rw [← htope]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h2
  exact h2.symm

/-- **`ConcPos K` is nontrivial for any `K` with a 2-cube** (`c : ⋁[2] ⟶ K`): lift the cube witness
along `proj K` — the target chain map is `g₀.1 ≫ c`, forced — so its crossing permutation is the
cube's, `≠ 1`.  Hence `Conc K` is a nonconstant functor on the fundamental groupoid. -/
theorem exists_permOf_ne_one_of_cube {K : BPSet}
    (c : ⋁((coarseExec (show (0 : ℕ) < 2 by norm_num) 1).chain.dims) ⟶ K) :
    ∃ (x y : Ch⋆ K) (f : x ⟶ y), permOf f ≠ 1 := by
  set g₀ := (proj (□2)).map cubeWitness with hg₀
  refine ⟨⟨op ⟨_, c⟩, (coarseExec (show (0 : ℕ) < 2 by norm_num) 1).2⟩,
    ⟨op ⟨_, g₀.1 ≫ c⟩, _⟩,
    ⟨(⟨g₀.1, rfl⟩ : (⟨_, g₀.1 ≫ c⟩ : Ch K) ⟶ ⟨_, c⟩).op, g₀.2⟩, ?_⟩
  exact permOf_cubeWitness_ne_one

end CubeChains
