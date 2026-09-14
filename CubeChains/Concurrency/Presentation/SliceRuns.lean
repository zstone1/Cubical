import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/SliceRuns — the arrows over a chain, and the exchange

One **geometric** fact, with nothing cube-specific in it: an arrow into `d` permutes each block of
`d` and no more (`index_crossPerm`), so a crossing at `k` says `k` and `k+1` share a block, which is
exactly the arrow out of the `k`-th atom shape.  The **exchange** `exists_run_mul_adjT` then says
that at a descent the shortened crossing permutation is realised by a run over `d` too.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

/-- An object of `Ch Zbp` is its own shape. -/
theorem eq_zObj (d : Ch Zbp) : zObj d.dims = d := Obj.eq_of_dims rfl

/-- **The runs are never all of the slice**: `Over (zObj [2])` has an object that is not a run —
`𝟙` on the one-bead chain of length `2`. -/
theorem exists_not_isRun_over :
    ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left :=
  ⟨Over.mk (𝟙 _), fun h => absurd (h 2 (List.mem_singleton_self 2)) (by decide)⟩

variable {d : Ch Zbp} {N : ℕ}

/-! ## The geometry: an arrow permutes each block and no more -/

/-- **An arrow permutes each block of its target and no more.**  Read the target in its own
standard chain: the source's firing order inverts `crossPerm` (`crossPerm_flatten`), and a
coarsening's beads are the target's blocks read in that order (`beadOf_of_hom`). -/
theorem index_crossPerm {c : Ch Zbp} (hd : dimSum d.dims = N) (hc : dimSum c.dims = N)
    (a : c ⟶ d) (r : Fin N) :
    ((dimComp d.dims hd).index (crossPerm hc a r) : ℕ) = ((dimComp d.dims hd).index r : ℕ) := by
  have hf : (⟨c.dims, a.φ ≫ stdChain hd⟩ : Ch (□N)) ⟶ ⟨d.dims, stdChain hd⟩ := ⟨a.φ, rfl⟩
  have hcross : ∀ q : Fin N,
      crossPerm hc a (flatten (⟨c.dims, a.φ ≫ stdChain hd⟩ : Ch (□N)) q) = q := fun q => by
    have h := crossPerm_flatten hc a (stdChain hd) q
    rwa [flatten_stdChain hd, Perm.one_apply] at h
  have hblock : ∀ q : Fin N, ((dimComp d.dims hd).index q : ℕ)
      = ((dimComp d.dims hd).index
          (flatten (⟨c.dims, a.φ ≫ stdChain hd⟩ : Ch (□N)) q) : ℕ) := fun q => by
    have h1 := beadOf_of_hom hf q
    rw [beadOf_stdChain hd q] at h1
    exact h1
  obtain ⟨q, rfl⟩ := (flatten (⟨c.dims, a.φ ≫ stdChain hd⟩ : Ch (□N))).surjective r
  rw [hcross q, hblock q]

/-- **Distinct blocks are ordered by their members** — `index_monotone` read as an iff. -/
theorem index_lt_iff_lt (hd : dimSum d.dims = N) {x y : Fin N}
    (hne : ((dimComp d.dims hd).index x : ℕ) ≠ ((dimComp d.dims hd).index y : ℕ)) :
    ((dimComp d.dims hd).index x : ℕ) < ((dimComp d.dims hd).index y : ℕ) ↔ x < y := by
  have hmono := (dimComp d.dims hd).index_monotone
  constructor
  · intro hlt
    by_contra hc
    have := hmono (not_lt.mp hc)
    dsimp only at this
    omega
  · intro hlt
    have := hmono (le_of_lt hlt)
    dsimp only at this
    omega

/-- **A crossing forces the cut to be interior**: two events in different blocks of `d` never
cross, so a descent of a run-arrow at `k` says that `k` and `k+1` share a block of `d`. -/
theorem index_adj_eq_of_descent (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d) {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    ((dimComp d.dims hd).index (adjLo k) : ℕ) = ((dimComp d.dims hd).index (adjHi k) : ℕ) := by
  have hmono := (dimComp d.dims hd).index_monotone
  have h1 := hmono (le_of_lt hdesc)
  have h2 := hmono (le_of_lt (show adjLo k < adjHi k by
    rw [Fin.lt_def, adjLo_val, adjHi_val]; omega))
  simp only [index_crossPerm hd (dimSum_replicate N) a] at h1
  dsimp only at h2
  omega

/-- **The `k`-th atom shape refines `d` exactly when `k`'s pair shares a block of `d`** — the
parabolic condition on `k`, which is all a cut over `d` may do. -/
theorem nonempty_atomComp_of_index (hd : dimSum d.dims = N) {k : Fin (N - 1)}
    (hsame : ((dimComp d.dims hd).index (adjLo k) : ℕ)
      = ((dimComp d.dims hd).index (adjHi k) : ℕ)) :
    Nonempty (zObj (atomComp N k) ⟶ d) := by
  refine nonempty_hom_of_index (a := zObj (atomComp N k)) (dimSum_atomComp N k) hd ?_
  intro x y hxy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
    exact Fin.ext hsame
  · rfl
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy.symm hgt
    exact Fin.ext hsame.symm

/-- …and a descent of a run-arrow is exactly that. -/
theorem nonempty_atomComp_of_descent (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d)
    {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    Nonempty (zObj (atomComp N k) ⟶ d) :=
  nonempty_atomComp_of_index hd (index_adj_eq_of_descent hd a hdesc)

/-! ## The exchange -/

/-- **At a descent, the shortened crossing permutation is realised too** —
`exists_crossPerm_of_blocks` at the run: the only pair `adjT k` reorders is `{k, k+1}`, which
`index_adj_eq_of_descent` puts inside a single block of `d`. -/
theorem exists_run_mul_adjT (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d) {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    ∃ a' : zObj (𝟙^N) ⟶ d,
      crossPerm (dimSum_replicate N) a' = crossPerm (dimSum_replicate N) a * adjT k := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ+, d = zObj l := ⟨d.dims, (eq_zObj d).symm⟩
  have hsame := index_adj_eq_of_descent hd a hdesc
  have hblk : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index
      ((crossPerm (dimSum_replicate N) a)⁻¹ x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    have h := index_crossPerm hd (dimSum_replicate N) a
      ((crossPerm (dimSum_replicate N) a)⁻¹ x)
    simpa using h.symm
  have hadj : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index (adjT k x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    by_cases h1 : (x : ℕ) = (k : ℕ)
    · rw [show x = adjLo k from Fin.ext (by rw [adjLo_val]; exact h1), adjT_lo, hsame]
    by_cases h2 : (x : ℕ) = (k : ℕ) + 1
    · rw [show x = adjHi k from Fin.ext (by rw [adjHi_val]; exact h2), adjT_hi, hsame]
    · rw [adjT_of_ne _ h1 h2]
  have hinv : ∀ x : Fin N, ((dimComp (zObj l).dims hd).index
      ((crossPerm (dimSum_replicate N) a * adjT k)⁻¹ x) : ℕ)
      = ((dimComp (zObj l).dims hd).index x : ℕ) := fun x => by
    rw [mul_inv_rev, adjT_inv, Perm.mul_apply, hadj, hblk]
  obtain ⟨f, hf⟩ := exists_crossPerm_of_blocks (dimSum_replicate N) hd
    (crossPerm (dimSum_replicate N) a * adjT k)
    (fun p q hpq hlt => by
      have h := congrArg Fin.val hpq
      rw [index_ones, index_ones] at h
      exact absurd (((crossPerm (dimSum_replicate N) a * adjT k)⁻¹).injective (Fin.ext h))
        (ne_of_lt hlt))
    (fun p q hne => by
      rw [index_ones, index_ones, ← hinv p, ← hinv q]
      exact (index_lt_iff_lt hd (by rw [hinv p, hinv q]; exact hne)).trans Fin.lt_def)
  exact ⟨f, hf⟩

end ChainCat
