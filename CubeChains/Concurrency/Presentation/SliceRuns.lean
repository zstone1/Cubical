import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Merge.Atom
import CubeChains.Machinery.Braid.RankTwo

/-!
# Concurrency/Presentation/SliceRuns — the arrows out of a run: the merge, the atoms, the exchange

One **geometric** fact, with nothing cube-specific in it: an arrow into `d` permutes each block of
`d` and no more (`index_crossPerm`), so a crossing at `k` says `k` and `k+1` share a block, which is
exactly the arrow out of the `k`-th atom shape.  The **exchange** `exists_run_mul_adjT` then says
that at a descent the shortened crossing permutation is realised by a run over `d` too; a run that
rises along the beads of a shape below `d` factors through it (`exists_crossPerm_of_rise`); and out
of the run a codimension-one refinement is the merge or the atom at one cut.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

/-! ## The merge out of the run -/

/-- **An arrow out of the all-ones chain pins the strand count.** -/
theorem dimSum_eq_of_onesHom {N : ℕ} {b : Ch Zbp} (r : zObj (𝟙^N) ⟶ b) : dimSum b.dims = N :=
  (dimSum_eq_of_hom r).symm.trans (dimSum_replicate N)

/-- **The merge from the run on `N` events** — every chain on `N` events is entered from it, in
exactly one crossing-free way. -/
noncomputable def runMerge {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) : zObj (𝟙^N) ⟶ b :=
  (exists_W_from_ones b hb).choose

theorem W_runMerge {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) : W Zbp (runMerge b hb) :=
  (exists_W_from_ones b hb).choose_spec

theorem crossPerm_runMerge {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    crossPerm (dimSum_replicate N) (runMerge s hs) = 1 :=
  crossPerm_eq_one_of_W _ (W_runMerge _ _)

/-- **A merge out of the run is the only one** — `eq_of_W` pins it by its endpoints. -/
theorem eq_runMerge {N : ℕ} {b : Ch Zbp} (hb : dimSum b.dims = N) {f : zObj (𝟙^N) ⟶ b}
    (hf : W Zbp f) : f = runMerge b hb :=
  eq_of_W hf (W_runMerge b hb)

/-- The merge that runs alongside the `k`-th atom. -/
noncomputable def mergeOnes (N : ℕ) (k : Fin (N - 1)) : zObj (𝟙^N) ⟶ zObj (atomComp N k) :=
  runMerge (zObj (atomComp N k)) (dimSum_atomComp N k)

theorem W_mergeOnes (N : ℕ) (k : Fin (N - 1)) : W Zbp (mergeOnes N k) :=
  W_runMerge _ _

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

/-- **…and a descent of a run-arrow is an atom over `d`** — the `k`-th atom shape refines `d`
exactly when `k`'s pair shares a block of `d`, the junction `k + 1` not being one of `d`'s. -/
theorem nonempty_atomComp_of_descent (hd : dimSum d.dims = N) (a : zObj (𝟙^N) ⟶ d)
    {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) a (adjHi k)
      < crossPerm (dimSum_replicate N) a (adjLo k)) :
    Nonempty (zObj (atomComp N k) ⟶ d) :=
  nonempty_hom_iff.mpr ⟨(dimSum_atomComp N k).trans hd.symm, fun t ht => by
    have hsame := index_adj_eq_of_descent hd a hdesc
    rw [zObj_dims, boundaries_atomComp, Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_singleton]
    refine ⟨Nat.lt_succ_of_le (hd ▸ le_dimSum_of_mem_boundaries ht), fun htk => ?_⟩
    have := (index_lt_iff_mem_boundaries hd (adjLo k) (adjHi k)).mpr
      ⟨t, ht, by rw [adjLo_val]; omega, by rw [adjHi_val]; omega⟩
    omega⟩

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

/-! ## Legs out of a shape below `d` -/

/-- **A run into `d` factors through a shape below `d` along which it rises** — realised into one
bead (`exists_crossPerm_single`) and at the run, hence in the middle (`exists_crossPerm_mid`). -/
theorem exists_crossPerm_of_rise {p : List ℕ+} (hp : dimSum p = N) (hpd : Nonempty (zObj p ⟶ d))
    {σ : Perm (Fin N)}
    (hrise : ∀ x y : Fin N, (dimComp p hp).index x = (dimComp p hp).index y → x < y → σ x < σ y)
    {a : zObj (𝟙^N) ⟶ d} (ha : crossPerm (dimSum_replicate N) a = σ) :
    ∃ t : zObj p ⟶ d, crossPerm hp t = σ := by
  rcases Nat.eq_zero_or_pos N with rfl | hn
  · exact ⟨hpd.some, Subsingleton.elim _ _⟩
  have hd := dimSum_eq_of_onesHom a
  obtain ⟨g, hg⟩ := exists_crossPerm_single hp (m := (⟨N, hn⟩ : ℕ+)) rfl hrise
  obtain ⟨z, hz⟩ := exists_crossPerm_eq_one hd (nonempty_hom_single (m := (⟨N, hn⟩ : ℕ+)) hd)
  exact exists_crossPerm_mid (t := runMerge (zObj p) hp) (crossPerm_runMerge _ _) hz hpd ha hg

/-- **One crossing step**: a run that ascends across the `k`-th cut factors through the `k`-th
merge, and crossing instead lengthens it by that atom. -/
theorem exists_atom_step {k : Fin (N - 1)} (hnk : Nonempty (zObj (atomComp N k) ⟶ d))
    {t : zObj (𝟙^N) ⟶ d} {σ : Perm (Fin N)} (hσ : crossPerm (dimSum_replicate N) t = σ)
    (hasc : σ (adjLo k) < σ (adjHi k)) :
    ∃ w : zObj (atomComp N k) ⟶ d, mergeOnes N k ≫ w = t ∧
      crossPerm (dimSum_replicate N) (atomOnes N k ≫ w) = σ * adjT k := by
  obtain ⟨w, hw⟩ := exists_crossPerm_of_rise (dimSum_atomComp N k) hnk (fun x y hxy hlt => by
    obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
    exact hasc) hσ
  refine ⟨w, hom_ext_of_crossPerm (h := dimSum_replicate N) ?_, ?_⟩
  · rw [crossPerm_comp, crossPerm_eq_one_of_W _ (W_mergeOnes N k), mul_one]
    exact hw.trans hσ.symm
  · rw [crossPerm_comp, crossPerm_atomOnes]
    exact congrArg (· * adjT k) hw

/-! ## The codimension-one refinements out of the run

A shape is its junction set, so out of the run a codimension-one refinement cuts one junction and
lands on an atom's shape; there a descent would be an atom reaching that shape, so it crosses at
most the atom's own cut. -/

/-- **A codimension-one refinement of the run lands on an atom's shape.** -/
theorem exists_atomComp {c : Ch Zbp} (f : zObj (𝟙^N) ⟶ c) (hcod : codim f = 1) :
    ∃ k : Fin (N - 1), c = zObj (atomComp N k) := by
  obtain ⟨t, ht⟩ := exists_cutsOf_eq_singleton hcod
  have htN := Finset.mem_Ioo.mp (cutsOf_ones_subset f (ht ▸ Finset.mem_singleton_self t))
  refine ⟨⟨t - 1, by omega⟩, Obj.eq_of_dims (boundaries_injective ?_)⟩
  rw [boundaries_eq_erase ht, zObj_dims, zObj_dims, boundaries_ones, boundaries_atomComp,
    Finset.erase_eq]
  simp only [show t - 1 + 1 = t by omega]

/-- **An atom reaches another atom's shape only if it is that atom** — the shapes drop one junction
each. -/
theorem eq_of_nonempty_atomComp {i k : Fin (N - 1)}
    (h : Nonempty (zObj (atomComp N i) ⟶ zObj (atomComp N k))) : i = k := by
  have hsub := (nonempty_hom_iff.mp h).2
  simp only [zObj_dims, boundaries_atomComp] at hsub
  have hi := i.isLt
  by_contra hne
  have := @hsub ((i : ℕ) + 1) (by
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    exact ⟨by omega, fun h => hne (Fin.ext (by omega))⟩)
  simp at this

/-- **Distinct atoms cut distinct shapes.** -/
theorem atomComp_ne {i j : Fin (N - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    zObj (atomComp N i) ≠ zObj (atomComp N j) :=
  fun h => hij (congrArg Fin.val (eq_of_nonempty_atomComp ⟨eqToHom h⟩))

/-- **Out of the run, a refinement onto an atom's shape is the merge or the atom** — every descent
of it is at the atom's cut, and after the exchange there none is left. -/
theorem eq_mergeOnes_or_atomOnes (k : Fin (N - 1)) (u : zObj (𝟙^N) ⟶ zObj (atomComp N k)) :
    u = mergeOnes N k ∨ u = atomOnes N k := by
  have hd := dimSum_atomComp N k
  have hk : ∀ (v : zObj (𝟙^N) ⟶ zObj (atomComp N k)) (j : Fin (N - 1)),
      crossPerm (dimSum_replicate N) v (adjHi j) < crossPerm (dimSum_replicate N) v (adjLo j) →
        j = k :=
    fun v j hj => eq_of_nonempty_atomComp (nonempty_atomComp_of_descent hd v hj)
  by_cases h1 : crossPerm (dimSum_replicate N) u = 1
  · exact Or.inl (eq_runMerge hd ((W_iff_crossPerm_eq_one _ u).mpr h1))
  obtain ⟨j, hj⟩ := exists_adjacent_descent _
    (Nat.pos_of_ne_zero fun h0 => h1 (eq_one_of_permLen_eq_zero _ h0))
  obtain rfl := hk u j hj
  obtain ⟨v, hv⟩ := exists_run_mul_adjT hd u hj
  have hv1 : crossPerm (dimSum_replicate N) v = 1 :=
    eq_one_of_no_adjacent_descent _ fun i hi => by
      obtain rfl := hk v i hi
      rw [hv] at hi
      exact absurd hi (not_lt.mpr (adjT_ascent_of_descent hj).le)
  refine Or.inr (hom_ext_of_crossPerm (h := dimSum_replicate N) ?_)
  rw [crossPerm_atomOnes, ← mul_adjT_adjT (crossPerm (dimSum_replicate N) u) j, ← hv, hv1,
    one_mul]

/-- **…and at that shape, a non-merge out of the run is the atom.** -/
theorem eq_atomOnes {k : Fin (N - 1)} {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)}
    (hnot : ¬ W Zbp f) : f = atomOnes N k :=
  (eq_mergeOnes_or_atomOnes k f).resolve_left fun h => hnot (by rw [h]; exact W_mergeOnes N k)

end ChainCat
