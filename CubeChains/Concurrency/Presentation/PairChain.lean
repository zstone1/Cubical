import CubeChains.Concurrency.Presentation.TopRefinement
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Machinery.Braid.Generated

/-!
# Concurrency/Presentation/PairChain — the codimension-two chain of two cuts

Two atoms meeting in one chain **determine** it: a codimension-one refinement erases exactly its
own junction (`boundaries_eq_erase`), so a chain receiving both atoms has lost both junctions and
nothing else.  Hence `pairChain`, the shape of the square (`i + 1 < j`) or of the hexagon
(`j = i + 1`), and `eq_pairChain`, which is what lets a cell over it be pushed into *every* chain
where its two atoms act.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-! ## The shape is forced -/

/-- **A chain below both atoms has lost exactly their two junctions.** -/
theorem boundaries_pairApex {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) {w : Ch Zbp}
    (u : zObj (atomComp n i) ⟶ w) (hu : codim u = 1)
    (v : zObj (atomComp n j) ⟶ w) :
    boundaries w.dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
  obtain ⟨t, ht⟩ := exists_cutsOf_eq_singleton hu
  have hw : boundaries w.dims = (boundaries (atomComp n i)).erase t := boundaries_eq_erase ht
  have hjmem : (j : ℕ) + 1 ∈ boundaries (atomComp n i) := by
    rw [boundaries_atomComp, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    have := j.isLt
    omega
  have hjnot : (j : ℕ) + 1 ∉ boundaries w.dims := fun hmem => by
    have := boundaries_subset_of_hom v hmem
    rw [zObj_dims, boundaries_atomComp, Finset.mem_sdiff, Finset.mem_singleton] at this
    exact this.2 rfl
  obtain rfl : t = (j : ℕ) + 1 := by
    by_contra hne
    exact hjnot (hw ▸ Finset.mem_erase.mpr ⟨hne ∘ Eq.symm, hjmem⟩)
  rw [hw, boundaries_atomComp]
  ext s
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

/-! ## The chain itself -/

/-- The shape of the codimension-two chain the cuts `i` and `j` share. -/
noncomputable def pairShape (n : ℕ) (i j : Fin (n - 1)) (hij : (i : ℕ) ≠ (j : ℕ)) : List ℕ+ :=
  (exists_pairCell i j hij).choose.dims

/-- **The codimension-two chain the cuts `i` and `j` share** — a square when they are far apart, a
hexagon when they are adjacent. -/
noncomputable def pairChain (n : ℕ) (i j : Fin (n - 1)) (hij : (i : ℕ) ≠ (j : ℕ)) : Ch Zbp :=
  zObj (pairShape n i j hij)

variable {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))

theorem pairChain_eq_choose : pairChain n i j hij = (exists_pairCell i j hij).choose :=
  Obj.eq_of_dims rfl


theorem dimSum_pairShape : dimSum (pairShape n i j hij) = n :=
  (exists_pairCell i j hij).choose_spec.1

theorem dimSum_pairChain : dimSum (pairChain n i j hij).dims = n := dimSum_pairShape hij

theorem degree_pairChain : degree (pairChain n i j hij) = 2 :=
  (pairChain_eq_choose hij) ▸ (exists_pairCell i j hij).choose_spec.2.1

theorem nonempty_left_pairChain : Nonempty (zObj (atomComp n i) ⟶ pairChain n i j hij) :=
  (pairChain_eq_choose hij) ▸ (exists_pairCell i j hij).choose_spec.2.2.1

theorem nonempty_right_pairChain : Nonempty (zObj (atomComp n j) ⟶ pairChain n i j hij) :=
  (pairChain_eq_choose hij) ▸ (exists_pairCell i j hij).choose_spec.2.2.2

/-- **A chain of degree two below both atoms is the pair chain** — `boundaries` is injective. -/
theorem eq_pairChain {w : Ch Zbp} (hdeg : degree w = 2)
    (hi : Nonempty (zObj (atomComp n i) ⟶ w)) (hj : Nonempty (zObj (atomComp n j) ⟶ w)) :
    w = pairChain n i j hij := by
  obtain ⟨u⟩ := hi
  obtain ⟨v⟩ := hj
  obtain ⟨u'⟩ := nonempty_left_pairChain hij
  obtain ⟨v'⟩ := nonempty_right_pairChain hij
  have hcu : codim u = 1 := by rw [codim, hdeg, degree_atomComp]
  have hcu' : codim u' = 1 := by rw [codim, degree_pairChain hij, degree_atomComp]
  exact Obj.eq_of_dims (boundaries_injective
    ((boundaries_pairApex hij u hcu v).trans (boundaries_pairApex hij u' hcu' v').symm))

/-- **The pair chain's own junctions.** -/
theorem boundaries_pairChain :
    boundaries (pairChain n i j hij).dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
  obtain ⟨u⟩ := nonempty_left_pairChain hij
  obtain ⟨v⟩ := nonempty_right_pairChain hij
  exact boundaries_pairApex hij u (by rw [codim, degree_pairChain hij, degree_atomComp]) v

/-! ## Its beads, and the leg it has into every chain where both cuts act

A bead of the pair chain is crossed only at `i` or at `j`, so both the comparison the hom-set asks
for and the ascent condition `exists_crossPerm_single` asks for are statements about those two
cuts alone — and the action supplies both. -/

/-- **Two coordinates share a bead of the pair chain only across `i` or across `j`.** -/
theorem pairChain_bead {x y : Fin n}
    (h : ((dimComp (pairChain n i j hij).dims (dimSum_pairChain hij)).index x : ℕ)
      = ((dimComp (pairChain n i j hij).dims (dimSum_pairChain hij)).index y : ℕ))
    {t : ℕ} (h1 : (x : ℕ) < t) (h2 : t ≤ (y : ℕ)) : t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1 := by
  have hno : ¬ ∃ s ∈ boundaries (pairChain n i j hij).dims, (x : ℕ) < s ∧ s ≤ (y : ℕ) := by
    rw [← beadAt_lt_iff, beadAt_eq_index_succ (dimSum_pairChain hij) x,
      beadAt_eq_index_succ (dimSum_pairChain hij) y]
    omega
  have hmem : t ∉ boundaries (pairChain n i j hij).dims := fun hc => hno ⟨t, hc, h1, h2⟩
  rw [boundaries_pairChain hij, Finset.mem_sdiff] at hmem
  have hy := y.isLt
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, not_and, not_not] at hmem
  exact hmem (by omega)

/-- **A leg from the pair chain into every chain where both cuts act**, carrying the merge run to
the given one: the two cuts are the only place a bead of the pair chain can be crossed, so the
ascents are the whole of `exists_crossPerm_single`'s hypothesis. -/
theorem exists_pairLeg {d : Ch Zbp} (hd : dimSum d.dims = n) {σ : Perm (Fin n)}
    (hbead : ∀ k : Fin (n - 1), (k : ℕ) = (i : ℕ) ∨ (k : ℕ) = (j : ℕ) →
      ((dimComp d.dims hd).index (adjLo k) : ℕ) = ((dimComp d.dims hd).index (adjHi k) : ℕ))
    (hasc : ∀ k : Fin (n - 1), (k : ℕ) = (i : ℕ) ∨ (k : ℕ) = (j : ℕ) → σ (adjLo k) < σ (adjHi k))
    {a : zObj (𝟙^n) ⟶ d} (ha : crossPerm (dimSum_replicate n) a = σ) :
    ∃ t : pairChain n i j hij ⟶ d, crossPerm (dimSum_pairChain hij) t = σ := by
  have hn : 0 < n := by have := i.isLt; omega
  -- a bead of the pair chain is a bead of `d`
  have hcoarse : ∀ x y : Fin n,
      (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index x
        = (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index y →
      (dimComp d.dims hd).index x = (dimComp d.dims hd).index y := by
    have key : ∀ x y : Fin n, (x : ℕ) < (y : ℕ) →
        (∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1) →
        ((dimComp d.dims hd).index x : ℕ) = ((dimComp d.dims hd).index y : ℕ) :=
      rel_of_span (P := fun t => t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1)
        (R := fun p q => ((dimComp d.dims hd).index p : ℕ) = ((dimComp d.dims hd).index q : ℕ))
        (fun _ _ _ h h' => h.trans h') fun k hk => hbead k (by omega)
    intro x y h
    refine Fin.ext ?_
    rcases lt_trichotomy (x : ℕ) (y : ℕ) with hlt | heq | hgt
    · exact key x y hlt fun _ => pairChain_bead hij (congrArg Fin.val h)
    · exact congrArg _ (congrArg _ (Fin.ext heq))
    · exact (key y x hgt fun _ => pairChain_bead hij (congrArg Fin.val h.symm)).symm
  -- and `σ` ascends across every one of them
  have hinc : ∀ x y : Fin n,
      (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index x
        = (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index y →
      x < y → σ x < σ y := fun x y h hxy =>
    rel_of_span (P := fun t => t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1) (R := fun p q => σ p < σ q)
      (fun _ _ _ => lt_trans) (fun k hk => hasc k (by omega)) x y (Fin.lt_def.mp hxy)
      fun _ => pairChain_bead hij (congrArg Fin.val h)
  -- the two extremes, and interpolation
  obtain ⟨g, hg⟩ := exists_crossPerm_single (a := pairShape n i j hij)
    (dimSum_pairShape hij) (m := (⟨n, hn⟩ : ℕ+)) rfl hinc
  obtain ⟨s, hs⟩ := exists_crossPerm_eq_one hd
    (nonempty_hom_single (m := (⟨n, hn⟩ : ℕ+)) (hd.trans rfl))
  have hab : Nonempty (pairChain n i j hij ⟶ d) :=
    nonempty_hom_of_index (dimSum_pairShape hij) hd hcoarse
  exact exists_crossPerm_mid (o := zObj (𝟙^n)) (z := zObj [(⟨n, hn⟩ : ℕ+)])
    (t := runMerge (pairChain n i j hij) (dimSum_pairChain hij))
    (crossPerm_eq_one_of_W _ (W_runMerge _ _)) hs hab ha hg

-- Sealed once characterised: the shape is a `Classical.choice`, and the unifier must not evaluate
-- it.  `boundaries_pairChain` and `eq_pairChain` are all a caller needs.
attribute [irreducible] pairShape


/-! ## The two species of the pair chain

`boundaries` pins a shape, and the pair chain's boundaries are the run's minus `i+1` and `j+1` — so
consecutive cuts leave one bead of three and cuts apart two of two.  The capacity of each is then a
computation, not a discriminant. -/

/-- **Consecutive cuts share a hexagon** — one bead of three, and edges either side. -/
theorem dims_pairChain_of_adj (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    ∃ p q : ℕ, (pairChain n i j hij).dims = 𝟙^p ++ (3 : ℕ+) :: 𝟙^q := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hadj with h | h
  · refine ⟨(i : ℕ), n - (i : ℕ) - 3, boundaries_injective ?_⟩
    rw [boundaries_pairChain hij, boundaries_three_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  · refine ⟨(j : ℕ), n - (j : ℕ) - 3, boundaries_injective ?_⟩
    rw [boundaries_pairChain hij, boundaries_three_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega

/-- **Cuts that are apart share a square** — two beads of two, with edges between and around. -/
theorem dims_pairChain_of_apart (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    ∃ p m q : ℕ,
      (pairChain n i j hij).dims = 𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q) := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hfar with h | h
  · refine ⟨(i : ℕ), (j : ℕ) - (i : ℕ) - 2, n - (j : ℕ) - 2, boundaries_injective ?_⟩
    rw [boundaries_pairChain hij, boundaries_two_two_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  · refine ⟨(j : ℕ), (i : ℕ) - (j : ℕ) - 2, n - (i : ℕ) - 2, boundaries_injective ?_⟩
    rw [boundaries_pairChain hij, boundaries_two_two_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega

/-- **The hexagon's capacity is three.** -/
theorem crossCap_pairChain_of_adj (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    crossCap (pairChain n i j hij).dims = 3 := by
  obtain ⟨p, q, hd⟩ := dims_pairChain_of_adj hij hadj
  rw [hd, crossCap_three_bead]

/-- **…and the square's is two.** -/
theorem crossCap_pairChain_of_apart (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    crossCap (pairChain n i j hij).dims = 2 := by
  obtain ⟨p, m, q, hd⟩ := dims_pairChain_of_apart hij hfar
  rw [hd, crossCap_two_two_bead]

/-- **A refinement of the pair chain out of the run as long as the pair's order is its greatest
one** — the capacity bounds every refinement out of a run and is attained only at the reversals, so
one comparison of lengths names the complement of the merge below. -/
private theorem isTop_of_permLen {wi : zObj (atomComp n i) ⟶ pairChain n i j hij}
    {σ : Perm (Fin n)} (htop : crossPerm (dimSum_replicate n) (atomOnes n i ≫ wi) = σ)
    (hcap : permLen σ = crossCap (pairChain n i j hij).dims) :
    Paper.IsTop (atomOnes n i ≫ wi) :=
  (Paper.isTop_iff_permLen (X := ⟨zObj (𝟙^n), fun _ hd => List.eq_of_mem_replicate hd⟩)
      (atomOnes n i ≫ wi)).mpr
    ((permLen_crossPerm (dimSum_replicate n) (dimSum_eq_of_hom (atomOnes n i ≫ wi))
        (atomOnes n i ≫ wi)).trans ((congrArg permLen htop).trans hcap))

/-- **The greatest cut of the pair chain is the longest word its two cuts spell**, and its two
one-cut factorisations are the legs `wi`, `wj`: two letters when the cuts are apart, three when they
are consecutive — the Coxeter exponent either way.

This is the one place the route reads the codimension-two dichotomy; everything above it is stated
at the order of the pair. -/
theorem exists_pairTop {σ : Perm (Fin n)} (hσi : σ (adjHi i) < σ (adjLo i))
    (hσj : σ (adjHi j) < σ (adjLo j)) (hlen : permLen σ = orderOf (adjT i * adjT j)) :
    ∃ (wi : zObj (atomComp n i) ⟶ pairChain n i j hij)
      (wj : zObj (atomComp n j) ⟶ pairChain n i j hij),
      σ⁻¹ = σ ∧
      crossPerm (dimSum_atomComp n i) wi = σ * adjT i ∧
      crossPerm (dimSum_atomComp n j) wj = σ * adjT j ∧
      Paper.IsTop (atomOnes n i ≫ wi) := by
  have hE : dimSum (pairChain n i j hij).dims = n := dimSum_pairChain hij
  obtain ⟨mi, -, hui⟩ := exists_merge_leg i (nonempty_left_pairChain hij)
  obtain ⟨mj, -, huj⟩ := exists_merge_leg j (nonempty_right_pairChain hij)
  rcases orderOf_adjT_mul_adjT_cases hij with ⟨hfar, hcox⟩ | ⟨hadj, hcox⟩
  · -- apart: the square, `σ = adjT j * adjT i`
    have hcomm := adjT_comm_of_apart hfar
    have hσeq : σ = adjT j * adjT i := by
      have hlen2 : permLen σ = 2 := hlen.trans hcox
      rcases hfar with h | h
      · exact eq_adjT_mul_adjT_of_descents h hσi hσj hlen2
      · exact (eq_adjT_mul_adjT_of_descents h hσj hσi hlen2).trans hcomm
    obtain ⟨wi, hwi⟩ := exists_leg i hE (nonempty_left_pairChain hij) (σ := adjT j)
      (adjT_ascent_of_ne hij) huj
    obtain ⟨wj, hwj⟩ := exists_leg j hE (nonempty_right_pairChain hij) (σ := adjT i)
      (adjT_ascent_of_ne (Ne.symm hij)) hui
    refine ⟨wi, wj, ?_, hwi.trans ?_, hwj.trans ?_, ?_⟩
    · rw [hσeq, mul_inv_rev]
      simp only [adjT_inv]
      exact hcomm
    · rw [hσeq, mul_assoc, adjT_mul_self, mul_one]
    · rw [hσeq, mul_assoc, hcomm, ← mul_assoc, adjT_mul_self, one_mul]
    · refine isTop_of_permLen hij ?_ (by rw [hlen, hcox, crossCap_pairChain_of_apart hij hfar])
      rw [crossPerm_comp, hwi, crossPerm_atomOnes, hσeq]
  · -- consecutive: the hexagon, `σ = adjT i * adjT j * adjT i`
    have hbraid := adjT_braid_of_adj hadj
    have hσeq : σ = adjT i * adjT j * adjT i := by
      have hlen3 : permLen σ = 3 := hlen.trans hcox
      rcases hadj with h | h
      · exact eq_braid_of_descents h hσi hσj hlen3
      · exact (eq_braid_of_descents h hσj hσi hlen3).trans hbraid.symm
    have hσi' : σ * adjT i = adjT i * adjT j := by
      rw [hσeq, mul_assoc (adjT i * adjT j), adjT_mul_self, mul_one]
    have hσj' : σ * adjT j = adjT j * adjT i := by
      rw [hσeq, hbraid, mul_assoc (adjT j * adjT i), adjT_mul_self, mul_one]
    obtain ⟨wj₁, hwj₁⟩ := exists_leg j hE (nonempty_right_pairChain hij) (σ := adjT i)
      (adjT_ascent_of_ne (Ne.symm hij)) hui
    obtain ⟨wi₁, hwi₁⟩ := exists_leg i hE (nonempty_left_pairChain hij) (σ := adjT j)
      (adjT_ascent_of_ne hij) huj
    obtain ⟨wi, hwi⟩ := exists_leg i hE (nonempty_left_pairChain hij)
      (σ := adjT i * adjT j) (adjT_mul_adjT_ascent hadj) (u := atomOnes n j ≫ wj₁)
      (by rw [crossPerm_comp, hwj₁, crossPerm_atomOnes])
    obtain ⟨wj, hwj⟩ := exists_leg j hE (nonempty_right_pairChain hij)
      (σ := adjT j * adjT i) (adjT_mul_adjT_ascent hadj.symm) (u := atomOnes n i ≫ wi₁)
      (by rw [crossPerm_comp, hwi₁, crossPerm_atomOnes])
    refine ⟨wi, wj, ?_, hwi.trans hσi'.symm, hwj.trans hσj'.symm, ?_⟩
    · rw [hσeq, mul_inv_rev, mul_inv_rev]
      simp only [adjT_inv]
      rw [← mul_assoc]
    have htop : crossPerm (dimSum_replicate n) (atomOnes n i ≫ wi) = σ := by
      rw [crossPerm_comp, hwi, crossPerm_atomOnes]
      exact hσeq.symm
    exact isTop_of_permLen hij htop (by rw [hlen, hcox, crossCap_pairChain_of_adj hij hadj])

end ChainCat
