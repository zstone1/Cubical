import CubeChains.Concurrency.Presentation.LocPresentation

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

@[simp] theorem dims_pairChain : (pairChain n i j hij).dims = pairShape n i j hij := rfl

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
  have hb : beadAt (pairChain n i j hij).dims x = beadAt (pairChain n i j hij).dims y :=
    (index_eq_iff_beadAt (dimSum_pairChain hij) x y).mp h
  have hno : ¬ ∃ s ∈ boundaries (pairChain n i j hij).dims, (x : ℕ) < s ∧ s ≤ (y : ℕ) := by
    rw [← beadAt_lt_iff]; omega
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
  -- the two cuts, as elements of `Fin (n-1)`
  have hcut : ∀ {t : ℕ}, t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1 →
      ∃ k : Fin (n - 1), ((k : ℕ) = (i : ℕ) ∨ (k : ℕ) = (j : ℕ)) ∧ t = (k : ℕ) + 1 := by
    rintro t (rfl | rfl)
    · exact ⟨i, Or.inl rfl, rfl⟩
    · exact ⟨j, Or.inr rfl, rfl⟩
  -- a relation holding across each of the two cuts holds across a whole bead
  have hspan : ∀ R : Fin n → Fin n → Prop,
      (∀ k : Fin (n - 1), (k : ℕ) = (i : ℕ) ∨ (k : ℕ) = (j : ℕ) → R (adjLo k) (adjHi k)) →
      (∀ a b c : Fin n, R a b → R b c → R a c) →
      ∀ (l : ℕ) (x y : Fin n), (y : ℕ) = (x : ℕ) + l + 1 →
        (∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1) → R x y := by
    intro R hbase htrans l
    induction l with
    | zero =>
        intro x y hy hall
        obtain ⟨k, hk, hsk⟩ := hcut (hall (y : ℕ) (by omega) le_rfl)
        have e1 : x = adjLo k := Fin.ext (by rw [adjLo_val]; omega)
        have e2 : y = adjHi k := Fin.ext (by rw [adjHi_val]; omega)
        rw [e1, e2]; exact hbase k hk
    | succ l ih =>
        intro x y hy hall
        have hlt : (x : ℕ) + l + 1 < n := by have := y.isLt; omega
        refine htrans x ⟨(x : ℕ) + l + 1, hlt⟩ y
          (ih x ⟨(x : ℕ) + l + 1, hlt⟩ rfl fun t h1 h2 => hall t h1
            (by have h2' : t ≤ (x : ℕ) + l + 1 := h2; omega)) ?_
        obtain ⟨k, hk, hsk⟩ := hcut (hall (y : ℕ) (by omega) le_rfl)
        have e1 : (⟨(x : ℕ) + l + 1, hlt⟩ : Fin n) = adjLo k :=
          Fin.ext (by rw [adjLo_val]; change (x : ℕ) + l + 1 = (k : ℕ); omega)
        have e2 : y = adjHi k := Fin.ext (by rw [adjHi_val]; omega)
        rw [e1, e2]; exact hbase k hk
  -- a bead of the pair chain is a bead of `d`
  have hcoarse : ∀ x y : Fin n,
      (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index x
        = (dimComp (pairShape n i j hij) (dimSum_pairShape hij)).index y →
      (dimComp d.dims hd).index x = (dimComp d.dims hd).index y := by
    have key : ∀ x y : Fin n, (x : ℕ) < (y : ℕ) →
        (∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1) →
        ((dimComp d.dims hd).index x : ℕ) = ((dimComp d.dims hd).index y : ℕ) :=
      fun x y hxy hall => hspan
        (fun p q => ((dimComp d.dims hd).index p : ℕ) = ((dimComp d.dims hd).index q : ℕ))
        hbead (fun _ _ _ h h' => Eq.trans h h') ((y : ℕ) - (x : ℕ) - 1) x y (by omega) hall
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
    hspan (fun p q => σ p < σ q) hasc (fun _ _ _ => lt_trans) ((y : ℕ) - (x : ℕ) - 1) x y
      (by have : (x : ℕ) < (y : ℕ) := hxy; omega)
      fun _ => pairChain_bead hij (congrArg Fin.val h)
  -- the two extremes, and interpolation
  obtain ⟨g, hg⟩ := exists_crossPerm_single (a := pairShape n i j hij)
    (dimSum_pairShape hij) (m := (⟨n, hn⟩ : ℕ+)) rfl hinc
  obtain ⟨s, hs⟩ := exists_crossPerm_eq_one hd
    ((nonempty_hom_single (m := (⟨n, hn⟩ : ℕ+)) (hd.trans rfl)).map
      fun v => eqToHom (Obj.eq_of_dims (b := zObj d.dims) rfl) ≫ v)
  have hab : Nonempty (pairChain n i j hij ⟶ d) :=
    (nonempty_hom_of_index (dimSum_pairShape hij) hd hcoarse).map fun v =>
      v ≫ eqToHom (Obj.eq_of_dims (a := zObj d.dims) rfl)
  exact exists_crossPerm_mid (o := zObj (𝟙^n)) (z := zObj [(⟨n, hn⟩ : ℕ+)])
    (t := runMerge (pairChain n i j hij) (dimSum_pairChain hij))
    (crossPerm_eq_one_of_W _ (W_runMerge _ _)) hs hab ha hg

-- Sealed once characterised: the shape is a `Classical.choice`, and the unifier must not evaluate
-- it.  `boundaries_pairChain` and `eq_pairChain` are all a caller needs.
attribute [irreducible] pairShape

end ChainCat
