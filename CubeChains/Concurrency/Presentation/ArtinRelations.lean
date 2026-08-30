import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Concurrency.Presentation.GarsideChains

/-!
# Concurrency/Presentation/ArtinRelations — the codimension-two species as the Artin relations

Out of the run, the codimension-one arrows that are not merges are the `n-1` **atoms** `σᵢ`: the
crossing staircase spliced at the edge beads `i, i+1`.  Codimension two has exactly two species
(`codim_eq_two_iff`), and out of the run they are the two Artin families — two disjoint edge cuts
give commutation, one bead cut in three gives the braid relation.  In the second, the remaining
factor merges a square with an edge and is *not* an atom; `germ_of_atom` is what rewrites it.
-/

open CategoryTheory CubeChains BPSet Equiv

namespace CubeChains

variable {n : ℕ}

/-! ### The two codimension-two compositions

`atomComp n i` cuts one bead of `1ⁿ` in two; these cut two beads in two, and one bead in three. -/

/-- `1ⁱ 2 1^{j-i-2} 2 1^{n-2-j}` — the edge pairs `{i,i+1}` and `{j,j+1}` merged. -/
def doubleComp (n i j : ℕ) : List ℕ+ :=
  𝟙^i ++ (2 : ℕ+) :: (𝟙^(j - i - 2) ++ (2 : ℕ+) :: 𝟙^(n - 2 - j))

/-- `1ⁱ 3 1^{n-3-i}` — the three edges `i, i+1, i+2` merged. -/
def tripleComp (n i : ℕ) : List ℕ+ := 𝟙^i ++ (3 : ℕ+) :: 𝟙^(n - 3 - i)

theorem dimSum_doubleComp {n i j : ℕ} (hij : i + 1 < j) (hj : j + 1 < n) :
    dimSum (doubleComp n i j) = n := by
  have h2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  rw [doubleComp, dimSum_append, dimSum_cons, dimSum_append, dimSum_cons, dimSum_replicate,
    dimSum_replicate, dimSum_replicate, h2]
  omega

theorem dimSum_tripleComp {n i : ℕ} (hi : i + 2 < n) : dimSum (tripleComp n i) = n := by
  have h3 : ((3 : ℕ+) : ℕ) = 3 := rfl
  rw [tripleComp, dimSum_append, dimSum_cons, dimSum_replicate, dimSum_replicate, h3]
  omega

theorem map_doubleComp (n i j : ℕ) :
    (doubleComp n i j).map (fun d : ℕ+ => (d : ℕ))
      = List.replicate i 1 ++ 2 :: (List.replicate (j - i - 2) 1 ++ 2 ::
          List.replicate (n - 2 - j) 1) := by
  simp [doubleComp]

theorem map_tripleComp (n i : ℕ) :
    (tripleComp n i).map (fun d : ℕ+ => (d : ℕ))
      = List.replicate i 1 ++ 3 :: List.replicate (n - 3 - i) 1 := by
  simp [tripleComp]

/-- The lower merged pair of `doubleComp` is one bead. -/
theorem blockOfPos_doubleComp_lo (n i j : ℕ) {x : ℕ} (h1 : i ≤ x) (h2 : x < i + 2) :
    blockOfPos ((doubleComp n i j).map fun d : ℕ+ => (d : ℕ)) x = i := by
  rw [map_doubleComp]
  exact blockOfPos_replicate_one_append_inside 2 _ i h1 h2

/-- The upper merged pair of `doubleComp` is one bead. -/
theorem blockOfPos_doubleComp_hi (n i j : ℕ) (hij : i + 1 < j) {x : ℕ}
    (h1 : j ≤ x) (h2 : x < j + 2) :
    blockOfPos ((doubleComp n i j).map fun d : ℕ+ => (d : ℕ)) x = j - 1 := by
  rw [map_doubleComp, blockOfPos_replicate_one_append_after 2 _ i (by omega),
    blockOfPos_replicate_one_append_inside 2 _ (j - i - 2) (by omega) (by omega)]
  omega

/-- The merged triple of `tripleComp` is one bead. -/
theorem blockOfPos_tripleComp (n i : ℕ) {x : ℕ} (h1 : i ≤ x) (h2 : x < i + 3) :
    blockOfPos ((tripleComp n i).map fun d : ℕ+ => (d : ℕ)) x = i := by
  rw [map_tripleComp]
  exact blockOfPos_replicate_one_append_inside 3 _ i h1 h2

theorem ones_cons₂ (r : ℕ) : (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^r = 𝟙^(r + 2) := by
  rw [show r + 2 = r + 1 + 1 from rfl, List.replicate_succ, List.replicate_succ]

theorem ones_cons₃ (r : ℕ) : (1 : ℕ+) :: (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^r = 𝟙^(r + 3) := by
  rw [show r + 3 = r + 2 + 1 from rfl, List.replicate_succ, ones_cons₂]

theorem ones_append (a b : ℕ) : 𝟙^a ++ 𝟙^b = 𝟙^(a + b) := (List.replicate_add a b _).symm

/-- The all-ones shape, cut at one pair of beads. -/
theorem ones_eq_atomCut {n i : ℕ} (h : i + 2 ≤ n) :
    𝟙^n = 𝟙^i ++ (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^(n - 2 - i) := by
  rw [ones_cons₂, ones_append]
  congr 1
  omega

/-- The all-ones shape, cut at three consecutive beads. -/
theorem ones_eq_tripleCut {n i : ℕ} (h : i + 3 ≤ n) :
    𝟙^n = 𝟙^i ++ (1 : ℕ+) :: (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^(n - 3 - i) := by
  rw [ones_cons₃, ones_append]
  congr 1
  omega

/-- The all-ones shape, cut at two disjoint pairs of beads. -/
theorem ones_eq_doubleCut {n i j : ℕ} (hij : i + 1 < j) (hj : j + 2 ≤ n) :
    𝟙^n = 𝟙^i ++ (1 : ℕ+) :: (1 : ℕ+) ::
      (𝟙^(j - i - 2) ++ (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^(n - 2 - j)) := by
  rw [ones_cons₂ ((n : ℕ) - 2 - j), ones_append, ones_cons₂, ones_append]
  congr 1
  omega

/-- Every bead of an all-ones shape is an edge. -/
theorem eq_one_of_mem_ones {n : ℕ} {L : List ℕ+} (h : 𝟙^n = L) {d : ℕ+} (hd : d ∈ L) : d = 1 :=
  List.eq_of_mem_replicate (by rw [h]; exact hd)

theorem eq_ones_of_mem {L : List ℕ+} (h : ∀ d ∈ L, d = (1 : ℕ+)) : L = 𝟙^L.length :=
  List.eq_replicate_iff.mpr ⟨rfl, h⟩

/-- The atom composition, with its tail length named. -/
theorem atomComp_eq_ones (n : ℕ) (i : Fin (n - 1)) {k : ℕ} (h : (i : ℕ) + 2 + k = n) :
    atomComp n i = 𝟙^(i : ℕ) ++ (2 : ℕ+) :: 𝟙^k := by
  rw [atomComp, show n - 2 - (i : ℕ) = k by omega]

theorem tripleComp_eq (n i k : ℕ) (h : i + 3 + k = n) :
    tripleComp n i = 𝟙^i ++ (3 : ℕ+) :: 𝟙^k := by
  rw [tripleComp, show n - 3 - i = k by omega]

theorem doubleComp_eq (n i j e k : ℕ) (h1 : i + 2 + e = j) (h2 : j + 2 + k = n) :
    doubleComp n i j = 𝟙^i ++ (2 : ℕ+) :: (𝟙^e ++ (2 : ℕ+) :: 𝟙^k) := by
  rw [doubleComp, show j - i - 2 = e by omega, show n - 2 - j = k by omega]

end CubeChains

namespace ChainCat

open CubeChains

variable {m : ℕ}

/-! ### The codimension-one atoms -/

/-- The target of the `i`-th atom. -/
def atomObj (m : ℕ) (i : Fin (m - 1)) : ChStrands Zbp m :=
  ⟨zObj (atomComp m i), dimSum_atomComp m i⟩

/-- **The `i`-th atom `σᵢ`**: the crossing staircase (`cubeReorder 1 1`, not `cubeMerge`) spliced at
the edge beads `i, i+1` of the run. -/
noncomputable def atomArrow (m : ℕ) (i : Fin (m - 1)) : onesObj m ⟶ atomObj m i :=
  ObjectProperty.homMk (exists_crossPerm_adjT m i).choose

@[simp] theorem crossPermN_atomArrow (m : ℕ) (i : Fin (m - 1)) :
    crossPermN (atomArrow m i) = adjT i :=
  (exists_crossPerm_adjT m i).choose_spec

/-- **The atom is not a merge**: it crosses its own pair, and a merge crosses nothing. -/
theorem not_wStrands_atomArrow (m : ℕ) (i : Fin (m - 1)) :
    ¬ WStrands Zbp m (atomArrow m i) := fun h => by
  have hone : adjT i = 1 := (crossPermN_atomArrow m i).symm.trans (crossPermN_eq_one_of_WStrands h)
  have hval : ((adjT i (adjLo i) : Fin m) : ℕ) = ((adjLo i : Fin m) : ℕ) := by
    rw [hone]; rfl
  rw [adjT_lo, adjHi_val, adjLo_val] at hval
  omega

/-- **`codim` reads the endpoints only**, so every arrow at this cut has codimension one — the
merge as well as the atom. -/
theorem codim_ones_to_atomObj (m : ℕ) (i : Fin (m - 1)) (u : onesObj m ⟶ atomObj m i) :
    codim u.hom = 1 := by
  have hi := i.isLt
  rw [codim_eq_length_sub]
  change (𝟙^m).length - (atomComp m i).length = 1
  simp only [atomComp, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem codim_atomArrow (m : ℕ) (i : Fin (m - 1)) : codim (atomArrow m i).hom = 1 :=
  codim_ones_to_atomObj m i (atomArrow m i)

/-! ### The species out of the run

`codim_eq_one_iff` / `codim_eq_two_iff` classify a refinement by its cuts.  Out of the run every
piece of a cut is an edge, so the targets are exactly `atomComp`, `tripleComp` and `doubleComp` —
that is what makes "the codimension-two relations are the Artin relations" a dichotomy. -/

/-- **Out of the run, codimension one is one edge pair merged.** -/
theorem codim_eq_one_ones_iff {n : ℕ} {b : Ch Zbp} (f : zObj (𝟙^n) ⟶ b) :
    codim f = 1 ↔ ∃ i : Fin (n - 1), b.dims = atomComp n i := by
  rw [codim_eq_one_iff f]
  constructor
  · rintro ⟨l, r, p, q, hb, ha⟩
    rw [zObj_dims] at ha
    have hall : ∀ d ∈ l ++ p :: q :: r, d = (1 : ℕ+) := fun d hd => eq_one_of_mem_ones ha hd
    obtain rfl : p = 1 := hall p (by simp)
    obtain rfl : q = 1 := hall q (by simp)
    obtain ⟨i, rfl⟩ : ∃ i, l = 𝟙^i :=
      ⟨l.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
    obtain ⟨k, rfl⟩ : ∃ k, r = 𝟙^k :=
      ⟨r.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
    have hlen : n = i + 2 + k := by
      have := congrArg List.length ha
      simp only [List.length_replicate, List.length_append, List.length_cons] at this
      omega
    exact ⟨⟨i, by omega⟩,
      hb.trans (atomComp_eq_ones n ⟨i, by omega⟩ (show i + 2 + k = n by omega)).symm⟩
  · rintro ⟨i, hb⟩
    have hi := i.isLt
    exact ⟨𝟙^(i : ℕ), 𝟙^(n - 2 - (i : ℕ)), 1, 1, hb, by
      rw [zObj_dims]; exact ones_eq_atomCut (by omega)⟩

/-- **Out of the run there are exactly two codimension-two species, and they are the two Artin
families**: one bead cut in three (the braid relation), or two disjoint edge pairs cut
(commutation). -/
theorem codim_eq_two_ones_iff {n : ℕ} {b : Ch Zbp} (f : zObj (𝟙^n) ⟶ b) :
    codim f = 2 ↔
      (∃ i : ℕ, i + 3 ≤ n ∧ b.dims = tripleComp n i) ∨
      (∃ i j : ℕ, i + 1 < j ∧ j + 2 ≤ n ∧ b.dims = doubleComp n i j) := by
  rw [codim_eq_two_iff f]
  constructor
  · rintro (⟨l, r, x, y, z, hb, ha⟩ | ⟨l, c, r, x, y, x', y', hb, ha⟩)
    · rw [zObj_dims] at ha
      have hall : ∀ d ∈ l ++ x :: y :: z :: r, d = (1 : ℕ+) := fun d hd => eq_one_of_mem_ones ha hd
      obtain rfl : x = 1 := hall x (by simp)
      obtain rfl : y = 1 := hall y (by simp)
      obtain rfl : z = 1 := hall z (by simp)
      obtain ⟨i, rfl⟩ : ∃ i, l = 𝟙^i :=
        ⟨l.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
      obtain ⟨k, rfl⟩ : ∃ k, r = 𝟙^k :=
        ⟨r.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
      have hlen : n = i + 3 + k := by
        have := congrArg List.length ha
        simp only [List.length_replicate, List.length_append, List.length_cons] at this
        omega
      exact Or.inl ⟨i, by omega, hb.trans (tripleComp_eq n i k (by omega)).symm⟩
    · rw [zObj_dims] at ha
      have hall : ∀ d ∈ l ++ x :: y :: (c ++ x' :: y' :: r), d = (1 : ℕ+) :=
        fun d hd => eq_one_of_mem_ones ha hd
      obtain rfl : x = 1 := hall x (by simp)
      obtain rfl : y = 1 := hall y (by simp)
      obtain rfl : x' = 1 := hall x' (by simp)
      obtain rfl : y' = 1 := hall y' (by simp)
      obtain ⟨i, rfl⟩ : ∃ i, l = 𝟙^i :=
        ⟨l.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
      obtain ⟨e, rfl⟩ : ∃ e, c = 𝟙^e :=
        ⟨c.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
      obtain ⟨k, rfl⟩ : ∃ k, r = 𝟙^k :=
        ⟨r.length, eq_ones_of_mem fun d hd => hall d (by simp [hd])⟩
      have hlen : n = i + 2 + (e + 2 + k) := by
        have := congrArg List.length ha
        simp only [List.length_replicate, List.length_append, List.length_cons] at this
        omega
      exact Or.inr ⟨i, i + 2 + e, by omega, by omega,
        hb.trans (doubleComp_eq n i (i + 2 + e) e k rfl (by omega)).symm⟩
  · rintro (⟨i, hi, hb⟩ | ⟨i, j, hij, hj, hb⟩)
    · exact Or.inl ⟨𝟙^i, 𝟙^(n - 3 - i), 1, 1, 1, hb, by
        rw [zObj_dims]; exact ones_eq_tripleCut hi⟩
    · exact Or.inr ⟨𝟙^i, 𝟙^(j - i - 2), 𝟙^(n - 2 - j), 1, 1, 1, 1, hb, by
        rw [zObj_dims]; exact ones_eq_doubleCut hij hj⟩

/-! ### The atoms in the localization

`locEquivPosBraid_locOf` names a class by its crossing permutation, so an atom's class is the
simple of `adjT i`, and a length-additive product of two simples splits. -/

/-- **The `i`-th Artin generator**, as a class in `Ch(Zbp)[W⁻¹]` at strand count `m`. -/
noncomputable def atomLoc (m : ℕ) (i : Fin (m - 1)) : LocMonoid (WStrands Zbp m) :=
  locOf (WStrands Zbp m) (atomArrow m i)

@[simp] theorem locEquivPosBraid_atomLoc (m : ℕ) (i : Fin (m - 1)) :
    locEquivPosBraid m (atomLoc m i) = posPerm (adjT i) := by
  rw [atomLoc, locEquivPosBraid_locOf, crossPermN_atomArrow]

/-- An arrow crossing exactly one adjacent pair has the class of that atom. -/
theorem locOf_eq_atomLoc {A B : ChStrands Zbp m} (f : A ⟶ B) {i : Fin (m - 1)}
    (h : crossPermN f = adjT i) : locOf (WStrands Zbp m) f = atomLoc m i :=
  (locEquivPosBraid m).injective (by
    rw [locEquivPosBraid_locOf, h, locEquivPosBraid_atomLoc])

/-- **Rewriting a non-atom factor into atoms**: a class named by a length-additive product of two
adjacent transpositions is the product of the two atoms — the germ relation, in the localization. -/
theorem locOf_eq_atomLoc_mul {A B : ChStrands Zbp m} (f : A ⟶ B) {k l : Fin (m - 1)}
    (hlen : permLen (adjT k * adjT l) = permLen (adjT k) + permLen (adjT l))
    (h : crossPermN f = adjT k * adjT l) :
    locOf (WStrands Zbp m) f = atomLoc m k * atomLoc m l :=
  (locEquivPosBraid m).injective (by
    rw [locEquivPosBraid_locOf, h, map_mul, locEquivPosBraid_atomLoc, locEquivPosBraid_atomLoc,
      posPerm_mul hlen])

/-! ### The double cut: two disjoint edge pairs

The second codimension-two species, at two pairs of *edges*.  Both of its factorizations are a pair
of atoms, so the relation drops out with no rewriting. -/

/-- An index of `Fin (n-1)` names an adjacent pair of `Fin n`. -/
theorem index_succ_lt {m : ℕ} (j : Fin (m - 1)) : (j : ℕ) + 1 < m := by
  have := j.isLt; omega

variable {m : ℕ} {i j : Fin (m - 1)}

theorem blockOfPos_double_lo (i j : Fin (m - 1)) :
    blockOfPos ((doubleComp m i j).map fun d : ℕ+ => (d : ℕ)) (i : ℕ)
      = blockOfPos ((doubleComp m i j).map fun d : ℕ+ => (d : ℕ)) ((i : ℕ) + 1) := by
  rw [blockOfPos_doubleComp_lo _ _ _ (Nat.le_refl _) (by omega),
    blockOfPos_doubleComp_lo _ _ _ (by omega) (by omega)]

theorem blockOfPos_double_hi (hij : (i : ℕ) + 1 < (j : ℕ)) :
    blockOfPos ((doubleComp m i j).map fun d : ℕ+ => (d : ℕ)) (j : ℕ)
      = blockOfPos ((doubleComp m i j).map fun d : ℕ+ => (d : ℕ)) ((j : ℕ) + 1) := by
  rw [blockOfPos_doubleComp_hi _ _ _ hij (Nat.le_refl _) (by omega),
    blockOfPos_doubleComp_hi _ _ _ hij (by omega) (by omega)]

/-- The target of the double cut. -/
def doubleObj (m : ℕ) (i j : Fin (m - 1)) (hij : (i : ℕ) + 1 < (j : ℕ)) : ChStrands Zbp m :=
  ⟨zObj (doubleComp m i j), dimSum_doubleComp hij (index_succ_lt j)⟩

theorem exists_doubleArrow (hij : (i : ℕ) + 1 < (j : ℕ)) :
    ∃ f : zObj (𝟙^m) ⟶ zObj (doubleComp m i j),
      crossPerm (dimSum_replicate m) f = adjT i * adjT j :=
  exists_crossPerm_ones (dimSum_doubleComp hij (index_succ_lt j))
    (mul_mem (adjT_mem_parabolic (blockOfPos_double_lo i j))
      (adjT_mem_parabolic (blockOfPos_double_hi hij)))

/-- **The double cut**: the codimension-two refinement of the run crossing both pairs. -/
noncomputable def doubleArrow (hij : (i : ℕ) + 1 < (j : ℕ)) :
    onesObj m ⟶ doubleObj m i j hij :=
  ObjectProperty.homMk (exists_doubleArrow hij).choose

@[simp] theorem crossPermN_doubleArrow (hij : (i : ℕ) + 1 < (j : ℕ)) :
    crossPermN (doubleArrow hij) = adjT i * adjT j :=
  (exists_doubleArrow hij).choose_spec

theorem codim_doubleArrow (hij : (i : ℕ) + 1 < (j : ℕ)) :
    codim (doubleArrow hij).hom = 2 := by
  have hi := i.isLt
  have hj := j.isLt
  rw [codim_eq_length_sub]
  change (𝟙^m).length - (doubleComp m i j).length = 2
  simp only [doubleComp, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem exists_doubleFactorHi (hij : (i : ℕ) + 1 < (j : ℕ)) :
    ∃ u : zObj (atomComp m i) ⟶ zObj (doubleComp m i j),
      crossPerm (dimSum_atomComp m i) u = adjT j :=
  exists_crossPerm_atomComp (dimSum_doubleComp hij (index_succ_lt j))
    (blockOfPos_double_lo i j) (adjT_mem_parabolic (blockOfPos_double_hi hij))
    (by simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val]; grind)

/-- The cut left over after `σᵢ`: the other pair, still an atom. -/
noncomputable def doubleFactorHi (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomObj m i ⟶ doubleObj m i j hij :=
  ObjectProperty.homMk (exists_doubleFactorHi hij).choose

@[simp] theorem crossPermN_doubleFactorHi (hij : (i : ℕ) + 1 < (j : ℕ)) :
    crossPermN (doubleFactorHi hij) = adjT j :=
  (exists_doubleFactorHi hij).choose_spec

theorem exists_doubleFactorLo (hij : (i : ℕ) + 1 < (j : ℕ)) :
    ∃ u : zObj (atomComp m j) ⟶ zObj (doubleComp m i j),
      crossPerm (dimSum_atomComp m j) u = adjT i :=
  exists_crossPerm_atomComp (dimSum_doubleComp hij (index_succ_lt j))
    (blockOfPos_double_hi hij) (adjT_mem_parabolic (blockOfPos_double_lo i j))
    (by simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val]; grind)

/-- The cut left over after `σⱼ`. -/
noncomputable def doubleFactorLo (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomObj m j ⟶ doubleObj m i j hij :=
  ObjectProperty.homMk (exists_doubleFactorLo hij).choose

@[simp] theorem crossPermN_doubleFactorLo (hij : (i : ℕ) + 1 < (j : ℕ)) :
    crossPermN (doubleFactorLo hij) = adjT i :=
  (exists_doubleFactorLo hij).choose_spec

/-- **The double cut factors as `σᵢ` then `σⱼ`.** -/
theorem atomArrow_comp_doubleFactorHi (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomArrow m i ≫ doubleFactorHi hij = doubleArrow hij :=
  hom_ext_of_crossPermN (by
    rw [crossPermN_comp, crossPermN_atomArrow, crossPermN_doubleFactorHi, crossPermN_doubleArrow]
    exact (adjT_comm i j hij).symm)

/-- **…and as `σⱼ` then `σᵢ`.** -/
theorem atomArrow_comp_doubleFactorLo (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomArrow m j ≫ doubleFactorLo hij = doubleArrow hij :=
  hom_ext_of_crossPermN (by
    rw [crossPermN_comp, crossPermN_atomArrow, crossPermN_doubleFactorLo, crossPermN_doubleArrow])

/-- **The double cut is the commutation relation.**  Its two codimension-one factorizations are
`σᵢ, σⱼ` and `σⱼ, σᵢ`; every factor is an atom, so no rewriting is needed. -/
theorem atomLoc_comm (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomLoc m i * atomLoc m j = atomLoc m j * atomLoc m i := by
  have hA : locOf (WStrands Zbp m) (doubleArrow hij) = atomLoc m j * atomLoc m i := by
    rw [← atomArrow_comp_doubleFactorHi hij, ← locOf_comp,
      locOf_eq_atomLoc _ (crossPermN_doubleFactorHi hij),
      locOf_eq_atomLoc _ (crossPermN_atomArrow m i)]
  have hB : locOf (WStrands Zbp m) (doubleArrow hij) = atomLoc m i * atomLoc m j := by
    rw [← atomArrow_comp_doubleFactorLo hij, ← locOf_comp,
      locOf_eq_atomLoc _ (crossPermN_doubleFactorLo hij),
      locOf_eq_atomLoc _ (crossPermN_atomArrow m j)]
  rw [← hB, hA]

/-! ### The triple cut: one bead cut in three

The first codimension-two species, at three consecutive edges.  Here the second factor merges a
*square with an edge*, so it is not an atom: `locOf_eq_atomLoc_mul` is what turns it into two. -/

theorem blockOfPos_triple_lo (i : Fin (m - 1)) :
    blockOfPos ((tripleComp m i).map fun d : ℕ+ => (d : ℕ)) (i : ℕ)
      = blockOfPos ((tripleComp m i).map fun d : ℕ+ => (d : ℕ)) ((i : ℕ) + 1) := by
  rw [blockOfPos_tripleComp _ _ (Nat.le_refl _) (by omega),
    blockOfPos_tripleComp _ _ (by omega) (by omega)]

theorem blockOfPos_triple_hi (hij : (j : ℕ) = (i : ℕ) + 1) :
    blockOfPos ((tripleComp m i).map fun d : ℕ+ => (d : ℕ)) (j : ℕ)
      = blockOfPos ((tripleComp m i).map fun d : ℕ+ => (d : ℕ)) ((j : ℕ) + 1) := by
  rw [blockOfPos_tripleComp _ _ (by omega) (by omega),
    blockOfPos_tripleComp _ _ (by omega) (by omega)]

/-- The target of the triple cut. -/
def tripleObj (m : ℕ) (i j : Fin (m - 1)) (hij : (j : ℕ) = (i : ℕ) + 1) : ChStrands Zbp m :=
  ⟨zObj (tripleComp m i),
    dimSum_tripleComp (by have := index_succ_lt j; omega)⟩

theorem exists_tripleArrow (hij : (j : ℕ) = (i : ℕ) + 1) :
    ∃ f : zObj (𝟙^m) ⟶ zObj (tripleComp m i),
      crossPerm (dimSum_replicate m) f = adjT i * adjT j * adjT i :=
  exists_crossPerm_ones (dimSum_tripleComp (by have := index_succ_lt j; omega))
    (mul_mem (mul_mem (adjT_mem_parabolic (blockOfPos_triple_lo i))
      (adjT_mem_parabolic (blockOfPos_triple_hi hij)))
      (adjT_mem_parabolic (blockOfPos_triple_lo i)))

/-- **The triple cut**: the codimension-two refinement of the run reversing the three strands. -/
noncomputable def tripleArrow (hij : (j : ℕ) = (i : ℕ) + 1) :
    onesObj m ⟶ tripleObj m i j hij :=
  ObjectProperty.homMk (exists_tripleArrow hij).choose

@[simp] theorem crossPermN_tripleArrow (hij : (j : ℕ) = (i : ℕ) + 1) :
    crossPermN (tripleArrow hij) = adjT i * adjT j * adjT i :=
  (exists_tripleArrow hij).choose_spec

theorem codim_tripleArrow (hij : (j : ℕ) = (i : ℕ) + 1) :
    codim (tripleArrow hij).hom = 2 := by
  have hj := index_succ_lt j
  rw [codim_eq_length_sub]
  change (𝟙^m).length - (tripleComp m i).length = 2
  simp only [tripleComp, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem exists_tripleFactorLo (hij : (j : ℕ) = (i : ℕ) + 1) :
    ∃ u : zObj (atomComp m i) ⟶ zObj (tripleComp m i),
      crossPerm (dimSum_atomComp m i) u = adjT i * adjT j :=
  exists_crossPerm_atomComp (dimSum_tripleComp (by have := index_succ_lt j; omega))
    (blockOfPos_triple_lo i)
    (mul_mem (adjT_mem_parabolic (blockOfPos_triple_lo i))
      (adjT_mem_parabolic (blockOfPos_triple_hi hij)))
    (by simp only [Fin.lt_def, Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]; grind)

/-- The cut left over after `σᵢ`: it merges a **square with an edge**, so it is not an atom. -/
noncomputable def tripleFactorLo (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomObj m i ⟶ tripleObj m i j hij :=
  ObjectProperty.homMk (exists_tripleFactorLo hij).choose

@[simp] theorem crossPermN_tripleFactorLo (hij : (j : ℕ) = (i : ℕ) + 1) :
    crossPermN (tripleFactorLo hij) = adjT i * adjT j :=
  (exists_tripleFactorLo hij).choose_spec

theorem exists_tripleFactorHi (hij : (j : ℕ) = (i : ℕ) + 1) :
    ∃ u : zObj (atomComp m j) ⟶ zObj (tripleComp m i),
      crossPerm (dimSum_atomComp m j) u = adjT j * adjT i :=
  exists_crossPerm_atomComp (dimSum_tripleComp (by have := index_succ_lt j; omega))
    (blockOfPos_triple_hi hij)
    (mul_mem (adjT_mem_parabolic (blockOfPos_triple_hi hij))
      (adjT_mem_parabolic (blockOfPos_triple_lo i)))
    (by simp only [Fin.lt_def, Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]; grind)

/-- The cut left over after `σⱼ` — likewise a square merged with an edge. -/
noncomputable def tripleFactorHi (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomObj m j ⟶ tripleObj m i j hij :=
  ObjectProperty.homMk (exists_tripleFactorHi hij).choose

@[simp] theorem crossPermN_tripleFactorHi (hij : (j : ℕ) = (i : ℕ) + 1) :
    crossPermN (tripleFactorHi hij) = adjT j * adjT i :=
  (exists_tripleFactorHi hij).choose_spec

/-- **The triple cut factors as `σᵢ` then the square-edge merge.** -/
theorem atomArrow_comp_tripleFactorLo (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomArrow m i ≫ tripleFactorLo hij = tripleArrow hij :=
  hom_ext_of_crossPermN (by
    rw [crossPermN_comp, crossPermN_atomArrow, crossPermN_tripleFactorLo, crossPermN_tripleArrow])

/-- **…and as `σⱼ` then the other one.** -/
theorem atomArrow_comp_tripleFactorHi (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomArrow m j ≫ tripleFactorHi hij = tripleArrow hij :=
  hom_ext_of_crossPermN (by
    rw [crossPermN_comp, crossPermN_atomArrow, crossPermN_tripleFactorHi, crossPermN_tripleArrow]
    exact (adjT_braid i j hij).symm)

theorem permLen_adjT_mul_adjT (hij : (j : ℕ) = (i : ℕ) + 1) :
    permLen (adjT i * adjT j) = permLen (adjT i) + permLen (adjT j) :=
  permLen_mul_adjT_add (by simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val]; grind)

theorem permLen_adjT_mul_adjT' (hij : (j : ℕ) = (i : ℕ) + 1) :
    permLen (adjT j * adjT i) = permLen (adjT j) + permLen (adjT i) :=
  permLen_mul_adjT_add (by simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val]; grind)

/-- **The triple cut is the braid relation.**  Its two codimension-one factorizations are `σᵢ` then
a square-edge merge and `σⱼ` then the other; those merges are not atoms, and rewriting each into
two is what turns a two-letter identity into Artin's three-letter one. -/
theorem atomLoc_braid (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomLoc m i * atomLoc m j * atomLoc m i = atomLoc m j * atomLoc m i * atomLoc m j := by
  have hA : locOf (WStrands Zbp m) (tripleArrow hij)
      = atomLoc m i * atomLoc m j * atomLoc m i := by
    rw [← atomArrow_comp_tripleFactorLo hij, ← locOf_comp,
      locOf_eq_atomLoc_mul _ (permLen_adjT_mul_adjT hij) (crossPermN_tripleFactorLo hij),
      locOf_eq_atomLoc _ (crossPermN_atomArrow m i)]
  have hB : locOf (WStrands Zbp m) (tripleArrow hij)
      = atomLoc m j * atomLoc m i * atomLoc m j := by
    rw [← atomArrow_comp_tripleFactorHi hij, ← locOf_comp,
      locOf_eq_atomLoc_mul _ (permLen_adjT_mul_adjT' hij) (crossPermN_tripleFactorHi hij),
      locOf_eq_atomLoc _ (crossPermN_atomArrow m j)]
  rw [← hA, hB]

/-! ### The headline: the localization in Artin shape -/

/-- **The atoms satisfy the codimension-two relations** — `atomLoc_comm` and `atomLoc_braid`, read
as a map out of the presentation. -/
noncomputable def artinPosToLoc (m : ℕ) : ArtinPosBraid m →* LocMonoid (WStrands Zbp m) :=
  ArtinPosBraid.lift (atomLoc m) ⟨fun _ _ h => atomLoc_comm h, fun _ _ h => atomLoc_braid h⟩

@[simp] theorem artinPosToLoc_gen (m : ℕ) (i : Fin (m - 1)) :
    artinPosToLoc m (artinPosGen i) = atomLoc m i := rfl

/-- **`Ch(Zbp)[W⁻¹]` at strand count `m` is presented by its `m-1` codimension-one atoms modulo
the codimension-two relations** — the Artin-shaped companion of `locEquivPosBraid`. -/
noncomputable def locEquivArtinPos (m : ℕ) : LocMonoid (WStrands Zbp m) ≃* ArtinPosBraid m :=
  (locEquivPosBraid m).trans (posBraid_equiv_artinPos m)

/-- …and it sends the `i`-th atom to the `i`-th Artin generator. -/
@[simp] theorem locEquivArtinPos_atomLoc (m : ℕ) (i : Fin (m - 1)) :
    locEquivArtinPos m (atomLoc m i) = artinPosGen i := by
  rw [locEquivArtinPos, MulEquiv.trans_apply, locEquivPosBraid_atomLoc,
    posBraid_equiv_artinPos_adjT]

/-- The presentation map is that isomorphism read backwards. -/
theorem locEquivArtinPos_symm_toMonoidHom (m : ℕ) :
    (locEquivArtinPos m).symm.toMonoidHom = artinPosToLoc m :=
  artinPosGen_ext fun i =>
    (locEquivArtinPos m).symm_apply_eq.mpr (locEquivArtinPos_atomLoc m i).symm

/-- **The atoms present**: `Ch(Zbp)[W⁻¹]` at strand count `m` *is* the Artin monoid on its `m-1`
codimension-one atoms. -/
theorem artinPosToLoc_bijective (m : ℕ) : Function.Bijective (artinPosToLoc m) := by
  have h : ⇑(artinPosToLoc m) = ⇑(locEquivArtinPos m).symm := by
    rw [← locEquivArtinPos_symm_toMonoidHom]; rfl
  rw [h]
  exact (locEquivArtinPos m).symm.bijective

/-- **The endomorphisms of the coarsest chain, in Artin shape.** -/
noncomputable def endEquivArtinPos (m : ℕ) :
    End ((WStrands Zbp m).Q.obj (topObj m)) ≃* ArtinPosBraid m :=
  (endEquivWStrands m).symm.trans (locEquivArtinPos m)

/-! ### Height is factorisation length

An atom has codimension one *and* length one, whereas a merge has codimension one and length zero
(`wStrands_iff_permLen`); inverting the merges leaves `permLen` as the grading.  So the number of
atoms in a factorisation is not a minimum over factorisations — `locLen` is additive, so **every**
factorisation has the same length, `permLen` of the crossing permutation. -/

/-- **The atom is codimension one and length one** (`codim_atomArrow` is the other half)… -/
theorem permLen_crossPermN_atomArrow (m : ℕ) (i : Fin (m - 1)) :
    permLen (crossPermN (atomArrow m i)) = 1 := by
  rw [crossPermN_atomArrow, permLen_adjT]

/-- …**and at the very same cut there is a merge, of codimension one and length zero** — `codim`
cannot separate the two species, `permLen` is what the localization keeps. -/
theorem exists_wStrands_ones_to_atomObj (m : ℕ) (i : Fin (m - 1)) :
    ∃ u : onesObj m ⟶ atomObj m i, codim u.hom = 1 ∧ permLen (crossPermN u) = 0 :=
  let ⟨u, hu⟩ := exists_WStrands_from_ones (atomObj m i)
  ⟨u, codim_ones_to_atomObj m i u, (wStrands_iff_permLen u).mp hu⟩

@[simp] theorem locLen_atomLoc (m : ℕ) (i : Fin (m - 1)) :
    locLen m (atomLoc m i) = Multiplicative.ofAdd 1 := by
  rw [atomLoc, locLen_locOf, crossPermN_atomArrow, permLen_adjT]

/-- The presentation map evaluates a word at the atoms. -/
theorem artinPosToLoc_mk (m : ℕ) (w : FreeMonoid (Fin (m - 1))) :
    artinPosToLoc m (PresentedMonoid.mk (ArtinRel m) w) = FreeMonoid.lift (atomLoc m) w := rfl

/-- **Length is the letter count.** -/
theorem locLen_comp_artinPosToLoc (m : ℕ) : (locLen m).comp (artinPosToLoc m) = artinLen m :=
  artinPosGen_ext fun i => by
    rw [MonoidHom.comp_apply, artinPosToLoc_gen, locLen_atomLoc, artinLen_gen]

/-- **Factorisation length is the height of the permutation.**  Any word of atoms whose product is
the class of `f` has exactly `permLen (crossPermN f)` letters. -/
theorem length_eq_permLen_crossPermN {A B : ChStrands Zbp m} (f : A ⟶ B)
    {w : FreeMonoid (Fin (m - 1))}
    (hw : FreeMonoid.lift (atomLoc m) w = locOf (WStrands Zbp m) f) :
    w.length = permLen (crossPermN f) := by
  have h := congrArg (locLen m) ((artinPosToLoc_mk m w).trans hw)
  rw [← MonoidHom.comp_apply, locLen_comp_artinPosToLoc, artinLen_mk, locLen_locOf] at h
  exact Multiplicative.ofAdd.injective h

/-- …and such a word exists, so the height *is* a factorisation length. -/
theorem exists_atomWord {A B : ChStrands Zbp m} (f : A ⟶ B) :
    ∃ w : FreeMonoid (Fin (m - 1)), FreeMonoid.lift (atomLoc m) w = locOf (WStrands Zbp m) f ∧
      w.length = permLen (crossPermN f) := by
  obtain ⟨β, hβ⟩ := (artinPosToLoc_bijective m).surjective (locOf (WStrands Zbp m) f)
  obtain ⟨w, rfl⟩ := PresentedMonoid.surjective_mk β
  have hw := (artinPosToLoc_mk m w).symm.trans hβ
  exact ⟨w, hw, length_eq_permLen_crossPermN f hw⟩

/-- **The classes of arrows do not exhaust the localization**: `σᵢ²` has length two, while a class
named by an arrow has both the permutation and the length of that arrow's crossing.  So "the height
of its permutation" is a statement about *arrows*, not about the monoid. -/
theorem locOf_ne_atomLoc_sq (i : Fin (m - 1)) {A B : ChStrands Zbp m} (f : A ⟶ B) :
    locOf (WStrands Zbp m) f ≠ atomLoc m i * atomLoc m i := fun h => by
  have hperm : crossPermN f = 1 := by
    have hp := congrArg (fun x => posPermHom m (locEquivPosBraid m x)) h
    simpa only [map_mul, locEquivPosBraid_locOf, locEquivPosBraid_atomLoc, posPermHom_posPerm,
      adjT_mul_self] using hp
  have hlen := congrArg (locLen m) h
  rw [locLen_locOf, hperm, permLen_one, map_mul, locLen_atomLoc, ← ofAdd_add] at hlen
  exact absurd (Multiplicative.ofAdd.injective hlen) (by omega)

end ChainCat
