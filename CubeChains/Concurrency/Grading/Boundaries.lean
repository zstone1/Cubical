import CubeChains.Precubical.Wedge.Wedge
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Concurrency/Grading/Boundaries — a dimension list is a composition, and its beads are its
boundaries

A dimension list `d : List ℕ+` is exactly a `Composition (dimSum d)` (`dimComp`), so `boundaries d`
is mathlib's `Composition.boundaries` read in `ℕ` — lists of different totals must be comparable,
which `Finset (Fin (n+1))` does not allow.  The junction set and the block index
(`Composition.index`) meet in exactly one lemma, `index_lt_iff_mem_boundaries`; everything else is
the cut combinatorics: erasing an interior boundary merges the two beads it separates
(`exists_cut_of_mem_boundaries`).
-/

open BPSet

namespace CubeChains

/-- **An all-edges shape is pinned by its strand count** — it is the replicate of its own length,
and that length is its `dimSum`. -/
theorem ones_eq_of_dimSum_eq {a b : List ℕ+} (ha : ∀ x ∈ a, x = 1) (hb : ∀ x ∈ b, x = 1)
    (h : dimSum a = dimSum b) : a = b := by
  rw [eq_replicate_of_ones ha, eq_replicate_of_ones hb,
    show a.length = b.length from
      (dimSum_eq_length_of_ones ha).symm.trans (h.trans (dimSum_eq_length_of_ones hb))]

/-! ## A dimension list is a composition -/

/-- A dimension list as a composition of its total — the positivity of `ℕ+` is the block
positivity, and `dimSum` is the block sum on the nose. -/
def dimComp {n : ℕ} (d : List ℕ+) (h : dimSum d = n) : Composition n where
  blocks := d.map (fun c : ℕ+ => (c : ℕ))
  blocks_pos := by
    rintro b hb
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    exact c.pos
  blocks_sum := h

@[simp] theorem dimComp_length {n : ℕ} (d : List ℕ+) (h : dimSum d = n) :
    (dimComp d h).length = d.length := List.length_map _

theorem dimComp_sizeUpTo {n : ℕ} (d : List ℕ+) (h : dimSum d = n) (i : ℕ) :
    (dimComp d h).sizeUpTo i = dimSum (d.take i) :=
  congrArg List.sum (List.map_take ..).symm

/-- The **bead boundaries** of a dimension list — `0`, the partial sums, and the total.  Valued in
`ℕ`, not `Fin (dimSum d + 1)`, so that a prefix's boundaries embed in the whole list's. -/
def boundaries (d : List ℕ+) : Finset ℕ :=
  (dimComp d rfl).boundaries.map ⟨Fin.val, Fin.val_injective⟩

/-- `boundaries` does not see which total the composition is taken over. -/
theorem boundaries_eq {n : ℕ} (d : List ℕ+) (h : dimSum d = n) :
    boundaries d = (dimComp d h).boundaries.map ⟨Fin.val, Fin.val_injective⟩ := by
  subst h; rfl

theorem mem_boundaries_iff_take {n : ℕ} {d : List ℕ+} (h : dimSum d = n) {t : ℕ} :
    t ∈ (dimComp d h).boundaries.map ⟨Fin.val, Fin.val_injective⟩ ↔ ∃ i ≤ d.length,
      dimSum (d.take i) = t := by
  constructor
  · intro ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨i, by simpa using Nat.lt_succ_iff.mp i.isLt, (dimComp_sizeUpTo d h i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < (dimComp d h).length + 1 := by rw [dimComp_length]; omega
    exact Finset.mem_map.mpr ⟨(dimComp d h).boundary ⟨i, hi'⟩,
      Finset.mem_map.mpr ⟨⟨i, hi'⟩, Finset.mem_univ _, rfl⟩, dimComp_sizeUpTo d h i⟩

/-- **A boundary is the total of a prefix** — the characterization everything below runs on. -/
theorem mem_boundaries_iff {d : List ℕ+} {t : ℕ} :
    t ∈ boundaries d ↔ ∃ l r : List ℕ+, d = l ++ r ∧ dimSum l = t := by
  rw [boundaries, mem_boundaries_iff_take]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨d.take i, d.drop i, (d.take_append_drop i).symm, rfl⟩
  · rintro ⟨l, r, rfl, rfl⟩
    exact ⟨l.length, by simp, by rw [List.take_left]⟩

theorem zero_mem_boundaries (d : List ℕ+) : 0 ∈ boundaries d :=
  mem_boundaries_iff.mpr ⟨[], d, rfl, rfl⟩

theorem dimSum_mem_boundaries (d : List ℕ+) : dimSum d ∈ boundaries d :=
  mem_boundaries_iff.mpr ⟨d, [], (List.append_nil d).symm, rfl⟩

theorem le_dimSum_of_mem_boundaries {d : List ℕ+} {t : ℕ} (ht : t ∈ boundaries d) :
    t ≤ dimSum d := by
  obtain ⟨l, r, rfl, rfl⟩ := mem_boundaries_iff.mp ht
  simp

theorem card_boundaries (d : List ℕ+) : (boundaries d).card = d.length + 1 := by
  rw [boundaries, Finset.card_map, Composition.card_boundaries_eq_succ_length, dimComp_length]

/-- Concatenation shifts the second list's boundaries. -/
theorem boundaries_append (l r : List ℕ+) :
    boundaries (l ++ r) = boundaries l ∪ (boundaries r).image (· + dimSum l) := by
  ext t
  simp only [Finset.mem_union, Finset.mem_image, mem_boundaries_iff]
  constructor
  · rintro ⟨u, v, huv, rfl⟩
    rcases List.append_eq_append_iff.mp huv with ⟨w, rfl, hr⟩ | ⟨w, hl, -⟩
    · exact Or.inr ⟨dimSum w, ⟨w, v, hr, rfl⟩, by simp [Nat.add_comm]⟩
    · exact Or.inl ⟨u, w, hl, rfl⟩
  · rintro (⟨u, v, rfl, rfl⟩ | ⟨s, ⟨u, v, rfl, rfl⟩, rfl⟩)
    · exact ⟨u, v ++ r, by rw [List.append_assoc], rfl⟩
    · exact ⟨l ++ u, v, by rw [List.append_assoc], by simp [Nat.add_comm]⟩

/-- A single bead has just its two ends — both are boundaries, and there are only two. -/
theorem boundaries_singleton (c : ℕ+) : boundaries [c] = {0, (c : ℕ)} := by
  have hc : dimSum [c] = (c : ℕ) := by simp [dimSum]
  refine (Finset.eq_of_subset_of_card_le (fun t ht => ?_) ?_).symm
  · rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact zero_mem_boundaries [c]
    · rw [Finset.mem_singleton.mp ht', ← hc]
      exact dimSum_mem_boundaries [c]
  · rw [card_boundaries, Finset.card_insert_of_notMem (by simpa using c.pos.ne),
      Finset.card_singleton]
    simp

/-- The `insert 0` does not collapse: every boundary of the shifted tail is positive. -/
theorem boundaries_cons (c : ℕ+) (ds : List ℕ+) :
    boundaries (c :: ds) = insert 0 ((boundaries ds).image (· + (c : ℕ))) := by
  rw [show c :: ds = [c] ++ ds from rfl, boundaries_append, boundaries_singleton]
  ext t
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    show dimSum [c] = (c : ℕ) from by simp]
  exact ⟨fun h => h.elim (fun h => h.elim Or.inl fun hc => Or.inr ⟨0, zero_mem_boundaries ds,
      by omega⟩) Or.inr,
    fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr⟩

/-! ## The block a coordinate falls in

The block of a coordinate is `Composition.index` of `dimComp`, and the junction set is what the
blocks are read off.  `index_lt_iff_mem_boundaries` is the *only* crossing between the two
spellings; every fact below is that `iff` with its witness carried along an inclusion. -/

/-- **A junction between them is what separates two coordinates.** -/
theorem index_lt_iff_mem_boundaries {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (p q : Fin N) :
    ((dimComp d hd).index p : ℕ) < ((dimComp d hd).index q : ℕ)
      ↔ ∃ t ∈ boundaries d, (p : ℕ) < t ∧ t ≤ (q : ℕ) := by
  have hmem : ∀ i ≤ d.length, (dimComp d hd).sizeUpTo i ∈ boundaries d := fun i hi => by
    rw [boundaries_eq d hd, dimComp_sizeUpTo]
    exact (mem_boundaries_iff_take hd).mpr ⟨i, hi, rfl⟩
  constructor
  · refine fun hlt => ⟨(dimComp d hd).sizeUpTo ((dimComp d hd).index q : ℕ),
      hmem _ (le_of_lt (by rw [← dimComp_length d hd]; exact ((dimComp d hd).index q).isLt)),
      ((dimComp d hd).index_lt_iff p _).mp hlt,
      not_lt.mp fun hc => absurd (((dimComp d hd).index_lt_iff q _).mpr hc) (lt_irrefl _)⟩
  · rintro ⟨t, ht, h1, h2⟩
    rw [boundaries_eq d hd] at ht
    obtain ⟨i, -, rfl⟩ := (mem_boundaries_iff_take hd).mp ht
    rw [← dimComp_sizeUpTo d hd] at h1 h2
    exact lt_of_lt_of_le (((dimComp d hd).index_lt_iff p i).mpr h1)
      (not_lt.mp fun hc => absurd (((dimComp d hd).index_lt_iff q i).mp hc) (not_lt.mpr h2))

/-- **Refining preserves the block order** — the separating junction carries over unchanged. -/
theorem index_lt_of_subset {N : ℕ} {d d' : List ℕ+} (hd : dimSum d = N) (hd' : dimSum d' = N)
    (hsub : boundaries d' ⊆ boundaries d) {p q : Fin N}
    (hlt : ((dimComp d' hd').index p : ℕ) < ((dimComp d' hd').index q : ℕ)) :
    ((dimComp d hd).index p : ℕ) < ((dimComp d hd).index q : ℕ) :=
  let ⟨t, ht, h1, h2⟩ := (index_lt_iff_mem_boundaries hd' p q).mp hlt
  (index_lt_iff_mem_boundaries hd p q).mpr ⟨t, hsub ht, h1, h2⟩

/-- **…so the coarser index cannot invert a comparison the finer one makes.** -/
theorem index_le_of_subset {N : ℕ} {d d' : List ℕ+} (hd : dimSum d = N) (hd' : dimSum d' = N)
    (hsub : boundaries d' ⊆ boundaries d) {p q : Fin N}
    (h : ((dimComp d hd).index p : ℕ) ≤ ((dimComp d hd).index q : ℕ)) :
    ((dimComp d' hd').index p : ℕ) ≤ ((dimComp d' hd').index q : ℕ) :=
  not_lt.mp fun hc => absurd (index_lt_of_subset hd hd' hsub hc) (not_lt.mpr h)

/-- **A junction is where the block changes**, so the blocks pin the junctions: a shape whose
blocks are unions of `d`'s has all of `d`'s junctions among them. -/
theorem boundaries_subset_of_index {N : ℕ} {d d' : List ℕ+} (hd : dimSum d = N)
    (hd' : dimSum d' = N)
    (h : ∀ p q : Fin N, (dimComp d hd).index p = (dimComp d hd).index q →
      (dimComp d' hd').index p = (dimComp d' hd').index q) :
    boundaries d' ⊆ boundaries d := by
  intro t ht
  have htN : t ≤ N := hd' ▸ le_dimSum_of_mem_boundaries ht
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact zero_mem_boundaries d
  rcases eq_or_lt_of_le htN with rfl | hlt
  · exact mem_boundaries_iff.mpr ⟨d, [], (List.append_nil d).symm, hd⟩
  -- `0 < t < N`: `d'` separates `t-1` from `t`, hence so does `d`, and `t` is the only junction
  -- the separation can sit at.
  have hsep : ((dimComp d' hd').index ⟨t - 1, by omega⟩ : ℕ)
      < ((dimComp d' hd').index ⟨t, hlt⟩ : ℕ) :=
    (index_lt_iff_mem_boundaries hd' _ _).mpr ⟨t, ht, show t - 1 < t by omega, le_rfl⟩
  obtain ⟨s, hs, h1, h2⟩ := (index_lt_iff_mem_boundaries hd ⟨t - 1, by omega⟩ ⟨t, hlt⟩).mp
    (lt_of_le_of_ne ((dimComp d hd).index_monotone (Fin.le_def.mpr (show t - 1 ≤ t by omega)))
      fun hc => absurd (congrArg Fin.val (h _ _ (Fin.ext hc))) (Nat.ne_of_lt hsep))
  have h1' : t - 1 < s := h1
  have h2' : s ≤ t := h2
  exact (show s = t by omega) ▸ hs

/-! ## Cutting a bead -/

/-- **A cut adds one boundary.**  Splitting the bead `p + q` in two adds exactly the total at
which it is split. -/
theorem boundaries_cut (l r : List ℕ+) (p q : ℕ+) :
    boundaries (l ++ p :: q :: r)
      = insert (dimSum l + (p : ℕ)) (boundaries (l ++ (p + q) :: r)) := by
  have hpair : boundaries (p :: q :: r) = insert (p : ℕ) (boundaries ((p + q) :: r)) := by
    have himg : (boundaries r).image ((fun x => x + (p : ℕ)) ∘ (fun x => x + (q : ℕ)))
        = (boundaries r).image (fun x => x + ((p + q : ℕ+) : ℕ)) :=
      Finset.image_congr fun x _ => by rw [Function.comp_apply, PNat.add_coe]; omega
    rw [boundaries_cons p (q :: r), boundaries_cons q r, boundaries_cons (p + q) r,
      Finset.image_insert, Nat.zero_add, Finset.image_image, himg, Finset.insert_comm]
  rw [boundaries_append l (p :: q :: r), boundaries_append l ((p + q) :: r), hpair,
    Finset.image_insert, Finset.union_insert]
  congr 1
  omega

/-- The dimension sum is blind to a cut. -/
theorem dimSum_cut (l r : List ℕ+) (p q : ℕ+) :
    dimSum (l ++ p :: q :: r) = dimSum (l ++ (p + q) :: r) := by
  simp only [dimSum, List.map_append, List.map_cons, List.sum_append, List.sum_cons, PNat.add_coe]
  omega

/-- The boundary a cut adds is interior to the merged bead, so the merge really is shorter. -/
theorem notMem_boundaries_cut (l r : List ℕ+) (p q : ℕ+) :
    dimSum l + (p : ℕ) ∉ boundaries (l ++ (p + q) :: r) := by
  intro hmem
  have hcard := congrArg Finset.card (boundaries_cut l r p q)
  rw [Finset.insert_eq_self.mpr hmem, card_boundaries, card_boundaries] at hcard
  simp only [List.length_append, List.length_cons] at hcard
  omega

/-- **An interior boundary splits the shape into two beads.** -/
theorem exists_split_of_mem_boundaries (d : List ℕ+) {t : ℕ} (ht : t ∈ boundaries d) (h0 : t ≠ 0)
    (hlast : t ≠ dimSum d) :
    ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ p :: q :: r ∧ dimSum l + (p : ℕ) = t := by
  obtain ⟨u, v, rfl, rfl⟩ := mem_boundaries_iff.mp ht
  obtain ⟨l, p, rfl⟩ : ∃ (l : List ℕ+) (p : ℕ+), u = l.concat p := by
    rcases u.eq_nil_or_concat with rfl | h
    · exact absurd rfl h0
    · exact h
  obtain ⟨q, r, rfl⟩ : ∃ (q : ℕ+) (r : List ℕ+), v = q :: r := by
    rcases v with _ | ⟨q, r⟩
    · exact absurd (by simp) hlast
    · exact ⟨q, r, rfl⟩
  exact ⟨l, r, p, q, by simp, by simp [List.concat_eq_append]⟩

/-- **Erasing an interior boundary merges the two beads it separates.** -/
theorem exists_cut_of_mem_boundaries (d : List ℕ+) {t : ℕ} (ht : t ∈ boundaries d) (h0 : t ≠ 0)
    (hlast : t ≠ dimSum d) :
    ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ p :: q :: r
      ∧ boundaries (l ++ (p + q) :: r) = (boundaries d).erase t := by
  obtain ⟨l, r, p, q, rfl, hlp⟩ := exists_split_of_mem_boundaries d ht h0 hlast
  refine ⟨l, r, p, q, rfl, ?_⟩
  rw [boundaries_cut, hlp, Finset.erase_insert (hlp ▸ notMem_boundaries_cut l r p q)]

/-! ## The boundaries determine the shape -/

/-- A composition is its boundary set — mathlib's `compositionEquiv`, read as injectivity. -/
private theorem blocks_eq_of_boundaries_eq {n : ℕ} {c c' : Composition n}
    (h : c.boundaries = c'.boundaries) : c.blocks = c'.blocks :=
  congrArg Composition.blocks ((compositionEquiv n).injective (CompositionAsSet.ext h))

theorem boundaries_injective {d d' : List ℕ+} (h : boundaries d = boundaries d') : d = d' := by
  have hdim : dimSum d = dimSum d' :=
    le_antisymm (le_dimSum_of_mem_boundaries (h ▸ dimSum_mem_boundaries d))
      (le_dimSum_of_mem_boundaries (h.symm ▸ dimSum_mem_boundaries d'))
  have hb : (dimComp d hdim).boundaries = (dimComp d' rfl).boundaries :=
    Finset.map_injective _ (by rw [← boundaries_eq d hdim, ← boundaries_eq d' rfl]; exact h)
  exact List.map_injective_iff.mpr PNat.coe_injective (blocks_eq_of_boundaries_eq hb)

/-- The dimension list of a composition — inverse to `dimComp`. -/
private def compDims {n : ℕ} (c : Composition n) : List ℕ+ :=
  c.blocks.attach.map fun b => ⟨b.1, c.blocks_pos b.2⟩

private theorem map_compDims {n : ℕ} (c : Composition n) :
    (compDims c).map (fun d : ℕ+ => (d : ℕ)) = c.blocks := by
  rw [compDims, List.map_map]
  simp

/-- **Every cut set is realised.**  The partner of `boundaries_injective`: a shape on `n` events is
exactly a subset of `{0,…,n}` containing both ends, which is mathlib's `CompositionAsSet`. -/
theorem exists_boundaries_eq {n : ℕ} {S : Finset ℕ} (hS : ∀ t ∈ S, t ≤ n) (h0 : 0 ∈ S)
    (hn : n ∈ S) : ∃ d : List ℕ+, dimSum d = n ∧ boundaries d = S := by
  classical
  have hlt : ∀ m ∈ S, m < n + 1 := fun m hm => Nat.lt_succ_of_le (hS m hm)
  let c : Composition n :=
    (⟨S.attachFin hlt, (Finset.mem_attachFin hlt).mpr h0,
      (Finset.mem_attachFin hlt).mpr (by simpa using hn)⟩ : CompositionAsSet n).toComposition
  have hsum : dimSum (compDims c) = n := by
    rw [dimSum, map_compDims]; exact c.blocks_sum
  refine ⟨compDims c, hsum, ?_⟩
  have hcomp : dimComp (compDims c) hsum = c :=
    Composition.ext (by rw [dimComp]; exact map_compDims c)
  rw [boundaries_eq _ hsum, hcomp,
    show c.boundaries = S.attachFin hlt from CompositionAsSet.toComposition_boundaries _,
    show (⟨Fin.val, Fin.val_injective⟩ : Fin (n + 1) ↪ ℕ) = Fin.valEmbedding from rfl,
    Finset.map_valEmbedding_attachFin]

end CubeChains
