import CubeChains.Foundations.Wedge
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Chains/Boundaries — a dimension list is a composition, and its beads are its boundaries

A dimension list `d : List ℕ+` is exactly a `Composition (dimSum d)` (`dimComp`), so `boundaries d`
is mathlib's `Composition.boundaries` read in `ℕ` — lists of different totals must be comparable,
which `Finset (Fin (n+1))` does not allow.  Everything else is the cut combinatorics: one deleted
boundary is one bead cut in two (`cutOfLengthSucc`), pinned by the boundary it happens at
(`cut_unique`).
-/

open BPSet

namespace CubeChains

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

/-- A prefix keeps its own boundaries. -/
theorem boundaries_prefix_subset (l r : List ℕ+) : boundaries l ⊆ boundaries (l ++ r) := by
  intro t ht
  obtain ⟨u, v, rfl, rfl⟩ := mem_boundaries_iff.mp ht
  exact mem_boundaries_iff.mpr ⟨u, v ++ r, by rw [List.append_assoc], rfl⟩

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

/-- A single bead has just its two ends. -/
theorem boundaries_singleton (c : ℕ+) : boundaries [c] = {0, (c : ℕ)} := by
  ext t
  rw [boundaries, mem_boundaries_iff_take]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp
    · simp
  · rintro ht
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact ⟨0, by simp, rfl⟩
    · obtain rfl := Finset.mem_singleton.mp ht'
      exact ⟨1, by simp, by simp⟩

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

/-- Splitting one bead at an interior total. -/
private def splitBead (c : ℕ+) {t : ℕ} (h0 : 0 < t) (hlt : t < (c : ℕ)) :
    Σ' p q : ℕ+, p + q = c ∧ (p : ℕ) = t :=
  ⟨⟨t, h0⟩, ⟨(c : ℕ) - t, by omega⟩,
    PNat.coe_injective (show t + ((c : ℕ) - t) = (c : ℕ) by omega), rfl⟩

/-- **Cutting a shape at a boundary it does not already have**: `t` is interior to a single bead,
which it splits in two. -/
def cutAt : ∀ (d : List ℕ+) {t : ℕ}, t ≤ dimSum d → t ∉ boundaries d →
    Σ' (l r : List ℕ+) (p q : ℕ+), d = l ++ (p + q) :: r ∧ dimSum l + (p : ℕ) = t
  | [], t, hle, hnot => absurd (show t ∈ boundaries ([] : List ℕ+) from
      (show t = 0 by simpa [dimSum] using hle) ▸ zero_mem_boundaries _) hnot
  | c :: ds, t, hle, hnot => by
      rw [dimSum_cons] at hle
      have h0 : 0 < t := Nat.pos_of_ne_zero fun h => hnot (h ▸ zero_mem_boundaries _)
      rw [boundaries_cons] at hnot
      refine dite (t < (c : ℕ)) (fun hlt => ?_) (fun hge => ?_)
      · obtain ⟨p, q, hpq, hp⟩ := splitBead c h0 hlt
        exact ⟨[], ds, p, q, by rw [hpq]; rfl, by simpa [dimSum] using hp⟩
      · have hsub : t - (c : ℕ) ∉ boundaries ds := fun hmem =>
          hnot (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hmem, by omega⟩))
        obtain ⟨l, r, p, q, hd, hl⟩ := cutAt ds (by omega) hsub
        exact ⟨c :: l, r, p, q, by rw [hd]; rfl, by rw [dimSum_cons]; omega⟩

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

/-- **A cut is pinned by the boundary at which it happens**, and that is the one boundary the merge
loses — so two presentations of one pair of shapes as "the bead `p + q`, cut" agree throughout. -/
theorem cut_unique {l r l' r' : List ℕ+} {p q p' q' : ℕ+}
    (h₁ : l ++ (p + q) :: r = l' ++ (p' + q') :: r')
    (h₂ : l ++ p :: q :: r = l' ++ p' :: q' :: r') :
    l = l' ∧ p = p' ∧ q = q' ∧ r = r' := by
  have hnot := notMem_boundaries_cut l r p q
  have hins : insert (dimSum l + (p : ℕ)) (boundaries (l ++ (p + q) :: r))
      = insert (dimSum l' + (p' : ℕ)) (boundaries (l ++ (p + q) :: r)) := by
    rw [← boundaries_cut, h₂, boundaries_cut, h₁]
  have ht : dimSum l + (p : ℕ) = dimSum l' + (p' : ℕ) := by
    have hmem : dimSum l + (p : ℕ)
        ∈ insert (dimSum l' + (p' : ℕ)) (boundaries (l ++ (p + q) :: r)) := by
      rw [← hins]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_insert.mp hmem).resolve_right hnot
  have hpre : l ++ [p] = l' ++ [p'] :=
    dimSum_prefix_eq (y := q :: r) (v := q' :: r') (by simpa using h₂) (by simpa using ht)
  obtain ⟨rfl, hcons⟩ := List.append_inj h₂ (by
    have := congrArg List.length hpre; simp at this; omega)
  obtain ⟨rfl, hcons'⟩ := List.cons_eq_cons.mp hcons
  obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hcons'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Locating the cuts of a coarsening

A refinement's shape carries the coarsening's boundaries and more; the extra boundaries are its
cuts, and where they fall among the coarsening's own boundaries is the whole classification. -/

/-- **One boundary more is one bead cut in two.** -/
def cutOfLengthSucc {d d' : List ℕ+} (hdim : dimSum d = dimSum d')
    (hsub : boundaries d' ⊆ boundaries d) (hlen : d.length = d'.length + 1) :
    Σ' (l r : List ℕ+) (p q : ℕ+), d' = l ++ (p + q) :: r ∧ d = l ++ p :: q :: r := by
  have hcard : (boundaries d).card = (boundaries d').card + 1 := by
    rw [card_boundaries, card_boundaries]; omega
  have hne : (boundaries d \ boundaries d').Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
  have hmem := Finset.mem_sdiff.mp ((boundaries d \ boundaries d').min'_mem hne)
  obtain ⟨l, r, p, q, rfl, hlp⟩ :=
    cutAt d' (by rw [← hdim]; exact le_dimSum_of_mem_boundaries hmem.1) hmem.2
  refine ⟨l, r, p, q, rfl, boundaries_injective ?_⟩
  rw [boundaries_cut, hlp]
  refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hmem.1 hsub) ?_).symm
  rw [Finset.card_insert_of_notMem hmem.2]
  omega

/-- **Two boundaries more are two cuts, in one of exactly two species**: one bead cut in three, or
two distinct beads each cut in two — according as the two new boundaries fall in one bead of the
coarsening or in two. -/
theorem exists_cuts_of_length_add_two {d d' : List ℕ+} (hdim : dimSum d = dimSum d')
    (hsub : boundaries d' ⊆ boundaries d) (hlen : d.length = d'.length + 2) :
    (∃ (l r : List ℕ+) (x y z : ℕ+), d' = l ++ (x + y + z) :: r ∧ d = l ++ x :: y :: z :: r) ∨
    (∃ (l m r : List ℕ+) (x y x' y' : ℕ+),
        d' = l ++ (x + y) :: (m ++ (x' + y') :: r) ∧
        d = l ++ x :: y :: (m ++ x' :: y' :: r)) := by
  -- The two boundaries `s < t` that `d` has and `d'` has not.
  obtain ⟨s, t, hst, hset⟩ : ∃ s t, s < t ∧ boundaries d \ boundaries d' = {s, t} := by
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp (by
      rw [Finset.card_sdiff_of_subset hsub, card_boundaries, card_boundaries]; omega)
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, h, hset⟩
    · exact ⟨y, x, by omega, hset.trans (Finset.pair_comm x y)⟩
  have hsmem : s ∈ boundaries d \ boundaries d' := by rw [hset]; exact Finset.mem_insert_self _ _
  have htmem : t ∈ boundaries d \ boundaries d' := by
    rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
  obtain ⟨hsd, hsd'⟩ := Finset.mem_sdiff.mp hsmem
  obtain ⟨htd, htd'⟩ := Finset.mem_sdiff.mp htmem
  have hd : boundaries d = insert s (insert t (boundaries d')) := by
    rw [← Finset.union_sdiff_of_subset hsub, hset]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- Cut `d'` at the upper boundary; the lower one is either inside that same bead, or before it.
  obtain ⟨l₀, r₀, P, Q, rfl, hPt⟩ :=
    cutAt d' (by rw [← hdim]; exact le_dimSum_of_mem_boundaries htd) htd'
  have hl₀ : dimSum l₀ ∈ boundaries (l₀ ++ (P + Q) :: r₀) :=
    boundaries_prefix_subset l₀ _ (dimSum_mem_boundaries l₀)
  rcases Nat.lt_or_ge (dimSum l₀) s with hlt | hge
  · -- both boundaries are interior to the bead `P + Q`, which is cut in three
    obtain ⟨x, hx⟩ : ∃ x : ℕ+, (x : ℕ) = s - dimSum l₀ := ⟨⟨_, by omega⟩, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : ℕ+, (y : ℕ) = t - s := ⟨⟨_, by omega⟩, rfl⟩
    have hxyz : x + y + Q = P + Q := PNat.coe_injective (by simp only [PNat.add_coe]; omega)
    have h1 : dimSum l₀ + (x : ℕ) = s := by omega
    have h2 : dimSum l₀ + ((x + y : ℕ+) : ℕ) = t := by rw [PNat.add_coe]; omega
    exact Or.inl ⟨l₀, r₀, x, y, Q, by rw [hxyz], boundaries_injective (by
      rw [hd, boundaries_cut l₀ (Q :: r₀) x y, boundaries_cut l₀ r₀ (x + y) Q, hxyz, h1, h2])⟩
  · -- the lower boundary is interior to an earlier bead: two beads, each cut in two
    have hslt : s < dimSum l₀ := lt_of_le_of_ne hge fun h => hsd' (by rw [h]; exact hl₀)
    obtain ⟨l, m, x, y, rfl, hlx⟩ :=
      cutAt l₀ (by omega) fun h => hsd' (boundaries_prefix_subset l₀ _ h)
    refine Or.inr ⟨l, m, r₀, x, y, P, Q, by simp, boundaries_injective ?_⟩
    rw [hd, boundaries_cut l (m ++ P :: Q :: r₀) x y,
      show l ++ (x + y) :: (m ++ P :: Q :: r₀) = (l ++ (x + y) :: m) ++ P :: Q :: r₀ by simp,
      boundaries_cut (l ++ (x + y) :: m) r₀ P Q, hlx, hPt]

end CubeChains
