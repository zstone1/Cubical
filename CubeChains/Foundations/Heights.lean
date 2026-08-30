import CubeChains.Foundations.Wedge

/-!
# Foundations/Heights — a dimension list is its set of bead boundaries

`heights d` is the set of totals of the prefixes of `d` (`mem_heights_iff`): `0`, the partial sums,
and `dimSum d`.  It determines `d` (`heights_injective`) and counts its beads (`card_heights`), so
coarsening a shape is deleting boundaries — one deleted boundary is one bead cut in two
(`cutOfLengthSucc`), and the cut is pinned by the height it happens at (`cut_unique`).
-/

open BPSet

namespace CubeChains

/-! ## The boundaries of a dimension list -/

/-- The **bead boundaries** of a dimension list — `0`, the partial sums, and the total. -/
def heights : List ℕ+ → Finset ℕ
  | [] => {0}
  | c :: ds => insert 0 ((heights ds).image (· + (c : ℕ)))

@[simp] theorem heights_nil : heights [] = {0} := rfl

theorem heights_cons (c : ℕ+) (ds : List ℕ+) :
    heights (c :: ds) = insert 0 ((heights ds).image (· + (c : ℕ))) := rfl

/-- **A boundary is the total of a prefix** — the characterization everything below runs on. -/
theorem mem_heights_iff : ∀ {d : List ℕ+} {t : ℕ},
    t ∈ heights d ↔ ∃ l r : List ℕ+, d = l ++ r ∧ dimSum l = t
  | [], _ => by
      rw [heights_nil, Finset.mem_singleton]
      refine ⟨fun h => ⟨[], [], rfl, h.symm⟩, ?_⟩
      rintro ⟨l, r, hlr, rfl⟩
      rw [(List.append_eq_nil_iff.mp hlr.symm).1]
      rfl
  | c :: ds, _ => by
      rw [heights_cons, Finset.mem_insert]
      constructor
      · rintro (rfl | hm)
        · exact ⟨[], c :: ds, rfl, rfl⟩
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨l, r, rfl, rfl⟩ := mem_heights_iff.mp hu
          exact ⟨c :: l, r, rfl, by rw [dimSum_cons]; omega⟩
      · rintro ⟨l, r, hlr, rfl⟩
        rcases l with _ | ⟨e, l'⟩
        · exact Or.inl rfl
        · rw [List.cons_append] at hlr
          obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hlr
          exact Or.inr (Finset.mem_image.mpr
            ⟨dimSum l', mem_heights_iff.mpr ⟨l', r, rfl, rfl⟩, by rw [dimSum_cons]; omega⟩)

theorem zero_mem_heights (d : List ℕ+) : 0 ∈ heights d :=
  mem_heights_iff.mpr ⟨[], d, rfl, rfl⟩

theorem dimSum_mem_heights (d : List ℕ+) : dimSum d ∈ heights d :=
  mem_heights_iff.mpr ⟨d, [], (List.append_nil d).symm, rfl⟩

theorem le_dimSum_of_mem_heights {d : List ℕ+} {t : ℕ} (ht : t ∈ heights d) : t ≤ dimSum d := by
  obtain ⟨l, r, rfl, rfl⟩ := mem_heights_iff.mp ht
  simp

/-- A prefix keeps its own boundaries. -/
theorem heights_prefix_subset (l r : List ℕ+) : heights l ⊆ heights (l ++ r) := by
  intro t ht
  obtain ⟨u, v, rfl, rfl⟩ := mem_heights_iff.mp ht
  exact mem_heights_iff.mpr ⟨u, v ++ r, by rw [List.append_assoc], rfl⟩

theorem coe_mem_heights_cons (c : ℕ+) (ds : List ℕ+) : (c : ℕ) ∈ heights (c :: ds) :=
  mem_heights_iff.mpr ⟨[c], ds, rfl, by simp⟩

/-- Every boundary of a shifted tail is positive, which is what keeps `insert 0` from collapsing. -/
theorem zero_notMem_shift (c : ℕ+) (ds : List ℕ+) :
    0 ∉ (heights ds).image (· + (c : ℕ)) := by
  simp only [Finset.mem_image, not_exists]
  rintro x ⟨-, hx⟩
  exact absurd hx (by have := c.pos; omega)

theorem card_heights : ∀ d : List ℕ+, (heights d).card = d.length + 1
  | [] => rfl
  | c :: ds => by
      rw [heights_cons, Finset.card_insert_of_notMem (zero_notMem_shift c ds),
        Finset.card_image_of_injective _ (add_left_injective ((c : ℕ))), card_heights ds]
      simp [Nat.add_comm]

/-- Concatenation shifts the second list's boundaries. -/
theorem heights_append : ∀ (l r : List ℕ+),
    heights (l ++ r) = heights l ∪ (heights r).image (· + dimSum l)
  | [], r => by
      have h : ∀ x : ℕ, x + dimSum ([] : List ℕ+) = x := fun _ => rfl
      simp only [List.nil_append, heights_nil, h, Finset.image_id']
      exact (Finset.union_eq_right.mpr
        (Finset.singleton_subset_iff.mpr (zero_mem_heights r))).symm
  | c :: l, r => by
      have himg : (heights r).image ((fun x => x + (c : ℕ)) ∘ (fun x => x + dimSum l))
          = (heights r).image (fun x => x + dimSum (c :: l)) :=
        Finset.image_congr fun x _ => by rw [Function.comp_apply, dimSum_cons]; omega
      rw [List.cons_append, heights_cons, heights_cons, heights_append l r, Finset.image_union,
        Finset.image_image, himg, Finset.insert_union]

/-! ## Cutting a bead -/

/-- **A cut adds one boundary.**  Splitting the bead `p + q` in two adds exactly the height at
which it is split. -/
theorem heights_cut (l r : List ℕ+) (p q : ℕ+) :
    heights (l ++ p :: q :: r) = insert (dimSum l + (p : ℕ)) (heights (l ++ (p + q) :: r)) := by
  have hpair : heights (p :: q :: r) = insert (p : ℕ) (heights ((p + q) :: r)) := by
    have himg : (heights r).image ((fun x => x + (p : ℕ)) ∘ (fun x => x + (q : ℕ)))
        = (heights r).image (fun x => x + ((p + q : ℕ+) : ℕ)) :=
      Finset.image_congr fun x _ => by rw [Function.comp_apply, PNat.add_coe]; omega
    rw [heights_cons p (q :: r), heights_cons q r, heights_cons (p + q) r, Finset.image_insert,
      Nat.zero_add, Finset.image_image, himg, Finset.insert_comm]
  rw [heights_append l (p :: q :: r), heights_append l ((p + q) :: r), hpair,
    Finset.image_insert, Finset.union_insert]
  congr 1
  omega

/-- The dimension sum is blind to a cut. -/
theorem dimSum_cut (l r : List ℕ+) (p q : ℕ+) :
    dimSum (l ++ p :: q :: r) = dimSum (l ++ (p + q) :: r) := by
  simp only [dimSum, List.map_append, List.map_cons, List.sum_append, List.sum_cons, PNat.add_coe]
  omega

/-- The height a cut removes is interior to the merged bead, so the merge really is shorter. -/
theorem notMem_heights_cut (l r : List ℕ+) (p q : ℕ+) :
    dimSum l + (p : ℕ) ∉ heights (l ++ (p + q) :: r) := by
  intro hmem
  have hcard := congrArg Finset.card (heights_cut l r p q)
  rw [Finset.insert_eq_self.mpr hmem, card_heights, card_heights] at hcard
  simp only [List.length_append, List.length_cons] at hcard
  omega

/-- Splitting one bead at an interior height. -/
private def splitBead (c : ℕ+) {t : ℕ} (h0 : 0 < t) (hlt : t < (c : ℕ)) :
    Σ' p q : ℕ+, p + q = c ∧ (p : ℕ) = t :=
  ⟨⟨t, h0⟩, ⟨(c : ℕ) - t, by omega⟩,
    PNat.coe_injective (show t + ((c : ℕ) - t) = (c : ℕ) by omega), rfl⟩

/-- **Cutting a shape at a height it does not already have**: `t` is interior to a single bead,
which it splits in two. -/
def cutAt : ∀ (d : List ℕ+) {t : ℕ}, t ≤ dimSum d → t ∉ heights d →
    Σ' (l r : List ℕ+) (p q : ℕ+), d = l ++ (p + q) :: r ∧ dimSum l + (p : ℕ) = t
  | [], t, hle, hnot => absurd (show t ∈ heights ([] : List ℕ+) from
      (show t = 0 by simpa [dimSum] using hle) ▸ zero_mem_heights _) hnot
  | c :: ds, t, hle, hnot => by
      rw [dimSum_cons] at hle
      have h0 : 0 < t := Nat.pos_of_ne_zero fun h => hnot (h ▸ zero_mem_heights _)
      refine dite (t < (c : ℕ)) (fun hlt => ?_) (fun hge => ?_)
      · obtain ⟨p, q, hpq, hp⟩ := splitBead c h0 hlt
        exact ⟨[], ds, p, q, by rw [hpq]; rfl, by simpa [dimSum] using hp⟩
      · have hsub : t - (c : ℕ) ∉ heights ds := fun hmem =>
          hnot (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hmem, by omega⟩))
        obtain ⟨l, r, p, q, hd, hl⟩ := cutAt ds (by omega) hsub
        exact ⟨c :: l, r, p, q, by rw [hd]; rfl, by rw [dimSum_cons]; omega⟩

/-- **An interior boundary splits the shape into two beads.** -/
theorem exists_split_of_mem_heights (d : List ℕ+) {t : ℕ} (ht : t ∈ heights d) (h0 : t ≠ 0)
    (hlast : t ≠ dimSum d) :
    ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ p :: q :: r ∧ dimSum l + (p : ℕ) = t := by
  obtain ⟨u, v, rfl, rfl⟩ := mem_heights_iff.mp ht
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

private theorem le_of_heights_cons_eq {x y : ℕ+} {xs ys : List ℕ+}
    (h : heights (x :: xs) = heights (y :: ys)) : (y : ℕ) ≤ (x : ℕ) := by
  have hm : (x : ℕ) ∈ heights (y :: ys) := by rw [← h]; exact coe_mem_heights_cons x xs
  rw [heights_cons, Finset.mem_insert] at hm
  rcases hm with h0 | himg
  · exact absurd h0 (by have := x.pos; omega)
  · obtain ⟨u, -, hu⟩ := Finset.mem_image.mp himg
    omega

theorem heights_injective : ∀ {d d' : List ℕ+}, heights d = heights d' → d = d'
  | [], [], _ => rfl
  | [], c :: ds, h => by
      have hm : (c : ℕ) ∈ heights ([] : List ℕ+) := by rw [h]; exact coe_mem_heights_cons c ds
      rw [heights_nil, Finset.mem_singleton] at hm
      exact absurd hm (by have := c.pos; omega)
  | c :: ds, [], h => by
      have hm : (c : ℕ) ∈ heights ([] : List ℕ+) := by
        rw [← h]; exact coe_mem_heights_cons c ds
      rw [heights_nil, Finset.mem_singleton] at hm
      exact absurd hm (by have := c.pos; omega)
  | c :: ds, c' :: ds', h => by
      obtain rfl : c = c' :=
        PNat.coe_injective (le_antisymm (le_of_heights_cons_eq h.symm) (le_of_heights_cons_eq h))
      have himg : (heights ds).image (· + (c : ℕ)) = (heights ds').image (· + (c : ℕ)) := by
        rw [heights_cons, heights_cons] at h
        rw [← Finset.erase_insert (zero_notMem_shift c ds), h,
          Finset.erase_insert (zero_notMem_shift c ds')]
      exact congrArg (c :: ·)
        (heights_injective (Finset.image_injective (add_left_injective ((c : ℕ))) himg))

/-- **A cut is pinned by the height at which it happens**, and that is the one boundary the merge
loses — so two presentations of one pair of shapes as "the bead `p + q`, cut" agree throughout. -/
theorem cut_unique {l r l' r' : List ℕ+} {p q p' q' : ℕ+}
    (h₁ : l ++ (p + q) :: r = l' ++ (p' + q') :: r')
    (h₂ : l ++ p :: q :: r = l' ++ p' :: q' :: r') :
    l = l' ∧ p = p' ∧ q = q' ∧ r = r' := by
  have hnot := notMem_heights_cut l r p q
  have hins : insert (dimSum l + (p : ℕ)) (heights (l ++ (p + q) :: r))
      = insert (dimSum l' + (p' : ℕ)) (heights (l ++ (p + q) :: r)) := by
    rw [← heights_cut, h₂, heights_cut, h₁]
  have ht : dimSum l + (p : ℕ) = dimSum l' + (p' : ℕ) := by
    have hmem : dimSum l + (p : ℕ)
        ∈ insert (dimSum l' + (p' : ℕ)) (heights (l ++ (p + q) :: r)) := by
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
    (hsub : heights d' ⊆ heights d) (hlen : d.length = d'.length + 1) :
    Σ' (l r : List ℕ+) (p q : ℕ+), d' = l ++ (p + q) :: r ∧ d = l ++ p :: q :: r := by
  have hcard : (heights d).card = (heights d').card + 1 := by
    rw [card_heights, card_heights]; omega
  have hne : (heights d \ heights d').Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
  have hmem := Finset.mem_sdiff.mp ((heights d \ heights d').min'_mem hne)
  obtain ⟨l, r, p, q, rfl, hlp⟩ :=
    cutAt d' (by rw [← hdim]; exact le_dimSum_of_mem_heights hmem.1) hmem.2
  refine ⟨l, r, p, q, rfl, heights_injective ?_⟩
  rw [heights_cut, hlp]
  refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hmem.1 hsub) ?_).symm
  rw [Finset.card_insert_of_notMem hmem.2]
  omega

/-- **Two boundaries more are two cuts, in one of exactly two species**: one bead cut in three, or
two distinct beads each cut in two — according as the two new boundaries fall in one bead of the
coarsening or in two. -/
theorem exists_cuts_of_length_add_two {d d' : List ℕ+} (hdim : dimSum d = dimSum d')
    (hsub : heights d' ⊆ heights d) (hlen : d.length = d'.length + 2) :
    (∃ (l r : List ℕ+) (x y z : ℕ+), d' = l ++ (x + y + z) :: r ∧ d = l ++ x :: y :: z :: r) ∨
    (∃ (l m r : List ℕ+) (x y x' y' : ℕ+),
        d' = l ++ (x + y) :: (m ++ (x' + y') :: r) ∧
        d = l ++ x :: y :: (m ++ x' :: y' :: r)) := by
  -- The two boundaries `s < t` that `d` has and `d'` has not.
  obtain ⟨s, t, hst, hset⟩ : ∃ s t, s < t ∧ heights d \ heights d' = {s, t} := by
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp (by
      rw [Finset.card_sdiff_of_subset hsub, card_heights, card_heights]; omega)
    rcases Nat.lt_or_ge x y with h | h
    · exact ⟨x, y, h, hset⟩
    · exact ⟨y, x, by omega, hset.trans (Finset.pair_comm x y)⟩
  have hsmem : s ∈ heights d \ heights d' := by rw [hset]; exact Finset.mem_insert_self _ _
  have htmem : t ∈ heights d \ heights d' := by
    rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
  obtain ⟨hsd, hsd'⟩ := Finset.mem_sdiff.mp hsmem
  obtain ⟨htd, htd'⟩ := Finset.mem_sdiff.mp htmem
  have hd : heights d = insert s (insert t (heights d')) := by
    rw [← Finset.union_sdiff_of_subset hsub, hset]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- Cut `d'` at the upper boundary; the lower one is either inside that same bead, or before it.
  obtain ⟨l₀, r₀, P, Q, rfl, hPt⟩ :=
    cutAt d' (by rw [← hdim]; exact le_dimSum_of_mem_heights htd) htd'
  have hl₀ : dimSum l₀ ∈ heights (l₀ ++ (P + Q) :: r₀) :=
    heights_prefix_subset l₀ _ (dimSum_mem_heights l₀)
  rcases Nat.lt_or_ge (dimSum l₀) s with hlt | hge
  · -- both boundaries are interior to the bead `P + Q`, which is cut in three
    obtain ⟨x, hx⟩ : ∃ x : ℕ+, (x : ℕ) = s - dimSum l₀ := ⟨⟨_, by omega⟩, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : ℕ+, (y : ℕ) = t - s := ⟨⟨_, by omega⟩, rfl⟩
    have hxyz : x + y + Q = P + Q := PNat.coe_injective (by simp only [PNat.add_coe]; omega)
    have h1 : dimSum l₀ + (x : ℕ) = s := by omega
    have h2 : dimSum l₀ + ((x + y : ℕ+) : ℕ) = t := by rw [PNat.add_coe]; omega
    exact Or.inl ⟨l₀, r₀, x, y, Q, by rw [hxyz], heights_injective (by
      rw [hd, heights_cut l₀ (Q :: r₀) x y, heights_cut l₀ r₀ (x + y) Q, hxyz, h1, h2])⟩
  · -- the lower boundary is interior to an earlier bead: two beads, each cut in two
    have hslt : s < dimSum l₀ := lt_of_le_of_ne hge fun h => hsd' (by rw [h]; exact hl₀)
    obtain ⟨l, m, x, y, rfl, hlx⟩ :=
      cutAt l₀ (by omega) fun h => hsd' (heights_prefix_subset l₀ _ h)
    refine Or.inr ⟨l, m, r₀, x, y, P, Q, by simp, heights_injective ?_⟩
    rw [hd, heights_cut l (m ++ P :: Q :: r₀) x y,
      show l ++ (x + y) :: (m ++ P :: Q :: r₀) = (l ++ (x + y) :: m) ++ P :: Q :: r₀ by simp,
      heights_cut (l ++ (x + y) :: m) r₀ P Q, hlx, hPt]

end CubeChains
