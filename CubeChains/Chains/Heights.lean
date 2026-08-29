import CubeChains.Chains.AtomPair

/-!
# Chains/Heights — a dimension list is its set of bead boundaries

`heights d` is the set of positions at which `d` is cut: `0`, the partial sums, and `dimSum d`.  It
determines `d` (`heights_injective`), and `heights b ⊆ heights a` is exactly the coarsening
relation.  The bridge to `Braid/Blocks` is `heights_succ_iff`: `x + 1` is a boundary exactly where
`blockOfPos` jumps.

Read back in `Ch Zbp` (`nonempty_hom_iff`): a morphism `a ⟶ b` exists exactly at a coarsening, and
is then a permutation preserving the beads of `b` and rising inside those of `a` — the converse of
`exists_crossPermAt_blocks`.
-/

open CategoryTheory Equiv BPSet CubeChain

namespace CubeChains

/-! ## The boundaries of a dimension list -/

/-- The **bead boundaries** of a dimension list — `0`, the partial sums, and the total. -/
def heights : List ℕ+ → Finset ℕ
  | [] => {0}
  | c :: ds => insert 0 ((heights ds).image (· + (c : ℕ)))

@[simp] theorem heights_nil : heights [] = {0} := rfl

theorem heights_cons (c : ℕ+) (ds : List ℕ+) :
    heights (c :: ds) = insert 0 ((heights ds).image (· + (c : ℕ))) := rfl

theorem zero_mem_heights : ∀ d : List ℕ+, 0 ∈ heights d
  | [] => Finset.mem_singleton_self 0
  | _ :: _ => Finset.mem_insert_self _ _

/-- Every boundary of a shifted tail is positive, which is what keeps `insert 0` from collapsing. -/
theorem zero_notMem_shift (c : ℕ+) (ds : List ℕ+) :
    0 ∉ (heights ds).image (· + (c : ℕ)) := by
  simp only [Finset.mem_image, not_exists]
  rintro x ⟨-, hx⟩
  exact absurd hx (by have := c.pos; omega)

theorem coe_mem_heights_cons (c : ℕ+) (ds : List ℕ+) : (c : ℕ) ∈ heights (c :: ds) := by
  rw [heights_cons]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨0, zero_mem_heights ds, by omega⟩)

theorem card_heights : ∀ d : List ℕ+, (heights d).card = d.length + 1
  | [] => rfl
  | c :: ds => by
      rw [heights_cons, Finset.card_insert_of_notMem (zero_notMem_shift c ds),
        Finset.card_image_of_injective _ (add_left_injective ((c : ℕ))), card_heights ds]
      simp [Nat.add_comm]

theorem le_dimSum_of_mem_heights : ∀ {d : List ℕ+} {t : ℕ}, t ∈ heights d → t ≤ dimSum d
  | [], t, ht => le_of_eq (Finset.mem_singleton.mp ht)
  | c :: ds, t, ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact Nat.zero_le _
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht'
        have := le_dimSum_of_mem_heights hu
        rw [dimSum_cons]
        omega

theorem dimSum_mem_heights : ∀ d : List ℕ+, dimSum d ∈ heights d
  | [] => Finset.mem_singleton_self 0
  | c :: ds => by
      rw [heights_cons]
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨dimSum ds, dimSum_mem_heights ds, ?_⟩)
      rw [dimSum_cons]
      omega

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

/-- **A height the shape does not cut is interior to one bead**, which it splits in two. -/
theorem exists_cut_of_notMem_heights : ∀ (d : List ℕ+) {t : ℕ}, t ≤ dimSum d → t ∉ heights d →
    ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ (p + q) :: r ∧ dimSum l + (p : ℕ) = t
  | [], t, hle, hnot => by
      exact absurd (show t ∈ heights ([] : List ℕ+) from
        (show t = 0 by simpa [dimSum] using hle) ▸ zero_mem_heights _) hnot
  | c :: ds, t, hle, hnot => by
      rw [dimSum_cons] at hle
      have h0 : t ≠ 0 := fun h => hnot (h ▸ zero_mem_heights _)
      rcases Nat.lt_or_ge t (c : ℕ) with hlt | hge
      · obtain ⟨p, hp⟩ : ∃ p : ℕ+, (p : ℕ) = t := ⟨⟨t, by omega⟩, rfl⟩
        obtain ⟨q, hq⟩ : ∃ q : ℕ+, (q : ℕ) = (c : ℕ) - t := ⟨⟨(c : ℕ) - t, by omega⟩, rfl⟩
        have hpq : p + q = c := PNat.coe_injective (by rw [PNat.add_coe, hp, hq]; omega)
        exact ⟨[], ds, p, q, by rw [hpq]; rfl, by simpa [dimSum] using hp⟩
      · have hne : t ≠ (c : ℕ) := fun h => hnot (h ▸ coe_mem_heights_cons c ds)
        have hsub : t - (c : ℕ) ∉ heights ds := fun hmem =>
          hnot (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, hmem, by omega⟩))
        obtain ⟨l, r, p, q, hd, hl⟩ := exists_cut_of_notMem_heights ds (by omega) hsub
        exact ⟨c :: l, r, p, q, by rw [hd]; rfl, by rw [dimSum_cons]; omega⟩

/-- **An interior boundary splits the shape into two beads.** -/
theorem exists_split_of_mem_heights : ∀ (d : List ℕ+) {t : ℕ}, t ∈ heights d → t ≠ 0 →
    t ≠ dimSum d → ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ p :: q :: r ∧ dimSum l + (p : ℕ) = t
  | [], _, hmem, h0, _ => absurd (Finset.mem_singleton.mp hmem) h0
  | c :: ds, t, hmem, h0, hlast => by
      rw [heights_cons] at hmem
      rcases Finset.mem_insert.mp hmem with rfl | himg
      · exact absurd rfl h0
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp himg
      rw [dimSum_cons] at hlast
      rcases Nat.eq_zero_or_pos u with rfl | hupos
      · rcases ds with _ | ⟨q, r⟩
        · exact absurd (by simp [dimSum]) hlast
        · exact ⟨[], r, c, q, rfl, by simp [dimSum]⟩
      · obtain ⟨l, r, p, q, hd, hl⟩ := exists_split_of_mem_heights ds hu (by omega)
          (fun h => hlast (by omega))
        exact ⟨c :: l, r, p, q, by rw [hd]; rfl, by rw [dimSum_cons]; omega⟩

/-! ## The bridge to `blockOfPos` -/

/-- **A boundary is where the block index jumps.** -/
theorem heights_succ_iff : ∀ (d : List ℕ+) {x : ℕ}, x < dimSum d →
    (x + 1 ∈ heights d ↔ blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) x
      < blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (x + 1))
  | [], x, hx => absurd hx (by simp [dimSum])
  | c :: ds, x, hx => by
      rw [dimSum_cons] at hx
      rw [List.map_cons, heights_cons]
      rcases Nat.lt_or_ge (x + 1) (c : ℕ) with hlt | hge
      · rw [blockOfPos_cons_of_lt _ (by omega), blockOfPos_cons_of_lt _ hlt]
        simp only [Finset.mem_insert, Finset.mem_image, lt_irrefl, iff_false, not_or]
        exact ⟨by omega, by rintro ⟨u, -, hu⟩; omega⟩
      rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · rw [blockOfPos_cons_of_lt _ (by omega), blockOfPos_cons_of_le _ (by omega)]
        simp only [Finset.mem_insert, Finset.mem_image]
        exact iff_of_true (Or.inr ⟨0, zero_mem_heights ds, by omega⟩) (by omega)
      · have hc : (c : ℕ) ≤ x := by omega
        have hx' : x - (c : ℕ) < dimSum ds := by omega
        have hIH := heights_succ_iff ds hx'
        rw [blockOfPos_cons_of_le _ hc, blockOfPos_cons_of_le _ (show (c : ℕ) ≤ x + 1 by omega),
          show x + 1 - (c : ℕ) = x - (c : ℕ) + 1 by omega]
        simp only [Finset.mem_insert, Finset.mem_image]
        constructor
        · rintro (h | ⟨u, hu, hu'⟩)
          · omega
          · obtain rfl : u = x - (c : ℕ) + 1 := by omega
            have := hIH.mp hu
            omega
        · intro hlt
          exact Or.inr ⟨x - (c : ℕ) + 1, hIH.mpr (by omega), by omega⟩

/-- **Boundaries are inherited by a refinement.**  If every bead of `d` sits inside a bead of `d'`
then `d'` cuts only where `d` does. -/
theorem heights_subset_of_blocks {d d' : List ℕ+} (hdim : dimSum d = dimSum d')
    (h : ∀ x y : ℕ, x < dimSum d → y < dimSum d →
      blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) x = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) y →
      blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) x
        = blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) y) :
    heights d' ⊆ heights d := by
  intro t ht
  have htle := le_dimSum_of_mem_heights ht
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact zero_mem_heights d
  obtain ⟨x, rfl⟩ : ∃ x, t = x + 1 := ⟨t - 1, by omega⟩
  rcases Nat.eq_or_lt_of_le htle with heq | hlt
  · rw [heq, ← hdim]; exact dimSum_mem_heights d
  · have hx : x < dimSum d := by omega
    have hne := (heights_succ_iff d' (show x < dimSum d' by omega)).mp ht
    rw [heights_succ_iff d hx]
    by_contra hcon
    exact absurd (h x (x + 1) hx (by omega)
      (le_antisymm (blockOfPos_monotone _ (Nat.le_succ x)) (Nat.not_lt.mp hcon))) (by omega)

/-- **…and conversely**: a shape with fewer boundaries does not separate what the finer one
joins. -/
theorem blocks_of_heights_subset {d d' : List ℕ+} (hdim : dimSum d = dimSum d')
    (hsub : heights d' ⊆ heights d) {x y : ℕ} (hx : x < dimSum d) (hy : y < dimSum d)
    (h : blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) x
      = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) y) :
    blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) x
      = blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) y := by
  have key : ∀ (k z : ℕ), z + k < dimSum d →
      blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) z
          = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (z + k) →
        blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) z
          = blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) (z + k) := by
    intro k
    induction k with
    | zero => intro z _ _; rfl
    | succ k ih =>
        intro z hlt hb
        have hmid : blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) z
            = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (z + k) :=
          le_antisymm (blockOfPos_monotone _ (by omega))
            (le_of_le_of_eq (blockOfPos_monotone _ (show z + k ≤ z + (k + 1) by omega)) hb.symm)
        have hjump : blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (z + k)
            = blockOfPos (d.map fun c : ℕ+ => (c : ℕ)) (z + k + 1) := by
          rw [show z + (k + 1) = z + k + 1 by omega] at hb
          omega
        have hnot : (z + k) + 1 ∉ heights d := fun hmem =>
          absurd ((heights_succ_iff d (show z + k < dimSum d by omega)).mp hmem) (by omega)
        have hd' : blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) (z + k)
            = blockOfPos (d'.map fun c : ℕ+ => (c : ℕ)) (z + k + 1) :=
          le_antisymm (blockOfPos_monotone _ (by omega))
            (Nat.not_lt.mp fun hlt' => hnot (hsub
              ((heights_succ_iff d' (show z + k < dimSum d' by omega)).mpr hlt')))
        rw [show z + (k + 1) = z + k + 1 by omega, ← hd']
        exact ih z (by omega) hmid
  rcases Nat.le_total x y with hxy | hxy
  · have hk : x + (y - x) = y := by omega
    have hres := key (y - x) x (by omega) (by rw [hk]; exact h)
    rwa [hk] at hres
  · have hk : y + (x - y) = x := by omega
    have hres := key (x - y) y (by omega) (by rw [hk]; exact h.symm)
    rw [hk] at hres
    exact hres.symm

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

end CubeChains

namespace ChainCat

open CubeChains

variable {K : BPSet} {N : ℕ}

/-! ## A hom-set of `Ch Zbp`, read on `Fin N`

`exists_crossPermAt_blocks` realises a permutation preserving the beads of the target and rising
inside those of the source.  Here is its converse: every chain morphism is such a permutation, and
its two shapes are related by `heights`. -/

/-- The event a strand names. -/
def eventOf {a : Ch K} (ha : dimSum a.dims = N) (x : Fin N) : beadEvent a.dims :=
  (strand a).symm ((finCongr ha).symm x)

@[simp] theorem pos_eventOf {a : Ch K} (ha : dimSum a.dims = N) (x : Fin N) :
    (pos (eventOf ha x) : ℕ) = (x : ℕ) := by
  rw [← strand_val a, eventOf, Equiv.apply_symm_apply]
  rfl

/-- The source block of a strand is the bead of its event. -/
theorem blockOfPos_val {a : Ch K} (ha : dimSum a.dims = N) (x : Fin N) :
    blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ) = ((eventOf ha x).1 : ℕ) := by
  rw [← pos_eventOf ha x, blockOfPos_pos]

/-- The crossing permutation moves a strand to the flattening of its event's image. -/
theorem crossPermAt_val {a b : Ch K} (ha : dimSum a.dims = N) (f : a ⟶ b) (x : Fin N) :
    ((crossPermAt ha f x : Fin N) : ℕ) = (pos (coordMap (Hom.φ f) (eventOf ha x)) : ℕ) := by
  rw [crossPermAt_apply_val, ← show (strand a) (eventOf ha x) = (finCongr ha).symm x from
    Equiv.apply_symm_apply _ _, crossPerm_strand]
  rfl

theorem blockOfPos_crossPermAt {a b : Ch K} (ha : dimSum a.dims = N) (f : a ⟶ b) (x : Fin N) :
    blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) ((crossPermAt ha f x : Fin N) : ℕ)
      = ((coordMap (Hom.φ f) (eventOf ha x)).1 : ℕ) := by
  rw [crossPermAt_val, blockOfPos_pos]

/-- **A chain morphism preserves the beads of its target** — its permutation is parabolic.  The
bead map is monotone with the target's fibre sizes, and a monotone map is pinned by those. -/
theorem crossPermAt_mem_parabolic {a b : Ch K} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    crossPermAt ha f ∈ parabolic N (b.dims.map fun c : ℕ+ => (c : ℕ)) := by
  have hu : Monotone fun x : Fin N =>
      blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ) := fun _ _ h =>
    blockOfPos_monotone _ h
  have hmono : Monotone ((fun x : Fin N =>
      blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)) ∘ (crossPermAt ha f)) := by
    intro x y hxy
    simp only [Function.comp_apply]
    rw [blockOfPos_crossPermAt, blockOfPos_crossPermAt]
    refine Fin.le_def.mp ?_
    have hb' := (isShuffle_coordMapEquiv (Hom.φ f)).bead (eventOf ha x) (eventOf ha y)
      (Fin.le_def.mpr (by rw [← blockOfPos_val ha, ← blockOfPos_val ha]
                          exact blockOfPos_monotone _ (Fin.le_def.mp hxy)))
    simpa only [coordMapEquiv_apply] using hb'
  exact fun i => congrFun (comp_perm_eq_of_monotone hu (crossPermAt ha f) hmono) i

/-- **A chain morphism rises inside each bead of its source.** -/
theorem crossPermAt_lt {a b : Ch K} (ha : dimSum a.dims = N) (f : a ⟶ b) {x y : Fin N}
    (hxy : blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
      = blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ)) (hlt : x < y) :
    crossPermAt ha f x < crossPermAt ha f y := by
  have hin := (isShuffle_coordMapEquiv (Hom.φ f)).inner (eventOf ha x) (eventOf ha y)
    (Fin.ext (by rw [← blockOfPos_val ha, ← blockOfPos_val ha, hxy]))
    (Fin.lt_def.mpr (by rw [pos_eventOf, pos_eventOf]; exact Fin.lt_def.mp hlt))
  rw [Fin.lt_def, crossPermAt_val, crossPermAt_val]
  simpa only [coordMapEquiv_apply, Fin.lt_def] using hin

/-- **The target's beads are unions of the source's** — the coarsening the two shapes stand in. -/
theorem blockOfPos_eq_of_hom {a b : Ch K} (ha : dimSum a.dims = N) (f : a ⟶ b) {x y : Fin N}
    (hxy : blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
      = blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ)) :
    blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
      = blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ) := by
  have hpar := crossPermAt_mem_parabolic ha f
  have hbead := (isShuffle_coordMapEquiv (Hom.φ f)).bead_eq (p := eventOf ha x) (q := eventOf ha y)
    (Fin.ext (by rw [← blockOfPos_val ha, ← blockOfPos_val ha, hxy]))
  rw [← mem_parabolic.mp hpar x, ← mem_parabolic.mp hpar y, blockOfPos_crossPermAt,
    blockOfPos_crossPermAt]
  simpa only [coordMapEquiv_apply] using congrArg Fin.val hbead

/-- **A refinement inherits every boundary of its coarsening.** -/
theorem heights_subset_of_hom {a b : Ch K} (f : a ⟶ b) : heights b.dims ⊆ heights a.dims :=
  heights_subset_of_blocks (strandsEq f) fun x y hx hy h =>
    blockOfPos_eq_of_hom rfl f (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h

/-- `exists_crossPermAt_blocks`, read at objects of `Ch Zbp`: a chain of `Zbp` **is** its dimension
list, so the classifying maps are `Subsingleton`-equal to the canonical ones. -/
theorem exists_crossPermAt_hom {a b : Ch Zbp} (ha : dimSum a.dims = N) (hb : dimSum b.dims = N)
    {σ : Equiv.Perm (Fin N)}
    (hcoarse : ∀ x y : Fin N,
      blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
          = blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ) →
      blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
          = blockOfPos (b.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ))
    (hpar : σ ∈ parabolic N (b.dims.map fun c : ℕ+ => (c : ℕ)))
    (hin : ∀ x y : Fin N, blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (x : ℕ)
        = blockOfPos (a.dims.map fun c : ℕ+ => (c : ℕ)) (y : ℕ) → x < y → σ x < σ y) :
    ∃ f : a ⟶ b, crossPermAt ha f = σ := by
  obtain ⟨da, ma⟩ := a
  obtain ⟨db, mb⟩ := b
  obtain rfl : ma = (zObj da).map := Subsingleton.elim _ _
  obtain rfl : mb = (zObj db).map := Subsingleton.elim _ _
  exact exists_crossPermAt_blocks ha hb hcoarse hpar hin

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings**: a morphism exists precisely when the
target's boundaries are among the source's. -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ heights b.dims ⊆ heights a.dims :=
  ⟨fun ⟨f⟩ => ⟨strandsEq f, heights_subset_of_hom f⟩, fun ⟨hdim, hsub⟩ =>
    (exists_crossPermAt_hom rfl hdim.symm
      (fun x y h => blocks_of_heights_subset hdim hsub x.isLt y.isLt h)
      (Subgroup.one_mem _) (fun _ _ _ hlt => hlt)).elim fun f _ => ⟨f⟩⟩

end ChainCat
