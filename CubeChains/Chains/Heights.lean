import CubeChains.Chains.MergeGenerate

/-!
# Chains/Heights — a dimension list is its set of bead boundaries

`heights d` is the set of positions at which `d` is cut: `0`, the partial sums, and `dimSum d`.  It
determines `d` (`heights_injective`), a single bead merge deletes exactly one of them
(`heights_cut`), and the merges generate, so `heights b ⊆ heights a` is exactly the coarsening
relation (`coarser_iff`) and hence exactly the existence of a chain morphism (`nonempty_hom_iff`).
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

/-! ## A coarsening is a composite of single merges

Every boundary the target loses is a bead merge, so the whole relation `heights d' ⊆ heights d`
is realised by merging one junction at a time. -/

/-- **Merging one junction at a time.**  Induct on the boundaries still to be removed. -/
private theorem nonempty_wedgeHom_aux : ∀ (k : ℕ) (d d' : List ℕ+), dimSum d = dimSum d' →
    heights d' ⊆ heights d → (heights d).card ≤ (heights d').card + k →
    Nonempty (⋁d ⟶ ⋁d') := by
  intro k
  induction k with
  | zero =>
      intro d d' _ hsub hk
      obtain rfl := heights_injective (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      exact ⟨𝟙 _⟩
  | succ k ih =>
      intro d d' hdim hsub hk
      by_cases heq : heights d = heights d'
      · obtain rfl := heights_injective heq
        exact ⟨𝟙 _⟩
      obtain ⟨t, htd, htd'⟩ :=
        Finset.exists_of_ssubset (hsub.ssubset_of_ne fun h => heq h.symm)
      have h0 : t ≠ 0 := fun h => htd' (h ▸ zero_mem_heights d')
      have hlast : t ≠ dimSum d := fun h =>
        htd' (by rw [h, hdim]; exact dimSum_mem_heights d')
      obtain ⟨l, r, p, q, rfl, rfl⟩ := exists_split_of_mem_heights d htd h0 hlast
      have hcut := heights_cut l r p q
      have hnm := notMem_heights_cut l r p q
      have hcard : (heights (l ++ p :: q :: r)).card
          = (heights (l ++ (p + q) :: r)).card + 1 := by
        rw [hcut, Finset.card_insert_of_notMem hnm]
      refine (ih (l ++ (p + q) :: r) d' ((dimSum_cut l r p q).symm.trans hdim) ?_ (by omega)).map
        fun ψ => ChainCat.Hom.φ (ChainCat.mergeHom l r p q) ≫ ψ
      intro x hx
      rcases Finset.mem_insert.mp (hcut ▸ hsub hx) with rfl | hx'
      · exact absurd hx htd'
      · exact hx'

end CubeChains

namespace ChainCat

open CubeChains

variable {K : BPSet}

/-! ## Read back in `Ch K`

A morphism removes boundaries and nothing else, and the merges generate, so the whole hom-set
question is settled by `heights`. -/

/-- Boundary containment, as a morphism property. -/
def HeightsSub (K : BPSet) : MorphismProperty (Ch K) :=
  fun a b _ => heights b.dims ⊆ heights a.dims

instance (K : BPSet) : (HeightsSub K).IsMultiplicative where
  id_mem _ := Finset.Subset.refl _
  comp_mem _ _ hf hg := hg.trans hf

/-- A single bead merge deletes exactly the boundary it merges at. -/
theorem heightsSub_of_merge {a b : Ch K} {f : a ⟶ b} (h : merge K f) : HeightsSub K f := by
  obtain ⟨d, -⟩ := h
  rw [HeightsSub, d.src_dims, d.tgt_dims, heights_cut]
  exact Finset.subset_insert _ _

theorem Winf_le_heightsSub (K : BPSet) : Winf K ≤ HeightsSub K := by
  rw [← multiplicativeClosure_merge K, MorphismProperty.multiplicativeClosure_le_iff]
  exact fun _ _ _ hm => heightsSub_of_merge hm

/-- **A refinement inherits every boundary of its coarsening** — a merge with the same endpoints
exists, and the merges are generated by single cuts. -/
theorem heights_subset_of_hom {a b : Ch K} (f : a ⟶ b) : heights b.dims ⊆ heights a.dims := by
  obtain ⟨φ, hφ⟩ := coarser_iff_exists_pos.mp (nonempty_wedgeHom_iff_coarser.mp ⟨Hom.φ f⟩)
  exact Winf_le_heightsSub Zbp (zHom φ) ((Winf_iff_pos (zHom φ)).mpr hφ)

/-- **A coarsening is an inclusion of boundary sets.** -/
theorem coarser_iff {d d' : List ℕ+} :
    Coarser d d' ↔ dimSum d = dimSum d' ∧ heights d' ⊆ heights d := by
  refine ⟨fun h => ?_, fun ⟨hdim, hsub⟩ => nonempty_wedgeHom_iff_coarser.mp
    (nonempty_wedgeHom_aux (heights d).card d d' hdim hsub (by omega))⟩
  obtain ⟨φ, -⟩ := coarser_iff_exists_pos.mp h
  exact ⟨serialWedge_dimSum_eq φ, heights_subset_of_hom (zHom φ)⟩

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings**: a morphism exists precisely when the
target's boundaries are among the source's. -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ heights b.dims ⊆ heights a.dims :=
  ⟨fun ⟨f⟩ => ⟨strandsEq f, heights_subset_of_hom f⟩,
   fun h => (nonempty_wedgeHom_iff_coarser.mpr (coarser_iff.mpr h)).map
     fun φ => ⟨φ, Subsingleton.elim _ _⟩⟩

end ChainCat
