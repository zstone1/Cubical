import CubeChains.Concurrency.Merge.MergeBraid
import CubeChains.Concurrency.Grading.ShuffleHom

/-!
# Concurrency/Merge/MergeGenerate — the canonical bead merges generate `W`

A dimension list is **coarsened** by summing consecutive beads, and a coarsening is realised by
exactly one wedge map — the monotone one (`ShuffleHom`).  So a monotone refinement that loses a
bead factors through the canonical merge at any junction its target does not separate, and
induction on the bead count exhausts it.  At codimension one the middle map is forced to be
`cubeMerge`, so the generators are exactly the codimension-one members.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace CubeChains

variable {d d' d'' : List ℕ+}

/-! ### Locating a junction the target does not separate -/

/-- A monotone map that cannot be injective agrees on some adjacent pair. -/
theorem exists_adjacent_eq {n m : ℕ} (γ : Fin n → Fin m) (hmono : Monotone γ) (hnm : m < n) :
    ∃ i : ℕ, ∃ hi : i + 1 < n, γ ⟨i, Nat.lt_of_succ_lt hi⟩ = γ ⟨i + 1, hi⟩ := by
  by_contra hcon0
  have hcon : ∀ (i : ℕ) (hi : i + 1 < n), γ ⟨i, Nat.lt_of_succ_lt hi⟩ ≠ γ ⟨i + 1, hi⟩ :=
    fun i hi h => hcon0 ⟨i, hi, h⟩
  have key : ∀ i, ∀ hi : i < n, i ≤ (γ ⟨i, hi⟩ : ℕ) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
        intro hi
        have hj : j < n := Nat.lt_of_succ_lt hi
        have hle : (γ ⟨j, hj⟩ : ℕ) ≤ (γ ⟨j + 1, hi⟩ : ℕ) :=
          Fin.le_def.mp (hmono (Fin.mk_le_mk.mpr (Nat.le_succ j)))
        have hne : (γ ⟨j, hj⟩ : ℕ) ≠ (γ ⟨j + 1, hi⟩ : ℕ) := fun hh => hcon j hi (Fin.ext hh)
        have hih := ih hj
        omega
  have hn1 : n - 1 < n := by omega
  have hlast := key (n - 1) hn1
  have hb := (γ ⟨n - 1, hn1⟩).isLt
  omega

/-- A dimension list with a junction at `i` splits around the two beads there. -/
theorem exists_split_at (d : List ℕ+) {i : ℕ} (hi : i + 1 < d.length) :
    ∃ (l r : List ℕ+) (p q : ℕ+), d = l ++ p :: q :: r ∧ l.length = i := by
  refine ⟨d.take i, d.drop (i + 2), d[i]'(by omega), d[i + 1]'hi, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop i d]
    congr 1
    rw [List.drop_eq_getElem_cons (show i < d.length by omega), List.drop_eq_getElem_cons hi]
  · rw [List.length_take]
    omega

end CubeChains

namespace ChainCat

open CubeChains

/-! ### The bead map of a canonical merge -/

/-- **The merge's bead map**: a bead at or before the cut keeps its index, a bead after it drops
by one — so the merged pair is exactly the pair that lands on the cut. -/
theorem mergeBead_cases (l r : List ℕ+) (p q : ℕ+) (e : beadEvent (l ++ p :: q :: r)) :
    (((coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) e).1 : ℕ) = (e.1 : ℕ)
        ∧ (e.1 : ℕ) ≤ l.length)
      ∨ (((coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) e).1 : ℕ) + 1 = (e.1 : ℕ)
        ∧ l.length < (e.1 : ℕ)) := by
  induction e using eventAppendCases (a := l) (b := p :: q :: r) with
  | hl x =>
      refine Or.inl ⟨?_, le_of_lt x.1.isLt⟩
      rw [coordMap_splicePhi_head]
      rfl
  | hr v =>
      rw [coordMap_splicePhi_rest]
      induction v using eventAppendCases (a := [p, q]) (b := r) with
      | hl y =>
          have hy : (y.1 : ℕ) < 2 := y.1.isLt
          rw [coordMap_spliceNil_head]
          have hz : ((coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y).1 : ℕ) = 0 := by
            have h := (coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y).1.isLt
            simp only [List.length_cons, List.length_nil] at h
            omega
          simp only [eventInr_fst_val, eventInl_fst_val, hz]
          omega
      | hr z =>
          rw [coordMap_spliceNil_tail]
          simp only [eventInr_fst_val, List.length_cons, List.length_nil]
          omega

/-- Two events share a bead of the merge only if they already shared one, or if they sit in the
merged pair. -/
theorem mergeBead_pair (l r : List ℕ+) (p q : ℕ+) {u v : beadEvent (l ++ p :: q :: r)}
    (h : (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) u).1
      = (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) v).1) :
    (u.1 : ℕ) = (v.1 : ℕ) ∨ (l.length ≤ (u.1 : ℕ) ∧ (u.1 : ℕ) ≤ l.length + 1
      ∧ l.length ≤ (v.1 : ℕ) ∧ (v.1 : ℕ) ≤ l.length + 1) := by
  have hu := mergeBead_cases l r p q u
  have hv := mergeBead_cases l r p q v
  have hval := congrArg Fin.val h
  omega

/-! ### A codimension-one refinement that does not braid is a merge -/

/-- **The middle map is forced.**  A wedge map is its coordinate bijection, and only `cubeMerge`'s
preserves the flattening. -/
theorem merge_of_pos_of_codim_one {K : BPSet} {a b : Ch K} {f : a ⟶ b} (hcod : codim f = 1)
    (hp : ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ)) : merge K f := by
  obtain ⟨l, r, p, q, hb, ha⟩ := (codim_eq_one_iff f).mp hcod
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  subst ha
  subst hb
  have hds : dimSum (l ++ p :: q :: r) = dimSum (l ++ (p + q) :: r) :=
    serialWedge_dimSum_eq (Hom.φ f)
  have hm : ∀ x : beadEvent (l ++ p :: q :: r),
      (pos (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) x) : ℕ) = (pos x : ℕ) :=
    pos_coordMap_splicePhi_cubeMerge l r p q
  have hfφ : Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) :=
    wedgeHom_ext ((eq_flatEquiv hds hp).trans (eq_flatEquiv hds hm).symm)
  have hw : splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) ≫ bm = am := by
    rw [← hfφ]; exact f.w
  rw [show f = ⟨splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)), hw⟩ from hom_ext' hfφ]
  exact ⟨spliceCutAt hw, rfl⟩

/-! ### Peeling one merge -/

/-- **Peeling.**  A refinement that does not braid and loses a bead factors as a bead merge
followed by a refinement losing one bead fewer: the junction to merge is one the target does not
separate, and the second factor is the coarsening that leaves. -/
theorem exists_merge_factor {K : BPSet} {a b : Ch K} (f : a ⟶ b) (hf : W K f)
    (hlt : b.dims.length < a.dims.length) :
    ∃ (c : Ch K) (g : a ⟶ c) (h : c ⟶ b), merge K g ∧ f = g ≫ h ∧
      c.dims.length + 1 = a.dims.length ∧ W K h := by
  have hp := (W_iff_pos f).mp hf
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  obtain ⟨i, hi, hchoice⟩ := exists_adjacent_eq (blockIdx (Hom.φ f).hom)
    (serialWedge_blockIdx_monotone _ (Hom.φ f).app_init) hlt
  obtain ⟨l, r, p, q, hd, hlen⟩ := exists_split_at ad hi
  subst hlen
  subst hd
  have h₁ : dimSum (l ++ p :: q :: r) = dimSum (l ++ (p + q) :: r) := by
    simp only [dimSum, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      PNat.add_coe]
    omega
  have h₂ : dimSum (l ++ p :: q :: r) = dimSum bd := serialWedge_dimSum_eq (Hom.φ f)
  have hm : ∀ x : beadEvent (l ++ p :: q :: r),
      (pos (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) x) : ℕ) = (pos x : ℕ) :=
    pos_coordMap_splicePhi_cubeMerge l r p q
  have hf1 : coordMapEquiv (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) = flatEquiv h₁ :=
    eq_flatEquiv h₁ hm
  have hf2 : coordMapEquiv (Hom.φ f) = flatEquiv h₂ := eq_flatEquiv h₂ hp
  -- Both beads of the merged pair sit over the same bead of the target, by the choice of `i`.
  have hbead : ∀ z : beadEvent (l ++ p :: q :: r), l.length ≤ (z.1 : ℕ) →
      (z.1 : ℕ) ≤ l.length + 1 →
      blockIdx (Hom.φ f).hom z.1 = blockIdx (Hom.φ f).hom ⟨l.length, Nat.lt_of_succ_lt hi⟩ := by
    intro z hz1 hz2
    rcases Nat.eq_or_lt_of_le hz1 with he | he
    · exact congrArg _ (Fin.ext he.symm)
    · rw [show z.1 = (⟨l.length + 1, hi⟩ : Fin (l ++ p :: q :: r).length) from
        Fin.ext (show (z.1 : ℕ) = l.length + 1 by omega)]
      exact hchoice.symm
  have hco : Coarser (l ++ (p + q) :: r) bd := by
    refine coarser_descend (h₁ := h₁) (h₂ := h₂) fun u v hu => ?_
    rw [← hf1] at hu
    rw [← hf2]
    rcases mergeBead_pair l r p q hu with heq | ⟨hu1, hu2, hv1, hv2⟩
    · exact (isShuffle_coordMapEquiv (Hom.φ f)).bead_eq (Fin.ext heq)
    · change (coordMap (Hom.φ f) u).1 = (coordMap (Hom.φ f) v).1
      rw [coordMap_fst, coordMap_fst, hbead u hu1 hu2, hbead v hv1 hv2]
  obtain ⟨ψ, hψ⟩ := coarser_iff_exists_pos.mp hco
  have hcomp : splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) ≫ ψ = Hom.φ f := by
    refine wedgeHom_ext ?_
    rw [hf2]
    refine eq_flatEquiv h₂ fun x => ?_
    change (pos (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) ≫ ψ) x) : ℕ) = _
    rw [coordMap_comp, Function.comp_apply, hψ]
    exact hm x
  have hw : splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) ≫ (ψ ≫ bm) = am := by
    rw [← Category.assoc, hcomp]; exact f.w
  exact ⟨⟨l ++ (p + q) :: r, ψ ≫ bm⟩, ⟨_, hw⟩, ⟨ψ, rfl⟩, ⟨spliceCutAt hw, rfl⟩,
    hom_ext' hcomp.symm, by simp only [List.length_append, List.length_cons]; omega,
    (W_iff_pos _).mpr hψ⟩

/-! ### The merges generate -/

/-- **The bead merges generate `W`.**  Peeling merges off strictly shortens the dimension list,
so the induction terminates at an endomorphism, which is the identity. -/
theorem multiplicativeClosure_merge (K : BPSet) : (merge K).multiplicativeClosure = W K := by
  refine _root_.le_antisymm
    (by rw [MorphismProperty.multiplicativeClosure_le_iff]; exact merge_le_W K) ?_
  suffices key : ∀ (k : ℕ) {x y : Ch K} (g : x ⟶ y), x.dims.length ≤ y.dims.length + k →
      W K g → (merge K).multiplicativeClosure g by
    exact fun a b f hf => key a.dims.length f (Nat.le_add_left _ _) hf
  intro k
  induction k with
  | zero =>
      intro x y g hlen _
      obtain rfl : x = y :=
        eq_of_hom_of_dims_length_eq g (Nat.le_antisymm (by omega) (dims_length_le_of_hom g))
      rw [endo_eq_id g]
      exact .id x
  | succ k ih =>
      intro x y g hlen hg
      rcases Nat.lt_or_ge y.dims.length x.dims.length with hlt | hge
      · obtain ⟨c, u, v, hu, huv, hc, hv⟩ := exists_merge_factor g hg hlt
        rw [huv]
        exact (merge K).multiplicativeClosure.comp_mem u v (.of u hu) (ih v (by omega) hv)
      · obtain rfl : x = y :=
          eq_of_hom_of_dims_length_eq g (Nat.le_antisymm hge (dims_length_le_of_hom g))
        rw [endo_eq_id g]
        exact .id x

/-- **The generators are the codimension-one members of the class they generate.** -/
theorem merge_iff {K : BPSet} {a b : Ch K} (f : a ⟶ b) : merge K f ↔ W K f ∧ codim f = 1 :=
  ⟨fun h => ⟨merge_le_W K f h, codim_eq_one_of_merge K h⟩,
    fun ⟨hW, hc⟩ => merge_of_pos_of_codim_one hc ((W_iff_pos f).mp hW)⟩

/-- **A codimension-one refinement is a merge exactly when it does not braid** — the general form
of `merge_cutRefine_iff`. -/
theorem merge_iff_of_codim_one {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    {f : a ⟶ b} (hcod : codim f = 1) : merge K f ↔ crossPerm h f = 1 :=
  ⟨crossPerm_eq_one_of_merge h,
    fun h => merge_of_pos_of_codim_one hcod (pos_coordMap_of_crossPerm_eq_one h)⟩

end ChainCat
