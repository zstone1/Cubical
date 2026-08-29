import CubeChains.Chains.MergeBraid
import CubeChains.Chains.ShuffleHom

/-!
# Chains/MergeGenerate — the merges are exactly the refinements that do not braid

A dimension list is **coarsened** by summing consecutive beads, and a coarsening is realised by
exactly one wedge map — the one preserving the flattening `pos` (`ShuffleHom`).  So a refinement
that moves no event and loses a bead factors through the canonical merge at any junction its
target does not separate, and induction on the bead count exhausts it.  At codimension one the
middle map is forced to be `cubeMerge`.  Together: `Winf K` is the class of refinements whose
coordinate map preserves `pos`.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace CubeChains

variable {d d' d'' : List ℕ+}

/-! ### The flattening-preserving bijection of events -/

theorem sumGet_eq_of_dimSum_eq (h : dimSum d = dimSum d') :
    (∑ i : Fin d.length, (d.get i : ℕ)) = ∑ i : Fin d'.length, (d'.get i : ℕ) := by
  rw [dimSum_eq_sum_get, dimSum_eq_sum_get, h]

/-- The bijection of events that preserves the flattening — what a non-braiding refinement does
on coordinates. -/
def flatEquiv (h : dimSum d = dimSum d') : beadEvent d ≃ beadEvent d' :=
  pos.trans ((finCongr (sumGet_eq_of_dimSum_eq h)).trans pos.symm)

@[simp] theorem pos_flatEquiv (h : dimSum d = dimSum d') (x : beadEvent d) :
    (pos (flatEquiv h x) : ℕ) = (pos x : ℕ) := by
  simp [flatEquiv]

/-- **Uniqueness**: there is only one flattening-preserving bijection. -/
theorem eq_flatEquiv {e : beadEvent d ≃ beadEvent d'} (h : dimSum d = dimSum d')
    (he : ∀ x, (pos (e x) : ℕ) = (pos x : ℕ)) : e = flatEquiv h :=
  Equiv.ext fun x => pos.injective (Fin.ext ((he x).trans (pos_flatEquiv h x).symm))

theorem pos_flatEquiv_symm (h : dimSum d = dimSum d') (y : beadEvent d') :
    (pos ((flatEquiv h).symm y) : ℕ) = (pos y : ℕ) := by
  conv_rhs => rw [← Equiv.apply_symm_apply (flatEquiv h) y]
  rw [pos_flatEquiv]

/-! ### Coarsening -/

/-- `d'` **coarsens** `d`: the same events, each bead of `d` inside a single bead of `d'`. -/
def Coarser (d d' : List ℕ+) : Prop :=
  ∃ h : dimSum d = dimSum d',
    ∀ x y : beadEvent d, x.1 = y.1 → (flatEquiv h x).1 = (flatEquiv h y).1

/-- The inner clause of `IsShuffle` is free for a flattening-preserving bijection, so only the
bead clause — coarsening — remains. -/
theorem isShuffle_flatEquiv (h : dimSum d = dimSum d')
    (hb : ∀ x y : beadEvent d, x.1 = y.1 → (flatEquiv h x).1 = (flatEquiv h y).1) :
    IsShuffle (flatEquiv h) where
  bead x y hxy := by
    rcases hxy.lt_or_eq with hlt | heq
    · refine Fin.le_def.mpr (fst_le_of_pos_lt ?_)
      rw [Fin.lt_def, pos_flatEquiv, pos_flatEquiv]
      exact Fin.lt_def.mp (pos_lt_of_fst_lt (Fin.lt_def.mp hlt))
    · exact le_of_eq (hb x y heq)
  inner x y _ hlt := by
    rw [Fin.lt_def, pos_flatEquiv, pos_flatEquiv]
    exact Fin.lt_def.mp hlt

/-- **A coarsening is exactly a wedge map that preserves the flattening.**  Realised by
`exists_coordMapEquiv_eq`, detected by `IsShuffle`'s bead clause. -/
theorem coarser_iff_exists_pos :
    Coarser d d' ↔ ∃ φ : ⋁d ⟶ ⋁d', ∀ x, (pos (coordMap φ x) : ℕ) = (pos x : ℕ) := by
  constructor
  · rintro ⟨h, hb⟩
    obtain ⟨φ, hφ⟩ := exists_coordMapEquiv_eq (isShuffle_flatEquiv h hb)
    exact ⟨φ, fun x => by
      rw [show coordMap φ x = flatEquiv h x from Equiv.ext_iff.mp hφ x, pos_flatEquiv]⟩
  · rintro ⟨φ, hp⟩
    refine ⟨serialWedge_dimSum_eq φ, fun x y hxy => ?_⟩
    rw [← eq_flatEquiv (e := coordMapEquiv φ) (serialWedge_dimSum_eq φ) hp]
    exact (isShuffle_coordMapEquiv φ).bead_eq hxy

/-- **Coarsenings descend.**  If the beads of `d'` are unions of beads of `d` that `d''` already
fails to separate, then `d''` coarsens `d'`. -/
theorem coarser_descend {h₁ : dimSum d = dimSum d'} {h₂ : dimSum d = dimSum d''}
    (href : ∀ u v : beadEvent d,
      (flatEquiv h₁ u).1 = (flatEquiv h₁ v).1 → (flatEquiv h₂ u).1 = (flatEquiv h₂ v).1) :
    Coarser d' d'' := by
  refine ⟨h₁.symm.trans h₂, fun x y hxy => ?_⟩
  have key : ∀ z : beadEvent d',
      flatEquiv (h₁.symm.trans h₂) z = flatEquiv h₂ ((flatEquiv h₁).symm z) := fun z =>
    pos.injective (Fin.ext (by rw [pos_flatEquiv, pos_flatEquiv, pos_flatEquiv_symm]))
  rw [key, key]
  exact href _ _ (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hxy)

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
theorem exists_merge_factor {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hp : ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ))
    (hlt : b.dims.length < a.dims.length) :
    ∃ (c : Ch K) (g : a ⟶ c) (h : c ⟶ b), merge K g ∧ f = g ≫ h ∧
      c.dims.length + 1 = a.dims.length ∧
      ∀ e, (pos (coordMap (Hom.φ h) e) : ℕ) = (pos e : ℕ) := by
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
    hom_ext' hcomp.symm, by simp only [List.length_append, List.length_cons]; omega, hψ⟩

/-! ### `Winf` is the non-braiding morphism property -/

/-- **The converse of `crossPerm_eq_one_of_Winf`**: a refinement whose coordinate map preserves
the flattening is a composite of bead merges. -/
theorem Winf_of_pos {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hp : ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ)) : Winf K f := by
  suffices key : ∀ (k : ℕ) {x y : Ch K} (g : x ⟶ y), x.dims.length ≤ y.dims.length + k →
      (∀ e, (pos (coordMap (Hom.φ g) e) : ℕ) = (pos e : ℕ)) → Winf K g by
    exact key a.dims.length f (Nat.le_add_left _ _) hp
  intro k
  induction k with
  | zero =>
      intro x y g hlen _
      obtain rfl : x = y :=
        eq_of_hom_of_dims_length_eq g (Nat.le_antisymm (by omega) (dims_length_le_of_hom g))
      rw [endo_eq_id g]
      exact (Winf K).id_mem x
  | succ k ih =>
      intro x y g hlen hg
      rcases Nat.lt_or_ge y.dims.length x.dims.length with hlt | hge
      · obtain ⟨c, u, v, hu, huv, hc, hv⟩ := exists_merge_factor g hg hlt
        rw [huv]
        exact (Winf K).comp_mem _ _ (merge_le_Winf K _ hu) (ih v (by omega) hv)
      · obtain rfl : x = y :=
          eq_of_hom_of_dims_length_eq g (Nat.le_antisymm hge (dims_length_le_of_hom g))
        rw [endo_eq_id g]
        exact (Winf K).id_mem x

theorem Winf_iff_pos {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    Winf K f ↔ ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) :=
  ⟨fun h => pos_coordMap_of_Winf h, Winf_of_pos f⟩

/-- The **non-braiding** refinements: those whose coordinate map preserves the flattening. -/
def NonBraiding (K : BPSet) : MorphismProperty (Ch K) :=
  fun _ _ f => ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ)

/-- **The class generated by the bead merges is exactly the refinements that do not braid.** -/
theorem Winf_eq_nonBraiding (K : BPSet) : Winf K = NonBraiding K := by
  ext a b f
  exact Winf_iff_pos f

theorem pos_coordMap_of_crossPerm_eq_one {K : BPSet} {a b : Ch K} {f : a ⟶ b}
    (h : crossPerm f = 1) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  have hs := crossPerm_strand f e
  rw [h, Equiv.Perm.one_apply, strand_val, strand_val] at hs
  exact hs.symm

/-- **The same, as the vanishing of the crossing permutation.** -/
theorem Winf_iff_crossPerm_eq_one {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    Winf K f ↔ crossPerm f = 1 :=
  ⟨crossPerm_eq_one_of_Winf, fun h => (Winf_iff_pos f).mpr (pos_coordMap_of_crossPerm_eq_one h)⟩

/-- **The generators are the codimension-one members of the class they generate.** -/
theorem merge_iff {K : BPSet} {a b : Ch K} (f : a ⟶ b) : merge K f ↔ Winf K f ∧ codim f = 1 :=
  ⟨fun h => ⟨merge_le_Winf K f h, codim_eq_one_of_merge K h⟩,
    fun ⟨hW, hc⟩ => merge_of_pos_of_codim_one hc ((Winf_iff_pos f).mp hW)⟩

/-- **A codimension-one refinement is a merge exactly when it does not braid** — the general form
of `merge_cutRefine_iff`. -/
theorem merge_iff_of_codim_one {K : BPSet} {a b : Ch K} {f : a ⟶ b} (hcod : codim f = 1) :
    merge K f ↔ crossPerm f = 1 :=
  ⟨crossPerm_eq_one_of_merge,
    fun h => merge_of_pos_of_codim_one hcod (pos_coordMap_of_crossPerm_eq_one h)⟩

end ChainCat
