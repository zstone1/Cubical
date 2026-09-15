import CubeChains.Concurrency.Merge.MergeClass
import CubeChains.Concurrency.Grading.CoordFunctor

/-!
# Concurrency/Merge/TotalMerge — the splice, and merging all the way down

`Ch Zbp` is the serial wedges (`Zbp` is terminal), and `spliceHom l r p q w` is a staircase `w`
spliced between two fixed stretches of beads.  The append isomorphism peels one head cube at a
time, so a splice at `c :: l` is the splice at `l` behind `□c` (`splicePhi_cons`) and at `[]` the
bare staircase `spliceNil`: on events a splice fixes everything in front of its cut and moves the
rest as its staircase does (`pos_coordMap_splicePhi`).
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain

namespace ChainCat

/-! ### `Ch Zbp` objects are dimension lists -/

/-- The chain of `Zbp` on a dimension list — the classifying map is forced. -/
def zObj (d : List ℕ+) : Ch Zbp := ⟨d, isTerminalZbp.from (⋁d)⟩

@[simp] theorem zObj_dims (d : List ℕ+) : (zObj d).dims = d := rfl

/-- A wedge map is a morphism of `Ch Zbp` on the nose: the triangle over `Zbp` is automatic. -/
def zHom {d e : List ℕ+} (φ : ⋁d ⟶ ⋁e) : zObj d ⟶ zObj e :=
  ⟨φ, Subsingleton.elim _ _⟩

@[simp] theorem zHom_φ {d e : List ℕ+} (φ : ⋁d ⟶ ⋁e) : Hom.φ (zHom φ) = φ := rfl

/-! ### Splicing a staircase between two stretches of beads -/

/-- `𝟙 ∨ w ∨ 𝟙` as a wedge map, for a prescribed middle `w`. -/
def splicePhi (l r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    ⋁(l ++ p :: q :: r) ⟶ ⋁(l ++ (p + q) :: r) :=
  (cutSrcIso l r p q).inv ≫ (𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r)))
    ≫ (serialWedgeAppend l ((p + q) :: r)).hom

/-- The refinement `𝟙 ∨ w ∨ 𝟙` of `Ch Zbp`. -/
def spliceHom (l r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    zObj (l ++ p :: q :: r) ⟶ zObj (l ++ (p + q) :: r) :=
  zHom (splicePhi l r p q w)

/-- **A splice is a cut**, with `w` back as the middle map — for a refinement of an arbitrary
`K`. -/
def spliceCutAt {K : BPSet} {l r : List ℕ+} {p q : ℕ+}
    {w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)}
    {am : ⋁(l ++ p :: q :: r) ⟶ K} {cm : ⋁(l ++ (p + q) :: r) ⟶ K}
    (hw : splicePhi l r p q w ≫ cm = am) :
    CutData (⟨splicePhi l r p q w, hw⟩ :
      (⟨l ++ p :: q :: r, am⟩ : Ch K) ⟶ ⟨l ++ (p + q) :: r, cm⟩) where
  l := l
  r := r
  p := p
  q := q
  w := w
  e₁ := (cutSrcIso l r p q).symm
  e₂ := (serialWedgeAppend l ((p + q) :: r)).symm
  sq := (Iso.comp_inv_eq (serialWedgeAppend l ((p + q) :: r)).symm).mp rfl

/-- The cut of a splice of `Ch Zbp`. -/
def spliceCut (l r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    CutData (spliceHom l r p q w) :=
  spliceCutAt (Subsingleton.elim _ _)

/-- **A cut is the splice of its own middle map** — the two identifications have nowhere to go
(`serialWedge_iso_unique`), so the square `sq` says exactly that. -/
theorem eq_splicePhi_of_sq {l r : List ℕ+} {p q : ℕ+}
    {w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)}
    {φ : ⋁(l ++ p :: q :: r) ⟶ ⋁(l ++ (p + q) :: r)}
    {e₁ : ⋁(l ++ p :: q :: r) ≅ ⋁l ∨ ((□(p : ℕ) ∨ □(q : ℕ)) ∨ ⋁r)}
    {e₂ : ⋁(l ++ (p + q) :: r) ≅ ⋁l ∨ (□((p + q : ℕ+) : ℕ) ∨ ⋁r)}
    (sq : e₁.hom ≫ (𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r))) = φ ≫ e₂.hom) :
    φ = splicePhi l r p q w := by
  obtain rfl : e₁ = (cutSrcIso l r p q).symm := serialWedge_iso_unique _ _
  obtain rfl : e₂ = (serialWedgeAppend l ((p + q) :: r)).symm := serialWedge_iso_unique _ _
  simp only [Iso.symm_hom] at sq
  calc φ = (φ ≫ (serialWedgeAppend l ((p + q) :: r)).inv)
            ≫ (serialWedgeAppend l ((p + q) :: r)).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = ((cutSrcIso l r p q).inv ≫ (𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r))))
            ≫ (serialWedgeAppend l ((p + q) :: r)).hom :=
        congrArg (fun z => z ≫ (serialWedgeAppend l ((p + q) :: r)).hom) sq.symm
    _ = splicePhi l r p q w := Category.assoc _ _ _

/-! ### The two staircases, spliced

`cubeMerge` and `cubeReorder` are the two wedge-to-tensor comparisons of a pair of cubes, and there
are two because `⊗ᵍ` has no swap.  Spliced at a cut they give the two families of codimension-one
refinements: the merge, which keeps the coordinate blocks in bead order, and — at a cut of two
edges, where the two targets agree — the atom, which exchanges them. -/

/-- **The bead merge**: the comparison `cubeMerge`, spliced between the beads `l` and `r`. -/
def mergeHom (l r : List ℕ+) (p q : ℕ+) :
    zObj (l ++ p :: q :: r) ⟶ zObj (l ++ (p + q) :: r) :=
  spliceHom l r p q (cubeMerge (p : ℕ) (q : ℕ))

/-- **The atom** `σ`: the flipped comparison `cubeReorder`, spliced at a cut of two edges. -/
def atomHom (l r : List ℕ+) :
    zObj (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) ⟶ zObj (l ++ (2 : ℕ+) :: r) :=
  spliceHom l r 1 1 (cubeReorder 1 1)

theorem merge_mergeHom (l r : List ℕ+) (p q : ℕ+) : merge Zbp (mergeHom l r p q) :=
  ⟨spliceCut l r p q _, rfl⟩

theorem W_mergeHom (l r : List ℕ+) (p q : ℕ+) : W Zbp (mergeHom l r p q) :=
  merge_le_W Zbp _ (merge_mergeHom l r p q)

/-- **Every coarsening is a composite of bead merges** — erase the dropped boundaries one at a
time, each erasure merging the two beads it separated. -/
theorem exists_W_of_coarser : ∀ (n : ℕ) {a b : Ch Zbp},
    (boundaries a.dims \ boundaries b.dims).card = n → dimSum a.dims = dimSum b.dims →
      boundaries b.dims ⊆ boundaries a.dims → ∃ u : a ⟶ b, W Zbp u
  | 0, a, b, hn, _, hsub => by
      obtain rfl : a = b := Obj.eq_of_dims (boundaries_injective (Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hn)) hsub))
      exact ⟨𝟙 a, (W Zbp).id_mem a⟩
  | n + 1, a, b, hn, hd, hsub => by
      obtain ⟨t, ht⟩ := Finset.card_pos.mp (show 0 < (boundaries a.dims \ boundaries b.dims).card
        by omega)
      have hmem := Finset.mem_sdiff.mp ht
      obtain ⟨l, r, p, q, ha, hl⟩ := exists_cut_of_mem_boundaries a.dims hmem.1
        (fun h => hmem.2 (h ▸ zero_mem_boundaries _))
        (fun h => hmem.2 (by rw [h, hd]; exact dimSum_mem_boundaries _))
      obtain ⟨v, hv⟩ := exists_W_of_coarser n (a := zObj (l ++ (p + q) :: r)) (b := b)
        (by rw [zObj_dims, hl, Finset.erase_sdiff_comm, Finset.card_erase_of_mem ht, hn]; rfl)
        (by rw [zObj_dims, ← dimSum_cut, ← ha, hd])
        (by rw [zObj_dims, hl]; exact Finset.subset_erase.mpr ⟨hsub, hmem.2⟩)
      exact ⟨eqToHom (Obj.eq_of_dims ha) ≫ mergeHom l r p q ≫ v,
        (W Zbp).comp_mem _ _ (W_eqToHom _) ((W Zbp).comp_mem _ _ (W_mergeHom l r p q) hv)⟩

/-! ### A splice peels one head cube at a time -/

/-- **The bare splice** `⋁(p :: q :: r) ⟶ ⋁((p + q) :: r)`: `w` on the first two beads, the rest
untouched. -/
def spliceNil (r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    ⋁(p :: q :: r) ⟶ ⋁((p + q) :: r) :=
  (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)).inv ≫ (w ⊗ₘ 𝟙 (⋁r))

theorem splicePhi_eq_conj (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    splicePhi l r p q w
      = (serialWedgeAppend l (p :: q :: r)).inv ≫ (⋁l ◁ spliceNil r p q w)
          ≫ (serialWedgeAppend l ((p + q) :: r)).hom := by
  simp only [splicePhi, cutSrcIso, spliceNil, Iso.trans_inv, whiskerLeftIso_inv, id_tensorHom,
    whiskerLeft_comp, Category.assoc]
  rfl

/-- At the empty prefix a splice is the bare staircase — the left unitor, natural. -/
theorem splicePhi_nil (r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    splicePhi [] r p q w = spliceNil r p q w := by
  rw [splicePhi_eq_conj]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (leftUnitor_inv_naturality (spliceNil r p q w)).symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (λ_ _).inv_hom_id).trans
      (Category.comp_id _))))

/-- **A splice behind a head cube** is the splice behind the rest, whiskered — the append
isomorphism is the associator followed by the whiskered append. -/
theorem splicePhi_cons (c : ℕ+) (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    splicePhi (c :: l) r p q w = (□(c : ℕ)) ◁ splicePhi l r p q w := by
  rw [splicePhi_eq_conj, splicePhi_eq_conj]
  simp only [serialWedgeAppend, Iso.trans_inv, Iso.trans_hom, whiskerLeftIso_inv,
    whiskerLeftIso_hom, Category.assoc, whiskerLeft_comp]
  congr 1
  exact (associator_inv_naturality_right_assoc (□(c : ℕ)) (⋁l) (spliceNil r p q w) _).symm.trans
    (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))

/-! ### Coordinates of a splice

The bare splice sends its two beads through the staircase's two restrictions and shifts the tail
past the merged bead; behind each head cube the events shift once more. -/

/-- A cube-to-cube map is the Yoneda image of its own cell (cube Yoneda). -/
theorem yoneda_map_yonedaEquiv {m m' : ℕ} (f : (□m).toPsh ⟶ (□m').toPsh) :
    yoneda.map (yonedaEquiv f) = f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

variable (r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ))

/-- The staircase's first bead goes through its left restriction. -/
theorem pos_coordMap_spliceNil_zero (k : Fin (((p :: q :: r).get 0 : ℕ))) :
    (pos (coordMap (spliceNil r p q w) ⟨0, k⟩) : ℕ)
      = (faceEmb (yonedaEquiv (wedgeInl (□(p : ℕ)) (□(q : ℕ)) ≫ w.hom)) k : ℕ) := by
  have hfac : ιᵂ (p :: q :: r) 0 ≫ (spliceNil r p q w).hom
      = yoneda.map (yonedaEquiv (wedgeInl (□(p : ℕ)) (□(q : ℕ)) ≫ w.hom))
        ≫ ιᵂ ((p + q) :: r) 0 := by
    change wedgeInl (□(p : ℕ)) (□(q : ℕ) ∨ ⋁r) ≫ wedge2AssocBwd _ _ _
        ≫ wedge2MapPsh w (𝟙 (⋁r)) = _
    rw [wedge2AssocBwd_inl_assoc, wedge2MapPsh_inl, yoneda_map_yonedaEquiv]
    exact (Category.assoc _ _ _).symm
  rw [coordMap_of_factor _ 0 0 _ hfac k, pos_cons_zero]
  rfl

/-- The staircase's second bead goes through its right restriction. -/
theorem pos_coordMap_spliceNil_one (k : Fin (((p :: q :: r).get 1 : ℕ))) :
    (pos (coordMap (spliceNil r p q w) ⟨1, k⟩) : ℕ)
      = (faceEmb (yonedaEquiv (wedgeInr (□(p : ℕ)) (□(q : ℕ)) ≫ w.hom)) k : ℕ) := by
  have hfac : ιᵂ (p :: q :: r) 1 ≫ (spliceNil r p q w).hom
      = yoneda.map (yonedaEquiv (wedgeInr (□(p : ℕ)) (□(q : ℕ)) ≫ w.hom))
        ≫ ιᵂ ((p + q) :: r) 0 := by
    change (wedgeInl (□(q : ℕ)) (⋁r) ≫ wedgeInr (□(p : ℕ)) (□(q : ℕ) ∨ ⋁r))
        ≫ wedge2AssocBwd _ _ _ ≫ wedge2MapPsh w (𝟙 (⋁r)) = _
    rw [Category.assoc, wedge2AssocBwd_inl_inr_assoc, wedge2MapPsh_inl, yoneda_map_yonedaEquiv]
    exact (Category.assoc _ _ _).symm
  rw [coordMap_of_factor _ 1 0 _ hfac k, pos_cons_zero]
  rfl

/-- The beads after the staircase keep their place, past the merged bead. -/
theorem pos_coordMap_spliceNil_tail (j : Fin r.length)
    (k : Fin (((p :: q :: r).get j.succ.succ : ℕ))) :
    (pos (coordMap (spliceNil r p q w) ⟨j.succ.succ, k⟩) : ℕ)
      = ((p + q : ℕ+) : ℕ) + (pos (⟨j, k⟩ : beadEvent r) : ℕ) := by
  have hfac : ιᵂ (p :: q :: r) j.succ.succ ≫ (spliceNil r p q w).hom
      = yoneda.map (𝟙 _) ≫ ιᵂ ((p + q) :: r) j.succ := by
    change ((ιᵂ r j ≫ wedgeInr (□(q : ℕ)) (⋁r)) ≫ wedgeInr (□(p : ℕ)) (□(q : ℕ) ∨ ⋁r))
        ≫ wedge2AssocBwd _ _ _ ≫ wedge2MapPsh w (𝟙 (⋁r)) = _
    rw [Category.assoc, Category.assoc, wedge2AssocBwd_inr_inr_assoc, wedge2MapPsh_inr,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [coordMap_of_factor (a := p :: q :: r) (b := (p + q) :: r) _ j.succ.succ j.succ _ hfac k,
    pos_cons_succ]
  exact congrArg (((p + q : ℕ+) : ℕ) + ·) (congrArg (fun x => (pos (⟨j, x⟩ : beadEvent r) : ℕ))
    (faceEmb_id _ k))

omit w in
/-- **An event of `p :: q :: r` is in the first bead, the second, or the tail.** -/
theorem spliceEventCases {P : beadEvent (p :: q :: r) → Prop}
    (h0 : ∀ k, P ⟨0, k⟩) (h1 : ∀ k, P ⟨1, k⟩) (ht : ∀ j k, P ⟨Fin.succ (Fin.succ j), k⟩)
    (e : beadEvent (p :: q :: r)) : P e := by
  obtain ⟨i, k⟩ := e
  induction i using Fin.cases with
  | zero => exact h0 k
  | succ i =>
      induction i using Fin.cases with
      | zero => exact h1 k
      | succ j => exact ht j k

/-- **A splice fixes the events in front of its cut and moves the rest as its staircase does**,
shifted past them — one head cube at a time (`splicePhi_cons`). -/
theorem pos_coordMap_splicePhi (σ : ℕ → ℕ)
    (hw : ∀ e, (pos (coordMap (spliceNil r p q w) e) : ℕ) = σ (pos e)) :
    ∀ (l : List ℕ+) (e : beadEvent (l ++ p :: q :: r)),
      (pos (coordMap (splicePhi l r p q w) e) : ℕ)
        = if (pos e : ℕ) < dimSum l then (pos e : ℕ) else dimSum l + σ ((pos e : ℕ) - dimSum l)
  | [], e => by
      rw [splicePhi_nil]
      exact (hw e).trans (by simp only [dimSum, List.map_nil, List.sum_nil, Nat.not_lt_zero,
        if_false, zero_add, Nat.sub_zero]; rfl)
  | c :: l, e => by
      rw [splicePhi_cons]
      revert e
      change ∀ e : beadEvent (c :: (l ++ p :: q :: r)),
        (pos (coordMap (a := c :: (l ++ p :: q :: r)) (b := c :: (l ++ (p + q) :: r))
          ((□(c : ℕ)) ◁ splicePhi l r p q w) e) : ℕ)
          = if (pos e : ℕ) < (c : ℕ) + dimSum l then (pos e : ℕ)
            else ((c : ℕ) + dimSum l) + σ ((pos e : ℕ) - ((c : ℕ) + dimSum l))
      rintro ⟨i, k⟩
      induction i using Fin.cases with
      | zero =>
          have hk : (k : ℕ) < c := k.isLt
          rw [pos_coordMap_whiskerLeft_zero, pos_cons_zero, if_pos (by omega)]
      | succ j =>
          rw [pos_coordMap_whiskerLeft_succ, pos_cons_succ, pos_coordMap_splicePhi σ hw l ⟨j, k⟩,
            Nat.add_sub_add_left]
          split_ifs <;> omega

end ChainCat
