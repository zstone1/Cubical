import CubeChains.Concurrency.Merge.MergeClass
import CubeChains.Concurrency.Grading.CoordFunctor

/-!
# Concurrency/Merge/TotalMerge — the splice, and merging all the way down

`Ch Zbp` is the serial wedges (`Zbp` is terminal), and `spliceHom l r p q w` is a staircase `w`
spliced between two fixed stretches of beads.  `l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, so a
splice is the tensorator of `⋁` applied twice: its coordinate map is the identity on the two blocks
flanking the cut and the staircase's own on the block it merges (`spliceEventCases`).
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

/-- **A splice is a cut**, with `w` back as the middle map — the generalisation of `cutOfMiddle`
to a splice, and to a refinement of an arbitrary `K`. -/
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

/-! ### The splice as a double concatenation

`l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, and `splicePhi` is the tensorator of `⋁` applied
twice: identities on `l` and on `r`, the staircase `w` in the middle. -/

/-- **The bare splice** `⋁(p :: q :: r) ⟶ ⋁((p + q) :: r)`: `w` on the first two beads, the rest
untouched.  Spelled with `⋁` on both ends, so `coordMap` sees it. -/
def spliceNil (r : List ℕ+) (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    ⋁(p :: q :: r) ⟶ ⋁((p + q) :: r) :=
  (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)).inv ≫ (w ⊗ₘ 𝟙 (⋁r))

/-- **The staircase as a serial-wedge map** `⋁[p, q] ⟶ ⋁[p + q]` — `w` with the unit tails put
back. -/
def pairMerge (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) : ⋁[p, q] ⟶ ⋁[p + q] :=
  (pairIso p q).hom ≫ w ≫ (serialWedge1 (p + q)).inv

theorem splicePhi_eq_conj (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    splicePhi l r p q w
      = (serialWedgeAppend l (p :: q :: r)).inv ≫ (⋁l ◁ spliceNil r p q w)
          ≫ (serialWedgeAppend l ((p + q) :: r)).hom := by
  simp only [splicePhi, cutSrcIso, spliceNil, Iso.trans_inv, whiskerLeftIso_inv, id_tensorHom,
    whiskerLeft_comp, Category.assoc]
  rfl

/-- **Outer split**: the beads of `l` are untouched, the rest is the bare splice. -/
theorem splicePhi_eq_concat (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    splicePhi l r p q w = concatHomφ (𝟙 (zObj l)) (zHom (spliceNil r p q w)) := by
  rw [splicePhi_eq_conj]
  change _ = (serialWedgeAppend l (p :: q :: r)).inv ≫ (𝟙 (⋁l) ⊗ₘ spliceNil r p q w)
      ≫ (serialWedgeAppend l ((p + q) :: r)).hom
  rw [id_tensorHom]

/-- **Inner split**: the beads of `r` are untouched, the rest is the staircase. -/
theorem spliceNil_eq_concat (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    spliceNil r p q w = concatHomφ (zHom (pairMerge p q w)) (𝟙 (zObj r)) := by
  have hw : w = (pairIso p q).inv ≫ pairMerge p q w ≫ (serialWedge1 (p + q)).hom := by
    rw [pairMerge]; simp
  have h1 : serialWedgeAppend [p, q] r
      = (pairIso p q ⊗ᵢ Iso.refl (⋁r)) ≪≫ α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r) :=
    Iso.ext (by simpa using serialWedgeAppend_pair p q r)
  have h2 : serialWedgeAppend [p + q] r = serialWedge1 (p + q) ⊗ᵢ Iso.refl (⋁r) :=
    Iso.ext (by simpa using serialWedgeAppend_singleton (p + q) r)
  change (α_ _ _ _).inv ≫ (w ⊗ₘ 𝟙 (⋁r))
      = (serialWedgeAppend [p, q] r).inv ≫ (pairMerge p q w ⊗ₘ 𝟙 (⋁r))
          ≫ (serialWedgeAppend [p + q] r).hom
  rw [h1, h2]
  conv_lhs => rw [hw]
  simp only [tensorHom_id, comp_whiskerRight, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    tensorIso_hom, Iso.refl_hom]
  exact (Category.assoc _ _ _).symm

/-- The splice as a refinement of `Ch Zbp`: the untouched prefix, concatenated with the rest. -/
theorem zHom_splicePhi_eq (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    zHom (splicePhi l r p q w)
      = zHom (concatHomφ (𝟙 (zObj l)) (zHom (spliceNil r p q w))) :=
  congrArg zHom (splicePhi_eq_concat l r p q w)

/-- …and the rest as the staircase, concatenated with the untouched suffix. -/
theorem zHom_spliceNil_eq (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) :
    zHom (spliceNil r p q w)
      = zHom (concatHomφ (zHom (pairMerge p q w)) (𝟙 (zObj r))) :=
  congrArg zHom (spliceNil_eq_concat r p q w)

/-! ### Coordinates of a splice

Three cases, one per block: the beads before the cut, the two beads merged, the beads after.  The
staircase's own two beads are read off its two half-restrictions. -/

/-- **Before the cut a splice keeps every event's rank** — the outer split is the identity there. -/
theorem pos_coordMap_splicePhi_left (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (e : beadEvent l) :
    (pos (coordMap (splicePhi l r p q w) (eventInl l (p :: q :: r) e)) : ℕ) = (pos e : ℕ) := by
  rw [splicePhi_eq_concat]
  refine (congrArg (fun z => (pos z : ℕ))
    (coordMap_concatHomφ_left (𝟙 (zObj l)) (zHom (spliceNil r p q w)) e)).trans ?_
  refine (pos_eventInl _ _ _).trans ?_
  exact congrArg (fun z => (pos z : ℕ)) (congrFun (coordMap_id (a := l)) e)

/-- **On the merged block a splice is the staircase**, shifted past the beads before the cut. -/
theorem pos_coordMap_splicePhi_mid (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (e : beadEvent [p, q]) :
    (pos (coordMap (splicePhi l r p q w) (eventInr l (p :: q :: r) (eventInl [p, q] r e))) : ℕ)
      = dimSum l + (pos (coordMap (pairMerge p q w) e) : ℕ) := by
  rw [splicePhi_eq_concat]
  refine (congrArg (fun z => (pos z : ℕ))
    (coordMap_concatHomφ_right (𝟙 (zObj l)) (zHom (spliceNil r p q w)) _)).trans ?_
  refine (pos_eventInr _ _ _).trans (congrArg (dimSum l + ·) ?_)
  change (pos (coordMap (spliceNil r p q w) (eventInl [p, q] r e)) : ℕ) = _
  rw [spliceNil_eq_concat]
  exact (congrArg (fun z => (pos z : ℕ))
    (coordMap_concatHomφ_left (zHom (pairMerge p q w)) (𝟙 (zObj r)) e)).trans (pos_eventInl _ _ _)

/-- **After the cut a splice keeps every event's rank.** -/
theorem pos_coordMap_splicePhi_right (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (e : beadEvent r) :
    (pos (coordMap (splicePhi l r p q w) (eventInr l (p :: q :: r) (eventInr [p, q] r e))) : ℕ)
      = dimSum l + ((p : ℕ) + (q : ℕ) + (pos e : ℕ)) := by
  rw [splicePhi_eq_concat]
  refine (congrArg (fun z => (pos z : ℕ))
    (coordMap_concatHomφ_right (𝟙 (zObj l)) (zHom (spliceNil r p q w)) _)).trans ?_
  refine (pos_eventInr l ((p + q) :: r) _).trans (congrArg (dimSum l + ·) ?_)
  change (pos (coordMap (spliceNil r p q w) (eventInr [p, q] r e)) : ℕ) = _
  rw [spliceNil_eq_concat]
  refine (congrArg (fun z => (pos z : ℕ))
    (coordMap_concatHomφ_right (zHom (pairMerge p q w)) (𝟙 (zObj r)) e)).trans ?_
  refine (pos_eventInr [p + q] r (coordMap (𝟙 (⋁r)) e)).trans ?_
  rw [show coordMap (𝟙 (⋁r)) e = e from congrFun coordMap_id e]
  simp [dimSum]

/-- A cube-to-cube map is the Yoneda image of its own cell (cube Yoneda). -/
theorem yoneda_map_yonedaEquiv {m m' : ℕ} (f : (□m).toPsh ⟶ (□m').toPsh) :
    yoneda.map (yonedaEquiv f) = f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- The staircase's first bead flips the coordinates its left restriction frees. -/
theorem coordMap_pairMerge_zero (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ))
    (k : Fin ((([p, q] : List ℕ+).get 0 : ℕ))) :
    coordMap (pairMerge p q w) ⟨0, k⟩
      = ⟨0, faceEmb (yonedaEquiv (wedgeInl (□(p : ℕ)) (□(q : ℕ))
          ≫ (w : BPSet.Hom _ _).hom)) k⟩ := by
  refine coordMap_of_factor (pairMerge p q w) 0 0 _ ?_ k
  change wedgeInl (□(p : ℕ)) (□(q : ℕ) ∨ □0) ≫ wedge2MapPsh (𝟙 (□(p : ℕ))) (ρ_ (□(q : ℕ))).hom
      ≫ (w : BPSet.Hom _ _).hom ≫ wedgeInl (□((p + q : ℕ+) : ℕ)) (□0)
    = yoneda.map (yonedaEquiv (wedgeInl (□(p : ℕ)) (□(q : ℕ)) ≫ (w : BPSet.Hom _ _).hom))
        ≫ wedgeInl (□((p + q : ℕ+) : ℕ)) (□0)
  rw [yoneda_map_yonedaEquiv, wedge2MapPsh_inl_assoc, id_hom, Category.id_comp]
  exact (Category.assoc _ _ _).symm

/-- The staircase's second bead flips the coordinates its right restriction frees. -/
theorem coordMap_pairMerge_one (p q : ℕ+) (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ))
    (k : Fin ((([p, q] : List ℕ+).get 1 : ℕ))) :
    coordMap (pairMerge p q w) ⟨1, k⟩
      = ⟨0, faceEmb (yonedaEquiv (wedgeInr (□(p : ℕ)) (□(q : ℕ))
          ≫ (w : BPSet.Hom _ _).hom)) k⟩ := by
  refine coordMap_of_factor (pairMerge p q w) 1 0 _ ?_ k
  change wedgeInl (□(q : ℕ)) (□0) ≫ wedgeInr (□(p : ℕ)) (□(q : ℕ) ∨ □0)
      ≫ wedge2MapPsh (𝟙 (□(p : ℕ))) (ρ_ (□(q : ℕ))).hom
      ≫ (w : BPSet.Hom _ _).hom ≫ wedgeInl (□((p + q : ℕ+) : ℕ)) (□0)
    = yoneda.map (yonedaEquiv (wedgeInr (□(p : ℕ)) (□(q : ℕ)) ≫ (w : BPSet.Hom _ _).hom))
        ≫ wedgeInl (□((p + q : ℕ+) : ℕ)) (□0)
  rw [yoneda_map_yonedaEquiv, wedge2MapPsh_inr_assoc,
    show ((ρ_ (□(q : ℕ))).hom : BPSet.Hom _ _).hom = wedge2RightUnitPsh (□(q : ℕ)) from rfl,
    wedge2RightUnitPsh_inl_assoc]
  exact (Category.assoc _ _ _).symm

/-- The flattening of the staircase's source: bead `q` starts at `p`. -/
theorem pos_pair_one (p q : ℕ+) (k : Fin ((([p, q] : List ℕ+).get 1 : ℕ))) :
    (pos (⟨1, k⟩ : beadEvent [p, q]) : ℕ) = (p : ℕ) + (k : ℕ) := by
  rw [pos_mk]
  simp [beadStart, dimSum]

/-- **A staircase has two beads** — one of width `p`, one of width `q`, and an event of its source
is in one of them. -/
theorem pairEventCases {p q : ℕ+} {P : beadEvent [p, q] → Prop}
    (h0 : ∀ k : Fin (p : ℕ), P ⟨0, k⟩) (h1 : ∀ k : Fin (q : ℕ), P ⟨1, k⟩)
    (y : beadEvent [p, q]) : P y := by
  obtain ⟨i, k⟩ := y
  have hi : (i : ℕ) < 2 := by simp
  rcases Nat.lt_or_ge (i : ℕ) 1 with h | h
  · obtain rfl : i = 0 := Fin.ext (by simp; omega)
    exact h0 k
  · obtain rfl : i = 1 := Fin.ext (by simp; omega)
    exact h1 k

/-- **The merge staircase does not braid its two beads**: `cubeMerge` runs its first bead through
the low coordinate block and its second through the high one, both increasingly. -/
theorem pos_coordMap_pairMerge_cubeMerge (p q : ℕ+) (y : beadEvent [p, q]) :
    (pos (coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y) : ℕ) = (pos y : ℕ) := by
  induction y using pairEventCases with
  | h0 k =>
      rw [coordMap_pairMerge_zero, pos_cons_zero, pos_cons_zero]
      exact faceEmb_cubeMerge_inl _ _ k
  | h1 k =>
      rw [coordMap_pairMerge_one, pos_cons_zero, pos_pair_one]
      exact faceEmb_cubeMerge_inr _ _ k

end ChainCat
