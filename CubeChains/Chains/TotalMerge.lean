import CubeChains.Chains.MergeClass

/-!
# Chains/TotalMerge — the splice, and merging all the way down

`Ch Zbp` is the serial wedges (`Zbp` is terminal), and `spliceHom l r p q w` is a staircase `w`
spliced between two fixed stretches of beads.  `l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, so a
splice is the tensorator of `⋁` applied twice and its coordinate map is the staircase's own
(`pos_coordMap_splicePhi`).
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
    zObj (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) ⟶ zObj (l ++ ((1 : ℕ+) + 1) :: r) :=
  spliceHom l r 1 1 (cubeReorder 1 1)

theorem merge_mergeHom (l r : List ℕ+) (p q : ℕ+) : merge Zbp (mergeHom l r p q) :=
  ⟨spliceCut l r p q _, rfl⟩

/-! ### The splice as a double concatenation

`l ++ p :: q :: r` is `l ++ ([p, q] ++ r)`, and `splicePhi` is the tensorator of `⋁` applied
twice: identities on `l` and on `r`, the staircase `w` in the middle.  So `coordMap_inclL`
/`coordMap_inclR` read its coordinate map off the middle map alone. -/

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

/-! ### Coordinates of a splice

Three cases, one per block: the beads before the cut, the two beads merged, the beads after.  The
staircase's own two beads are read off its two half-restrictions. -/

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

/-- The two merged beads move by the staircase alone. -/
theorem coordMap_spliceNil_head (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (y : beadEvent [p, q]) :
    coordMap (spliceNil r p q w) (eventInl [p, q] r y)
      = eventInl [p + q] r (coordMap (pairMerge p q w) y) := by
  rw [spliceNil_eq_concat]
  exact coordMap_inclL _ (concatHomφ_inclL (zHom (pairMerge p q w)) (𝟙 (zObj r))) y

/-- The beads after the cut keep their coordinates. -/
theorem coordMap_spliceNil_tail (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (z : beadEvent r) :
    coordMap (spliceNil r p q w) (eventInr [p, q] r z) = eventInr [p + q] r z := by
  rw [spliceNil_eq_concat]
  have h := coordMap_inclR _ (concatHomφ_inclR (zHom (pairMerge p q w)) (𝟙 (zObj r))) z
  rwa [id_φ, coordMap_id, id_eq] at h

/-- The beads before the cut keep their coordinates. -/
theorem coordMap_splicePhi_head (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (x : beadEvent l) :
    coordMap (splicePhi l r p q w) (eventInl l (p :: q :: r) x)
      = eventInl l ((p + q) :: r) x := by
  rw [splicePhi_eq_concat]
  have h := coordMap_inclL _ (concatHomφ_inclL (𝟙 (zObj l)) (zHom (spliceNil r p q w))) x
  rwa [id_φ, coordMap_id, id_eq] at h

/-- The tail of the splice is the tail of the bare splice. -/
theorem coordMap_splicePhi_rest (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) (y : beadEvent (p :: q :: r)) :
    coordMap (splicePhi l r p q w) (eventInr l (p :: q :: r) y)
      = eventInr l ((p + q) :: r) (coordMap (spliceNil r p q w) y) := by
  rw [splicePhi_eq_concat]
  exact coordMap_inclR _ (concatHomφ_inclR (𝟙 (zObj l)) (zHom (spliceNil r p q w))) y

/-! ### The flattening under a splice

The staircase's own action on `[0, p+q)` — the function `g` below — is all a splice does; the
beads on either side of the cut keep their strands. -/

/-- **The bare splice acts by the staircase alone.** -/
theorem pos_coordMap_spliceNil (r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {g : ℕ → ℕ}
    (hg : ∀ y : beadEvent [p, q], (pos (coordMap (pairMerge p q w) y) : ℕ) = g (pos y : ℕ))
    (v : beadEvent (p :: q :: r)) {t : ℕ} (ht : (pos v : ℕ) = t) :
    (pos (coordMap (spliceNil r p q w) v) : ℕ) = if t < (p : ℕ) + (q : ℕ) then g t else t := by
  induction v using eventAppendCases (a := [p, q]) (b := r) with
  | hl y =>
      have hy : (pos y : ℕ) = t := (pos_eventInl [p, q] r y).symm.trans ht
      have hlt : (pos y : ℕ) < (p : ℕ) + q :=
        lt_of_lt_of_eq (pos y).isLt (by rw [dimSum_eq_sum_get]; simp [dimSum])
      rw [coordMap_spliceNil_head]
      refine (pos_eventInl [p + q] r _).trans ?_
      rw [hg, hy, if_pos (by omega)]
  | hr z =>
      have hz : dimSum ([p, q] : List ℕ+) + (pos z : ℕ) = t :=
        (pos_eventInr [p, q] r z).symm.trans ht
      rw [show dimSum ([p, q] : List ℕ+) = (p : ℕ) + q from by simp [dimSum]] at hz
      rw [coordMap_spliceNil_tail]
      refine (pos_eventInr [p + q] r z).trans ?_
      rw [show dimSum ([p + q] : List ℕ+) = (p : ℕ) + q from by simp [dimSum], if_neg (by omega)]
      omega

/-- **A splice moves only the beads it merges** — the staircase's action `g`, shifted past the
beads in front. -/
theorem pos_coordMap_splicePhi (l r : List ℕ+) (p q : ℕ+)
    (w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)) {g : ℕ → ℕ}
    (hg : ∀ y : beadEvent [p, q], (pos (coordMap (pairMerge p q w) y) : ℕ) = g (pos y : ℕ))
    (e : beadEvent (l ++ p :: q :: r)) {t : ℕ} (ht : (pos e : ℕ) = t) :
    (pos (coordMap (splicePhi l r p q w) e) : ℕ)
      = if t < dimSum l then t
        else dimSum l
          + (if t - dimSum l < (p : ℕ) + q then g (t - dimSum l) else t - dimSum l) := by
  induction e using eventAppendCases (a := l) (b := p :: q :: r) with
  | hl x =>
      have hx : (pos x : ℕ) = t := (pos_eventInl l (p :: q :: r) x).symm.trans ht
      have hlt : (pos x : ℕ) < dimSum l := lt_of_lt_of_eq (pos x).isLt (dimSum_eq_sum_get l)
      rw [coordMap_splicePhi_head, pos_eventInl, hx, if_pos (by omega)]
  | hr v =>
      have hv : dimSum l + (pos v : ℕ) = t := (pos_eventInr l (p :: q :: r) v).symm.trans ht
      rw [coordMap_splicePhi_rest, pos_eventInr,
        pos_coordMap_spliceNil r p q w hg v (t := (pos v : ℕ)) rfl,
        if_neg (show ¬(t < dimSum l) by omega), show t - dimSum l = (pos v : ℕ) from by omega]

end ChainCat
