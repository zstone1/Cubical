import CubeChains.Concurrency.Presentation.PaperPresents

/-!
# Concurrency/Presentation/RunCells — a word of bead cuts is the refinement it performs

Over a chain the atoms out of the runs form a web of ascents whose degree-two cells are the
codimension-two cuts out of a run, and those hold on the paper's cells (`Paper.readCut_cell`):

    run r ──atom k──▸ ▪ ◂──atom l── run r'        two climbs, one arrow

That is `Web.IsArtin`, so category-valued Matsumoto applies and a climb names one arrow.  Hence
`readCut_congr`: a word of bead cuts is pinned by the refinement it performs.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-- A renaming on either side of an arrow that is itself one. -/
private theorem eqToHom_sandwich {C : Type*} [Category C] {A B D E : C} (h₁ : A = B)
    {f : B ⟶ D} {h : B = D} (hf : f = eqToHom h) (h₂ : D = E) (hAE : A = E) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom hAE := by
  subst hf; rw [eqToHom_trans, eqToHom_trans]

/-- Renaming both sides of an arrow does not see which arrow it is. -/
private theorem sandwich_congr {C : Type*} [Category C] {A B D E : C} (h₁ : A = B) (h₂ : D = E)
    {f g : B ⟶ D} (h : f = g) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by rw [h]

/-! ## The atoms, read on the paper's cells -/

/-- The 0-cell of the contraction a run names, read there. -/
noncomputable def subObj {N : ℕ} {z : (chCutPoly K).V} (σ : RunPerm N z) :
    (Paper.poly K).presented := (readColl K).obj ((chCollapse K).poly.pt (runObj σ))

/-- The arrow a 1-cell names there. -/
noncomputable def subArr {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    (readColl K).obj ((chCollapse K).poly.pt X) ⟶ (readColl K).obj ((chCollapse K).poly.pt Y) :=
  (readColl K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath

/-- …and the arrow a climb names. -/
noncomputable def climbArr {N : ℕ} {z : (chCutPoly K).V} {a : RunPerm N z} :
    ∀ {b : RunPerm N z}, Climb (runDescents N z).perm a b → (subObj a ⟶ subObj b)
  | _, .nil => 𝟙 _
  | _, .cons R e => climbArr R ≫ subArr (ascAtom e)

theorem subF_climbPath {N : ℕ} {z : (chCutPoly K).V} {a : RunPerm N z} : ∀ {b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b), (readColl K).map (climbPath R) = climbArr R
  | _, .nil => (readColl K).map_id _
  | _, .cons R e => ((readColl K).map_comp (climbPath R)
      (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath).trans
    (congrArg (fun t => t ≫ subArr (ascAtom e)) (subF_climbPath R))

variable {X Y : (chCollapse K).V}

theorem subArr_eq_map (g : (chCollapse K).Gen X Y) :
    subArr g = (readColl K).map (runCellWord g) := by
  have h0 : keptWord (P := (chCollapse K).poly) RunCut (runCellWord g) (all_runCellWord g)
      = (runAtomWords K).map (runCellWord g) :=
    (subWords_of_all RunCut (word_all := all_runCellWord) runCellWord_self
      (runCellWord g) (all_runCellWord g)).symm
  have h : (runAtomWords K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = (runAtomWords K).map (runCellWord g) :=
    (Paths.lift_toPath _ _).trans h0
  exact congrArg (Paper.runPre.pathsFunctor ⋙ (Paper.poly K).quot).map h

/-- **A 1-cell reads on the paper's cells as the climb its word spells.** -/
theorem subArr_eq_climbArr (g : (chCollapse K).Gen X Y) (hg : ¬ RunCut g) :
    subArr g = eqToHom (congrArg (readColl K).obj (congrArg (chCollapse K).poly.pt
          (Subtype.ext (runObj_runBot_gen g)))).symm
      ≫ climbArr (genClimb g) ≫ eqToHom (congrArg (readColl K).obj
        (congrArg (chCollapse K).poly.pt (Subtype.ext (runObj_genTop g)))) := by
  rw [subArr_eq_map g, runCellWord, dif_neg hg]
  refine Eq.trans (Paths.map_cellCongr₂ (readColl K) _ _ _) ?_
  exact sandwich_congr _ _ (subF_climbPath (genClimb g))

/-- **An atom is pinned by its leg**, read at any naming of the two runs it joins. -/
theorem subArr_legAtom_eq {M : ℕ} {y : (chCutPoly K).V} {k : Fin (M - 1)}
    {w w' : zObj (atomComp M k) ⟶ shOf y} (hww : w = w')
    {X Y X' Y' : (chCollapse K).V}
    (hX : eltRep (eltRestrict y w) = X.1) (hY : eltRestrict y (atomOnes M k ≫ w) = Y.1)
    (hX' : eltRep (eltRestrict y w') = X'.1) (hY' : eltRestrict y (atomOnes M k ≫ w') = Y'.1)
    (p : (readColl K).obj ((chCollapse K).poly.pt X)
      = (readColl K).obj ((chCollapse K).poly.pt X'))
    (q : (readColl K).obj ((chCollapse K).poly.pt Y')
      = (readColl K).obj ((chCollapse K).poly.pt Y)) :
    subArr (legAtom w hX hY) = eqToHom p ≫ subArr (legAtom w' hX' hY') ≫ eqToHom q := by
  subst hww
  obtain rfl : X = X' := Subtype.ext (hX.symm.trans hX')
  obtain rfl : Y = Y' := Subtype.ext (hY.symm.trans hY')
  simp

/-! ## Reading the bead cuts

A letter of the lifted cut polygraph collapses to the empty word when it is a merge and to its own
1-cell otherwise; `cutArr` is what it names either way. -/

/-- The arrow a bead cut names on the paper's cells. -/
noncomputable def cutArr {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') :
    (readCut K).obj ((chCutPoly K).pt z) ⟶ (readCut K).obj ((chCutPoly K).pt z') :=
  (readCut K).map (Polygraph.cell e).toPath

theorem cutArr_eq {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') :
    cutArr e = (readColl K).map ((chCollapse K).cell (Polygraph.cell e)) :=
  congrArg (readColl K).map (Paths.lift_toPath (chCollapse K).pre (Polygraph.cell e))

/-- **A merge names a renaming.** -/
theorem cutArr_merge {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') (he : chCutPicked K e)
    (h : (readCut K).obj ((chCutPoly K).pt z) = (readCut K).obj ((chCutPoly K).pt z')) :
    cutArr e = eqToHom h := by
  rw [cutArr_eq, (chCollapse K).cell_of_S (Polygraph.cell e) he]
  refine Eq.trans (Paths.map_cellCongr₂ (readColl K) _ _ _) ?_
  exact eqToHom_sandwich _ (((readColl K).map_id _).trans (eqToHom_refl _ rfl).symm) _ h

/-- **…and any other cut is its own 1-cell of the collapse.** -/
theorem cutArr_gen {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z')
    (he : ¬ chCutPicked K e) :
    cutArr e = subArr ((chCollapse K).genCell (Polygraph.cell e) he) := by
  rw [cutArr_eq, (chCollapse K).cell_of_not_S (Polygraph.cell e) he]
  rfl

theorem readCut_two {a b c : (chCutPoly K).V} (f : (chCutPoly K).Gen a b)
    (g : (chCutPoly K).Gen b c) :
    (readCut K).map ((Quiver.Path.nil.cons (Polygraph.cell f)).cons (Polygraph.cell g))
      = cutArr f ≫ cutArr g :=
  (readCut K).map_comp (Polygraph.cell f).toPath (Polygraph.cell g).toPath

/-- **The two factorisations of the greatest codimension-two cut out of a run spell one word** —
the only 2-cell the paper's polygraph needs at degree zero. -/
theorem cutArr_pair {z zm zm' zd : (chCutPoly K).V}
    (e₁ : (chCutPoly K).Gen zd zm) (e₂ : (chCutPoly K).Gen zm z)
    (e₁' : (chCutPoly K).Gen zd zm') (e₂' : (chCutPoly K).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1)
    (htop : Paper.IsTop (Cut.genHom e₂.1 ≫ Cut.genHom e₁.1)) :
    cutArr e₁ ≫ cutArr e₂ = cutArr e₁' ≫ cutArr e₂' :=
  (readCut_two e₁ e₂).symm.trans
    ((Paper.readCut_cell (pairCell e₁ e₂ e₁' e₂' hev) htop).trans (readCut_two e₁' e₂'))

/-! ## A cut over a base, read at the runs of its two ends -/

/-- The object a 0-cell of the contraction names on the paper's cells. -/
noncomputable abbrev subPt (X : (chCollapse K).V) : (Paper.poly K).presented :=
  (readColl K).obj ((chCollapse K).poly.pt X)

theorem subPt_eq {z : (chCutPoly K).V} {X : (chCollapse K).V} (hX : eltRep z = X.1) :
    (readCut K).obj ((chCutPoly K).pt z) = subPt X :=
  congrArg subPt (Subtype.ext hX : (⟨eltRep z, eltRep_idem z⟩ : (chCollapse K).V) = X)

/-- The arrow a cut over a base names between two named runs. -/
noncomputable def atRun {X Y : (chCollapse K).V} {z₁ z₂ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1)
    (f : (readCut K).obj ((chCutPoly K).pt z₁) ⟶ (readCut K).obj ((chCutPoly K).pt z₂)) :
    subPt X ⟶ subPt Y :=
  eqToHom (subPt_eq hX).symm ≫ f ≫ eqToHom (subPt_eq hY)

theorem atRun_comp {X Y Z : (chCollapse K).V} {z₁ z₂ z₃ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1) (hZ : eltRep z₃ = Z.1)
    (f : (readCut K).obj ((chCutPoly K).pt z₁) ⟶ (readCut K).obj ((chCutPoly K).pt z₂))
    (g : (readCut K).obj ((chCutPoly K).pt z₂) ⟶ (readCut K).obj ((chCutPoly K).pt z₃)) :
    atRun hX hZ (f ≫ g) = atRun hX hY f ≫ atRun hY hZ g :=
  Iso.homCongr_comp (eqToIso (subPt_eq hX)) (eqToIso (subPt_eq hY)) (eqToIso (subPt_eq hZ)) f g

theorem atRun_eqToHom {X Y : (chCollapse K).V} {z₁ z₂ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1)
    (h : (readCut K).obj ((chCutPoly K).pt z₁) = (readCut K).obj ((chCutPoly K).pt z₂))
    (hXY : X = Y) : atRun hX hY (eqToHom h) = eqToHom (congrArg subPt hXY) :=
  eqToHom_sandwich _ rfl _ _

/-- **An atom's cut, read at the runs it joins, is that atom.** -/
theorem atRun_topCut {N : ℕ} {k : Fin (N - 1)} {z : (chCutPoly K).V}
    (w : zObj (atomComp N k) ⟶ shOf z) {X Y : (chCollapse K).V}
    (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRep (eltRestrict z (atomOnes N k ≫ w)) = Y.1) :
    atRun hX hY (cutArr (cutGen (c := eltRestrict z w)
        (c' := eltRestrict z (atomOnes N k ≫ w)) (atomOnes N k) (codim_atomOnes N k) rfl))
      = subArr (legAtom w hX ((eltRep_eq_self rfl).symm.trans hY)) := by
  rw [cutArr_gen _ (fun hm => not_W_atomOnes N k ((merge_iff _).mp hm).1)]
  exact (subArr_legAtom_eq (w' := w) rfl hX ((eltRep_eq_self rfl).symm.trans hY)
    (X' := ⟨eltRep (eltRestrict z w), eltRep_idem _⟩)
    (Y' := ⟨eltRep (eltRestrict z (atomOnes N k ≫ w)), eltRep_idem _⟩) rfl
    (eltRep_eq_self rfl).symm _ _).symm

/-! ## The cell over a pair chain

The degree-two chain two parabolic cuts share (`pairChain`) sits over the base carrying the foot's
own crossing permutation (`exists_pairLeg`), and the legs out of it realise the two words the cell
compares. -/

variable {N : ℕ} {z : (chCutPoly K).V}

theorem crossPerm_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    crossPerm (dimSum_atomComp N e.idx) (ascLeg e) = a.1 := by
  have h := crossPerm_comp (dimSum_replicate N) (mergeOnes N e.idx) (ascLeg e)
  rw [mergeOnes_ascLeg e, a.crossPerm_arr, crossPerm_eq_one_of_W _ (W_mergeOnes N e.idx),
    mul_one] at h
  exact h.symm

theorem eltRep_legChain {k : Fin (N - 1)} {σ : RunPerm N z} (w : zObj (atomComp N k) ⟶ shOf z)
    (hσ : mergeOnes N k ≫ w = σ.arr) : eltRep (eltRestrict z w) = (runObj σ).1 :=
  (eltRep_eltRestrict_atom w).trans (congrArg (eltRestrict z) hσ)

theorem eltRep_pairChain {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z)
    {σ : RunPerm N z} (hσ : runMerge E hE ≫ Q = σ.arr) :
    eltRep (eltRestrict z Q) = (runObj σ).1 :=
  (eltRestrict_merge_comp Q (W_runMerge E hE) (W_zRunMerge E)
      (congrArg (fun n => zObj (𝟙^n)) hE.symm)).symm.trans (congrArg (eltRestrict z) hσ)

/-- A cut over a base into the chain a leg names. -/
noncomputable def midCut {E : Ch Zbp} (Q : E ⟶ shOf z) {k : Fin (N - 1)}
    (v : zObj (atomComp N k) ⟶ E) (hv : codim v = 1) :
    (chCutPoly K).Gen (eltRestrict z Q) (eltRestrict z (v ≫ Q)) := cutGen v hv rfl

/-- …and the cut out of a run above it, named at the run-arrow it reaches. -/
noncomputable def topCut {E : Ch Zbp} (Q : E ⟶ shOf z) {k : Fin (N - 1)}
    (v : zObj (atomComp N k) ⟶ E) {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)} (hf : codim f = 1)
    {r : zObj (𝟙^N) ⟶ E} (hfv : f ≫ v = r) :
    (chCutPoly K).Gen (eltRestrict z (v ≫ Q)) (eltRestrict z (r ≫ Q)) :=
  cutGen f hf (congrArg (fun t : zObj (𝟙^N) ⟶ shOf z => (wedgeHoms K).map t.op z.2)
    (congrArg (fun t : zObj (𝟙^N) ⟶ E => t ≫ Q) hfv))

theorem atRun_topCut' {k : Fin (N - 1)} {E : Ch Zbp} (Q : E ⟶ shOf z)
    (v : zObj (atomComp N k) ⟶ E) {r : zObj (𝟙^N) ⟶ E} (hfv : atomOnes N k ≫ v = r)
    {X Y : (chCollapse K).V} (hX : eltRep (eltRestrict z (v ≫ Q)) = X.1)
    (hY : eltRep (eltRestrict z (r ≫ Q)) = Y.1) (hY' : eltRestrict z (r ≫ Q) = Y.1) :
    atRun hX hY (cutArr (topCut Q v (codim_atomOnes N k) hfv))
      = subArr (legAtom (v ≫ Q) hX
        ((congrArg (fun t : zObj (𝟙^N) ⟶ E => eltRestrict z (t ≫ Q)) hfv).trans hY')) := by
  subst hfv
  exact atRun_topCut (v ≫ Q) hX hY

/-- **Two two-step factorisations over one chain spell one word**, read at the runs of their
ends. -/
theorem legPair {E : Ch Zbp} (Q : E ⟶ shOf z) {k l : Fin (N - 1)}
    {v : zObj (atomComp N k) ⟶ E} (hv : codim v = 1)
    {v' : zObj (atomComp N l) ⟶ E} (hv' : codim v' = 1)
    {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)} (hf : codim f = 1)
    {f' : zObj (𝟙^N) ⟶ zObj (atomComp N l)} (hf' : codim f' = 1)
    {r : zObj (𝟙^N) ⟶ E} (hfv : f ≫ v = r) (hfv' : f' ≫ v' = r) (htop : Paper.IsTop r)
    {X M M' Y : (chCollapse K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hM : eltRep (eltRestrict z (v ≫ Q)) = M.1) (hM' : eltRep (eltRestrict z (v' ≫ Q)) = M'.1)
    (hY : eltRep (eltRestrict z (r ≫ Q)) = Y.1) :
    atRun hX hM (cutArr (midCut Q v hv)) ≫ atRun hM hY (cutArr (topCut Q v hf hfv))
      = atRun hX hM' (cutArr (midCut Q v' hv')) ≫ atRun hM' hY (cutArr (topCut Q v' hf' hfv')) := by
  rw [← atRun_comp hX hM hY, ← atRun_comp hX hM' hY]
  refine congrArg (atRun hX hY) (cutArr_pair _ _ _ _ (hfv.trans hfv'.symm) ?_)
  rw [show Cut.genHom (topCut Q v hf hfv).1 ≫ Cut.genHom (midCut Q v hv).1 = r from hfv]
  exact htop

theorem subArr_ascAtom_eq_legAtom {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b)
    {w : zObj (atomComp N e.idx) ⟶ shOf z} (hw : ascLeg e = w)
    {X Y : (chCollapse K).V} (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRestrict z (atomOnes N e.idx ≫ w) = Y.1)
    (p : subPt (runObj a) = subPt X) (q : subPt Y = subPt (runObj b)) :
    subArr (ascAtom e) = eqToHom p ≫ subArr (legAtom w hX hY) ≫ eqToHom q :=
  subArr_legAtom_eq hw _ _ hX hY p q

/-! ## A 1-cell read at an explicit strand count

`genTop` and `runBot` are taken at `vCount`; the cells below the square need them at the count the
pair chain names, so both come with an explicit `hM` and `subst` moves between them. -/

noncomputable def genTopAt {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : RunPerm M g.dom :=
  runOf (runMerge (shOf g.cod) ((dimSum_eq_of_hom (genCut g)).trans hM) ≫ genCut g)

theorem arr_genTopAt {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) :
    (genTopAt g hM).arr
      = runMerge (shOf g.cod) ((dimSum_eq_of_hom (genCut g)).trans hM) ≫ genCut g := arr_runOf _

theorem runObj_genTopAt {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : (runObj (genTopAt g hM)).1 = B.1 := by
  subst hM; exact runObj_genTop g

theorem subObj_runBot_gen {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : subPt A = subObj (runBot g.dom hM) :=
  (congrArg subPt (Subtype.ext ((runObj_runBot g.dom hM).trans g.rep_dom))).symm

theorem subObj_genTopAt {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : subObj (genTopAt g hM) = subPt B :=
  congrArg subPt (Subtype.ext (runObj_genTopAt g hM))

/-! ## A run over a refinement, read over the chain it refines

`eltRestrict` is functorial on the nose, so a cut out of a run over `eltRestrict u t` *is* the cut
over `u` along the composite: only the 0-cells' names change, and the crossings add.  This sits
before the pair chain because the cells below the square are read at a leg's own base. -/

/-- A run over a chain's refinement, read over the chain. -/
noncomputable def pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : RunPerm M u := runOf (σ.arr ≫ t)

theorem arr_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : (pushPerm t σ).arr = σ.arr ≫ t := arr_runOf _

theorem val_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) (σ : RunPerm M (eltRestrict u t)) :
    (pushPerm t σ).1 = crossPerm hd t * σ.1 :=
  (runOf_val (σ.arr ≫ t)).trans ((crossPerm_comp (dimSum_replicate M) σ.arr t).trans
    (congrArg (fun p => crossPerm hd t * p) σ.crossPerm_arr))

theorem permLen_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) (σ : RunPerm M (eltRestrict u t)) :
    permLen (pushPerm t σ).1 = permLen σ.1 + permLen (crossPerm hd t) :=
  ((congrArg permLen (runOf_val (σ.arr ≫ t))).trans
      (permLen_crossPerm_comp (dimSum_replicate M) σ.arr t)).trans
    (congrArg (fun n => n + permLen (crossPerm hd t)) (congrArg permLen σ.crossPerm_arr))

theorem runObj_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : (runObj (pushPerm t σ)).1 = (runObj σ).1 :=
  congrArg (eltRestrict u) (arr_pushPerm t σ)

theorem subObj_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : subObj (pushPerm t σ) = subObj σ :=
  congrArg subPt (Subtype.ext (runObj_pushPerm t σ))

/-- **Pushing an ascent onto a coarser base** — crossings add, so the length still goes up by one
and `ascent_of_permLen_mul_adjT` reads the ascent back off it. -/
noncomputable def pushAscent {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (e : Ascent (runDescents M (eltRestrict u t)).perm a b) :
    Ascent (runDescents M u).perm (pushPerm t a) (pushPerm t b) where
  idx := e.idx
  asc := by
    have hlb : permLen b.1 = permLen a.1 + 1 := e.permLen_eq
    have hperm : (pushPerm t b).1 = (pushPerm t a).1 * adjT e.idx := by
      rw [val_pushPerm t hd b, val_pushPerm t hd a, mul_assoc]
      exact congrArg (fun p => crossPerm hd t * p) e.perm_eq
    refine ascent_of_permLen_mul_adjT ?_
    rw [runDescents_perm, ← hperm, permLen_pushPerm t hd b, permLen_pushPerm t hd a]
    omega
  perm_eq := by
    rw [runDescents_perm, runDescents_perm, val_pushPerm t hd b, val_pushPerm t hd a, mul_assoc]
    exact congrArg (fun p => crossPerm hd t * p) e.perm_eq

/-- …and a whole climb. -/
noncomputable def pushClimb {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a : RunPerm M (eltRestrict u t)} :
    ∀ {b : RunPerm M (eltRestrict u t)}, Climb (runDescents M (eltRestrict u t)).perm a b →
      Climb (runDescents M u).perm (pushPerm t a) (pushPerm t b)
  | _, .nil => .nil
  | _, .cons R e => (pushClimb t hd R).cons (pushAscent t hd e)

/-- The leg of a pushed ascent is its own leg, composed with the refinement. -/
theorem ascLeg_pushAscent {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (e : Ascent (runDescents M (eltRestrict u t)).perm a b) :
    ascLeg (pushAscent t hd e) = ascLeg e ≫ t :=
  hom_ext_of_crossPerm (h := dimSum_atomComp M e.idx)
    (((crossPerm_ascLeg (pushAscent t hd e)).trans (val_pushPerm t hd a)).trans
      ((congrArg (fun p => crossPerm hd t * p) (crossPerm_ascLeg e).symm).trans
        (crossPerm_comp (dimSum_atomComp M e.idx) (ascLeg e) t).symm))

/-- **A pushed atom is that atom** — the leg composes with the refinement, and the chain it cuts is
the same one. -/
theorem subArr_ascAtom_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (e : Ascent (runDescents M (eltRestrict u t)).perm a b)
    (p : subObj (pushPerm t a) = subObj a) (q : subObj b = subObj (pushPerm t b)) :
    subArr (ascAtom (pushAscent t hd e)) = eqToHom p ≫ subArr (ascAtom e) ≫ eqToHom q :=
  subArr_ascAtom_eq_legAtom (pushAscent t hd e) (ascLeg_pushAscent t hd e)
    (X := runObj a) (Y := runObj b) (eltRep_ascLeg e)
    (congrArg (eltRestrict (eltRestrict u t)) (atomOnes_ascLeg e)) p q

theorem climbArr_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (R : Climb (runDescents M (eltRestrict u t)).perm a b) :
    climbArr (pushClimb t hd R)
      = eqToHom (subObj_pushPerm t a) ≫ climbArr R ≫ eqToHom (subObj_pushPerm t b).symm := by
  induction R with
  | nil =>
      change 𝟙 (subObj (pushPerm t a)) = eqToHom (subObj_pushPerm t a) ≫ 𝟙 (subObj a)
        ≫ eqToHom (subObj_pushPerm t a).symm
      simp
  | cons R e ih =>
      change climbArr (pushClimb t hd R) ≫ subArr (ascAtom (pushAscent t hd e))
        = eqToHom _ ≫ (climbArr R ≫ subArr (ascAtom e)) ≫ eqToHom _
      rw [ih, subArr_ascAtom_push t hd e (subObj_pushPerm t _) (subObj_pushPerm t _).symm]
      exact (Iso.homCongr_comp (eqToIso (subObj_pushPerm t _).symm)
        (eqToIso (subObj_pushPerm t _).symm) (eqToIso (subObj_pushPerm t _).symm)
        (climbArr R) (subArr (ascAtom e))).symm

/-- **A run reached through a base performs the base's crossing permutation** — the merge onto the
base makes no crossing. -/
theorem val_eq_crossPerm {u : (chCutPoly K).V} {M : ℕ} {d : Ch Zbp} (t : d ⟶ shOf u)
    (hd : dimSum d.dims = M) {σ : RunPerm M u} (hσ : runMerge d hd ≫ t = σ.arr) :
    σ.1 = crossPerm hd t := by
  rw [← σ.crossPerm_arr, ← hσ, crossPerm_comp (dimSum_replicate M) (runMerge d hd) t,
    crossPerm_eq_one_of_W _ (W_runMerge d hd), mul_one]

/-- **A 1-cell whose cut does not start at a run is the climb its word spells**, read at an explicit
strand count. -/
theorem exists_climb_subArr {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) (hg : ¬ RunCut g)
    (p : subPt A = subObj (runBot g.dom hM)) (q : subObj (genTopAt g hM) = subPt B) :
    ∃ R : Climb (runDescents M g.dom).perm (runBot g.dom hM) (genTopAt g hM),
      subArr g = eqToHom p ≫ climbArr R ≫ eqToHom q := by
  subst hM
  exact ⟨genClimb g, subArr_eq_climbArr g hg⟩

/-- **A bead cut over a base, read at the runs of its two ends, is a climb of atoms** — the word the
cut spells, pushed onto the base it sits over. -/
theorem exists_climb_midCut {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z)
    (hdeg : degree E = 2) {k : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ E} (hnW : ¬ W Zbp w)
    {a b : RunPerm N z} (ha : runMerge E hE ≫ Q = a.arr)
    (hb : mergeOnes N k ≫ (w ≫ Q) = b.arr) :
    ∃ R : Climb (runDescents N z).perm a b,
      atRun (eltRep_pairChain hE Q ha) (eltRep_legChain (w ≫ Q) hb)
          (cutArr (midCut Q w (codim_leg hdeg w))) = climbArr R := by
  have hnotS : ¬ chCutPicked K (midCut Q w (codim_leg hdeg w)) :=
    fun hmg => hnW ((merge_iff w).mp hmg).1
  set g := (chCollapse K).genCell
    (Polygraph.cell (midCut Q w (codim_leg hdeg w))) hnotS with hg
  have hnRC : ¬ RunCut g := by
    intro hrc
    have h0 : (zObj (atomComp N k) : Ch Zbp) = zObj (𝟙^N) :=
      shOf_eq_ones_of_eltRep hrc (dimSum_atomComp N k)
    have h1 : (1 : ℕ) = 0 := by
      rw [← degree_atomComp N k, ← show ChainCat.degree (zObj (𝟙^N)) = 0 from
        (degree_eq_zero_iff _).mpr fun x hx => List.eq_of_mem_replicate hx]
      exact congrArg (fun c : Ch Zbp => ChainCat.degree c) h0
    exact absurd h1 one_ne_zero
  obtain ⟨R₀, hR₀⟩ := exists_climb_subArr g hE hnRC (subObj_runBot_gen g hE) (subObj_genTopAt g hE)
  obtain rfl : a = pushPerm Q (runBot (eltRestrict z Q) hE) :=
    Subtype.ext ((val_eq_crossPerm Q hE ha).trans
      (by rw [val_pushPerm Q hE, runBot_val, mul_one]))
  obtain rfl : b = pushPerm Q (genTopAt g hE) :=
    Subtype.ext ((val_eq_crossPerm (w ≫ Q) (dimSum_atomComp N k) hb).trans (by
      rw [val_pushPerm Q hE, ← (genTopAt g hE).crossPerm_arr, arr_genTopAt,
        crossPerm_comp (dimSum_replicate N) (runMerge (shOf g.cod) _) (genCut g),
        crossPerm_eq_one_of_W _ (W_runMerge _ _), mul_one,
        crossPerm_comp (dimSum_atomComp N k) w Q]
      exact rfl))
  refine ⟨pushClimb Q hE R₀, ?_⟩
  rw [cutArr_gen _ hnotS, ← hg, hR₀, atRun, climbArr_push]
  exact eqToHom_nest _ _ _ _ _ _

/-- **The two factorisations of the greatest cut out of a run spell one word** — the relation a
degree-two chain imposes, read at the runs.  Only the greatest cut gives one: that is the single
degree-zero 2-cell the paper's polygraph needs. -/
theorem atRun_midCut_pair {E : Ch Zbp} (Q : E ⟶ shOf z) (hdeg : degree E = 2)
    {k l : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ E} {w' : zObj (atomComp N l) ⟶ E}
    (hsq : atomOnes N l ≫ w' = atomOnes N k ≫ w) (htop : Paper.IsTop (atomOnes N k ≫ w))
    {X M M' Y : (chCollapse K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hw : eltRep (eltRestrict z (w ≫ Q)) = M.1) (hw' : eltRep (eltRestrict z (w' ≫ Q)) = M'.1)
    (hY : eltRestrict z ((atomOnes N k ≫ w) ≫ Q) = Y.1) :
    atRun hX hw (cutArr (midCut Q w (codim_leg hdeg w))) ≫ subArr (legAtom (w ≫ Q) hw hY)
      = atRun hX hw' (cutArr (midCut Q w' (codim_leg hdeg w')))
        ≫ subArr (legAtom (w' ≫ Q) hw'
          ((congrArg (fun t : zObj (𝟙^N) ⟶ E => eltRestrict z (t ≫ Q)) hsq).trans hY)) := by
  have c1 := legPair Q (codim_leg hdeg w) (codim_leg hdeg w') (codim_atomOnes N k)
    (codim_atomOnes N l) (r := atomOnes N k ≫ w) rfl hsq htop hX hw hw'
    ((eltRep_eq_self rfl).trans hY)
  rw [atRun_topCut' Q w (r := atomOnes N k ≫ w) rfl (X := M) (Y := Y) hw
      ((eltRep_eq_self rfl).trans hY) hY,
    atRun_topCut' Q w' (r := atomOnes N k ≫ w) hsq (X := M') (Y := Y) hw'
      ((eltRep_eq_self rfl).trans hY) hY] at c1
  exact c1

/-- **The crossing permutation of a leg into a placed chain.** -/
theorem crossPerm_leg_comp {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z)
    {σ : Perm (Fin N)} (hQ : crossPerm hE Q = σ) {k : Fin (N - 1)}
    (w : zObj (atomComp N k) ⟶ E) {s : Perm (Fin N)}
    (hw : crossPerm (dimSum_atomComp N k) w = s) :
    crossPerm (dimSum_atomComp N k) (w ≫ Q) = σ * s := by
  rw [crossPerm_comp (dimSum_atomComp N k) w Q, hQ, hw]

/-- **The run a cut out of a leg into a placed chain reaches.** -/
theorem leg_run {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z) {σ : Perm (Fin N)}
    (hQ : crossPerm hE Q = σ) {k : Fin (N - 1)} (w : zObj (atomComp N k) ⟶ E)
    {s : Perm (Fin N)} (hw : crossPerm (dimSum_atomComp N k) w = s)
    (g : zObj (𝟙^N) ⟶ zObj (atomComp N k)) {t : Perm (Fin N)}
    (hg : crossPerm (dimSum_replicate N) g = t) {τ : RunPerm N z} (hτ : σ * s * t = τ.1) :
    g ≫ w ≫ Q = τ.arr := by
  refine τ.eq_arr ?_
  rw [crossPerm_comp (dimSum_replicate N) g (w ≫ Q), crossPerm_leg_comp hE Q hQ w hw, hg]
  exact hτ

/-- …and the run the placed chain's own merge reaches. -/
theorem base_run {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z) {c : RunPerm N z}
    (hQ : crossPerm hE Q = c.1) : runMerge E hE ≫ Q = c.arr := by
  refine c.eq_arr ?_
  rw [crossPerm_comp (dimSum_replicate N) (runMerge E hE) Q, hQ,
    crossPerm_eq_one_of_W _ (W_runMerge E hE), mul_one]

/-- **The degree-two chain of two parabolic cuts, placed over a run** — its own run is that run. -/
theorem exists_pairQ (hz : dimSum (shOf z).dims = N) {i j : Fin (N - 1)}
    (hij' : (i : ℕ) ≠ (j : ℕ)) {c : RunPerm N z}
    (hci : c.1 (adjLo i) < c.1 (adjHi i)) (hcj : c.1 (adjLo j) < c.1 (adjHi j))
    (hi : ∃ σ : RunPerm N z, σ.1 = c.1 * adjT i) (hj : ∃ σ : RunPerm N z, σ.1 = c.1 * adjT j) :
    ∃ Q : pairChain N i j hij' ⟶ shOf z, crossPerm (dimSum_pairChain hij') Q = c.1 := by
  refine exists_pairLeg hij' hz ?_ ?_ c.crossPerm_arr
  · rintro k (hk | hk)
    · obtain rfl : k = i := Fin.ext hk
      obtain ⟨σ, hσ⟩ := hi
      refine index_adj_eq_of_descent hz σ.arr ?_
      simp only [RunPerm.crossPerm_arr, hσ, Equiv.Perm.mul_apply, adjT_lo, adjT_hi]
      exact hci
    · obtain rfl : k = j := Fin.ext hk
      obtain ⟨σ, hσ⟩ := hj
      refine index_adj_eq_of_descent hz σ.arr ?_
      simp only [RunPerm.crossPerm_arr, hσ, Equiv.Perm.mul_apply, adjT_lo, adjT_hi]
      exact hcj
  · rintro k (hk | hk)
    · obtain rfl : k = i := Fin.ext hk; exact hci
    · obtain rfl : k = j := Fin.ext hk; exact hcj

/-! ## The web of atoms over a chain

The runs over a chain index the objects and the atoms are the ascents.  Two ascents into one run out
of different runs span a pair of cuts, the pair chain sits over the foot they share
(`exists_pairQ`), and the two one-cut factorisations of its greatest cut spell the two climbs
(`exists_pairTop`) — which is `Web.IsArtin`, so a climb names one arrow independently of the climb.

    c ──wi──▸ b ──atom──▸ v        the two factorisations of one degree-two cut,
      └──wj──▸ b' ─atom──▸ v       each a climb below an atom -/

/-- **The atoms out of the runs over a chain, as a web of ascents** — the strand count is carried
only to pin it. -/
noncomputable def runWeb (_hz : dimSum (shOf z).dims = N) :
    Web N (RunPerm N z) ((Paper.poly K).presented) where
  toDescents := runDescents N z
  obj := subObj
  arr e := subArr (ascAtom e)

theorem runWeb_perm (hz : dimSum (shOf z).dims = N) (σ : RunPerm N z) :
    (runWeb hz).perm σ = σ.1 := rfl

theorem runWeb_arr (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (e : Ascent (runWeb hz).perm a b) : (runWeb hz).arr e = subArr (ascAtom e) := rfl

theorem ev_eq_climbArr (hz : dimSum (shOf z).dims = N) {a : RunPerm N z} :
    ∀ {b : RunPerm N z} (R : Climb (runDescents N z).perm a b),
      (runWeb hz).ev R = climbArr R
  | _, .nil => rfl
  | _, .cons R e => congrArg (fun t => t ≫ subArr (ascAtom e)) (ev_eq_climbArr hz R)

/-- **Artin's relation holds over every chain**: the foot's own pair chain carries the degree-two
cell, and the two legs of that cell are the two climbs.  No index arithmetic: the length hypothesis
says the foot is as far below as the pair's order, which is what `exists_pairTop` reads. -/
theorem isArtin_runWeb (hz : dimSum (shOf z).dims = N) : (runWeb hz).IsArtin := by
  intro v b b' c e e' hbb' hcb hcb' hlen
  simp only [runWeb_perm] at hcb hcb' hlen
  have hij : (e.idx : ℕ) ≠ (e'.idx : ℕ) :=
    (e.idx_ne_iff (runDescents N z).perm_inj e').mpr hbb'
  -- the residue the foot sits below the top by
  obtain ⟨σ, hσdef⟩ : ∃ s : Perm (Fin N), s = c.1⁻¹ * v.1 := ⟨_, rfl⟩
  have hcσv : c.1 * σ = v.1 := by rw [hσdef]; exact mul_inv_cancel_left _ _
  have hadd : permLen c.1 + permLen σ = permLen v.1 := by
    rw [hσdef]
    simpa only [WeakOrder.perm_of] using WeakOrder.le_def.mp (hcb.trans e.le)
  have hσlen : permLen σ = orderOf (adjT e.idx * adjT e'.idx) := by
    rw [← show (b.1)⁻¹ * b'.1 = adjT e.idx * adjT e'.idx from e.inv_mul e']; omega
  -- each of the two ascents is a descent of the residue
  have hdesc : ∀ {w : RunPerm N z} {k : Fin (N - 1)},
      WeakOrder.of c.1 ≤ WeakOrder.of w.1 → w.1 = v.1 * adjT k →
      permLen v.1 = permLen w.1 + 1 → permLen (σ * adjT k) + 1 = permLen σ := by
    intro w k hcw hw h2
    have h1 : permLen c.1 + permLen (σ * adjT k) = permLen w.1 := by
      have h := WeakOrder.le_def.mp hcw
      simp only [WeakOrder.perm_of] at h
      rwa [show c.1⁻¹ * w.1 = σ * adjT k from by rw [hw, hσdef, mul_assoc]] at h
    omega
  have hLi : permLen (σ * adjT e.idx) + 1 = permLen σ :=
    hdesc hcb e.perm_eq' e.permLen_eq
  have hLj : permLen (σ * adjT e'.idx) + 1 = permLen σ :=
    hdesc hcb' e'.perm_eq' e'.permLen_eq
  have hσi : σ (adjHi e.idx) < σ (adjLo e.idx) := descent_of_permLen_drop hLi
  have hσj : σ (adjHi e'.idx) < σ (adjLo e'.idx) := descent_of_permLen_drop hLj
  -- the pair chain's greatest cut, with its two one-cut factorisations
  obtain ⟨wi, wj, hinv, hwi, hwj, hcap⟩ := exists_pairTop hij hσi hσj hσlen
  -- the residue is a palindrome, so it descends on the left too, and the foot ascends
  have hleft : ∀ {k : Fin (N - 1)}, permLen (σ * adjT k) + 1 = permLen σ →
      permLen (adjT k * σ) + 1 = permLen σ := by
    intro k hk
    have h : permLen (adjT k * σ) = permLen (σ * adjT k) := by
      rw [← permLen_inv (adjT k * σ), mul_inv_rev, adjT_inv, hinv]
    omega
  have hup : ∀ {k : Fin (N - 1)}, permLen (σ * adjT k) + 1 = permLen σ →
      permLen (c.1 * adjT k) = permLen c.1 + 1 := by
    intro k hk
    have hL := hleft hk
    have hle1 := permLen_mul_le (c.1 * adjT k) (adjT k * σ)
    rw [show c.1 * adjT k * (adjT k * σ) = v.1 from by
      rw [← mul_assoc, mul_adjT_adjT, hcσv]] at hle1
    have hle2 := permLen_mul_le c.1 (adjT k)
    rw [permLen_adjT] at hle2
    omega
  have hrun : ∀ {k : Fin (N - 1)}, permLen (σ * adjT k) + 1 = permLen σ →
      ∃ s : RunPerm N z, s.1 = c.1 * adjT k := by
    intro k hk
    have hL := hleft hk
    have hlek : WeakOrder.of (c.1 * adjT k) ≤ WeakOrder.of v.1 := by
      rw [WeakOrder.le_def]
      simp only [WeakOrder.perm_of]
      rw [show (c.1 * adjT k)⁻¹ * v.1 = adjT k * σ from by
        rw [mul_inv_rev, adjT_inv, mul_assoc, ← hσdef], hup hk]
      omega
    obtain ⟨s, hs⟩ := (runDescents N z).exists_of_le _ le_rfl hlek
    exact ⟨s, hs⟩
  obtain ⟨Q, hQ⟩ := exists_pairQ hz hij (ascent_of_permLen_mul_adjT (hup hLi))
    (ascent_of_permLen_mul_adjT (hup hLj)) (hrun hLi) (hrun hLj)
  have hE : dimSum (pairChain N e.idx e'.idx hij).dims = N := dimSum_pairChain hij
  have hdeg : degree (pairChain N e.idx e'.idx hij) = 2 := degree_pairChain hij
  have hcone : ∀ k : Fin (N - 1), crossPerm (dimSum_replicate N) (mergeOnes N k) = 1 :=
    fun k => crossPerm_eq_one_of_W _ (W_mergeOnes N k)
  -- the legs, over the base: each reaches one of the two runs below the top
  have hQc : runMerge (pairChain N e.idx e'.idx hij) hE ≫ Q = c.arr := base_run hE Q hQ
  have hleg : ∀ {k : Fin (N - 1)} {w : RunPerm N z}
      {wk : zObj (atomComp N k) ⟶ pairChain N e.idx e'.idx hij},
      crossPerm (dimSum_atomComp N k) wk = σ * adjT k → w.1 = v.1 * adjT k →
      mergeOnes N k ≫ (wk ≫ Q) = w.arr ∧ atomOnes N k ≫ (wk ≫ Q) = v.arr := by
    intro k w wk hwk hw
    refine ⟨leg_run hE Q hQ wk hwk (mergeOnes N k) (hcone k) ?_,
      leg_run hE Q hQ wk hwk (atomOnes N k) (crossPerm_atomOnes N k) ?_⟩
    · rw [mul_one, ← mul_assoc, hcσv]; exact hw.symm
    · rw [← mul_assoc, mul_adjT_adjT, hcσv]
  obtain ⟨hbi, hvi⟩ := hleg hwi e.perm_eq'
  obtain ⟨hbj, hvj⟩ := hleg hwj e'.perm_eq'
  -- the legs cross, so each is a climb of atoms
  have hsmall : 2 ≤ permLen σ := by
    by_contra hc
    have hi0 : σ * adjT e.idx = 1 := eq_one_of_permLen_eq_zero _ (by omega)
    have hj0 : σ * adjT e'.idx = 1 := eq_one_of_permLen_eq_zero _ (by omega)
    exact hij (congrArg Fin.val (adjT_injective (mul_left_cancel (hi0.trans hj0.symm))))
  have hnW : ∀ {k : Fin (N - 1)} {wk : zObj (atomComp N k) ⟶ pairChain N e.idx e'.idx hij},
      crossPerm (dimSum_atomComp N k) wk = σ * adjT k →
      permLen (σ * adjT k) + 1 = permLen σ → ¬ W Zbp wk := by
    intro k wk hwk hk hWk
    have h0 := (W_iff_crossPerm_eq_one (dimSum_atomComp N k) wk).mp hWk
    rw [hwk] at h0
    have h1 := congrArg permLen h0
    rw [permLen_one] at h1
    omega
  obtain ⟨R, hR⟩ := exists_climb_midCut hE Q hdeg (hnW hwi hLi) hQc hbi
  obtain ⟨R', hR'⟩ := exists_climb_midCut hE Q hdeg (hnW hwj hLj) hQc hbj
  -- and the cell of the pair chain closes the diamond
  have hsq : atomOnes N e'.idx ≫ wj = atomOnes N e.idx ≫ wi :=
    (atom_pair_eq (by rw [hwi, hwj, mul_adjT_adjT, mul_adjT_adjT])).symm
  have hcell := atRun_midCut_pair Q hdeg hsq hcap (Y := runObj v)
    (eltRep_pairChain hE Q hQc) (eltRep_legChain (wi ≫ Q) hbi) (eltRep_legChain (wj ≫ Q) hbj)
    (congrArg (eltRestrict z) hvi)
  refine ⟨R, R', ?_⟩
  rw [Web.ev_cons, Web.ev_cons, runWeb_arr, runWeb_arr, ev_eq_climbArr, ev_eq_climbArr, ← hR, ← hR',
    subArr_ascAtom_eq_legAtom e (hom_ext_of_crossPerm (h := dimSum_atomComp N e.idx)
        ((crossPerm_ascLeg e).trans ((crossPerm_leg_comp hE Q hQ wi hwi).trans
          (by rw [← mul_assoc, hcσv]; exact e.perm_eq'.symm)).symm))
      (X := runObj b) (Y := runObj v) (eltRep_legChain (wi ≫ Q) hbi)
      (congrArg (eltRestrict z) hvi) rfl rfl,
    subArr_ascAtom_eq_legAtom e' (hom_ext_of_crossPerm (h := dimSum_atomComp N e'.idx)
        ((crossPerm_ascLeg e').trans ((crossPerm_leg_comp hE Q hQ wj hwj).trans
          (by rw [← mul_assoc, hcσv]; exact e'.perm_eq'.symm)).symm))
      (X := runObj b') (Y := runObj v) (eltRep_legChain (wj ≫ Q) hbj)
      (congrArg (eltRestrict z) hvj) rfl rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact hcell

/-- **The arrow a climb over a chain spells** — Matsumoto, so it does not see which climb. -/
noncomputable def webArrow (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (h : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm b)) :
    subObj a ⟶ subObj b := (runWeb hz).arrow h

theorem climbArr_eq_arrow (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) : climbArr R = webArrow hz R.le :=
  (ev_eq_climbArr hz R).symm.trans (Web.ev_eq_arrow (isArtin_runWeb hz) R)

theorem runArrow_refl (hz : dimSum (shOf z).dims = N) {a : RunPerm N z}
    (h : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm a)) :
    webArrow hz h = 𝟙 (subObj a) := Web.arrow_refl (isArtin_runWeb hz) h

theorem runArrow_comp (hz : dimSum (shOf z).dims = N) {a b c : RunPerm N z}
    (h₁ : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm b))
    (h₂ : WeakOrder.of ((runDescents N z).perm b) ≤ WeakOrder.of ((runDescents N z).perm c)) :
    webArrow hz h₁ ≫ webArrow hz h₂ = webArrow hz (h₁.trans h₂) :=
  Web.arrow_comp (isArtin_runWeb hz) h₁ h₂

/-! ## The 0-cell and the run a word of bead cuts reaches

A letter restricts the element its source carries, so a word restricts along the refinement it
performs — and the run over the word's coarse end that the fine end's own merge names is the run the
word climbs to. -/

/-- **A bead cut is the cut of its own base map** — the lift carries no extra data. -/
theorem eq_cutGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    e = cutGen (Cut.genHom e.1) (Cut.codim_genHom e.1) (map_cutHom e) :=
  Subtype.ext (Subtype.ext rfl)

/-- **The element a word of bead cuts restricts.** -/
theorem map_ev {u : (chCutPoly K).V} : ∀ {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v),
    (wedgeHoms K).map (Cut.ev ((chProj K).mapPath w)).op u.2 = v.as.2
  | _, .nil => by rw [Prefunctor.mapPath_nil, Cut.ev_nil, op_id, Functor.map_id_apply]
  | _, .cons w e =>
      (congrArg ((wedgeHoms K).map (Cut.genHom e.1).op) (map_ev w)).trans (map_cutHom e)

theorem eltRestrict_ev {u : (chCutPoly K).V} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) :
    eltRestrict u (Cut.ev ((chProj K).mapPath w)) = v.as :=
  congrArg (fun s => (⟨shOf v.as, s⟩ : (chCutPoly K).V)) (map_ev w)

/-- A run-arrow read at itself is the run it names. -/
@[simp] theorem runOf_arr {M : ℕ} {c : (chCutPoly K).V} (σ : RunPerm M c) : runOf σ.arr = σ :=
  Subtype.ext σ.crossPerm_arr

theorem arr_runBot {M : ℕ} (c : (chCutPoly K).V) (hc : dimSum (shOf c).dims = M) :
    (runBot c hc).arr = runMerge (shOf c) hc := arr_runOf _

/-- The run a word of bead cuts reaches, read over its coarse end. -/
noncomputable def wordPerm {u : (chCutPoly K).V} {M : ℕ} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) (hv : dimSum (shOf v.as).dims = M) : RunPerm M u :=
  runOf (runMerge (shOf v.as) hv ≫ Cut.ev ((chProj K).mapPath w))

theorem eltRep_wordPerm {u : (chCutPoly K).V} {M : ℕ} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) (hv : dimSum (shOf v.as).dims = M) :
    eltRep v.as = (runObj (wordPerm w hv)).1 :=
  (congrArg eltRep (eltRestrict_ev w)).symm.trans
    (eltRep_pairChain hv (Cut.ev ((chProj K).mapPath w)) (arr_runOf _).symm)

/-- **A cut lengthens the run it reaches by its own crossings** — so the run below it is climbed
to. -/
theorem runPerm_le_of_cut {u : (chCutPoly K).V} {M : ℕ} {d b : Ch Zbp} (t : d ⟶ shOf u)
    (hd : dimSum d.dims = M) (hb : dimSum b.dims = M) (f : b ⟶ d) {σ₀ σ : RunPerm M u}
    (hσ₀ : runMerge d hd ≫ t = σ₀.arr) (hσ : runMerge b hb ≫ f ≫ t = σ.arr) :
    WeakOrder.of ((runDescents M u).perm σ₀) ≤ WeakOrder.of ((runDescents M u).perm σ) := by
  have h₀ := val_eq_crossPerm t hd hσ₀
  have h₁ := val_eq_crossPerm (f ≫ t) hb hσ
  rw [runDescents_perm, runDescents_perm]
  refine WeakOrder.le_of_mul_eq (π := crossPerm hb f) ?_ ?_
  · rw [h₁, crossPerm_comp hb f t, h₀]
  · rw [h₁, permLen_crossPerm_comp hb f t, h₀]

/-- **The web arrow over a chain is the one over anything it refines.** -/
theorem webArrow_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hu : dimSum (shOf u).dims = M) (hd : dimSum d.dims = M)
    {a b : RunPerm M (eltRestrict u t)}
    (h : WeakOrder.of ((runDescents M (eltRestrict u t)).perm a)
      ≤ WeakOrder.of ((runDescents M (eltRestrict u t)).perm b))
    (h' : WeakOrder.of ((runDescents M u).perm (pushPerm t a))
      ≤ WeakOrder.of ((runDescents M u).perm (pushPerm t b))) :
    webArrow hu h'
      = eqToHom (subObj_pushPerm t a) ≫ webArrow hd h ≫ eqToHom (subObj_pushPerm t b).symm := by
  obtain ⟨R⟩ := (runDescents M (eltRestrict u t)).nonempty_climb' h
  refine Eq.trans (climbArr_eq_arrow hu (pushClimb t hd R)).symm ?_
  exact (climbArr_push t hd R).trans (sandwich_congr _ _ (climbArr_eq_arrow hd R))

/-! ## A 1-cell is the web arrow to the run of its target

`subArr_eq_climbArr` reads a 1-cell whose cut does not start at a run as its own climb; a 1-cell
whose cut *does* start at a run cuts an atom's cell (`exists_atomComp`) and is the atom there
(`eq_atomOnes`), so its climb is the single ascent across that atom. -/

/-- **A 1-cell whose cut does not start at a run is the web arrow its climb spells.** -/
theorem subArr_eq_arrow {A B : (chCollapse K).V} (g : (chCollapse K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) (hg : ¬ RunCut g)
    (p : subPt A = subObj (runBot g.dom hM)) (q : subObj (genTopAt g hM) = subPt B) :
    subArr g = eqToHom p ≫ webArrow hM (runBot_le hM (genTopAt g hM)) ≫ eqToHom q := by
  subst hM
  exact (subArr_eq_climbArr g hg).trans
    (sandwich_congr _ _ (climbArr_eq_arrow rfl (genClimb g)))

/-! ## A bead cut over a base, read at the runs of its two ends -/

/-- The 1-cell of the collapse a non-merge bead cut over a base becomes. -/
noncomputable def cutCell {u : (chCutPoly K).V} {d b : Ch Zbp} (t : d ⟶ shOf u) {f : b ⟶ d}
    (hf : codim f = 1) (hnW : ¬ W Zbp f) :
    (chCollapse K).Gen ⟨eltRep (eltRestrict u t), eltRep_idem _⟩
      ⟨eltRep (eltRestrict u (f ≫ t)), eltRep_idem _⟩ :=
  (chCollapse K).genCell
    (Polygraph.cell (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl))
    (fun hm => hnW ((merge_iff f).mp hm).1)

theorem cutArr_cutCell {u : (chCutPoly K).V} {d b : Ch Zbp} (t : d ⟶ shOf u) {f : b ⟶ d}
    (hf : codim f = 1) (hnW : ¬ W Zbp f) :
    cutArr (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl)
      = subArr (cutCell t hf hnW) :=
  cutArr_gen (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl)
    (fun hm => hnW ((merge_iff f).mp hm).1)

/-- **A bead cut over a base, read at the runs of its two ends, is the web arrow between them** — a
merge names a renaming, an atom out of a run names itself, and any other cut its own climb pushed
onto the base. -/
theorem atRun_cutRestrict {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {d : Ch Zbp} (t : d ⟶ shOf u) (hd : dimSum d.dims = M)
    {b : Ch Zbp} (hb : dimSum b.dims = M) {f : b ⟶ d} (hf : codim f = 1)
    {σ₀ σ : RunPerm M u} (hσ₀ : runMerge d hd ≫ t = σ₀.arr)
    (hσ : runMerge b hb ≫ f ≫ t = σ.arr)
    (hA : eltRep (eltRestrict u t) = (runObj σ₀).1)
    (hB : eltRep (eltRestrict u (f ≫ t)) = (runObj σ).1)
    (hle : WeakOrder.of ((runDescents M u).perm σ₀)
      ≤ WeakOrder.of ((runDescents M u).perm σ)) :
    atRun hA hB (cutArr (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl))
      = webArrow hu hle := by
  by_cases hW : W Zbp f
  · -- a merge: the two runs agree, and the cut names a renaming
    have hpick : chCutPicked K
        (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl) :=
      (merge_iff f).mpr ⟨hW, hf⟩
    have harr : σ₀.arr = σ.arr :=
      hσ₀.symm.trans ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
        (eq_of_W ((W Zbp).comp_mem _ _ (W_runMerge b hb) hW) (W_runMerge d hd))).symm.trans hσ)
    obtain rfl : σ₀ = σ := Subtype.ext (σ₀.crossPerm_arr.symm.trans
      ((congrArg (crossPerm (dimSum_replicate M)) harr).trans σ.crossPerm_arr))
    rw [cutArr_merge _ hpick ((subPt_eq hA).trans (subPt_eq hB).symm),
      atRun_eqToHom hA hB _ (rfl : runObj σ₀ = runObj σ₀), runArrow_refl hu hle]
    exact eqToHom_refl _ _
  · by_cases hg : eltRep (eltRestrict u (f ≫ t)) = eltRestrict u (f ≫ t)
    · -- the cut starts at a run: it is the atom at the cell its source names
      obtain rfl : b = zObj (𝟙^M) := shOf_eq_ones_of_eltRep hg hb
      obtain ⟨k, rfl⟩ := exists_atomComp f hf
      obtain rfl : f = atomOnes M k := eq_atomOnes hW
      have hval₀ := val_eq_crossPerm t hd hσ₀
      have hcomp := val_eq_crossPerm (atomOnes M k ≫ t) hb hσ
      have hval : σ.1 = σ₀.1 * adjT k := by
        rw [hcomp, crossPerm_comp hb (atomOnes M k) t, crossPerm_atomOnes, hval₀]
      have hlen : permLen (σ₀.1 * adjT k) = permLen σ₀.1 + 1 := by
        rw [← hval, hcomp, permLen_crossPerm_comp hb (atomOnes M k) t,
          crossPerm_atomOnes, permLen_adjT, hval₀]
        omega
      have hleg : ascLeg (⟨k, ascent_of_permLen_mul_adjT hlen, hval⟩ :
          Ascent (runDescents M u).perm σ₀ σ) = t :=
        hom_ext_of_crossPerm (h := dimSum_atomComp M k) (by
          rw [crossPerm_ascLeg]; exact hval₀)
      have hsand := subArr_ascAtom_eq_legAtom
        (⟨k, ascent_of_permLen_mul_adjT hlen, hval⟩ : Ascent (runDescents M u).perm σ₀ σ) hleg
        (X := runObj σ₀) (Y := runObj σ) hA ((eltRep_eq_self rfl).symm.trans hB) rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsand
      refine Eq.trans (atRun_topCut t hA hB) ?_
      refine Eq.trans hsand.symm ?_
      exact (Category.id_comp _).symm.trans (climbArr_eq_arrow hu (Climb.nil.cons
        (⟨k, ascent_of_permLen_mul_adjT hlen, hval⟩ : Ascent (runDescents M u).perm σ₀ σ)))
    · -- any other cut: its own climb over its source, pushed onto the base
      have h₀ : pushPerm t (runBot (eltRestrict u t) hd) = σ₀ :=
        (congrArg runOf ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
          (arr_runBot (eltRestrict u t) hd)).trans hσ₀)).trans (runOf_arr σ₀)
      have h₁ : pushPerm t (genTopAt (cutCell t hf hW) hd) = σ :=
        (congrArg runOf ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
          (arr_genTopAt (cutCell t hf hW) hd)).trans hσ)).trans (runOf_arr σ)
      subst h₀
      subst h₁
      refine Eq.trans (congrArg (atRun hA hB) ((cutArr_cutCell t hf hW).trans
        (subArr_eq_arrow (cutCell t hf hW) hd hg
          (subObj_runBot_gen (cutCell t hf hW) hd) (subObj_genTopAt (cutCell t hf hW) hd)))) ?_
      refine Eq.trans ?_ (webArrow_push t hu hd
        (runBot_le (z := eltRestrict u t) hd (genTopAt (cutCell t hf hW) hd)) hle).symm
      exact eqToHom_nest _ _ _ _ _ _

/-- …and at any naming of the element its source carries. -/
theorem atRun_cutGen {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {d : Ch Zbp} (t : d ⟶ shOf u) (hd : dimSum d.dims = M)
    {x : (wedgeHoms K).obj (op d)} (hx : (wedgeHoms K).map t.op u.2 = x)
    {b : Ch Zbp} (hb : dimSum b.dims = M) {f : b ⟶ d} (hf : codim f = 1)
    {y : (wedgeHoms K).obj (op b)} (hy : (wedgeHoms K).map f.op x = y)
    {σ₀ σ : RunPerm M u} (hσ₀ : runMerge d hd ≫ t = σ₀.arr)
    (hσ : runMerge b hb ≫ f ≫ t = σ.arr)
    (hA : eltRep (⟨d, x⟩ : (chCutPoly K).V) = (runObj σ₀).1)
    (hB : eltRep (⟨b, y⟩ : (chCutPoly K).V) = (runObj σ).1)
    (hle : WeakOrder.of ((runDescents M u).perm σ₀)
      ≤ WeakOrder.of ((runDescents M u).perm σ)) :
    atRun hA hB (cutArr (cutGen f hf hy)) = webArrow hu hle := by
  subst hx
  subst hy
  exact atRun_cutRestrict hu t hd hb hf hσ₀ hσ hA hB hle

/-! ## The word a refinement spells, independent of the word

`atRun_cutGen` makes each letter a web arrow, so a word is the web arrow to the run its refinement
reaches — and that run sees only the refinement. -/

theorem readCut_cons {a m v : GenObj (chCutPoly K).Gen} (w : Quiver.Path a m) (e : m ⟶ v) :
    (readCut K).map (w.cons e) = (readCut K).map w ≫ cutArr e :=
  (readCut K).map_comp w e.toPath

/-- **A word of bead cuts is the web arrow to the run its refinement reaches.** -/
theorem atRun_readCut {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {v : GenObj (chCutPoly K).Gen} (w : Quiver.Path ((chCutPoly K).pt u) v) :
    ∀ (hv : dimSum (shOf v.as).dims = M) {σ : RunPerm M u}
      (_hσ : runMerge (shOf v.as) hv ≫ Cut.ev ((chProj K).mapPath w) = σ.arr)
      (hA : eltRep u = (runObj (runBot u hu)).1) (hB : eltRep v.as = (runObj σ).1),
      atRun hA hB ((readCut K).map w) = webArrow hu (runBot_le hu σ) := by
  induction w with
  | nil =>
      intro hv σ hσ hA hB
      have hWσ : W Zbp σ.arr := by
        rw [← hσ]
        exact (W Zbp).comp_mem _ _ (W_runMerge (shOf u) hv) (MorphismProperty.id_mem _ _)
      obtain rfl : σ = runBot u hu := Subtype.ext (σ.crossPerm_arr.symm.trans
        ((crossPerm_eq_one_of_W _ hWσ).trans (runBot_val u hu).symm))
      rw [runArrow_refl hu (runBot_le hu (runBot u hu)),
        show (readCut K).map (Quiver.Path.nil :
            Quiver.Path ((chCutPoly K).pt u) ((chCutPoly K).pt u)) = 𝟙 _ from
          (readCut K).map_id _]
      exact (atRun_eqToHom hA hB rfl rfl).trans (eqToHom_refl _ _)
  | @cons m v w e ih =>
      intro hv σ hσ hA hB
      have hm : dimSum (shOf m.as).dims = M :=
        (dimSum_eq_of_hom (Cut.genHom e.1)).symm.trans hv
      have hσ₀ : runMerge (shOf m.as) hm ≫ Cut.ev ((chProj K).mapPath w)
          = (wordPerm w hm).arr := (arr_runOf _).symm
      have hstep := runPerm_le_of_cut (Cut.ev ((chProj K).mapPath w)) hm hv
        (Cut.genHom e.1) hσ₀ hσ
      rw [readCut_cons w e, atRun_comp hA (eltRep_wordPerm w hm) hB,
        ih hm hσ₀ hA (eltRep_wordPerm w hm),
        show atRun (eltRep_wordPerm w hm) hB (cutArr e) = webArrow hu hstep from
          Eq.trans (congrArg (atRun (eltRep_wordPerm w hm) hB) (congrArg cutArr (eq_cutGen e)))
            (atRun_cutGen hu (Cut.ev ((chProj K).mapPath w)) hm (map_ev w) hv
              (Cut.codim_genHom e.1) (map_cutHom e) hσ₀ hσ (eltRep_wordPerm w hm) hB hstep)]
      exact runArrow_comp hu (runBot_le hu (wordPerm w hm)) hstep

/-- Cancelling a renaming against its inverse, on either side of an arrow. -/
private theorem sandwich_cancel {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    (f : A ⟶ B) : eqToHom p ≫ (eqToHom p.symm ≫ f ≫ eqToHom q) ≫ eqToHom q.symm = f := by
  subst p; subst q; simp

theorem atRun_injective {A B : (chCollapse K).V} {z₁ z₂ : (chCutPoly K).V}
    (hA : eltRep z₁ = A.1) (hB : eltRep z₂ = B.1)
    {f f' : (readCut K).obj ((chCutPoly K).pt z₁) ⟶ (readCut K).obj ((chCutPoly K).pt z₂)}
    (h : atRun hA hB f = atRun hA hB f') : f = f' :=
  (sandwich_cancel (subPt_eq hA) (subPt_eq hB) f).symm.trans
    ((congrArg (fun s => eqToHom (subPt_eq hA) ≫ s ≫ eqToHom (subPt_eq hB).symm) h).trans
      (sandwich_cancel (subPt_eq hA) (subPt_eq hB) f'))

/-- **Two words of bead cuts with the same value read alike** — they climb to one run, and
Matsumoto does not see which climb. -/
theorem readCut_congr {u : (chCutPoly K).V} {v : GenObj (chCutPoly K).Gen}
    {w w' : Quiver.Path ((chCutPoly K).pt u) v}
    (h : Cut.ev ((chProj K).mapPath w) = Cut.ev ((chProj K).mapPath w')) :
    (readCut K).map w = (readCut K).map w' := by
  have hu : dimSum (shOf u).dims = dimSum (shOf u).dims := rfl
  have hv : dimSum (shOf v.as).dims = dimSum (shOf u).dims :=
    dimSum_eq_of_hom (Cut.ev ((chProj K).mapPath w))
  refine atRun_injective ((runObj_runBot u hu).symm) (eltRep_wordPerm w hv) ?_
  refine Eq.trans (atRun_readCut hu w hv (arr_runOf _).symm _ (eltRep_wordPerm w hv)) ?_
  exact (atRun_readCut hu w' hv (by rw [← h]; exact (arr_runOf _).symm) _
    (eltRep_wordPerm w hv)).symm

end ChainCat
