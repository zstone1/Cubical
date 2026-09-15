import CubeChains.Concurrency.Presentation.TopRefinement
import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Machinery.Braid.MatsumotoCat

/-!
# Concurrency/Presentation/RunAtoms — the atoms out of the runs

Over a chain `z` of `Ch K` the runs form a lower set of the right weak order (`runLower`), an
adjacent ascent is an atom out of a run (`ascAtom`), and a climb is a word of such atoms:

    run r ──atom k──▸ ▪ ◂──atom l── run r'        two climbs, one arrow

`runCellWord` spells every 1-cell of the contraction in atoms — itself when its cut already starts
at a run, and the climb out of its source's own run otherwise.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-! ## The runs over a shape

A run-arrow into a shape is pinned by its crossing permutation, so the runs index the permutations
they realise faithfully, and the arrow is recovered from the permutation.  Only the shape is seen,
never the element over it: that is what lets the paper's own words be spelled without the cut
polygraph, and makes a 0-cell's climb its shape's. -/

/-- A crossing permutation some run-arrow into a shape realises. -/
def ShapePerm (N : ℕ) (s : Ch Zbp) : Type :=
  {σ : Perm (Fin N) // ∃ r : zObj (𝟙^N) ⟶ s, crossPerm (dimSum_replicate N) r = σ}

namespace ShapePerm

variable {N : ℕ} {s : Ch Zbp}

/-- The run-arrow a realised permutation names. -/
noncomputable def arr (σ : ShapePerm N s) : zObj (𝟙^N) ⟶ s := σ.2.choose

@[simp] theorem crossPerm_arr (σ : ShapePerm N s) :
    crossPerm (dimSum_replicate N) σ.arr = σ.1 := σ.2.choose_spec

/-- **A run-arrow is pinned by its crossing permutation.** -/
theorem eq_arr (σ : ShapePerm N s) {r : zObj (𝟙^N) ⟶ s}
    (hr : crossPerm (dimSum_replicate N) r = σ.1) : r = σ.arr :=
  hom_ext_of_crossPerm (hr.trans (σ.crossPerm_arr).symm)

theorem strands (σ : ShapePerm N s) : dimSum s.dims = N := dimSum_eq_of_onesHom σ.arr

end ShapePerm

/-- The run a map out of a run names. -/
def runOf {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) : ShapePerm N s :=
  ⟨crossPerm (dimSum_replicate N) r, ⟨r, rfl⟩⟩

@[simp] theorem runOf_val {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) :
    (runOf r).1 = crossPerm (dimSum_replicate N) r := rfl

@[simp] theorem arr_runOf {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) :
    (runOf r).arr = r := ((runOf r).eq_arr rfl).symm

/-- **The runs over a shape are a lower set of the right weak order** — `exists_run_mul_adjT` is the
exchange, so every cover below a run is realised, and a run-arrow is its permutation. -/
noncomputable def shapeLower (N : ℕ) (s : Ch Zbp) : WeakOrder.Lower N (ShapePerm N s) where
  perm := Subtype.val
  perm_inj := Subtype.val_injective
  isLowerSet := WeakOrder.isLowerSet_of_covBy (by
    rintro x _ hcov ⟨σ, rfl⟩
    obtain ⟨k, hd, hx⟩ := WeakOrder.covBy_iff.mp hcov
    simp only [WeakOrder.perm_of] at hd hx
    obtain ⟨r, hr⟩ := exists_run_mul_adjT σ.strands σ.arr (by simpa using hd)
    refine ⟨runOf r, congrArg WeakOrder.of ?_⟩
    rw [runOf_val, hr, σ.crossPerm_arr]
    exact hx.symm)

@[simp] theorem shapeLower_perm (N : ℕ) (s : Ch Zbp) (σ : ShapePerm N s) :
    (shapeLower N s).perm σ = σ.1 := rfl

/-- The run a shape is merged into from. -/
noncomputable def shapeBot {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    ShapePerm N s := runOf (runMerge s hs)

@[simp] theorem shapeBot_val {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    (shapeBot s hs).1 = 1 := crossPerm_eq_one_of_W _ (W_runMerge _ _)

/-- **Every run is climbed to from the merge run.** -/
theorem shapeBot_le {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N)
    (σ : ShapePerm N s) : WeakOrder.of ((shapeLower N s).perm (shapeBot s hs))
      ≤ WeakOrder.of ((shapeLower N s).perm σ) := by
  rw [shapeLower_perm, shapeLower_perm, shapeBot_val]
  exact WeakOrder.le_of_mul_eq (one_mul σ.1) (by rw [permLen_one, Nat.add_zero])

theorem W_shapeBot_arr {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) :
    W Zbp ((shapeBot s hs).arr) := by
  have h : (shapeBot s hs).arr = runMerge s hs := arr_runOf _
  rw [h]
  exact W_runMerge _ _

/-- **The chosen climb from a shape's merge run up to one of its runs.** -/
noncomputable def shapeClimb {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N)
    (σ : ShapePerm N s) : Climb (shapeLower N s).perm (shapeBot s hs) σ :=
  ((shapeLower N s).nonempty_climb (shapeBot_le hs σ)).some

/-! ### An ascent is an atom out of a run

At an ascent the run-arrow below factors through the `k`-th atom shape and the one above crosses it
(`exists_atom_step`), so the leg is a chain of atom shape over the shape. -/

section Asc

variable {N : ℕ} {s : Ch Zbp}

/-- The leg an ascent crosses: the atom shape at its index, over the shape. -/
noncomputable def ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    zObj (atomComp N e.idx) ⟶ s :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose

theorem mergeOnes_ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    mergeOnes N e.idx ≫ ascLeg e = a.arr :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.1

theorem crossPerm_atomOnes_ascLeg {a b : ShapePerm N s}
    (e : Ascent (shapeLower N s).perm a b) :
    crossPerm (dimSum_replicate N) (atomOnes N e.idx ≫ ascLeg e) = a.1 * adjT e.idx :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.2

theorem atomOnes_ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    atomOnes N e.idx ≫ ascLeg e = b.arr :=
  b.eq_arr ((crossPerm_atomOnes_ascLeg e).trans e.perm_eq.symm)

end Asc

/-! ## …read at a 0-cell of the cut polygraph

A 0-cell is its shape carrying an element, and the runs see only the shape. -/

/-- A crossing permutation some run-arrow into a chain realises. -/
abbrev RunPerm (N : ℕ) (z : (chCutPoly K).V) : Type := ShapePerm N (shOf z)

/-- **The runs over a chain are a lower set of the right weak order.** -/
noncomputable abbrev runLower (N : ℕ) (z : (chCutPoly K).V) : WeakOrder.Lower N (RunPerm N z) :=
  shapeLower N (shOf z)

/-- The run a chain is merged into from. -/
noncomputable abbrev runBot {N : ℕ} (z : (chCutPoly K).V) (hz : dimSum (shOf z).dims = N) :
    RunPerm N z := shapeBot (shOf z) hz

/-! ## The 0-cell a run names -/

/-- The 0-cell of the contracted polygraph a run over a chain names. -/
noncomputable def runObj {N : ℕ} {z : (chCutPoly K).V} (σ : RunPerm N z) :
    (chCollapse K).V := ⟨eltRestrict z σ.arr, eltRep_eq_self rfl⟩

theorem runObj_runBot {N : ℕ} (z : (chCutPoly K).V) (hz : dimSum (shOf z).dims = N) :
    (runObj (runBot z hz)).1 = eltRep z := by
  refine Eq.trans (congrArg (eltRestrict z) (arr_runOf (runMerge (shOf z) hz))) ?_
  exact eltRestrict_eq_of_W z (congrArg (fun n => zObj (𝟙^n)) hz.symm)
    (W_runMerge _ _) (W_zRunMerge (shOf z))

/-- The refinement a leg into a chain is, carrying the restricted element. -/
noncomputable def legLift {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    vChain (eltRestrict z w) ⟶ vChain z := liftOf w rfl

@[simp] theorem baseHom_legLift {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    baseHom (legLift w) = w := rfl

theorem W_legLift {z : (chCutPoly K).V} {p : Ch Zbp} {w : p ⟶ shOf z} (hw : W Zbp w) :
    W K (legLift w) := (W_baseHom_iff _).mp hw

/-! ## A bead cut out of a run, as a 1-cell of the contraction -/

/-- A bead cut, acting on the element its source carries. -/
def cutGen {c c' : (chCutPoly K).V} (f : shOf c' ⟶ shOf c) (hf : codim f = 1)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) : (chCutPoly K).Gen c c' :=
  ⟨⟨f, hf⟩, (congrArg (fun g => (wedgeHoms K).map g c.2) (zCutPresentation_arrow _)).trans hres⟩

/-- **A bead cut out of a run**, as a 1-cell of the contraction: the cut merges nothing, and its
target is the run on its own events. -/
noncomputable def runGen {c c' : (chCutPoly K).V} {N : ℕ} (hc' : shOf c' = zObj (𝟙^N))
    (f : shOf c' ⟶ shOf c) (hf : codim f = 1) (hnW : ¬ W Zbp f)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) {X Y : (chCollapse K).V}
    (hX : eltRep c = X.1) (hY : c' = Y.1) : (chCollapse K).Gen X Y where
  dom := c
  cod := c'
  gen := cutGen f hf hres
  not_mem := fun hm => hnW ((merge_iff f).mp hm).1
  rep_dom := hX
  rep_cod := (eltRep_eq_self hc').trans hY

/-! ## An ascent is an atom out of a run

At an ascent the run-arrow below factors through the `k`-th atom shape and the one above crosses it
(`exists_atom_step`), so the leg is a chain of atom shape over the base and the atom's cut is
`atomOnes` — with no transport, the shapes being what `eltRestrict` records. -/

/-- **The run of a chain of atom shape** — the atom's own merge reaches it. -/
theorem eltRep_eltRestrict_atom {N : ℕ} {k : Fin (N - 1)} {z : (chCutPoly K).V}
    (w : zObj (atomComp N k) ⟶ shOf z) :
    eltRep (eltRestrict z w) = eltRestrict z (mergeOnes N k ≫ w) :=
  (eltRestrict_eq_of_W (eltRestrict z w)
      (congrArg (fun n => zObj (𝟙^n)) (dimSum_atomComp N k)) (W_zRunMerge _)
      (W_mergeOnes N k)).trans (eltRestrict_comp z w (mergeOnes N k))

variable {N : ℕ} {z : (chCutPoly K).V}

/-- **The `k`-th atom over a leg into a chain** — restricting twice is restricting along the
composite, so this is also the atom over the same leg read into anything the chain refines. -/
noncomputable def legAtom {k : Fin (N - 1)} (w : zObj (atomComp N k) ⟶ shOf z)
    {X Y : (chCollapse K).V} (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRestrict z (atomOnes N k ≫ w) = Y.1) : (chCollapse K).Gen X Y :=
  runGen rfl (atomOnes N k) (codim_atomOnes N k) (not_W_atomOnes N k)
    (map_op_comp w (atomOnes N k) z.2) hX hY

theorem map_mergeOnes_ascLeg {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    (wedgeHoms K).map (mergeOnes N e.idx).op (eltRestrict z (ascLeg e)).2
      = (eltRestrict z a.arr).2 :=
  (map_op_comp (ascLeg e) (mergeOnes N e.idx) z.2).trans
    (congrArg (fun t : zObj (𝟙^N) ⟶ shOf z => (wedgeHoms K).map t.op z.2) (mergeOnes_ascLeg e))

theorem eltRep_ascLeg {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    eltRep (eltRestrict z (ascLeg e)) = (runObj a).1 :=
  (eltRep_eltRestrict_atom (ascLeg e)).trans (congrArg (eltRestrict z) (mergeOnes_ascLeg e))

/-- **The atom an ascent names** — the `k`-th cut out of the run below it. -/
noncomputable def ascAtom {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    (chCollapse K).Gen (runObj a) (runObj b) :=
  legAtom (ascLeg e) (eltRep_ascLeg e) (congrArg (eltRestrict z) (atomOnes_ascLeg e))

theorem runCut_ascAtom {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    RunCut (ascAtom e) := eltRep_eq_self rfl

/-- **The atoms out of the runs over a chain, as a prefunctor on the ascent quiver** — a climb's
word of atoms is its `mapPath`. -/
noncomputable def atomPre : Ascents (runLower N z).perm ⥤q GenObj (chCollapse K).poly.Gen where
  obj σ := (chCollapse K).poly.pt (runObj σ)
  map e := Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)

theorem all_atomPath {a b : RunPerm N z} (R : Climb (runLower N z).perm a b) :
    Quiver.Path.All (fun ⦃_ _⦄ g => RunCut g) (atomPre.mapPath R) := by
  induction R with
  | nil => exact Quiver.Path.all_nil _
  | cons R e ih => exact (Quiver.Path.all_cons_iff _ _).mpr ⟨ih, runCut_ascAtom e⟩

/-! ## The two legs out of an ascent's atom shape

One is a merge and one is the atom itself, and both land on the base — which is what lets a climb
telescope into the single refinement it performs. -/

/-- The atom's own cut, as a refinement of `Ch K`. -/
noncomputable def ascCut {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    vChain (eltRestrict z (atomOnes N e.idx ≫ ascLeg e)) ⟶ vChain (eltRestrict z (ascLeg e)) :=
  liftOf (atomOnes N e.idx) (map_op_comp (ascLeg e) (atomOnes N e.idx) z.2)

/-- …and its merge leg. -/
noncomputable def ascMerge {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    vChain (eltRestrict z a.arr) ⟶ vChain (eltRestrict z (ascLeg e)) :=
  liftOf (mergeOnes N e.idx) (map_mergeOnes_ascLeg e)

theorem W_ascMerge {a b : RunPerm N z} (e : Ascent (runLower N z).perm a b) :
    W K (ascMerge e) :=
  (W_baseHom_iff _).mp (by rw [ascMerge, baseHom_liftOf]; exact W_mergeOnes N e.idx)

/-! ## The word a 1-cell spells

The climb from the source's own run to the run of the target is a word of atoms performing the same
refinement. -/

variable {X Y : (chCollapse K).V}

/-- The bead cut a 1-cell of the collapse performs. -/
def genCut (g : (chCollapse K).Gen X Y) : shOf g.cod ⟶ shOf g.dom :=
  Cut.genHom g.gen.1

theorem map_genCut (g : (chCollapse K).Gen X Y) :
    (wedgeHoms K).map (genCut g).op g.dom.2 = g.cod.2 := map_cutHom g.gen

/-- The run of a 1-cell's target, read over its source. -/
noncomputable def genTop (g : (chCollapse K).Gen X Y) : RunPerm (vCount g.dom) g.dom :=
  runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)

/-- **Restricting along a merge prefix sees only its shape** — `eq_of_W` pins the merge. -/
theorem eltRestrict_merge_comp {z : (chCutPoly K).V} {c : Ch Zbp} (f : c ⟶ shOf z) {N : ℕ}
    {m : zObj (𝟙^N) ⟶ c} (hm : W Zbp m) {m' : zRep c ⟶ c} (hm' : W Zbp m')
    (hs : zObj (𝟙^N) = zRep c) : eltRestrict z (m ≫ f) = eltRestrict z (m' ≫ f) :=
  (eltRestrict_comp z f m).symm.trans
    ((eltRestrict_eq_of_W (eltRestrict z f) hs hm hm').trans (eltRestrict_comp z f m'))

theorem runObj_genTop (g : (chCollapse K).Gen X Y) : (runObj (genTop g)).1 = Y.1 :=
  (congrArg (eltRestrict g.dom) (arr_runOf _)).trans
    ((eltRestrict_merge_comp (genCut g) (W_runMerge _ _) (W_zRunMerge _)
        (congrArg (fun n => zObj (𝟙^n)) (dimSum_eq_of_hom (genCut g)).symm)).trans
      ((eltRep_eq_eltRestrict g.gen).symm.trans g.rep_cod))

theorem runObj_runBot_gen (g : (chCollapse K).Gen X Y) :
    (runObj (runBot g.dom rfl)).1 = X.1 := (runObj_runBot g.dom rfl).trans g.rep_dom

/-- The climb a 1-cell's word reads. -/
noncomputable def genClimb (g : (chCollapse K).Gen X Y) :
    Climb (runLower (vCount g.dom) g.dom).perm (runBot g.dom rfl) (genTop g) :=
  shapeClimb (shOf g.dom) rfl (genTop g)

/-- **The atom word a 1-cell spells**: itself when its cut starts at a run, and the climb out of the
source's own run otherwise. -/
noncomputable def runCellWord (g : (chCollapse K).Gen X Y) :
    Quiver.Path ((chCollapse K).poly.pt X) ((chCollapse K).poly.pt Y) :=
  @dite _ (RunCut g) (Classical.propDecidable _)
    (fun _ => (Polygraph.cell (P := (chCollapse K).poly) g).toPath)
    (fun _ => cellCongr Quiver.Path
      (congrArg (chCollapse K).poly.pt (Subtype.ext (runObj_runBot_gen g)))
      (congrArg (chCollapse K).poly.pt (Subtype.ext (runObj_genTop g)))
      (atomPre.mapPath (genClimb g)))

theorem all_runCellWord (g : (chCollapse K).Gen X Y) :
    Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) (runCellWord g) := by
  by_cases h : RunCut g
  · rw [runCellWord, dif_pos h]
    exact Quiver.Path.all_toPath.mpr h
  · rw [runCellWord, dif_neg h]
    exact (Quiver.Path.all_cellCongr _ _ _).mpr (all_atomPath (genClimb g))

/-- **A kept 1-cell spells itself.** -/
theorem runCellWord_self (g : (chCollapse K).Gen X Y) (h : RunCut g) :
    runCellWord g = (Polygraph.cell (P := (chCollapse K).poly) g).toPath := by
  rw [runCellWord, dif_pos h]

theorem map_genTopMerge (g : (chCollapse K).Gen X Y) :
    (wedgeHoms K).map (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))).op g.cod.2
      = (eltRestrict g.dom (genTop g).arr).2 := by
  refine Eq.trans (congrArg
    ((wedgeHoms K).map (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))).op)
    (map_genCut g).symm) ?_
  refine Eq.trans (map_op_comp (genCut g)
    (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))) g.dom.2) ?_
  exact congrArg (fun t : zObj (𝟙^(vCount g.dom)) ⟶ shOf g.dom =>
    (wedgeHoms K).map t.op g.dom.2)
    (arr_runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)).symm

/-- The merge onto the target's run, read over the source. -/
noncomputable def genTopMerge (g : (chCollapse K).Gen X Y) :
    vChain (eltRestrict g.dom (genTop g).arr) ⟶ vChain g.cod :=
  liftOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))) (map_genTopMerge g)

theorem W_genTopMerge (g : (chCollapse K).Gen X Y) : W K (genTopMerge g) :=
  (W_baseHom_iff _).mp (by rw [genTopMerge, baseHom_liftOf]; exact W_runMerge _ _)

/-! ## The substitution into atom words -/

/-- The substitution, on a letter. -/
noncomputable abbrev runAtomPre (K : BPSet) :
    GenObj (chCollapse K).poly.Gen ⥤q Paths (GenObj (RunAtom K)) :=
  subPre (P := (chCollapse K).poly) RunCut runCellWord all_runCellWord

/-- …and on whole words. -/
noncomputable abbrev runAtomWords (K : BPSet) :
    (chCollapse K).poly.Word ⥤ Paths (GenObj (RunAtom K)) :=
  Paths.lift (runAtomPre K)

end ChainCat
