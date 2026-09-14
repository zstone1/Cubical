import CubeChains.Concurrency.Presentation.PaperPoly

/-!
# Concurrency/Presentation/PaperPresents — bead cuts, read on the paper's cells

`readCut` spells a word of bead cuts in atoms out of the runs and reads each atom as the degree-one
object it lands on.  A codimension-two cut out of a run compares two two-letter words whose letters
lift to its two one-cut factorisations:

    run ──cut──▸ ▪ ──cut──▸ obj        two factorisations, one degree-two object

That cut is a degree-two object's, and each factorisation is one of the two words the object reads,
so the object's own 2-cell equates them — which is `Paper.readCut_cell`.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-! ## The reading -/

/-- A word of the contraction, spelled in atoms and read on the paper's cells. -/
noncomputable def atomWords (K : BPSet) : (chCollapse K).poly.Word ⥤ (Paper.poly K).Word :=
  runAtomWords K ⋙ Paper.runPre.pathsFunctor

/-- …and a word of bead cuts, through the contraction. -/
noncomputable def readWords (K : BPSet) : (chCutPoly K).Word ⥤ (Paper.poly K).Word :=
  (chCollapse K).words ⋙ atomWords K

/-- The arrow a word of the contraction names on the paper's cells. -/
noncomputable def readColl (K : BPSet) : (chCollapse K).poly.Word ⥤ (Paper.poly K).presented :=
  atomWords K ⋙ (Paper.poly K).quot

/-- **…and the arrow a word of bead cuts names.** -/
noncomputable def readCut (K : BPSet) : (chCutPoly K).Word ⥤ (Paper.poly K).presented :=
  readWords K ⋙ (Paper.poly K).quot

namespace Paper

/-- A kept cut is the degree-one object it lands on. -/
@[simp] theorem obj_genOfRunCut {U V : (chCollapse K).V} (g : (chCollapse K).Gen U V)
    (hg : RunCut g) : (genOfRunCut g hg).obj = vChain g.dom :=
  cellCongr_const (F := Cell 1) Cell.obj _ _ _

/-! ## The 2-cells: a degree-two object carries the cell of its greatest refinement

A degree-two object's greatest refinement has codimension two, so `oneCutEquivBool` names its two
one-cut factorisations, and the two of them *are* a 2-cell of the lifted cut polygraph.  That cell
is kept: its cut is the object's greatest refinement, read at the base (`isTop_zHom`). -/

/-- A cell's refinement, factored in two at the boundary the boolean names. -/
noncomputable def cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) : OneCut α.hom :=
  (oneCutEquivBool α.hom α.codim_hom).symm ε

theorem comp_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    (cellFactor α ε).1.fst ≫ (cellFactor α ε).1.snd = α.hom := (cellFactor α ε).1.comp

theorem codim_fst_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    codim (cellFactor α ε).1.fst = 1 := (cellFactor α ε).2

theorem codim_snd_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    codim (cellFactor α ε).1.snd = 1 := (cellFactor α ε).codim_snd α.codim_hom

/-- The bead cut a codimension-one refinement is, as a 1-cell of the lifted cut polygraph. -/
noncomputable def cutGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (chCutPoly K).Gen (chV d) (chV c) := cutGen (baseMap u) hu u.w

/-! ## The boundaries agree, letter by letter

`cutWord` *is* the contraction's own word for the bead cut, read on the runs — that is how it is
defined — so the comparison of boundaries is the same statement one letter at a time. -/

/-- **A merge is picked** — it is one of the 1-cells the localization inverts. -/
theorem chCutPicked_cutGenOf {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : W K u) :
    chCutPicked K (cutGenOf u hu) :=
  (merge_iff (baseMap u)).mpr ⟨(W_baseHom_iff (a := chV c) (b := chV d) u).mpr hW, hu⟩

/-- **…and any other cut is not.** -/
theorem not_chCutPicked_cutGenOf {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u) :
    ¬ chCutPicked K (cutGenOf u hu) := fun hm =>
  hW ((W_baseHom_iff (a := chV c) (b := chV d) u).mp ((merge_iff (baseMap u)).mp hm).1)

/-! ## The word a cut reads, letter by letter

`cutWord` is spelled on the shape alone: the letter at a cut out of a run, and otherwise the climb
`shapeClimb` picks.  The contraction spells the same cut on the *same* climb — its runs are its
shape's — so the two words agree letter by letter, which is `atomWords_cell`. -/

/-- A 1-cell, read as a one-letter word. -/
noncomputable abbrev genWord {X Y : Run K} (α : Gen X Y) : Quiver.Path (runPt X) (runPt Y) :=
  (Polygraph.cell (P := poly K) α).toPath

/-- **A letter is its object**, read at other names for its two ends. -/
theorem genWord_congr {X Y X' Y' : Run K} (hx : X = X') (hy : Y = Y')
    {α : Gen X Y} {β : Gen X' Y'} (h : α.obj = β.obj) :
    readAt hx hy (genWord α) = genWord β := by
  subst hx; subst hy
  exact congrArg (fun γ : Gen X Y => genWord γ) (Cell.ext h)

theorem readAt_cons {X Y Z X' Y' Z' : Run K} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (p : Quiver.Path (runPt X) (runPt Y)) {L : Gen Y Z} {L' : Gen Y' Z'} (hL : L.obj = L'.obj) :
    readAt hx hz (p.cons L) = (readAt hx hy p).cons L' := by
  subst hx; subst hy; subst hz
  exact congrArg (fun M : Gen Y Z => p.cons M) (Cell.ext hL)

theorem readAt_trans {X Y X' Y' X'' Y'' : Run K} (hx : X = X') (hy : Y = Y') (hx' : X' = X'')
    (hy' : Y' = Y'') (p : Quiver.Path (runPt X) (runPt Y)) :
    readAt hx' hy' (readAt hx hy p) = readAt (hx.trans hx') (hy.trans hy') p := by
  subst hx; subst hy; subst hx'; subst hy'; rfl

/-- **A cut out of a run reads as one letter** — the object it lands on. -/
theorem cutWord_of_run {X : Run K} {e : Ch K} (he : degree e = 1) {u : X.chain ⟶ e}
    (hu : codim u = 1) (hW : ¬ W K u) :
    cutWord u hu = readAt rfl (bottomRun_self X).symm (genWord (genOfHom he hW)) := by
  rw [cutWord, dif_neg hW, dif_pos X.property]
  rfl

/-- **A chain with a bead is not a run.** -/
theorem not_isRun_of_degree_ne_zero {c : Ch K} (hc : degree c ≠ 0) : ¬ IsRun K c :=
  fun h => hc ((isRun_iff_degree_eq_zero c).mp h)

/-- **A cut that does not start at a run reads as its climb.** -/
theorem cutWord_eq_climbWord {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u)
    (hc : ¬ IsRun K c) :
    cutWord u hu
      = readAt (bottomRun_eq_shapeRun d).symm (shapeRun_cutTop u) (cutClimbWord u) := by
  rw [cutWord, dif_neg hW, dif_neg hc]

/-- **A kept atom, read on the runs, is the paper's letter for the same ascent** — both are the
object the atom's leg lands on. -/
theorem runPre_ascAtom {e : Ch K} {a b : ChPerm e} (ε : ChAsc e a b) :
    runPre.map (keptCell (P := (chCollapse K).poly) RunCut (ascAtom (z := chV e) ε)
      (runCut_ascAtom (z := chV e) ε)) = ascGen e ε := by
  refine Cell.ext ?_
  have h1 : (genOfRunCut (ascAtom (z := chV e) ε) (runCut_ascAtom (z := chV e) ε)).obj
      = vChain (ascAtom (z := chV e) ε).dom :=
    obj_genOfRunCut (ascAtom (z := chV e) ε) (runCut_ascAtom (z := chV e) ε)
  have h2 : vChain (ascAtom (z := chV e) ε).dom = (ascGen e ε).obj := rfl
  exact h1.trans h2

/-- **…so a climb, read on the runs, is the word the paper spells for it.** -/
theorem runPre_climbPath {e : Ch K} {a : ChPerm e} : ∀ {b : ChPerm e}
    (R : Climb (shapeDescents (dimSum e.dims) (zObj e.dims)).perm a b),
    runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut (climbPath (z := chV e) R)
      (all_climbPath (z := chV e) R)) = climbGenWord e R
  | _, .nil => rfl
  | _, .cons R ε => by
      change (runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut
          (climbPath (z := chV e) R) (all_climbPath (z := chV e) R))).cons
            (runPre.map (keptCell (P := (chCollapse K).poly) RunCut (ascAtom (z := chV e) ε)
              (runCut_ascAtom (z := chV e) ε)))
        = (climbGenWord e R).cons (ascGen e ε)
      rw [runPre_climbPath R, runPre_ascAtom ε]
      rfl

private theorem keptWord_cellCongr {P : Polygraph} {T : ∀ {a b : P.V}, P.Gen a b → Prop}
    {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y') (w : Quiver.Path x y)
    (hw : Quiver.Path.All (fun ⦃_ _⦄ e => T e) w)
    (hw' : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (cellCongr Quiver.Path hx hy w)) :
    keptWord T (cellCongr Quiver.Path hx hy w) hw'
      = cellCongr Quiver.Path (congrArg (fun z : GenObj P.Gen => (⟨z.as⟩ : GenObj (keptGen T))) hx)
          (congrArg (fun z : GenObj P.Gen => (⟨z.as⟩ : GenObj (keptGen T))) hy)
          (keptWord T w hw) := by
  subst hx; subst hy; rfl

/-- **A 1-cell's climb is the paper's climb for the cut it performs** — both are the shape's own,
and the shape sees neither the element over it nor which polygraph reads it.

`rfl` in one step sends `isDefEq` into `Classical.choice`; the two steps below do not. -/
theorem genClimb_eq_cutClimb {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) (hW : ¬ W K u) :
    genClimb (chGenOf u hu hW) = cutClimb u := by
  have h1 : genClimb (chGenOf u hu hW)
      = shapeClimb (N := vCount (chGenOf u hu hW).dom) (shOf (chGenOf u hu hW).dom) rfl
          (genTop (chGenOf u hu hW)) := rfl
  have h2 : shapeClimb (N := vCount (chGenOf u hu hW).dom) (shOf (chGenOf u hu hW).dom) rfl
        (genTop (chGenOf u hu hW))
      = shapeClimb (N := dimSum d.dims) (zObj d.dims) rfl (cutTop u) := rfl
  exact h1.trans h2

/-- **The contraction's word for a bead cut, read on the runs, is `cutWord`** — a merge reads as the
empty word on either side, a cut out of a run as its own letter, and any other cut as the climb both
spell. -/
theorem atomWords_cell {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (atomWords K).map ((chCollapse K).cell (Polygraph.cell (cutGenOf u hu))) = cutWord u hu := by
  by_cases hW : W K u
  · rw [(chCollapse K).cell_of_S
      (Polygraph.cell (cutGenOf u hu))
      (chCutPicked_cutGenOf hu hW), cutWord, dif_pos hW]
    exact (congrArg runPre.mapPath
        (Paths.map_cellCongr_hom (runAtomWords K) rfl _ Quiver.Path.nil)).trans
      (Prefunctor.mapPath_cellCongr runPre rfl _ Quiver.Path.nil)
  · rw [(chCollapse K).cell_of_not_S
      (Polygraph.cell (cutGenOf u hu))
      (not_chCutPicked_cutGenOf hu hW)]
    refine Eq.trans (congrArg runPre.mapPath (Paths.lift_toPath _ _)) ?_
    change runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut
      (runCellWord (chGenOf u hu hW)) (all_runCellWord (chGenOf u hu hW))) = cutWord u hu
    by_cases hrc : RunCut (chGenOf u hu hW)
    · have hc : IsRun K c := (eltRep_eq_self_iff_isRun (chV c)).mp hrc
      rw [keptWord_congr _ (runCellWord_self (chGenOf u hu hW) hrc) _
          (Quiver.Path.all_toPath.mpr hrc), keptWord_toPath _ _ hrc,
        cutWord_of_run (degree_eq_one_of_isRun hc hu) (X := ⟨c, hc⟩) hu hW]
      refine Eq.trans (Prefunctor.mapPath_toPath runPre _) ?_
      exact (genWord_congr rfl (bottomRun_self (⟨c, hc⟩ : Run K)).symm
        (obj_genOfRunCut (chGenOf u hu hW) hrc).symm).symm
    · have hc : ¬ IsRun K c := fun h => hrc ((eltRep_eq_self_iff_isRun (chV c)).mpr h)
      have e1 : runCellWord (chGenOf u hu hW)
          = cellCongr Quiver.Path
              (congrArg (chCollapse K).poly.pt (Subtype.ext (runObj_runBot_gen (chGenOf u hu hW))))
              (congrArg (chCollapse K).poly.pt (Subtype.ext (runObj_genTop (chGenOf u hu hW))))
              (climbPath (genClimb (chGenOf u hu hW))) := dif_neg hrc
      rw [cutWord_eq_climbWord hu hW hc, keptWord_congr _ e1 _
        ((Quiver.Path.all_cellCongr _ _ _).mpr (all_climbPath (genClimb (chGenOf u hu hW))))]
      refine Eq.trans (congrArg runPre.mapPath (keptWord_cellCongr _ _ _
        (all_climbPath (genClimb (chGenOf u hu hW))) _)) ?_
      refine Eq.trans (Prefunctor.mapPath_cellCongr runPre _ _ _) ?_
      rw [cutClimbWord, ← genClimb_eq_cutClimb u hu hW]
      exact congrArg (readAt _ _) (runPre_climbPath (e := d) (genClimb (chGenOf u hu hW)))

/-- **A letter's reading is `cutWord`.** -/
theorem readWords_toPath {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (readWords K).map (Polygraph.cell (cutGenOf u hu)).toPath = cutWord u hu :=
  (congrArg (atomWords K).map
      (Paths.lift_toPath (chCollapse K).pre (Polygraph.cell (cutGenOf u hu)))).trans
    (atomWords_cell u hu)

/-! ## A letter, read back as a refinement

A bead cut of the lifted polygraph lifts to a refinement of `Ch K` (`chCutHom`), and that
refinement's own cut is the letter again — up to the renaming `chV (vChain a) = a`, which crossing
permutations do not see. -/

@[simp] theorem baseHom_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    baseHom (chCutHom e) = Cut.genHom e.1 := rfl

/-- **Renaming a letter's ends conjugates the cut it performs.** -/
theorem genHom_cellCongr {a a' b b' : (chCutPoly K).V} (ha : a = a') (hb : b = b')
    (e : (chCutPoly K).Gen a b) :
    Cut.genHom (cellCongr (chCutPoly K).Gen ha hb e).1
      = eqToHom (congrArg shOf hb).symm ≫ Cut.genHom e.1 ≫ eqToHom (congrArg shOf ha) := by
  subst ha; subst hb
  rw [cellCongr_self (chCutPoly K).Gen]
  simp

/-- **A letter is the cut of its own lift** — both crossings are the letter's, and a refinement of
`Ch Zbp` is its crossing permutation. -/
theorem cutGenOf_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    cutGenOf (chCutHom e) (codim_chCutHom e)
      = cellCongr (chCutPoly K).Gen (chV_vChain a).symm (chV_vChain b).symm e := by
  have hmap : Cut.genHom (cutGenOf (chCutHom e) (codim_chCutHom e)).1
      = Cut.genHom (cellCongr (chCutPoly K).Gen (chV_vChain a).symm (chV_vChain b).symm e).1 := by
    rw [genHom_cellCongr]
    refine hom_ext_of_crossPerm (h := rfl) ?_
    rw [crossPerm_comp, crossPerm_comp, crossPerm_eq_one_of_W _ (W_eqToHom _),
      crossPerm_eq_one_of_W _ (W_eqToHom _), mul_one, one_mul]
    exact crossPerm_eq_of_φ _ rfl
  exact Subtype.ext (Subtype.ext hmap)

/-! ## A greatest cut out of a run is a degree-two object's

Codimension two out of a run is degree two, and the greatest refinement comes out of the run
`topOf` names — so the cut *is* a cell's, and each of its two one-cut factorisations is one of the
two words the cell reads. -/

/-- **The degree-two object a greatest codimension-two cut out of a run names.** -/
noncomputable def cellOfCut {X : Run K} {e : Ch K} (f : X.chain ⟶ e) (hf : codim f = 2)
    (hmax : IsTop f) : Cell 2 (bottomRun e) X where
  obj := e
  degree_obj := by
    have h := degree_eq_add_codim f
    rw [(isRun_iff_degree_eq_zero _).mp X.property, hf] at h
    simpa using h
  below := rfl
  top := hmax.fst_eq

/-- **…and that object's refinement is the cut** — there is only one greatest refinement out of a
run. -/
theorem hom_cellOfCut {X : Run K} {e : Ch K} (f : X.chain ⟶ e) (hf : codim f = 2)
    (hmax : IsTop f) : (cellOfCut f hf hmax).hom = f :=
  IsTop.hom_eq (isTop_hom _) hmax

/-- Which factorisation a word spells matters, which proofs name its codimensions does not. -/
private theorem factorWord_congr {X : Run K} {b : Ch K} {f : X.chain ⟶ b} (hf : codim f = 2)
    {F G : OneCut f} (h : F = G) :
    readAt rfl (bottomRun_self X)
        ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))
      = readAt rfl (bottomRun_self X)
        ((cutWord G.1.snd (G.codim_snd hf)).comp (cutWord G.1.fst G.2)) := by
  subst h; rfl

/-- **Each one-cut factorisation of a cell's refinement is one of the two sides it reads.** -/
theorem exists_bool_cellWords {X Y : Run K} (α : Cell 2 X Y) (F : OneCut α.hom) :
    ∃ ε : Bool, cellWords α ε
      = cellCongr Quiver.Path (congrArg runPt α.below) (congrArg runPt (bottomRun_self Y))
        ((cutWord F.1.snd (F.codim_snd α.codim_hom)).comp (cutWord F.1.fst F.2)) := by
  refine ⟨oneCutEquivBool α.hom α.codim_hom F, ?_⟩
  have h1 : cellWords α (oneCutEquivBool α.hom α.codim_hom F)
      = readAt α.below rfl (readAt rfl (bottomRun_self Y)
        ((cutWord F.1.snd (F.codim_snd α.codim_hom)).comp (cutWord F.1.fst F.2))) :=
    congrArg (readAt α.below rfl)
      (factorWord_congr α.codim_hom ((oneCutEquivBool α.hom α.codim_hom).symm_apply_apply F))
  rw [h1, readAt, readAt, cellCongr_trans]

/-- **Renaming a letter's ends renames its reading.** -/
theorem readCut_cellCongr {a a' b b' : (chCutPoly K).V} (ha : a = a') (hb : b = b')
    (e : (chCutPoly K).Gen a b) :
    (readCut K).map (Polygraph.cell (cellCongr (chCutPoly K).Gen ha hb e)).toPath
      = eqToHom (congrArg (fun z : (chCutPoly K).V => (readCut K).obj ((chCutPoly K).pt z))
            ha).symm
        ≫ (readCut K).map (Polygraph.cell e).toPath
        ≫ eqToHom (congrArg (fun z : (chCutPoly K).V => (readCut K).obj ((chCutPoly K).pt z))
            hb) := by
  subst ha; subst hb
  rw [cellCongr_self (chCutPoly K).Gen]
  simp

/-- **A letter's reading is the paper's word for the refinement it lifts to**, the renaming of the
two ends being absorbed by the quotient. -/
theorem quot_cutWord_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (poly K).quot.map (cutWord (chCutHom e) (codim_chCutHom e))
      = eqToHom (congrArg (fun z : (chCutPoly K).V => (readCut K).obj ((chCutPoly K).pt z))
            (chV_vChain a).symm).symm
        ≫ (readCut K).map (Polygraph.cell e).toPath
        ≫ eqToHom (congrArg (fun z : (chCutPoly K).V => (readCut K).obj ((chCutPoly K).pt z))
            (chV_vChain b).symm) := by
  rw [← readWords_toPath (chCutHom e) (codim_chCutHom e), cutGenOf_chCutHom]
  exact readCut_cellCongr _ _ e

/-- The 0-cell a letter's end names, read on the runs: the run below the chain it sits over. -/
theorem readPt_eq_bottomRun (z : (chCutPoly K).V) :
    (readCut K).obj ((chCutPoly K).pt z) = (poly K).quot.obj (runPt (bottomRun (vChain z))) :=
  congrArg (poly K).quot.obj (congrArg runPt (bottomRun_runOfV z).symm)

/-- …and at a run it is that run. -/
theorem readPt_eq_runOfV {z : (chCutPoly K).V} (h : eltRep z = z) :
    (readCut K).obj ((chCutPoly K).pt z) = (poly K).quot.obj (runPt (runOfV ⟨z, h⟩)) :=
  congrArg (poly K).quot.obj (congrArg runPt (congrArg runOfV (Subtype.ext h)))

private theorem eqToHom_move {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : g = eqToHom p.symm ≫ f ≫ eqToHom q) :
    f = eqToHom p ≫ g ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h.symm

@[inherit_doc quot_cutWord_chCutHom]
theorem readCut_letter {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (readCut K).map (Polygraph.cell e).toPath
      = eqToHom (readPt_eq_bottomRun a)
        ≫ (poly K).quot.map (cutWord (chCutHom e) (codim_chCutHom e))
        ≫ eqToHom (readPt_eq_bottomRun b).symm :=
  eqToHom_move _ _ (quot_cutWord_chCutHom e)

/-- **A kept cell's side, read on the runs, is one of the two words its object reads** — the letters
lift to the factorisation's two legs, and the cell is the object's. -/
theorem exists_bool_readCut {x y m : GenObj (chCutPoly K).Gen} (hrun : eltRep y.as = y.as)
    {f : (runOfV ⟨y.as, hrun⟩).chain ⟶ vChain x.as} (hf : codim f = 2) (hmax : IsTop f)
    (p : x ⟶ m) (q : m ⟶ y) (hcomp : chCutHom q ≫ chCutHom p = f) :
    ∃ ε : Bool,
      (readCut K).map ((Quiver.Path.nil.cons (Polygraph.cell p)).cons (Polygraph.cell q))
        = eqToHom (readPt_eq_bottomRun x.as)
          ≫ (poly K).quot.map (cellWords (cellOfCut f hf hmax) ε)
          ≫ eqToHom (readPt_eq_runOfV hrun).symm := by
  obtain ⟨ε, hε⟩ := exists_bool_cellWords (cellOfCut f hf hmax)
    ⟨⟨vChain m.as, chCutHom q, chCutHom p, hcomp.trans (hom_cellOfCut f hf hmax).symm⟩,
      codim_chCutHom q⟩
  refine ⟨ε, ?_⟩
  have hsplit : (readCut K).map ((Quiver.Path.nil.cons
        (Polygraph.cell p)).cons (Polygraph.cell q))
      = (readCut K).map (Polygraph.cell p).toPath
        ≫ (readCut K).map (Polygraph.cell q).toPath :=
    (readCut K).map_comp (Polygraph.cell p).toPath (Polygraph.cell q).toPath
  have hε' : cellWords (cellOfCut f hf hmax) ε
      = cellCongr Quiver.Path rfl
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))
        ((cutWord (chCutHom p) (codim_chCutHom p)).comp
          (cutWord (chCutHom q) (codim_chCutHom q))) := hε
  have hrhs : (poly K).quot.map (cellCongr Quiver.Path rfl
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))
        ((cutWord (chCutHom p) (codim_chCutHom p)).comp (cutWord (chCutHom q) (codim_chCutHom q))))
      = ((poly K).quot.map (cutWord (chCutHom p) (codim_chCutHom p))
          ≫ (poly K).quot.map (cutWord (chCutHom q) (codim_chCutHom q)))
        ≫ eqToHom (congrArg (poly K).quot.obj
            (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))) :=
    (Paths.map_cellCongr (poly K).quot _ _).trans
      (congrArg (fun t => t ≫ eqToHom (congrArg (poly K).quot.obj
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))))
        ((poly K).quot.map_comp _ _))
  rw [hsplit, readCut_letter, readCut_letter,
    show (poly K).quot.map (cellWords (cellOfCut f hf hmax) ε)
        = ((poly K).quot.map (cutWord (chCutHom p) (codim_chCutHom p))
            ≫ (poly K).quot.map (cutWord (chCutHom q) (codim_chCutHom q)))
          ≫ eqToHom (congrArg (poly K).quot.obj
              (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))) from
      (congrArg (poly K).quot.map hε').trans hrhs]
  simp

/-! ## Every kept cell's two sides agree

A kept cell compares two two-letter words whose letters lift to two factorisations of one greatest
cut out of a run.  That cut is a degree-two object's, and each factorisation is one of the two words
the object reads — so the object's own 2-cell equates them, whichever way round they came. -/

/-- A word of length two is its two letters. -/
theorem exists_two_of_length_eq_two {V : Type*} [Quiver V] :
    ∀ {x y : V} (w : Quiver.Path x y), w.length = 2 →
      ∃ (m : V) (p : x ⟶ m) (q : m ⟶ y), w = (Quiver.Path.nil.cons p).cons q
  | _, _, .nil, h => by simp at h
  | _, _, .cons .nil _, h => by simp at h
  | _, _, .cons (.cons .nil p) q, _ => ⟨_, p, q, rfl⟩
  | _, _, .cons (.cons (.cons _ _) _) _, h => by simp at h

/-- **The cut a two-letter word performs is its two letters' lifts, composed.** -/
theorem baseHom_chCutHom_comp {x m y : GenObj (chCutPoly K).Gen} (p : x ⟶ m) (q : m ⟶ y) :
    baseHom (chCutHom q ≫ chCutHom p)
      = Cut.ev ((chProj K).mapPath ((Quiver.Path.nil.cons p).cons q)) := by
  rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, Prefunctor.mapPath_nil, Cut.ev_cons,
    Cut.ev_cons, Cut.ev_nil, Category.comp_id, baseHom_comp, baseHom_chCutHom, baseHom_chCutHom]
  exact rfl

/-- **A 2-cell whose cut is greatest out of a run holds on the paper's cells** — each side is one of
the two words the object of that cut reads, and that object's own 2-cell equates them. -/
theorem readCut_cell {x y : GenObj (chCutPoly K).Gen} (γ : (chCutPoly K).Rel x y)
    (hmax : IsTop (Cut.ev γ.cell.src)) :
    (readCut K).map ((chCutPoly K).src γ) = (readCut K).map ((chCutPoly K).tgt γ) := by
  have hrun : eltRep y.as = y.as := (eltRep_eq_self_iff_isRun y.as).mpr hmax.1
  obtain ⟨ms, p, q, hsrc⟩ := exists_two_of_length_eq_two γ.src
    ((Prefunctor.length_mapPath (chProj K) γ.src).symm.trans
      ((congrArg Quiver.Path.length γ.src_eq).trans γ.cell.src_length))
  obtain ⟨mt, p', q', htgt⟩ := exists_two_of_length_eq_two γ.tgt
    ((Prefunctor.length_mapPath (chProj K) γ.tgt).symm.trans
      ((congrArg Quiver.Path.length γ.tgt_eq).trans γ.cell.tgt_length))
  have hbs : baseHom (chCutHom q ≫ chCutHom p) = Cut.ev γ.cell.src :=
    (baseHom_chCutHom_comp p q).trans
      (congrArg Cut.ev ((congrArg (chProj K).mapPath hsrc).symm.trans γ.src_eq))
  have hbt : baseHom (chCutHom q' ≫ chCutHom p') = Cut.ev γ.cell.tgt :=
    (baseHom_chCutHom_comp p' q').trans
      (congrArg Cut.ev ((congrArg (chProj K).mapPath htgt).symm.trans γ.tgt_eq))
  have hff : chCutHom q' ≫ chCutHom p' = chCutHom q ≫ chCutHom p :=
    hom_ext_baseHom (by rw [hbs, hbt, γ.cell.ev_eq])
  have hf : codim (chCutHom q ≫ chCutHom p) = 2 := by
    have h := codim_comp (chCutHom q) (chCutHom p)
    rw [codim_chCutHom, codim_chCutHom] at h
    omega
  have hmax' : IsTop (chCutHom q ≫ chCutHom p) := by
    refine (isTop_iff_zHom (X := runOfV ⟨y.as, hrun⟩) _).mpr ?_
    have heq : zHom (Hom.φ (chCutHom q ≫ chCutHom p)) = Cut.ev γ.cell.src :=
      hom_ext' (congrArg Hom.φ hbs)
    exact heq ▸ hmax
  obtain ⟨ε, hE⟩ := exists_bool_readCut hrun hf hmax' p q rfl
  obtain ⟨ε', hE'⟩ := exists_bool_readCut hrun hf hmax' p' q' hff
  have hsrc' : (chCutPoly K).src γ
      = (Quiver.Path.nil.cons (Polygraph.cell p)).cons
        (Polygraph.cell q) :=
    hsrc
  have htgt' : (chCutPoly K).tgt γ
      = (Quiver.Path.nil.cons (Polygraph.cell p')).cons
        (Polygraph.cell q') :=
    htgt
  have hrel := quot_cellWords
    (cellOfCut (X := runOfV ⟨y.as, hrun⟩) (e := vChain x.as) (chCutHom q ≫ chCutHom p) hf hmax')
  rw [hsrc', htgt']
  refine hE.trans (Eq.trans ?_ hE'.symm)
  refine congrArg (fun t => eqToHom (readPt_eq_bottomRun x.as)
    ≫ t ≫ eqToHom (readPt_eq_runOfV hrun).symm) ?_
  cases ε <;> cases ε' <;> first | rfl | exact hrel | exact hrel.symm

end Paper

end ChainCat
