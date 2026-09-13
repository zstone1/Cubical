import CubeChains.Concurrency.Presentation.PaperPoly

/-!
# Concurrency/Presentation/PaperPresents — the degree-two cuts, read on the paper's cells

A kept 2-cell of the collapse compares two two-letter words of bead cuts whose letters lift to two
one-cut factorisations of one greatest cut out of a run:

    run ──cut──▸ ▪ ──cut──▸ obj        two factorisations, one degree-two object

That cut is a degree-two object's, and each factorisation is one of the two words the object reads,
so the object's own 2-cell equates them.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

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

/-- **The contraction's word for a bead cut, read on the runs, is `cutWord`** — a merge reads as the
empty word on either side, and any other cut as its own letter. -/
theorem runPre_mapPath_cell {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    runPre.mapPath ((chRunCutSpans K).subWords.map ((chCollapse K).cell
        (Polygraph.cell (cutGenOf u hu))))
      = cutWord u hu := by
  by_cases hW : W K u
  · rw [(chCollapse K).cell_of_S
      (Polygraph.cell (cutGenOf u hu))
      (chCutPicked_cutGenOf hu hW), cutWord, dif_pos hW]
    exact (congrArg runPre.mapPath
        (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) rfl _ Quiver.Path.nil)).trans
      (Prefunctor.mapPath_cellCongr runPre rfl _ Quiver.Path.nil)
  · rw [(chCollapse K).cell_of_not_S
      (Polygraph.cell (cutGenOf u hu))
      (not_chCutPicked_cutGenOf hu hW), cutWord, dif_neg hW]
    exact congrArg runPre.mapPath (Paths.lift_toPath _ _)

/-- The reading of a word of the localized cut polygraph on the runs. -/
noncomputable def readRuns {U V : GenObj (chCutPoly K).Gen} (w : Quiver.Path U V) :
    Quiver.Path (runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj U)))
      (runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj V))) :=
  runPre.mapPath ((chRunCutSpans K).subWords.map ((chCollapse K).words.map w))

/-- **Reading is multiplicative** — three functors in a row. -/
theorem readRuns_cons {U V W : GenObj (chCutPoly K).Gen} (p : Quiver.Path U V) (e : V ⟶ W) :
    readRuns (p.cons e) = (readRuns p).comp (readRuns e.toPath) :=
  (congrArg runPre.mapPath
      ((congrArg (chRunCutSpans K).subWords.map
          ((chCollapse K).words.map_comp p e.toPath)).trans
        ((chRunCutSpans K).subWords.map_comp _ _))).trans
    (Prefunctor.mapPath_comp _ _ _)

theorem readRuns_nil {U : GenObj (chCutPoly K).Gen} :
    readRuns (Quiver.Path.nil : Quiver.Path U U) = Quiver.Path.nil :=
  (congrArg runPre.mapPath
      ((congrArg (chRunCutSpans K).subWords.map ((chCollapse K).words.map_id _)).trans
        ((chRunCutSpans K).subWords.map_id _))).trans (Prefunctor.mapPath_nil _ _)

/-- …so a two-letter word reads as its two letters. -/
theorem readRuns_two {U V W : GenObj (chCutPoly K).Gen} (a : U ⟶ V) (b : V ⟶ W) :
    readRuns ((Quiver.Path.nil.cons a).cons b)
      = (readRuns a.toPath).comp (readRuns b.toPath) := by
  have h1 := readRuns_cons (Quiver.Path.nil.cons a) b
  have h2 := readRuns_cons (Quiver.Path.nil : Quiver.Path U U) a
  rw [h1, h2, readRuns_nil, Quiver.Path.nil_comp]

/-- **A letter's reading is `cutWord`.** -/
theorem readRuns_toPath {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    readRuns (Polygraph.cell (cutGenOf u hu)).toPath
      = cutWord u hu :=
  (congrArg (fun w => runPre.mapPath ((chRunCutSpans K).subWords.map w))
      (Paths.lift_toPath (chCollapse K).pre
        (Polygraph.cell (cutGenOf u hu)))).trans
    (runPre_mapPath_cell u hu)

/-! ## A letter, read back as a refinement

A bead cut of the lifted polygraph lifts to a refinement of `Ch K` (`liftGen`), and that
refinement's own cut is the letter again — up to the renaming `chV (vChain a) = a`, which crossing
permutations do not see. -/

/-- The refinement of `Ch K` a bead cut of the lifted polygraph performs. -/
noncomputable def liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    vChain b ⟶ vChain a := liftOf (Cut.genHom e.1) (map_cutHom e)

@[simp] theorem baseHom_liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    baseHom (liftGen e) = Cut.genHom e.1 := rfl

theorem codim_liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    codim (liftGen e) = 1 := Cut.codim_genHom e.1

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
theorem cutGenOf_liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    cutGenOf (liftGen e) (codim_liftGen e)
      = cellCongr (chCutPoly K).Gen (chV_vChain a).symm (chV_vChain b).symm e := by
  have hmap : Cut.genHom (cutGenOf (liftGen e) (codim_liftGen e)).1
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
theorem readRuns_cellCongr {a a' b b' : (chCutPoly K).V} (ha : a = a') (hb : b = b')
    (e : (chCutPoly K).Gen a b) :
    readRuns (Polygraph.cell
        (cellCongr (chCutPoly K).Gen ha hb e)).toPath
      = cellCongr Quiver.Path
          (congrArg (fun z : (chCutPoly K).V =>
            runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩))) ha)
          (congrArg (fun z : (chCutPoly K).V =>
            runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩))) hb)
          (readRuns (Polygraph.cell e).toPath) :=
  cellCongr_map (F := (chCutPoly K).Gen) (G := Quiver.Path) _
    (fun {_ _} e => readRuns (Polygraph.cell e).toPath) ha hb e

/-- **A letter's reading is the paper's word for the refinement it lifts to**, the renaming of the
two ends being absorbed by the quotient. -/
theorem quot_cutWord_liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (poly K).quot.map (cutWord (liftGen e) (codim_liftGen e))
      = eqToHom (congrArg (poly K).quot.obj
            (congrArg (fun z : (chCutPoly K).V =>
              runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩)))
            (chV_vChain a).symm)).symm
        ≫ (poly K).quot.map
            (readRuns (Polygraph.cell e).toPath)
        ≫ eqToHom (congrArg (poly K).quot.obj
            (congrArg (fun z : (chCutPoly K).V =>
              runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩)))
            (chV_vChain b).symm)) := by
  rw [← readRuns_toPath (liftGen e) (codim_liftGen e), cutGenOf_liftGen, readRuns_cellCongr]
  exact Paths.map_cellCongr₂ (poly K).quot _ _ _

/-- The 0-cell a letter's end names, read on the runs: the run below the chain it sits over. -/
theorem readPt_eq_bottomRun (z : (chCutPoly K).V) :
    runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩))
      = runPt (bottomRun (vChain z)) :=
  congrArg runPt (congrArg runOfV (Subtype.ext (congrArg eltRep (chV_vChain z).symm)))

/-- …and at a run it is that run. -/
theorem readPt_eq_runOfV {z : (chCutPoly K).V} (h : eltRep z = z) :
    runPre.obj ((chRunCutSpans K).pre.obj ((chCollapse K).repObj ⟨z⟩))
      = runPt (runOfV ⟨z, h⟩) :=
  congrArg runPt (congrArg runOfV (Subtype.ext h))

private theorem eqToHom_move {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : g = eqToHom p.symm ≫ f ≫ eqToHom q) :
    f = eqToHom p ≫ g ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h.symm

@[inherit_doc quot_cutWord_liftGen]
theorem quot_readRuns_letter {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (poly K).quot.map (readRuns (Polygraph.cell e).toPath)
      = eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun a))
        ≫ (poly K).quot.map (cutWord (liftGen e) (codim_liftGen e))
        ≫ eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun b)).symm :=
  eqToHom_move _ _ (quot_cutWord_liftGen e)

/-- **A kept cell's side, read on the runs, is one of the two words its object reads** — the letters
lift to the factorisation's two legs, and the cell is the object's. -/
theorem exists_bool_quot_readRuns {x y m : GenObj (chCutPoly K).Gen} (hrun : eltRep y.as = y.as)
    {f : (runOfV ⟨y.as, hrun⟩).chain ⟶ vChain x.as} (hf : codim f = 2) (hmax : IsTop f)
    (p : x ⟶ m) (q : m ⟶ y) (hcomp : liftGen q ≫ liftGen p = f) :
    ∃ ε : Bool,
      (poly K).quot.map (readRuns ((Quiver.Path.nil.cons
          (Polygraph.cell p)).cons
          (Polygraph.cell q)))
        = eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun x.as))
          ≫ (poly K).quot.map (cellWords (cellOfCut f hf hmax) ε)
          ≫ eqToHom (congrArg (poly K).quot.obj (readPt_eq_runOfV hrun)).symm := by
  obtain ⟨ε, hε⟩ := exists_bool_cellWords (cellOfCut f hf hmax)
    ⟨⟨vChain m.as, liftGen q, liftGen p, hcomp.trans (hom_cellOfCut f hf hmax).symm⟩,
      codim_liftGen q⟩
  refine ⟨ε, ?_⟩
  have hsplit : (poly K).quot.map (readRuns ((Quiver.Path.nil.cons
        (Polygraph.cell p)).cons
        (Polygraph.cell q)))
      = (poly K).quot.map (readRuns (Polygraph.cell p).toPath)
        ≫ (poly K).quot.map
          (readRuns (Polygraph.cell q).toPath) :=
    (congrArg (poly K).quot.map (readRuns_two _ _)).trans ((poly K).quot.map_comp _ _)
  have hε' : cellWords (cellOfCut f hf hmax) ε
      = cellCongr Quiver.Path rfl
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))
        ((cutWord (liftGen p) (codim_liftGen p)).comp
          (cutWord (liftGen q) (codim_liftGen q))) := hε
  have hrhs : (poly K).quot.map (cellCongr Quiver.Path rfl
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))
        ((cutWord (liftGen p) (codim_liftGen p)).comp (cutWord (liftGen q) (codim_liftGen q))))
      = ((poly K).quot.map (cutWord (liftGen p) (codim_liftGen p))
          ≫ (poly K).quot.map (cutWord (liftGen q) (codim_liftGen q)))
        ≫ eqToHom (congrArg (poly K).quot.obj
            (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))) :=
    (Paths.map_cellCongr (poly K).quot _ _).trans
      (congrArg (fun t => t ≫ eqToHom (congrArg (poly K).quot.obj
        (congrArg runPt (bottomRun_self (runOfV ⟨y.as, hrun⟩)))))
        ((poly K).quot.map_comp _ _))
  rw [hsplit, quot_readRuns_letter, quot_readRuns_letter,
    show (poly K).quot.map (cellWords (cellOfCut f hf hmax) ε)
        = ((poly K).quot.map (cutWord (liftGen p) (codim_liftGen p))
            ≫ (poly K).quot.map (cutWord (liftGen q) (codim_liftGen q)))
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
theorem baseHom_liftGen_comp {x m y : GenObj (chCutPoly K).Gen} (p : x ⟶ m) (q : m ⟶ y) :
    baseHom (liftGen q ≫ liftGen p)
      = Cut.ev ((chProj K).mapPath ((Quiver.Path.nil.cons p).cons q)) := by
  rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons, Prefunctor.mapPath_nil, Cut.ev_cons,
    Cut.ev_cons, Cut.ev_nil, Category.comp_id, baseHom_comp, baseHom_liftGen, baseHom_liftGen]
  exact rfl

/-- **A kept cell's two sides read alike on the runs** — each is one of the two words the object of
its cut reads, and that object's own 2-cell equates them. -/
theorem quot_readRuns_src_eq_tgt {x y : GenObj (chCutPoly K).Gen} (γ : (chCutPoly K).Rel x y)
    (hmax : IsTop (Cut.ev γ.cell.src)) :
    (poly K).quot.map (readRuns ((chCutPoly K).src γ))
      = (poly K).quot.map (readRuns ((chCutPoly K).tgt γ)) := by
  have hrun : eltRep y.as = y.as := (eltRep_eq_self_iff_isRun y.as).mpr hmax.1
  obtain ⟨ms, p, q, hsrc⟩ := exists_two_of_length_eq_two γ.src
    ((Prefunctor.length_mapPath (chProj K) γ.src).symm.trans
      ((congrArg Quiver.Path.length γ.src_eq).trans γ.cell.src_length))
  obtain ⟨mt, p', q', htgt⟩ := exists_two_of_length_eq_two γ.tgt
    ((Prefunctor.length_mapPath (chProj K) γ.tgt).symm.trans
      ((congrArg Quiver.Path.length γ.tgt_eq).trans γ.cell.tgt_length))
  have hbs : baseHom (liftGen q ≫ liftGen p) = Cut.ev γ.cell.src :=
    (baseHom_liftGen_comp p q).trans
      (congrArg Cut.ev ((congrArg (chProj K).mapPath hsrc).symm.trans γ.src_eq))
  have hbt : baseHom (liftGen q' ≫ liftGen p') = Cut.ev γ.cell.tgt :=
    (baseHom_liftGen_comp p' q').trans
      (congrArg Cut.ev ((congrArg (chProj K).mapPath htgt).symm.trans γ.tgt_eq))
  have hff : liftGen q' ≫ liftGen p' = liftGen q ≫ liftGen p :=
    hom_ext_baseHom (by rw [hbs, hbt, γ.cell.ev_eq])
  have hf : codim (liftGen q ≫ liftGen p) = 2 := by
    have h := codim_comp (liftGen q) (liftGen p)
    rw [codim_liftGen, codim_liftGen] at h
    omega
  have hmax' : IsTop (liftGen q ≫ liftGen p) := by
    have h1 : crossPerm (dimSum_eq_of_hom (liftGen q ≫ liftGen p)) (liftGen q ≫ liftGen p)
        = crossPerm (dimSum_eq_of_hom (Cut.ev γ.cell.src)) (Cut.ev γ.cell.src) :=
      crossPerm_eq_of_φ _ (congrArg ChainCat.Hom.φ hbs)
    exact (isTop_iff_permLen (X := runOfV ⟨y.as, hrun⟩) _).mpr
      ((congrArg permLen h1).trans hmax.permLen_eq)
  obtain ⟨ε, hE⟩ := exists_bool_quot_readRuns hrun hf hmax' p q rfl
  obtain ⟨ε', hE'⟩ := exists_bool_quot_readRuns hrun hf hmax' p' q' hff
  have hsrc' : (chCutPoly K).src γ
      = (Quiver.Path.nil.cons (Polygraph.cell p)).cons
        (Polygraph.cell q) :=
    hsrc
  have htgt' : (chCutPoly K).tgt γ
      = (Quiver.Path.nil.cons (Polygraph.cell p')).cons
        (Polygraph.cell q') :=
    htgt
  have hrel := quot_cellWords
    (cellOfCut (X := runOfV ⟨y.as, hrun⟩) (e := vChain x.as) (liftGen q ≫ liftGen p) hf hmax')
  rw [hsrc', htgt']
  refine hE.trans (Eq.trans ?_ hE'.symm)
  refine congrArg (fun t => eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun x.as))
    ≫ t ≫ eqToHom (congrArg (poly K).quot.obj (readPt_eq_runOfV hrun)).symm) ?_
  cases ε <;> cases ε' <;> first | rfl | exact hrel | exact hrel.symm

/-- **A kept 2-cell's two sides agree** — they are the two words its object reads. -/
theorem quot_readRuns_src_eq_tgt_of_runCutCell {X Y : GenObj (chCollapse K).poly.Gen}
    (α : (chCollapse K).poly.Rel X Y) (hα : RunCutCell α) :
    (poly K).quot.map (readRuns ((chCutPoly K).src α.cell))
      = (poly K).quot.map (readRuns ((chCutPoly K).tgt α.cell)) :=
  quot_readRuns_src_eq_tgt α.cell hα

end ChainCat.Paper
