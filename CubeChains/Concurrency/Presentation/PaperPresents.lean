import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Machinery.Presentation.Bijective

/-!
# Concurrency/Presentation/PaperPresents — the paper's polygraph presents `Ch(K)[W⁻¹]`

`chCellPresentation` presents `Ch(K)[W⁻¹]` on the runs, the kept cuts and the greatest
codimension-two cuts out of a run.  `Paper.poly` presents it on the runs and the **objects** of
degree one and two.  The comparison is one bijection per dimension below two:

    kept cut out of a run ◂───────▸ degree-one object        `genOfRunCut` / its greatest refinement

and in dimension two derivability both ways, the kept cells being ordered pairs of the two
factorisations where a degree-two object carries the pair itself.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The 1-cells are the kept cuts

A kept cut is the degree-one object it lands on, and that object's greatest refinement is the cut
again — at degree one there is no other crossing refinement (`hom_eq_of_not_W_deg_one`). -/

@[simp] theorem obj_genOfRunCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : (genOfRunCut g hg).obj = vChain g.dom :=
  cellCongr_const (F := Cell 1) Cell.obj _ _ _

/-- **A kept cut crosses** — it is not one of the merges the contraction inverts. -/
theorem not_W_genHom_of_not_merged {a b : (chCutPoly K).V} (c : (chCutPoly K).Gen a b)
    (hc : ¬ Cut.merged (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) c)) :
    ¬ W Zbp (Cut.genHom c.1) := fun hW =>
  hc ((merge_iff (Cut.genHom c.1)).mpr ⟨hW, Cut.codim_genHom c.1⟩)

/-- **A kept cut is pinned by the object it lands on** — the cut itself is then forced, there being
only one crossing refinement at degree one. -/
theorem genOfRunCut_injective {U V : (chContraction K).V} :
    Function.Injective
      (fun e : {g : (chContraction K).Gen U V // RunCut g} => genOfRunCut e.1 e.2) := by
  rintro ⟨⟨dom, cod, gen, nm, rd, rc⟩, hg⟩ ⟨⟨dom', cod', gen', nm', rd', rc'⟩, hg'⟩ h
  obtain rfl : cod = V.1 := hg.symm.trans rc
  obtain rfl : cod' = V.1 := hg'.symm.trans rc'
  obtain rfl : dom = dom' := by
    have hobj : vChain dom = vChain dom' :=
      (obj_genOfRunCut _ hg).symm.trans ((congrArg Cell.obj h).trans (obj_genOfRunCut _ hg'))
    exact (chV_vChain dom).symm.trans ((congrArg chV hobj).trans (chV_vChain dom'))
  obtain ⟨c, rfl⟩ : ∃ c, gen = Sum.inl c := by
    rcases gen with c | ⟨c, hc⟩
    · exact ⟨c, rfl⟩
    · exact absurd trivial nm
  obtain ⟨c', rfl⟩ : ∃ c', gen' = Sum.inl c' := by
    rcases gen' with c' | ⟨c', hc'⟩
    · exact ⟨c', rfl⟩
    · exact absurd trivial nm'
  have hrun : ∀ x ∈ (shOf V.1).dims, x = 1 := fun x hx =>
    List.eq_of_mem_replicate
      (congrArg ChainCat.Obj.dims (shOf_eq_ones_of_eltRep hg rfl) ▸ hx)
  have hdeg : degree (shOf dom) = 1 := by
    have h1 := degree_eq_add_codim (Cut.genHom c.1)
    rw [(degree_eq_zero_iff (shOf V.1)).mpr hrun, Cut.codim_genHom c.1] at h1
    simpa using h1
  have hcut : Cut.genHom c.1 = Cut.genHom c'.1 :=
    eq_of_not_W_deg_one hrun hdeg (not_W_genHom_of_not_merged c nm)
      (not_W_genHom_of_not_merged c' nm')
  obtain rfl : c = c' := Subtype.ext (Subtype.ext hcut)
  rfl

/-- **The kept cut a degree-one object is** — its greatest refinement. -/
noncomputable def runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (chContraction K).Gen U V :=
  cellCongr (chContraction K).Gen
    (((runEquiv K).right_inv _).symm.trans
      ((congrArg vOfRun α.below).trans ((runEquiv K).right_inv U)))
    (Subtype.ext ((congrArg eltRep (chV_vChain V.1)).trans V.2))
    (chGenOf α.hom α.codim_hom (α.not_W_hom one_ne_zero))

@[simp] theorem dom_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (runCutOfGen α).dom = chV α.obj :=
  cellCongr_const (F := (chContraction K).Gen) Contraction.Gen.dom _ _ _

@[simp] theorem cod_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (runCutOfGen α).cod = chV (runOfV V).chain :=
  cellCongr_const (F := (chContraction K).Gen) Contraction.Gen.cod _ _ _

theorem runCut_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    RunCut (runCutOfGen α) := by
  change eltRep (runCutOfGen α).cod = (runCutOfGen α).cod
  rw [cod_runCutOfGen]
  exact eltRep_chV (runOfV V)

/-- **…and it lands on that object again**, so the kept cuts and the degree-one objects biject. -/
theorem genOfRunCut_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    genOfRunCut (runCutOfGen α) (runCut_runCutOfGen α) = α :=
  Cell.ext (by rw [obj_genOfRunCut, dom_runCutOfGen, vChain_chV])

theorem genOfRunCut_surjective {U V : (chContraction K).V} :
    Function.Surjective
      (fun e : {g : (chContraction K).Gen U V // RunCut g} => genOfRunCut e.1 e.2) :=
  fun α => ⟨⟨runCutOfGen α, runCut_runCutOfGen α⟩, genOfRunCut_runCutOfGen α⟩

/-- **The kept cuts out of a run are the degree-one objects.** -/
noncomputable def genEquiv (U V : (chContraction K).V) :
    {g : (chContraction K).Gen U V // RunCut g} ≃ Gen (runOfV U) (runOfV V) :=
  Equiv.ofBijective _ ⟨genOfRunCut_injective, genOfRunCut_surjective⟩

@[simp] theorem genEquiv_apply {U V : (chContraction K).V}
    (e : {g : (chContraction K).Gen U V // RunCut g}) :
    genEquiv U V e = genOfRunCut e.1 e.2 := rfl

/-- **The comparison of generating quivers**: a degree-one object is the kept cut it is. -/
noncomputable def paperPre : GenObj (Gen (K := K)) ⥤q GenObj (chRunCutSpans K).poly.Gen where
  obj X := ⟨vOfRun X.as⟩
  map {X Y} α := (genEquiv (vOfRun X.as) (vOfRun Y.as)).symm α

/-- **…and reading it back on the runs is the object again**, with no transport: a run is the run of
the 0-cell it names, on the nose. -/
@[simp] theorem runPre_map_paperPre_map {X Y : GenObj (Gen (K := K))} (α : X ⟶ Y) :
    runPre.map (paperPre.map α) = α :=
  (genEquiv (vOfRun X.as) (vOfRun Y.as)).apply_symm_apply α

theorem runPre_mapPath_paperPre_mapPath : ∀ {X Y : GenObj (Gen (K := K))}
    (w : Quiver.Path X Y), runPre.mapPath (paperPre.mapPath w) = w
  | _, _, .nil => rfl
  | _, _, .cons w e => by
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons,
        runPre_mapPath_paperPre_mapPath w, runPre_map_paperPre_map]
      rfl

/-- **A word of kept cuts is pinned by its reading on the runs** — the comparison is injective in
every dimension below two. -/
theorem runPre_mapPath_injective {x y : GenObj (chRunCutSpans K).poly.Gen} :
    Function.Injective (runPre.mapPath : Quiver.Path x y → _) := by
  haveI : runPre.pathsFunctor.Faithful :=
    Prefunctor.pathsFunctor_faithful runPre fun x => by
      rintro ⟨y₁, e₁⟩ ⟨y₂, e₂⟩ h
      obtain ⟨hy, he⟩ := Sigma.mk.inj_iff.mp h
      obtain rfl : y₁ = y₂ :=
        GenObj.ext ((runEquiv K).symm.injective (congrArg GenObj.as hy))
      exact Sigma.ext rfl (heq_of_eq (genOfRunCut_injective (eq_of_heq he)))
  exact fun {u v} h => runPre.pathsFunctor.map_injective h

/-! ## The 2-cells: a degree-two object carries the cell of its greatest refinement

A degree-two object's greatest refinement has codimension two, so `oneCutEquivBool` names its two
one-cut factorisations, and the two of them *are* a 2-cell of the lifted cut polygraph.  That cell
is kept: its cut is the object's greatest refinement, read at the base (`isTop_zHom`). -/

/-- The bead cut a codimension-one refinement is, as a 1-cell of the lifted cut polygraph. -/
noncomputable def cutGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (chCutPoly K).Gen (chV d) (chV c) := cutGen (baseMap u) hu u.w

@[simp] theorem genHom_cutGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    Cut.genHom (cutGenOf u hu).1 = baseMap u := rfl

/-- A cell's refinement, factored in two at the boundary the boolean names. -/
noncomputable def cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) : OneCut α.hom :=
  (oneCutEquivBool α.hom α.codim_hom).symm ε

theorem comp_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    (cellFactor α ε).1.fst ≫ (cellFactor α ε).1.snd = α.hom := (cellFactor α ε).1.comp

theorem codim_fst_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    codim (cellFactor α ε).1.fst = 1 := (cellFactor α ε).2

theorem codim_snd_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    codim (cellFactor α ε).1.snd = 1 := (cellFactor α ε).codim_snd α.codim_hom

/-- **A factorisation's two cuts compose to the refinement's.** -/
theorem genHom_comp_cutGenOf {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    Cut.genHom (cutGenOf (cellFactor α ε).1.fst (codim_fst_cellFactor α ε)).1
        ≫ Cut.genHom (cutGenOf (cellFactor α ε).1.snd (codim_snd_cellFactor α ε)).1
      = baseMap α.hom :=
  (hom_ext' rfl).trans (congrArg baseMap (comp_cellFactor α ε))

/-- **The two factorisations of a cell's refinement, as a 2-cell of the lifted cut polygraph.** -/
noncomputable def pairCellOf {X Y : Run K} (α : Cell 2 X Y) :
    (chCutPoly K).Rel ⟨chV α.obj⟩ ⟨chV Y.chain⟩ :=
  pairCell (cutGenOf (cellFactor α false).1.snd (codim_snd_cellFactor α false))
    (cutGenOf (cellFactor α false).1.fst (codim_fst_cellFactor α false))
    (cutGenOf (cellFactor α true).1.snd (codim_snd_cellFactor α true))
    (cutGenOf (cellFactor α true).1.fst (codim_fst_cellFactor α true))
    ((genHom_comp_cutGenOf α false).trans (genHom_comp_cutGenOf α true).symm)

/-- **…which is the cut the object's greatest refinement performs.** -/
theorem ev_pairCellOf {X Y : Run K} (α : Cell 2 X Y) :
    Cut.ev (pairCellOf α).cell.src = baseMap α.hom := by
  simpa using genHom_comp_cutGenOf α false

/-- **The 2-cell of the contraction a degree-two object carries**, between the two runs it spans. -/
noncomputable def cellOf {X Y : Run K} (α : Cell 2 X Y) :
    (chContraction K).poly.Rel ⟨vOfRun X⟩ ⟨vOfRun Y⟩ where
  dom := ⟨chV α.obj⟩
  cod := ⟨chV Y.chain⟩
  cell := Polygraph.InvRel.keep (pairCellOf α)
  rep_dom := GenObj.ext (((runEquiv K).right_inv _).symm.trans (congrArg vOfRun α.below))
  rep_cod := GenObj.ext (Subtype.ext (eltRep_chV Y))

/-- **…and it is kept**: its cut is the object's greatest refinement, read at the base. -/
theorem runCutCell_cellOf {X Y : Run K} (α : Cell 2 X Y) : RunCutCell (cellOf α) :=
  ⟨baseMap α.hom, congrArg some (ev_pairCellOf α), isTop_zHom (isTop_hom α)⟩

/-- The kept 2-cell a degree-two object is. -/
noncomputable def relOf {X Y : Run K} (α : Cell 2 X Y) :
    (chRunCutSpans K).poly.Rel ⟨vOfRun X⟩ ⟨vOfRun Y⟩ := ⟨cellOf α, runCutCell_cellOf α⟩

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
    runPre.mapPath ((chRunCutSpans K).subWords.map ((chContraction K).cell
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) (cutGenOf u hu))))
      = cutWord u hu := by
  by_cases hW : W K u
  · rw [(chContraction K).cell_of_S
      (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) (cutGenOf u hu))
      (chCutPicked_cutGenOf hu hW), cutWord, dif_pos hW]
    exact (congrArg runPre.mapPath
        (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) rfl _ Quiver.Path.nil)).trans
      (Prefunctor.mapPath_cellCongr runPre rfl _ Quiver.Path.nil)
  · rw [(chContraction K).cell_of_not_S
      (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) (cutGenOf u hu))
      (not_chCutPicked_cutGenOf hu hW), cutWord, dif_neg hW]
    exact congrArg runPre.mapPath (Paths.lift_toPath _ _)

/-- The reading of a word of the localized cut polygraph on the runs. -/
noncomputable def readRuns {U V : GenObj (cutLocPoly K).Gen} (w : Quiver.Path U V) :
    Quiver.Path (runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj U)))
      (runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj V))) :=
  runPre.mapPath ((chRunCutSpans K).subWords.map ((chContraction K).words.map w))

/-- **Reading is multiplicative** — three functors in a row. -/
theorem readRuns_cons {U V W : GenObj (cutLocPoly K).Gen} (p : Quiver.Path U V) (e : V ⟶ W) :
    readRuns (p.cons e) = (readRuns p).comp (readRuns e.toPath) :=
  (congrArg runPre.mapPath
      ((congrArg (chRunCutSpans K).subWords.map
          ((chContraction K).words.map_comp p e.toPath)).trans
        ((chRunCutSpans K).subWords.map_comp _ _))).trans
    (Prefunctor.mapPath_comp _ _ _)

theorem readRuns_nil {U : GenObj (cutLocPoly K).Gen} :
    readRuns (Quiver.Path.nil : Quiver.Path U U) = Quiver.Path.nil :=
  (congrArg runPre.mapPath
      ((congrArg (chRunCutSpans K).subWords.map ((chContraction K).words.map_id _)).trans
        ((chRunCutSpans K).subWords.map_id _))).trans (Prefunctor.mapPath_nil _ _)

/-- …so a two-letter word reads as its two letters. -/
theorem readRuns_two {U V W : GenObj (cutLocPoly K).Gen} (a : U ⟶ V) (b : V ⟶ W) :
    readRuns ((Quiver.Path.nil.cons a).cons b)
      = (readRuns a.toPath).comp (readRuns b.toPath) := by
  have h1 := readRuns_cons (Quiver.Path.nil.cons a) b
  have h2 := readRuns_cons (Quiver.Path.nil : Quiver.Path U U) a
  rw [h1, h2, readRuns_nil, Quiver.Path.nil_comp]

/-- **A letter's reading is `cutWord`.** -/
theorem readRuns_toPath {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) (cutGenOf u hu)).toPath
      = cutWord u hu :=
  (congrArg (fun w => runPre.mapPath ((chRunCutSpans K).subWords.map w))
      (Paths.lift_toPath (chContraction K).pre
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) (cutGenOf u hu)))).trans
    (runPre_mapPath_cell u hu)

/-- **The kept cell's boundary, read on the runs, is the cell's word** — the two cuts of a
factorisation, one letter each. -/
theorem readRuns_src_pairCellOf {X Y : Run K} (α : Cell 2 X Y) :
    readRuns ((cutLocPoly K).src (Polygraph.InvRel.keep (pairCellOf α)))
      = (cutWord (cellFactor α false).1.snd (codim_snd_cellFactor α false)).comp
        (cutWord (cellFactor α false).1.fst (codim_fst_cellFactor α false)) :=
  by
  refine (readRuns_two _ _).trans ?_
  exact congrArg₂ Quiver.Path.comp (readRuns_toPath _ _) (readRuns_toPath _ _)

@[inherit_doc readRuns_src_pairCellOf]
theorem readRuns_tgt_pairCellOf {X Y : Run K} (α : Cell 2 X Y) :
    readRuns ((cutLocPoly K).tgt (Polygraph.InvRel.keep (pairCellOf α)))
      = (cutWord (cellFactor α true).1.snd (codim_snd_cellFactor α true)).comp
        (cutWord (cellFactor α true).1.fst (codim_fst_cellFactor α true)) := by
  refine (readRuns_two _ _).trans ?_
  exact congrArg₂ Quiver.Path.comp (readRuns_toPath _ _) (readRuns_toPath _ _)

/-- **The kept cell's boundary, read on the runs, is the paper's word** — both are the two
factorisations of the object's greatest refinement, spelled letter by letter. -/
theorem runPre_mapPath_src_relOf {X Y : Run K} (α : Cell 2 X Y) :
    runPre.mapPath ((chRunCutSpans K).poly.src (relOf α)) = cellWords α false := by
  refine (congrArg runPre.mapPath
    (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) _ _ _)).trans ?_
  refine (Prefunctor.mapPath_cellCongr runPre _ _ _).trans ?_
  refine (congrArg (cellCongr Quiver.Path _ _) (readRuns_src_pairCellOf α)).trans ?_
  exact (cellCongr_trans Quiver.Path _ _ _ _ _).symm

@[inherit_doc runPre_mapPath_src_relOf]
theorem runPre_mapPath_tgt_relOf {X Y : Run K} (α : Cell 2 X Y) :
    runPre.mapPath ((chRunCutSpans K).poly.tgt (relOf α)) = cellWords α true := by
  refine (congrArg runPre.mapPath
    (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) _ _ _)).trans ?_
  refine (Prefunctor.mapPath_cellCongr runPre _ _ _).trans ?_
  refine (congrArg (cellCongr Quiver.Path _ _) (readRuns_tgt_pairCellOf α)).trans ?_
  exact (cellCongr_trans Quiver.Path _ _ _ _ _).symm

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
  top := topOf_fst_eq_of_permLen hmax.permLen_eq

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
    readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K)
        (cellCongr (chCutPoly K).Gen ha hb e)).toPath
      = cellCongr Quiver.Path
          (congrArg (fun z : (chCutPoly K).V =>
            runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩))) ha)
          (congrArg (fun z : (chCutPoly K).V =>
            runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩))) hb)
          (readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath) :=
  cellCongr_map (F := (chCutPoly K).Gen) (G := Quiver.Path) _
    (fun {_ _} e => readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath) ha hb e

/-- **A letter's reading is the paper's word for the refinement it lifts to**, the renaming of the
two ends being absorbed by the quotient. -/
theorem quot_cutWord_liftGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (poly K).quot.map (cutWord (liftGen e) (codim_liftGen e))
      = eqToHom (congrArg (poly K).quot.obj
            (congrArg (fun z : (chCutPoly K).V =>
              runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩)))
            (chV_vChain a).symm)).symm
        ≫ (poly K).quot.map
            (readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath)
        ≫ eqToHom (congrArg (poly K).quot.obj
            (congrArg (fun z : (chCutPoly K).V =>
              runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩)))
            (chV_vChain b).symm)) := by
  rw [← readRuns_toPath (liftGen e) (codim_liftGen e), cutGenOf_liftGen, readRuns_cellCongr]
  exact Paths.map_cellCongr₂ (poly K).quot _ _ _

/-- The 0-cell a letter's end names, read on the runs: the run below the chain it sits over. -/
theorem readPt_eq_bottomRun (z : (chCutPoly K).V) :
    runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩))
      = runPt (bottomRun (vChain z)) :=
  congrArg runPt (congrArg runOfV (Subtype.ext (congrArg eltRep (chV_vChain z).symm)))

/-- …and at a run it is that run. -/
theorem readPt_eq_runOfV {z : (chCutPoly K).V} (h : eltRep z = z) :
    runPre.obj ((chRunCutSpans K).pre.obj ((chContraction K).repObj ⟨z⟩))
      = runPt (runOfV ⟨z, h⟩) :=
  congrArg runPt (congrArg runOfV (Subtype.ext h))

/-- Two renamings in the middle of a two-letter word cancel. -/
private theorem eqToHom_splice {C : Type*} [Category C] {P A M M' B Q : C}
    (a : P = A) (h : M' = M) (d : B = Q) (f : A ⟶ M) (g : M ⟶ B) :
    (eqToHom a ≫ f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g ≫ eqToHom d)
      = eqToHom a ≫ f ≫ g ≫ eqToHom d := by
  subst a; subst h; subst d; simp

private theorem eqToHom_move {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : g = eqToHom p.symm ≫ f ≫ eqToHom q) :
    f = eqToHom p ≫ g ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h.symm

@[inherit_doc quot_cutWord_liftGen]
theorem quot_readRuns_letter {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (poly K).quot.map (readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath)
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
          (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) p)).cons
          (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) q)))
        = eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun x.as))
          ≫ (poly K).quot.map (cellWords (cellOfCut f hf hmax) ε)
          ≫ eqToHom (congrArg (poly K).quot.obj (readPt_eq_runOfV hrun)).symm := by
  obtain ⟨ε, hε⟩ := exists_bool_cellWords (cellOfCut f hf hmax)
    ⟨⟨vChain m.as, liftGen q, liftGen p, hcomp.trans (hom_cellOfCut f hf hmax).symm⟩,
      codim_liftGen q⟩
  refine ⟨ε, ?_⟩
  have hsplit : (poly K).quot.map (readRuns ((Quiver.Path.nil.cons
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) p)).cons
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) q)))
      = (poly K).quot.map (readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) p).toPath)
        ≫ (poly K).quot.map
          (readRuns (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) q).toPath) :=
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
  simp only [Category.assoc, eqToHom_trans]
  exact eqToHom_splice _ _ _ _ _

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
    (poly K).quot.map (readRuns ((cutLocPoly K).src (Polygraph.InvRel.keep γ)))
      = (poly K).quot.map (readRuns ((cutLocPoly K).tgt (Polygraph.InvRel.keep γ))) := by
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
  have hsrc' : (cutLocPoly K).src (Polygraph.InvRel.keep γ)
      = (Quiver.Path.nil.cons (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) p)).cons
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) q) :=
    congrArg (Polygraph.fwdPre (chCutPoly K) (chCutPicked K)).mapPath hsrc
  have htgt' : (cutLocPoly K).tgt (Polygraph.InvRel.keep γ)
      = (Quiver.Path.nil.cons (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) p')).cons
        (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) q') :=
    congrArg (Polygraph.fwdPre (chCutPoly K) (chCutPicked K)).mapPath htgt
  have hrel := quot_cellWords
    (cellOfCut (X := runOfV ⟨y.as, hrun⟩) (e := vChain x.as) (liftGen q ≫ liftGen p) hf hmax')
  rw [hsrc', htgt']
  refine hE.trans (Eq.trans ?_ hE'.symm)
  refine congrArg (fun t => eqToHom (congrArg (poly K).quot.obj (readPt_eq_bottomRun x.as))
    ≫ t ≫ eqToHom (congrArg (poly K).quot.obj (readPt_eq_runOfV hrun)).symm) ?_
  cases ε <;> cases ε' <;> first | rfl | exact hrel | exact hrel.symm

/-- **The comparison of polygraphs**: a degree-one object is its kept cut, a degree-two object the
kept cell of its greatest refinement, and the boundaries agree on the nose. -/
noncomputable def paperHom : Polygraph.Hom (poly K) ((chRunCutSpans K).poly) where
  pre := paperPre
  two {_ _} α := relOf α
  src_two α :=
    runPre_mapPath_injective
      ((runPre_mapPath_paperPre_mapPath (cellWords α false)).trans
        (runPre_mapPath_src_relOf α).symm).symm
  tgt_two α :=
    runPre_mapPath_injective
      ((runPre_mapPath_paperPre_mapPath (cellWords α true)).trans
        (runPre_mapPath_tgt_relOf α).symm).symm

theorem paperPre_obj_bijective : Function.Bijective (paperPre (K := K)).obj :=
  ⟨fun _ _ h => GenObj.ext ((runEquiv K).injective (congrArg GenObj.as h)),
    fun U => ⟨⟨runOfV U.as⟩, GenObj.ext ((runEquiv K).right_inv U.as)⟩⟩

theorem paperPre_map_bijective (X Y : GenObj (Gen (K := K))) :
    Function.Bijective (paperPre.map : (X ⟶ Y) → _) :=
  (genEquiv (vOfRun X.as) (vOfRun Y.as)).symm.bijective

/-! ## …so the paper's relations derive the kept cells

A kept 2-cell is a `keep`, the formal cancellations carrying no cut (`invCellHom` is `none` on
them), and a `keep` is one of the paper's by `quot_readRuns_src_eq_tgt`.  The renaming of its two
ends is the same on both sides, so the quotient does not see it. -/

/-- A renaming of a word's two ends is invisible to an equation between words. -/
private theorem quot_cellCongr_congr {A B A' B' : GenObj (Gen (K := K))} (h : A = A') (h' : B = B')
    {w w' : Quiver.Path A B} (hw : (poly K).quot.map w = (poly K).quot.map w') :
    (poly K).quot.map (cellCongr Quiver.Path h h' w)
      = (poly K).quot.map (cellCongr Quiver.Path h h' w') := by
  subst h; subst h'; exact hw

/-- **A kept 2-cell's two sides agree** — only a `keep` carries a cut, and a `keep`'s two sides are
the two words its object reads. -/
theorem quot_readRuns_src_eq_tgt_of_runCutCell {X Y : GenObj (chContraction K).poly.Gen} :
    ∀ (α : (chContraction K).poly.Rel X Y), RunCutCell α →
      (poly K).quot.map (readRuns ((cutLocPoly K).src α.cell))
        = (poly K).quot.map (readRuns ((cutLocPoly K).tgt α.cell))
  | ⟨_, _, .keep γ, _, _⟩, ⟨f, hf, hmax⟩ => by
      obtain rfl : f = Cut.ev γ.cell.src := by simpa [invCellHom] using hf.symm
      exact quot_readRuns_src_eq_tgt γ hmax
  | ⟨_, _, .cancel _ _, _, _⟩, ⟨_, hf, _⟩ => absurd hf (by simp [invCellHom])
  | ⟨_, _, .cancel' _ _, _, _⟩, ⟨_, hf, _⟩ => absurd hf (by simp [invCellHom])

/-- **The paper's relations derive the kept cells** — the last obligation of `Presents.ofCells`. -/
theorem paperCellsDerivable {x y : GenObj (Gen (K := K))} {u v : Quiver.Path x y}
    (h : (chRunCutSpans K).poly.homRel (paperPre.mapPath u) (paperPre.mapPath v)) :
    (poly K).quot.map u = (poly K).quot.map v := by
  obtain ⟨β, hs, ht⟩ := h
  have hu : runPre.mapPath ((chRunCutSpans K).poly.src β) = u :=
    (congrArg runPre.mapPath hs).trans (runPre_mapPath_paperPre_mapPath u)
  have hv : runPre.mapPath ((chRunCutSpans K).poly.tgt β) = v :=
    (congrArg runPre.mapPath ht).trans (runPre_mapPath_paperPre_mapPath v)
  have hsw : runPre.mapPath ((chRunCutSpans K).poly.src β)
      = cellCongr Quiver.Path (congrArg (fun Z => runPre.obj ((chRunCutSpans K).pre.obj Z))
            β.1.rep_dom)
          (congrArg (fun Z => runPre.obj ((chRunCutSpans K).pre.obj Z)) β.1.rep_cod)
          (readRuns ((cutLocPoly K).src β.1.cell)) :=
    (congrArg runPre.mapPath
        (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) _ _ _)).trans
      (Prefunctor.mapPath_cellCongr runPre _ _ _)
  have htw : runPre.mapPath ((chRunCutSpans K).poly.tgt β)
      = cellCongr Quiver.Path (congrArg (fun Z => runPre.obj ((chRunCutSpans K).pre.obj Z))
            β.1.rep_dom)
          (congrArg (fun Z => runPre.obj ((chRunCutSpans K).pre.obj Z)) β.1.rep_cod)
          (readRuns ((cutLocPoly K).tgt β.1.cell)) :=
    (congrArg runPre.mapPath
        (Paths.map_cellCongr_hom (Paths.lift (chRunCutSpans K).pre) _ _ _)).trans
      (Prefunctor.mapPath_cellCongr runPre _ _ _)
  rw [← hu, ← hv, hsw, htw]
  exact quot_cellCongr_congr _ _ (quot_readRuns_src_eq_tgt_of_runCutCell β.1 β.2)

/-- **The paper's polygraph presents `Ch(K)[W⁻¹]`** — 0-cells the runs, 1- and 2-cells the objects
of degree one and two — for every `K` and with no hypothesis on `K`. -/
noncomputable def paperPresents (K : BPSet) :
    Presents (poly K) (((W K).op).Localization) :=
  Polygraph.Presents.ofCells paperHom paperPre_obj_bijective
    (fun x y => paperPre_map_bijective x y) (chCellPresentation K) paperCellsDerivable

end ChainCat.Paper
