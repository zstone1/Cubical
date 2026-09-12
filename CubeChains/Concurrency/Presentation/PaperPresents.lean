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

/-- Renaming a cell's endpoints leaves its object alone. -/
theorem obj_cellCongr {n : ℕ} {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y') (α : Cell n X Y) :
    (cellCongr (Cell n) hx hy α).obj = α.obj := by subst hx; subst hy; rfl

/-- …and renaming a 1-cell of the contraction leaves its source alone. -/
theorem dom_cellCongr {U U' V V' : (chContraction K).V} (hu : U = U') (hv : V = V')
    (g : (chContraction K).Gen U V) :
    (cellCongr (chContraction K).Gen hu hv g).dom = g.dom := by subst hu; subst hv; rfl

/-- …and its target. -/
theorem cod_cellCongr {U U' V V' : (chContraction K).V} (hu : U = U') (hv : V = V')
    (g : (chContraction K).Gen U V) :
    (cellCongr (chContraction K).Gen hu hv g).cod = g.cod := by subst hu; subst hv; rfl

@[simp] theorem obj_genOfRunCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : (genOfRunCut g hg).obj = vChain g.dom :=
  obj_cellCongr _ _ _

/-- **A kept cut lands on its target run** — `RunCut` says the target is its own representative. -/
theorem cod_eq_of_runCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : g.cod = V.1 := hg.symm.trans g.rep_cod

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
    (runCutOfGen α).dom = chV α.obj := dom_cellCongr _ _ _

@[simp] theorem cod_runCutOfGen {U V : (chContraction K).V} (α : Gen (runOfV U) (runOfV V)) :
    (runCutOfGen α).cod = chV (runOfV V).chain := cod_cellCongr _ _ _

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
is kept: its target is the run the refinement comes out of and its cut attains the capacity
(`permLen_runCross_topOf`). -/

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

/-- **…and it is kept**: its target is the run the refinement comes out of, and the refinement
crosses as much as the object's beads allow. -/
theorem runCutCell_cellOf {X Y : Run K} (α : Cell 2 X Y) : RunCutCell (cellOf α) :=
  ⟨eltRep_chV Y, baseMap α.hom, congrArg some (ev_pairCellOf α),
    (congrArg permLen (runCross_zHom α.hom (dimSum_eq_of_hom α.hom))).trans
      (permLen_runCross_hom α)⟩

/-- The kept 2-cell a degree-two object is. -/
noncomputable def relOf {X Y : Run K} (α : Cell 2 X Y) :
    (chRunCutSpans K).poly.Rel ⟨vOfRun X⟩ ⟨vOfRun Y⟩ := ⟨cellOf α, runCutCell_cellOf α⟩

/-! ## The boundaries agree, letter by letter

`cutWord` *is* the contraction's own word for the bead cut, read on the runs — that is how it is
defined — so the comparison of boundaries is the same statement one letter at a time. -/

/-- A renaming of a 0-cell carries the empty word and nothing else. -/
private theorem map_cellCongr_nil {A : Type*} [Quiver A] {B : Type*} [Quiver B]
    (π : A ⥤q Paths B) {a b : A} (h : a = b) :
    (Paths.lift π).map (cellCongr Quiver.Path rfl h Quiver.Path.nil)
      = cellCongr (fun x y : Paths B => x ⟶ y) rfl (congrArg π.obj h) Quiver.Path.nil := by
  subst h; rfl

/-- …and a prefunctor carries it along. -/
private theorem mapPath_cellCongr_nil {A : Type*} [Quiver A] {B : Type*} [Quiver B]
    (π : A ⥤q B) {a b : A} (h : a = b) :
    π.mapPath (cellCongr Quiver.Path rfl h Quiver.Path.nil)
      = cellCongr Quiver.Path rfl (congrArg π.obj h) Quiver.Path.nil := by
  subst h; rfl

/-- **A merge is picked** — it is one of the 1-cells the localization inverts. -/
theorem chCutPicked_cutGenOf {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : W K u) :
    chCutPicked K (cutGenOf u hu) :=
  (merge_iff (baseMap u)).mpr ⟨(W_baseHom_iff (a := chV c) (b := chV d) u).mpr hW, hu⟩

/-- **…and any other cut is not.** -/
theorem not_chCutPicked_cutGenOf {c d : Ch K} {u : c ⟶ d} (hu : codim u = 1) (hW : ¬ W K u) :
    ¬ chCutPicked K (cutGenOf u hu) := fun hm =>
  hW ((W_baseHom_iff (a := chV c) (b := chV d) u).mp ((merge_iff (baseMap u)).mp hm).1)

/-- A renaming of the two ends carries a word. -/
private theorem lift_map_cellCongr {A : Type*} [Quiver A] {B : Type*} [Quiver B]
    (π : A ⥤q Paths B) {a a' b b' : A} (h : a = a') (h' : b = b') (w : Quiver.Path a b) :
    (Paths.lift π).map (cellCongr Quiver.Path h h' w)
      = cellCongr (fun x y : Paths B => x ⟶ y) (congrArg π.obj h) (congrArg π.obj h')
        ((Paths.lift π).map w) := by
  subst h; subst h'; rfl

/-- …and so does a prefunctor. -/
private theorem mapPath_cellCongr {A : Type*} [Quiver A] {B : Type*} [Quiver B]
    (π : A ⥤q B) {a a' b b' : A} (h : a = a') (h' : b = b') (w : Quiver.Path a b) :
    π.mapPath (cellCongr Quiver.Path h h' w)
      = cellCongr Quiver.Path (congrArg π.obj h) (congrArg π.obj h') (π.mapPath w) := by
  subst h; subst h'; rfl

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
    exact (congrArg runPre.mapPath (map_cellCongr_nil (chRunCutSpans K).pre _)).trans
      (mapPath_cellCongr_nil runPre _)
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
  refine (congrArg runPre.mapPath (lift_map_cellCongr (chRunCutSpans K).pre _ _ _)).trans ?_
  refine (mapPath_cellCongr runPre _ _ _).trans ?_
  refine (congrArg (cellCongr Quiver.Path _ _) (readRuns_src_pairCellOf α)).trans ?_
  exact (cellCongr_trans Quiver.Path _ _ _ _ _).symm

@[inherit_doc runPre_mapPath_src_relOf]
theorem runPre_mapPath_tgt_relOf {X Y : Run K} (α : Cell 2 X Y) :
    runPre.mapPath ((chRunCutSpans K).poly.tgt (relOf α)) = cellWords α true := by
  refine (congrArg runPre.mapPath (lift_map_cellCongr (chRunCutSpans K).pre _ _ _)).trans ?_
  refine (mapPath_cellCongr runPre _ _ _).trans ?_
  refine (congrArg (cellCongr Quiver.Path _ _) (readRuns_tgt_pairCellOf α)).trans ?_
  exact (cellCongr_trans Quiver.Path _ _ _ _ _).symm

/-- **The comparison of polygraphs**: a degree-one object is its kept cut, a degree-two object is the
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
  ⟨fun X Y h => GenObj.ext ((runEquiv K).injective (congrArg GenObj.as h)),
    fun U => ⟨⟨runOfV U.as⟩, GenObj.ext ((runEquiv K).right_inv U.as)⟩⟩

theorem paperPre_map_bijective (X Y : GenObj (Gen (K := K))) :
    Function.Bijective (paperPre.map : (X ⟶ Y) → _) :=
  (genEquiv (vOfRun X.as) (vOfRun Y.as)).symm.bijective

end ChainCat.Paper
