import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Concurrency.Executions.Complement
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/PaperPoly — the polygraph, defined directly

0-cells the runs; cells the **objects**, graded by degree — degree one a 1-cell, degree two a
2-cell.  An object needs no refinement beside it: the merge onto it (`bottomHom`) and that merge's
complement (`Run.compl`), which is its greatest refinement (`topOf`), are both functions of it.

    X.chain ──bottomHom──▸ obj ◂──topOf── Y.chain            a cell  X ⟶ Y

Two facts make that the right indexing.  The complement of a merge is never a merge
(`not_W_topOf`), so a cell's refinement crosses; and at degree one it is the *only* crossing one
(`topOf_fst_eq_of_not_W`, from `eq_atomOnes`), so a degree-one object carries exactly one 1-cell.

`objWords` reads a degree-two object as its two words: `oneCutEquivBool` names the two
factorisations of its greatest refinement, and `cutWord` spells each — of length one or two, which
is why the braid relation runs to three letters a side where commutation runs to two.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## A chain, and the run below it -/

/-- The 0-cell of the lifted cut polygraph a chain names. -/
def chV (a : Ch K) : (chCutPoly K).V := ⟨zObj a.dims, a.map⟩

@[simp] theorem vChain_chV (a : Ch K) : vChain (chV a) = a := rfl

/-- **A 0-cell of the contraction is a run** — it is its own merge, so its shape is all ones. -/
theorem isRun_vChain (U : (chContraction K).V) : IsRun K (vChain U.1) := fun _ hd =>
  List.eq_of_mem_replicate (congrArg ChainCat.Obj.dims (shOf_eq_ones_of_eltRep U.2 rfl) ▸ hd)

/-- The run a 0-cell of the contraction names. -/
def runOfV (U : (chContraction K).V) : Run K := ⟨vChain U.1, isRun_vChain U⟩

/-- **A run is its own run** — its shape is all ones, and the merge out of that shape is the
identity. -/
theorem eltRep_chV (X : Run K) : eltRep (chV X.chain) = chV X.chain :=
  eltRep_eq_self (N := X.dims.length) (Obj.eq_of_dims (List.eq_replicate_of_mem X.ones))

/-- The 0-cell of the contraction a run names. -/
def vOfRun (X : Run K) : (chContraction K).V := ⟨chV X.chain, eltRep_chV X⟩

/-- **A 0-cell is the shape it sits over, carrying its map** — the only transport the `Ch K`↔`∫F`
comparison pays, and it is definitional in the fibre. -/
theorem chV_vChain (z : (chCutPoly K).V) : chV (vChain z) = z :=
  Sigma.ext (Obj.eq_of_dims rfl) HEq.rfl

/-- **The 0-cells are the runs** — the comparison in dimension zero. -/
def runEquiv (K : BPSet) : Run K ≃ (chContraction K).V where
  toFun := vOfRun
  invFun := runOfV
  left_inv _ := rfl
  right_inv U := Subtype.ext (chV_vChain U.1)

/-- **The run a chain is merged into from.** -/
noncomputable def bottomRun (a : Ch K) : Run K := runOfV ⟨eltRep (chV a), eltRep_idem _⟩

/-- **A run is the run below itself.** -/
theorem bottomRun_self (X : Run K) : bottomRun X.chain = X :=
  Run.ext (congrArg vChain (eltRep_chV X))

/-- **A merge does not change the run below.** -/
theorem bottomRun_eq_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) : bottomRun d = bottomRun c :=
  Run.ext (congrArg vChain (eltRep_eq_of_W (a := chV d) (b := chV c) u hu).symm)

/-- **A merge out of a run names the run below its target.** -/
theorem eq_bottomRun_of_W {X : Run K} {a : Ch K} (m : X.chain ⟶ a) (hm : W K m) :
    bottomRun a = X := (bottomRun_eq_of_W m hm).trans (bottomRun_self X)

/-- **The merge a chain is entered by** from the run below it. -/
noncomputable def bottomHom (a : Ch K) : (bottomRun a).chain ⟶ a := runMergeK (chV a)

theorem W_bottomHom (a : Ch K) : W K (bottomHom a) := W_runMergeK (chV a)

/-! ## The greatest refinement, by complementing the merge

A refinement of `e` out of a run *is* a run of `⋁e.dims` — the source's classifying map is forced to
`φ ≫ e.map` — so the complement (`Run.compl`, reversal inside every bead) acts on it.  The
complement of the merge is the refinement of `e` that crosses as much as `e` allows. -/

/-- A refinement out of a run, as a run of the target's wedge. -/
def wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : Run (⋁e.dims) :=
  ⟨⟨X.dims, Hom.φ f⟩, X.ones⟩

/-- …and back: the run it refines `e` by, with the refinement. -/
def ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) : Σ X : Run K, X.chain ⟶ e :=
  ⟨⟨⟨r.dims, r.chain.map ≫ e.map⟩, r.ones⟩, ⟨r.chain.map, rfl⟩⟩

/-- **The greatest refinement of a chain out of a run** — the complement of its merge. -/
noncomputable def topOf (e : Ch K) : Σ X : Run K, X.chain ⟶ e :=
  ofWedgeRun e (wedgeRun (bottomHom e)).compl

/-- **The run a chain's greatest refinement comes out of** — the complement of `bottomRun`.  The two
runs a chain spans: `bottomRun` crosses nothing, `topRun` crosses as much as the chain allows. -/
noncomputable abbrev topRun (e : Ch K) : Run K := (topOf e).1

/-- …and that refinement. -/
noncomputable abbrev topHom (e : Ch K) : (topRun e).chain ⟶ e := (topOf e).2

/-- **Codimension is degree, out of a run.** -/
theorem codim_topOf (e : Ch K) : codim (topOf e).2 = degree e := by
  change degree e - degree (topOf e).1.chain = degree e
  rw [(isRun_iff_degree_eq_zero _).mp (topOf e).1.property, Nat.sub_zero]

@[simp] theorem wedgeRun_ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) :
    wedgeRun (ofWedgeRun e r).2 = r := rfl

/-- **Two merges into one chain out of runs name one run of its wedge** — `eq_bottomRun_of_W`
identifies the runs and `eq_of_W` the refinements. -/
theorem wedgeRun_eq_of_W {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (hf : W K f) (hg : W K g) : wedgeRun f = wedgeRun g := by
  obtain rfl : X = Y := (eq_bottomRun_of_W f hf).symm.trans (eq_bottomRun_of_W g hg)
  rw [eq_of_W hf hg]

/-- **The greatest refinement crosses**, as soon as there is anything to cross: it is the complement
of the merge, and the complement fixes only the runs of degree zero (`Run.compl_ne`).  So the two
factorisations a degree-two object reads spell a relation, not `w = w`. -/
theorem not_W_topOf (e : Ch K) (he : degree e ≠ 0) : ¬ W K (topOf e).2 := fun hW =>
  Run.compl_ne (wedgeRun (bottomHom e)) he
    ((wedgeRun_ofWedgeRun e _).symm.trans (wedgeRun_eq_of_W hW (W_bottomHom e)))

/-- **A refinement out of a run recovers the run** — its source's classifying map is forced. -/
theorem ofWedgeRun_wedgeRun_fst {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    (ofWedgeRun e (wedgeRun f)).1 = X :=
  Run.ext (congrArg (fun m => (⟨X.dims, m⟩ : Ch K)) f.w)

/-- A run refining a chain has the chain's events as its beads. -/
theorem Run.dims_eq_of_hom {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    X.dims = 𝟙^(dimSum e.dims) :=
  List.eq_replicate_iff.mpr
    ⟨by rw [← dimSum_eq_length_of_ones X.ones]; exact dimSum_eq_of_hom f, X.ones⟩

/-- **`W` is a condition on the wedge map** — so it is the same upstairs and at the base. -/
theorem W_zHom_iff {a b : Ch K} (f : a ⟶ b) : W Zbp (zHom (Hom.φ f)) ↔ W K f :=
  (W_iff_monotone_coordMap _).trans (W_iff_monotone_coordMap f).symm

/-- **At degree one there is only one crossing refinement out of the run** — `eq_atomOnes`: the
shape is an atom's cell (`exists_atomComp`), and at that cell a non-merge is the atom. -/
theorem eq_of_not_W_deg_one {d : List ℕ+} (hd : ∀ x ∈ d, x = 1) {c : Ch Zbp}
    (hdeg : degree c = 1) {u v : zObj d ⟶ c} (hu : ¬ W Zbp u) (hv : ¬ W Zbp v) : u = v := by
  obtain ⟨n, rfl⟩ : ∃ n, d = 𝟙^n := ⟨d.length, List.eq_replicate_iff.mpr ⟨rfl, hd⟩⟩
  have hcod : codim u = 1 := by
    change degree c - degree (zObj (𝟙^n)) = 1
    rw [hdeg, (degree_eq_zero_iff (zObj (𝟙^n))).mpr fun x hx => List.eq_of_mem_replicate hx,
      Nat.sub_zero]
  obtain ⟨k, rfl⟩ := exists_atomComp u hcod
  rw [eq_atomOnes hu, eq_atomOnes hv]

/-- **…and so it names one run of the wedge** — the degree-one twin of `wedgeRun_eq_of_W`. -/
theorem wedgeRun_eq_of_not_W {e : Ch K} (he : degree e = 1) {X Y : Run K}
    {f : X.chain ⟶ e} {g : Y.chain ⟶ e} (hf : ¬ W K f) (hg : ¬ W K g) :
    wedgeRun f = wedgeRun g := by
  obtain ⟨⟨Xd, Xm⟩, Xp⟩ := X
  obtain ⟨⟨Yd, Ym⟩, Yp⟩ := Y
  obtain ⟨n, rfl⟩ : ∃ n, Xd = 𝟙^n := ⟨Xd.length, List.eq_replicate_iff.mpr ⟨rfl, Xp⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, Yd = 𝟙^m := ⟨Yd.length, List.eq_replicate_iff.mpr ⟨rfl, Yp⟩⟩
  obtain rfl : n = m := by
    have h1 := dimSum_eq_of_hom f
    have h2 := dimSum_eq_of_hom g
    rw [show dimSum (𝟙^n : List ℕ+) = n from dimSum_replicate n] at h1
    rw [show dimSum (𝟙^m : List ℕ+) = m from dimSum_replicate m] at h2
    omega
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    eq_of_not_W_deg_one (fun x hx => List.eq_of_mem_replicate hx) (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact Run.ext (congrArg (fun φ => (⟨𝟙^n, φ⟩ : Ch (⋁e.dims)))
    (congrArg ChainCat.Hom.φ hbase))

/-- **At degree one the greatest refinement is the only crossing one.**  So a degree-one object
carries a 1-cell with nothing beside it: the merge names one end, the complement the other. -/
theorem topOf_fst_eq_of_not_W {e : Ch K} (he : degree e = 1) {X : Run K} {f : X.chain ⟶ e}
    (hf : ¬ W K f) : (topOf e).1 = X :=
  (congrArg (fun r => (ofWedgeRun e r).1)
      (wedgeRun_eq_of_not_W he (not_W_topOf e (by rw [he]; exact one_ne_zero)) hf)).trans
    (ofWedgeRun_wedgeRun_fst f)

/-! ## The cells -/

/-- A **cell** `X ⟶ Y` of dimension `n`: an **object of degree `n`**, read between the two runs it
spans — `X` the run below it (its merge), `Y` the run its greatest refinement comes out of (the
complement of that merge).  Both ends are functions of the object, so the object is the only datum.

Dimension one is a generator and dimension two a relation: the same data one degree up.  At
dimension one `topOf` is the *only* crossing refinement (`topOf_fst_eq_of_not_W`), which is why a
degree-one object needs no cut beside it. -/
structure Cell (n : ℕ) (X Y : Run K) where
  /-- the object -/
  obj : Ch K
  /-- …of degree `n` -/
  degree_obj : degree obj = n
  /-- the run below it -/
  below : bottomRun obj = X
  /-- the run its greatest refinement comes out of -/
  top : (topOf obj).1 = Y

/-- A **1-cell**: a degree-one object. -/
abbrev Gen (X Y : Run K) : Type := Cell 1 X Y

/-- **The refinement a cell carries**, out of the run at its far end. -/
noncomputable abbrev Cell.hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : Y.chain ⟶ α.obj :=
  eqToHom (congrArg Run.chain α.top.symm) ≫ (topOf α.obj).2

/-- **A cell's refinement has codimension `n`.** -/
theorem Cell.codim_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : codim α.hom = n :=
  ((codim_eqToHom_comp _ _).trans (codim_topOf α.obj)).trans α.degree_obj

/-- **…and it crosses**, at every positive degree (`not_W_topOf`). -/
theorem Cell.not_W_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) (hn : n ≠ 0) : ¬ W K α.hom := by
  intro h
  exact not_W_topOf α.obj (α.degree_obj.trans_ne hn)
    (W_of_comp_right (eqToHom (congrArg Run.chain α.top.symm)) _ h)

/-- A 0-cell, as a vertex of the generating quiver — `Polygraph.pt` before `poly` exists. -/
abbrev runPt (X : Run K) : GenObj (Gen (K := K)) := ⟨X⟩

/-- A 1-cell, as a letter of the generating quiver — what `toPath` wants. -/
def Gen.letter {X Y : Run K} (g : Gen X Y) : runPt X ⟶ runPt Y := g

/-! ## What a span names in `Ch K[W⁻¹]`

Read in `(Ch K)ᵒᵖ`, so that a word runs the way its 1-cells do: the merge is the invertible leg, so
the arrow points from the run below the target to the run the cut comes out of. -/

/-- The arrow a merge-and-refinement span names.

    X.chain ──m──▸ b ◂──f── Y.chain          `W K m`,  `arr hm f : ⟦X⟧ ⟶ ⟦Y⟧` -/
noncomputable def arr {X Y : Run K} {b : Ch K} {m : X.chain ⟶ b} (hm : W K m) (f : Y.chain ⟶ b) :
    (W K).op.Q.obj (op X.chain) ⟶ (W K).op.Q.obj (op Y.chain) :=
  (Localization.Construction.wIso (W := (W K).op) m.op hm).inv ≫ (W K).op.Q.map f.op

/-- A 1-cell, read in `Ch K[W⁻¹]`: its object's merge inverted, then its greatest refinement. -/
noncomputable def pre (K : BPSet) : GenObj (Gen (K := K)) ⥤q ((W K).op).Localization where
  obj X := (W K).op.Q.obj (op X.as.chain)
  map g := eqToHom (congrArg (fun Z : Run K => (W K).op.Q.obj (op Z.chain)) g.below).symm
    ≫ arr (W_bottomHom g.obj) g.hom

/-- The arrow a **word** of 1-cells names. -/
noncomputable def ev (K : BPSet) : Paths (GenObj (Gen (K := K))) ⥤ ((W K).op).Localization :=
  Paths.lift (pre K)

@[simp] theorem ev_toPath {X Y : Run K} (g : Gen X Y) :
    (ev K).map g.letter.toPath
      = eqToHom (congrArg (fun Z : Run K => (W K).op.Q.obj (op Z.chain)) g.below).symm
        ≫ arr (W_bottomHom g.obj) g.hom :=
  Paths.lift_toPath (pre K) g

/-- **Conjugating a two-step factorisation telescopes** — the merge in the middle is cancelled by
the inverse it names.  This is the whole calculation behind `ev_cutWord_comp`. -/
theorem arr_comp {X Y Z : Run K} {b mid : Ch K} {m : X.chain ⟶ b} (hm : W K m)
    {k : Z.chain ⟶ mid} (hk : W K k) (g : mid ⟶ b) (e : Y.chain ⟶ mid) :
    arr hm (k ≫ g) ≫ arr hk e = arr hm (e ≫ g) := by
  have hk' : (W K).op.Q.map k.op
      = (Localization.Construction.wIso (W := (W K).op) k.op hk).hom := rfl
  rw [arr, arr, arr, op_comp, op_comp, Functor.map_comp, Functor.map_comp, hk']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- A word read at other names for its two ends — the only transport a word here carries. -/
private def readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) : Quiver.Path (runPt X') (runPt Y') :=
  cellCongr Quiver.Path (congrArg runPt hx) (congrArg runPt hy) w

/-! ## A kept cut of the contraction, as a 1-cell

`RunCut` says the cut starts at a run, and the merge onto the chain it lands on is the contraction's
own (`runMergeK`) — so a kept 1-cell carries exactly a `Gen`'s data. -/

theorem codim_chCutHom {a b : (chCutPoly K).V}
    (g : InvGen (chCutPoly K) (chCutPicked K) a b) (hg : ¬ Cut.merged g) :
    codim (chCutHom g hg) = 1 := (chFwdOf g hg).1.2

theorem not_W_chCutHom {a b : (chCutPoly K).V}
    (g : InvGen (chCutPoly K) (chCutPicked K) a b) (hg : ¬ Cut.merged g) :
    ¬ W K (chCutHom g hg) := by
  rcases g with e | ⟨e, he⟩
  · exact fun hW => hg ((merge_iff (Cut.genHom e.1)).mpr
      ⟨(W_baseHom_iff _).mpr hW, Cut.codim_genHom e.1⟩)
  · exact absurd trivial hg

/-- **A kept 1-cell of the contraction is a 1-cell here** — the same degree-one object.  Its cut is
the object's greatest refinement, because at degree one there is no other crossing one. -/
noncomputable def genOfRunCut {U V : (chContraction K).V} (g : (chContraction K).Gen U V)
    (hg : RunCut g) : Gen (runOfV U) (runOfV V) :=
  cellCongr (Cell 1) (congrArg runOfV (Subtype.ext g.rep_dom))
    (congrArg runOfV (Subtype.ext (hg.symm.trans g.rep_cod)))
    (show Cell 1 (runOfV ⟨eltRep g.dom, eltRep_idem _⟩) (runOfV ⟨g.cod, hg⟩) from
      have hdeg : degree (vChain g.dom) = 1 := by
        have h1 := degree_eq_add_codim (chCutHom g.gen g.not_mem)
        rw [(isRun_iff_degree_eq_zero _).mp (isRun_vChain ⟨g.cod, hg⟩),
          codim_chCutHom g.gen g.not_mem] at h1
        simpa using h1
      { obj := vChain g.dom
        degree_obj := hdeg
        below := eq_bottomRun_of_W (runMergeK g.dom) (W_runMergeK g.dom)
        top := topOf_fst_eq_of_not_W (X := runOfV ⟨g.cod, hg⟩) hdeg
          (not_W_chCutHom g.gen g.not_mem) })

/-- **The comparison of generating quivers**: the kept cuts of the contraction, read on the runs. -/
noncomputable def runPre : GenObj (chRunCutSpans K).poly.Gen ⥤q GenObj (Gen (K := K)) where
  obj U := runPt (runOfV U.as)
  map e := genOfRunCut e.1 e.2

/-! ## The word a codimension-one refinement reads as -/

/-- The 1-cell of the contraction a crossing codimension-one refinement is. -/
noncomputable def chGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) (hW : ¬ W K u) :
    (chContraction K).Gen ⟨eltRep (chV d), eltRep_idem _⟩ ⟨eltRep (chV c), eltRep_idem _⟩ :=
  (chContraction K).genCell
    (fwdCell (chCutPoly K) (chCutPicked K) (cutGen (c := chV d) (c' := chV c) (baseMap u) hu u.w))
    (fun hm => hW ((W_baseHom_iff (a := chV c) (b := chV d) u).mp
      ((merge_iff (baseMap u)).mp hm).1))

/-- **The word a codimension-one refinement reads as**, between the runs of its two ends: a merge
reads as the empty word, and any other cut as the word its conjugate spells — one letter when it
starts at a run, two when it does not. -/
noncomputable def cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    Quiver.Path (runPt (bottomRun d)) (runPt (bottomRun c)) :=
  @dite _ (W K u) (Classical.propDecidable _)
    (fun hW => readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil)
    (fun hW => runPre.mapPath (keptWord (P := (chContraction K).poly) RunCut
      (runCellWord (chGenOf u hu hW)) (all_runCellWord _)))

/-! ## The two words a codimension-two refinement out of a run reads as -/

/-- **The word a factorisation of a codimension-two refinement out of a run reads as.**  The first
leg is a cut out of the run, hence one letter; the second starts off a run, hence one or two — which
is the whole of the braid/commutation asymmetry. -/
noncomputable def factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2)
    (ε : Bool) : Quiver.Path (runPt (bottomRun b)) (runPt X) :=
  let F := (oneCutEquivBool f hf).symm ε
  readAt rfl (bottomRun_self X)
    ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))

/-- **The two words a degree-two object reads as** — `oneCutEquivBool` names the two factorisations
of its greatest refinement, and `cutWord` spells each.  No data beyond the object. -/
noncomputable def objWords (e : Ch K) (he : degree e = 2) (ε : Bool) :
    Quiver.Path (runPt (bottomRun e)) (runPt (topOf e).1) :=
  factorWords (topOf e).2 ((codim_topOf e).trans he) ε

/-- **The polygraph**: the runs, the codimension-one cuts out of them, and one relation per
codimension-two refinement out of a run, equating the words its two factorisations read as. -/
noncomputable def poly (K : BPSet) : Polygraph where
  V := Run K
  Gen := Gen
  Rel x y := Cell 2 x.as y.as
  src α := readAt α.below α.top (objWords α.obj α.degree_obj false)
  tgt α := readAt α.below α.top (objWords α.obj α.degree_obj true)

/-! ## That the reading is sound

One equation, about `cutWord` itself rather than about some word: the content is `quot_runCellWord`,
read through `(W K).op.Q` instead of through the cut presentation's comparison functor. -/

/-- **The reading is sound**: the word a codimension-one refinement reads as names the arrow the
refinement names between the runs at its two ends. -/
def Reads (K : BPSet) : Prop :=
  ∀ {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1),
    (ev K).map (cutWord u hu) = arr (W_bottomHom d) (bottomHom c ≫ u)

/-- **A transported word names the transported arrow.** -/
theorem ev_readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) :
    (ev K).map (readAt hx hy w)
      = eqToHom (congrArg (fun Z : Run K => (ev K).obj (runPt Z)) hx).symm ≫ (ev K).map w
        ≫ eqToHom (congrArg (fun Z : Run K => (ev K).obj (runPt Z)) hy) := by
  subst hx
  subst hy
  rw [readAt, cellCongr_self]
  simp

/-- **Both factorisations read as the refinement itself** — the right-hand side does not mention the
factorisation, so the two words of a 2-cell name one arrow of `Ch K[W⁻¹]`. -/
theorem ev_cutWord_comp (h : Reads K) {X : Run K} {b : Ch K} {f : X.chain ⟶ b} (hf : codim f = 2)
    (F : OneCut f) :
    (ev K).map ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))
      = arr (W_bottomHom b) (bottomHom X.chain ≫ f) := by
  refine ((ev K).map_comp _ _).trans ?_
  rw [h F.1.snd (F.codim_snd hf), h F.1.fst F.2]
  refine (arr_comp (W_bottomHom b) (W_bottomHom F.1.mid) F.1.snd
    (bottomHom X.chain ≫ F.1.fst)).trans ?_
  rw [Category.assoc, F.1.comp]

/-- **The relations of `poly` hold in `Ch K[W⁻¹]`.**  What a presentation theorem adds is that they
*suffice*. -/
theorem ev_src_eq_tgt (h : Reads K) {X Y : Run K} (α : Cell 2 X Y) :
    (ev K).map ((poly K).src (x := runPt X) (y := runPt Y) α)
      = (ev K).map ((poly K).tgt α) := by
  change (ev K).map (readAt α.below α.top
        (readAt rfl (bottomRun_self (topOf α.obj).1) _))
      = (ev K).map (readAt α.below α.top
        (readAt rfl (bottomRun_self (topOf α.obj).1) _))
  rw [ev_readAt, ev_readAt, ev_readAt, ev_readAt,
    ev_cutWord_comp h ((codim_topOf α.obj).trans α.degree_obj),
    ev_cutWord_comp h ((codim_topOf α.obj).trans α.degree_obj)]

end ChainCat.Paper
