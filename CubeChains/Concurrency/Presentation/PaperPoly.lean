import CubeChains.Concurrency.Presentation.BeadOrder
import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Concurrency.Executions.Complement
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/PaperPoly — the polygraph, defined directly

0-cells the runs; cells the **objects**, graded by degree — degree one a 1-cell, degree two a
2-cell.  An object needs no refinement beside it: the merge onto it (`bottomHom`) and its greatest
refinement (`topOf`, the reversal inside every bead) are both functions of it.

    X.chain ──bottomHom──▸ obj ◂──topOf── Y.chain            a cell  X ⟶ Y

Two facts make that the right indexing.  The greatest refinement attains the crossing capacity, so
it is never a merge (`not_W_topOf`) and a cell's refinement crosses; and at degree one it is the
*only* crossing one (`topOf_fst_eq_of_not_W`, from `eq_atomOnes`), so a degree-one object carries
exactly one 1-cell.

`objWords` reads a degree-two object as its two words: `oneCutEquivBool` names the two
factorisations of its greatest refinement, and `cutWord` spells each — of length one or two, which
is why the braid relation runs to three letters a side where commutation runs to two.
-/

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains Equiv

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

/-! ## The greatest refinement out of a run

A refinement of `e` out of a run *is* a run of `⋁e.dims` — the source's classifying map is forced to
`φ ≫ e.map` — and a run of a wedge crosses one permutation per bead (`blockSum`).  The greatest
refinement is the reversal in every bead (`blockTop`): `crossCap` bounds every crossing and the weak
order is graded bead by bead, so nothing else crosses that much. -/

/-- A refinement out of a run, as a run of the target's wedge. -/
def wedgeRun {X : Run K} {e : Ch K} (f : X.chain ⟶ e) : Run (⋁e.dims) :=
  ⟨⟨X.dims, Hom.φ f⟩, X.ones⟩

/-- …and back: the run it refines `e` by, with the refinement. -/
def ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) : Σ X : Run K, X.chain ⟶ e :=
  ⟨⟨⟨r.dims, r.chain.map ≫ e.map⟩, r.ones⟩, ⟨r.chain.map, rfl⟩⟩

@[simp] theorem wedgeRun_ofWedgeRun (e : Ch K) (r : Run (⋁e.dims)) :
    wedgeRun (ofWedgeRun e r).2 = r := rfl

/-- **A refinement out of a run recovers the run** — its source's classifying map is forced. -/
theorem ofWedgeRun_wedgeRun_fst {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    (ofWedgeRun e (wedgeRun f)).1 = X :=
  Run.ext (congrArg (fun m => (⟨X.dims, m⟩ : Ch K)) f.w)

/-- A run refining a chain has the chain's events as its beads. -/
theorem Run.dims_eq_of_hom {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    X.dims = 𝟙^(dimSum e.dims) :=
  List.eq_replicate_iff.mpr
    ⟨by rw [← dimSum_eq_length_of_ones X.ones]; exact dimSum_eq_of_hom f, X.ones⟩

/-- **The crossing permutation of a refinement out of a run**, on the target's own events. -/
noncomputable def runCross {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    Perm (Fin (dimSum e.dims)) := crossPerm (dimSum_eq_of_hom f) f

/-- …read at the base, where the bead order lives. -/
theorem runCross_zHom {X : Run K} {e : Ch K} (f : X.chain ⟶ e)
    (h : dimSum X.dims = dimSum e.dims) :
    crossPerm (a := zObj X.dims) h (zHom (Hom.φ f)) = runCross f :=
  crossPerm_eq_of_φ _ rfl

/-- **A refinement out of a run is one of the target's runs.** -/
theorem runSet_runCross {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    RunSet (zObj e.dims) (dimSum e.dims) (runCross f) :=
  runSet_iff_exists_wedgeHom.mpr
    ⟨X.dims, X.ones, dimSum_eq_of_hom f, Hom.φ f, runCross_zHom f (dimSum_eq_of_hom f)⟩

/-- **The capacity bounds every refinement out of a run.** -/
theorem permLen_runCross_le {X : Run K} {e : Ch K} (f : X.chain ⟶ e) :
    permLen (runCross f) ≤ crossCap e.dims := by
  have hd : dimSum X.dims = dimSum e.dims := dimSum_eq_of_hom f
  have hbound : permLen (crossPerm (a := zObj X.dims) hd (zHom (Hom.φ f))) ≤ crossCap e.dims :=
    permLen_crossPerm_le_crossCap e.dims (zHom (Hom.φ f)) rfl hd
  exact (congrArg permLen (runCross_zHom f hd).symm).trans_le hbound

/-- **Two refinements out of runs that cross alike name one run of the wedge** — a chain map is its
wedge map, and the crossing pins that. -/
theorem wedgeRun_eq_of_runCross_eq {e : Ch K} {X Y : Run K} {f : X.chain ⟶ e} {g : Y.chain ⟶ e}
    (h : runCross f = runCross g) : wedgeRun f = wedgeRun g := by
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
  have hd : dimSum (𝟙^n : List ℕ+) = dimSum e.dims := dimSum_eq_of_hom f
  have hbase : zHom (Hom.φ f) = zHom (Hom.φ g) :=
    hom_ext_of_crossPerm (h := hd)
      ((runCross_zHom f hd).trans (h.trans (runCross_zHom g hd).symm))
  exact Run.ext (congrArg (fun φ => (⟨𝟙^n, φ⟩ : Ch (⋁e.dims))) (congrArg ChainCat.Hom.φ hbase))

/-- The greatest run of a wedge: the reversal in every bead. -/
noncomputable def topWedgeRun (l : List ℕ+) : Run (⋁l) :=
  ⟨wedgeRunChain l (blockTop l), wedgeRunChain_ones l (blockTop l)⟩

/-- **The greatest refinement of a chain out of a run.** -/
noncomputable def topOf (e : Ch K) : Σ X : Run K, X.chain ⟶ e := ofWedgeRun e (topWedgeRun e.dims)

/-- **The run a chain's greatest refinement comes out of.**  The two runs a chain spans:
`bottomRun` crosses nothing, `topRun` crosses as much as the chain allows. -/
noncomputable abbrev topRun (e : Ch K) : Run K := (topOf e).1

/-- …and that refinement. -/
noncomputable abbrev topHom (e : Ch K) : (topRun e).chain ⟶ e := (topOf e).2

/-- **Codimension is degree, out of a run.** -/
theorem codim_topOf (e : Ch K) : codim (topOf e).2 = degree e := by
  change degree e - degree (topOf e).1.chain = degree e
  rw [(isRun_iff_degree_eq_zero _).mp (topOf e).1.property, Nat.sub_zero]

/-- **The greatest refinement crosses the greatest tuple.** -/
theorem runCross_topOf (e : Ch K) : runCross (topOf e).2 = blockSum e.dims (blockTop e.dims) :=
  (runCross_zHom (topOf e).2 (dimSum_eq_of_hom (topOf e).2)).symm.trans
    (crossPerm_wedgeRunChain e.dims (blockTop e.dims) _)

/-- …so it attains the capacity. -/
theorem permLen_runCross_topOf (e : Ch K) :
    permLen (runCross (topOf e).2) = crossCap e.dims :=
  (congrArg permLen (runCross_topOf e)).trans (permLen_blockSum_blockTop e.dims)

/-- **A refinement as long as the capacity crosses what the greatest one crosses** — the weak order
is graded, so the capacity is attained only at the reversals. -/
theorem runCross_eq_of_permLen {X : Run K} {e : Ch K} {f : X.chain ⟶ e}
    (hf : permLen (runCross f) = crossCap e.dims) : runCross f = runCross (topOf e).2 :=
  (eq_blockSum_blockTop_of_permLen e.dims (runSet_runCross f) hf).trans (runCross_topOf e).symm

/-- **…and so it comes out of the same run.** -/
theorem topOf_fst_eq_of_permLen {X : Run K} {e : Ch K} {f : X.chain ⟶ e}
    (hf : permLen (runCross f) = crossCap e.dims) : (topOf e).1 = X :=
  (congrArg (fun r => (ofWedgeRun e r).1)
      (wedgeRun_eq_of_runCross_eq (f := (topOf e).2) (g := f)
        (runCross_eq_of_permLen hf).symm)).trans (ofWedgeRun_wedgeRun_fst f)

/-- **A reversal to make** — a shape with a bead of more than one dimension has capacity. -/
theorem crossCap_ne_zero_of_degree_ne_zero {e : Ch K} (he : degree e ≠ 0) :
    crossCap e.dims ≠ 0 := fun h0 =>
  he ((degree_eq_zero_iff e).mpr (crossCap_eq_zero_iff.mp h0))

/-- **The greatest refinement crosses**, as soon as there is anything to cross: it attains the
capacity, and only an all-edges shape has none.  So the two factorisations a degree-two object reads
spell a relation, not `w = w`. -/
theorem not_W_topOf (e : Ch K) (he : degree e ≠ 0) : ¬ W K (topOf e).2 := fun hW =>
  crossCap_ne_zero_of_degree_ne_zero he
    ((permLen_runCross_topOf e).symm.trans
      ((congrArg permLen
        (crossPerm_eq_one_of_W (dimSum_eq_of_hom (topOf e).2) hW)).trans permLen_one))

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

/-- **At degree one a crossing refinement out of a given run is unique** — `eq_of_not_W_deg_one` at
the base, and a chain map is its wedge map. -/
theorem hom_eq_of_not_W_deg_one {e : Ch K} (he : degree e = 1) {X : Run K} {f g : X.chain ⟶ e}
    (hf : ¬ W K f) (hg : ¬ W K g) : f = g := by
  have h0 : zHom f.φ = zHom g.φ :=
    eq_of_not_W_deg_one X.ones (c := zObj e.dims) he
      (fun h => hf ((W_zHom_iff f).mp h)) (fun h => hg ((W_zHom_iff g).mp h))
  exact hom_ext' (((zHom_φ f.φ).symm.trans (congrArg ChainCat.Hom.φ h0)).trans (zHom_φ g.φ))

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

/-- **A cell is its object** — the three remaining fields are proofs. -/
theorem Cell.ext {n : ℕ} {X Y : Run K} : ∀ {α β : Cell n X Y}, α.obj = β.obj → α = β
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by subst h; rfl

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

/-- **A 1-cell's refinement is any crossing refinement out of its far end** — at degree one there is
only one (`hom_eq_of_not_W_deg_one`). -/
theorem Cell.hom_eq {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    α.hom = f :=
  hom_eq_of_not_W_deg_one α.degree_obj (α.not_W_hom one_ne_zero) hf

/-- **A crossing codimension-one refinement out of a run is a 1-cell** — the object it lands on,
read between the run below it and the run it comes out of. -/
def genOfHom {X : Run K} {e : Ch K} (he : degree e = 1) {f : X.chain ⟶ e} (hf : ¬ W K f) :
    Gen (bottomRun e) X := ⟨e, he, rfl, topOf_fst_eq_of_not_W he hf⟩

@[simp] theorem genOfHom_obj {X : Run K} {e : Ch K} (he : degree e = 1) {f : X.chain ⟶ e}
    (hf : ¬ W K f) : (genOfHom he hf).obj = e := rfl

/-- **A renaming is a merge** — `subst`, and the identity is one. -/
theorem W_eqToHom {a b : Ch K} (h : a = b) : W K (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact MorphismProperty.id_mem _ _

/-- **A merge in front crosses nothing**, so it leaves the crossing permutation alone. -/
theorem runCross_W_comp {X Y : Run K} {e : Ch K} {u : X.chain ⟶ Y.chain} (hu : W K u)
    (f : Y.chain ⟶ e) : runCross (u ≫ f) = runCross f :=
  (crossPerm_comp (dimSum_eq_of_hom (u ≫ f)) u f).trans (by
    rw [crossPerm_eq_one_of_W _ hu, mul_one]
    exact rfl)

/-- **A cell's refinement crosses what the greatest one does** — it *is* the greatest one, read at
the other name for its source. -/
theorem runCross_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    runCross α.hom = runCross (topOf α.obj).2 := runCross_W_comp (W_eqToHom _) _

/-- …so it attains the capacity. -/
theorem permLen_runCross_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    permLen (runCross α.hom) = crossCap α.obj.dims :=
  (congrArg permLen (runCross_hom α)).trans (permLen_runCross_topOf α.obj)

/-- A 0-cell, as a vertex of the generating quiver — `Polygraph.pt` before `poly` exists. -/
abbrev runPt (X : Run K) : GenObj (Gen (K := K)) := ⟨X⟩

/-- A word read at other names for its two ends — the only transport a word here carries. -/
def readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
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

/-- …read between the two runs a 2-cell spans, which is where its boundary lives. -/
noncomputable def cellWords {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    Quiver.Path (runPt X) (runPt Y) :=
  readAt α.below rfl (factorWords α.hom α.codim_hom ε)

/-- **The polygraph**: the runs, the codimension-one cuts out of them, and one relation per
codimension-two refinement out of a run, equating the words its two factorisations read as. -/
noncomputable def poly (K : BPSet) : Polygraph where
  V := Run K
  Gen := Gen
  Rel x y := Cell 2 x.as y.as
  src α := cellWords α false
  tgt α := cellWords α true

/-- **A 2-cell's two words spell one arrow** — `quot_src_tgt`, with the boundary named by
`cellWords` rather than by the structure projection. -/
theorem quot_cellWords {X Y : Run K} (α : Cell 2 X Y) :
    (poly K).quot.map (cellWords α false) = (poly K).quot.map (cellWords α true) :=
  (poly K).quot_src_tgt (x := runPt X) (y := runPt Y) α

end ChainCat.Paper
