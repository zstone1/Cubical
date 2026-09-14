import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.LocFunctor

/-!
# Concurrency/Presentation/DirectPresents — the paper's cells, read straight in the localization

`Rconj u` is the refinement `u` conjugated by the two merges the localization inverts, built out of
`Q` alone with no model of `Ch(K)[W⁻¹]` in between:

    run(c) ──bottomHom──▸ c ──u──▸ d ◂──bottomHom── run(d)

The geometric input is `lift_cutWord`: the word a codimension-one cut spells reads as its conjugate.
Then `paperE` interprets the cells, `Theta` reads the chains back on them, and the two are inverse —
so `Theta` is a localization functor and `paperE` the presentation.

`Q ⋙ chLocOpMap f = (pushforward f).op ⋙ Q` is an *equality*, so this reading is natural in `K` on
the nose, where a reading through a model of the localization is natural only up to isomorphism.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-- The localization functor. -/
noncomputable abbrev Lc (K : BPSet) : (Ch K)ᵒᵖ ⥤ ((W K).op).Localization := ((W K).op).Q

/-- The object a chain names. -/
noncomputable abbrev rho (c : Ch K) : ((W K).op).Localization := (Lc K).obj (op c)

/-- The arrow a refinement names. -/
noncomputable def arr {c d : Ch K} (u : c ⟶ d) : rho d ⟶ rho c := (Lc K).map u.op

theorem arr_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) : arr (v ≫ u) = arr u ≫ arr v :=
  (Lc K).map_comp u.op v.op

@[simp] theorem arr_id (c : Ch K) : arr (𝟙 c) = 𝟙 (rho c) := (Lc K).map_id _

theorem arr_eqToHom {c d : Ch K} (h : c = d) :
    arr (eqToHom h) = eqToHom (congrArg rho h).symm := by
  subst h; simp [arr]

noncomputable instance isIso_arr {c d : Ch K} (u : c ⟶ d) (hu : W K u) : IsIso (arr u) :=
  Localization.inverts (Lc K) ((W K).op) u.op hu

/-- The isomorphism a merge names. -/
noncomputable def mergeIso {c d : Ch K} {m : c ⟶ d} (hm : W K m) : rho d ≅ rho c :=
  @asIso _ _ _ _ (arr m) (isIso_arr m hm)

@[simp] theorem mergeIso_hom {c d : Ch K} {m : c ⟶ d} (hm : W K m) :
    (mergeIso hm).hom = arr m := rfl

/-- **The arrow a refinement names between the runs of its two ends.** -/
noncomputable def Rconj {c d : Ch K} (u : c ⟶ d) :
    rho (bottomRun d).chain ⟶ rho (bottomRun c).chain :=
  (mergeIso (W_bottomHom d)).inv ≫ arr u ≫ arr (bottomHom c)

theorem Rconj_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) :
    Rconj (v ≫ u) = Rconj u ≫ Rconj v := by
  rw [Rconj, Rconj, Rconj, arr_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (arr (bottomHom c)) _ _, ← mergeIso_hom (W_bottomHom c),
    Iso.hom_inv_id, Category.id_comp]

theorem Rconj_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) :
    Rconj u = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_of_W u hu)) := by
  set h := bottomRun_eq_of_W u hu with hh
  have key : eqToHom (congrArg Run.chain h) ≫ (bottomHom c ≫ u) = bottomHom d :=
    eq_of_W ((W K).comp_mem _ _ (W_eqToHom _) ((W K).comp_mem _ _ (W_bottomHom c) hu))
      (W_bottomHom d)
  have harr : arr (bottomHom d)
      = (arr u ≫ arr (bottomHom c)) ≫ eqToHom (congrArg rho (congrArg Run.chain h)).symm := by
    rw [← key, arr_comp, arr_comp, arr_eqToHom]
  rw [Rconj, Iso.inv_comp_eq, mergeIso_hom, harr]
  simp

/-- **The merge below the target carries the conjugate to the refinement.** -/
theorem arr_bottomHom_comp_Rconj {c d : Ch K} (u : c ⟶ d) :
    arr (bottomHom d) ≫ Rconj u = arr u ≫ arr (bottomHom c) := by
  rw [Rconj, ← Category.assoc, ← mergeIso_hom (W_bottomHom d), Iso.hom_inv_id, Category.id_comp]

/-- **…and pins it.** -/
theorem Rconj_eq_of {c d : Ch K} (u : c ⟶ d)
    {t : rho (bottomRun d).chain ⟶ rho (bottomRun c).chain}
    (h : arr (bottomHom d) ≫ t = arr u ≫ arr (bottomHom c)) : t = Rconj u := by
  rw [Rconj, Iso.eq_inv_comp, mergeIso_hom]; exact h

private theorem eqToHom_move {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : eqToHom p.symm ≫ f ≫ eqToHom q = g) :
    f = eqToHom p ≫ g ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h

/-- **Two merges into one chain name one arrow**, up to the renaming of their sources. -/
theorem arr_eq_of_W {a r r' : Ch K} {m : r ⟶ a} {m' : r' ⟶ a} (hm : W K m) (hm' : W K m')
    (h : r = r') : arr m = arr m' ≫ eqToHom (congrArg rho h).symm := by
  subst h
  rw [eq_of_W hm hm']
  simp

/-! ## The conjugate, indexed by the base

The run below a chain is `eltRep` of the 0-cell it names, so a conjugate indexed by
`(chCutPoly K).V` avoids the renaming `chV (vChain z) = z` at every step; `Rconj_eq_zConj` pays it
once. -/

/-- **The arrow a refinement names between the runs of its two ends**, at a 0-cell of the base. -/
noncomputable def zConj {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) :
    rho (vChain (eltRep a)) ⟶ rho (vChain (eltRep b)) :=
  (mergeIso (W_runMergeK a)).inv ≫ arr u ≫ arr (runMergeK b)

/-- **The merge below the source carries the conjugate to the refinement**, and pins it. -/
theorem arr_runMergeK_comp_zConj {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) :
    arr (runMergeK a) ≫ zConj u = arr u ≫ arr (runMergeK b) := by
  rw [zConj, ← Category.assoc, ← mergeIso_hom (W_runMergeK a), Iso.hom_inv_id, Category.id_comp]

theorem zConj_eq_of {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a)
    {t : rho (vChain (eltRep a)) ⟶ rho (vChain (eltRep b))}
    (h : arr (runMergeK a) ≫ t = arr u ≫ arr (runMergeK b)) : t = zConj u := by
  rw [zConj, Iso.eq_inv_comp, mergeIso_hom]; exact h

theorem zConj_comp {a b c : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (v : vChain c ⟶ vChain b) :
    zConj (v ≫ u) = zConj u ≫ zConj v :=
  (zConj_eq_of (v ≫ u) (by
    rw [← Category.assoc, arr_runMergeK_comp_zConj, Category.assoc,
      arr_runMergeK_comp_zConj, arr_comp, Category.assoc])).symm

theorem zConj_of_W {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (hu : W K u) :
    zConj u = eqToHom (congrArg (fun z : (chCutPoly K).V => rho (vChain z))
      (eltRep_eq_of_W u hu).symm) :=
  (zConj_eq_of u (by
    rw [← arr_comp, arr_eq_of_W ((W K).comp_mem _ _ (W_runMergeK b) hu) (W_runMergeK a)
      (congrArg vChain (eltRep_eq_of_W u hu))])).symm

/-- **The run below a chain, read at the 0-cell it names.** -/
theorem bottomRun_vChain (z : (chCutPoly K).V) :
    (bottomRun (vChain z)).chain = vChain (eltRep z) :=
  congrArg Run.chain (bottomRun_runOfV z)

/-- **…so the two conjugates agree**, the renaming `chV (vChain z) = z` being the whole
difference. -/
theorem Rconj_eq_zConj {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) :
    eqToHom (congrArg rho (bottomRun_vChain a)) ≫ zConj u
        ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm = Rconj u := by
  refine Rconj_eq_of u ?_
  have hA : arr (bottomHom (vChain a)) ≫ eqToHom (congrArg rho (bottomRun_vChain a))
      = arr (runMergeK a) := by
    rw [arr_eq_of_W (W_bottomHom (vChain a)) (W_runMergeK a) (bottomRun_vChain a)]
    exact ((Category.assoc _ _ _).trans (congrArg (fun t => arr (runMergeK a) ≫ t)
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _)))).trans (Category.comp_id _)
  have hB : arr (runMergeK b) ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm
      = arr (bottomHom (vChain b)) :=
    (arr_eq_of_W (W_bottomHom (vChain b)) (W_runMergeK b) (bottomRun_vChain b)).symm
  calc arr (bottomHom (vChain a)) ≫ eqToHom (congrArg rho (bottomRun_vChain a)) ≫ zConj u
          ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm
      = (arr (bottomHom (vChain a)) ≫ eqToHom (congrArg rho (bottomRun_vChain a)))
          ≫ (zConj u ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm) :=
        (Category.assoc _ _ _).symm
    _ = arr (runMergeK a) ≫ (zConj u ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm) := by
        rw [hA]
    _ = (arr (runMergeK a) ≫ zConj u) ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm :=
        (Category.assoc _ _ _).symm
    _ = (arr u ≫ arr (runMergeK b)) ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm := by
        rw [arr_runMergeK_comp_zConj]
    _ = arr u ≫ (arr (runMergeK b) ≫ eqToHom (congrArg rho (bottomRun_vChain b)).symm) :=
        Category.assoc _ _ _
    _ = arr u ≫ arr (bottomHom (vChain b)) := by rw [hB]

/-! ## The interpretation -/

/-- The arrow a cell names. -/
noncomputable def cellRconj {n : ℕ} {X Y : Run K} (α : Cell n X Y) : rho X.chain ⟶ rho Y.chain :=
  eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj α.hom
    ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y))

/-- **The interpretation of the paper's cells** in the localization. -/
noncomputable def paperPre' : GenObj (Gen (K := K)) ⥤q ((W K).op).Localization where
  obj X := rho X.as.chain
  map α := cellRconj α

/-! ## Essential surjectivity -/

theorem essSurj_paperPre' : (Paths.lift (paperPre' (K := K))).EssSurj where
  mem_essImage c :=
    ⟨runPt (bottomRun ((Lc K).objPreimage c).unop),
      ⟨(mergeIso (W_bottomHom ((Lc K).objPreimage c).unop)).symm
        ≪≫ (Lc K).objObjPreimageIso c⟩⟩

/-! ## A word of the collapse, read in the localization

`runPre` reads a kept cut as the degree-one object it lands on, so substituting each 1-cell by its
atom word and reading those on the runs interprets the whole collapse. -/

/-- Inserting a cancelling triple of renamings. -/
private theorem insert_cancel {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (s : X₃ ⟶ X₄) (q : X₄ ⟶ X₅) {s' : X₃ ⟶ X₅}
    (hs : s ≫ q = s') (m₁ : X₂ ⟶ Y₁) (m₂ : Y₁ ⟶ Y₂) (m₃ : Y₂ ⟶ X₂)
    (h : m₁ ≫ m₂ ≫ m₃ = 𝟙 X₂) :
    p ≫ (f ≫ g ≫ s) ≫ q = (p ≫ (f ≫ m₁) ≫ m₂) ≫ (m₃ ≫ g ≫ s') := by
  subst hs
  have key : (m₁ ≫ m₂ ≫ m₃) ≫ g ≫ s ≫ q = g ≫ s ≫ q := by rw [h, Category.id_comp]
  simp only [Category.assoc] at key ⊢
  rw [key]

/-- A renaming on either side of an arrow that is itself one. -/
private theorem eqToHom_sandwich {C : Type*} [Category C] {A B D E : C} (h₁ : A = B)
    {f : B ⟶ D} {h : B = D} (hf : f = eqToHom h) (h₂ : D = E) (hAE : A = E) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom hAE := by
  subst hf; rw [eqToHom_trans, eqToHom_trans]

/-- Renaming both sides of an arrow does not see which arrow it is. -/
private theorem sandwich_congr {C : Type*} [Category C] {A B D E : C} (h₁ : A = B) (h₂ : D = E)
    {f g : B ⟶ D} (h : f = g) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by rw [h]

/-- Collapsing a sandwich of renamings onto the arrow inside it. -/
private theorem sandwich_collapse {C : Type*} [Category C] {A A₁ A₂ B₀ B₁ B₂ B₃ : C}
    (p : A = A₁) (q : A₁ = A₂) {f : A₂ ⟶ B₀} (v : B₀ = B₁) (r : B₁ = B₂) (s : B₂ = B₃)
    (hA : A = A₂) (hB : B₀ = B₃) :
    eqToHom p ≫ (eqToHom q ≫ (f ≫ eqToHom v) ≫ eqToHom r) ≫ eqToHom s
      = eqToHom hA ≫ f ≫ eqToHom hB := by
  subst p; subst q; subst v; subst r; subst s; simp

/-- **A word of the collapse, read in the localization**: each letter spelled by its atom word, and
each atom read as the cell it is. -/
noncomputable def runLoc (K : BPSet) : (chCollapse K).poly.Word ⥤ ((W K).op).Localization :=
  (runAtomWords K) ⋙ Paths.lift (runPre ⋙q paperPre' (K := K))

/-- **A kept cut reads as the cell it is.** -/
theorem runLoc_cell_kept {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) (hg : RunCut g) :
    (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = cellRconj (genOfRunCut g hg) := by
  have h1 : (runAtomWords K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = (keptCell (P := (chCollapse K).poly) RunCut g hg).toPath := by
    refine Eq.trans (Paths.lift_toPath (runAtomPre K) _) ?_
    exact subPre_map_kept (P := (chCollapse K).poly) RunCut runCellWord all_runCellWord
      runCellWord_self (keptCell (P := (chCollapse K).poly) RunCut g hg)
  refine Eq.trans (congrArg (Paths.lift (runPre ⋙q paperPre' (K := K))).map h1) ?_
  exact Paths.lift_toPath (runPre ⋙q paperPre' (K := K)) _

/-- **A cell's arrow, at other names for its two runs.** -/
theorem cellRconj_cellCongr {n : ℕ} {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (β : Cell n X Y) :
    cellRconj (cellCongr (Cell n) hx hy β)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) hx).symm ≫ cellRconj β
        ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) hy) := by
  subst hx; subst hy
  rw [cellCongr_self]
  simp

/-- **A 1-cell's arrow is any crossing refinement out of its far end, conjugated.** -/
theorem cellRconj_of_hom {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    cellRconj α = eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj f
      ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y)) := by
  rw [cellRconj, Cell.hom_eq α hf]

/-- **A kept cut's cell is its bead cut**, conjugated onto the runs of its two ends. -/
theorem cellRconj_genOfRunCut {U V : (chCollapse K).V} (g : (chCollapse K).Gen U V)
    (hg : RunCut g) :
    cellRconj (genOfRunCut g hg)
      = eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_dom).symm
        ≫ zConj (chCutHom g.gen)
        ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_cod) := by
  rw [genOfRunCut, cellRconj_cellCongr,
    cellRconj_of_hom _ (not_W_chCutHom g.gen g.not_mem)]
  refine Eq.trans (sandwich_congr _ _
    (sandwich_congr _ _ (Rconj_eq_zConj (chCutHom g.gen)).symm)) ?_
  exact Eq.trans (sandwich_congr _ _ (eqToHom_nest _ _ _ _ rfl
      (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) hg)))
    (eqToHom_nest _ _ _ _ _ _)

/-! ## A climb, read in the localization

The two legs out of an ascent's atom shape are a merge and the atom itself, and both land on the
base, so `zConj`'s contravariance telescopes a climb into one conjugated refinement. -/

/-- **Two refinements of one shape, out of chains that agree, name one arrow.** -/
theorem zConj_eq_of_eq {c b₁ b₂ : (chCutPoly K).V} (h : b₁ = b₂) {u : vChain b₁ ⟶ vChain c}
    {u' : vChain b₂ ⟶ vChain c} (hbase : baseHom u = eqToHom (congrArg shOf h) ≫ baseHom u') :
    zConj u ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) (congrArg eltRep h))
      = zConj u' := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hbase
  rw [hom_ext_baseHom hbase, eqToHom_refl, Category.comp_id]

/-- The arrow a run over a chain names, out of the chain's own run. -/
noncomputable def zConjAt {N : ℕ} {z : (chCutPoly K).V} (hz : dimSum (shOf z).dims = N)
    (σ : RunPerm N z) :
    rho (vChain (runObj (runBot z hz)).1) ⟶ rho (vChain (runObj σ).1) :=
  eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) (runObj_runBot z hz))
    ≫ zConj (legLift σ.arr)
    ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
        (eltRep_eq_self (N := N) (c := eltRestrict z σ.arr) rfl))

theorem zConjAt_bot {N : ℕ} {z : (chCutPoly K).V} (hz : dimSum (shOf z).dims = N) :
    zConjAt hz (runBot z hz) = 𝟙 (rho (vChain (runObj (runBot z hz)).1)) :=
  (eqToHom_sandwich _ (zConj_of_W _ (W_legLift (W_runBot_arr hz))) _ rfl).trans
    (eqToHom_refl _ _)

/-- **A kept cut of the collapse reads as its bead cut, conjugated.** -/
theorem runLoc_gen_kept {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) (hg : RunCut g) :
    (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_dom).symm
        ≫ zConj (chCutHom g.gen)
        ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_cod) :=
  (runLoc_cell_kept g hg).trans (cellRconj_genOfRunCut g hg)

/-- **One atom appends to the conjugated refinement below it.** -/
theorem zConjAt_cons {N : ℕ} {z : (chCutPoly K).V} (hz : dimSum (shOf z).dims = N)
    {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    zConjAt hz b = zConjAt hz a
      ≫ (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath := by
  have hb : zConj (legLift (ascLeg e)) ≫ zConj (ascCut e)
      ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) (congrArg eltRep
        (congrArg (eltRestrict z) (atomOnes_ascLeg e)))) = zConj (legLift b.arr) := by
    rw [← Category.assoc, ← zConj_comp]
    refine zConj_eq_of_eq (congrArg (eltRestrict z) (atomOnes_ascLeg e)) ?_
    rw [baseHom_comp, baseHom_legLift, ascCut, baseHom_liftOf, baseHom_legLift]
    exact atomOnes_ascLeg e
  have ha : zConj (legLift a.arr) = zConj (legLift (ascLeg e))
      ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
        (eltRep_eq_of_W (ascMerge e) (W_ascMerge e)).symm) := by
    rw [show legLift a.arr = ascMerge e ≫ legLift (ascLeg e) from
      hom_ext_baseHom (by
        rw [baseHom_comp, baseHom_legLift, baseHom_legLift, ascMerge, baseHom_liftOf]
        exact (mergeOnes_ascLeg e).symm), zConj_comp, zConj_of_W (ascMerge e) (W_ascMerge e)]
  have hgen : (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath
      = eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
          (ascAtom e).rep_dom).symm ≫ zConj (ascCut e)
        ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) (ascAtom e).rep_cod) :=
    runLoc_gen_kept (ascAtom e) (runCut_ascAtom e)
  refine Eq.trans ?_ (congrArg (fun t => zConjAt hz a ≫ t) hgen).symm
  refine Eq.trans (sandwich_congr _ _ hb.symm) (Eq.trans ?_ (congrArg (fun t => t
    ≫ (eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
        (ascAtom e).rep_dom).symm ≫ zConj (ascCut e)
      ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) (ascAtom e).rep_cod)))
    (sandwich_congr _ _ ha)).symm)
  refine insert_cancel _ _ _ _ _ (eqToHom_trans _ _) _ _ _ ?_
  exact (congrArg (fun t => eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
      (eltRep_eq_of_W (ascMerge e) (W_ascMerge e)).symm) ≫ t) (eqToHom_trans _ _)).trans
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- **A climb is the refinement it performs**, conjugated onto the chain's own run. -/
theorem runLoc_climbPath {N : ℕ} {z : (chCutPoly K).V} (hz : dimSum (shOf z).dims = N) :
    ∀ {σ : RunPerm N z} (R : Climb (runDescents N z).perm (runBot z hz) σ),
      (runLoc K).map (climbPath R) = zConjAt hz σ
  | _, .nil => ((runLoc K).map_id _).trans (zConjAt_bot hz).symm
  | _, .cons R e =>
      (((runLoc K).map_comp (climbPath R)
          (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath).trans
        (congrArg (fun t => t ≫ (runLoc K).map
          (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath)
          (runLoc_climbPath hz R))).trans (zConjAt_cons hz e).symm

/-! ## Every 1-cell of the collapse, read in the localization -/

/-- A renaming that renames nothing. -/
private theorem sandwich_refl {C : Type*} [Category C] {A B : C} (p : A = A) (q : B = B)
    (f : A ⟶ B) : eqToHom p ≫ f ≫ eqToHom q = f := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A renaming cancelled against its inverse. -/
private theorem cancel_eqToHom {C : Type*} [Category C] {A A' B : C} (p : A = A') (f : A ⟶ B) :
    eqToHom p ≫ eqToHom p.symm ≫ f = f := by subst p; simp

/-- An arrow inverse to a renaming is the renaming back. -/
private theorem eq_eqToHom_symm {C : Type*} [Category C] {A B : C} (p : A = B) {f : B ⟶ A}
    (h : eqToHom p ≫ f = 𝟙 A) : f = eqToHom p.symm := by subst p; simpa using h

/-- Four nested renamings are one. -/
private theorem collapse4 {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₄ B₃ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) (a₂ : A₂ = A₃) (a₃ : A₃ = A₄) {f : A₄ ⟶ B₄}
    (b₃ : B₄ = B₃) (b₂ : B₃ = B₂) (b₁ : B₂ = B₁) (b₀ : B₁ = B₀)
    (p : A₀ = A₄) (q : B₄ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ (eqToHom a₂ ≫ (eqToHom a₃ ≫ f ≫ eqToHom b₃)
        ≫ eqToHom b₂) ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ f ≫ eqToHom q := by
  subst a₀; subst a₁; subst a₂; subst a₃; subst b₃; subst b₂; subst b₁; subst b₀; simp

/-- **The top of a 1-cell's climb is its own cut**, the merge onto the target's run contributing
nothing. -/
theorem zConj_genTop {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    zConj (legLift ((genTop g).arr)) = zConj (liftOf (genCut g) (map_genCut g))
      ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w))
          (eltRep_eq_of_W (genTopMerge g) (W_genTopMerge g)).symm) := by
  rw [show legLift ((genTop g).arr) = genTopMerge g ≫ liftOf (genCut g) (map_genCut g) from
    hom_ext_baseHom (by
      rw [baseHom_comp, baseHom_legLift, genTopMerge, baseHom_liftOf, baseHom_liftOf]
      exact arr_runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)),
    zConj_comp, zConj_of_W (genTopMerge g) (W_genTopMerge g)]

/-- **A 1-cell and its atom word read alike** — the substitution is the identity on kept words. -/
theorem runLoc_runCellWord {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = (runLoc K).map (runCellWord g) := by
  have h0 : keptWord (P := (chCollapse K).poly) RunCut (runCellWord g) (all_runCellWord g)
      = (runAtomWords K).map (runCellWord g) :=
    (subWords_of_all (P := (chCollapse K).poly) RunCut (word_all := all_runCellWord)
      runCellWord_self (runCellWord g) (all_runCellWord g)).symm
  have h : (runAtomWords K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = (runAtomWords K).map (runCellWord g) :=
    (Paths.lift_toPath (runAtomPre K) _).trans h0
  exact congrArg (Paths.lift (runPre ⋙q paperPre' (K := K))).map h

/-- **Every 1-cell of the collapse reads as its bead cut, conjugated onto the runs of its two
ends** — a kept cut by itself, any other by the climb its word spells. -/
theorem runLoc_gen {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    (runLoc K).map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_dom).symm
        ≫ zConj (chCutHom g.gen)
        ≫ eqToHom (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_cod) := by
  by_cases h : RunCut g
  · exact runLoc_gen_kept g h
  · rw [runLoc_runCellWord, runCellWord, dif_neg h]
    refine Eq.trans (Paths.map_cellCongr₂ (runLoc K) _ _ _) ?_
    refine Eq.trans (sandwich_congr _ _ ((runLoc_climbPath rfl (genClimb g)).trans
      (sandwich_congr _ _ (zConj_genTop g)))) ?_
    exact sandwich_collapse _ _ _ _ _
      (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_dom).symm
      (congrArg (fun w : (chCutPoly K).V => rho (vChain w)) g.rep_cod)

/-- **A crossing codimension-one refinement is the bead cut of the 1-cell it names.** -/
theorem chCutHom_chGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) (hW : ¬ W K u) :
    chCutHom (chGenOf u hu hW).gen = u := hom_ext_baseHom rfl

/-! ## The word a cut reads is its conjugate

This is the one geometric input the reading needs: `cutWord` is the contraction's own word for the
bead cut, and the climb it spells performs that cut. -/

/-- **The word a codimension-one refinement reads is its conjugate.** -/
theorem lift_cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (Paths.lift (paperPre' (K := K))).map (cutWord u hu) = Rconj u := by
  by_cases hW : W K u
  · have hc : cutWord u hu = readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil := dif_pos hW
    rw [hc, Rconj_of_W u hW, readAt]
    refine Eq.trans (Paths.map_cellCongr₂ (Paths.lift (paperPre' (K := K))) _ _ _) ?_
    exact eqToHom_sandwich _ (((Paths.lift (paperPre' (K := K))).map_id _).trans
      (eqToHom_refl _ rfl).symm) _ _
  · have hc : cutWord u hu = runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut
        (runCellWord (chGenOf u hu hW)) (all_runCellWord _)) := dif_neg hW
    rw [hc]
    refine Eq.trans (Paths.lift_mapPath runPre (paperPre' (K := K)) _) ?_
    have h0 : keptWord (P := (chCollapse K).poly) RunCut (runCellWord (chGenOf u hu hW))
          (all_runCellWord _)
        = (runAtomWords K).map (runCellWord (chGenOf u hu hW)) :=
      (subWords_of_all (P := (chCollapse K).poly) RunCut (word_all := all_runCellWord)
        runCellWord_self _ (all_runCellWord _)).symm
    refine Eq.trans (congrArg (Paths.lift (runPre ⋙q paperPre' (K := K))).map h0) ?_
    refine Eq.trans (runLoc_runCellWord (chGenOf u hu hW)).symm ?_
    refine Eq.trans (runLoc_gen (chGenOf u hu hW)) ?_
    rw [chCutHom_chGenOf u hu hW]
    exact sandwich_refl _ _ _

/-! ## Soundness -/

/-- **A factorisation's word names the refinement**, whichever factorisation it is. -/
theorem lift_factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2) (ε : Bool) :
    (Paths.lift (paperPre' (K := K))).map (factorWords f hf ε)
      = Rconj f ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self X)) := by
  set F := (oneCutEquivBool f hf).symm ε with hF
  change (Paths.lift (paperPre' (K := K))).map
      (readAt rfl (bottomRun_self X)
        ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))) = _
  rw [readAt, Paths.map_cellCongr, Paths.lift_map_comp, lift_cutWord, lift_cutWord]
  exact congrArg (fun t => t ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain)
      (bottomRun_self X)))
    ((Rconj_comp F.1.fst F.1.snd).symm.trans (congrArg (fun u : X.chain ⟶ b => Rconj u) F.1.comp))

/-- **The paper's 2-cells are sound** — both sides name the object's own greatest refinement. -/
theorem sound_paperPre {x y : GenObj (Gen (K := K))} (α : (poly K).Rel x y) :
    (Paths.lift (paperPre' (K := K))).map ((poly K).src α)
      = (Paths.lift (paperPre' (K := K))).map ((poly K).tgt α) := by
  change (Paths.lift (paperPre' (K := K))).map (cellWords α false)
    = (Paths.lift (paperPre' (K := K))).map (cellWords α true)
  rw [cellWords, cellWords, readAt, readAt, Paths.map_cellCongr₂, Paths.map_cellCongr₂,
    lift_factorWords, lift_factorWords]

/-- **The paper's polygraph, interpreted in `Ch(K)[W⁻¹]`** — the comparison itself, with no model
of the localization in between. -/
noncomputable def paperE (K : BPSet) : (poly K).presented ⥤ ((W K).op).Localization :=
  Polygraph.desc (paperPre' (K := K)) sound_paperPre

theorem paperE_quot {x y : GenObj (Gen (K := K))} (w : Quiver.Path x y) :
    (paperE K).map ((poly K).quot.map w) = (Paths.lift (paperPre' (K := K))).map w := rfl

/-! ## A refinement, read on the paper's cells

`readCut_congr` says a word of bead cuts is pinned by the refinement it performs, so every
refinement names one arrow, contravariantly. -/

/-- The object a chain names on the paper's cells. -/
noncomputable abbrev subPt' (c : Ch K) : (poly K).presented :=
  (readCut K).obj ((chCutPoly K).pt (chV c))

/-- **The arrow a refinement names there.** -/
noncomputable def cutArrow {c d : Ch K} (f : c ⟶ d) : subPt' d ⟶ subPt' c :=
  (readCut K).map (chPath (a := chV c) (b := chV d) f)

theorem cutArrow_comp {c d e : Ch K} (f : c ⟶ d) (g : d ⟶ e) :
    cutArrow (f ≫ g) = cutArrow g ≫ cutArrow f := by
  have h1 : cutArrow (f ≫ g) = (readCut K).map
      ((chPath (a := chV d) (b := chV e) g).comp (chPath (a := chV c) (b := chV d) f)) := by
    refine readCut_congr ?_
    rw [ev_chPath, Prefunctor.mapPath_comp, Cut.ev_comp, ev_chPath, ev_chPath]
    rfl
  rw [h1]
  exact (readCut K).map_comp _ _

theorem cutArrow_id (c : Ch K) : cutArrow (𝟙 c) = 𝟙 (subPt' c) := by
  have h1 : cutArrow (𝟙 c) = (readCut K).map
      (Quiver.Path.nil : Quiver.Path ((chCutPoly K).pt (chV c)) ((chCutPoly K).pt (chV c))) := by
    refine readCut_congr ?_
    rw [ev_chPath, Prefunctor.mapPath_nil, Cut.ev_nil]
    rfl
  rw [h1]
  exact (readCut K).map_id _

/-- **The paper's polygraph, receiving the chains**, contravariantly: a chain names the run below it
and a refinement the word its cuts spell. -/
noncomputable def Theta (K : BPSet) : (Ch K)ᵒᵖ ⥤ (poly K).presented where
  obj c := subPt' c.unop
  map u := cutArrow u.unop
  map_id c := cutArrow_id c.unop
  map_comp u v := cutArrow_comp v.unop u.unop

/-! ## …and the same reading in the localization

`cutLoc` is `Theta` followed by the paper's interpretation, and a word of bead cuts reads there as
the conjugate of the refinement it performs — one letter at a time. -/

/-- A word of bead cuts, read in the localization. -/
noncomputable def cutLoc (K : BPSet) : (chCutPoly K).Word ⥤ ((W K).op).Localization :=
  (chCollapse K).words ⋙ runLoc K

/-- **A bead cut reads as its own conjugate** — a merge as a renaming, any other as its 1-cell. -/
theorem cutLoc_cell {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (cutLoc K).map (Polygraph.cell e).toPath = zConj (chCutHom e) := by
  have h1 : (cutLoc K).map (Polygraph.cell e).toPath
      = (runLoc K).map ((chCollapse K).cell (Polygraph.cell e)) :=
    congrArg (runLoc K).map (Paths.lift_toPath (chCollapse K).pre (Polygraph.cell e))
  rw [h1]
  by_cases he : chCutPicked K e
  · rw [(chCollapse K).cell_of_S (Polygraph.cell e) he,
      zConj_of_W (chCutHom e)
        ((W_baseHom_iff (chCutHom e)).mp ((merge_iff (Cut.genHom e.1)).mp he).1)]
    refine Eq.trans (Paths.map_cellCongr₂ (runLoc K) _ _ _) ?_
    exact eqToHom_sandwich _ (((runLoc K).map_id _).trans (eqToHom_refl _ rfl).symm) _ _
  · rw [(chCollapse K).cell_of_not_S (Polygraph.cell e) he]
    refine Eq.trans (runLoc_gen ((chCollapse K).genCell (Polygraph.cell e) he)) ?_
    exact sandwich_refl _ _ _

/-- **A word of bead cuts reads as the conjugate of the refinement it performs.** -/
theorem cutLoc_word {z : (chCutPoly K).V} : ∀ {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt z) v) {f : vChain v.as ⟶ vChain z}
    (_hf : baseHom f = Cut.ev ((chProj K).mapPath w)), (cutLoc K).map w = zConj f := by
  intro v w
  induction w with
  | nil =>
      intro f hf
      obtain rfl : f = 𝟙 (vChain z) := hom_ext_baseHom (by
        rw [hf, Prefunctor.mapPath_nil, Cut.ev_nil]; rfl)
      refine Eq.trans ((cutLoc K).map_id ((chCutPoly K).pt z)) ?_
      rw [zConj_of_W _ (MorphismProperty.id_mem _ _)]
      exact (eqToHom_refl _ _).symm
  | @cons m v w e ih =>
      intro f hf
      obtain rfl : f = chCutHom e ≫ liftOf (Cut.ev ((chProj K).mapPath w)) (map_ev w) :=
        hom_ext_baseHom (by
          rw [hf, baseHom_comp, baseHom_liftOf, Prefunctor.mapPath_cons, Cut.ev_cons]
          rfl)
      refine Eq.trans ((cutLoc K).map_comp w (Polygraph.cell e).toPath) ?_
      rw [ih (f := liftOf (Cut.ev ((chProj K).mapPath w)) (map_ev w)) rfl, cutLoc_cell e,
        zConj_comp]
      rfl

/-- **The paper's reading of a word of bead cuts is the reading in the localization.** -/
theorem paperE_readCut {x y : GenObj (chCutPoly K).Gen} (w : Quiver.Path x y) :
    (paperE K).map ((readCut K).map w) = (cutLoc K).map w :=
  Paths.lift_mapPath runPre (paperPre' (K := K)) _

/-- **…so the paper reads a refinement as its conjugate.** -/
theorem paperE_Theta {c d : Ch K} (u : c ⟶ d) :
    (paperE K).map ((Theta K).map u.op) = Rconj u :=
  (paperE_readCut (chPath (a := chV c) (b := chV d) u)).trans
    (cutLoc_word _ (ev_chPath (a := chV c) (b := chV d) u).symm)

/-! ## The merges become isomorphisms

A merge's cut word is spelled out of the picked letters, and each of those reads as a renaming. -/

/-- **A word of picked letters reads as a renaming.** -/
theorem readCut_of_all_picked : ∀ {x y : GenObj (chCutPoly K).Gen} (w : Quiver.Path x y)
    (_hw : Quiver.Path.All (fun ⦃_ _⦄ e => chCutPicked K e) w),
    ∃ h : (readCut K).obj x = (readCut K).obj y, (readCut K).map w = eqToHom h := by
  intro x y w
  induction w with
  | nil => intro _; exact ⟨rfl, ((readCut K).map_id _).trans (eqToHom_refl _ rfl).symm⟩
  | @cons m v w e ih =>
      intro hw
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff w (Polygraph.cell e)).mp hw
      obtain ⟨hx, hxw⟩ := ih h₀
      have hobj : (readCut K).obj m = (readCut K).obj v :=
        congrArg (readColl K).obj ((chCollapse K).repObj_eq_of_S (Polygraph.cell e) he)
      refine ⟨hx.trans hobj, ?_⟩
      refine Eq.trans ((readCut K).map_comp w (Polygraph.cell e).toPath) ?_
      rw [hxw]
      refine Eq.trans (congrArg (fun t => eqToHom hx ≫ t) (cutArr_merge e he hobj)) ?_
      exact eqToHom_trans _ _

/-- **A merge names a renaming.** -/
theorem cutArrow_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    ∃ h : subPt' d = subPt' c, cutArrow m = eqToHom h :=
  readCut_of_all_picked _ (all_chPath_of_W (a := chV c) (b := chV d) m hm)

/-- **…and the paper's polygraph inverts them.** -/
theorem Theta_inverts : ((W K).op).IsInvertedBy (Theta K) := by
  rintro ⟨d⟩ ⟨c⟩ u hu
  obtain ⟨h, hu'⟩ := cutArrow_of_W u.unop hu
  rw [show (Theta K).map u = eqToHom h from hu']
  exact ⟨⟨eqToHom h.symm, (eqToHom_trans _ _).trans (eqToHom_refl _ _),
    (eqToHom_trans _ _).trans (eqToHom_refl _ _)⟩⟩

/-! ## …so the paper's reading is a localization

`Theta ⋙ paperE ≅ Q` is the merge below each chain, so the descent of `Theta` along `Q` and the
paper's reading are mutually inverse. -/

/-- **The paper reads a chain as the run below it.** -/
noncomputable def ThetaIso (K : BPSet) : Theta K ⋙ paperE K ≅ ((W K).op).Q :=
  NatIso.ofComponents (fun c => (mergeIso (W_bottomHom c.unop)).symm) (by
    rintro ⟨d⟩ ⟨c⟩ u
    change (paperE K).map ((Theta K).map u.unop.op) ≫ (mergeIso (W_bottomHom c)).inv
      = (mergeIso (W_bottomHom d)).inv ≫ arr u.unop
    rw [paperE_Theta u.unop, Iso.comp_inv_eq, Rconj, mergeIso_hom]
    exact (Category.assoc _ _ _).symm)

/-- The descent of the paper's reading of the chains along the localization. -/
noncomputable abbrev Phi (K : BPSet) : ((W K).op).Localization ⥤ (poly K).presented :=
  Localization.Construction.lift (Theta K) Theta_inverts

theorem Q_comp_Phi (K : BPSet) : ((W K).op).Q ⋙ Phi K = Theta K :=
  Localization.Construction.fac _ _

/-- **Reading back, then reading, is the identity on `Ch(K)[W⁻¹]`.** -/
noncomputable def PhiPaperIso (K : BPSet) : Phi K ⋙ paperE K ≅ 𝟭 (((W K).op).Localization) :=
  Localization.liftNatIso ((W K).op).Q ((W K).op) (Theta K ⋙ paperE K) (((W K).op).Q)
    (Phi K ⋙ paperE K) (𝟭 _) (ThetaIso K)

/-! ## …and the other way round

A 1-cell of the paper's polygraph is a crossing codimension-one cut, so its word is its own letter;
that is what makes reading and reading back the identity on the presented category. -/

/-- **A codimension-one refinement's cut word is its own letter.** -/
theorem cutArrow_eq_cutArr {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    cutArrow u = cutArr (cutGenOf u hu) := by
  refine readCut_congr ?_
  rw [ev_chPath, Prefunctor.mapPath_toPath]
  exact (Category.comp_id _).symm

/-- **…so the paper reads it as the word that cut spells.** -/
theorem cutArrow_eq_cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    cutArrow u = (poly K).quot.map (cutWord u hu) :=
  (cutArrow_eq_cutArr u hu).trans (congrArg (poly K).quot.map (readWords_toPath u hu))

/-- A 1-cell read at other names for its ends, as a word. -/
private theorem toPath_cellCongr {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y') (α : Gen X Y) :
    (Polygraph.cell (P := poly K) (cellCongr (Cell 1) hx hy α)).toPath
      = cellCongr Quiver.Path (congrArg runPt hx) (congrArg runPt hy)
          (Polygraph.cell (P := poly K) α).toPath := by
  subst hx; subst hy; rfl

/-- **A 1-cell's own refinement spells that 1-cell.** -/
theorem cutWord_hom {X Y : Run K} (α : Gen X Y) :
    cutWord α.hom α.codim_hom
      = readAt α.below.symm (bottomRun_self Y).symm (Polygraph.cell (P := poly K) α).toPath := by
  have hW : ¬ W K α.hom := α.not_W_hom one_ne_zero
  have hc : cutWord α.hom α.codim_hom = runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut
      (runCellWord (chGenOf α.hom α.codim_hom hW)) (all_runCellWord _)) := dif_neg hW
  have hg : RunCut (chGenOf α.hom α.codim_hom hW) := eltRep_chV Y
  have hcell : genOfRunCut (chGenOf α.hom α.codim_hom hW) hg
      = cellCongr (Cell 1) α.below.symm (bottomRun_self Y).symm α :=
    Cell.ext ((obj_genOfRunCut _ hg).trans (cellCongr_const (F := Cell 1) Cell.obj _ _ α).symm)
  have hall : Quiver.Path.All (V := GenObj (chCollapse K).poly.Gen) (fun ⦃_ _⦄ e => RunCut e)
      (Polygraph.cell (P := (chCollapse K).poly) (chGenOf α.hom α.codim_hom hW)).toPath := by
    simpa using hg
  have hkw : keptWord (P := (chCollapse K).poly) RunCut
        (runCellWord (chGenOf α.hom α.codim_hom hW)) (all_runCellWord _)
      = (keptCell (P := (chCollapse K).poly) RunCut _ hg).toPath :=
    (keptWord_congr (P := (chCollapse K).poly) RunCut (runCellWord_self _ hg)
        (all_runCellWord _) hall).trans
      (keptWord_toPath (P := (chCollapse K).poly) RunCut _ hg hall)
  rw [hc, hkw]
  refine Eq.trans (Prefunctor.mapPath_toPath runPre _) ?_
  refine Eq.trans (congrArg Quiver.Hom.toPath hcell) ?_
  exact toPath_cellCongr α.below.symm (bottomRun_self Y).symm α

/-! ## Reading a 1-cell back -/

/-- The object a chain names, read back. -/
theorem Phi_obj (c : Ch K) : (Phi K).obj (rho c) = (Theta K).obj (op c) :=
  Functor.congr_obj (Q_comp_Phi K) (op c)

theorem Phi_arr {c d : Ch K} (v : c ⟶ d) :
    (Phi K).map (arr v)
      = eqToHom (Phi_obj d) ≫ (Theta K).map v.op ≫ eqToHom (Phi_obj c).symm :=
  Functor.congr_hom (Q_comp_Phi K) v.op

/-- **A merge is read back as a renaming.** -/
theorem Phi_arr_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    ∃ h : (Phi K).obj (rho d) = (Phi K).obj (rho c), (Phi K).map (arr m) = eqToHom h := by
  obtain ⟨h, hm'⟩ := cutArrow_of_W m hm
  refine ⟨((Phi_obj d).trans h).trans (Phi_obj c).symm, ?_⟩
  rw [Phi_arr m, show (Theta K).map m.op = eqToHom h from hm']
  exact (congrArg (fun t => eqToHom (Phi_obj d) ≫ t) (eqToHom_trans _ _)).trans
    (eqToHom_trans _ _)

/-- **…so the conjugate of a refinement is read back as the refinement.** -/
theorem Phi_Rconj {c d : Ch K} (v : c ⟶ d) :
    ∃ (p : (Phi K).obj (rho (bottomRun d).chain) = (Phi K).obj (rho d))
      (q : (Phi K).obj (rho c) = (Phi K).obj (rho (bottomRun c).chain)),
      (Phi K).map (Rconj v) = eqToHom p ≫ (Phi K).map (arr v) ≫ eqToHom q := by
  obtain ⟨hd, hd'⟩ := Phi_arr_of_W (bottomHom d) (W_bottomHom d)
  obtain ⟨hc, hc'⟩ := Phi_arr_of_W (bottomHom c) (W_bottomHom c)
  refine ⟨hd.symm, hc, ?_⟩
  have hinv : (Phi K).map ((mergeIso (W_bottomHom d)).inv) = eqToHom hd.symm := by
    refine eq_eqToHom_symm hd ?_
    rw [← hd', ← (Phi K).map_comp]
    exact (congrArg (Phi K).map (mergeIso (W_bottomHom d)).hom_inv_id).trans ((Phi K).map_id _)
  rw [Rconj, (Phi K).map_comp, (Phi K).map_comp, hinv, hc']

/-! ## Reading, then reading back, is the identity -/

/-- **The run below a run is that run.** -/
theorem Theta_obj_run (X : Run K) : (Theta K).obj (op X.chain) = (poly K).quot.obj (runPt X) :=
  congrArg (fun Z : Run K => (poly K).quot.obj (runPt Z)) (bottomRun_self X)

theorem paperPhi_obj (X : Run K) :
    (poly K).quot.obj (runPt X) = (Phi K).obj (rho X.chain) :=
  (Theta_obj_run X).symm.trans (Phi_obj X.chain).symm

/-- **A 1-cell is read, then read back, as itself.** -/
theorem Phi_cellRconj {X Y : Run K} (α : Gen X Y) :
    (Phi K).map (cellRconj α)
      = eqToHom (paperPhi_obj X).symm
        ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (paperPhi_obj Y) := by
  obtain ⟨p, q, hR⟩ := Phi_Rconj α.hom
  have hArr : (Phi K).map (arr α.hom)
      = eqToHom (Phi_obj α.obj) ≫ (poly K).quot.map (cutWord α.hom α.codim_hom)
        ≫ eqToHom (Phi_obj Y.chain).symm :=
    (Phi_arr α.hom).trans (sandwich_congr _ _ (cutArrow_eq_cutWord α.hom α.codim_hom))
  have hWd : (poly K).quot.map (cutWord α.hom α.codim_hom)
      = eqToHom (congrArg (poly K).quot.obj (congrArg runPt α.below.symm)).symm
        ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (congrArg (poly K).quot.obj (congrArg runPt (bottomRun_self Y).symm)) := by
    rw [cutWord_hom α, readAt]
    exact Paths.map_cellCongr₂ (poly K).quot _ _ _
  rw [cellRconj, (Phi K).map_comp, (Phi K).map_comp, eqToHom_map, eqToHom_map, hR,
    hArr.trans (sandwich_congr _ _ hWd)]
  exact collapse4 _ _ _ _ _ _ _ _ _ _

/-- **Reading, then reading back, is the identity on the presented category.** -/
noncomputable def paperPhiIso (K : BPSet) :
    𝟭 ((poly K).presented) ≅ paperE K ⋙ Phi K := by
  refine NatIso.ofComponents (fun x => eqToIso (paperPhi_obj x.as.as)) ?_
  rintro ⟨x⟩ ⟨y⟩ f
  obtain ⟨w, rfl⟩ := (poly K).quot.map_surjective f
  refine Polygraph.naturality_of_gen (P := poly K) (fun z => eqToHom (paperPhi_obj z.as))
    (fun {a b} e => ?_) w
  have hp : (paperE K ⋙ Phi K).map ((poly K).quot.map e.toPath)
      = (Phi K).map (cellRconj e) :=
    congrArg (Phi K).map ((paperE_quot _).trans (Paths.lift_toPath (paperPre' (K := K)) e))
  exact Eq.trans (cancel_eqToHom (paperPhi_obj a.as) _).symm
    (congrArg (fun t => eqToHom (paperPhi_obj a.as) ≫ t) (hp.trans (Phi_cellRconj e))).symm

/-- **The interpretation of the paper's cells is an equivalence**, with the reading of the chains
as its inverse. -/
noncomputable instance isEquivalence_paperE (K : BPSet) : (paperE K).IsEquivalence :=
  Functor.IsEquivalence.mk' (Phi K) (paperPhiIso K) (PhiPaperIso K)

/-- **The paper's polygraph presents `Ch(K)[W⁻¹]`** — 0-cells the runs, 1- and 2-cells the objects
of degree one and two — for every `K` and with no hypothesis on `K`. -/
noncomputable def paperPresents (K : BPSet) :
    Presents (poly K) (((W K).op).Localization) := ⟨paperE K, inferInstance⟩

@[simp] theorem paperPresents_E (K : BPSet) : (paperPresents K).E = paperE K := rfl

/-- **A 1-cell names the arrow its object's refinement conjugates to.** -/
theorem paperE_map_gen {x y : GenObj (Gen (K := K))} (e : x ⟶ y) :
    (paperE K).map ((poly K).quot.map e.toPath) = cellRconj e :=
  (paperE_quot _).trans (Paths.lift_toPath (paperPre' (K := K)) e)

/-- **…so the chains, read on the paper's cells, are a localization.** -/
instance isLocalization_Theta (K : BPSet) : (Theta K).IsLocalization ((W K).op) where
  inverts := Theta_inverts
  isEquivalence := by
    have h : Localization.Construction.lift (Theta K) Theta_inverts = Phi K := rfl
    rw [h]
    exact Functor.IsEquivalence.mk' (paperE K) (PhiPaperIso K).symm (paperPhiIso K).symm

/-! ## Strict naturality of the interpretation -/

section Natural

variable {K' : BPSet} (f : K ⟶ K')

/-- **The run below a chain is carried along.** -/
theorem bottomRun_pushforward (c : Ch K) :
    bottomRun ((pushforward f).obj c) = (Run.pushforward f).obj (bottomRun c) :=
  eq_bottomRun_of_W ((pushforward f).map (bottomHom c))
    ((W_pushforward_iff f (bottomHom c)).mpr (W_bottomHom c))

/-- **…and so is the object a chain names.** -/
theorem chLocOpMap_obj (c : Ch K) :
    (chLocOpMap f).obj (rho c) = rho ((pushforward f).obj c) :=
  Functor.congr_obj (Q_comp_chLocOpMap f) (op c)

theorem chLocOpMap_arr {c d : Ch K} (u : c ⟶ d) :
    (chLocOpMap f).map (arr u)
      = eqToHom (chLocOpMap_obj f d) ≫ arr ((pushforward f).map u)
        ≫ eqToHom (chLocOpMap_obj f c).symm :=
  Functor.congr_hom (Q_comp_chLocOpMap f) u.op

theorem arr_pushforward {c d : Ch K} (u : c ⟶ d) :
    arr ((pushforward f).map u)
      = eqToHom (chLocOpMap_obj f d).symm ≫ (chLocOpMap f).map (arr u)
        ≫ eqToHom (chLocOpMap_obj f c) := by
  rw [chLocOpMap_arr]; simp

/-- …spelled at the chain, where the merge below lives. -/
theorem bottomRun_chain_pushforward (c : Ch K) :
    (bottomRun ((pushforward f).obj c)).chain = (pushforward f).obj (bottomRun c).chain :=
  congrArg Run.chain (bottomRun_pushforward f c)

/-- The object a run names, carried along. -/
theorem locObj_bottom (c : Ch K) :
    (chLocOpMap f).obj (rho (bottomRun c).chain) = rho (bottomRun ((pushforward f).obj c)).chain :=
  (chLocOpMap_obj f (bottomRun c).chain).trans
    (congrArg rho (bottomRun_chain_pushforward f c).symm)

/-- **The merge below a chain is carried to the merge below its image** — both are merges. -/
theorem pushforward_bottomHom (c : Ch K) :
    (pushforward f).map (bottomHom c)
      = eqToHom (bottomRun_chain_pushforward f c).symm ≫ bottomHom ((pushforward f).obj c) :=
  eq_of_W ((W_pushforward_iff f _).mpr (W_bottomHom c))
    ((W K').comp_mem _ _ (W_eqToHom _) (W_bottomHom _))

/-- The merge below the image, read through the image of the merge below. -/
theorem arr_bottomHom_pushforward (a : Ch K) :
    arr (bottomHom ((pushforward f).obj a))
      = arr ((pushforward f).map (bottomHom a))
        ≫ eqToHom (congrArg rho (bottomRun_chain_pushforward f a)) := by
  rw [pushforward_bottomHom f a, arr_comp, arr_eqToHom, Category.assoc, eqToHom_trans]
  exact (Category.comp_id _).symm

/-- Two renamings after an arrow are one. -/
private theorem sandwich_merge {C : Type*} [Category C] {A B X Y Z : C} (p : A = B) {g : B ⟶ X}
    (r : X = Y) (s : Y = Z) (q : X = Z) :
    eqToHom p ≫ (g ≫ eqToHom r) ≫ eqToHom s = eqToHom p ≫ g ≫ eqToHom q := by
  subst p; subst r; subst s; simp

/-- Two conjugates spliced at a renaming and its inverse. -/
private theorem splice {C : Type*} [Category C] {P Q R M S T : C} (a : P ⟶ Q) (g : Q ⟶ R)
    (p : R = M) (k : R ⟶ S) (c : S ⟶ T) :
    (a ≫ g ≫ eqToHom p) ≫ (eqToHom p.symm ≫ k ≫ c) = (a ≫ g ≫ k) ≫ c := by
  subst p; simp

/-- **The merge below a chain, carried along.** -/
theorem chLocOpMap_arr_bottomHom (a : Ch K) :
    (chLocOpMap f).map (arr (bottomHom a))
      = eqToHom (chLocOpMap_obj f a) ≫ arr (bottomHom ((pushforward f).obj a))
        ≫ eqToHom (locObj_bottom f a).symm := by
  rw [chLocOpMap_arr f (bottomHom a), arr_bottomHom_pushforward f a]
  exact (sandwich_merge _ _ _ _).symm

/-- **…and so is the conjugate of a refinement**, the only transports being the two runs' names. -/
theorem chLocOpMap_Rconj {c d : Ch K} (u : c ⟶ d) :
    eqToHom (locObj_bottom f d).symm ≫ (chLocOpMap f).map (Rconj u)
        ≫ eqToHom (locObj_bottom f c) = Rconj ((pushforward f).map u) := by
  refine Rconj_eq_of _ ?_
  have hd : arr (bottomHom ((pushforward f).obj d))
      = eqToHom (chLocOpMap_obj f d).symm ≫ (chLocOpMap f).map (arr (bottomHom d))
        ≫ eqToHom (locObj_bottom f d) := by
    rw [chLocOpMap_arr_bottomHom f d]; simp
  have key : (chLocOpMap f).map (arr (bottomHom d)) ≫ (chLocOpMap f).map (Rconj u)
      = (chLocOpMap f).map (arr u) ≫ (chLocOpMap f).map (arr (bottomHom c)) :=
    ((chLocOpMap f).map_comp _ _).symm.trans
      ((congrArg (chLocOpMap f).map (arr_bottomHom_comp_Rconj u)).trans
        ((chLocOpMap f).map_comp _ _))
  have hc : arr (bottomHom ((pushforward f).obj c))
      = eqToHom (chLocOpMap_obj f c).symm ≫ (chLocOpMap f).map (arr (bottomHom c))
        ≫ eqToHom (locObj_bottom f c) := by
    rw [chLocOpMap_arr_bottomHom f c]; simp
  rw [hd, hc, arr_pushforward f u]
  refine Eq.trans (splice _ _ _ _ _) (Eq.trans ?_ (splice _ _ _ _ _).symm)
  exact congrArg
    (fun t => (eqToHom (chLocOpMap_obj f d).symm ≫ t) ≫ eqToHom (locObj_bottom f c)) key

end Natural

end ChainCat.Paper
