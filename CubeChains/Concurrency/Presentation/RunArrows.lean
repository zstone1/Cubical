import CubeChains.Concurrency.Presentation.RunReduce

/-!
# Concurrency/Presentation/RunArrows — a refinement of `Ch K`, read in the localized cut polygraph

The fibration over `Ch Zbp` is discrete, so a 0-cell of the lifted cut polygraph *is* a chain of `K`
and a refinement upstairs is one downstairs carrying the element (`hom_ext_baseHom`).  A word is
pinned by the refinement it performs, so every refinement names an arrow (`chArrow`), and a 1-cell
of the contraction is its bead cut conjugated by the merges onto the runs of its two ends:

    run b ──merge──▸ b ──u──▸ a ◂──merge── run a          runConj u
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

variable {K : BPSet}

/-! ## A 0-cell is a chain, and a refinement is its lift

The fibre presheaf of `Ch K` over `Ch Zbp` is `wedgeHoms K`, so a 0-cell of the lifted cut
polygraph is literally a chain of `K` and a refinement upstairs is one downstairs carrying the
element. -/

/-- The chain a 0-cell names. -/
def vChain (z : (chCutPoly K).V) : Ch K := ⟨(shOf z).dims, z.2⟩

/-- The shape a refinement of chains performs. -/
def baseHom {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) : shOf a ⟶ shOf b :=
  ⟨f.φ, Subsingleton.elim _ _⟩

@[simp] theorem baseHom_comp {a b c : (chCutPoly K).V} (f : vChain a ⟶ vChain b)
    (g : vChain b ⟶ vChain c) : baseHom (f ≫ g) = baseHom f ≫ baseHom g := rfl

/-- The lift of a base refinement carrying the element. -/
def liftOf {a b : (chCutPoly K).V} (g : shOf a ⟶ shOf b)
    (h : (wedgeHoms K).map g.op b.2 = a.2) : vChain a ⟶ vChain b := ⟨g.φ, h⟩

@[simp] theorem baseHom_liftOf {a b : (chCutPoly K).V} (g : shOf a ⟶ shOf b)
    (h : (wedgeHoms K).map g.op b.2 = a.2) : baseHom (liftOf g h) = g := rfl

/-- **A refinement is its shape** — the fibration is discrete, so two lifts of one base refinement
agree. -/
theorem hom_ext_baseHom {a b : (chCutPoly K).V} {f f' : vChain a ⟶ vChain b}
    (h : baseHom f = baseHom f') : f = f' :=
  hom_ext' (congrArg (fun t : shOf a ⟶ shOf b => t.φ) h)

theorem W_baseHom_iff {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) :
    W Zbp (baseHom f) ↔ W K f := by
  rw [W_iff_flat, W_iff_flat]
  rfl

/-! ## The reading of a refinement in the localized cut polygraph

`elt_quot_eq_of_ev_eq` says a word of the lifted cut polygraph is pinned by the refinement it
performs, so *every* refinement names one arrow there (`chArrow`).  It is not a `Functor.map`, so
composition is `chArrow_comp`. -/

/-- Projection of a lifted word to the bead cuts it performs. -/
noncomputable abbrev chProj (K : BPSet) :
    GenObj (chCutPoly K).Gen ⥤q GenObj Cut.Refine :=
  zCutPresentation.elementsProj (wedgeHoms K)

/-- A cut word spelling a refinement, lifted to the chains of `K` it acts on. -/
noncomputable def chPath {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) :
    Quiver.Path (⟨b⟩ : GenObj (chCutPoly K).Gen) ⟨a⟩ :=
  zCutPresentation.wordLift (wedgeHoms K) (cutPath (baseHom f))
    (by rw [show zCutPresentation.eval.map (cutPath (baseHom f)) = (baseHom f).op from
          congrArg Quiver.Hom.op (ev_cutPath (baseHom f))]
        exact f.w)

theorem ev_chPath {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) :
    Cut.ev ((chProj K).mapPath (chPath f)) = baseHom f :=
  (congrArg Cut.ev
    (zCutPresentation.elementsProj_mapPath_wordLift (wedgeHoms K) _ _)).trans (ev_cutPath _)

/-- **A word of the lifted cut polygraph is pinned by the refinement it performs**, still after the
merges are formally inverted. -/
theorem chQuot_congr {X Y : GenObj (chCutPoly K).Gen} {R R' : Quiver.Path X Y}
    (h : Cut.ev ((chProj K).mapPath R) = Cut.ev ((chProj K).mapPath R')) :
    (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath R)
      = (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath R') :=
  Polygraph.Hom.quot_map_congr (Polygraph.invIncl _ _) (elt_quot_eq_of_ev_eq R R' h)

/-- The 0-cell a chain names in the localized cut polygraph. -/
noncomputable def chPt (z : (chCutPoly K).V) : (cutLocPoly K).presented :=
  (cutLocPoly K).quot.obj ((cutLocPoly K).pt z)

/-- **The arrow a refinement names there.** -/
noncomputable def chArrow {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) : chPt b ⟶ chPt a :=
  (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath (chPath f))

theorem Cut.ev_comp {x y z : GenObj Cut.Refine} (R : Quiver.Path x y) (R' : Quiver.Path y z) :
    Cut.ev (R.comp R') = Cut.ev R' ≫ Cut.ev R := by
  induction R' with
  | nil => exact (Category.id_comp _).symm
  | cons R' e ih => rw [Quiver.Path.comp_cons, Cut.ev_cons, Cut.ev_cons, ih, Category.assoc]

theorem chArrow_comp {a b c : (chCutPoly K).V} (f : vChain a ⟶ vChain b) (g : vChain b ⟶ vChain c) :
    chArrow (f ≫ g) = chArrow g ≫ chArrow f := by
  have h1 : chArrow (f ≫ g)
      = (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath
        ((chPath g).comp (chPath f))) := by
    refine chQuot_congr ?_
    rw [ev_chPath, Prefunctor.mapPath_comp, Cut.ev_comp, ev_chPath, ev_chPath]
    rfl
  rw [h1, Prefunctor.mapPath_comp]
  exact Polygraph.quot_map_comp _ _ _

/-- A merge word, spelled out of the inverted 1-cells. -/
theorem all_chPath_of_W {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) (hf : W K f) :
    Quiver.Path.All (fun ⦃_ _⦄ e => chCutPicked K e) (chPath f) :=
  zCutPresentation.all_elementsPicked_wordLift (wedgeHoms K) Cut.mergeGen _
    (Cut.all_mergeGen_of_W _ (by rw [ev_cutPath]; exact (W_baseHom_iff f).mpr hf))

/-- **A merge names an isomorphism** — the formal inverses adjoined to its letters. -/
noncomputable instance isIso_chArrow {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b)
    (hf : W K f) : IsIso (chArrow f) :=
  ⟨(cutLocPoly K).quot.map
      (Polygraph.invWord (chCutPoly K) (chCutPicked K) (chPath f) (all_chPath_of_W f hf)),
    (Polygraph.quot_map_comp _ _ _).symm.trans
      (Polygraph.quot_fwd_invWord (chCutPoly K) _ (chPath f) (all_chPath_of_W f hf)),
    (Polygraph.quot_map_comp _ _ _).symm.trans
      (Polygraph.quot_invWord_fwd (chCutPoly K) _ (chPath f) (all_chPath_of_W f hf))⟩

/-- **Two merges out of one run name one arrow** — `eq_of_W` pins them. -/
theorem chArrow_eq_of_W {a r r' : (chCutPoly K).V} {u : vChain r ⟶ vChain a}
    {v : vChain r' ⟶ vChain a} (hu : W K u) (hv : W K v) (h : r = r') :
    chArrow u ≫ eqToHom (congrArg chPt h) = chArrow v := by
  subst h
  rw [eqToHom_refl, Category.comp_id,
    hom_ext_baseHom (eq_of_W ((W_baseHom_iff u).mpr hu) ((W_baseHom_iff v).mpr hv))]

/-! ## The contraction, read as arrows

A 0-cell's merge onto its run is the contraction's own word, so a 1-cell is its bead cut
conjugated by the two merges — `runConj`, a relative hom that composes. -/

/-- The merge onto a 0-cell's run. -/
noncomputable def runMergeK (z : (chCutPoly K).V) : vChain (eltRep z) ⟶ vChain z :=
  liftOf (zRunMerge (shOf z)) rfl

theorem W_runMergeK (z : (chCutPoly K).V) : W K (runMergeK z) :=
  (W_baseHom_iff _).mp (W_zRunMerge _)

noncomputable instance isIso_chArrow_runMergeK (z : (chCutPoly K).V) :
    IsIso (chArrow (runMergeK z)) := isIso_chArrow _ (W_runMergeK z)

/-- **The collapse's merge word performs that merge.** -/
theorem quot_word_eq (z : (chCutPoly K).V) :
    (cutLocPoly K).quot.map ((chCollapse K).locWord z) = chArrow (runMergeK z) :=
  chQuot_congr (R := eltRunWord z) (R' := chPath (runMergeK z))
    ((congrArg Cut.ev (elementsProj_eltRunWord z)).trans
      ((ev_runCutWord (shOf z)).trans (ev_chPath (runMergeK z)).symm))

theorem inv_chArrow_runMergeK (z : (chCutPoly K).V) :
    inv (chArrow (runMergeK z)) = (cutLocPoly K).quot.map ((chCollapse K).invWord z) :=
  IsIso.inv_eq_of_hom_inv_id (by
    rw [← quot_word_eq]
    exact ((chCollapse K).wordIso z).hom_inv_id)

/-- **The arrow a refinement names between the runs of its two ends.** -/
noncomputable def runConj {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) :
    chPt (eltRep a) ⟶ chPt (eltRep b) :=
  inv (chArrow (runMergeK a)) ≫ chArrow u ≫ chArrow (runMergeK b)

theorem runConj_comp {a b c : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (v : vChain c ⟶ vChain b) :
    runConj (v ≫ u) = runConj u ≫ runConj v := by
  rw [runConj, runConj, runConj, chArrow_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- **A merge names a renaming of runs.** -/
theorem eltRep_eq_of_W {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (hu : W K u) :
    eltRep b = eltRep a :=
  (congrArg eltRep (show b = eltRestrict a (baseHom u) from
      congrArg (fun t => (⟨shOf b, t⟩ : (chCutPoly K).V)) u.w.symm)).trans
    ((eltRestrict_comp a (baseHom u) (zRunMerge (shOf b))).trans
      (eltRestrict_eq_of_W a (congrArg (fun n => zObj (𝟙^n)) (dimSum_eq_of_hom (baseHom u)))
        ((W Zbp).comp_mem _ _ (W_zRunMerge (shOf b)) ((W_baseHom_iff u).mpr hu))
        (W_zRunMerge (shOf a))))

theorem runConj_of_W {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (hu : W K u) :
    runConj u = eqToHom (congrArg chPt (eltRep_eq_of_W u hu).symm) := by
  have h := chArrow_eq_of_W (u := runMergeK b ≫ u) (v := runMergeK a)
    ((W K).comp_mem _ _ (W_runMergeK b) hu) (W_runMergeK a) (eltRep_eq_of_W u hu)
  rw [chArrow_comp] at h
  have h2 : chArrow u ≫ chArrow (runMergeK b)
      = chArrow (runMergeK a) ≫ eqToHom (congrArg chPt (eltRep_eq_of_W u hu).symm) := by
    rw [← h]; simp
  rw [runConj, h2, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-! ## Reading a 1-cell of the contraction -/

/-- The refinement of `Ch K` a bead cut of the lifted polygraph performs. -/
noncomputable def chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    vChain b ⟶ vChain a :=
  liftOf (Cut.genHom e.1) (map_cutHom e)

theorem chArrow_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (cutLocPoly K).quot.map (fwdCell (chCutPoly K) (chCutPicked K) e).toPath
      = chArrow (chCutHom e) := by
  have h1 : (cutLocPoly K).quot.map (fwdCell (chCutPoly K) (chCutPicked K) e).toPath
      = (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath
        (Polygraph.cell (P := chCutPoly K) e).toPath) :=
    congrArg (cutLocPoly K).quot.map (Prefunctor.mapPath_toPath
      (fwdPre (chCutPoly K) (chCutPicked K)) (Polygraph.cell (P := chCutPoly K) e)).symm
  refine h1.trans (chQuot_congr ?_)
  rw [ev_chPath, Prefunctor.mapPath_toPath]
  exact (Category.comp_id _).symm

/-- The 1-cell a bead cut of the collapse becomes, at the runs of its two ends. -/
theorem backQuot_gen {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    (chCollapse K).backQuot.map (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = eqToHom (congrArg chPt g.rep_dom).symm ≫ runConj (chCutHom g.gen)
        ≫ eqToHom (congrArg chPt g.rep_cod) := by
  have h1 : (chCollapse K).backQuot.map
        (Polygraph.cell (P := (chCollapse K).poly) g).toPath
      = (cutLocPoly K).quot.map (cellCongr Quiver.Path
          (congrArg (cutLocPoly K).pt g.rep_dom) (congrArg (cutLocPoly K).pt g.rep_cod)
          (((chCollapse K).invWord g.dom).comp
            ((fwdCell (chCutPoly K) (chCutPicked K) g.gen).toPath.comp
              ((chCollapse K).locWord g.cod)))) :=
    congrArg (cutLocPoly K).quot.map (Paths.lift_toPath (chCollapse K).backPre g)
  have h2 : (cutLocPoly K).quot.map (((chCollapse K).invWord g.dom).comp
        ((fwdCell (chCutPoly K) (chCutPicked K) g.gen).toPath.comp
          ((chCollapse K).locWord g.cod)))
      = runConj (chCutHom g.gen) := by
    have h3 : (cutLocPoly K).quot.map (fwdCell (chCutPoly K) (chCutPicked K) g.gen).toPath
          ≫ (cutLocPoly K).quot.map ((chCollapse K).locWord g.cod)
        = chArrow (chCutHom g.gen) ≫ chArrow (runMergeK g.cod) :=
      (congrArg (fun t => t ≫ (cutLocPoly K).quot.map ((chCollapse K).locWord g.cod))
          (chArrow_chCutHom g.gen)).trans
        (congrArg (fun t => chArrow (chCutHom g.gen) ≫ t) (quot_word_eq g.cod))
    refine Eq.trans (Polygraph.quot_map_comp (cutLocPoly K) _ _) ?_
    refine Eq.trans (congrArg
      (fun t => (cutLocPoly K).quot.map ((chCollapse K).invWord g.dom) ≫ t)
      ((Polygraph.quot_map_comp (cutLocPoly K) _ _).trans h3)) ?_
    exact congrArg (fun t => t ≫ (chArrow (chCutHom g.gen) ≫ chArrow (runMergeK g.cod)))
      (inv_chArrow_runMergeK g.dom).symm
  refine Eq.trans h1 ?_
  refine Eq.trans (Paths.map_cellCongr₂ (cutLocPoly K).quot _ _ _) ?_
  exact congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _) h2

/-! ## The sub-polygraph at degree zero -/

/-- **The 1-cells to keep**: those whose bead cut starts at a run. -/
def RunCut {x y : (chCollapse K).V} (g : (chCollapse K).Gen x y) : Prop :=
  eltRep g.cod = g.cod

/-- The number of events a 0-cell carries. -/
abbrev vCount (z : (chCutPoly K).V) : ℕ := dimSum (shOf z).dims

/-- **Words with the same conjugate agree** — the collapse's equivalence is faithful. -/
theorem poly_quot_congr {X Y : GenObj (chCollapse K).poly.Gen} {w w' : Quiver.Path X Y}
    (h : (chCollapse K).backQuot.map w = (chCollapse K).backQuot.map w') :
    (chCollapse K).poly.quot.map w = (chCollapse K).poly.quot.map w' :=
  (chCollapse K).equivalence.inverse.map_injective h

end ChainCat
