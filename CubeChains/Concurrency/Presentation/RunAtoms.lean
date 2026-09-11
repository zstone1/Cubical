import CubeChains.Concurrency.Presentation.RunReduce
import CubeChains.Concurrency.Presentation.SliceRuns

/-!
# Concurrency/Presentation/RunAtoms — the cuts out of a run spell every bead cut

The slice over a chain `d` splits bead by bead — `(Ch K)/d ≃ (Ch Z)/zObj d.dims ≃ ∏ᵢ Ch(□dᵢ)` —
so a run-arrow into `d` crosses only inside `d`'s blocks (`index_crossPerm`), and each descent of
its crossing permutation is realised by an atom over that same `d`:

    run r ──atom k──▸ eₖ ◂──merge── run r'      one crossing shorter
       └────── u ──────┴──── w ────▸ d ◂──merge── run d

Iterating spells `u` by atoms out of runs, which is `Spans`' dimension one at every `K`.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-! ## A 0-cell is a chain, and a refinement is its lift

The fibre presheaf of `Ch K` over `Ch Zbp` is `wedgeHoms K`, so a 0-cell of the lifted cut
polygraph is literally a chain of `K` and a refinement upstairs is one downstairs carrying the
element. -/

/-- The shape a 0-cell names.  `Cut.poly.V` does not unfold at instance transparency, so the
projection is wrapped at the type callers see. -/
abbrev shOf (z : (chCutPoly K).V) : Ch Zbp := z.1

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
  rw [W_iff_monotone_coordMap, W_iff_monotone_coordMap]
  rfl

/-! ## The reading of a refinement in the localized cut polygraph

`elt_quot_eq_of_ev_eq` says a word of the lifted cut polygraph is pinned by the refinement it
performs, so *every* refinement names one arrow there — a functor `(Ch K)ᵒᵖ ⥤ …` built by hand
rather than transported. -/

/-- The merges among the lifted bead cuts. -/
noncomputable abbrev chCutPicked (K : BPSet) :
    ∀ {a b : (chCutPoly K).V}, (chCutPoly K).Gen a b → Prop :=
  chPicked zCutPresentation Cut.mergeGen K

/-- The lifted bead cuts with a formal inverse adjoined to each merge. -/
noncomputable abbrev cutLocPoly (K : BPSet) : Polygraph := chCutLocFunctor.obj K

/-- Projection of a lifted word to the bead cuts it performs. -/
noncomputable abbrev chProj (K : BPSet) :
    GenObj (chCutPoly K).Gen ⥤q GenObj Cut.Refine :=
  zCutPresentation.elementsProj (wedgeHoms K)

/-- A cut word spelling a refinement. -/
noncomputable def cutPath {a b : Ch Zbp} (f : a ⟶ b) : Quiver.Path (Cut.vert b) (Cut.vert a) :=
  (Cut.exists_path (codim f) f le_rfl).choose

theorem ev_cutPath {a b : Ch Zbp} (f : a ⟶ b) : Cut.ev (cutPath f) = f :=
  (Cut.exists_path (codim f) f le_rfl).choose_spec

/-- …lifted to the chains of `K` it acts on. -/
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

theorem chArrow_id (a : (chCutPoly K).V) : chArrow (𝟙 (vChain a)) = 𝟙 (chPt a) := by
  have h1 : chArrow (𝟙 (vChain a))
      = (cutLocPoly K).quot.map
        ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath (Quiver.Path.nil (a := ⟨a⟩))) :=
    chQuot_congr (by rw [ev_chPath]; rfl)
  rw [h1, Prefunctor.mapPath_nil]
  exact Polygraph.quot_map_nil _ _

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

/-- **The contraction's merge word performs that merge.** -/
theorem quot_word_eq (z : (chCutPoly K).V) :
    (cutLocPoly K).quot.map ((chContraction K).word z) = chArrow (runMergeK z) :=
  chQuot_congr (R := eltRunWord z) (R' := chPath (runMergeK z))
    ((congrArg Cut.ev (elementsProj_eltRunWord z)).trans
      ((ev_runCutWord (shOf z)).trans (ev_chPath (runMergeK z)).symm))

theorem inv_chArrow_runMergeK (z : (chCutPoly K).V) :
    inv (chArrow (runMergeK z)) = (cutLocPoly K).quot.map ((chContraction K).invWord z) :=
  IsIso.inv_eq_of_hom_inv_id (by
    rw [← quot_word_eq]
    exact ((chContraction K).wordIso z).hom_inv_id)

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

/-- The bead cut an unmerged 1-cell of the extension is. -/
def chFwdOf {a b : (chCutPoly K).V} :
    ∀ g : InvGen (chCutPoly K) (chCutPicked K) a b, ¬ Cut.merged g → (chCutPoly K).Gen a b
  | .inl e, _ => e
  | .inr _, h => absurd trivial h

/-- …as a refinement of `Ch K`. -/
noncomputable def chCutHom {a b : (chCutPoly K).V}
    (g : InvGen (chCutPoly K) (chCutPicked K) a b) (hg : ¬ Cut.merged g) : vChain b ⟶ vChain a :=
  liftOf (Cut.genHom (chFwdOf g hg).1) (chFwdOf g hg).2

theorem chArrow_chCutHom {a b : (chCutPoly K).V}
    (g : InvGen (chCutPoly K) (chCutPicked K) a b) (hg : ¬ Cut.merged g) :
    (cutLocPoly K).quot.map (Polygraph.cell (P := cutLocPoly K) g).toPath
      = chArrow (chCutHom g hg) := by
  rcases g with e | ⟨e, he⟩
  case inr => exact absurd trivial hg
  have h1 : (cutLocPoly K).quot.map (Polygraph.cell (P := cutLocPoly K) (Sum.inl e)).toPath
      = (cutLocPoly K).quot.map ((fwdPre (chCutPoly K) (chCutPicked K)).mapPath
        (Polygraph.cell (P := chCutPoly K) e).toPath) :=
    congrArg (cutLocPoly K).quot.map (Prefunctor.mapPath_toPath
      (fwdPre (chCutPoly K) (chCutPicked K)) (Polygraph.cell (P := chCutPoly K) e)).symm
  refine h1.trans (chQuot_congr ?_)
  rw [ev_chPath, Prefunctor.mapPath_toPath]
  exact (Category.comp_id _).symm

/-- The 1-cell a non-merge letter of the extension becomes, at the runs of its two ends. -/
theorem backQuot_gen {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    (chContraction K).backQuot.map (Polygraph.cell (P := (chContraction K).poly) g).toPath
      = eqToHom (congrArg chPt g.rep_dom).symm ≫ runConj (chCutHom g.gen g.not_mem)
        ≫ eqToHom (congrArg chPt g.rep_cod) := by
  have h1 : (chContraction K).backQuot.map
        (Polygraph.cell (P := (chContraction K).poly) g).toPath
      = (cutLocPoly K).quot.map (cellCongr Quiver.Path
          (congrArg (cutLocPoly K).pt g.rep_dom) (congrArg (cutLocPoly K).pt g.rep_cod)
          (((chContraction K).invWord g.dom).comp
            ((Polygraph.cell (P := cutLocPoly K) g.gen).toPath.comp
              ((chContraction K).word g.cod)))) :=
    congrArg (cutLocPoly K).quot.map (Paths.lift_toPath (chContraction K).backPre g)
  have h2 : (cutLocPoly K).quot.map (((chContraction K).invWord g.dom).comp
        ((Polygraph.cell (P := cutLocPoly K) g.gen).toPath.comp ((chContraction K).word g.cod)))
      = runConj (chCutHom g.gen g.not_mem) := by
    rw [Polygraph.quot_map_comp (cutLocPoly K), Polygraph.quot_map_comp (cutLocPoly K),
      ← inv_chArrow_runMergeK, quot_word_eq, chArrow_chCutHom]
    rfl
  rw [h1, Paths.map_cellCongr₂, h2]
  rfl

/-! ## A descent is realised by an atom

`nonempty_atomComp_of_descent` puts the crossed pair inside one block of the target — the geometry
— and the exchange then shortens the run-arrow by exactly one crossing. -/

private theorem crossPerm_eqToHom_comp {N : ℕ} {c c' d : Ch Zbp} (h : c = c') (f : c' ⟶ d)
    (hc : dimSum c.dims = N) (hc' : dimSum c'.dims = N) :
    crossPerm hc (eqToHom h ≫ f) = crossPerm hc' f := by
  subst h; rw [eqToHom_refl, Category.id_comp]

/-- **At a descent the run-arrow factors through the atom shape**, and the merge leg is one
crossing shorter. -/
theorem exists_atom_leg {N : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = N)
    (t : zObj (𝟙^N) ⟶ d) {k : Fin (N - 1)}
    (hdesc : crossPerm (dimSum_replicate N) t (adjHi k)
      < crossPerm (dimSum_replicate N) t (adjLo k)) :
    ∃ w : zObj (atomComp N k) ⟶ d, atomOnes N k ≫ w = t ∧
      permLen (crossPerm (dimSum_replicate N) (mergeOnes N k ≫ w)) + 1
        = permLen (crossPerm (dimSum_replicate N) t) := by
  obtain ⟨t', ht'⟩ := exists_run_mul_adjT hd t hdesc
  obtain ⟨w, hmerge, hatom⟩ := exists_atom_step hd k (nonempty_atomComp_of_descent hd t hdesc)
    (rfl : crossPerm (dimSum_replicate N) t' = crossPerm (dimSum_replicate N) t')
    (by rw [ht']; exact adjT_ascent_of_descent hdesc)
  refine ⟨w, hom_ext_of_crossPerm (h := dimSum_replicate N) ?_, ?_⟩
  · rw [hatom, ht', mul_adjT_adjT]
  · rw [hmerge, ht']
    exact (permLen_mul_adjT_of_descent hdesc).symm

/-! ## The sub-polygraph at degree zero -/

/-- **The 1-cells to keep**: those whose bead cut starts at a run. -/
def RunCut {x y : (chContraction K).V} (g : (chContraction K).Gen x y) : Prop :=
  eltRep g.cod = g.cod

/-- **At the base these are `OutOfRun`'s 1-cells** — the same condition, read at `K = Zbp`. -/
theorem runCut_iff_outOfRun {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    RunCut g ↔ OutOfRun g := Iff.rfl

/-- The number of events a 0-cell carries. -/
abbrev vCount (z : (chCutPoly K).V) : ℕ := dimSum (shOf z).dims

/-- The crossing permutation a refinement into a chain performs. -/
noncomputable def uPerm {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) : Perm (Fin (vCount a)) :=
  crossPerm (dimSum_eq_of_hom (baseHom u)) (baseHom u)

/-- **A crossing-free refinement names a renaming of runs.** -/
theorem exists_runCutPath_W {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (hu : W K u)
    {X Y : (chContraction K).V} (hX : eltRep a = X.1) (hY : eltRep b = Y.1) :
    ∃ w : Quiver.Path ((chContraction K).poly.pt X) ((chContraction K).poly.pt Y),
      Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) w ∧
      (chContraction K).backQuot.map w
        = eqToHom (congrArg chPt hX).symm ≫ runConj u ≫ eqToHom (congrArg chPt hY) := by
  obtain rfl : X = Y := Subtype.ext (hX.symm.trans ((eltRep_eq_of_W u hu).symm.trans hY))
  refine ⟨Quiver.Path.nil, Quiver.Path.all_nil _, ?_⟩
  rw [runConj_of_W u hu]
  simpa using ((chContraction K).backQuot.map_id ((chContraction K).poly.pt X)).symm

/-- **One descent, spelled by an atom out of the run** — the atom 1-cell of the contraction, the
shorter refinement behind it, and the factorisation they make. -/
theorem exists_atom_step_up {a b : (chCutPoly K).V} (hb : eltRep b = b) (u : vChain b ⟶ vChain a)
    {Y : (chContraction K).V} (hY : eltRep b = Y.1) (hpos : 0 < permLen (uPerm u)) :
    ∃ (X' : (chContraction K).V) (v : vChain X'.1 ⟶ vChain a) (hv : eltRep X'.1 = X'.1)
      (α : (chContraction K).Gen X' Y), RunCut α ∧
      permLen (uPerm v) + 1 = permLen (uPerm u) ∧
      runConj u = runConj v ≫ eqToHom (congrArg chPt hv)
        ≫ eqToHom (congrArg chPt α.rep_dom).symm ≫ runConj (chCutHom α.gen α.not_mem)
        ≫ eqToHom (congrArg chPt α.rep_cod) ≫ eqToHom (congrArg chPt hY).symm := by
  have hbN : shOf b = zObj (𝟙^(vCount a)) :=
    (congrArg (fun z : (chCutPoly K).V => shOf z) hb).symm.trans
      (congrArg (fun m => zObj (𝟙^m)) (dimSum_eq_of_hom (baseHom u)))
  have hut : crossPerm (dimSum_replicate (vCount a)) (eqToHom hbN.symm ≫ baseHom u) = uPerm u :=
    crossPerm_eqToHom_comp hbN.symm (baseHom u) _ _
  obtain ⟨k, hdesc⟩ := exists_adjacent_descent
    (crossPerm (dimSum_replicate (vCount a)) (eqToHom hbN.symm ≫ baseHom u))
    (by rw [hut]; exact hpos)
  obtain ⟨w, hw, hlen⟩ := exists_atom_leg (d := shOf a) rfl (eqToHom hbN.symm ≫ baseHom u) hdesc
  have hrep : eltRep (eltRestrict a w) = eltRestrict (eltRestrict a w) (mergeOnes (vCount a) k) :=
    eltRestrict_eq_of_W (eltRestrict a w)
      (congrArg (fun m => zObj (𝟙^m)) (dimSum_atomComp (vCount a) k)) (W_zRunMerge _)
      (W_mergeOnes (vCount a) k)
  have hrun : eltRep (eltRestrict (eltRestrict a w) (mergeOnes (vCount a) k))
      = eltRestrict (eltRestrict a w) (mergeOnes (vCount a) k) := by
    rw [← hrep]; exact eltRep_idem _
  have hcomp : (eqToHom hbN ≫ atomOnes (vCount a) k) ≫ w = baseHom u := by
    rw [Category.assoc, hw, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hat : (wedgeHoms K).map (eqToHom hbN ≫ atomOnes (vCount a) k).op (eltRestrict a w).2
      = b.2 := by
    change (eqToHom hbN ≫ atomOnes (vCount a) k).φ ≫ w.φ ≫ (vChain a).map = (vChain b).map
    rw [← Category.assoc]
    exact (congrArg (fun s : shOf b ⟶ shOf a => s.φ ≫ (vChain a).map) hcomp).trans u.w
  have hcod : codim (eqToHom hbN ≫ atomOnes (vCount a) k) = 1 :=
    (codim_eqToHom_comp _ _).trans (codim_atomOnes (vCount a) k)
  have hnm : ¬ Cut.merged (F := wedgeHoms K)
      (Sum.inl (⟨⟨eqToHom hbN ≫ atomOnes (vCount a) k, hcod⟩, hat⟩ :
        (chCutPoly K).Gen (eltRestrict a w) b)) :=
    fun hm => not_W_atomOnes (vCount a) k (W_of_comp_right _ _ ((merge_iff _).mp hm).1)
  set mm : vChain (eltRestrict (eltRestrict a w) (mergeOnes (vCount a) k))
      ⟶ vChain (eltRestrict a w) := liftOf (mergeOnes (vCount a) k) rfl with hmm
  set wt : vChain (eltRestrict a w) ⟶ vChain a := liftOf w rfl with hwt
  refine ⟨⟨_, hrun⟩, mm ≫ wt, hrun,
    { dom := eltRestrict a w
      cod := b
      gen := Sum.inl ⟨⟨eqToHom hbN ≫ atomOnes (vCount a) k, hcod⟩, hat⟩
      not_mem := hnm
      rep_dom := hrep
      rep_cod := hY }, hb, ?_, ?_⟩
  · have h1 : uPerm (mm ≫ wt)
        = crossPerm (dimSum_replicate (vCount a)) (mergeOnes (vCount a) k ≫ w) := by
      rw [hmm, hwt]; rfl
    rw [h1, ← hut]
    exact hlen
  · have hWm : W K mm := by rw [hmm]; exact (W_baseHom_iff _).mp (W_mergeOnes (vCount a) k)
    have h3 : runConj u
        = runConj wt ≫ runConj (liftOf (eqToHom hbN ≫ atomOnes (vCount a) k) hat) := by
      rw [← runConj_comp]
      refine congrArg runConj (hom_ext_baseHom ?_).symm
      rw [hwt]
      exact hcomp
    have h4 : runConj (mm ≫ wt)
        = runConj wt ≫ eqToHom (congrArg chPt (eltRep_eq_of_W mm hWm).symm) := by
      rw [runConj_comp, runConj_of_W mm hWm]
    change runConj u = runConj (mm ≫ wt) ≫ eqToHom (congrArg chPt hrun)
      ≫ eqToHom (congrArg chPt hrep).symm
      ≫ runConj (liftOf (eqToHom hbN ≫ atomOnes (vCount a) k) hat)
      ≫ eqToHom (congrArg chPt hY) ≫ eqToHom (congrArg chPt hY).symm
    rw [h3, h4]
    simp

/-- Re-bracketing a six-fold composite past a cancelling pair.  Stated for `exact`: the object
slots of `≫` carry two spellings of one object here, which defeats `simp`'s matching. -/
private theorem assoc_cancel {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆)
    (g : X₆ ⟶ X₇) (g' : X₇ ⟶ X₆) (hg : g ≫ g' = 𝟙 X₆) :
    (a ≫ b ≫ c) ≫ d ≫ e ≫ f = a ≫ (b ≫ c ≫ d ≫ e ≫ f ≫ g) ≫ g' := by
  simp only [Category.assoc]
  rw [hg, Category.comp_id]

/-- **Every refinement out of a run is spelled by atoms out of runs** — descent induction on the
crossing count, each step an atom `exists_atom_leg` supplies. -/
theorem exists_runCutPath (K : BPSet) : ∀ (n : ℕ) {a b : (chCutPoly K).V} (_hb : eltRep b = b)
    (u : vChain b ⟶ vChain a), permLen (uPerm u) ≤ n →
    ∀ {X Y : (chContraction K).V} (hX : eltRep a = X.1) (hY : eltRep b = Y.1),
      ∃ w : Quiver.Path ((chContraction K).poly.pt X) ((chContraction K).poly.pt Y),
        Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) w ∧
        (chContraction K).backQuot.map w
          = eqToHom (congrArg chPt hX).symm ≫ runConj u ≫ eqToHom (congrArg chPt hY) := by
  intro n
  induction n with
  | zero =>
      intro a b _hb u hn X Y hX hY
      exact exists_runCutPath_W u ((W_baseHom_iff u).mp
        ((W_iff_crossPerm_eq_one _ (baseHom u)).mpr
          (eq_one_of_permLen_eq_zero _ (Nat.le_zero.mp hn)))) hX hY
  | succ n ih =>
      intro a b hb u hn X Y hX hY
      by_cases h0 : permLen (uPerm u) = 0
      · exact exists_runCutPath_W u ((W_baseHom_iff u).mp
          ((W_iff_crossPerm_eq_one _ (baseHom u)).mpr (eq_one_of_permLen_eq_zero _ h0))) hX hY
      · obtain ⟨X', v, hv, α, hRC, hlen, heqn⟩ :=
          exists_atom_step_up hb u hY (Nat.pos_of_ne_zero h0)
        obtain ⟨w', hall', heq'⟩ := ih hv v (by omega) hX hv
        refine ⟨w'.cons (Polygraph.cell (P := (chContraction K).poly) α),
          (Quiver.Path.all_cons_iff _ _).mpr ⟨hall', hRC⟩, ?_⟩
        refine Eq.trans ((chContraction K).backQuot.map_comp w'
          (Polygraph.cell (P := (chContraction K).poly) α).toPath) ?_
        rw [heq', backQuot_gen α, heqn]
        exact assoc_cancel _ _ _ _ _ _ _ _
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- Cancelling a pair inside a triple composite.  Stated for `exact`, for the same reason. -/
private theorem comp_reassoc {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄} {e : X₂ ⟶ X₄} (h : c ≫ d = e) :
    a ≫ (b ≫ c) ≫ d = a ≫ b ≫ e := by rw [Category.assoc, h]

/-- **…and so is every refinement**, its source merged onto its own run first. -/
theorem exists_runCutPath' {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a)
    {X Y : (chContraction K).V} (hX : eltRep a = X.1) (hY : eltRep b = Y.1) :
    ∃ w : Quiver.Path ((chContraction K).poly.pt X) ((chContraction K).poly.pt Y),
      Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) w ∧
      (chContraction K).backQuot.map w
        = eqToHom (congrArg chPt hX).symm ≫ runConj u ≫ eqToHom (congrArg chPt hY) := by
  obtain ⟨w, hall, hw⟩ := exists_runCutPath K (permLen (uPerm (runMergeK b ≫ u)))
    (eltRep_idem b) (runMergeK b ≫ u) le_rfl hX ((eltRep_idem b).trans hY)
  refine ⟨w, hall, hw.trans ?_⟩
  rw [runConj_comp, runConj_of_W (runMergeK b) (W_runMergeK b)]
  exact comp_reassoc _ _ (eqToHom_trans _ _)

/-! ## The presentation

`word_eq` is an equation in `P.presented`, and the contraction's own equivalence carries it there
from the localized cut polygraph, where `runConj` computes.  Every 2-cell is kept — `T₂` is `True`,
so `cell_derivable` is `quot_src_tgt`. -/

/-- **Words with the same conjugate agree** — the contraction's equivalence is faithful. -/
theorem poly_quot_congr {X Y : GenObj (chContraction K).poly.Gen} {w w' : Quiver.Path X Y}
    (h : (chContraction K).backQuot.map w = (chContraction K).backQuot.map w') :
    (chContraction K).poly.quot.map w = (chContraction K).poly.quot.map w' :=
  (chContraction K).equivalence.inverse.map_injective h

/-- The atom word a 1-cell spells, or the 1-cell itself when its cut already starts at a run. -/
noncomputable def atomWord {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    Quiver.Path ((chContraction K).poly.pt X) ((chContraction K).poly.pt Y) :=
  @dite _ (RunCut g) (Classical.propDecidable _)
    (fun _ => (Polygraph.cell (P := (chContraction K).poly) g).toPath)
    (fun _ => (exists_runCutPath' (chCutHom g.gen g.not_mem) g.rep_dom g.rep_cod).choose)

theorem all_atomWord {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) (atomWord g) := by
  by_cases h : RunCut g
  · rw [atomWord, dif_pos h]
    exact Quiver.Path.all_toPath.mpr h
  · rw [atomWord, dif_neg h]
    exact (exists_runCutPath' (chCutHom g.gen g.not_mem) g.rep_dom g.rep_cod).choose_spec.1

/-- **A kept 1-cell spells itself.** -/
theorem atomWord_self {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y)
    (h : RunCut g) :
    atomWord g = (Polygraph.cell (P := (chContraction K).poly) g).toPath := by
  rw [atomWord, dif_pos h]

/-- **Each 1-cell and its atom word name one arrow** — the dimension-one half of `Spans`. -/
theorem quot_atomWord {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    (chContraction K).poly.quot.map (atomWord g)
      = (chContraction K).poly.quot.map
        (Polygraph.cell (P := (chContraction K).poly) g).toPath := by
  by_cases h : RunCut g
  · rw [atomWord_self g h]
  · refine poly_quot_congr ?_
    rw [atomWord, dif_neg h]
    exact ((exists_runCutPath' (chCutHom g.gen g.not_mem) g.rep_dom g.rep_cod).choose_spec.2).trans
      (backQuot_gen g).symm

/-- **The cuts out of the runs span every bead cut**, for every `K` and with no hypothesis on
`K`. -/
noncomputable def runCutSpans (K : BPSet) :
    Spans (chContraction K).poly RunCut (fun _ => True) where
  word := atomWord
  word_all := all_atomWord
  word_eq := quot_atomWord
  word_self := atomWord_self
  cell_derivable := fun {x y} α => by
    exact Polygraph.quot_src_tgt (Polygraph.sub (P := (chContraction K).poly)
      (fun {_ _} => RunCut) (fun {_ _} _ => True) (fun {_ _} => atomWord)
      (fun {_ _} => all_atomWord)) (x := ⟨x.as⟩) (y := ⟨y.as⟩) ⟨α, trivial⟩

/-- **`Ch(K)[W⁻¹]` presented by the bead cuts out of the runs**, for every `K` and with no
hypothesis on `K`. -/
noncomputable def chAtomPresentation (K : BPSet) :
    Presents (runCutSpans K).poly (((W K).op).Localization) :=
  (chRunPresentation K).restrictCells (runCutSpans K)

end ChainCat
