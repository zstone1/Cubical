import CubeChains.Machinery.Presentation.ContractMap
import CubeChains.Machinery.Presentation.LocalizeCut
import CubeChains.Concurrency.Presentation.LiftLocalize
import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/RunContract — the cut presentation contracted onto the runs

Every chain is entered from the run on its own events by exactly one merge (`existsUnique_W_ones`),
so the merges `Machinery/Presentation/LocalizeCut` inverts contract away: `chRunPresentation` keeps
one 0-cell per run and one 1-cell per bead cut that braids.

The contraction is built over an arbitrary fibre presheaf, where `K` never appears.  `eltRep`
restricts an element along the merge out of its run; `word_comp_of_S` is the uniqueness of that
merge, which is `eq_of_W` downstairs in `Ch Zbp`; and `eltRep_natural` — restriction commuting with
a map of presheaves — is the whole of the functoriality.
-/

open CategoryTheory CubeChains BPSet Opposite

namespace ChainCat

/-! ## A factor of a merge is a merge

Crossings add along a composite, and a merge makes none. -/

theorem W_of_comp {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K f ∧ W K g := by
  have h0 := permLen_crossPerm_comp (rfl : dimSum a.dims = dimSum a.dims) f g
  rw [(W_iff_crossPerm_eq_one rfl (f ≫ g)).mp h, permLen_one] at h0
  exact ⟨(W_iff_crossPerm_eq_one rfl f).mpr (eq_one_of_permLen_eq_zero _ (by omega)),
    (W_iff_crossPerm_eq_one (tgtStrands f rfl) g).mpr (eq_one_of_permLen_eq_zero _ (by omega))⟩

theorem W_of_comp_left {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K f := (W_of_comp f g h).1

theorem W_of_comp_right {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K g := (W_of_comp f g h).2

/-! ## A cut word crosses nothing exactly when its letters do not -/

/-- **Every letter of a crossing-free cut word is a merge.** -/
theorem Cut.all_mergeGen_of_W : ∀ {x y : GenObj Cut.Refine} (R : Quiver.Path x y),
    W Zbp (Cut.ev R) → Quiver.Path.All (fun ⦃_ _⦄ e => Cut.mergeGen e) R := by
  intro x y R
  induction R with
  | nil => exact fun _ => Quiver.Path.all_nil _
  | cons R e ih =>
      intro hW
      rw [Cut.ev_cons] at hW
      refine (Quiver.Path.all_cons_iff R e).mpr ⟨ih (W_of_comp_right _ _ hW), ?_⟩
      exact (merge_iff (Cut.genHom e)).mpr ⟨W_of_comp_left _ _ hW, Cut.codim_genHom e⟩

/-- **…and conversely, a cut word of merges crosses nothing.** -/
theorem Cut.W_ev_of_all_mergeGen : ∀ {x y : GenObj Cut.Refine} (R : Quiver.Path x y),
    Quiver.Path.All (fun ⦃_ _⦄ e => Cut.mergeGen e) R → W Zbp (Cut.ev R) := by
  intro x y R
  induction R with
  | nil => intro _; rw [Cut.ev_nil]; exact MorphismProperty.id_mem _ _
  | cons R e ih =>
      intro h
      rw [Quiver.Path.all_cons_iff] at h
      rw [Cut.ev_cons]
      exact (W Zbp).comp_mem _ _ (merge_le_W Zbp _ h.2) (ih h.1)

/-! ## The run on a chain's own events -/

/-- The run on a chain's own events. -/
def zRep (d : Ch Zbp) : Ch Zbp := zObj (𝟙^(dimSum d.dims))

@[simp] theorem dimSum_zRep (d : Ch Zbp) : dimSum (zRep d).dims = dimSum d.dims :=
  dimSum_replicate _

theorem zRep_idem (d : Ch Zbp) : zRep (zRep d) = zRep d :=
  congrArg (fun N => zObj (𝟙^N)) (dimSum_zRep d)

/-- The merge from the run on a chain's own events. -/
noncomputable def zRunMerge (d : Ch Zbp) : zRep d ⟶ d := runMerge d rfl

theorem W_zRunMerge (d : Ch Zbp) : W Zbp (zRunMerge d) := W_runMerge d rfl

/-- A cut word spelling a refinement. -/
noncomputable def cutPath {a b : Ch Zbp} (f : a ⟶ b) : Quiver.Path (Cut.vert b) (Cut.vert a) :=
  (Cut.exists_path (codim f) f le_rfl).choose

theorem ev_cutPath {a b : Ch Zbp} (f : a ⟶ b) : Cut.ev (cutPath f) = f :=
  (Cut.exists_path (codim f) f le_rfl).choose_spec

/-- …spelled by bead cuts. -/
noncomputable def runCutWord (d : Ch Zbp) : Quiver.Path (Cut.vert d) (Cut.vert (zRep d)) :=
  cutPath (zRunMerge d)

theorem ev_runCutWord (d : Ch Zbp) : Cut.ev (runCutWord d) = zRunMerge d := ev_cutPath _

theorem all_runCutWord (d : Ch Zbp) :
    Quiver.Path.All (fun ⦃_ _⦄ e => Cut.mergeGen e) (runCutWord d) :=
  Cut.all_mergeGen_of_W _ (by rw [ev_runCutWord]; exact W_zRunMerge d)

/-- **The merge onto the run, as an arrow of `(Ch Zbp)ᵒᵖ`.** -/
theorem eval_runCutWord (d : Ch Zbp) :
    zCutPresentation.eval.map (runCutWord d) = (zRunMerge d).op :=
  congrArg Quiver.Hom.op (ev_runCutWord d)

/-! ## Restricting an element of the fibre presheaf

A 0-cell of the bead-cut polygraph of `∫F` is a shape carrying an element over it, and a refinement
of the shape restricts the element.  `K` enters only as the fibre presheaf. -/

section Elements

variable {F : (Ch Zbp)ᵒᵖ ⥤ Type}

local notation "EC" => zCutPresentation.elementsPoly F

local notation "ES" => zCutPresentation.elementsPicked F Cut.mergeGen

local notation "EG" => Polygraph.InvGen (EC) (ES)

local notation "EP" => Polygraph.invPoly (EC) (ES)

local notation "EV" => zCutPresentation.elementsV F

local notation "EO" => GenObj (zCutPresentation.elementsGen F)

local notation "EQ" => zCutPresentation.elementsProj F

local notation "Efwd" => Polygraph.fwdPre (EC) (ES)

local notation "allS" => Quiver.Path.All (fun ⦃_ _⦄ e => (ES) e)

/-- Restricting twice along the opposite of a composite. -/
theorem map_op_comp {x y z : Ch Zbp} (u : y ⟶ x) (v : z ⟶ y) (t : F.obj (op x)) :
    F.map v.op (F.map u.op t) = F.map (v ≫ u).op t :=
  (congrArg (fun g : F.obj (op x) ⟶ F.obj (op z) => g t) (F.map_comp u.op v.op)).symm

/-- A 0-cell, restricted along a refinement of its shape. -/
def eltRestrict (z : EV) {e : Ch Zbp} (u : e ⟶ z.1) : EV := ⟨e, F.map u.op z.2⟩

theorem eltRestrict_comp (z : EV) {e e' : Ch Zbp} (u : e ⟶ z.1) (v : e' ⟶ e) :
    eltRestrict (eltRestrict z u) v = eltRestrict z (v ≫ u) :=
  congrArg (fun t => (⟨e', t⟩ : EV)) (map_op_comp u v z.2)

/-- **Two merges into one shape restrict an element the same way** — `eq_of_W` pins the merge, so
the restriction sees only the shape it lands on. -/
theorem eltRestrict_eq_of_W (z : EV) {e e' : Ch Zbp} {u : e ⟶ z.1} {v : e' ⟶ z.1} (h : e = e')
    (hu : W Zbp u) (hv : W Zbp v) : eltRestrict z u = eltRestrict z v := by
  subst h
  rw [eq_of_W hu hv]

/-- **The run on a 0-cell's own events** — restriction along the merge out of it. -/
noncomputable def eltRep (z : EV) : EV := eltRestrict z (zRunMerge z.1)

theorem eltRep_idem (z : EV) : eltRep (eltRep z) = eltRep z :=
  (eltRestrict_comp z (zRunMerge z.1) (zRunMerge (zRep z.1))).trans
    (eltRestrict_eq_of_W z (zRep_idem z.1)
      ((W Zbp).comp_mem _ _ (W_zRunMerge (zRep z.1)) (W_zRunMerge z.1)) (W_zRunMerge z.1))

/-- **The run of a generator's target, read at its source** — restriction along the composite. -/
theorem eltRep_eq_eltRestrict {a b : EV} (e : (EC).Gen a b) :
    eltRep b = eltRestrict a (zRunMerge b.1 ≫ Cut.genHom e.1) :=
  congrArg (fun t => (⟨zRep b.1, t⟩ : EV))
    ((congrArg (F.map (zRunMerge b.1).op) e.2.symm).trans
      (map_op_comp (Cut.genHom e.1) (zRunMerge b.1) a.2))

/-- **A merge does not change the run** — the two merges into its source agree. -/
theorem eltRep_eq_of_mergeGen {a b : EV} (e : (EC).Gen a b) (he : (ES) e) :
    eltRep a = eltRep b := by
  rw [eltRep_eq_eltRestrict e]
  exact eltRestrict_eq_of_W a
    (congrArg (fun N => zObj (𝟙^N)) (dimSum_eq_of_hom (Cut.genHom e.1)).symm)
    (W_zRunMerge a.1) ((W Zbp).comp_mem _ _ (W_zRunMerge b.1) (merge_le_W Zbp _ he))

/-- **Restriction is natural in the fibre presheaf** — a map of presheaves moves no shape, so it
commutes with restricting along one, which is the whole of the functoriality below. -/
theorem eltRestrict_natural {F' : (Ch Zbp)ᵒᵖ ⥤ Type} (τ : F ⟶ F') (z : EV) {e : Ch Zbp}
    (u : e ⟶ z.1) :
    eltRestrict (⟨z.1, τ.app _ z.2⟩ : zCutPresentation.elementsV F') u
      = ⟨(eltRestrict z u).1, τ.app _ (eltRestrict z u).2⟩ :=
  congrArg (fun t => (⟨e, t⟩ : zCutPresentation.elementsV F'))
    (NatTrans.naturality_apply τ u.op z.2).symm

/-- …so the run is, the merge out of it depending on the shape alone. -/
theorem eltRep_natural {F' : (Ch Zbp)ᵒᵖ ⥤ Type} (τ : F ⟶ F') (z : EV) :
    eltRep (⟨z.1, τ.app _ z.2⟩ : zCutPresentation.elementsV F')
      = ⟨(eltRep z).1, τ.app _ (eltRep z).2⟩ :=
  eltRestrict_natural τ z (zRunMerge z.1)

/-! ## The merge onto the run, lifted -/

/-- The cut word onto the run, lifted from the element it acts on. -/
noncomputable def eltRunWord (z : EV) : Quiver.Path (⟨z⟩ : EO) ⟨eltRep z⟩ :=
  zCutPresentation.wordLift F (runCutWord z.1)
    (congrArg (fun g => F.map g z.2) (eval_runCutWord z.1))

theorem all_eltRunWord (z : EV) : allS (eltRunWord z) :=
  zCutPresentation.all_elementsPicked_wordLift F Cut.mergeGen _ (all_runCutWord z.1)

theorem elementsProj_eltRunWord (z : EV) : (EQ).mapPath (eltRunWord z) = runCutWord z.1 :=
  zCutPresentation.elementsProj_mapPath_wordLift F _ _

/-- …in the extension by formal inverses. -/
noncomputable def eltRunInvWord (z : EV) : Quiver.Path (⟨z⟩ : GenObj EG) ⟨eltRep z⟩ :=
  (Efwd).mapPath (eltRunWord z)

/-- **Reindexing lifts the same cut word onto the run** — the word is chosen from the shape, a
map of presheaves moves no shape, and a lifted word is pinned by its projection. -/
theorem elementsQuiver_mapPath_eltRunWord {F' : (Ch Zbp)ᵒᵖ ⥤ Type} (τ : F ⟶ F') (z : EV) :
    (zCutPresentation.elementsQuiver τ).mapPath (eltRunWord z)
      = cellCongr Quiver.Path rfl
          (congrArg (fun w : zCutPresentation.elementsV F' =>
            (⟨w⟩ : GenObj (zCutPresentation.elementsGen F'))) (eltRep_natural τ z))
          (eltRunWord (⟨z.1, τ.app _ z.2⟩ : zCutPresentation.elementsV F')) := by
  refine Eq.trans (zCutPresentation.elementsQuiver_mapPath_wordLift F τ (runCutWord z.1) _
    ((congrArg (fun g => F'.map g (τ.app _ z.2)) (eval_runCutWord z.1)).trans
      (NatTrans.naturality_apply τ (zRunMerge z.1).op z.2).symm)) ?_
  refine (zCutPresentation.eq_wordLift F' _ _ ?_).symm
  refine Eq.trans (Prefunctor.mapPath_cellCongr (zCutPresentation.elementsProj F') rfl _ _) ?_
  refine Eq.trans (congrArg (cellCongr Quiver.Path rfl _) (elementsProj_eltRunWord _)) ?_
  exact cellCongr_self Quiver.Path _ _ _

/-! ## Merging to the run, as an arrow of the extension

Two words of `∫F` agree as soon as the base arrows they evaluate to do (`elt_quot_eq_of_ev_eq`, the
presentation being complete), and two merges out of a run with equal endpoints *are* equal
(`eq_of_W`): together they make merging onto the run natural in the 1-cells. -/

/-- **Two words of `∫F` with the same value agree** — a morphism of elements is the base arrow it
lies over, and the presentation is complete. -/
theorem elt_quot_eq_of_ev_eq {X Y : EO} (R R' : Quiver.Path X Y)
    (h : Cut.ev ((EQ).mapPath R) = Cut.ev ((EQ).mapPath R')) :
    (EC).quot.map R = (EC).quot.map R' :=
  (zCutPresentation.elements F).E.map_injective
    (Subtype.ext ((zCutPresentation.elements_eval_val F R).trans
      ((congrArg Quiver.Hom.op h).trans (zCutPresentation.elements_eval_val F R').symm)))

/-- **A word of `∫F` spelled by merges performs a merge.** -/
theorem W_elt_ev_of_all {X Y : EO} (R : Quiver.Path X Y) (hR : allS R) :
    W Zbp (Cut.ev ((EQ).mapPath R)) :=
  Cut.W_ev_of_all_mergeGen _ (Quiver.Path.All.mapPath (EQ) (fun _ he => he) hR)

/-- **…so two such words with the same endpoints agree** — `eq_of_W` pins the merge they perform,
and the presentation is complete.  This is the whole of the contraction's functoriality. -/
theorem elt_quot_eq_of_all_mergeGen {X Y : EO} (R R' : Quiver.Path X Y) (hR : allS R)
    (hR' : allS R') : (EC).quot.map R = (EC).quot.map R' :=
  elt_quot_eq_of_ev_eq R R' (eq_of_W (W_elt_ev_of_all R hR) (W_elt_ev_of_all R' hR'))

/-- The generators the localization inverts: the merges, and the formal inverses adjoined to
them. -/
def Cut.merged {F : (Ch Zbp)ᵒᵖ ⥤ Type} {a b : zCutPresentation.elementsV F} :
    Polygraph.InvGen (zCutPresentation.elementsPoly F)
        (zCutPresentation.elementsPicked F Cut.mergeGen) a b → Prop
  | .inl e => zCutPresentation.elementsPicked F Cut.mergeGen e
  | .inr _ => True

theorem eltRep_eq_of_merged {a b : EV} (g : EG a b) (h : Cut.merged g) : eltRep a = eltRep b := by
  rcases g with e | ⟨e, he⟩
  · exact eltRep_eq_of_mergeGen e h
  · exact (eltRep_eq_of_mergeGen e he).symm

/-- The merge onto the run, as an arrow. -/
noncomputable def eltRunArrow (z : EV) : (⟨⟨z⟩⟩ : (EP).presented) ⟶ ⟨⟨eltRep z⟩⟩ :=
  (EP).quot.map (eltRunInvWord z)

/-- The renaming of runs a merged generator induces. -/
noncomputable def eltRepHom {a b : EV} (h : eltRep a = eltRep b) :
    (⟨⟨eltRep a⟩⟩ : (EP).presented) ⟶ ⟨⟨eltRep b⟩⟩ :=
  eqToHom (congrArg (fun z : EV => (⟨⟨z⟩⟩ : (EP).presented)) h)

theorem eltRepHom_trans {a b : EV} (h : eltRep a = eltRep b) (h' : eltRep b = eltRep a) :
    eltRepHom h ≫ eltRepHom h' = 𝟙 (⟨⟨eltRep a⟩⟩ : (EP).presented) := by
  rw [eltRepHom, eltRepHom, eqToHom_trans, eqToHom_refl]

/-- **Merging `a` to its run is the merge `a ⟶ b` followed by merging `b`** — at a merge
generator. -/
theorem eltRunArrow_fwd {a b : EV} (e : (EC).Gen a b) (he : (ES) e) :
    eltRunArrow a ≫ eltRepHom (eltRep_eq_of_mergeGen e he)
      = Polygraph.fwdArrow (EC) (ES) e ≫ eltRunArrow b := by
  have hv : (⟨eltRep a⟩ : EO) = ⟨eltRep b⟩ :=
    congrArg (fun z : EV => (⟨z⟩ : EO)) (eltRep_eq_of_mergeGen e he)
  have hev := elt_quot_eq_of_all_mergeGen (cellCongr Quiver.Path rfl hv (eltRunWord a))
    ((Polygraph.cell e).toPath.comp (eltRunWord b))
    ((Quiver.Path.all_cellCongr _ _ _).mpr (all_eltRunWord a))
    (Quiver.Path.All.comp (Quiver.Path.all_toPath.mpr he) (all_eltRunWord b))
  refine Eq.trans (Polygraph.quot_map_cellCongr (EP)
    (congrArg (fun z : EV => (⟨z⟩ : GenObj EG)) (eltRep_eq_of_mergeGen e he))
      (eltRunInvWord a)).symm ?_
  refine Eq.trans (congrArg (fun t => (EP).quot.map t)
    (Prefunctor.mapPath_cellCongr (Efwd) rfl hv (eltRunWord a)).symm) ?_
  refine Eq.trans (Polygraph.Hom.quot_map_congr (Polygraph.invIncl (EC) (ES)) hev) ?_
  exact Eq.trans (congrArg (fun t => (EP).quot.map t)
      (Prefunctor.mapPath_comp (Efwd) (Polygraph.cell e).toPath (eltRunWord b)))
    (Polygraph.quot_map_comp (EP) _ _)

/-- **…and at a formal inverse**, by cancelling the merge it inverts. -/
theorem eltRunArrow_bwd {a b : EV} (e : (EC).Gen b a) (he : (ES) e) :
    eltRunArrow a ≫ eltRepHom (eltRep_eq_of_mergeGen e he).symm
      = Polygraph.bwdArrow (EC) (ES) e he ≫ eltRunArrow b := by
  have hcancel : Polygraph.bwdArrow (EC) (ES) e he
      ≫ (eltRunArrow b ≫ eltRepHom (eltRep_eq_of_mergeGen e he)) = eltRunArrow a := by
    rw [eltRunArrow_fwd e he, ← Category.assoc, Polygraph.bwdArrow_fwdArrow, Category.id_comp]
  rw [← hcancel, Category.assoc, Category.assoc, eltRepHom_trans, Category.comp_id]

/-- **Merging to the run factors through any inverted generator.** -/
theorem eltRunArrow_step {a b : EV} (g : EG a b) (h : Cut.merged g) :
    eltRunArrow a ≫ eltRepHom (eltRep_eq_of_merged g h)
      = (EP).quot.map (Polygraph.cell (P := (EP)) g).toPath ≫ eltRunArrow b := by
  rcases g with e | ⟨e, he⟩
  · exact eltRunArrow_fwd e h
  · exact eltRunArrow_bwd e he

/-! ## The contraction -/

variable (F) in
/-- **The merges of the cut presentation of `∫F` contract onto the runs.** -/
noncomputable def eltRunContraction : Contraction (EP) Cut.merged where
  rep := eltRep
  rep_idem := eltRep_idem
  word := eltRunInvWord
  word_all z := Quiver.Path.All.mapPath (Efwd) (fun _ he => he) (all_eltRunWord z)
  invWord z := Polygraph.invWord (EC) (ES) (eltRunWord z) (all_eltRunWord z)
  invWord_all z :=
    Polygraph.all_invWord (EC) (ES) (fun _ _ => trivial) (eltRunWord z) (all_eltRunWord z)
  word_invWord z := (Polygraph.quot_map_comp (EP) _ _).trans
    (Polygraph.quot_fwd_invWord (EC) (ES) (eltRunWord z) (all_eltRunWord z))
  invWord_word z := (Polygraph.quot_map_comp (EP) _ _).trans
    (Polygraph.quot_invWord_fwd (EC) (ES) (eltRunWord z) (all_eltRunWord z))
  rep_eq_of_S {_ _} g h := eltRep_eq_of_merged g h
  word_comp_of_S g h :=
    (Polygraph.quot_map_cellCongr (EP) _ _).trans
      ((eltRunArrow_step g h).trans (Polygraph.quot_map_comp (EP) _ _).symm)

end Elements

/-! ## …as a functor of the fibre presheaf -/

/-- **The bead cuts of `∫F` with the merges inverted, as a functor of the fibre presheaf.** -/
noncomputable def eltLocFunctor : ((Ch Zbp)ᵒᵖ ⥤ Type) ⥤ Polygraph :=
  Polygraph.invFunctor zCutPresentation.elementsPolyFunctor
    (fun F => zCutPresentation.elementsPicked F Cut.mergeGen)
    fun {_ _} τ _ _ e he => zCutPresentation.elementsPicked_map Cut.mergeGen τ e he

section Functorial

variable {F F' : (Ch Zbp)ᵒᵖ ⥤ Type} (τ : F ⟶ F')

local notation "SF" => zCutPresentation.elementsPicked F Cut.mergeGen

local notation "SF'" => zCutPresentation.elementsPicked F' Cut.mergeGen

local notation "τS" => fun e he => zCutPresentation.elementsPicked_map Cut.mergeGen τ e he

/-- **A map of presheaves carries the contraction along** — it moves no base 1-cell, so it reflects
the merges, and `eltRep_natural` is the rest. -/
noncomputable def eltRunMap : Contraction.Map (eltRunContraction F) (eltRunContraction F') where
  hom := eltLocFunctor.map τ
  mem_iff g := by rcases g with e | ⟨e, he⟩ <;> exact Iff.rfl
  rep_hom z := eltRep_natural τ z
  word_hom z := Polygraph.invPolyMap_mapPath_fwd_cellCongr SF SF'
    (zCutPresentation.elementsPolyFunctor.map τ) τS _ _ _
    (elementsQuiver_mapPath_eltRunWord τ z)
  invWord_hom z := Polygraph.invPolyMap_mapPath_invWord_cellCongr SF SF'
    (zCutPresentation.elementsPolyFunctor.map τ) τS _ (all_eltRunWord z) _ _
    (elementsQuiver_mapPath_eltRunWord τ z) (all_eltRunWord _)

end Functorial

/-- **The contracted polygraph, as a functor of the fibre presheaf.** -/
noncomputable def eltRunFunctor : ((Ch Zbp)ᵒᵖ ⥤ Type) ⥤ Polygraph :=
  Contraction.Map.polyFunctor eltLocFunctor (fun _ => Cut.merged) eltRunContraction
    (fun τ => eltRunMap τ) fun _ => rfl

/-! ## At a cube chain set

`wedgeHoms K` is the fibre presheaf of `Ch K` over `Ch Zbp`, so the contraction above *is* the one
at `K`, and the functor is the one of `K`. -/

/-- **Every chain over `K` is merged into from the run on its own events, canonically.** -/
noncomputable def chContraction (K : BPSet) : Contraction (chCutLocFunctor.obj K) Cut.merged :=
  eltRunContraction (wedgeHoms K)

/-- **`Ch(K)[W⁻¹]`, presented on the runs** — one 0-cell per run, and one 1-cell per bead cut that
braids, for every `K` and with no hypothesis on `K`. -/
noncomputable def chRunPresentation (K : BPSet) :
    Presents (chContraction K).poly (((W K).op).Localization) :=
  (chCutLocPresentation K).contract (chContraction K)

/-- …and the polygraph is a functor of `K`. -/
noncomputable def chRunFunctor : BPSet ⥤ Polygraph := wedgeHomsFunctor ⋙ eltRunFunctor

/-! ## At the base -/

/-- **The merges of the cut presentation contract onto the runs.** -/
noncomputable def zCutContraction : Contraction (chCutLocFunctor.obj Zbp) Cut.merged :=
  chContraction Zbp

/-- **The cut presentation of `Ch(Z)[W⁻¹]`, contracted onto the runs** — one 0-cell per run, and
one 1-cell per bead cut that braids. -/
noncomputable def zRunPresentation :
    Presents zCutContraction.poly (((W Zbp).op).Localization) :=
  chRunPresentation Zbp

end ChainCat
