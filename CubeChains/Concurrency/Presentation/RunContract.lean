import CubeChains.Machinery.Presentation.ContractMap
import CubeChains.Concurrency.Presentation.LiftLocalize
import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/RunContract — the cut presentation contracted onto the runs

Every chain is entered from the run on its own events by exactly one merge (`existsUnique_W_ones`),
so the merges `CutPresentation` inverts contract away: `chRunPresentation` keeps
one 0-cell per run and one 1-cell per bead cut that braids.

The contraction is built over an arbitrary fibre presheaf, where `K` never appears.  `eltRep`
restricts an element along the merge out of its run; `word_comp_of_S` is the uniqueness of that
merge, which is `eq_of_W` downstairs in `Ch Zbp`; and `eltRep_natural` — restriction commuting with
a map of presheaves — is the whole of the functoriality.
-/

open CategoryTheory CubeChains BPSet Opposite

namespace ChainCat

/-! ## A factor of a merge is a merge

Flatness is inherited by factors (`Flat.of_comp`), so a merge leaves neither leg a reordering to
undo. -/

theorem W_of_comp {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K f ∧ W K g :=
  have h0 := Flat.of_comp f g (flat_of_W h)
  ⟨(W_iff_flat f).mpr h0.1, (W_iff_flat g).mpr h0.2⟩

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

local notation "EV" => zCutPresentation.elementsV F

local notation "EO" => GenObj (zCutPresentation.elementsGen F)

local notation "EQ" => zCutPresentation.elementsProj F

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

/-! ## The collapse -/

variable (F) in
/-- **The merges of the cut presentation of `∫F` collapse onto the runs.** -/
noncomputable def eltRunCollapse : Collapse (EC) (ES) where
  rep := eltRep
  rep_idem := eltRep_idem
  word := eltRunWord
  word_all := all_eltRunWord
  rep_eq_of_S h := eltRep_eq_of_mergeGen _ h
  word_comp_of_S _ h := elt_quot_eq_of_all_mergeGen _ _
    ((Quiver.Path.all_cellCongr _ _ _).mpr (all_eltRunWord _))
    (Quiver.Path.All.comp (Quiver.Path.all_toPath.mpr h) (all_eltRunWord _))

end Elements

/-! ## …as a functor of the fibre presheaf -/

section Functorial

variable {F F' : (Ch Zbp)ᵒᵖ ⥤ Type} (τ : F ⟶ F')

/-- **A map of presheaves carries the collapse along** — it moves no base 1-cell, so it reflects
the merges, and `eltRep_natural` is the rest. -/
noncomputable def eltRunMap : Collapse.Map (eltRunCollapse F) (eltRunCollapse F') where
  hom := zCutPresentation.elementsPolyFunctor.map τ
  mem_iff _ := Iff.rfl
  rep_hom z := eltRep_natural τ z

end Functorial

/-! ## At a cube chain set

`wedgeHoms K` is the fibre presheaf of `Ch K` over `Ch Zbp`, so the collapse above *is* the one at
`K`, and the functor is the one of `K`. -/

/-- **Every chain over `K` is merged into from the run on its own events, canonically.** -/
noncomputable def chCollapse (K : BPSet) :
    Collapse (chCutPoly K) (chPicked zCutPresentation Cut.mergeGen K) :=
  eltRunCollapse (wedgeHoms K)

/-- **`Ch(K)[W⁻¹]`, presented on the runs** — one 0-cell per run, and one 1-cell per bead cut that
braids, for every `K` and with no hypothesis on `K`. -/
noncomputable def chRunPresentation (K : BPSet) :
    Presents (chCollapse K).poly (((W K).op).Localization) :=
  (chCutPresentation K).collapse (chCollapse K)
    (multiplicativeClosure_chPicked zCutPresentation Cut.mergeGen
      W_op_eq_multiplicativeClosure_mergeGen K)

end ChainCat
