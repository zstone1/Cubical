import CubeChains.Concurrency.Presentation.RunReduce

/-!
# Concurrency/Presentation/RunArrows — a refinement of `Ch K`, as a word of bead cuts

The fibration over `Ch Zbp` is discrete, so a 0-cell of the lifted cut polygraph *is* a chain of `K`
and a refinement upstairs is one downstairs carrying the element (`hom_ext_baseHom`).  `chPath`
spells such a refinement as a word of bead cuts, and `RunCut` names the letters the atoms out of the
runs keep:

    run b ──merge──▸ b ──u──▸ a ◂──merge── run a
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
    W Zbp (baseHom f) ↔ W K f := W_iff_of_φ rfl

/-! ## A refinement, spelled by bead cuts -/

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

theorem Cut.ev_comp {x y z : GenObj Cut.Refine} (R : Quiver.Path x y) (R' : Quiver.Path y z) :
    Cut.ev (R.comp R') = Cut.ev R' ≫ Cut.ev R := by
  induction R' with
  | nil => exact (Category.id_comp _).symm
  | cons R' e ih => rw [Quiver.Path.comp_cons, Cut.ev_cons, Cut.ev_cons, ih, Category.assoc]

/-- A merge word, spelled out of the inverted 1-cells. -/
theorem all_chPath_of_W {a b : (chCutPoly K).V} (f : vChain a ⟶ vChain b) (hf : W K f) :
    Quiver.Path.All (fun ⦃_ _⦄ e => chCutPicked K e) (chPath f) :=
  zCutPresentation.all_elementsPicked_wordLift (wedgeHoms K) Cut.mergeGen _
    (Cut.all_mergeGen_of_W _ (by rw [ev_cutPath]; exact (W_baseHom_iff f).mpr hf))

/-! ## The merge onto a 0-cell's run -/

/-- The merge onto a 0-cell's run. -/
noncomputable def runMergeK (z : (chCutPoly K).V) : vChain (eltRep z) ⟶ vChain z :=
  liftOf (zRunMerge (shOf z)) rfl

theorem W_runMergeK (z : (chCutPoly K).V) : W K (runMergeK z) :=
  (W_baseHom_iff _).mp (W_zRunMerge _)

/-- **A merge names a renaming of runs.** -/
theorem eltRep_eq_of_W {a b : (chCutPoly K).V} (u : vChain b ⟶ vChain a) (hu : W K u) :
    eltRep b = eltRep a :=
  (congrArg eltRep (show b = eltRestrict a (baseHom u) from
      congrArg (fun t => (⟨shOf b, t⟩ : (chCutPoly K).V)) u.w.symm)).trans
    ((eltRestrict_comp a (baseHom u) (zRunMerge (shOf b))).trans
      (eltRestrict_eq_of_W a (congrArg (fun n => zObj (𝟙^n)) (dimSum_eq_of_hom (baseHom u)))
        ((W Zbp).comp_mem _ _ (W_zRunMerge (shOf b)) ((W_baseHom_iff u).mpr hu))
        (W_zRunMerge (shOf a))))

/-! ## Reading a 1-cell of the contraction -/

/-- The refinement of `Ch K` a bead cut of the lifted polygraph performs. -/
noncomputable def chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    vChain b ⟶ vChain a :=
  liftOf (Cut.genHom e.1) (map_cutHom e)

/-! ## The atoms out of the runs -/

/-- **The 1-cells to keep**: those whose bead cut starts at a run. -/
def RunCut {x y : (chCollapse K).V} (g : (chCollapse K).Gen x y) : Prop :=
  eltRep g.cod = g.cod

/-- **An atom out of a run**: a 1-cell of the contraction whose bead cut starts at a run. -/
abbrev RunAtom (K : BPSet) : (chCollapse K).V → (chCollapse K).V → Type :=
  keptGen (P := (chCollapse K).poly) RunCut

/-- The number of events a 0-cell carries. -/
abbrev vCount (z : (chCutPoly K).V) : ℕ := dimSum (shOf z).dims

end ChainCat
