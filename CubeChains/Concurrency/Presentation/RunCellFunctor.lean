import CubeChains.Concurrency.Presentation.RunCells

/-!
# Concurrency/Presentation/RunCellFunctor — the atom words, carried along a map of `K`

A map of `K` moves the element a chain carries and no shape, so every choice `runCellWord` makes is
untouched: `RunCut` asks only that a shape be a run (`eltRep_eq_self_iff`), hence is reflected as
well as preserved, and the chosen climb is chosen from shapes alone, hence is the *same* climb.
What is left is the naturality square of the fibre presheaf, which moves `runObj` and the atoms.
-/

open CategoryTheory BPSet CubeChains

namespace ChainCat

variable {K K' : BPSet} (f : K ⟶ K')

/-! ## The contraction, carried along a map of `K` -/

/-- **A map of `K` carries the collapse along** — it is `eltRunMap` at the wedge presheaf. -/
noncomputable def chRunMap : Collapse.Map (chCollapse K) (chCollapse K') :=
  eltRunMap (wedgeHomsFunctor.map f)

theorem eltRestrict_chRunMap {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    eltRestrict ((chRunMap f).obj z) w = (chRunMap f).obj (eltRestrict z w) :=
  eltRestrict_natural (wedgeHomsFunctor.map f) z w

/-! ## The kept cells, carried along

`RunCut` asks that a 0-cell's shape be a run, and shapes are untouched, so it is reflected as well
as preserved. -/

theorem runCut_chRunMap_iff {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    RunCut ((chRunMap f).pre.map (Polygraph.cell (P := (chCollapse K).poly) g)) ↔ RunCut g :=
  (eltRep_eq_self_iff _).trans (eltRep_eq_self_iff g.cod).symm

/-! ## The run of a chain, and the atoms out of it -/

/-- **The 0-cell a run names moves with the element**, and with nothing else. -/
theorem runObj_chRunMap {N : ℕ} {z : (chCutPoly K).V} (a : RunPerm N z) :
    runObj (K := K') (z := (chRunMap f).obj z) a = (chRunMap f).vtx (runObj a) :=
  Subtype.ext (eltRestrict_chRunMap f a.arr)

/-- A bead cut is pinned by the base cut it carries. -/
private theorem gen_heq {a b a' b' : (chCutPoly K).V} (ha : a = a') (hb : b = b')
    {e : (chCutPoly K).Gen a b} {e' : (chCutPoly K).Gen a' b'} (h : e.1 ≍ e'.1) : e ≍ e' := by
  subst ha; subst hb
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

/-- **The atom an ascent names is the atom its leg names at `K'`** — the leg is a base arrow, so the
two 1-cells carry one cut and differ only in the runs naming their ends. -/
theorem pre_map_ascAtom {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (e : Ascent (runDescents N z).perm a b) :
    (chRunMap f).pre.map (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e))
      = Quiver.homOfEq
          (Polygraph.cell (P := (chCollapse K').poly)
            (ascAtom (z := (chRunMap f).obj z) e))
          (congrArg GenObj.mk (runObj_chRunMap f a)) (congrArg GenObj.mk (runObj_chRunMap f b)) :=
  Collapse.gen_eq_homOfEq (runObj_chRunMap f a) (runObj_chRunMap f b) _ _
    (eltRestrict_chRunMap f (ascLeg e))
    (eltRestrict_chRunMap f (atomOnes N e.idx ≫ ascLeg e))
    (gen_heq (eltRestrict_chRunMap f (ascLeg e))
      (eltRestrict_chRunMap f (atomOnes N e.idx ≫ ascLeg e)) HEq.rfl)

/-- **…so a climb spells the same climb at `K'`.** -/
theorem pre_mapPath_climbPath {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) :
    (chRunMap f).pre.mapPath (climbPath R)
      = cellCongr Quiver.Path (congrArg (chCollapse K').poly.pt (runObj_chRunMap f a))
          (congrArg (chCollapse K').poly.pt (runObj_chRunMap f b))
          (climbPath (K := K') (z := (chRunMap f).obj z) R) := by
  induction R with
  | nil => exact (cellCongr_self Quiver.Path rfl rfl _).symm.trans (cellCongr_nil_eq rfl rfl _ _)
  | @cons bmid v R e ih =>
      have hletter : (chRunMap f).pre.mapPath
            (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath
          = cellCongr Quiver.Path (congrArg (chCollapse K').poly.pt (runObj_chRunMap f bmid))
              (congrArg (chCollapse K').poly.pt (runObj_chRunMap f v))
              (Polygraph.cell (P := (chCollapse K').poly)
                (ascAtom (z := (chRunMap f).obj z) e)).toPath :=
        ((Prefunctor.mapPath_toPath (chRunMap f).pre _).trans
          (congrArg Quiver.Hom.toPath (pre_map_ascAtom f e))).trans
          (cellCongr_toPath _ _ _).symm
      refine Eq.trans (Prefunctor.mapPath_comp (chRunMap f).pre (climbPath R)
        (Polygraph.cell (P := (chCollapse K).poly) (ascAtom e)).toPath) ?_
      exact (congrArg₂ Quiver.Path.comp ih hletter).trans (cellCongr_comp _ _ _ _ _)

/-! ## The word a 1-cell spells, carried along

The climb a non-`RunCut` 1-cell peels is `Nonempty.some` of a statement about shapes alone, so it is
the *same* climb at `K'` — a `rfl`, and only because the model is strict: routing the cut through
`Classical.choice` on the decomposition would make every leg opaque here. -/

/-- **The chosen word is carried to the chosen word.** -/
theorem pre_mapPath_runCellWord {X Y : (chCollapse K).V} (g : (chCollapse K).Gen X Y) :
    (chRunMap f).pre.mapPath (runCellWord g)
      = runCellWord ((chRunMap f).pre.map (Polygraph.cell (P := (chCollapse K).poly) g)) := by
  by_cases h : RunCut g
  · rw [runCellWord_self g h, runCellWord_self _ ((runCut_chRunMap_iff f g).mpr h)]
    exact Prefunctor.mapPath_toPath (chRunMap f).pre _
  · rw [runCellWord, dif_neg h, runCellWord,
      dif_neg (fun hh => h ((runCut_chRunMap_iff f _).mp hh))]
    refine Eq.trans (Prefunctor.mapPath_cellCongr (chRunMap f).pre _ _ _) ?_
    refine Eq.trans (congrArg (cellCongr Quiver.Path _ _) (pre_mapPath_climbPath f _)) ?_
    exact cellCongr_trans Quiver.Path _ _ _ _ _

/-! ## The atoms, carried along

The kept cuts form a sub-quiver of the collapse's, and the inclusion is faithful on words
(`keptPre_mapPath_injective`), so the square below is `pre_mapPath_runCellWord` read back through
it — the substitution needs no coherence of its own.

    (chCollapse K).poly.Word ──runAtomWords──▸ Paths (GenObj (runAtomPoly K).Gen)
              │ (chRunMap f).pre                        │ runAtomMap f
              ▾                                         ▾
    (chCollapse K').poly.Word ─runAtomWords─▸ Paths (GenObj (runAtomPoly K').Gen)
-/

/-- **The kept cuts, carried along** — the same 0-cells, and a kept cut stays kept. -/
noncomputable def runAtomMap :
    GenObj (runAtomPoly K).Gen ⥤q GenObj (runAtomPoly K').Gen where
  obj x := ⟨((chRunMap f).pre.obj ⟨x.as⟩).as⟩
  map e := ⟨(chRunMap f).pre.map (Polygraph.cell e.1), (runCut_chRunMap_iff f _).mpr e.2⟩

/-- The kept cuts, included in the collapse's 1-cells. -/
noncomputable abbrev atomIncl (K : BPSet) :
    GenObj (runAtomPoly K).Gen ⥤q GenObj (chCollapse K).poly.Gen :=
  keptPre (P := (chCollapse K).poly) RunCut

theorem atomIncl_mapPath_runAtomMap {x y : GenObj (runAtomPoly K).Gen} (w : Quiver.Path x y) :
    (atomIncl K').mapPath ((runAtomMap f).mapPath w)
      = (chRunMap f).pre.mapPath ((atomIncl K).mapPath w) :=
  (Prefunctor.mapPath_comp_apply (runAtomMap f) (atomIncl K') w).symm.trans
    ((eq_of_heq (Prefunctor.mapPath_heq_of_eq
        (show runAtomMap f ⋙q atomIncl K' = atomIncl K ⋙q (chRunMap f).pre from rfl) w)).trans
      (Prefunctor.mapPath_comp_apply (atomIncl K) (chRunMap f).pre w))

/-- **The substitution squares with the map, on a letter.** -/
theorem runAtomMap_mapPath_pre {X Y : GenObj (chCollapse K).poly.Gen} (g : X ⟶ Y) :
    (runAtomMap f).mapPath ((runAtomPre K).map g)
      = (runAtomPre K').map ((chRunMap f).pre.map g) :=
  keptPre_mapPath_injective (P := (chCollapse K').poly) RunCut
    (((atomIncl_mapPath_runAtomMap f _).trans (congrArg (chRunMap f).pre.mapPath
          (keptPre_mapPath_keptWord (P := (chCollapse K).poly) RunCut
            (runCellWord g) (all_runCellWord g)))).trans
      ((pre_mapPath_runCellWord f g).trans
        (keptPre_mapPath_keptWord (P := (chCollapse K').poly) RunCut
          (runCellWord _) (all_runCellWord _)).symm))

end ChainCat
