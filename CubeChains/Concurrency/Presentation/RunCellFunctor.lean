import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Machinery.Presentation.SpansMap

/-!
# Concurrency/Presentation/RunCellFunctor — the degree-zero polygraph, as a functor of `K`

A map of `K` moves the element a chain carries and no shape, so every choice `chRunCutSpans` makes
is untouched: `RunCut` asks only that a shape be a run (`eltRep_eq_self_iff`), hence is reflected as
well as preserved, and the chosen climb is chosen from shapes alone, hence is the *same* climb.
What is left is the naturality square of the fibre presheaf, which moves `runObj` and the atoms.

    (chRunCutSpans K).poly ───────▸ (chRunCutSpans K').poly
              │ incl                          │ incl
              ▾                               ▾
      chRunFunctor.obj K ─────────▸ chRunFunctor.obj K'
-/

open CategoryTheory BPSet CubeChains

namespace ChainCat

variable {K K' : BPSet} (f : K ⟶ K')

/-! ## The contraction, carried along a map of `K` -/

/-- **A map of `K` carries the contraction along** — it is `eltRunMap` at the wedge presheaf. -/
noncomputable def chRunMap : Contraction.Map (chContraction K) (chContraction K') :=
  eltRunMap (wedgeHomsFunctor.map f)

@[simp] theorem chRunFunctor_map : chRunFunctor.map f = (chRunMap f).poly := rfl

/-- **The shape a 0-cell carries is untouched** — load-bearing: every choice below is made from the
shape, so it is literally the same choice at `K'`. -/
theorem shOf_chRunMap_obj (z : (chCutPoly K).V) : shOf ((chRunMap f).obj z) = shOf z := rfl

theorem eltRestrict_chRunMap {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    eltRestrict ((chRunMap f).obj z) w = (chRunMap f).obj (eltRestrict z w) :=
  eltRestrict_natural (wedgeHomsFunctor.map f) z w

/-! ## The kept cells, carried along

`RunCut` and `RunCutCell` both ask that a 0-cell's shape be a run, and the shape does not move, so
each is reflected as well as preserved. -/

theorem runCut_chRunMap_iff {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    RunCut ((chRunMap f).pre.map (Polygraph.cell (P := (chContraction K).poly) g)) ↔ RunCut g :=
  (eltRep_eq_self_iff _).trans (eltRep_eq_self_iff g.cod).symm

theorem runCutCell_chRunMap {u v : GenObj (chContraction K).poly.Gen}
    {α : (chContraction K).poly.Rel u v} (h : RunCutCell α) :
    RunCutCell ((chRunMap f).poly.two α) :=
  (eltRep_eq_self_iff _).mpr ((eltRep_eq_self_iff α.cod.as).mp h)

/-! ## The run of a chain, and the atoms out of it -/

/-- **The 0-cell a run names moves with the element**, and with nothing else. -/
theorem runObj_chRunMap {N : ℕ} {z : (chCutPoly K).V} (a : RunPerm N z) :
    runObj (K := K') (z := (chRunMap f).obj z) a = (chRunMap f).vtx (runObj a) :=
  Subtype.ext (eltRestrict_chRunMap f a.arr)

/-- A forward letter of the extension is pinned by the base cut it carries. -/
private theorem inl_heq {a b a' b' : (chCutPoly K).V} (ha : a = a') (hb : b = b')
    {e : (chCutPoly K).Gen a b} {e' : (chCutPoly K).Gen a' b'} (h : e.1 ≍ e'.1) :
    (Sum.inl e : Polygraph.InvGen (chCutPoly K) (chCutPicked K) a b)
      ≍ (Sum.inl e' : Polygraph.InvGen (chCutPoly K) (chCutPicked K) a' b') := by
  subst ha; subst hb
  exact heq_of_eq (congrArg Sum.inl (Subtype.ext (eq_of_heq h)))

/-- **The atom an ascent names is the atom its leg names at `K'`** — the leg is a base arrow, so the
two 1-cells carry one cut and differ only in the runs naming their ends. -/
theorem pre_map_ascAtom {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (e : Ascent (runDescents N z).perm a b) :
    (chRunMap f).pre.map (Polygraph.cell (P := (chContraction K).poly) (ascAtom e))
      = Quiver.homOfEq
          (Polygraph.cell (P := (chContraction K').poly)
            (ascAtom (z := (chRunMap f).obj z) e))
          (congrArg GenObj.mk (runObj_chRunMap f a)) (congrArg GenObj.mk (runObj_chRunMap f b)) :=
  Contraction.gen_eq_homOfEq (runObj_chRunMap f a) (runObj_chRunMap f b) _ _
    (eltRestrict_chRunMap f (ascLeg e))
    (eltRestrict_chRunMap f (atomOnes N e.idx ≫ ascLeg e))
    (inl_heq (eltRestrict_chRunMap f (ascLeg e))
      (eltRestrict_chRunMap f (atomOnes N e.idx ≫ ascLeg e)) HEq.rfl)

/-- **…so a climb spells the same climb at `K'`.** -/
theorem pre_mapPath_climbPath {N : ℕ} {z : (chCutPoly K).V} {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) :
    (chRunMap f).pre.mapPath (climbPath R)
      = cellCongr Quiver.Path (congrArg (chContraction K').poly.pt (runObj_chRunMap f a))
          (congrArg (chContraction K').poly.pt (runObj_chRunMap f b))
          (climbPath (K := K') (z := (chRunMap f).obj z) R) := by
  induction R with
  | nil => exact (cellCongr_self Quiver.Path rfl rfl _).symm.trans (cellCongr_nil_eq rfl rfl _ _)
  | @cons bmid v R e ih =>
      have hletter : (chRunMap f).pre.mapPath
            (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath
          = cellCongr Quiver.Path (congrArg (chContraction K').poly.pt (runObj_chRunMap f bmid))
              (congrArg (chContraction K').poly.pt (runObj_chRunMap f v))
              (Polygraph.cell (P := (chContraction K').poly)
                (ascAtom (z := (chRunMap f).obj z) e)).toPath :=
        ((Prefunctor.mapPath_toPath (chRunMap f).pre _).trans
          (congrArg Quiver.Hom.toPath (pre_map_ascAtom f e))).trans
          (cellCongr_toPath _ _ _).symm
      refine Eq.trans (Prefunctor.mapPath_comp (chRunMap f).pre (climbPath R)
        (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath) ?_
      exact (congrArg₂ Quiver.Path.comp ih hletter).trans (cellCongr_comp _ _ _ _ _)

/-! ## The word a 1-cell spells, carried along

The climb a non-`RunCut` 1-cell peels is `Nonempty.some` of a statement about shapes alone, so it is
the *same* climb at `K'` — a `rfl`, and only because the model is strict: routing the cut through
`Classical.choice` on the decomposition would make every leg opaque here. -/

/-- **The chosen word is carried to the chosen word** — `Spans.Map`'s one equation of words. -/
theorem pre_mapPath_runCellWord {X Y : (chContraction K).V} (g : (chContraction K).Gen X Y) :
    (chRunMap f).pre.mapPath (runCellWord g)
      = runCellWord ((chRunMap f).pre.map (Polygraph.cell (P := (chContraction K).poly) g)) := by
  by_cases h : RunCut g
  · rw [runCellWord_self g h, runCellWord_self _ ((runCut_chRunMap_iff f g).mpr h)]
    exact Prefunctor.mapPath_toPath (chRunMap f).pre _
  · obtain ⟨d, c, gen, hnm, hd, hc⟩ := g
    rcases gen with e | ⟨e, he⟩
    · rw [runCellWord, dif_neg h, runCellWord,
        dif_neg (fun hh => h ((runCut_chRunMap_iff f _).mp hh))]
      refine Eq.trans (Prefunctor.mapPath_cellCongr (chRunMap f).pre _ _ _) ?_
      refine Eq.trans (congrArg (cellCongr Quiver.Path _ _) (pre_mapPath_climbPath f _)) ?_
      exact cellCongr_trans Quiver.Path _ _ _ _ _
    · exact absurd trivial hnm

/-! ## The functor -/

/-- **A map of `K` carries the degree-zero span along.** -/
noncomputable def chCellSpansMap : Spans.Map (chRunCutSpans K) (chRunCutSpans K') where
  hom := (chRunMap f).poly
  mem_one h := (runCut_chRunMap_iff f _).mpr h
  mem_two h := runCutCell_chRunMap f h
  word_hom g := pre_mapPath_runCellWord f g

@[simp] theorem chCellSpansMap_hom : (chCellSpansMap f).hom = chRunFunctor.map f := rfl

/-- **The atoms out of the runs with the degree-zero cells, as a functor of `K`** — for every `K`
and with no hypothesis on `K`. -/
noncomputable def chCellFunctor : BPSet ⥤ Polygraph :=
  Spans.Map.polyFunctor chRunFunctor (fun _ => RunCut) (fun _ => RunCutCell) chRunCutSpans
    (fun f => chCellSpansMap f) fun _ => rfl

@[simp] theorem chCellFunctor_obj (K : BPSet) : chCellFunctor.obj K = (chRunCutSpans K).poly := rfl

@[simp] theorem chCellFunctor_map : chCellFunctor.map f = (chCellSpansMap f).poly := rfl

/-! ## …and the presentation along it

`chCellPresentation` is the inclusion of the kept cells followed by `chRunPresentation`, so the
square for it is the square for `chRunPresentation` conjugated by a commuting triangle. -/

/-- **`chCellFunctor` lies over `chRunFunctor`** — on the nose, no coherence. -/
theorem chCellFunctor_incl :
    (chCellFunctor.map f).functor ⋙ (chRunCutSpans K').incl.functor
      = (chRunCutSpans K).incl.functor ⋙ (chRunFunctor.map f).functor :=
  Spans.Map.incl_functor_naturality (chCellSpansMap f)

end ChainCat
