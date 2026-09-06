import CubeChains.Concurrency.Presentation.SliceFibre
import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/SliceInherit — the slice family, inherited from the base

The slice polygraph over `d` is the base's, lifted along the runs over `d`
(`Presents.partialElements`): 0-cells the runs, 1-cells the base's generators *where they act*,
2-cells its relations there.  So the family is parametric in the presentation of the base, and its
1- and 2-cells move when that presentation does.

`RunAt.push` is strictly functorial — postcomposition leaves a run's source untouched — and only
**laxly** natural: a step undefined over `d'` can be defined over `d`, which is exactly what
`Presents.partialElementsMap` consumes.  The `ᵒᵖ` is the orientation: a braid *raises* the weak
order where an arrow of the localized slice lowers it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d' d : Ch Zbp} {N : ℕ}

/-! ## Pushing a run forward -/

/-- Postcomposition on the runs; it does not touch the source, so the strand count survives on the
nose. -/
def RunAt.push (f : d' ⟶ d) (u : RunAt d' N) : RunAt d N := ⟨RunOver.push f u.1, u.2⟩

theorem RunAt.push_perm (f : d' ⟶ d) (hd : dimSum d'.dims = N) (u : RunAt d' N) :
    (RunAt.push f u).perm = crossPerm hd f * u.perm := crossPerm_comp _ u.1.1.hom f

theorem RunAt.push_permLen (f : d' ⟶ d) (hd : dimSum d'.dims = N) (u : RunAt d' N) :
    permLen (RunAt.push f u).perm = permLen u.perm + permLen (crossPerm hd f) :=
  permLen_crossPerm_comp _ u.1.1.hom f

/-- **A defined step survives postcomposition** — the crossings a run makes downstream are new
there, so length-additivity is untouched. -/
theorem sliceActionAt_push (f : d' ⟶ d) {β : PosBraid N} {u v : RunAt d' N}
    (h : (sliceActionAt d' N β).unop.val (some u) = some v) :
    (sliceActionAt d N β).unop.val (some (RunAt.push f u)) = some (RunAt.push f v) := by
  obtain ⟨hperm, hlen⟩ := (sliceActionAt_eq_some_iff β u v).mp h
  refine (sliceActionAt_eq_some_iff β _ _).mpr ⟨?_, ?_⟩
  · rw [RunAt.push_perm f u.strands, RunAt.push_perm f u.strands, hperm, mul_assoc]
  · rw [RunAt.push_permLen f u.strands, RunAt.push_permLen f u.strands]
    omega

/-- **The runs push forward laxly**: defined where they were, and commuting with the action there.
-/
theorem partialFam_push (f : d' ⟶ d) :
    Presents.PartialFam (sliceFibre d') (sliceFibre d) (sliceBot d') (sliceBot d)
      (chartFam (sliceActionAt d') (sliceActionAt d) fun _ => RunAt.push f) where
  ne_bot := chartFam_ne_bot (sliceActionAt d') (sliceActionAt d) _
  lax g x hx hgx := chartFam_lax (sliceActionAt d') (sliceActionAt d) _
    (fun _ _ _ _ h => sliceActionAt_push f h) g x hx hgx

/-! ## The family -/

variable {P : Polygraph.{0, 0, 0}}

/-- **The slice polygraph over `d`, inherited from the base** — the base's cells where they act on
the runs over `d`. -/
noncomputable def slicePolyRaw (p : Presents P (((W Zbp).op).Localization)) (d : Ch Zbp) :
    Polygraph :=
  (p.elements (sliceFibre d)).restrictPoly (Presents.defined (sliceFibre d) (sliceBot d))

/-- **…functorially in `d`.**  `Over.map` is strictly functorial on `Ch Zbp` and a 1-cell keeps the
base generator it names, so both laws are the identity family's. -/
noncomputable def slicePolyRawFunctor (p : Presents P (((W Zbp).op).Localization)) :
    Ch Zbp ⥤ Polygraph where
  obj d := slicePolyRaw p d
  map f := Presents.partialElementsMap p _ (partialFam_push f)
  map_id d :=
    (Presents.partialElementsMap_congr p (partialFam_push (𝟙 d))
        (Presents.PartialFam.id (sliceFibre d) (sliceBot d))
        (funext fun _ => funext fun x => by cases x <;> rfl)).trans
      (Presents.partialElementsMap_id p (sliceFibre d) (sliceBot d))
  map_comp f g :=
    (Presents.partialElementsMap_congr p (partialFam_push (f ≫ g))
        ((partialFam_push f).comp (partialFam_push g))
        (funext fun _ => funext fun x => by cases x <;> rfl)).trans
      (Presents.partialElementsMap_comp p (partialFam_push f) (partialFam_push g))

/-- **The slice family**, in the orientation the glue route consumes. -/
noncomputable def slicePolyFunctor (p : Presents P (((W Zbp).op).Localization)) :
    Ch Zbp ⥤ Polygraph :=
  slicePolyRawFunctor p ⋙ Polygraph.opFunctor

/-! ## What it presents -/

/-- The run a 0-cell names. -/
noncomputable def sliceCellRun {p : Presents P (((W Zbp).op).Localization)} {d : Ch Zbp}
    (a : (slicePolyRaw p d).V) :
    RunAt d (strandDecomposition.functor.obj (p.at' (P.pt a.1.1))).1 :=
  a.1.2.get (Option.ne_none_iff_isSome.mp a.2)

/-- …as an object of the slice. -/
noncomputable def sliceCellOver {p : Presents P (((W Zbp).op).Localization)} {d : Ch Zbp}
    (a : (slicePolyRaw p d).V) : Over d := (sliceCellRun a).1.1

/-- **The localized slice over `d`, presented by the base's cells.**  `p` is arbitrary: the runs
carry a partial action of the braid monoid, and nothing about the presentation entered its
construction. -/
noncomputable def slicePresentationOf (p : Presents P (((W Zbp).op).Localization)) (d : Ch Zbp) :
    Presents ((slicePolyFunctor p).obj d) (((W Zbp).over (X := d)).Localization) :=
  (((Presents.partialElements (sliceFibre d) (sliceBot d)
    (fun g => sliceBot_absorbing d g) p).transport (definedSliceLoc d)).op).transport
      (opOpEquivalence _)

/-- **The 0-cells name their own slice objects** — no transport is left. -/
theorem slicePresentationOf_at (p : Presents P (((W Zbp).op).Localization)) (d : Ch Zbp)
    (a : (slicePolyRaw p d).V) :
    (slicePresentationOf p d).at' ⟨a⟩ = ((W Zbp).over (X := d)).Q.obj (sliceCellOver a) := rfl


/-- **Pushing a 0-cell pushes its run.** -/
theorem sliceCellRun_push {p : Presents P (((W Zbp).op).Localization)} (f : d' ⟶ d)
    (a : (slicePolyRaw p d').V) :
    sliceCellRun (Presents.famV p _ (partialFam_push f) a) = RunAt.push f (sliceCellRun a) := by
  have h1 : some (sliceCellRun (Presents.famV p _ (partialFam_push f) a))
      = (Presents.famV p _ (partialFam_push f) a).1.2 := Option.some_get _
  have h2 : some (sliceCellRun a) = a.1.2 := Option.some_get _
  refine Option.some_inj.mp (h1.trans ?_)
  change chartFam (sliceActionAt d') (sliceActionAt d) (fun _ => RunAt.push f) _ a.1.2
    = some (RunAt.push f (sliceCellRun a))
  rw [← h2]
  rfl

theorem sliceCellOver_push {p : Presents P (((W Zbp).op).Localization)} (f : d' ⟶ d)
    (a : (slicePolyRaw p d').V) :
    sliceCellOver (Presents.famV p _ (partialFam_push f) a) = (Over.map f).obj (sliceCellOver a) :=
  congrArg (fun u : RunAt d _ => u.1.1) (sliceCellRun_push f a)

/-- **The slice presentations are compatible with the base** — on objects the 0-cells name their
own slice objects and pushing them is `Over.map`; on morphisms the slice is a poset. -/
theorem slicePoly_hP (p : Presents P (((W Zbp).op).Localization)) (f : d' ⟶ d) :
    ((slicePolyFunctor p).map f).functor ⋙ (slicePresentationOf p d).E
      = (slicePresentationOf p d').E ⋙ overMapLoc (W Zbp) f := by
  fapply CategoryTheory.Functor.ext
  · rintro ⟨⟨a⟩⟩
    change (slicePresentationOf p d).at' ⟨Presents.famV p _ (partialFam_push f) a⟩
      = (overMapLoc (W Zbp) f).obj ((slicePresentationOf p d').at' ⟨a⟩)
    rw [slicePresentationOf_at, slicePresentationOf_at, sliceCellOver_push]
    exact (overMapLoc_obj (W Zbp) f _).symm
  · intro _ _ _
    exact Subsingleton.elim _ _


/-! ## The runs are a skeleton

The 0-cells are the runs over `d` — one per base 0-cell carrying a defined chart — so they meet
each isomorphism class of the localized slice exactly once, provided the base's own 0-cells are
separated by their strand count. -/

/-- **The base presentation names one 0-cell per strand count.**  Not automatic: a presentation is
only an equivalence, so it may name a component several times, and then the runs are counted with
multiplicity. -/
def StrandSeparated (p : Presents P (((W Zbp).op).Localization)) : Prop :=
  ∀ (x y : P.V) (M : ℕ), AtStrands M (p.at' (P.pt x)) → AtStrands M (p.at' (P.pt y)) → x = y

/-- **A 0-cell of the slice polygraph sits at `d`'s strand count** — nothing else carries a run
over `d`. -/
theorem atStrands_of_sliceCell {p : Presents P (((W Zbp).op).Localization)} {d : Ch Zbp}
    (a : (slicePolyRaw p d).V) : AtStrands (dimSum d.dims) (p.at' (P.pt a.1.1)) := by
  obtain ⟨D, ⟨e⟩⟩ := chartFibre_cover_of_defined (sliceActionAt d)
    (fun _ hN => isEmpty_runAt hN) (p.at' (P.pt a.1.1)) a.1.2 a.2
  exact (ObjectProperty.prop_iff_of_hom AtStrands exists_atStrands
    (fun hX hY g => atStrands_eq_of_hom hX hY g) e.hom).mp (atStrands_run _)

/-- **Distinct 0-cells name distinct slice objects.** -/
theorem sliceCell_eq_of_iso {p : Presents P (((W Zbp).op).Localization)} (hp : StrandSeparated p)
    {d : Ch Zbp} {a b : (slicePolyRaw p d).V}
    (e : ((W Zbp).over (X := d)).Q.obj (sliceCellOver a)
      ≅ ((W Zbp).over (X := d)).Q.obj (sliceCellOver b)) : a = b := by
  have hx : a.1.1 = b.1.1 :=
    hp _ _ (dimSum d.dims) (atStrands_of_sliceCell a) (atStrands_of_sliceCell b)
  obtain ⟨⟨x, ch⟩, hch⟩ := a
  obtain ⟨⟨x', ch'⟩, hch'⟩ := b
  obtain rfl : x = x' := hx
  have hrun : (sliceCellRun (⟨⟨x, ch⟩, hch⟩ : (slicePolyRaw p d).V)).1
      = (sliceCellRun (⟨⟨x, ch'⟩, hch'⟩ : (slicePolyRaw p d).V)).1 :=
    RunOver.eq_of_locIso (d := d) (N := dimSum d.dims) rfl e
  have e1 : some (sliceCellRun (⟨⟨x, ch⟩, hch⟩ : (slicePolyRaw p d).V)) = ch := Option.some_get _
  have e2 : some (sliceCellRun (⟨⟨x, ch'⟩, hch'⟩ : (slicePolyRaw p d).V)) = ch' := Option.some_get _
  exact Subtype.ext (congrArg (Sigma.mk x)
    (e1.symm.trans ((congrArg some (Subtype.ext hrun)).trans e2)))

/-- **The runs are a skeleton of each localized slice.** -/
noncomputable def sliceSkeleton (p : Presents P (((W Zbp).op).Localization))
    (hp : StrandSeparated p) :
    SliceSkeleton (P := slicePolyFunctor p) (W Zbp) (slicePresentationOf p) where
  entry {d} y := by
    obtain ⟨⟨w⟩, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := (slicePresentationOf p d).E)
      (((W Zbp).over (X := d)).Q.obj y)
    refine ⟨w.as, ⟨i⟩, fun b hb => ?_⟩
    obtain ⟨j⟩ := hb
    refine sliceCell_eq_of_iso hp ?_
    rw [← slicePresentationOf_at, ← slicePresentationOf_at]
    exact j ≪≫ i.symm

/-- **`Ch(K)[W⁻¹]` is presented by the colimit of the inherited slices, for every `K`** — 0-cells
the runs over a chain, 1-cells the base's generators acting on them, 2-cells the base's relations.
-/
noncomputable def presentsChainsSliceColimit (K : BPSet)
    (p : Presents P (((W Zbp).op).Localization)) (hp : StrandSeparated p) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) (slicePolyFunctor p)))
      ((W K).Localization) :=
  presentsChainsColimit K (slicePresentationOf p) (fun {_ _} f => slicePoly_hP p f)
    (sliceSkeleton p hp)


/-! ## The cells at a run

A `BraidPresentation` names the run at each strand count (`base_at'`) and its generators are the
loops there (`base_arrow`), so a run over `d` names a 0-cell outright and a generator acting on it
names a 1-cell.  Nothing evaluates the strand decomposition: `runChartFibre`'s naturality carries
every step. -/

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **The 0-cell of the slice polygraph a run names.** -/
noncomputable def runPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) : (slicePolyRaw p.base d).V :=
  ⟨⟨⟨N, p.v N⟩, runChart (sliceActionAt d) N u⟩, runChart_ne_bot (sliceActionAt d) N u⟩

/-- **…and it names that run.** -/
theorem sliceCellRun_runPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) :
    (sliceCellRun (p.runPt u)).1 = u.1 :=
  runChartFibre_hom_run
    ((congrArg ((runChartFibre (sliceActionAt d) N).hom.app
        (op (SingleObj.star (PosBraid N)))) (Option.some_get _)).trans
      (runChartFibre_hom_runChart (sliceActionAt d) N u))

theorem sliceCellOver_runPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) :
    sliceCellOver (p.runPt u) = u.1.1 :=
  congrArg (fun w : RunOver d => w.1) (p.sliceCellRun_runPt u)

/-- **Every 0-cell of the slice polygraph is a run's.** -/
theorem exists_runPt {d : Ch Zbp} (a : (slicePolyRaw p.base d).V) :
    ∃ (N : ℕ) (u : RunAt d N), a = p.runPt u := by
  obtain ⟨⟨⟨M, x⟩, t⟩, ht⟩ := a
  obtain rfl : x = p.v M := p.eq_v x
  obtain ⟨u, hu⟩ : ∃ u, (runChartFibre (sliceActionAt d) M).hom.app
      (op (SingleObj.star (PosBraid M))) t = some u :=
    Option.ne_none_iff_exists'.mp fun h => ht
      (((runChartFibre (sliceActionAt d) M).app _).toEquiv.injective
        (h.trans (runChartFibre_hom_none (sliceActionAt d) M _).symm))
  obtain rfl : t = runChart (sliceActionAt d) M u := eq_runChart (sliceActionAt d) M hu
  exact ⟨M, u, rfl⟩

/-- **The 1-cell a generator acting on a run names.** -/
noncomputable def runGen {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (s : p.S N)
    (h : (sliceActionAt d N (p.braid s)).unop.val (some u) = some v) :
    (⟨p.runPt u⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨p.runPt v⟩ :=
  ⟨p.gen s,
    (congrArg (fun φ => (sliceFibre d).map φ (runChart (sliceActionAt d) N u))
        (p.base_arrow s)).trans
      (chartFibre_map_runChart (sliceActionAt d) N (p.braid s) h)⟩

/-- **Every 1-cell is a generator acting on a run**, and its two 0-cells are the two ends of that
step.  The generator is carried as a `HEq` because the two 0-cells are still unidentified;
substituting them makes both sides sit at the run and the `HEq` an `Eq`. -/
theorem gen_action {d : Ch Zbp} {a b : (slicePolyRaw p.base d).V}
    (g : (⟨a⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨b⟩) :
    ∃ (N : ℕ) (s : p.S N) (u v : RunAt d N), a = p.runPt u ∧ b = p.runPt v ∧
      (sliceActionAt d N (p.braid s)).unop.val (some u) = some v ∧ HEq g.1 (p.gen s) := by
  obtain ⟨⟨⟨M, x⟩, ta⟩, ha⟩ := a
  obtain ⟨⟨⟨M', y⟩, tb⟩, hb⟩ := b
  obtain rfl : x = p.v M := p.eq_v x
  obtain rfl : y = p.v M' := p.eq_v y
  obtain ⟨ε, hε⟩ := g
  cases ε with
  | @mk _ _ _ s =>
    have hg : (sliceFibre d).map ((runBase M).map (posArrow M (p.braid s))) ta = tb :=
      (congrArg (fun φ => (sliceFibre d).map φ ta) (p.base_arrow s)).symm.trans hε
    have hact := action_of_chartFibre_map (sliceActionAt d) M (p.braid s) hg
    obtain ⟨u, hu⟩ : ∃ u, (runChartFibre (sliceActionAt d) M).hom.app
        (op (SingleObj.star (PosBraid M))) ta = some u :=
      Option.ne_none_iff_exists'.mp fun h => ha
        (((runChartFibre (sliceActionAt d) M).app _).toEquiv.injective
          (h.trans (runChartFibre_hom_none (sliceActionAt d) M _).symm))
    obtain ⟨v, hv⟩ : ∃ v, (runChartFibre (sliceActionAt d) M).hom.app
        (op (SingleObj.star (PosBraid M))) tb = some v :=
      Option.ne_none_iff_exists'.mp fun h => hb
        (((runChartFibre (sliceActionAt d) M).app _).toEquiv.injective
          (h.trans (runChartFibre_hom_none (sliceActionAt d) M _).symm))
    have hstep := (congrArg (sliceActionAt d M (p.braid s)).unop.val hu).symm.trans
      (hact.trans hv)
    obtain rfl : ta = runChart (sliceActionAt d) M u := eq_runChart (sliceActionAt d) M hu
    obtain rfl : tb = runChart (sliceActionAt d) M v := eq_runChart (sliceActionAt d) M hv
    exact ⟨M, s, u, v, rfl, rfl, hstep, HEq.rfl⟩

/-- …at a known strand count. -/
theorem gen_action_of_strands {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N)
    {a b : (slicePolyRaw p.base d).V}
    (g : (⟨a⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨b⟩) :
    ∃ (s : p.S N) (u v : RunAt d N), a = p.runPt u ∧ b = p.runPt v ∧
      (sliceActionAt d N (p.braid s)).unop.val (some u) = some v ∧ HEq g.1 (p.gen s) := by
  obtain ⟨M, s, u, v, ha, hb, hstep, hval⟩ := p.gen_action g
  obtain rfl : M = N := u.strands.symm.trans hd
  exact ⟨s, u, v, ha, hb, hstep, hval⟩

/-- **Every 0-cell is a run's, at a known strand count.** -/
theorem exists_runPt_of_strands {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N)
    (a : (slicePolyRaw p.base d).V) : ∃ u : RunAt d N, a = p.runPt u := by
  obtain ⟨M, u, ha⟩ := p.exists_runPt a
  obtain rfl : M = N := u.strands.symm.trans hd
  exact ⟨u, ha⟩

/-- **The 0-cells of the slice polygraph *are* the runs over the chain.**  `vertex` is what makes
it an equivalence and not a surjection: a second 0-cell at a strand count would name every run
twice. -/
noncomputable def runPtEquiv (d : Ch Zbp) :
    RunAt d (dimSum d.dims) ≃ (slicePolyRaw p.base d).V :=
  Equiv.ofBijective p.runPt
    ⟨fun u v h => Subtype.ext (Subtype.ext ((p.sliceCellOver_runPt u).symm.trans
        ((congrArg sliceCellOver h).trans (p.sliceCellOver_runPt v)))),
      fun a => (p.exists_runPt_of_strands rfl a).imp fun _ hu => hu.symm⟩

@[simp] theorem runPtEquiv_apply {d : Ch Zbp} (u : RunAt d (dimSum d.dims)) :
    p.runPtEquiv d u = p.runPt u := rfl

/-- **A braid presentation names one 0-cell per strand count** — one component, one 0-cell. -/
theorem strandSeparated : StrandSeparated p.base := by
  rintro ⟨M, x⟩ ⟨M', y⟩ L hx hy
  have h1 : M = L := atStrands_eq_of_hom (atStrands_run M) hx (𝟙 _)
  have h2 : M' = L := atStrands_eq_of_hom (atStrands_run M') hy (𝟙 _)
  obtain rfl : M = M' := h1.trans h2.symm
  exact congrArg (Sigma.mk M) ((p.eq_v x).trans (p.eq_v y).symm)

/-- **A 0-cell is its run's** — separation pins it. -/
theorem eq_runPt {d : Ch Zbp} {N : ℕ} {a : (slicePolyRaw p.base d).V} {u : RunAt d N}
    (h : sliceCellOver a = u.1.1) : a = p.runPt u :=
  sliceCell_eq_of_iso p.strandSeparated
    (eqToIso (congrArg ((W Zbp).over (X := d)).Q.obj
      (h.trans (p.sliceCellOver_runPt u).symm)))

/-- **Pushing a run's 0-cell pushes the run.** -/
theorem famV_runPt {d' d : Ch Zbp} (f : d' ⟶ d) {N : ℕ} (u : RunAt d' N) :
    Presents.famV p.base _ (partialFam_push f) (p.runPt u) = p.runPt (RunAt.push f u) :=
  p.eq_runPt
    ((sliceCellOver_push f (p.runPt u)).trans
      (congrArg (Over.map f).obj (p.sliceCellOver_runPt u)))

/-- The slice family `p` inherits. -/
noncomputable def fam : Ch Zbp ⥤ Polygraph.{0, 0, 0} := slicePolyFunctor p.base

/-- **The polygraph a braid presentation induces on `Ch(K)[W⁻¹]`** — one copy of `p`'s cells per
run of a chain of `K`, glued over the elements. -/
noncomputable def Br (K : BPSet) : Polygraph.{0, 0, 0} :=
  Limits.colimit (elementsPoly (wedgeHoms K) p.fam)

/-- **…and it presents `Ch(K)[W⁻¹]`**, with no side hypothesis: the braid monoids are the base's
hom-sets, so a presentation of them names one 0-cell per strand count and the runs are a
skeleton. -/
noncomputable def presentsBr (K : BPSet) : Presents (p.Br K) ((W K).Localization) :=
  presentsChainsSliceColimit K p.base p.strandSeparated

end BraidPresentation

/-- **`Ch(K)[W⁻¹]` presented by the colimit of the germ-inherited slices**, for every `K`. -/
noncomputable def presentsChainsGarsideColimit (K : BPSet) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) (slicePolyFunctor germBP.base)))
      ((W K).Localization) :=
  germBP.presentsBr K

/-- **…and by the Artin-inherited ones** — the same lemma at a different base presentation, and
the 1- and 2-cells of the colimit move with it. -/
noncomputable def presentsChainsArtinColimit (K : BPSet) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) (slicePolyFunctor artinBP.base)))
      ((W K).Localization) :=
  artinBP.presentsBr K

/-! ### What a generator does to a run

A generator acts by *length-additive* right multiplication of the crossing permutation, so the step
it makes is read off its own braid: a germ generator is a simple (`germBP_braid`) and crosses it, an
Artin generator is an atom (`artinBP_braid`) and crosses one pair. -/

/-- **A simple is crossed above a run exactly when the lengths add.** -/
theorem sliceActionAt_posPerm_iff {d : Ch Zbp} {N : ℕ} (σ : Perm (Fin N)) (u v : RunAt d N) :
    (sliceActionAt d N (posPerm σ)).unop.val (some u) = some v ↔
      v.perm = u.perm * σ ∧ permLen u.perm + permLen σ = permLen v.perm := by
  rw [sliceActionAt_eq_some_iff, posPermHom_posPerm, posLen_posPerm, toAdd_ofAdd]

/-- …and an atom is crossed by one pair — codimension one, on the nose. -/
theorem sliceActionAt_adjT_iff {d : Ch Zbp} {N : ℕ} (k : Fin (N - 1)) (u v : RunAt d N) :
    (sliceActionAt d N (posPerm (adjT k))).unop.val (some u) = some v ↔
      v.perm = u.perm * adjT k ∧ permLen u.perm + 1 = permLen v.perm := by
  rw [sliceActionAt_posPerm_iff, permLen_adjT]

end ChainCat
