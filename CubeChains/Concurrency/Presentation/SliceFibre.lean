import CubeChains.Concurrency.Presentation.SliceRunSet
import CubeChains.Concurrency.Presentation.ChartFibre

/-!
# Concurrency/Presentation/SliceFibre — the runs over a chain, as a partial braid action

`SliceRunSet` has the runs over `d` and their down-closure; `Machinery/Braid/WeakAction` turns that
into a partial action of `PosBraid N`, hence a presheaf on the localized base, and a presentation
of the base lifts to it with nothing chosen.

This is `ChartFibre`'s machine at `Y N = RunAt d N`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-- **The braid monoid on `N` strands acts partially on the runs over `d`** — by length-additive
right multiplication of the crossing permutation, defined where the result is still a run. -/
noncomputable def sliceActionAt (d : Ch Zbp) (N : ℕ) :
    PosBraid N →* (strictEnd (RunAt d N))ᵐᵒᵖ :=
  weakActionOn (RunSet d N) (runAtEquiv d N) (weakDown_runSet d N)

/-- **A braid acts on the runs exactly at a germ step** — the `Option` is only the encoding of the
germ's partial product. -/
theorem sliceActionAt_eq_some_iff (β : PosBraid N) (u v : RunAt d N) :
    (sliceActionAt d N β).unop.val (some u) = some v ↔ GermStep β u.perm v.perm :=
  weakActionOn_eq_some_iff_germStep (RunSet d N) (runAtEquiv d N) (weakDown_runSet d N) β u v

/-- **The runs over `d`, as a presheaf on the localized base.** -/
noncomputable def sliceFibre (d : Ch Zbp) : ((W Zbp).op).Localization ⥤ Type :=
  chartFibre (sliceActionAt d)

/-- The undefined run, at every object. -/
noncomputable def sliceBot (d : Ch Zbp) (c : ((W Zbp).op).Localization) : (sliceFibre d).obj c :=
  chartFibreBot (sliceActionAt d) c

theorem sliceBot_absorbing (d : Ch Zbp) {c c' : ((W Zbp).op).Localization} (g : c ⟶ c') :
    (sliceFibre d).map g (sliceBot d c) = sliceBot d c' :=
  chartFibreBot_absorbing (sliceActionAt d) g

/-- The defined runs over `d`, as a category: 0-cells the runs, 1-cells the braids defined on
them. -/
abbrev SliceCharts (d : Ch Zbp) : Type := ChartsAt (sliceActionAt d) (dimSum d.dims)

/-- **The defined part of the presheaf is the defined part of the one live strand count.** -/
noncomputable def sliceChartEquiv (d : Ch Zbp) :
    SliceCharts d ≌ (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategory :=
  chartFibreEquiv (sliceActionAt d) fun _ hN => isEmpty_runAt hN


/-! ## The defined runs are the localized slice, reversed

A braid acts by *raising* the weak order and an arrow of the localized slice *lowers* it, so the
two categories are opposite.  Nothing else separates them: both are thin, the runs are a skeleton
of the slice (`exists_runOver_iso`), and every rise is realised by the simple that names the gap.
-/

/-- The run a defined 0-cell names. -/
noncomputable def chartRun (z : SliceCharts d) : RunAt d (dimSum d.dims) :=
  chartOfDefined (sliceActionAt d) z

/-- …as an object of the slice. -/
noncomputable def chartOver (z : SliceCharts d) : Over d := (chartRun z).1.1

/-- **A defined braid step raises the weak order.** -/
theorem le_of_sliceCharts_hom {z w : SliceCharts d} (f : z ⟶ w) :
    weakOver rfl (chartOver z) ≤ weakOver rfl (chartOver w) :=
  weakChart_le (sliceActionAt d) (runAtEquiv d (dimSum d.dims)) rfl
    (chartAction_hom (sliceActionAt d) f)

instance sliceCharts_isThin (d : Ch Zbp) : Quiver.IsThin (SliceCharts d) :=
  chartsWeak_isThin (sliceActionAt d) (runAtEquiv d (dimSum d.dims)) rfl

/-- **The defined runs over `d` are the localized slice over `d`, reversed.** -/
noncomputable def sliceChartLoc (d : Ch Zbp) :
    (SliceCharts d)ᵒᵖ ⥤ ((W Zbp).over (X := d)).Localization where
  obj z := ((W Zbp).over (X := d)).Q.obj (chartOver z.unop)
  map {z _} f := (nonempty_locOver_hom_of_le rfl (chartRun z.unop).1 (chartRun _).1
    (le_of_sliceCharts_hom f.unop)).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance sliceChartLoc_faithful (d : Ch Zbp) : (sliceChartLoc d).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance sliceChartLoc_full (d : Ch Zbp) : (sliceChartLoc d).Full where
  map_surjective {_ _} h :=
    ⟨Quiver.Hom.op (chartAction_homMk (sliceActionAt d) _
      (weakChart_of_le (sliceActionAt d) (runAtEquiv d (dimSum d.dims)) rfl
        (WeakOrder.le_def.mp (weakOver_le_of_loc_hom rfl h)))),
      Subsingleton.elim _ _⟩

instance sliceChartLoc_essSurj (d : Ch Zbp) : (sliceChartLoc d).EssSurj where
  mem_essImage Y := by
    obtain ⟨y, hy⟩ := Localization.Construction.exists_Q_obj ((W Zbp).over (X := d)) Y
    obtain ⟨a, ⟨i⟩⟩ := exists_runOver_iso (d := d) (N := dimSum d.dims) rfl y
    exact ⟨op ⟨⟨op (SingleObj.star (PosBraid (dimSum d.dims))),
      some ⟨a, RunOver.left_dimSum rfl a⟩⟩, Option.some_ne_none _⟩, ⟨i ≪≫ eqToIso hy⟩⟩

instance sliceChartLoc_isEquivalence (d : Ch Zbp) : (sliceChartLoc d).IsEquivalence := { }

/-- **A defined braid step raises the weak order** — the one fact the transport to the component is
read through, and the only one `ChartFibre`'s descent asks for. -/
theorem runLe_of_action (N : ℕ) (β : PosBraid N) (u v : RunAt d N)
    (h : (sliceActionAt d N β).unop.val (some u) = some v) :
    weakOver rfl u.1.1 ≤ weakOver rfl v.1.1 := by
  obtain rfl := u.strands
  exact weakChart_le (sliceActionAt d) (runAtEquiv d (dimSum d.dims)) rfl h

/-- **The transport fixes the run**: it fixes the weak class, and a run is pinned by its crossing
permutation. -/
theorem runChartFibre_hom_run {N : ℕ} {c : (SingleObj (PosBraid N))ᵒᵖ}
    {u : RunAt d (strandDecomposition.functor.obj ((runBase N).obj c)).1} {v : RunAt d N}
    (h : (runChartFibre (sliceActionAt d) N).hom.app c (some u) = some v) : u.1 = v.1 :=
  RunOver.perm_injective rfl (WeakOrder.of_injective
    (runChartFibre_hom_invariant (π := fun _ u => weakOver rfl u.1.1) (sliceActionAt d)
      runLe_of_action h))


/-! ## The localized slice, read on the whole base

Every cell of the lifted polygraph is indexed by a defined element over the whole base, so that is
where the comparison with the slice must live.  The transport to the component fixes the run, so
the run a defined element names is the same either way. -/

/-- The run a defined element of the presheaf names. -/
noncomputable def definedRun (z : (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategory) :
    RunAt d (strandDecomposition.functor.obj z.obj.1).1 :=
  z.obj.2.get (Option.ne_none_iff_isSome.mp z.property)

@[simp] theorem some_definedRun
    (z : (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategory) :
    some (definedRun z) = z.obj.2 := Option.some_get _

/-- …as an object of the slice. -/
noncomputable def definedOver (z : (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategory) :
    Over d := (definedRun z).1.1

/-- **A defined step over the base raises the weak order.** -/
theorem le_of_defined_hom {z w : (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategory}
    (f : z ⟶ w) : weakOver rfl (definedOver z) ≤ weakOver rfl (definedOver w) :=
  chartLe_of_sigmaDesc (π := fun _ u => weakOver rfl u.1.1) (sliceActionAt d) runLe_of_action
    (strandDecomposition.functor.map f.hom.1) (definedRun z) (definedRun w)
    (by rw [some_definedRun, some_definedRun]; exact f.hom.2)

/-- **The defined runs over the base are the localized slice, reversed** — the same comparison as
on the component, read where the cells are. -/
noncomputable def definedSliceLocFunctor (d : Ch Zbp) :
    (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategoryᵒᵖ ⥤
      ((W Zbp).over (X := d)).Localization where
  obj z := ((W Zbp).over (X := d)).Q.obj (definedOver z.unop)
  map {z _} f := (nonempty_locOver_hom_of_le rfl (definedRun z.unop).1 (definedRun _).1
    (le_of_defined_hom f.unop)).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The transport to the component names the same run.** -/
theorem definedOver_preDefined (z : SliceCharts d) :
    definedOver ((sliceChartEquiv d).functor.obj z) = chartOver z := by
  have hsome : (runChartFibre (sliceActionAt d) (dimSum d.dims)).inv.app z.obj.1 z.obj.2
      = some (definedRun ((sliceChartEquiv d).functor.obj z)) :=
    (some_definedRun ((sliceChartEquiv d).functor.obj z)).symm
  have hhom : (runChartFibre (sliceActionAt d) (dimSum d.dims)).hom.app z.obj.1
      (some (definedRun ((sliceChartEquiv d).functor.obj z))) = some (chartRun z) :=
    ((congrArg ((runChartFibre (sliceActionAt d) (dimSum d.dims)).hom.app z.obj.1) hsome).symm.trans
      (((runChartFibre (sliceActionAt d) (dimSum d.dims)).app z.obj.1).toEquiv.apply_symm_apply
        z.obj.2)).trans (some_chartOfDefined (sliceActionAt d) z).symm
  exact congrArg Subtype.val (runChartFibre_hom_run hhom)

/-- On the component, the comparison is the one already built. -/
theorem sliceChartEquiv_comp_definedSliceLoc (d : Ch Zbp) :
    (sliceChartEquiv d).op.functor ⋙ definedSliceLocFunctor d = sliceChartLoc d :=
  CategoryTheory.Functor.ext (fun z => by
    change ((W Zbp).over (X := d)).Q.obj (definedOver ((sliceChartEquiv d).functor.obj z.unop))
      = ((W Zbp).over (X := d)).Q.obj (chartOver z.unop)
    rw [definedOver_preDefined]) (fun _ _ _ => Subsingleton.elim _ _)

instance definedSliceLocFunctor_isEquivalence (d : Ch Zbp) :
    (definedSliceLocFunctor d).IsEquivalence := by
  haveI : ((sliceChartEquiv d).op.inverse ⋙ (sliceChartEquiv d).op.functor
      ⋙ definedSliceLocFunctor d).IsEquivalence := by
    rw [sliceChartEquiv_comp_definedSliceLoc]
    infer_instance
  exact Functor.isEquivalence_of_iso ((sliceChartEquiv d).op.invFunIdAssoc _)

/-- **The defined part of the run presheaf is the localized slice, reversed.** -/
noncomputable def definedSliceLoc (d : Ch Zbp) :
    (Presents.defined (sliceFibre d) (sliceBot d)).FullSubcategoryᵒᵖ ≌
      ((W Zbp).over (X := d)).Localization :=
  (definedSliceLocFunctor d).asEquivalence

end ChainCat
