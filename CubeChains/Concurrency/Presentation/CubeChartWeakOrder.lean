import CubeChains.Concurrency.Presentation.CubeChartAction
import CubeChains.Concurrency.Merge.CubeWeakEquiv

/-!
# Concurrency/Presentation/CubeChartWeakOrder — the lifted charts are the weak order

The category `cubeChartPresentation` presents is the *weak order* on `Sₙ`, hence `Ch(□n)[W⁻¹]ᵒᵖ`.
A chart over the run is its crossing permutation (`crossOnesEquiv`), a braid is defined at it
exactly where it adds all its own crossings (`chartActionAt_eq_some_iff`), and that is the right
weak Bruhat order.

The decomposition of the base is never computed on objects: `preDefined` transports the defined
part along `runBase n`, and `runCubeFibre` names the restricted fibre.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-! ## The charts over the run, as a category -/

/-- The undefined chart, at the single object of the strand-`n` component. -/
noncomputable def chartBot (n : ℕ) (c : (SingleObj (PosBraid n))ᵒᵖ) :
    (partialActionFunctor (chartActionAt n n)).obj c := none

/-- The defined charts of `□n` over the run of `n` events. -/
abbrev ChartCat (n : ℕ) : Type :=
  (Presents.defined (partialActionFunctor (chartActionAt n n)) (chartBot n)).FullSubcategory

/-- The chart an object of `ChartCat` names. -/
noncomputable def chartOf (z : ChartCat n) : RunChart (□n) n :=
  z.obj.2.get (Option.ne_none_iff_isSome.mp z.property)

@[simp] theorem some_chartOf (z : ChartCat n) : some (chartOf z) = z.obj.2 := Option.some_get _

/-- A morphism of `ChartCat` is a defined braid step. -/
theorem chartActionAt_hom {z w : ChartCat n} (f : z ⟶ w) :
    (chartActionAt n n f.hom.1.unop).unop.val (some (chartOf z)) = some (chartOf w) := by
  rw [some_chartOf, some_chartOf]
  exact f.hom.2

/-! ## A defined braid is a simple -/

/-- **A braid defined at a chart is reduced there**, hence a simple, and it multiplies the
crossing permutation by its own. -/
theorem eq_posPerm_of_chartActionAt {β : PosBraid n} {x y : RunChart (□n) n}
    (h : (chartActionAt n n β).unop.val (some x) = some y) :
    β = posPerm (posPermHom n β) ∧ crossOnes y = crossOnes x * posPermHom n β ∧
      permLen (crossOnes x) + permLen (posPermHom n β) = permLen (crossOnes y) := by
  obtain ⟨hy, hly⟩ := (chartActionAt_eq_some_iff β x y).mp h
  have h1 := permLen_mul_le (crossOnes x) (posPermHom n β)
  have h2 := permLen_posPermHom_le β
  rw [← hy] at h1
  exact ⟨eq_posPerm_of_posLen (by omega), hy, by omega⟩

/-- A defined braid rises in the weak order. -/
theorem le_of_chartActionAt {β : PosBraid n} {x y : RunChart (□n) n}
    (h : (chartActionAt n n β).unop.val (some x) = some y) :
    WeakOrder.of (crossOnes x) ≤ WeakOrder.of (crossOnes y) := by
  obtain ⟨-, hy, hly⟩ := eq_posPerm_of_chartActionAt h
  rw [hy] at hly ⊢
  exact WeakOrder.le_of_mul hly

/-- …and every rise is realised, by the simple that names the gap. -/
theorem chartActionAt_of_le {x y : RunChart (□n) n}
    (h : WeakOrder.of (crossOnes x) ≤ WeakOrder.of (crossOnes y)) :
    (chartActionAt n n (posPerm ((crossOnes x)⁻¹ * crossOnes y))).unop.val (some x) = some y :=
  (chartActionAt_posPerm_eq_some_iff _ x y).mpr
    ⟨(mul_inv_cancel_left (crossOnes x) (crossOnes y)).symm, WeakOrder.le_def.mp h⟩

/-- **The acting braid is pinned by the two charts.** -/
theorem chartActionAt_injective {β γ : PosBraid n} {x y : RunChart (□n) n}
    (hβ : (chartActionAt n n β).unop.val (some x) = some y)
    (hγ : (chartActionAt n n γ).unop.val (some x) = some y) : β = γ := by
  obtain ⟨hsβ, hyβ, -⟩ := eq_posPerm_of_chartActionAt hβ
  obtain ⟨hsγ, hyγ, -⟩ := eq_posPerm_of_chartActionAt hγ
  rw [hsβ, hsγ, mul_left_cancel (hyβ.symm.trans hyγ)]

/-! ## The charts over the run are the weak order -/

instance chartCat_isThin (n : ℕ) : Quiver.IsThin (ChartCat n) := fun _ _ =>
  ⟨fun f g => ObjectProperty.hom_ext _ (Subtype.ext (Quiver.Hom.unop_inj
    (chartActionAt_injective (chartActionAt_hom f) (chartActionAt_hom g))))⟩

/-- **The defined charts of `□n` over the run are the right weak order on `Sₙ`.** -/
noncomputable def chartWeak (n : ℕ) : ChartCat n ⥤ WeakOrder n where
  obj z := WeakOrder.of (crossOnes (chartOf z))
  map f := homOfLE (le_of_chartActionAt (chartActionAt_hom f))
  map_id _ := rfl
  map_comp _ _ := rfl

instance chartWeak_faithful (n : ℕ) : (chartWeak n).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance chartWeak_full (n : ℕ) : (chartWeak n).Full where
  map_surjective {z w} h := by
    refine ⟨ObjectProperty.homMk ⟨Quiver.Hom.op (show w.obj.1.unop ⟶ z.obj.1.unop from
        posPerm ((crossOnes (chartOf z))⁻¹ * crossOnes (chartOf w))), ?_⟩,
      Subsingleton.elim _ _⟩
    change (chartActionAt n n _).unop.val z.obj.2 = w.obj.2
    rw [← some_chartOf z, ← some_chartOf w]
    exact chartActionAt_of_le (leOfHom h)

instance chartWeak_essSurj (n : ℕ) : (chartWeak n).EssSurj where
  mem_essImage σ := by
    refine ⟨⟨⟨op (SingleObj.star (PosBraid n)),
      some ((crossOnesEquiv n).symm (WeakOrder.perm σ))⟩, Option.some_ne_none _⟩, ⟨eqToIso ?_⟩⟩
    change WeakOrder.of (crossOnes ((crossOnesEquiv n).symm (WeakOrder.perm σ))) = σ
    rw [crossOnes_symm, WeakOrder.of_perm]

instance chartWeak_isEquivalence (n : ℕ) : (chartWeak n).IsEquivalence := { }

/-- **The lifted charts over the run are the weak order.** -/
noncomputable def chartWeakEquiv (n : ℕ) : ChartCat n ≌ WeakOrder n :=
  (chartWeak n).asEquivalence

/-! ## Restricting the fibre to the run

`strandDecomposition.functor` is a `Functor.inv`, opaque on objects; nothing below evaluates it.
Restricting along `runBase N` undoes the decomposition by the counit, and what is left is the
partial action at that strand count. -/

/-- The strand-`N` component, included into the disjoint union. -/
noncomputable def runSigma (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ⥤ Σ M : ℕ, (AtStrands M).FullSubcategory :=
  runBaseAt N ⋙ Sigma.incl (C := fun M : ℕ => (AtStrands M).FullSubcategory) N

theorem runSigma_comp_inverse (N : ℕ) :
    runSigma N ⋙ strandDecomposition.inverse = runBase N := rfl

/-- Restricting the decomposition along the run of `N` events undoes it. -/
noncomputable def runStrandIso (N : ℕ) :
    runBase N ⋙ strandDecomposition.functor ≅ runSigma N :=
  Functor.isoWhiskerLeft (runSigma N) strandDecomposition.counitIso ≪≫ (runSigma N).rightUnitor

/-- **The cube's charts over the run of `N` events**: the strand-`N` fibre of `cubeFibre n` is the
partial action at that strand count. -/
noncomputable def runCubeFibre (n N : ℕ) :
    runBase N ⋙ cubeFibre n ≅ partialActionFunctor (chartActionAt n N) :=
  Functor.isoWhiskerRight (runStrandIso N)
      (Sigma.desc fun M => (strandComponentGarside M).inverse
        ⋙ partialActionFunctor (chartActionAt n M)) ≪≫
    Functor.isoWhiskerRight (strandComponentGarside N).unitIso.symm
      (partialActionFunctor (chartActionAt n N)) ≪≫
    (partialActionFunctor (chartActionAt n N)).leftUnitor

theorem runCubeFibre_hom_none (n N : ℕ) (d : (SingleObj (PosBraid N))ᵒᵖ) :
    (runCubeFibre n N).hom.app d (cubeBot n ((runBase N).obj d)) = none := by
  have h1 := sigmaDesc_map_none n ((runBase N ⋙ strandDecomposition.functor).obj d)
    ((runSigma N).obj d) ((runStrandIso N).hom.app d)
  have h2 := partialActionFunctor_map_none (chartActionAt n N)
    ((strandComponentGarside N).unitIso.symm.hom.app d)
  change (runCubeFibre n N).hom.app d none = none
  simp only [runCubeFibre, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, types_comp_apply]
  exact congrArg _ ((congrArg _ h1).trans h2)

theorem runCubeFibre_inv_none (n N : ℕ) (d : (SingleObj (PosBraid N))ᵒᵖ) :
    (runCubeFibre n N).inv.app d none = cubeBot n ((runBase N).obj d) :=
  (congrArg _ (runCubeFibre_hom_none n N d).symm).trans
    (((runCubeFibre n N).app d).toEquiv.symm_apply_apply _)

/-- Off the cube's own strand count the fibre over the run is the undefined point alone. -/
theorem cubeFibre_run_eq_bot {n N : ℕ} (hN : N ≠ n) (d : (SingleObj (PosBraid N))ᵒᵖ)
    (x : (cubeFibre n).obj ((runBase N).obj d)) : x = cubeBot n ((runBase N).obj d) := by
  haveI := isEmpty_runChart hN
  haveI : Subsingleton ((partialActionFunctor (chartActionAt n N)).obj d) :=
    ⟨fun a b => by cases a <;> cases b <;> first | rfl | exact isEmptyElim ‹RunChart (□n) N›⟩
  exact ((runCubeFibre n N).app d).toEquiv.injective (Subsingleton.elim _ _)

/-- **Only the cube's own strand count carries a defined chart**, so every object of the base that
carries one is the run of `n` events. -/
theorem cover_of_defined (n : ℕ) (c : ((W Zbp).op).Localization) (x : (cubeFibre n).obj c)
    (hx : x ≠ cubeBot n c) : ∃ d, Nonempty ((runBase n).obj d ≅ c) := by
  obtain ⟨N, a, ha, rfl⟩ := exists_atStrands c
  set e := runIso a ha with he
  have hy : (cubeFibre n).map e.hom x ≠ cubeBot n _ := fun h => hx (by
    have := congrArg (fun t => (cubeFibre n).map e.inv t) h
    simpa only [← Functor.map_comp_apply, e.hom_inv_id, Functor.map_id_apply,
      cubeBot_absorbing] using this)
  obtain rfl : N = n := by
    by_contra hne
    exact hy (cubeFibre_run_eq_bot hne (op (SingleObj.star (PosBraid N))) _)
  exact ⟨op (SingleObj.star _), ⟨e.symm⟩⟩

/-! ## The identification -/

/-- **The category `cubeChartPresentation` presents is the charts over the run** — the base's
decomposition is transported, never evaluated. -/
noncomputable def cubeChartEquiv (n : ℕ) :
    ChartCat n ≌ (Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory :=
  Presents.preDefinedEquiv (cubeFibre n) (cubeBot n) (runBase n) (chartBot n)
    (runCubeFibre n n) (runCubeFibre_inv_none n n) (fun g => cubeBot_absorbing n g)
    (cover_of_defined n)

/-- **…and it is the right weak Bruhat order on `Sₙ`.** -/
noncomputable def definedCubeFibreWeakOrder (n : ℕ) :
    (Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory ≌ WeakOrder n :=
  (cubeChartEquiv n).symm.trans (chartWeakEquiv n)

/-- **…hence the localized cube itself.**  Two things put a `ᵒᵖ` here — the base is presented on
`((W Zbp).op).Localization`, and the atoms go *up* the weak order where a localization morphism
goes down — and `WeakOrder.revEquivalence` removes both at once. -/
noncomputable def definedCubeFibreLoc (n : ℕ) :
    (Presents.defined (cubeFibre n) (cubeBot n)).FullSubcategory ≌ (W (□n)).Localization :=
  ((definedCubeFibreWeakOrder n).trans (WeakOrder.revEquivalence n)).trans
    (locCubeWeakOrder n).symm

/-- **The localized cube, presented parametrically.**  Same polygraph as `cubeChartPresentation`,
read in the orientation the glue family consumes; `p` is still arbitrary. -/
noncomputable def cubeLocPresentation (n : ℕ) {P : Polygraph}
    (p : Presents P (((W Zbp).op).Localization)) :
    Presents (cubeChartPoly n p) ((W (□n)).Localization) :=
  (cubeChartPresentation n p).transport (definedCubeFibreLoc n)

end ChainCat
