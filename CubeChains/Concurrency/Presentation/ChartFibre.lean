import CubeChains.Concurrency.Presentation.BaseDecomposition
import CubeChains.Machinery.Presentation.Partial
import CubeChains.Machinery.Braid.WeakAction
import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Presentation/ChartFibre — a partial action per strand count is a presheaf on the base

`Ch Zbp[W⁻¹]` is the disjoint union of its strand components (`strandDecomposition`) and each is one
object carrying `PosBraid N`, so a family of **partial actions** — one per strand count — is a
presheaf on the whole localized base, with the undefined point absorbing by construction.

Only one strand count carries anything (`hemp`), so an object of the base with a defined element is
the run of that count; that is what identifies the defined part with the component's own.

The fibre family `Y` is a parameter: `SliceFibre` instantiates it at the runs over a chain of the
base, `CubeChartAction` at the charts of a cube over the run.  Everything a caller needs of the
opaque `strandDecomposition` is here — in particular `runChartFibre_hom_invariant`, which is why an
instance never unfolds the descent.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

variable {Y : ℕ → Type} (A : ∀ N : ℕ, PosBraid N →* (strictEnd (Y N))ᵐᵒᵖ)

/-- **The charts, as a presheaf on the localized base**: one fibre per strand count, that count's
braid monoid acting partially on it. -/
noncomputable def chartFibre : ((W Zbp).op).Localization ⥤ Type :=
  strandDecomposition.functor ⋙ Sigma.desc fun N =>
    (strandComponentGarside N).inverse ⋙ partialActionFunctor (A N)

/-- `none` is absorbing in each fibre, hence in the descent. -/
theorem chartSigmaDesc_map_none :
    ∀ (a b : Σ N : ℕ, (AtStrands N).FullSubcategory) (f : a ⟶ b),
      (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (A N)).map f none = none := by
  rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩
  exact partialActionFunctor_map_none _ _

/-- The undefined chart, at the single object of the strand-`N` component. -/
noncomputable def chartBot (N : ℕ) (c : (SingleObj (PosBraid N))ᵒᵖ) :
    (partialActionFunctor (A N)).obj c := none

/-- …and at every object of the base. -/
noncomputable def chartFibreBot (c : ((W Zbp).op).Localization) : (chartFibre A).obj c := none

theorem chartFibreBot_absorbing {c c' : ((W Zbp).op).Localization} (g : c ⟶ c') :
    (chartFibre A).map g (chartFibreBot A c) = chartFibreBot A c' :=
  chartSigmaDesc_map_none A _ _ (strandDecomposition.functor.map g)

/-! ## The defined charts of one component -/

/-- The defined charts at strand count `N`. -/
abbrev ChartsAt (N : ℕ) : Type :=
  (Presents.defined (partialActionFunctor (A N)) (chartBot A N)).FullSubcategory

/-- The chart a defined 0-cell names. -/
noncomputable def chartOfDefined {N : ℕ} (z : ChartsAt A N) : Y N :=
  z.obj.2.get (Option.ne_none_iff_isSome.mp z.property)

@[simp] theorem some_chartOfDefined {N : ℕ} (z : ChartsAt A N) :
    some (chartOfDefined A z) = z.obj.2 := Option.some_get _

/-- A morphism of the defined charts is a defined braid step. -/
theorem chartAction_hom {N : ℕ} {z w : ChartsAt A N} (f : z ⟶ w) :
    (A N f.hom.1.unop).unop.val (some (chartOfDefined A z)) = some (chartOfDefined A w) := by
  rw [some_chartOfDefined, some_chartOfDefined]
  exact f.hom.2

/-- …and every defined braid step is one — the converse of `chartAction_hom`. -/
def chartAction_homMk {N : ℕ} {z w : ChartsAt A N} (β : PosBraid N)
    (h : (A N β).unop.val (some (chartOfDefined A z)) = some (chartOfDefined A w)) : z ⟶ w :=
  ObjectProperty.homMk ⟨Quiver.Hom.op (show w.obj.1.unop ⟶ z.obj.1.unop from β), by
    change (A N β).unop.val z.obj.2 = w.obj.2
    rw [← some_chartOfDefined A z, ← some_chartOfDefined A w]
    exact h⟩

/-- **The defined charts of an injective action are a poset**: an arrow *is* the braid it
performs. -/
theorem chartsAt_isThin {N : ℕ} (hinj : ∀ {β γ : PosBraid N} {u v : Y N},
    (A N β).unop.val (some u) = some v → (A N γ).unop.val (some u) = some v → β = γ) :
    Quiver.IsThin (ChartsAt A N) := fun _ _ =>
  ⟨fun f g => ObjectProperty.hom_ext _ (Subtype.ext (Quiver.Hom.unop_inj
    (hinj (chartAction_hom A f) (chartAction_hom A g))))⟩

/-! ### …and of a weak action, the weak order

`weakActionOn` acts by length-additive right multiplication, so a defined braid step *is* a rise in
the right weak Bruhat order.  Where the permutations are unrestricted, the defined charts are that
order entire: one 0-cell per permutation, and one arrow per rise. -/

/-- **A defined braid step rises in the weak order** — the one reading every comparison below is
made through. -/
theorem weakActionOn_le {N : ℕ} {X : Equiv.Perm (Fin N) → Prop} {hX : WeakDown X} {Z : Type}
    {e : Z ≃ WeakSet X} {β : PosBraid N} {u v : Z}
    (h : (weakActionOn X e hX β).unop.val (some u) = some v) :
    WeakOrder.of (e u).1 ≤ WeakOrder.of (e v).1 := by
  obtain ⟨hv, hl⟩ := weakActionOn_reduced X e hX h
  rw [hv]
  exact WeakOrder.le_of_mul (by rw [← hv]; omega)

section Weak

variable {N : ℕ} {X : Equiv.Perm (Fin N) → Prop} {hX : WeakDown X} (e : Y N ≃ WeakSet X)
  (hA : A N = weakActionOn X e hX)

include hA

/-- **A braid is defined at a chart exactly where it adds all of its own crossings.** -/
theorem weakChart_eq_some_iff (β : PosBraid N) (u v : Y N) :
    (A N β).unop.val (some u) = some v ↔
      (e v).1 = (e u).1 * posPermHom N β ∧
        permLen (e u).1 + Multiplicative.toAdd (posLen N β) = permLen (e v).1 := by
  rw [hA, weakActionOn_eq_some_iff]

/-- **A defined braid is reduced**, hence a simple, and it multiplies by its own permutation. -/
theorem weakChart_reduced {β : PosBraid N} {u v : Y N}
    (h : (A N β).unop.val (some u) = some v) :
    (e v).1 = (e u).1 * posPermHom N β ∧
      permLen (e u).1 + permLen (posPermHom N β) = permLen (e v).1 := by
  rw [hA] at h
  exact weakActionOn_reduced _ _ _ h

/-- **The acting braid is pinned by the two charts.** -/
theorem weakChart_injective {β γ : PosBraid N} {u v : Y N}
    (hβ : (A N β).unop.val (some u) = some v) (hγ : (A N γ).unop.val (some u) = some v) :
    β = γ := by
  rw [hA] at hβ hγ
  exact weakActionOn_injective _ _ _ hβ hγ

/-- **…and every rise is realised**, by the simple that names the gap. -/
theorem weakChart_of_le {u v : Y N}
    (h : permLen (e u).1 + permLen ((e u).1⁻¹ * (e v).1) = permLen (e v).1) :
    (A N (posPerm ((e u).1⁻¹ * (e v).1))).unop.val (some u) = some v := by
  rw [hA]
  exact weakActionOn_of_le _ _ _ h

/-- **A defined braid step rises in the weak order.** -/
theorem weakChart_le {β : PosBraid N} {u v : Y N}
    (h : (A N β).unop.val (some u) = some v) :
    WeakOrder.of (e u).1 ≤ WeakOrder.of (e v).1 := by
  rw [hA] at h
  exact weakActionOn_le h

theorem chartsWeak_isThin : Quiver.IsThin (ChartsAt A N) :=
  chartsAt_isThin A fun hβ hγ => weakChart_injective A e hA hβ hγ

end Weak

/-! ### The unrestricted action, whose charts are the whole order -/

section WeakUniv

variable {N : ℕ} (e : Y N ≃ Equiv.Perm (Fin N))
  (hA : A N = weakActionOn _ (e.trans (weakSetUniv N).symm) weakDown_univ)

include hA

/-- The closed form, read on the permutations themselves. -/
theorem weakChartUniv_eq_some_iff (β : PosBraid N) (u v : Y N) :
    (A N β).unop.val (some u) = some v ↔
      e v = e u * posPermHom N β ∧
        permLen (e u) + Multiplicative.toAdd (posLen N β) = permLen (e v) :=
  weakChart_eq_some_iff A _ hA β u v

/-- **The defined charts of the unrestricted weak action are the right weak order on `Sₙ`.** -/
noncomputable def chartsWeak : ChartsAt A N ⥤ WeakOrder N where
  obj z := WeakOrder.of (e (chartOfDefined A z))
  map f := homOfLE (weakChart_le A _ hA (chartAction_hom A f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **…as an equivalence.**  Fullness is the simple that names the gap, essential surjectivity the
chart that names each permutation, and faithfulness is thinness. -/
noncomputable def chartsWeakEquiv : ChartsAt A N ≌ WeakOrder N :=
  haveI := chartsWeak_isThin A _ hA
  haveI : (chartsWeak A e hA).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  haveI : (chartsWeak A e hA).Full := ⟨fun {_ _} h =>
    ⟨chartAction_homMk A _ (weakChart_of_le A _ hA (WeakOrder.le_def.mp (leOfHom h))),
      Subsingleton.elim _ _⟩⟩
  haveI : (chartsWeak A e hA).EssSurj := ⟨fun σ =>
    ⟨⟨⟨op (SingleObj.star (PosBraid N)), some (e.symm (WeakOrder.perm σ))⟩,
        Option.some_ne_none _⟩,
      ⟨eqToIso (by
        change WeakOrder.of (e (e.symm (WeakOrder.perm σ))) = σ
        rw [Equiv.apply_symm_apply, WeakOrder.of_perm])⟩⟩⟩
  haveI : (chartsWeak A e hA).IsEquivalence := { }
  (chartsWeak A e hA).asEquivalence

end WeakUniv

/-! ## Restricting the fibre to the run

`strandDecomposition.functor` is a `Functor.inv`, opaque on objects; nothing below evaluates it.
Restricting along `runBase N` undoes the decomposition by the counit. -/

/-- The strand-`N` component, included into the disjoint union. -/
noncomputable def runSigma (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ⥤ Σ M : ℕ, (AtStrands M).FullSubcategory :=
  runBaseAt N ⋙ Sigma.incl (C := fun M : ℕ => (AtStrands M).FullSubcategory) N

noncomputable def runStrandIso (N : ℕ) :
    runBase N ⋙ strandDecomposition.functor ≅ runSigma N :=
  Functor.isoWhiskerLeft (runSigma N) strandDecomposition.counitIso ≪≫ (runSigma N).rightUnitor

/-- **The fibre over the run of `N` events** is the partial action at that strand count. -/
noncomputable def runChartFibre (N : ℕ) :
    runBase N ⋙ chartFibre A ≅ partialActionFunctor (A N) :=
  Functor.isoWhiskerRight (runStrandIso N)
      (Sigma.desc fun M => (strandComponentGarside M).inverse
        ⋙ partialActionFunctor (A M)) ≪≫
    Functor.isoWhiskerRight (strandComponentGarside N).unitIso.symm
      (partialActionFunctor (A N)) ≪≫
    (partialActionFunctor (A N)).leftUnitor

/-- The transport to the component, as a composite of two action maps. -/
theorem runChartFibre_hom_apply (N : ℕ) (c : (SingleObj (PosBraid N))ᵒᵖ)
    (x : (chartFibre A).obj ((runBase N).obj c)) :
    (runChartFibre A N).hom.app c x
      = (partialActionFunctor (A N)).map ((strandComponentGarside N).unitIso.symm.hom.app c)
          ((Sigma.desc fun M => (strandComponentGarside M).inverse
            ⋙ partialActionFunctor (A M)).map ((runStrandIso N).hom.app c) x) := by
  simp only [runChartFibre, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, types_comp_apply]
  rfl

/-- …and back, likewise: the inverse of an iso of the descent is again an action map. -/
theorem runChartFibre_inv_apply (N : ℕ) (c : (SingleObj (PosBraid N))ᵒᵖ)
    (x : (partialActionFunctor (A N)).obj c) :
    (runChartFibre A N).inv.app c x
      = (Sigma.desc fun M => (strandComponentGarside M).inverse
            ⋙ partialActionFunctor (A M)).map ((runStrandIso N).inv.app c)
          ((partialActionFunctor (A N)).map
            ((strandComponentGarside N).unitIso.symm.inv.app c) x) := by
  simp only [runChartFibre, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, types_comp_apply]
  rfl

theorem runChartFibre_hom_none (N : ℕ) (d : (SingleObj (PosBraid N))ᵒᵖ) :
    (runChartFibre A N).hom.app d (chartFibreBot A ((runBase N).obj d)) = none := by
  have h1 := chartSigmaDesc_map_none A ((runBase N ⋙ strandDecomposition.functor).obj d)
    ((runSigma N).obj d) ((runStrandIso N).hom.app d)
  have h2 := partialActionFunctor_map_none (A N)
    ((strandComponentGarside N).unitIso.symm.hom.app d)
  change (runChartFibre A N).hom.app d none = none
  rw [runChartFibre_hom_apply]
  exact (congrArg _ h1).trans h2

theorem runChartFibre_inv_none (N : ℕ) (d : (SingleObj (PosBraid N))ᵒᵖ) :
    (runChartFibre A N).inv.app d (chartBot A N d) = chartFibreBot A ((runBase N).obj d) :=
  (congrArg _ (runChartFibre_hom_none A N d).symm).trans
    (((runChartFibre A N).app d).toEquiv.symm_apply_apply _)

/-- The chart over the run a value of the partial action is. -/
noncomputable def runChart (N : ℕ) (u : Y N) :
    (chartFibre A).obj ((runBase N).obj (op (SingleObj.star (PosBraid N)))) :=
  (runChartFibre A N).inv.app (op (SingleObj.star (PosBraid N))) (some u)

@[simp] theorem runChartFibre_hom_runChart (N : ℕ) (u : Y N) :
    (runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N))) (runChart A N u) = some u :=
  ((runChartFibre A N).app (op (SingleObj.star (PosBraid N)))).toEquiv.apply_symm_apply (some u)

/-- **A chart over the run is the value it names** — `runChartFibre` is an isomorphism. -/
theorem eq_runChart (N : ℕ)
    {x : (chartFibre A).obj ((runBase N).obj (op (SingleObj.star (PosBraid N))))} {u : Y N}
    (h : (runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N))) x = some u) :
    x = runChart A N u :=
  ((runChartFibre A N).app (op (SingleObj.star (PosBraid N)))).toEquiv.injective
    (h.trans (runChartFibre_hom_runChart A N u).symm)

theorem runChart_ne_bot (N : ℕ) (u : Y N) :
    runChart A N u ≠ chartFibreBot A ((runBase N).obj (op (SingleObj.star (PosBraid N)))) :=
  fun h => Option.some_ne_none u
    ((runChartFibre_hom_runChart A N u).symm.trans
      ((congrArg ((runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N)))) h).trans
        (runChartFibre_hom_none A N (op (SingleObj.star (PosBraid N))))))

/-- **A braid acts on the charts over the run by the partial action** — the naturality of
`runChartFibre`, which is the only thing that reads through the opaque decomposition. -/
theorem runChartFibre_hom_map (N : ℕ) (β : PosBraid N)
    (x : (chartFibre A).obj ((runBase N).obj (op (SingleObj.star (PosBraid N))))) :
    (runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N)))
        ((chartFibre A).map ((runBase N).map (posArrow N β)) x)
      = (A N β).unop.val
          ((runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N))) x) :=
  NatTrans.naturality_apply (runChartFibre A N).hom (posArrow N β) x

/-- **…so a defined step of the action is a defined step of the fibre.** -/
theorem chartFibre_map_runChart (N : ℕ) (β : PosBraid N) {u v : Y N}
    (h : (A N β).unop.val (some u) = some v) :
    (chartFibre A).map ((runBase N).map (posArrow N β)) (runChart A N u) = runChart A N v :=
  ((runChartFibre A N).app (op (SingleObj.star (PosBraid N)))).toEquiv.injective
    (((runChartFibre_hom_map A N β (runChart A N u)).trans
        (congrArg (A N β).unop.val (runChartFibre_hom_runChart A N u))).trans
      (h.trans (runChartFibre_hom_runChart A N v).symm))

/-- **…and back**: a defined step of the fibre over the run is one of the action. -/
theorem action_of_chartFibre_map (N : ℕ) (β : PosBraid N)
    {x y : (chartFibre A).obj ((runBase N).obj (op (SingleObj.star (PosBraid N))))}
    (h : (chartFibre A).map ((runBase N).map (posArrow N β)) x = y) :
    (A N β).unop.val ((runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N))) x)
      = (runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N))) y :=
  (runChartFibre_hom_map A N β x).symm.trans
    (congrArg ((runChartFibre A N).hom.app (op (SingleObj.star (PosBraid N)))) h)

/- Sealed: the unifier will otherwise evaluate the transport, and every `Option.get` downstream
sends it into the strand decomposition. -/
attribute [irreducible] runChart

/-- Where there is nothing to act on, the fibre over the run is the undefined point alone. -/
theorem chartFibre_run_eq_bot {N : ℕ} (hN : IsEmpty (Y N)) (d : (SingleObj (PosBraid N))ᵒᵖ)
    (x : (chartFibre A).obj ((runBase N).obj d)) : x = chartFibreBot A ((runBase N).obj d) := by
  haveI := hN
  haveI : Subsingleton ((partialActionFunctor (A N)).obj d) :=
    ⟨fun a b => by cases a <;> cases b <;> first | rfl | exact isEmptyElim ‹Y N›⟩
  exact ((runChartFibre A N).app d).toEquiv.injective (Subsingleton.elim _ _)

/-- **Only one strand count carries a defined chart**, so every object of the base that carries one
is the run of that many events. -/
theorem chartFibre_cover_of_defined {n₀ : ℕ} (hemp : ∀ N, N ≠ n₀ → IsEmpty (Y N))
    (c : ((W Zbp).op).Localization) (x : (chartFibre A).obj c) (hx : x ≠ chartFibreBot A c) :
    ∃ d, Nonempty ((runBase n₀).obj d ≅ c) := by
  obtain ⟨N, a, ha, rfl⟩ := exists_atStrands c
  set e := runIso a ha with he
  have hy : (chartFibre A).map e.hom x ≠ chartFibreBot A _ := fun h => hx (by
    have := congrArg (fun t => (chartFibre A).map e.inv t) h
    simpa only [← Functor.map_comp_apply, e.hom_inv_id, Functor.map_id_apply,
      chartFibreBot_absorbing] using this)
  obtain rfl : N = n₀ := by
    by_contra hne
    exact hy (chartFibre_run_eq_bot A (hemp N hne) (op (SingleObj.star (PosBraid N))) _)
  exact ⟨op (SingleObj.star _), ⟨e.symm⟩⟩

/-! ## A map of the fibres

A family of maps of the fibres — one per strand count, commuting with the action **where it is
defined** — is a lax map of the two presheaves.  It is never a natural transformation: a step
undefined upstairs may be defined downstairs. -/

section Fam

variable {Y' : ℕ → Type} (A' : ∀ N : ℕ, PosBraid N →* (strictEnd (Y' N))ᵐᵒᵖ) (η : ∀ N, Y N → Y' N)

/-- The family of maps a family of maps of the fibres gives. -/
noncomputable def chartFam (c : ((W Zbp).op).Localization) :
    (chartFibre A).obj c → (chartFibre A').obj c :=
  Option.map (η (strandDecomposition.functor.obj c).1)

/-- **A defined step is carried across, one strand count at a time.** -/
theorem sigmaDesc_fam
    (hη : ∀ (N : ℕ) (β : PosBraid N) (u v : Y N), (A N β).unop.val (some u) = some v →
      (A' N β).unop.val (some (η N u)) = some (η N v))
    {a b : Σ N : ℕ, (AtStrands N).FullSubcategory} (m : a ⟶ b) (u : Y a.1) (v : Y b.1)
    (h : (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (A N)).map m (some u) = some v) :
    (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (A' N)).map m (some (η a.1 u)) = some (η b.1 v) := by
  cases m with
  | mk f => exact hη _ _ u v h

/-- **A defined step of the base is a defined step of one component** — the shape in which every
property of the action is read off, the strand count being opaque. -/
theorem sigmaDesc_rel {motive : ∀ N M : ℕ, Y N → Y M → Prop}
    (hmot : ∀ (N : ℕ) (β : PosBraid N) (u v : Y N),
      (A N β).unop.val (some u) = some v → motive N N u v)
    {a b : Σ N : ℕ, (AtStrands N).FullSubcategory} (m : a ⟶ b) (u : Y a.1) (v : Y b.1)
    (h : (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (A N)).map m (some u) = some v) :
    motive a.1 b.1 u v := by
  cases m with
  | mk f => exact hmot _ _ u v h

/-- **…hence across the whole base**: a family of maps of the fibres commuting with the action
*where it is defined* is a lax map of the two presheaves. -/
theorem partialFam_chartFam
    (hη : ∀ (N : ℕ) (β : PosBraid N) (u v : Y N), (A N β).unop.val (some u) = some v →
      (A' N β).unop.val (some (η N u)) = some (η N v)) :
    Presents.PartialFam (chartFibre A) (chartFibre A') (chartFibreBot A) (chartFibreBot A')
      (chartFam A A' η) where
  ne_bot c x hx := by
    obtain ⟨u, rfl⟩ : ∃ u : Y (strandDecomposition.functor.obj c).1, x = some u :=
      Option.ne_none_iff_exists'.mp hx
    exact Option.some_ne_none _
  lax {c c'} g x hx hgx := by
    obtain ⟨u, rfl⟩ : ∃ u : Y (strandDecomposition.functor.obj c).1, x = some u :=
      Option.ne_none_iff_exists'.mp hx
    obtain ⟨v, hv⟩ : ∃ v : Y (strandDecomposition.functor.obj c').1,
        (chartFibre A).map g (some u) = some v := Option.ne_none_iff_exists'.mp hgx
    rw [hv]
    exact sigmaDesc_fam A A' η hη (strandDecomposition.functor.map g) u v hv

end Fam

/-! ## An invariant of the action, along the descent

The transport to the component is two action maps in a row, so anything monotone along a defined
step of the action is monotone along it — in both directions, hence *fixed* by it.  That is the
only thing an instantiation ever needs of the opaque decomposition. -/

section Invariant

variable {Z : Type*} [PartialOrder Z] {π : ∀ N, Y N → Z}
  (hstep : ∀ (N : ℕ) (β : PosBraid N) (u v : Y N),
    (A N β).unop.val (some u) = some v → π N u ≤ π N v)

/-- **A composite of two partial maps raising `π` raises it** — the middle value is defined because
the undefined point is absorbing.  Both directions of the transport are this. -/
theorem chartLe_of_comp {N M L : ℕ} {f : Option (Y N) → Option (Y M)}
    {g : Option (Y M) → Option (Y L)} (hg : g none = none)
    (hf : ∀ u v, f (some u) = some v → π N u ≤ π M v)
    (hg' : ∀ u v, g (some u) = some v → π M u ≤ π L v)
    {u : Y N} {w : Y L} (h : g (f (some u)) = some w) : π N u ≤ π L w := by
  rcases hm : f (some u) with _ | v
  · rw [hm, hg] at h; exact absurd h (by simp)
  · exact le_trans (hf u v hm) (hg' v w (by rw [← hm]; exact h))

include hstep

/-- …read on the descent, where the strand count is opaque. -/
theorem chartLe_of_sigmaDesc {a b : Σ N : ℕ, (AtStrands N).FullSubcategory} (m : a ⟶ b)
    (u : Y a.1) (v : Y b.1)
    (h : (Sigma.desc fun N => (strandComponentGarside N).inverse
        ⋙ partialActionFunctor (A N)).map m (some u) = some v) : π a.1 u ≤ π b.1 v :=
  sigmaDesc_rel A (motive := fun N M u v => π N u ≤ π M v) hstep m u v h

/-- **The transport to the component raises `π`.** -/
theorem chartLe_of_runChartFibre_hom {N : ℕ} {c : (SingleObj (PosBraid N))ᵒᵖ}
    {u : Y (strandDecomposition.functor.obj ((runBase N).obj c)).1} {v : Y N}
    (h : (runChartFibre A N).hom.app c (some u) = some v) :
    π (strandDecomposition.functor.obj ((runBase N).obj c)).1 u ≤ π N v := by
  rw [runChartFibre_hom_apply] at h
  exact chartLe_of_comp (partialActionFunctor_map_none (A N) _)
    (fun _ _ hm => chartLe_of_sigmaDesc A hstep ((runStrandIso N).hom.app c) _ _ hm)
    (fun _ _ hm => hstep _ _ _ _ hm) h

/-- **…and so does the transport back.** -/
theorem chartLe_of_runChartFibre_inv {N : ℕ} {c : (SingleObj (PosBraid N))ᵒᵖ} {u : Y N}
    {v : Y (strandDecomposition.functor.obj ((runBase N).obj c)).1}
    (h : (runChartFibre A N).inv.app c (some u) = some v) :
    π N u ≤ π (strandDecomposition.functor.obj ((runBase N).obj c)).1 v := by
  rw [runChartFibre_inv_apply] at h
  exact chartLe_of_comp (chartSigmaDesc_map_none A _ _ ((runStrandIso N).inv.app c))
    (fun _ _ hm => hstep _ _ _ _ hm)
    (fun _ _ hm => chartLe_of_sigmaDesc A hstep ((runStrandIso N).inv.app c) _ _ hm) h

/-- **The transport to the component fixes `π`** — it raises it both ways. -/
theorem runChartFibre_hom_invariant {N : ℕ} {c : (SingleObj (PosBraid N))ᵒᵖ}
    {u : Y (strandDecomposition.functor.obj ((runBase N).obj c)).1} {v : Y N}
    (h : (runChartFibre A N).hom.app c (some u) = some v) :
    π (strandDecomposition.functor.obj ((runBase N).obj c)).1 u = π N v :=
  _root_.le_antisymm (chartLe_of_runChartFibre_hom A hstep h)
    (chartLe_of_runChartFibre_inv A hstep (by
      rw [← h]; exact ((runChartFibre A N).app c).toEquiv.symm_apply_apply _))

end Invariant

/-- **The defined part of the presheaf is the defined part of its one live component.** -/
noncomputable def chartFibreEquiv {n₀ : ℕ} (hemp : ∀ N, N ≠ n₀ → IsEmpty (Y N)) :
    (Presents.defined (partialActionFunctor (A n₀)) (chartBot A n₀)).FullSubcategory ≌
      (Presents.defined (chartFibre A) (chartFibreBot A)).FullSubcategory :=
  Presents.preDefinedEquiv (chartFibre A) (chartFibreBot A) (runBase n₀) (chartBot A n₀)
    (runChartFibre A n₀) (runChartFibre_inv_none A n₀) (fun g => chartFibreBot_absorbing A g)
    (chartFibre_cover_of_defined A hemp)

end ChainCat
