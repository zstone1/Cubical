import CubeChains.Concurrency.Presentation.CubeChartAction
import CubeChains.Concurrency.Merge.CubeWeakEquiv

/-!
# Concurrency/Presentation/CubeChartWeakOrder — the cube's defined charts are the weak order

A chart of `□n` over the run is its crossing permutation (`crossOnesEquiv`), and a braid is defined
at it exactly where it adds all of its own crossings (`chartActionAt_eq_some_iff`) — which is the
right weak Bruhat order on `Sₙ`, so the partial atom action realises it (`chartWeakEquiv`).
Compare `locCubeWeakOrder`, the same order reached from thinness instead.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-! ## The charts over the run, as a category -/

/-- The defined charts of `□n` over the run of `n` events. -/
abbrev ChartCat (n : ℕ) : Type := ChartsAt (chartActionAt n) n

/-- The chart an object of `ChartCat` names. -/
noncomputable def chartOf (z : ChartCat n) : RunChart (□n) n := chartOfDefined (chartActionAt n) z

@[simp] theorem some_chartOf (z : ChartCat n) : some (chartOf z) = z.obj.2 :=
  some_chartOfDefined (chartActionAt n) z

/-- A morphism of `ChartCat` is a defined braid step. -/
theorem chartActionAt_hom {z w : ChartCat n} (f : z ⟶ w) :
    (chartActionAt n n f.hom.1.unop).unop.val (some (chartOf z)) = some (chartOf w) :=
  chartAction_hom (chartActionAt n) f

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

end ChainCat
