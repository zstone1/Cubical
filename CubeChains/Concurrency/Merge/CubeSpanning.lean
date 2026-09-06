import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Executions.Elements

/-!
# Concurrency/Merge/CubeSpanning — the cube's arrows are the base's

`cubeTop n` is terminal, so `Ch (□n)` is its own slice; `toChZ (□n)` is a discrete fibration, so
that slice is the base's over the one-block shape.  Both comparisons localize the same class, and
a hom of one localization is a hom of any other — so the base's spanning theorem
(`nonempty_locOver_hom`) *is* `nonempty_loc_hom`, with no second induction on `permLen`.
-/

open CategoryTheory BPSet CubeChains CubeChain

/-- **A hom of one localization is a hom of any other**, at the same pair of objects. -/
theorem CategoryTheory.nonempty_loc_hom_of_isLocalization {C D₁ D₂ : Type*} [Category C]
    [Category D₁] [Category D₂] (W : MorphismProperty C) (L₁ : C ⥤ D₁) [L₁.IsLocalization W]
    (L₂ : C ⥤ D₂) [L₂.IsLocalization W] {X Y : C}
    (h : Nonempty (L₁.obj X ⟶ L₁.obj Y)) : Nonempty (L₂.obj X ⟶ L₂.obj Y) := by
  obtain ⟨f⟩ := h
  refine ⟨(Localization.compUniqFunctor L₁ L₂ W).inv.app X ≫
    (Localization.uniq L₁ L₂ W).functor.map f ≫ (Localization.compUniqFunctor L₁ L₂ W).hom.app Y⟩

namespace ChainCat

variable {n : ℕ}

/-! ## `Ch (□n)` is its own slice

`cubeTop n` is terminal, so `Over.forget` is an equivalence carrying `W/cubeTop` to `W` — a
localization of the slice at the class the cube's own localization inverts. -/

/-- **The one-bead chain is terminal**: every chain refines it, and `Ch (□n)` is thin. -/
noncomputable def isTerminal_cubeTop (n : ℕ) : Limits.IsTerminal (cubeTop n) :=
  Limits.IsTerminal.ofUniqueHom toCubeTop fun _ _ => Subsingleton.elim _ _

instance forget_cubeTop_isEquivalence (n : ℕ) : (Over.forget (cubeTop n)).IsEquivalence :=
  (Over.equivalenceOfIsTerminal (isTerminal_cubeTop n)).isEquivalence_functor

theorem isLocalization_forget_cubeTop (n : ℕ) :
    (Over.forget (cubeTop n) ⋙ (W (□n)).Q).IsLocalization ((W (□n)).over (X := cubeTop n)) :=
  Functor.IsLocalization.of_inverseImage _ _ _ _ rfl

/-! ## …and that slice is the base's

`toChZ (□n)` is a discrete fibration, so `Over.post` is an equivalence of the two slices, and it
carries one class to the other on the nose. -/

/-- Serialising a chain morphism keeps its crossing permutation. -/
theorem crossPerm_toChZ {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b) :
    crossPerm (a := (toChZ K).obj a) (b := (toChZ K).obj b) h ((toChZ K).map g)
      = crossPerm h g := rfl

/-- **Serialising is a localization of the slice**: `W K` is `W Zbp` pulled back, and the two
slices agree because `toChZ K` is a discrete fibration. -/
theorem isLocalization_post_chZ (K : BPSet) (c : Ch K) :
    (Over.post (X := c) (toChZ K) ⋙
        ((W Zbp).over (X := (toChZ K).obj c)).Q).IsLocalization ((W K).over (X := c)) := by
  rw [show (W K).over (X := c) = ((W Zbp).inverseImage (toChZ K)).over from
    congrArg (fun V => MorphismProperty.over V) (W_eq_inverseImage_toChZ K)]
  infer_instance

/-- **The weak class of a chain is the weak order of its image in the base's slice.** -/
theorem weakOver_post (c : Ch (□n)) :
    weakOver (dimSum_dims_cube (cubeTop n))
        ((Over.post (X := cubeTop n) (toChZ (□n))).obj (Over.mk (toCubeTop c)))
      = weakClass c :=
  congrArg WeakOrder.of (crossPerm_toChZ (dimSum_dims_cube c) (toCubeTop c))

/-- **Everything the weak order allows is an arrow of `Ch (□n)[W⁻¹]`** — the base's spanning
theorem, read through the two localizations. -/
theorem nonempty_loc_hom {c c' : Ch (□n)} (h : weakClass c' ≤ weakClass c) :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') := by
  haveI := isLocalization_post_chZ (□n) (cubeTop n)
  haveI := isLocalization_forget_cubeTop n
  have hle : weakOver (dimSum_dims_cube (cubeTop n))
        ((Over.post (X := cubeTop n) (toChZ (□n))).obj (Over.mk (toCubeTop c')))
      ≤ weakOver (dimSum_dims_cube (cubeTop n))
        ((Over.post (X := cubeTop n) (toChZ (□n))).obj (Over.mk (toCubeTop c))) := by
    rw [weakOver_post, weakOver_post]
    exact h
  exact nonempty_loc_hom_of_isLocalization ((W (□n)).over (X := cubeTop n))
    (Over.post (X := cubeTop n) (toChZ (□n)) ⋙
      ((W Zbp).over (X := (toChZ (□n)).obj (cubeTop n))).Q)
    (Over.forget (cubeTop n) ⋙ (W (□n)).Q)
    (nonempty_locOver_hom (dimSum_dims_cube (cubeTop n)) hle)

end ChainCat
