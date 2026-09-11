import CubeChains.Concurrency.Merge.CubeCrossing
import CubeChains.Machinery.Braid.WeakOrder

/-!
# Concurrency/Merge/CubeWeakOrder — the localized cube slice is the weak order

`crossLen_eq_add` says a refinement drops the Coxeter length by exactly the length of its own
crossing permutation.  That *is* the right weak (Bruhat) order: `cross c = cross c' * crossPerm f`
with the lengths adding, so `cross c'` sits below `cross c`.  So `cross` is a functor to the weak
order read backwards, it inverts `W`, and it descends to the localization.

The order itself is `Machinery/Braid/WeakOrder`, which names no chain.
-/

open CategoryTheory BPSet CubeChains CubeChain


namespace ChainCat

variable {n : ℕ}

/-! ## `cross`, as a functor to the weak order -/

/-- **A refinement factors the crossing permutation on the right.** -/
theorem cross_eq_mul {c c' : Ch (□n)} (f : c ⟶ c') :
    cross c = cross c' * crossPerm (dimSum_dims_cube c) f := by
  rw [cross, ← comp_toCubeTop f, crossPerm_comp]
  rfl

/-- The weak-order class of a chain of `□n` — its crossing permutation. -/
noncomputable def weakClass (c : Ch (□n)) : WeakOrder n := WeakOrder.of (cross c)


/-- **A refinement descends the weak order**, by length-additivity of the crossings. -/
theorem weakClass_le {c c' : Ch (□n)} (f : c ⟶ c') : weakClass c' ≤ weakClass c :=
  WeakOrder.le_of_mul_eq (cross_eq_mul f).symm (crossLen_eq_add f)

theorem weakClass_eq_of_W {c c' : Ch (□n)} {f : c ⟶ c'} (hf : W (□n) f) :
    weakClass c = weakClass c' := by
  rw [weakClass, weakClass, cross_eq_mul f, crossPerm_eq_one_of_W _ hf, mul_one]

theorem weakClass_le_of_W {c c' : Ch (□n)} {f : c ⟶ c'} (hf : W (□n) f) :
    weakClass c ≤ weakClass c' := le_of_eq (weakClass_eq_of_W hf)

theorem weakClass_le_of_loc_hom {c c' : Ch (□n)}
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') : weakClass c' ≤ weakClass c :=
  deg_le_of_loc_hom weakClass weakClass_le (W (□n)) weakClass_le_of_W g


/-! ## The collapse: off `W`, the crossing permutation strictly descends -/

/-- **A refinement that preserves the crossing permutation is a merge.**  With `crossLen_eq_add`
this is immediate, and it is what makes the weak order the whole story: a non-`W` arrow strictly
descends `cross`, so the `W`-arrows are exactly the fibres of `cross`. -/
theorem W_of_cross_eq {c c' : Ch (□n)} (f : c ⟶ c') (h : cross c = cross c') : W (□n) f := by
  rw [W_iff_crossPerm_eq_one (dimSum_dims_cube c) f]
  refine eq_one_of_permLen_eq_zero _ ?_
  have hadd := crossLen_eq_add f
  rw [crossLen, crossLen, h] at hadd
  omega

/-- `W` is exactly the class of refinements fixing the weak-order class. -/
theorem W_iff_weakClass_eq {c c' : Ch (□n)} (f : c ⟶ c') :
    W (□n) f ↔ weakClass c = weakClass c' :=
  ⟨weakClass_eq_of_W, fun h => W_of_cross_eq f (WeakOrder.of_injective h)⟩


/-! ## The localization is not the braid action

A hom-set is empty as soon as it would have to climb the weak order, so `Ch(□²)[W⁻¹]` is
disconnected — while the positive braids act transitively on the orderings, so every hom-set of
`PosBraidAction n` is inhabited.  The braiding lives in the decoration: `hLocEquiv` is about
`Hbp □n`, not `□n`. -/

/-- **A hom-set of the localized cube slice is empty** when it would have to climb the weak
order. -/
theorem isEmpty_loc_hom_of_not_le {c c' : Ch (□n)} (h : ¬ weakClass c' ≤ weakClass c) :
    IsEmpty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :=
  isEmpty_loc_hom_of_deg_lt weakClass weakClass_le (W (□n)) weakClass_le_of_W h

/-- **`Ch(□²)[W⁻¹]` has an empty hom-set**: the braided chain is not below the one-bead chain. -/
theorem isEmpty_loc_hom_cubeTop :
    IsEmpty ((W (□2)).Q.obj (cubeTop 2) ⟶ (W (□2)).Q.obj (cutChain (cubeReorder 1 1))) :=
  isEmpty_loc_hom_of_not_le fun hle => by
    have h := WeakOrder.permLen_le_of_le hle
    simp only [weakClass, WeakOrder.perm_of, cross_cubeTop, permLen_one] at h
    exact absurd h (not_le.mpr crossLen_cutChain_pos)

/-- **The positive braids act transitively on the orderings**, so every hom-set of
`PosBraidAction n` is inhabited. -/
theorem nonempty_posBraidAction_hom (p q : PosBraidAction n) : Nonempty (p ⟶ q) :=
  ⟨⟨posPerm (q.back * p.back⁻¹), by
    change posPermHom n (posPerm (q.back * p.back⁻¹)) * p.back = q.back
    rw [posPermHom_posPerm, mul_assoc, inv_mul_cancel, mul_one]⟩⟩

theorem nonempty_posBraidAction_hom_op (p q : (PosBraidAction n)ᵒᵖ) : Nonempty (p ⟶ q) :=
  ⟨(nonempty_posBraidAction_hom q.unop p.unop).some.op⟩

/-- **`Ch(□²)[W⁻¹]` is not the positive braid action.**  Both have `2! = 2` objects, but the
localized cube slice is not connected and the action category is. -/
theorem not_nonempty_equiv_posBraidAction :
    ¬ Nonempty ((W (□2)).Localization ≌ PosBraidAction 2) := fun ⟨e⟩ =>
  isEmpty_loc_hom_cubeTop.elim
    (nonempty_hom_of_equiv e.symm nonempty_posBraidAction_hom _ _).some

/-- …and not its opposite either, which is the form `hLocActionPresentation` presents. -/
theorem not_nonempty_equiv_posBraidAction_op :
    ¬ Nonempty ((W (□2)).Localization ≌ (PosBraidAction 2)ᵒᵖ) := fun ⟨e⟩ =>
  isEmpty_loc_hom_cubeTop.elim
    (nonempty_hom_of_equiv e.symm nonempty_posBraidAction_hom_op _ _).some


/-! ## Every object is a run

A chain of a cube *is* its wedge map (`chainHomEquiv`), so the base's crossing-free merge out
of the run lifts to one here by composing maps — the fibre description of `Ch (□n) ⥤ Ch Zbp`. -/

/-- **Every chain of a cube is entered from a run by a merge.** -/
theorem exists_W_run (c : Ch (□n)) :
    ∃ (r : Ch (□n)) (f : r ⟶ c), r.dims = 𝟙^n ∧ W (□n) f :=
  exists_W_run_gen c (dimSum_dims_cube c)

/-- **A run is pinned by its crossing permutation.**  A chain of a cube is its wedge map, which
`crossPerm` sees, and a wedge map is pinned by its crossing permutation
(`hom_ext_of_crossPerm`) — so `cross` is injective on runs, with no coordinates in sight. -/
theorem run_eq_of_cross_eq {r r' : Ch (□n)} (hr : r.dims = 𝟙^n) (hr' : r'.dims = 𝟙^n)
    (h : cross r = cross r') : r = r' := by
  obtain ⟨d, x⟩ := r
  obtain ⟨d', x'⟩ := r'
  subst hr
  subst hr'
  have key : zHom (Hom.φ (toCubeTop (⟨𝟙^n, x⟩ : Ch (□n))))
      = zHom (Hom.φ (toCubeTop (⟨𝟙^n, x'⟩ : Ch (□n)))) :=
    hom_ext_of_crossPerm (h := dimSum_replicate n) h
  have hφ : x ≫ (topWedgeIso n).inv = x' ≫ (topWedgeIso n).inv := by
    have hk := congrArg Hom.φ key
    rwa [zHom_φ, zHom_φ] at hk
  rw [(cancel_mono (topWedgeIso n).inv).mp hφ]


theorem run_dims (r : Run (□n)) : r.chain.dims = 𝟙^n :=
  ones_dims_eq r.ones (wedgeDimSum_eq r.chain.map)

end ChainCat
