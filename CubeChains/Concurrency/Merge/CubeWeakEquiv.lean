import CubeChains.Concurrency.Presentation.SliceExchange

/-!
# Concurrency/Merge/CubeWeakEquiv — `Ch (□n)[W⁻¹]` *is* the weak order

`locOverWeakOrder`, read at the cube.  `cubeTop n` is terminal, so `Ch (□n)` is its own slice;
`locOverEquivBase` moves that slice down to the base's slice over the one-block shape
`topDims n`; and there every permutation is a run (`onesTopEquiv`), which is the only thing the
general statement asks for.
-/

open CategoryTheory BPSet CubeChains CubeChain

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

/-- **`(Ch(□n)/cubeTop)[W⁻¹] ≌ Ch(□n)[W⁻¹]`.** -/
noncomputable def locOverTopEquivCube (n : ℕ) :
    ((W (□n)).over (X := cubeTop n)).Localization ≌ (W (□n)).Localization :=
  haveI := isLocalization_forget_cubeTop n
  Localization.uniq ((W (□n)).over (X := cubeTop n)).Q
    (Over.forget (cubeTop n) ⋙ (W (□n)).Q) ((W (□n)).over (X := cubeTop n))

/-! ## …and its runs are all of `Sₙ` -/

/-- **Over the one-block shape every permutation is a run** — `onesTopEquiv` names the run-arrow
that spells it. -/
theorem exists_runOver_topDims (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ a : RunOver (zObj (topDims n)), RunOver.perm (dimSum_topDims n) a = σ :=
  ⟨⟨Over.mk ((onesTopEquiv n).symm σ), fun _ hc => List.eq_of_mem_replicate hc⟩,
    (onesTopEquiv n).apply_symm_apply σ⟩

/-- **`Ch (□n)[W⁻¹]` is the right weak Bruhat order on `Perm (Fin n)`, read backwards.** -/
noncomputable def locCubeWeakOrder (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ :=
  (locOverTopEquivCube n).symm.trans <|
    (locOverEquivBase (□n) (cubeTop n)).trans <|
      locOverWeakOrder (dimSum_topDims n) (exists_runOver_topDims n)

end ChainCat
