import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Concurrency.Merge.CubeSpanning
import CubeChains.Concurrency.Merge.CubeFaces

/-!
# Concurrency/Merge/CubeWeakEquiv — `Ch (□n)[W⁻¹]` *is* the weak order

The comparison **is** the weak-order class (`weakClassLoc`, a `degLoc`), so it computes on a
`Q`-image: full by `nonempty_loc_hom`, essentially surjective because every permutation is a run
(`weakClass_runAt`), faithful because `Ch (□n)[W⁻¹]` is a poset — which is the one thing
`locOverWeakOrder` is spent on, read at the cube through the terminality of `cubeTop n`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-- **`(Ch(□n)/cubeTop)[W⁻¹] ≌ Ch(□n)[W⁻¹]`.** -/
noncomputable def locOverTopEquivCube (n : ℕ) :
    ((W (□n)).over (X := cubeTop n)).Localization ≌ (W (□n)).Localization :=
  haveI := isLocalization_forget_cubeTop n
  Localization.uniq ((W (□n)).over (X := cubeTop n)).Q
    (Over.forget (cubeTop n) ⋙ (W (□n)).Q) ((W (□n)).over (X := cubeTop n))

/-- **Over the one-block shape every permutation is a run** — `onesTopEquiv` names the run-arrow
that spells it. -/
theorem exists_runOver_topDims (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ a : RunOver (zObj (topDims n)), RunOver.perm (dimSum_topDims n) a = σ :=
  ⟨⟨Over.mk ((onesTopEquiv n).symm σ), fun _ hc => List.eq_of_mem_replicate hc⟩,
    (onesTopEquiv n).apply_symm_apply σ⟩

/-- **`Ch (□n)[W⁻¹]` is a poset** — `cubeTop n` is terminal, so it is the localized slice over it,
and that is the base's over the one-block shape. -/
instance isThin_locCube (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) :=
  haveI e : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ :=
    (locOverTopEquivCube n).symm.trans <|
      (locOverEquivBase (□n) (cubeTop n)).trans <|
        locOverWeakOrder (dimSum_topDims n) (exists_runOver_topDims n)
  fun _ _ => ⟨fun _ _ => e.functor.map_injective (Subsingleton.elim _ _)⟩

/-! ## The weak-order class, localized -/

/-- **The weak-order class on `Ch (□n)[W⁻¹]`** — a refinement descends it (`weakClass_le`) and a
merge fixes it (`weakClass_le_of_W`). -/
noncomputable def weakClassLoc (n : ℕ) : (W (□n)).Localization ⥤ (WeakOrder n)ᵒᵖ :=
  degLoc weakClass weakClass_le (W (□n)) weakClass_le_of_W

@[simp] theorem weakClassLoc_obj_Q (c : Ch (□n)) :
    (weakClassLoc n).obj ((W (□n)).Q.obj c) = op (weakClass c) := rfl

instance weakClassLoc_faithful (n : ℕ) : (weakClassLoc n).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance weakClassLoc_full (n : ℕ) : (weakClassLoc n).Full where
  map_surjective {X Y} h := by
    obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj _ X
    obtain ⟨c', rfl⟩ := Localization.Construction.exists_Q_obj _ Y
    exact ⟨(nonempty_loc_hom (leOfHom h.unop)).some, Subsingleton.elim _ _⟩

instance weakClassLoc_essSurj (n : ℕ) : (weakClassLoc n).EssSurj where
  mem_essImage σ :=
    ⟨(W (□n)).Q.obj (runAt (WeakOrder.perm σ.unop)).chain,
      ⟨eqToIso (by rw [weakClassLoc_obj_Q, weakClass_runAt]; rfl)⟩⟩

instance weakClassLoc_isEquivalence (n : ℕ) : (weakClassLoc n).IsEquivalence := { }

/-- **`Ch (□n)[W⁻¹]` is the right weak Bruhat order on `Perm (Fin n)`, read backwards** — as the
weak-order class itself, so it computes: `locCubeWeakOrder_obj_Q`. -/
noncomputable def locCubeWeakOrder (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ :=
  (weakClassLoc n).asEquivalence

@[simp] theorem locCubeWeakOrder_obj_Q (c : Ch (□n)) :
    (locCubeWeakOrder n).functor.obj ((W (□n)).Q.obj c) = op (weakClass c) := rfl

end ChainCat
