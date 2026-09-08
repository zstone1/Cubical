import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Concurrency.Merge.CubeSpanning
import CubeChains.Concurrency.Merge.CubeFaces

/-!
# Concurrency/Merge/CubeWeakEquiv — `Ch (□n)[W⁻¹]` *is* the weak order

The comparison **is** the weak-order class (`weakClassLoc`, a `degLoc`), so it computes on a
`Q`-image: full by `nonempty_loc_hom`, essentially surjective because every permutation is a run
(`weakClass_runAt`), faithful because `Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`).
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

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
