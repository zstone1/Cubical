import CubeChains.Concurrency.Presentation.SliceExchange

/-!
# Concurrency/Merge/CubeWeakEquiv — `Ch (□n)[W⁻¹]` *is* the weak order

The comparison **is** the weak-order class (`weakClassLoc`, a `degLoc`), so it computes on a
`Q`-image: full by `nonempty_loc_hom`, essentially surjective because every permutation is a run
(`weakClass_wordRun`), faithful because `Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`).
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

/-! ## …and its inverse, the run of a class

`Functor.inv` is a choice, so the equivalence is built from a second *named* functor rather than
from essential surjectivity: a class is sent to its own run's chain. -/

/-- **The run of a weak-order class, in the localization.** -/
noncomputable def runClassLoc (n : ℕ) : (WeakOrder n)ᵒᵖ ⥤ (W (□n)).Localization where
  obj x := (W (□n)).Q.obj (wordRun (WeakOrder.perm x.unop)).chain
  map {_ _} h := (nonempty_loc_hom (by
    rw [weakClass_wordRun, weakClass_wordRun]
    exact leOfHom h.unop)).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem runClassLoc_obj (x : (WeakOrder n)ᵒᵖ) :
    (runClassLoc n).obj x = (W (□n)).Q.obj (wordRun (WeakOrder.perm x.unop)).chain := rfl

/-- **Every chain is isomorphic to its own class's run**, in the localization — `classRunIso` at
the chain's own crossing. -/
theorem nonempty_iso_runClassLoc (X : (W (□n)).Localization) :
    Nonempty (X ≅ (runClassLoc n).obj ((weakClassLoc n).obj X)) := by
  obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj _ X
  exact ⟨(classRunIso (rfl : cross c = cross c)).symm⟩

/-- **`Ch (□n)[W⁻¹]` is the right weak Bruhat order on `Perm (Fin n)`, read backwards** — the
weak-order class one way, the class's run the other, so both directions compute
(`locCubeWeakOrder_obj_Q`, `locCubeWeakOrder_inverse_obj`). -/
noncomputable def locCubeWeakOrder (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ :=
  Equivalence.ofThinInverse (weakClassLoc n) (runClassLoc n)
    (fun X => (nonempty_iso_runClassLoc X).some)
    (fun x => eqToIso (by rw [runClassLoc_obj, weakClassLoc_obj_Q, weakClass_wordRun]; rfl))

@[simp] theorem locCubeWeakOrder_obj_Q (c : Ch (□n)) :
    (locCubeWeakOrder n).functor.obj ((W (□n)).Q.obj c) = op (weakClass c) := rfl

@[simp] theorem locCubeWeakOrder_inverse_obj (x : (WeakOrder n)ᵒᵖ) :
    (locCubeWeakOrder n).inverse.obj x
      = (W (□n)).Q.obj (wordRun (WeakOrder.perm x.unop)).chain := rfl

end ChainCat
