import CubeChains.Concurrency.Merge.CubeThin

/-!
# Concurrency/Merge/CubeWeakEquiv — `Ch (□n)[W⁻¹]` *is* the weak order

`locCubeWeakOrder`: the localized cube slice is equivalent to the right weak Bruhat order on
`Perm (Fin n)`, read backwards.  Each half is a theorem of its own — `locCube_isThin` makes
`weakLoc` faithful, `exists_word` makes it full, and `runAt` realises every class on the nose.

Concretely, a morphism between two chains exists exactly when their crossing permutations compare
(`nonempty_loc_hom_iff`), and then it is unique.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-- **A descent of the weak order is realised** by the word `exists_word` gives, conjugated back
off the class runs. -/
theorem nonempty_loc_hom {c c' : Ch (□n)} (h : weakClass c' ≤ weakClass c) :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') := by
  obtain ⟨g, -⟩ := exists_word (permLen (cross c)) (cross c) (cross c') le_rfl h
  exact ⟨(classRunIso (rfl : cross c = cross c)).inv ≫ g
    ≫ (classRunIso (rfl : cross c' = cross c')).hom⟩

instance weakLoc_full (n : ℕ) : (weakLoc n).Full where
  map_surjective {X Y} h := by
    obtain ⟨c, rfl⟩ := exists_loc_obj X
    obtain ⟨c', rfl⟩ := exists_loc_obj Y
    obtain ⟨g⟩ := nonempty_loc_hom (leOfHom h.unop)
    exact ⟨g, Subsingleton.elim _ _⟩

/-- The run at `σ` has weak-order class `σ` on the nose. -/
instance weakLoc_essSurj (n : ℕ) : (weakLoc n).EssSurj where
  mem_essImage x :=
    ⟨(W (□n)).Q.obj (runAt (WeakOrder.perm x.unop)).chain,
      ⟨eqToIso (congrArg Opposite.op (weakClass_runAt _))⟩⟩

/-- Faithfulness is `locCube_isThin`: a thin source leaves nothing to separate. -/
instance weakLoc_isEquivalence (n : ℕ) : (weakLoc n).IsEquivalence := { }

/-- **`Ch (□n)[W⁻¹]` is the right weak Bruhat order on `Perm (Fin n)`, read backwards.** -/
noncomputable def locCubeWeakOrder (n : ℕ) : (W (□n)).Localization ≌ (WeakOrder n)ᵒᵖ :=
  (weakLoc n).asEquivalence

/-- **The hom-sets are the order relation**: `weakClass_le_of_loc_hom` one way, the word the
other. -/
theorem nonempty_loc_hom_iff {c c' : Ch (□n)} :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') ↔ weakClass c' ≤ weakClass c :=
  ⟨fun ⟨g⟩ => weakClass_le_of_loc_hom g, nonempty_loc_hom⟩

end ChainCat
