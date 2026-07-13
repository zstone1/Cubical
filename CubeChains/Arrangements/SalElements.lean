import CubeChains.Arrangements.Sal
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence

/-!
# Arrangements/SalElements — the Salvetti poset `Sal L` is a category of elements

For a COM `L` the Salvetti face poset `Sal L` (`Arrangements/Sal.lean`) is *presented* as the
category of elements of a presheaf on its faces.  Concretely we build a functor

> `salFunctor L : Face L ⥤ Type`,  `X ↦ { T // IsTope T ∧ X ⊑ T }`

sending a face `X` to the set of topes above it, with restriction `X ≤ X'  ↦  (T ↦ X' ⊙ T)`
(the wall-crossing projection), and prove

> `Sal L  ≌  (salFunctor L).Elements`.

This is the abstract half of the comparison `Sal (braidCOM n) ≌ Int(Lines(□ⁿ))`: both sides are
categories of elements, so we compare the *bases* (faces vs. refinement cells) and the
*presheaves* separately.

The functor `salFunctor` needs closure of the covectors under composition (`comp`).  This is
`compClosed`, a theorem for *every* COM — and, pleasantly, it needs only **face symmetry**:
`X ∘ Y = X ∘ (−(X ∘ (−Y)))`, so two applications of (FS) suffice and (SE) is never used.  It is
therefore applied silently wherever needed; `salFunctor L` takes no composition-closure hypothesis.

-/

open CategoryTheory

namespace CubeChains

namespace SignVec
variable {E : Type*}

/-- Pointwise unfolding of composition. -/
theorem comp_apply (X Y : SignVec E) (e : E) :
    (X ⊙ Y) e = if X e = 0 then Y e else X e := rfl

/-- A face is below any composition on its left: `X ⊑ X ∘ Y`. -/
theorem faceLE_comp_left (X Y : SignVec E) : X ⊑ X ⊙ Y := by
  intro e
  by_cases h : X e = 0
  · exact Or.inl h
  · exact Or.inr (by rw [comp_apply, if_neg h])

/-- Composing on the left with the zero covector is the identity: `0 ∘ Z = Z`. -/
theorem comp_zero_left (Z : SignVec E) : (0 : SignVec E) ⊙ Z = Z := by
  funext e
  rw [comp_apply, Pi.zero_apply, if_pos rfl]

/-- **Composition is a double face symmetry:** `X ∘ Y = X ∘ (−(X ∘ (−Y)))`.  Where `X` vanishes
both sides read `Y`, the inner double negation cancelling; elsewhere both read `X`. -/
theorem comp_eq_comp_neg_comp_neg (X Y : SignVec E) : X ⊙ Y = X ⊙ (-(X ⊙ (-Y))) := by
  funext e
  simp only [comp_apply, Pi.neg_apply]
  by_cases h : X e = 0
  · rw [if_pos h, if_pos h, if_pos h]; exact (neg_neg _).symm
  · rw [if_neg h, if_neg h]

end SignVec

namespace COM
variable {E : Type*}

open SignVec

/-- **Every COM has composition-closed covectors** (Bandelt–Chepoi–Knauer).  Only face symmetry
is needed: `X ∘ Y = X ∘ (−(X ∘ (−Y)))` exhibits `X ∘ Y` as two nested applications of (FS).  This
was formerly carried as a hypothesis `CompClosed L`; it is a theorem, so nothing downstream needs
to assume it. -/
theorem compClosed (L : COM E) {X : SignVec E} (hX : X ∈ L.covectors) {Y : SignVec E}
    (hY : Y ∈ L.covectors) : X ⊙ Y ∈ L.covectors :=
  (comp_eq_comp_neg_comp_neg X Y) ▸ L.faceSymm X hX _ (L.faceSymm X hX Y hY)

/-- In an oriented matroid the covectors are closed under negation: `Y ∈ L ⟹ −Y ∈ L`. -/
theorem neg_mem_of_isOM {L : COM E} (h : L.IsOM) :
    ∀ Y ∈ L.covectors, -Y ∈ L.covectors := by
  intro Y hY
  have hmem := L.faceSymm 0 h Y hY
  rwa [comp_zero_left] at hmem

/-- A tope has the smallest zero set among all covectors: `zeroSet T ⊆ zeroSet X`. -/
theorem zeroSet_isTope_subset {L : COM E} {T X : SignVec E}
    (hT : L.IsTope T) (hX : X ∈ L.covectors) : zeroSet T ⊆ zeroSet X := by
  intro e he
  have hTe : T e = 0 := he
  have heq : T ⊙ (-X) = T :=
    hT.2 _ (L.faceSymm T hT.1 X hX) (faceLE_comp_left T (-X))
  have h1 : (T ⊙ (-X)) e = 0 := by rw [heq]; exact hTe
  rw [comp_apply, if_pos hTe, Pi.neg_apply] at h1
  exact SignType.neg_eq_zero_iff.mp h1

/-- Composing a covector into a tope again yields a tope: `X ∈ L`, `T` a tope ⟹ `X ∘ T` a tope. -/
theorem isTope_comp {L : COM E} {X T : SignVec E}
    (hX : X ∈ L.covectors) (hT : L.IsTope T) : L.IsTope (X ⊙ T) := by
  refine ⟨compClosed L hX hT.1, ?_⟩
  intro Z hZ hZface
  funext e
  by_cases hTe : T e = 0
  · have hXe : X e = 0 := zeroSet_isTope_subset hT hX hTe
    have hZe : Z e = 0 := zeroSet_isTope_subset hT hZ hTe
    rw [hZe, comp_apply, if_pos hXe, hTe]
  · have hne : (X ⊙ T) e ≠ 0 := by
      rw [comp_apply]
      by_cases hXe : X e = 0
      · rw [if_pos hXe]; exact hTe
      · rw [if_neg hXe]; exact hXe
    rcases hZface e with h | h
    · exact absurd h hne
    · exact h.symm

/-- The **faces** of `L`: its covectors, under the face (conformal) order `faceLE`. -/
def Face (L : COM E) : Type _ := {X : SignVec E // X ∈ L.covectors}

/-- The face order makes `Face L` a partial order (a thin category). -/
instance instPartialOrderFace (L : COM E) : PartialOrder (Face L) where
  le X Y := X.1 ⊑ Y.1
  le_refl X := faceLE_refl X.1
  le_trans _ _ _ hXY hYZ := faceLE_trans hXY hYZ
  le_antisymm _ _ hXY hYX := Subtype.ext (faceLE_antisymm hXY hYX)

/-- **The Salvetti presheaf** of `L`: a face `X` is sent to the set of topes above it, and a
refinement `X ≤ X'` restricts a tope `T` to its wall-crossing projection `X' ⊙ T`. -/
def salFunctor (L : COM E) : Face L ⥤ Type _ where
  obj X := {T : SignVec E // L.IsTope T ∧ X.1 ⊑ T}
  map {_ X'} _ := TypeCat.ofHom fun T =>
    (⟨X'.1 ⊙ T.1, isTope_comp X'.2 T.2.1, faceLE_comp_left X'.1 T.1⟩ :
      {T : SignVec E // L.IsTope T ∧ X'.1 ⊑ T})
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro T
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact Subtype.ext (comp_eq_right_of_faceLE T.2.2)
  map_comp _ g := by
    apply ConcreteCategory.hom_ext
    intro T
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact Subtype.ext (comp_comp_of_faceLE (leOfHom g)).symm

/-- The action of `salFunctor` on elements: `(salFunctor L).map h` sends a tope `T` above `X`
to its wall-crossing projection `X' ⊙ T` above the finer face `X'`. -/
theorem salFunctor_map_apply (L : COM E) {X X' : Face L} (h : X ⟶ X')
    (T : (salFunctor L).obj X) :
    (salFunctor L).map h T =
      (⟨X'.1 ⊙ T.1, isTope_comp X'.2 T.2.1, faceLE_comp_left X'.1 T.1⟩ :
        {T : SignVec E // L.IsTope T ∧ X'.1 ⊑ T}) := rfl

/-- The category of elements of the Salvetti presheaf is thin (its base `Face L` is a poset). -/
instance salFunctor_elements_isThin (L : COM E) :
    Quiver.IsThin (salFunctor L).Elements := fun _ _ =>
  ⟨fun f g => Subtype.ext (Subsingleton.elim f.1 g.1)⟩

/-- The comparison functor `Sal L ⥤ (salFunctor L).Elements`: a Salvetti cell `(X, T)` is exactly
an element `T` of the fibre `salFunctor L` at `X`.  The Salvetti/Paris order on cells is precisely
a morphism of the category of elements. -/
def salToElements (L : COM E) :
    Sal L ⥤ (salFunctor L).Elements where
  obj a := ⟨⟨a.face, a.2.1⟩, ⟨a.tope, a.2.2.1, a.2.2.2⟩⟩
  map h := ⟨homOfLE (leOfHom h).1, by
    rw [salFunctor_map_apply]
    exact Subtype.ext (leOfHom h).2.symm⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **`Sal L` is a category of elements**: it is equivalent to `(salFunctor L).Elements`. -/
noncomputable def salElementsEquiv (L : COM E) :
    Sal L ≌ (salFunctor L).Elements :=
  haveI : (salToElements L).IsEquivalence :=
    { faithful := ⟨fun _ => Subsingleton.elim _ _⟩
      full := ⟨fun {a b} k => by
        refine ⟨homOfLE ⟨leOfHom k.1, ?_⟩, Subsingleton.elim _ _⟩
        have hk := k.2
        rw [salFunctor_map_apply] at hk
        exact (Subtype.ext_iff.mp hk).symm⟩
      essSurj := ⟨fun Z =>
        ⟨⟨(Z.1.1, Z.2.1), Z.1.2, Z.2.2.1, Z.2.2.2⟩, ⟨eqToIso rfl⟩⟩⟩ }
  (salToElements L).asEquivalence

end COM

end CubeChains
