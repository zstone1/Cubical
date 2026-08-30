import CubeChains.Machinery.Arrangement.SalElements

/-!
# Machinery/Arrangement/COMSum — the direct sum of COMs and the splitting of `Sal`

The **direct sum** `L₁ ⊕ L₂ : COM (E₁ ⊕ E₂)` of two COMs (`COM.directSum`): a sign vector on the
disjoint union is a covector iff each of its two reindexings along the injections is.  Both COM
axioms split coordinatewise; the only cross-talk is in strong elimination, where eliminating in
(say) the left summand needs *some* covector of the right summand agreeing with `X ∘ Y` off the
separator — for which `comp` itself serves, by `COM.compClosed`.

Topes, faces and the Salvetti/Paris order all split as well, giving

> `salSumEquiv : Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`

(the categorical product; both sides are posets, hence thin).  This is the COM-side half of
`Sal (L₁ ⊕ L₂) ≌ Ch⋆ (P ∨ Q)`; the wedge splitting of `Lines` is the other half.

-/

open CategoryTheory

namespace CubeChains

namespace SignVec

variable {E₁ E₂ : Type*}

/-- A sign vector on `E₁ ⊕ E₂` is the join of its two restrictions. -/
@[simp] theorem elim_restrict (Z : SignVec (E₁ ⊕ E₂)) :
    Sum.elim (restrict Sum.inl Z) (restrict Sum.inr Z) = Z := by
  funext e; cases e <;> rfl

/-- **Extensionality on a sum:** sign vectors agreeing on both summands are equal. -/
theorem sum_ext {X Y : SignVec (E₁ ⊕ E₂)} (hl : restrict Sum.inl X = restrict Sum.inl Y)
    (hr : restrict Sum.inr X = restrict Sum.inr Y) : X = Y := by
  rw [← elim_restrict X, hl, hr, elim_restrict]

/-- The face order on `E₁ ⊕ E₂` is the conjunction of the two restricted face orders. -/
theorem faceLE_sum_iff {X Y : SignVec (E₁ ⊕ E₂)} :
    X ⊑ Y ↔ restrict Sum.inl X ⊑ restrict Sum.inl Y ∧ restrict Sum.inr X ⊑ restrict Sum.inr Y :=
  ⟨fun h => ⟨faceLE_restrict _ h, faceLE_restrict _ h⟩,
   fun h e => by cases e with
     | inl a => exact h.1 a
     | inr b => exact h.2 b⟩

end SignVec

namespace COM

open SignVec

variable {E₁ E₂ : Type*}

/-! ## The direct sum -/

/-- **The direct sum of two COMs.**  On the ground set `E₁ ⊕ E₂`, a sign vector is a covector iff
each of its restrictions is a covector of the corresponding summand.  (Equivalently: the covectors
are the `Sum.elim X Y` for `X ∈ L₁`, `Y ∈ L₂`.) -/
def directSum (L₁ : COM E₁) (L₂ : COM E₂) : COM (E₁ ⊕ E₂) where
  covectors := {Z | restrict Sum.inl Z ∈ L₁.covectors ∧ restrict Sum.inr Z ∈ L₂.covectors}
  carrier_nonempty :=
    ⟨Sum.elim L₁.carrier_nonempty.choose L₂.carrier_nonempty.choose,
      L₁.carrier_nonempty.choose_spec, L₂.carrier_nonempty.choose_spec⟩
  faceSymm X hX Y hY :=
    ⟨L₁.faceSymm _ hX.1 _ hY.1, L₂.faceSymm _ hX.2 _ hY.2⟩
  strongElim X hX Y hY e he := by
    cases e with
    | inl a =>
        obtain ⟨Z, hZ, hZa, hZf⟩ :=
          L₁.strongElim _ hX.1 _ hY.1 a ((mem_sep_restrict Sum.inl a).mp he)
        refine ⟨Sum.elim Z (restrict Sum.inr (X ⊙ Y)), ⟨hZ, compClosed L₂ hX.2 hY.2⟩, hZa, ?_⟩
        rintro (b | b) hg
        · exact hZf b fun hb => hg ((mem_sep_restrict Sum.inl b).mpr hb)
        · rfl
    | inr b =>
        obtain ⟨Z, hZ, hZb, hZf⟩ :=
          L₂.strongElim _ hX.2 _ hY.2 b ((mem_sep_restrict Sum.inr b).mp he)
        refine ⟨Sum.elim (restrict Sum.inl (X ⊙ Y)) Z, ⟨compClosed L₁ hX.1 hY.1, hZ⟩, hZb, ?_⟩
        rintro (a | a) hg
        · rfl
        · exact hZf a fun ha => hg ((mem_sep_restrict Sum.inr a).mpr ha)

@[simp] theorem mem_directSum_covectors {L₁ : COM E₁} {L₂ : COM E₂} {Z : SignVec (E₁ ⊕ E₂)} :
    Z ∈ (L₁.directSum L₂).covectors ↔
      restrict Sum.inl Z ∈ L₁.covectors ∧ restrict Sum.inr Z ∈ L₂.covectors := Iff.rfl

/-- The direct sum of oriented matroids is an oriented matroid. -/
theorem directSum_isOM {L₁ : COM E₁} {L₂ : COM E₂} (h₁ : L₁.IsOM) (h₂ : L₂.IsOM) :
    (L₁.directSum L₂).IsOM := ⟨h₁, h₂⟩

/-! ## Topes of a direct sum -/

/-- **Topes split.**  A sign vector on `E₁ ⊕ E₂` is a tope of `L₁ ⊕ L₂` exactly when both of its
restrictions are topes.  (⟸) is maximality checked coordinatewise; (⟹) glues a competitor in one
summand to `T`'s own restriction in the other. -/
theorem isTope_directSum_iff {L₁ : COM E₁} {L₂ : COM E₂} {T : SignVec (E₁ ⊕ E₂)} :
    (L₁.directSum L₂).IsTope T ↔
      L₁.IsTope (restrict Sum.inl T) ∧ L₂.IsTope (restrict Sum.inr T) := by
  constructor
  · rintro ⟨hT, hmax⟩
    exact ⟨⟨hT.1, fun X hX hface => congrArg (restrict Sum.inl)
        (hmax (Sum.elim X (restrict Sum.inr T)) ⟨hX, hT.2⟩
          (faceLE_sum_iff.mpr ⟨hface, faceLE_refl _⟩))⟩,
      ⟨hT.2, fun Y hY hface => congrArg (restrict Sum.inr)
        (hmax (Sum.elim (restrict Sum.inl T) Y) ⟨hT.1, hY⟩
          (faceLE_sum_iff.mpr ⟨faceLE_refl _, hface⟩))⟩⟩
  · rintro ⟨hL, hR⟩
    refine ⟨⟨hL.1, hR.1⟩, fun Z hZ hface => ?_⟩
    have h := faceLE_sum_iff.mp hface
    exact sum_ext (hL.2 _ hZ.1 h.1) (hR.2 _ hZ.2 h.2)

/-! ## The Salvetti poset of a direct sum -/

variable (L₁ : COM E₁) (L₂ : COM E₂)

/-- A Salvetti cell of `L₁ ⊕ L₂` restricted to the left summand. -/
def SalCell.restrictL (a : Sal (L₁.directSum L₂)) : Sal L₁ :=
  ⟨(restrict Sum.inl a.face, restrict Sum.inl a.tope), a.2.1.1,
    (isTope_directSum_iff.mp a.2.2.1).1, (faceLE_sum_iff.mp a.2.2.2).1⟩

/-- A Salvetti cell of `L₁ ⊕ L₂` restricted to the right summand. -/
def SalCell.restrictR (a : Sal (L₁.directSum L₂)) : Sal L₂ :=
  ⟨(restrict Sum.inr a.face, restrict Sum.inr a.tope), a.2.1.2,
    (isTope_directSum_iff.mp a.2.2.1).2, (faceLE_sum_iff.mp a.2.2.2).2⟩

/-- Gluing a pair of Salvetti cells into a cell of the direct sum. -/
def SalCell.elim (u : Sal L₁) (v : Sal L₂) : Sal (L₁.directSum L₂) :=
  ⟨(Sum.elim u.face v.face, Sum.elim u.tope v.tope), ⟨u.2.1, v.2.1⟩,
    isTope_directSum_iff.mpr ⟨u.2.2.1, v.2.2.1⟩,
    faceLE_sum_iff.mpr ⟨u.2.2.2, v.2.2.2⟩⟩

/-- The Salvetti/Paris order on `Sal (L₁ ⊕ L₂)` is the coordinatewise one: both the face order and
the wall-crossing projection `T' = X' ∘ T` are computed summand by summand. -/
theorem salCell_le_iff {a b : Sal (L₁.directSum L₂)} :
    a ≤ b ↔ SalCell.restrictL L₁ L₂ a ≤ SalCell.restrictL L₁ L₂ b ∧
      SalCell.restrictR L₁ L₂ a ≤ SalCell.restrictR L₁ L₂ b := by
  constructor
  · rintro ⟨hface, htope⟩
    exact ⟨⟨(faceLE_sum_iff.mp hface).1, congrArg (restrict Sum.inl) htope⟩,
      ⟨(faceLE_sum_iff.mp hface).2, congrArg (restrict Sum.inr) htope⟩⟩
  · rintro ⟨⟨hfL, htL⟩, ⟨hfR, htR⟩⟩
    exact ⟨faceLE_sum_iff.mpr ⟨hfL, hfR⟩, sum_ext htL htR⟩

/-- The product of two Salvetti posets is thin (a product of thin categories). -/
instance salSum_prod_isThin : Quiver.IsThin (Sal L₁ × Sal L₂) := fun _ _ =>
  ⟨fun _ _ => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- **The splitting functor** `Sal (L₁ ⊕ L₂) ⥤ Sal L₁ × Sal L₂`, restricting a cell to each
summand.  Monotone by `salCell_le_iff`. -/
def salSumFunctor : Sal (L₁.directSum L₂) ⥤ Sal L₁ × Sal L₂ where
  obj a := (SalCell.restrictL L₁ L₂ a, SalCell.restrictR L₁ L₂ a)
  map h := ((salCell_le_iff L₁ L₂ |>.mp (leOfHom h)).1.hom,
            (salCell_le_iff L₁ L₂ |>.mp (leOfHom h)).2.hom)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The gluing functor** `Sal L₁ × Sal L₂ ⥤ Sal (L₁ ⊕ L₂)`.  Written out rather than inverted
through `essSurj`, which would recover it by `Classical.choice`. -/
def salSumInverse : Sal L₁ × Sal L₂ ⥤ Sal (L₁.directSum L₂) where
  obj uv := SalCell.elim L₁ L₂ uv.1 uv.2
  map k := homOfLE ((salCell_le_iff L₁ L₂).mpr ⟨leOfHom k.1, leOfHom k.2⟩)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **`Sal` turns direct sums into products.**  Cells, topes and the Salvetti order all split
coordinatewise, and both round trips are the identity on the nose. -/
def salSumEquiv : Sal (L₁.directSum L₂) ≌ Sal L₁ × Sal L₂ where
  functor := salSumFunctor L₁ L₂
  inverse := salSumInverse L₁ L₂
  unitIso := NatIso.ofComponents (fun a => eqToIso (Subtype.ext (by
      simp [salSumInverse, salSumFunctor, SalCell.elim, SalCell.restrictL, SalCell.restrictR,
        SalCell.face, SalCell.tope])))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => eqToIso rfl) (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end COM

end CubeChains
