import CubeChains.Arrangements.SalElements

/-!
# Arrangements/COMSum — the direct sum of COMs and the splitting of `Sal`

The **direct sum** `L₁ ⊕ L₂ : COM (E₁ ⊕ E₂)` of two COMs (`COM.directSum`): a sign vector on the
disjoint union is a covector iff each of its two restrictions is.  Both COM axioms split
coordinatewise; the only cross-talk is in strong elimination, where eliminating in (say) the left
summand needs *some* covector of the right summand agreeing with `X ∘ Y` off the separator — for
which `comp` itself serves, by `COM.compClosed` (which holds for every COM, from face symmetry
alone).  So no oriented-matroid hypothesis is needed anywhere here.

Topes, faces and the Salvetti/Paris order all split as well, giving

> `salSumEquiv : Sal (L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`

(the categorical product; both sides are posets, hence thin).  This is the COM-side half of
`Sal (L₁ ⊕ L₂) ≌ Int(Lines(P ∨ Q))` — the other half is `linesWedgeEquiv` (`LinesWedge.lean`), and
they are combined in `SalWedge.lean`.

-/

open CategoryTheory

namespace CubeChains

namespace SignVec

variable {E₁ E₂ : Type*}

/-- Restriction of a sign vector on `E₁ ⊕ E₂` to the left summand. -/
def restrictL (Z : SignVec (E₁ ⊕ E₂)) : SignVec E₁ := fun e => Z (Sum.inl e)

/-- Restriction of a sign vector on `E₁ ⊕ E₂` to the right summand. -/
def restrictR (Z : SignVec (E₁ ⊕ E₂)) : SignVec E₂ := fun e => Z (Sum.inr e)

@[simp] theorem restrictL_elim (X : SignVec E₁) (Y : SignVec E₂) :
    restrictL (Sum.elim X Y) = X := rfl

@[simp] theorem restrictR_elim (X : SignVec E₁) (Y : SignVec E₂) :
    restrictR (Sum.elim X Y) = Y := rfl

/-- A sign vector on `E₁ ⊕ E₂` is the join of its two restrictions. -/
@[simp] theorem elim_restrict (Z : SignVec (E₁ ⊕ E₂)) :
    Sum.elim (restrictL Z) (restrictR Z) = Z := by
  funext e; cases e <;> rfl

@[simp] theorem restrictL_comp (X Y : SignVec (E₁ ⊕ E₂)) :
    restrictL (X ⊙ Y) = restrictL X ⊙ restrictL Y := rfl

@[simp] theorem restrictR_comp (X Y : SignVec (E₁ ⊕ E₂)) :
    restrictR (X ⊙ Y) = restrictR X ⊙ restrictR Y := rfl

@[simp] theorem restrictL_neg (Y : SignVec (E₁ ⊕ E₂)) :
    restrictL (-Y) = -(restrictL Y) := rfl

@[simp] theorem restrictR_neg (Y : SignVec (E₁ ⊕ E₂)) :
    restrictR (-Y) = -(restrictR Y) := rfl

@[simp] theorem restrictL_zero : restrictL (0 : SignVec (E₁ ⊕ E₂)) = 0 := rfl

@[simp] theorem restrictR_zero : restrictR (0 : SignVec (E₁ ⊕ E₂)) = 0 := rfl

theorem mem_sep_inl {X Y : SignVec (E₁ ⊕ E₂)} {e : E₁} :
    Sum.inl e ∈ sep X Y ↔ e ∈ sep (restrictL X) (restrictL Y) := Iff.rfl

theorem mem_sep_inr {X Y : SignVec (E₁ ⊕ E₂)} {e : E₂} :
    Sum.inr e ∈ sep X Y ↔ e ∈ sep (restrictR X) (restrictR Y) := Iff.rfl

/-- The face order on `E₁ ⊕ E₂` is the conjunction of the two restricted face orders. -/
theorem faceLE_sum_iff {X Y : SignVec (E₁ ⊕ E₂)} :
    X ⊑ Y ↔ restrictL X ⊑ restrictL Y ∧ restrictR X ⊑ restrictR Y :=
  ⟨fun h => ⟨fun e => h (Sum.inl e), fun e => h (Sum.inr e)⟩,
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
  covectors := {Z | restrictL Z ∈ L₁.covectors ∧ restrictR Z ∈ L₂.covectors}
  carrier_nonempty :=
    ⟨Sum.elim L₁.carrier_nonempty.choose L₂.carrier_nonempty.choose,
      L₁.carrier_nonempty.choose_spec, L₂.carrier_nonempty.choose_spec⟩
  faceSymm X hX Y hY :=
    ⟨L₁.faceSymm _ hX.1 _ hY.1, L₂.faceSymm _ hX.2 _ hY.2⟩
  strongElim X hX Y hY e he := by
    cases e with
    | inl a =>
        obtain ⟨Z, hZ, hZa, hZf⟩ := L₁.strongElim _ hX.1 _ hY.1 a (mem_sep_inl.mp he)
        refine ⟨Sum.elim Z (restrictR X ⊙ restrictR Y),
          ⟨hZ, compClosed L₂ hX.2 hY.2⟩, hZa, ?_⟩
        intro f hf
        cases f with
        | inl b => exact hZf b fun hb => hf (mem_sep_inl.mpr hb)
        | inr b => rfl
    | inr b =>
        obtain ⟨Z, hZ, hZb, hZf⟩ := L₂.strongElim _ hX.2 _ hY.2 b (mem_sep_inr.mp he)
        refine ⟨Sum.elim (restrictL X ⊙ restrictL Y) Z,
          ⟨compClosed L₁ hX.1 hY.1, hZ⟩, hZb, ?_⟩
        intro f hf
        cases f with
        | inl a => rfl
        | inr a => exact hZf a fun ha => hf (mem_sep_inr.mpr ha)

@[simp] theorem mem_directSum_covectors {L₁ : COM E₁} {L₂ : COM E₂} {Z : SignVec (E₁ ⊕ E₂)} :
    Z ∈ (L₁.directSum L₂).covectors ↔
      restrictL Z ∈ L₁.covectors ∧ restrictR Z ∈ L₂.covectors := Iff.rfl

/-- The direct sum of oriented matroids is an oriented matroid. -/
theorem directSum_isOM {L₁ : COM E₁} {L₂ : COM E₂} (h₁ : L₁.IsOM) (h₂ : L₂.IsOM) :
    (L₁.directSum L₂).IsOM := ⟨h₁, h₂⟩

/-! ## Topes of a direct sum -/

/-- **Topes split.**  A sign vector on `E₁ ⊕ E₂` is a tope of `L₁ ⊕ L₂` exactly when both of its
restrictions are topes.  (⟸) is maximality checked coordinatewise; (⟹) glues a competitor in one
summand to `T`'s own restriction in the other. -/
theorem isTope_directSum_iff {L₁ : COM E₁} {L₂ : COM E₂} {T : SignVec (E₁ ⊕ E₂)} :
    (L₁.directSum L₂).IsTope T ↔ L₁.IsTope (restrictL T) ∧ L₂.IsTope (restrictR T) := by
  constructor
  · rintro ⟨hT, hmax⟩
    refine ⟨⟨hT.1, fun X hX hface => ?_⟩, ⟨hT.2, fun Y hY hface => ?_⟩⟩
    · have hmem : Sum.elim X (restrictR T) ∈ (L₁.directSum L₂).covectors := ⟨hX, hT.2⟩
      have := hmax _ hmem (faceLE_sum_iff.mpr ⟨hface, faceLE_refl _⟩)
      exact congrArg restrictL this
    · have hmem : Sum.elim (restrictL T) Y ∈ (L₁.directSum L₂).covectors := ⟨hT.1, hY⟩
      have := hmax _ hmem (faceLE_sum_iff.mpr ⟨faceLE_refl _, hface⟩)
      exact congrArg restrictR this
  · rintro ⟨hL, hR⟩
    refine ⟨⟨hL.1, hR.1⟩, fun Z hZ hface => ?_⟩
    have h := faceLE_sum_iff.mp hface
    rw [← elim_restrict Z, hL.2 _ hZ.1 h.1, hR.2 _ hZ.2 h.2, elim_restrict]

/-! ## The Salvetti poset of a direct sum -/

variable (L₁ : COM E₁) (L₂ : COM E₂)

/-- A Salvetti cell of `L₁ ⊕ L₂` restricted to the left summand. -/
def SalCell.restrictL (a : Sal (L₁.directSum L₂)) : Sal L₁ :=
  ⟨(SignVec.restrictL a.face, SignVec.restrictL a.tope), a.2.1.1,
    (isTope_directSum_iff.mp a.2.2.1).1, (faceLE_sum_iff.mp a.2.2.2).1⟩

/-- A Salvetti cell of `L₁ ⊕ L₂` restricted to the right summand. -/
def SalCell.restrictR (a : Sal (L₁.directSum L₂)) : Sal L₂ :=
  ⟨(SignVec.restrictR a.face, SignVec.restrictR a.tope), a.2.1.2,
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
    exact ⟨⟨(faceLE_sum_iff.mp hface).1, congrArg SignVec.restrictL htope⟩,
      ⟨(faceLE_sum_iff.mp hface).2, congrArg SignVec.restrictR htope⟩⟩
  · rintro ⟨⟨hfL, htL⟩, ⟨hfR, htR⟩⟩
    refine ⟨faceLE_sum_iff.mpr ⟨hfL, hfR⟩, ?_⟩
    funext e
    cases e with
    | inl x => exact congrFun htL x
    | inr x => exact congrFun htR x

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

/-- **`Sal` turns direct sums into products.**  Cells, topes and the Salvetti order all split
coordinatewise, so restriction to the two summands is an equivalence (indeed an isomorphism of
posets).  Matches the wedge splitting `linesWedgeEquiv` of the chamber presheaf. -/
noncomputable def salSumEquiv : Sal (L₁.directSum L₂) ≌ Sal L₁ × Sal L₂ :=
  haveI : (salSumFunctor L₁ L₂).IsEquivalence :=
    { faithful := ⟨fun _ => Subsingleton.elim _ _⟩
      full := ⟨fun {_ _} k =>
        ⟨(salCell_le_iff L₁ L₂ |>.mpr ⟨leOfHom k.1, leOfHom k.2⟩).hom, Subsingleton.elim _ _⟩⟩
      essSurj := ⟨fun uv => ⟨SalCell.elim L₁ L₂ uv.1 uv.2, ⟨eqToIso rfl⟩⟩⟩ }
  (salSumFunctor L₁ L₂).asEquivalence

end COM

end CubeChains
