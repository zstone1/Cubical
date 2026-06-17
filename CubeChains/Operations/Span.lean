import CubeChains.Operations.Homotopical

/-!
# Operations presented by spans

An **operation** `X ⤳ Y` is presented by a *span* `X ⟵ apex ⟶ Y` whose two legs are
both `Φ`-homotopical (weak equivalences).  This is the carrier the user asked for:
the conceptual transformation `X → Y` need *not* be a morphism of `C` at all (it may
be "badly non-cubical" — e.g. an edge-swap, which is not a precubical map in the
symmetry-free model), yet the span still induces a canonical equivalence
`Φ X ≌ Φ Y` (design condition **(1)**).

Spans are the length-2 case of the zigzags that `W⁻¹·C` (the localization at
`Homotopical Φ`) is built from.  **DPO rewrites** will, in a later layer, *produce*
such spans: a rule `L ← I → R` at a match yields the bottom span `K ← D → FK`
(pushout-complement leg, then pushout leg); the content needed to know those legs
are homotopical is a *base-change stability* theorem for `Homotopical Φ`, which is
deferred (it is the dual of the cobase-change/"properness" property and belongs with
the obstruction discussed in `Conjectures.lean`).  Because that theorem is exactly
what span *composition* needs (composing along a pullback), span composition is
deferred too — but operations already compose at the level of the induced
*equivalences* (`Equivalence.trans`), which needs nothing extra.
-/

open CategoryTheory

namespace Operations

variable {C : Type*} [Category C] (Φ : C ⥤ Cat.{v, u})

/-- An operation `X ⤳ Y`: a span `X ⟵ apex ⟶ Y` with both legs `Φ`-homotopical. -/
structure Span (X Y : C) where
  /-- The apex of the span. -/
  apex : C
  /-- The leg into the source. -/
  left : apex ⟶ X
  /-- The leg into the target. -/
  right : apex ⟶ Y
  /-- The left leg is a weak equivalence. -/
  left_homotopical : Homotopical Φ left
  /-- The right leg is a weak equivalence. -/
  right_homotopical : Homotopical Φ right

namespace Span

variable {Φ}

/-- A single homotopical map `f : X ⟶ Y` as a span (apex `X`, identity left leg).
Embeds the simpler "operation = a map of `C`" design into the span carrier; e.g.
dead-code elimination as the accessible-part inclusion arises this way. -/
def ofHom {X Y : C} (f : X ⟶ Y) (hf : Homotopical Φ f) : Span Φ X Y where
  apex := X
  left := 𝟙 X
  right := f
  left_homotopical := (Homotopical Φ).id_mem X
  right_homotopical := hf

/-- The identity operation. -/
def id (X : C) : Span Φ X X := ofHom (𝟙 X) ((Homotopical Φ).id_mem X)

/-- Any isomorphism (relabeling/ambient isotopy) as an operation. -/
def ofIso {X Y : C} (f : X ⟶ Y) [IsIso f] : Span Φ X Y :=
  ofHom f (homotopical_of_isIso Φ f)

/-- Operations are reversible at the span level: swap the legs. -/
def symm {X Y : C} (s : Span Φ X Y) : Span Φ Y X where
  apex := s.apex
  left := s.right
  right := s.left
  left_homotopical := s.right_homotopical
  right_homotopical := s.left_homotopical

/-- **Condition (1) for a span.**  The equivalence of categories `Φ X ≌ Φ Y` induced by
an operation: invert the left leg's equivalence, then compose with the right leg's.
This is the sense in which a chain `p` in `Φ X` and its image in `Φ Y` are "the same
up to equivalence", so homotopies of d-paths transport across the operation. -/
noncomputable def equivalence {X Y : C} (s : Span Φ X Y) : Φ.obj X ≌ Φ.obj Y :=
  (Homotopical.equivalence s.left_homotopical).symm.trans
    (Homotopical.equivalence s.right_homotopical)

@[simp] theorem symm_equivalence_functor {X Y : C} (s : Span Φ X Y) :
    (s.symm.equivalence).functor = s.equivalence.inverse := rfl

end Span
end Operations
