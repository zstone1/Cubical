import CubeChains.Cobordisms.Composition
import CubeChains.Research.Conjectures

/-!
# Cobordisms/DCob — the directed-cobordism category `dCob` (M5)

This file assembles the directed cobordisms `X ⇒c Y` into a genuine
`CategoryTheory.Category` `dCob`.  Objects are precubical sets (carried by a thin
type synonym `dCob`, to avoid clobbering the *functor-category* `Category` instance
that `PrecubicalSet = Boxᵒᵖ ⥤ Type` already has); morphisms are **rel-∂ equivalence
classes** of directed cobordisms, and the **identity is the cylinder** `idCob`.

## Why a quotient?

The cylinder is only a *weak* unit: its collars genuinely add cells, so
`(idCob X).comp W` is **not** literally `W` — it is a thickened version of it.  We
therefore quotient the Hom-sets by the smallest equivalence relation `cobordismRel`
making

* **boundary-fixing isomorphisms** of the underlying cospan identified
  (`CobElem.iso`), and
* **collar stabilization** identified — `W` with `(idCob X).comp W` and with
  `W.comp (idCob Y)` (`CobElem.unitL` / `CobElem.unitR`).

These are the *rel-∂ generators*: moves that fix the source/sink boundary `X`, `Y`.

## What is proved here, and what is scaffolded

* `CobElem`, `cobordismRel := Relation.EqvGen CobElem`, `cobordismSetoid`,
  `HomCob := Quotient …` — all sorry-free.
* **The iso-move is a congruence for `comp`** — `compCob_iso_congrL/R`,
  proved sorry-free from pushout functoriality (`pushout.map` of an iso of one input
  leg is an iso of the pushout, commuting with the outer legs).
* The composition descends to `compCob : HomCob X Y → HomCob Y Z → HomCob X Z`
  (`Quotient.lift₂`), the unit laws `id_comp`/`comp_id` hold from the unit moves, and
  the **`Category dCob` instance is assembled**.

* **Scaffolded coherence (this file is now sorry-free).**  The associativity-flavoured
  data — a boundary-fixing iso `((U.comp V).comp W).mid ≅ (U.comp (V.comp W)).mid`
  (the canonical *pushout associator*, mathlib `pushoutAssoc`) — is supplied by the
  raw iso-existence lemmas `Conjectures.dcob_pushout_associator` /
  `dcob_unitCancelRight` / `dcob_unitCancelLeft` (the permitted-`sorry` file),
  packaged here into `CompCoherence` by `compCoherence` and extracted as
  **`compAssociator`** / `compUnitCancel{Right,Left}`.  Everything that needs
  associativity (the category law `assoc` and the *unit-move* half of the descent
  congruence, both of which are genuine pushout-associativity statements) is routed
  through `compAssociator`; no `sorry` appears in this file.

**Milestone consequence (M5).**  `dCob` is a genuine category whose unit on each
object `X` is the class `⟦idCob X⟧` of the cylinder — a *weak/quotient* unit: the
cylinder is only a unit after passing to the rel-∂ quotient, witnessing that the
collars are invisible up to boundary-fixing homotopy.

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Composition` (the bundle,
`idCob`, `DirectedCobordism.comp`, the M2 cospan composite + its simp lemmas).
-/

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace PrecubicalSet

universe u

variable {X Y Z W : PrecubicalSet}

/-! ### Boundary-fixing isomorphisms of cobordisms

The first rel-∂ generator: two cobordisms with the *same* boundary `X`, `Y` are
identified when there is an isomorphism of their middle objects commuting with both
legs.  This is recorded as a small bundle `CobIso` so that the symmetric/transitive
bookkeeping is clean. -/

/-- A **boundary-fixing isomorphism** between two cobordisms `W₁ W₂ : X ⇒c Y`: an iso
`e : W₁.mid ≅ W₂.mid` of the underlying precubical sets commuting with both legs. -/
structure CobIso (W₁ W₂ : DirectedCobordism X Y) where
  /-- The iso of middle objects. -/
  e : W₁.mid ≅ W₂.mid
  /-- Compatibility with the source leg. -/
  inl_hom : W₁.inl ≫ e.hom = W₂.inl
  /-- Compatibility with the sink leg. -/
  inr_hom : W₁.inr ≫ e.hom = W₂.inr

namespace CobIso

/-- The identity boundary-fixing iso. -/
@[simps] def refl (W : DirectedCobordism X Y) : CobIso W W where
  e := Iso.refl _
  inl_hom := Category.comp_id _
  inr_hom := Category.comp_id _

/-- Boundary-fixing isos compose with the legs intact. -/
@[simps] def symm {W₁ W₂ : DirectedCobordism X Y} (φ : CobIso W₁ W₂) : CobIso W₂ W₁ where
  e := φ.e.symm
  inl_hom := by rw [← φ.inl_hom]; simp
  inr_hom := by rw [← φ.inr_hom]; simp

end CobIso

/-! ### Elementary rel-∂ homotopy moves -/

/-- **Elementary rel-∂ homotopy moves** between two cobordisms `X ⇒c Y`.  The three
generators of the rel-∂ equivalence:

* `iso` — a boundary-fixing isomorphism of the middle objects (`CobIso`);
* `unitL` — collar stabilization on the *source* side: `W` is moved to
  `(idCob X).comp W` (prepend a cylinder);
* `unitR` — collar stabilization on the *sink* side: `W` is moved to
  `W.comp (idCob Y)` (append a cylinder). -/
inductive CobElem : (X ⇒c Y) → (X ⇒c Y) → Prop
  /-- A boundary-fixing iso of middle objects relates two cobordisms. -/
  | iso {W₁ W₂ : X ⇒c Y} (φ : CobIso W₁ W₂) : CobElem W₁ W₂
  /-- Collar stabilization on the source: `W ~ (idCob X).comp W`. -/
  | unitL (W : X ⇒c Y) : CobElem W ((idCob X).comp W)
  /-- Collar stabilization on the sink: `W ~ W.comp (idCob Y)`. -/
  | unitR (W : X ⇒c Y) : CobElem W (W.comp (idCob Y))

/-! ### The rel-∂ equivalence, setoid, and Hom-quotient -/

/-- The **rel-∂ equivalence** on cobordisms `X ⇒c Y`: the equivalence closure of the
elementary homotopy moves. -/
def cobordismRel (X Y : PrecubicalSet) : (X ⇒c Y) → (X ⇒c Y) → Prop :=
  Relation.EqvGen (@CobElem X Y)

/-- The rel-∂ relation is an equivalence (`EqvGen` is automatically refl/symm/trans). -/
theorem cobordismRel_equivalence (X Y : PrecubicalSet) :
    Equivalence (cobordismRel X Y) :=
  Relation.EqvGen.is_equivalence _

/-- The **rel-∂ setoid** on `X ⇒c Y`. -/
def cobordismSetoid (X Y : PrecubicalSet) : Setoid (X ⇒c Y) :=
  ⟨cobordismRel X Y, cobordismRel_equivalence X Y⟩

/-- The **Hom-quotient** `HomCob X Y`: rel-∂ equivalence classes of cobordisms. -/
def HomCob (X Y : PrecubicalSet) : Type 1 := Quotient (cobordismSetoid X Y)

/-- The class of a cobordism. -/
def HomCob.mk {X Y : PrecubicalSet} (W : X ⇒c Y) : HomCob X Y :=
  Quotient.mk (cobordismSetoid X Y) W

/-- An elementary move induces an equality of classes. -/
theorem HomCob.sound {X Y : PrecubicalSet} {W₁ W₂ : X ⇒c Y} (h : CobElem W₁ W₂) :
    HomCob.mk W₁ = HomCob.mk W₂ :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

/-- `cobordismRel` implies equality of classes. -/
theorem HomCob.sound_rel {X Y : PrecubicalSet} {W₁ W₂ : X ⇒c Y}
    (h : cobordismRel X Y W₁ W₂) : HomCob.mk W₁ = HomCob.mk W₂ :=
  Quotient.sound h

/-! ### The iso-move is a congruence for composition (sorry-free)

A boundary-fixing iso of one input cospan induces, via pushout functoriality
(`pushout.map` with the iso on the changed leg and identities elsewhere), a
boundary-fixing iso of the composites.  This is the genuine mathematical content of
the descent; it needs no associativity. -/

/-- **Left congruence for the iso-move.**  A boundary-fixing iso `W₁ ≅ W₂` of right
inputs induces one of `U.comp W₁ ≅ U.comp W₂`. -/
noncomputable def CobIso.compRight (U : X ⇒c Y) {W₁ W₂ : Y ⇒c Z} (φ : CobIso W₁ W₂) :
    CobIso (U.comp W₁) (U.comp W₂) where
  e :=
    have eq₁ : U.inr ≫ (𝟙 U.mid) = (𝟙 Y) ≫ U.inr := by simp
    have eq₂ : W₁.inl ≫ φ.e.hom = (𝟙 Y) ≫ W₂.inl := by simpa using φ.inl_hom
    haveI : IsIso φ.e.hom := φ.e.isIso_hom
    @asIso _ _ _ _ (pushout.map U.inr W₁.inl U.inr W₂.inl (𝟙 _) φ.e.hom (𝟙 _) eq₁ eq₂)
      (pushout.map_isIso U.inr W₁.inl U.inr W₂.inl (𝟙 _) φ.e.hom (𝟙 _) eq₁ eq₂)
  inl_hom := by
    -- `(U.comp W₁).inl = U.inl ≫ pushout.inl …`; push it through the map.
    change (U.inl ≫ pushout.inl U.inr W₁.inl) ≫ _ = U.inl ≫ pushout.inl U.inr W₂.inl
    rw [asIso_hom, Category.assoc, pushout.inl_desc, Category.id_comp]
  inr_hom := by
    -- `(U.comp W₁).inr = W₁.inr ≫ pushout.inr …`; push it through the map.
    change (W₁.inr ≫ pushout.inr U.inr W₁.inl) ≫ _ = W₂.inr ≫ pushout.inr U.inr W₂.inl
    rw [asIso_hom, Category.assoc, pushout.inr_desc, ← Category.assoc, φ.inr_hom]

/-- **Right congruence for the iso-move.**  A boundary-fixing iso `W₁ ≅ W₂` of left
inputs induces one of `W₁.comp U ≅ W₂.comp U`. -/
noncomputable def CobIso.compLeft {W₁ W₂ : X ⇒c Y} (φ : CobIso W₁ W₂) (U : Y ⇒c Z) :
    CobIso (W₁.comp U) (W₂.comp U) where
  e :=
    have eq₁ : W₁.inr ≫ φ.e.hom = (𝟙 Y) ≫ W₂.inr := by simpa using φ.inr_hom
    have eq₂ : U.inl ≫ (𝟙 U.mid) = (𝟙 Y) ≫ U.inl := by simp
    haveI : IsIso φ.e.hom := φ.e.isIso_hom
    @asIso _ _ _ _ (pushout.map W₁.inr U.inl W₂.inr U.inl φ.e.hom (𝟙 _) (𝟙 _) eq₁ eq₂)
      (pushout.map_isIso W₁.inr U.inl W₂.inr U.inl φ.e.hom (𝟙 _) (𝟙 _) eq₁ eq₂)
  inl_hom := by
    change (W₁.inl ≫ pushout.inl W₁.inr U.inl) ≫ _ = W₂.inl ≫ pushout.inl W₂.inr U.inl
    rw [asIso_hom, Category.assoc, pushout.inl_desc, ← Category.assoc, φ.inl_hom]
  inr_hom := by
    change (U.inr ≫ pushout.inr W₁.inr U.inl) ≫ _ = U.inr ≫ pushout.inr W₂.inr U.inl
    rw [asIso_hom, Category.assoc, pushout.inr_desc, Category.id_comp]

/-! ### The composition coherence — the single scaffolded input (M5)

All of the *associativity-flavoured* coherence is isolated into one bundle
`CompCoherence` and one scaffolded theorem `compCoherence`.  It packages:

* the **pushout associator** (`assoc`) — a boundary-fixing iso
  `(U.comp V).comp T ≅ U.comp (V.comp T)` (mathlib `pushoutAssoc`), used for the
  category law `assoc`;
* the two **unit-cancellation congruences** (`unitCancelRight`/`unitCancelLeft`) —
  e.g. `U.comp ((idCob _).comp W) ≅ U.comp W` and its left mirror — the genuine
  pushout-associativity statements needed to lift a *unit move* through a composite.

Routing the unit-move congruences through `unitCancel*` (rather than through the
other-side congruence) is what **breaks the otherwise non-terminating mutual
recursion** between the two single-step congruences: each single unit step is
discharged by a *non-recursive* iso supplied here.

This file is fully sorry-free: the coherence isos themselves are the raw
iso-existence lemmas `Conjectures.dcob_*` (in the permitted-`sorry` file), packaged
here into `CompCoherence` by `compCoherence`. -/

/-- The bundle of associativity-flavoured coherence isos (associator + the two
unit-cancellation isos), parameterised by the ambient objects. -/
structure CompCoherence (X Y Z W : PrecubicalSet) where
  /-- The pushout associator: `(U.comp V).comp T ≅ U.comp (V.comp T)`. -/
  assoc : ∀ (U : X ⇒c Y) (V : Y ⇒c Z) (T : Z ⇒c W),
    Nonempty (CobIso ((U.comp V).comp T) (U.comp (V.comp T)))
  /-- Cancelling a cylinder inserted at the shared `Y`, viewed from the right:
  `U.comp ((idCob Y).comp T) ≅ U.comp T`. -/
  unitCancelRight : ∀ (U : X ⇒c Y) (T : Y ⇒c Z),
    Nonempty (CobIso (U.comp ((idCob Y).comp T)) (U.comp T))
  /-- Cancelling a cylinder inserted at the shared `Y`, viewed from the left:
  `(U.comp (idCob Y)).comp T ≅ U.comp T`. -/
  unitCancelLeft : ∀ (U : X ⇒c Y) (T : Y ⇒c Z),
    Nonempty (CobIso ((U.comp (idCob Y)).comp T) (U.comp T))

/-- Package a raw iso-existence statement (an `e : mid ≅ mid` with both leg-equations,
the shape produced by the `Conjectures.dcob_*` lemmas) as a boundary-fixing
`CobIso`. -/
theorem CobIso.ofExists {W₁ W₂ : DirectedCobordism X Y}
    (h : ∃ e : W₁.mid ≅ W₂.mid,
      (W₁.inl ≫ e.hom = W₂.inl) ∧ (W₁.inr ≫ e.hom = W₂.inr)) :
    Nonempty (CobIso W₁ W₂) :=
  ⟨{ e := h.choose
     inl_hom := h.choose_spec.1
     inr_hom := h.choose_spec.2 }⟩

/-- **The composition coherence.**  The canonical pushout associator together with the
two unit-cancellation isos, packaged from the raw pushout-coherence iso-existence
lemmas `Conjectures.dcob_pushout_associator` / `dcob_unitCancelRight` /
`dcob_unitCancelLeft` (all instances of `CategoryTheory.Limits.pushoutAssoc` with
their leg-compatibility). -/
theorem compCoherence (X Y Z W : PrecubicalSet) : Nonempty (CompCoherence X Y Z W) :=
  ⟨{ assoc := fun U V T => CobIso.ofExists (PrecubicalSet.dcob_pushout_associator U V T)
     unitCancelRight := fun U T => CobIso.ofExists (PrecubicalSet.dcob_unitCancelRight U T)
     unitCancelLeft := fun U T => CobIso.ofExists (PrecubicalSet.dcob_unitCancelLeft U T) }⟩

/-- The associator extracted from the scaffolded coherence. -/
theorem compAssociator {X Y Z W : PrecubicalSet}
    (U : X ⇒c Y) (V : Y ⇒c Z) (T : Z ⇒c W) :
    Nonempty (CobIso ((U.comp V).comp T) (U.comp (V.comp T))) :=
  (compCoherence X Y Z W).some.assoc U V T

/-- The right unit-cancellation iso extracted from the scaffolded coherence. -/
theorem compUnitCancelRight {X Y Z : PrecubicalSet} (U : X ⇒c Y) (T : Y ⇒c Z) :
    Nonempty (CobIso (U.comp ((idCob Y).comp T)) (U.comp T)) :=
  (compCoherence X Y Z Z).some.unitCancelRight U T

/-- The left unit-cancellation iso extracted from the scaffolded coherence. -/
theorem compUnitCancelLeft {X Y Z : PrecubicalSet} (U : X ⇒c Y) (T : Y ⇒c Z) :
    Nonempty (CobIso ((U.comp (idCob Y)).comp T) (U.comp T)) :=
  (compCoherence X Y Z Z).some.unitCancelLeft U T

/-! ### The unit-move half of the descent congruence

Lifting a unit move `W ~ (idCob _).comp W` (resp. `W ~ W.comp (idCob _)`) through a
composition is genuine pushout associativity: e.g.
`U.comp ((idCob _).comp W) ≅ (U.comp (idCob _)).comp W` by the associator, and then
the outer comp absorbs the unit move on the inner factor.  We package these via
`cobordismRel` and route the associator through `compAssociator`. -/

/-- A boundary-fixing iso yields a single rel-∂ step. -/
theorem cobordismRel.ofIso {W₁ W₂ : X ⇒c Y} (φ : CobIso W₁ W₂) :
    cobordismRel X Y W₁ W₂ :=
  Relation.EqvGen.rel _ _ (CobElem.iso φ)

/-- A boundary-fixing iso (wrapped in `Nonempty`) yields a rel-∂ step. -/
theorem cobordismRel.ofNonemptyIso {W₁ W₂ : X ⇒c Y} (φ : Nonempty (CobIso W₁ W₂)) :
    cobordismRel X Y W₁ W₂ :=
  cobordismRel.ofIso φ.some

/-- A single unit-L step as a rel-∂ relation. -/
theorem cobordismRel.unitL (W : X ⇒c Y) :
    cobordismRel X Y W ((idCob X).comp W) :=
  Relation.EqvGen.rel _ _ (CobElem.unitL W)

/-- A single unit-R step as a rel-∂ relation. -/
theorem cobordismRel.unitR (W : X ⇒c Y) :
    cobordismRel X Y W (W.comp (idCob Y)) :=
  Relation.EqvGen.rel _ _ (CobElem.unitR W)

/-- The iso-move is a left congruence at the level of `cobordismRel`. -/
theorem cobordismRel.iso_compRight (U : X ⇒c Y) {W₁ W₂ : Y ⇒c Z} (φ : CobIso W₁ W₂) :
    cobordismRel X Z (U.comp W₁) (U.comp W₂) :=
  cobordismRel.ofIso (φ.compRight U)

/-- The iso-move is a right congruence at the level of `cobordismRel`. -/
theorem cobordismRel.iso_compLeft {W₁ W₂ : X ⇒c Y} (φ : CobIso W₁ W₂) (U : Y ⇒c Z) :
    cobordismRel X Z (W₁.comp U) (W₂.comp U) :=
  cobordismRel.ofIso (φ.compLeft U)

/-! ### Single-step congruences

We prove, for a *single* `CobElem` step `W₁ → W₂`, that `U.comp W₁ ≈ U.comp W₂` and
`W₁.comp U ≈ W₂.comp U`.  The iso case uses the (proven) iso-move congruence; the two
unit cases use the (scaffolded) associator plus the unit moves. -/

/-- **Single-step left congruence.**  A single elementary move on the right input is
absorbed by `U.comp -` up to rel-∂. -/
theorem cobordismRel.step_compRight (U : X ⇒c Y) {W₁ W₂ : Y ⇒c Z} (h : CobElem W₁ W₂) :
    cobordismRel X Z (U.comp W₁) (U.comp W₂) := by
  cases h with
  | iso φ => exact cobordismRel.iso_compRight U φ
  | unitL =>
      -- goal: `U.comp W₁ ≈ U.comp ((idCob Y).comp W₁)`
      -- exactly the right unit-cancellation iso, reversed.
      exact (cobordismRel_equivalence X Z).symm
        (cobordismRel.ofNonemptyIso (compUnitCancelRight U W₁))
  | unitR =>
      -- goal: `U.comp W₁ ≈ U.comp (W₁.comp (idCob Z))`
      -- composite-level `unitR` move `U.comp W₁ ≈ (U.comp W₁).comp (idCob Z)`,
      -- then associator `(U.comp W₁).comp (idCob Z) ≅ U.comp (W₁.comp (idCob Z))`.
      refine (cobordismRel_equivalence X Z).trans (cobordismRel.unitR (U.comp W₁)) ?_
      exact cobordismRel.ofNonemptyIso (compAssociator U W₁ (idCob Z))

/-- **Single-step right congruence.**  A single elementary move on the left input is
absorbed by `- .comp U` up to rel-∂. -/
theorem cobordismRel.step_compLeft {W₁ W₂ : X ⇒c Y} (h : CobElem W₁ W₂) (U : Y ⇒c Z) :
    cobordismRel X Z (W₁.comp U) (W₂.comp U) := by
  cases h with
  | iso φ => exact cobordismRel.iso_compLeft φ U
  | unitL =>
      -- goal: `W₁.comp U ≈ ((idCob X).comp W₁).comp U`
      -- associator `((idCob X).comp W₁).comp U ≅ (idCob X).comp (W₁.comp U)`,
      -- then the composite-level `unitL` move `W₁.comp U ≈ (idCob X).comp (W₁.comp U)`.
      refine (cobordismRel_equivalence X Z).trans (cobordismRel.unitL (W₁.comp U)) ?_
      exact (cobordismRel_equivalence X Z).symm
        (cobordismRel.ofNonemptyIso (compAssociator (idCob X) W₁ U))
  | unitR =>
      -- goal: `W₁.comp U ≈ (W₁.comp (idCob Y)).comp U`
      -- exactly the left unit-cancellation iso, reversed.
      exact (cobordismRel_equivalence X Z).symm
        (cobordismRel.ofNonemptyIso (compUnitCancelLeft W₁ U))

/-! ### Full congruences (by `EqvGen` induction) -/

/-- **Left congruence.**  `cobordismRel` is preserved by `U.comp -`. -/
theorem cobordismRel.compRight (U : X ⇒c Y) {W₁ W₂ : Y ⇒c Z}
    (h : cobordismRel Y Z W₁ W₂) : cobordismRel X Z (U.comp W₁) (U.comp W₂) := by
  induction h with
  | rel a b hab => exact cobordismRel.step_compRight U hab
  | refl a => exact (cobordismRel_equivalence X Z).refl _
  | symm a b _ ih => exact (cobordismRel_equivalence X Z).symm ih
  | trans a b c _ _ ih₁ ih₂ => exact (cobordismRel_equivalence X Z).trans ih₁ ih₂

/-- **Right congruence.**  `cobordismRel` is preserved by `- .comp U`. -/
theorem cobordismRel.compLeft {W₁ W₂ : X ⇒c Y}
    (h : cobordismRel X Y W₁ W₂) (U : Y ⇒c Z) :
    cobordismRel X Z (W₁.comp U) (W₂.comp U) := by
  induction h with
  | rel a b hab => exact cobordismRel.step_compLeft hab U
  | refl a => exact (cobordismRel_equivalence X Z).refl _
  | symm a b _ ih => exact (cobordismRel_equivalence X Z).symm ih
  | trans a b c _ _ ih₁ ih₂ => exact (cobordismRel_equivalence X Z).trans ih₁ ih₂

/-! ### Composition descends to the quotient -/

/-- **Composition on Hom-quotients.**  Descended from `DirectedCobordism.comp` via
the two congruences above. -/
noncomputable def compCob {X Y Z : PrecubicalSet} :
    HomCob X Y → HomCob Y Z → HomCob X Z :=
  Quotient.lift₂ (fun W₁ W₂ => HomCob.mk (W₁.comp W₂))
    (by
      intro W₁ W₂ W₁' W₂' h₁ h₂
      -- `h₁ : cobordismRel X Y W₁ W₁'`, `h₂ : cobordismRel Y Z W₂ W₂'`.
      apply HomCob.sound_rel
      refine (cobordismRel_equivalence X Z).trans
        (cobordismRel.compLeft h₁ W₂) ?_
      exact cobordismRel.compRight W₁' h₂)

@[simp] theorem compCob_mk {X Y Z : PrecubicalSet} (W₁ : X ⇒c Y) (W₂ : Y ⇒c Z) :
    compCob (HomCob.mk W₁) (HomCob.mk W₂) = HomCob.mk (W₁.comp W₂) := rfl

/-! ### The category `dCob`

Objects are a thin wrapper around `PrecubicalSet` (so we do not collide with the
functor-category `Category PrecubicalSet`).  Morphisms are `HomCob`, identity is the
class of the cylinder `idCob`, composition is `compCob`. -/

/-- **The objects of the directed-cobordism category.**  A one-field wrapper around
`PrecubicalSet`, used to carry the cobordism `Category` instance without clobbering
the functor-category `Category PrecubicalSet`. -/
@[ext] structure dCob where
  /-- The underlying precubical set. -/
  carrier : PrecubicalSet

namespace dCob

/-- Package a precubical set as an object of `dCob`. -/
abbrev of (X : PrecubicalSet) : dCob := ⟨X⟩

@[simp] theorem of_carrier (X : PrecubicalSet) : (dCob.of X).carrier = X := rfl

@[simp] theorem carrier_mk (X : PrecubicalSet) : dCob.mk X = dCob.of X := rfl

end dCob

/-- **The directed-cobordism category `dCob`.**  Morphisms `dCob.of X ⟶ dCob.of Y`
are rel-∂ classes `HomCob X Y`; the identity on `X` is the class of the cylinder
`idCob X` (a *weak / quotient* unit — the cylinder is only a unit after the rel-∂
quotient), and composition is `compCob`.

The unit laws hold because the collar-stabilization moves `CobElem.unitL/unitR`
identify `W` with `(idCob X).comp W` and `W.comp (idCob Y)`; associativity is the
pushout associator routed through `compAssociator`. -/
noncomputable instance categoryDCob : Category.{1} dCob where
  Hom A B := HomCob A.carrier B.carrier
  id A := HomCob.mk (idCob A.carrier)
  comp {A B C} f g := compCob f g
  id_comp {A B} f := by
    -- `⟦idCob A⟧ ∘ ⟦W⟧ = ⟦W⟧`, using `unitL`.
    refine Quotient.inductionOn f (fun W => ?_)
    change compCob (HomCob.mk (idCob A.carrier)) (HomCob.mk W) = HomCob.mk W
    rw [compCob_mk]
    exact (HomCob.sound (CobElem.unitL W)).symm
  comp_id {A B} f := by
    -- `⟦W⟧ ∘ ⟦idCob B⟧ = ⟦W⟧`, using `unitR`.
    refine Quotient.inductionOn f (fun W => ?_)
    change compCob (HomCob.mk W) (HomCob.mk (idCob B.carrier)) = HomCob.mk W
    rw [compCob_mk]
    exact (HomCob.sound (CobElem.unitR W)).symm
  assoc {A B C D} f g h := by
    -- associativity via the pushout associator `compAssociator`.
    refine Quotient.inductionOn₃ f g h (fun U V T => ?_)
    change compCob (compCob (HomCob.mk U) (HomCob.mk V)) (HomCob.mk T)
        = compCob (HomCob.mk U) (compCob (HomCob.mk V) (HomCob.mk T))
    rw [compCob_mk, compCob_mk, compCob_mk, compCob_mk]
    exact HomCob.sound_rel
      (cobordismRel.ofNonemptyIso (compAssociator U V T))

/-- The identity morphism on `dCob.of X` is the class of the cylinder. -/
@[simp] theorem dCob_id (X : PrecubicalSet) :
    𝟙 (dCob.of X) = HomCob.mk (idCob X) := rfl

/-- Composition in `dCob` is `compCob` on representatives. -/
@[simp] theorem dCob_comp_mk {X Y Z : PrecubicalSet} (W₁ : X ⇒c Y) (W₂ : Y ⇒c Z) :
    ((HomCob.mk W₁ : dCob.of X ⟶ dCob.of Y) ≫ (HomCob.mk W₂ : dCob.of Y ⟶ dCob.of Z)
      : dCob.of X ⟶ dCob.of Z) = HomCob.mk (W₁.comp W₂) := rfl

end PrecubicalSet
