import CubeChains.Foundations.LocalizationMonoid

/-!
# Foundations/GarsidePresentation — the localization, presented by an interval

`IsWideTerminal W x` makes `x` terminal in the wide subcategory `W`; dually `IsWideInitial W y`
makes `y` initial.  Between them the **simples** `y ⟶ x` present the whole localization:
`GarsideMonoid W y x` has one relation per factorisation `y ⟶ b ⟶ x` — a simple times a simple is a
simple — and one declaring the `W`-simple to be the unit.  That last relation is not optional:
without it every generator may go to a single idempotent.

No length function appears: the intermediate object `b` is the witness Garside must otherwise
recover from "the lengths add", so the condition is carried by the factorisation.  Matching the two
relation sets is then a theorem about the target, not a hypothesis here.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ### Wide-initial objects

The mirror of `IsWideTerminal`: `to_comp` is `IsInitial.to_comp` and `to_self` is
`IsInitial.to_self`. -/

section WideInitial

variable (W : MorphismProperty C) [W.IsMultiplicative]

/-- **`y` is initial among the `W`-arrows**: every object receives exactly one `W`-arrow
from `y`. -/
abbrev IsWideInitial (y : C) :=
  Limits.IsInitial (WideSubcategory.mk y : WideSubcategory W)

variable {W} {y : C}

namespace IsWideInitial

variable (T : IsWideInitial W y)

/-- The canonical `W`-arrow out of the basepoint. -/
def «to» (a : C) : y ⟶ a := (Limits.IsInitial.to T (WideSubcategory.mk a)).hom

theorem mem (a : C) : W (T.to a) := (Limits.IsInitial.to T (WideSubcategory.mk a)).property

/-- Travelling on by `W` changes nothing. -/
theorem to_comp {a b : C} (w : a ⟶ b) (hw : W w) : T.to a ≫ w = T.to b := by
  have h := Limits.IsInitial.to_comp T
    (⟨w, hw⟩ : (WideSubcategory.mk a : WideSubcategory W) ⟶ WideSubcategory.mk b)
  exact congrArg InducedWideCategory.Hom.hom h

/-- The basepoint is its own — what makes the pad at `y` invisible. -/
theorem to_self : T.to y = 𝟙 y :=
  congrArg InducedWideCategory.Hom.hom (Limits.IsInitial.to_self T)

/-- **Inverting `W` collapses the component onto `y`.** -/
noncomputable def locIso (a : C) : W.Q.obj y ≅ W.Q.obj a :=
  haveI := W.Q_inverts _ (T.mem a)
  asIso (W.Q.map (T.to a))

include T in
/-- …so the localized component is connected. -/
theorem nonempty_locIso (a b : C) : Nonempty (W.Q.obj a ≅ W.Q.obj b) :=
  ⟨(T.locIso a).symm ≪≫ T.locIso b⟩

end IsWideInitial

end WideInitial

/-! ### The presentation -/

section Presentation

variable (W : MorphismProperty C) (y x : C)

/-- The relations on the simples: a `W`-simple is the unit, and a factorisation `y ⟶ b ⟶ x` splits
a simple into a composable pair of simples. -/
inductive GarsideRel : FreeMonoid (y ⟶ x) → FreeMonoid (y ⟶ x) → Prop
  | triv {w : y ⟶ x} (hw : W w) : GarsideRel (FreeMonoid.of w) 1
  | comp {b : C} (f : y ⟶ b) (g : b ⟶ x) {u : y ⟶ b} {v : b ⟶ x} (hu : W u) (hv : W v) :
      GarsideRel (FreeMonoid.of (u ≫ g) * FreeMonoid.of (f ≫ v)) (FreeMonoid.of (f ≫ g))

/-- **The monoid of the interval `y ⟶ x`**: generators the simples, relations the factorisations. -/
def GarsideMonoid : Type v := PresentedMonoid (GarsideRel W y x)

instance : Monoid (GarsideMonoid W y x) :=
  inferInstanceAs (Monoid (PresentedMonoid (GarsideRel W y x)))

end Presentation

section Generators

variable {W : MorphismProperty C} {y x : C}

variable (W) in
/-- A simple, as a generator. -/
def garOf (h : y ⟶ x) : GarsideMonoid W y x := PresentedMonoid.of _ h

theorem garOf_triv {w : y ⟶ x} (hw : W w) : garOf W w = 1 :=
  PresentedMonoid.mk_eq_mk_of_rel (GarsideRel.triv hw)

theorem garOf_comp {b : C} (f : y ⟶ b) (g : b ⟶ x) {u : y ⟶ b} {v : b ⟶ x} (hu : W u) (hv : W v) :
    garOf W (u ≫ g) * garOf W (f ≫ v) = garOf W (f ≫ g) :=
  PresentedMonoid.mk_eq_mk_of_rel (GarsideRel.comp f g hu hv)

theorem garsideMonoid_ext {M : Type*} [Monoid M] {φ ψ : GarsideMonoid W y x →* M}
    (h : ∀ f : y ⟶ x, φ (garOf W f) = ψ (garOf W f)) : φ = ψ :=
  PresentedMonoid.ext _ h

variable (W) in
/-- **The universal property**: a map on simples killing the `W`-simple and splitting along
factorisations extends to `GarsideMonoid W y x`. -/
def GarsideMonoid.lift {M : Type*} [Monoid M] (φ : (y ⟶ x) → M)
    (htriv : ∀ {w : y ⟶ x}, W w → φ w = 1)
    (hcomp : ∀ {b : C} (f : y ⟶ b) (g : b ⟶ x) (u : y ⟶ b) (v : b ⟶ x), W u → W v →
      φ (u ≫ g) * φ (f ≫ v) = φ (f ≫ g)) :
    GarsideMonoid W y x →* M :=
  PresentedMonoid.lift φ (by
    rintro a b (⟨hw⟩ | ⟨f, g, hu, hv⟩)
    · simpa using htriv hw
    · simpa using hcomp f g _ _ hu hv)

@[simp] theorem GarsideMonoid.lift_garOf {M : Type*} [Monoid M] {φ : (y ⟶ x) → M}
    {htriv hcomp} (h : y ⟶ x) : GarsideMonoid.lift W φ htriv hcomp (garOf W h) = φ h := rfl

end Generators

/-! ### The comparison

Padding an arrow by the wide-initial arrow on the left and the wide-terminal one on the right makes
it a simple without changing its class, since both pads are `W`.  At the two ends the pads are
identities (`from_self`, `to_self`), which is the other round trip. -/

section Comparison

variable {W : MorphismProperty C} [W.IsMultiplicative] {y x : C}

/-- An arrow, padded into a simple. -/
def pad (S : IsWideTerminal W x) (T : IsWideInitial W y) {a b : C} (f : a ⟶ b) : y ⟶ x :=
  T.to a ≫ f ≫ S.from b

theorem mem_pad (S : IsWideTerminal W x) (T : IsWideInitial W y) {a b : C} {w : a ⟶ b} (hw : W w) :
    W (pad S T w) :=
  W.comp_mem _ _ (T.mem a) (W.comp_mem _ _ hw (S.mem b))

/-- **The pads are invisible in `LocMonoid W`.** -/
theorem locOf_pad (S : IsWideTerminal W x) (T : IsWideInitial W y) {a b : C} (f : a ⟶ b) :
    locOf W (pad S T f) = locOf W f := by
  simp only [pad]
  rw [← locOf_comp, ← locOf_comp, locOf_triv (S.mem b), one_mul, locOf_triv (T.mem a), mul_one]

/-- **The pads split along composition** — the factorisation relation at the middle object. -/
theorem garOf_pad_comp (S : IsWideTerminal W x) (T : IsWideInitial W y) {a b c : C} (f : a ⟶ b)
    (g : b ⟶ c) : garOf W (pad S T g) * garOf W (pad S T f) = garOf W (pad S T (f ≫ g)) := by
  simpa [pad] using garOf_comp (W := W) (T.to a ≫ f) (g ≫ S.from c) (T.mem b) (S.mem b)

/-- **Forward**: an arrow goes to the simple it pads to. -/
def locToGar (S : IsWideTerminal W x) (T : IsWideInitial W y) :
    LocMonoid W →* GarsideMonoid W y x :=
  LocMonoid.lift W (fun f => garOf W (pad S T f))
    (fun f g => garOf_pad_comp S T f g)
    (fun hw => garOf_triv (mem_pad S T hw))

variable (W) (y x) in
/-- **Backward**: a simple is an arrow. -/
def garToLoc : GarsideMonoid W y x →* LocMonoid W :=
  GarsideMonoid.lift W (locOf W) (fun hw => locOf_triv hw)
    (fun f g _ _ hu hv => by
      rw [← locOf_comp, ← locOf_comp, locOf_triv hu, mul_one, locOf_triv hv, one_mul, locOf_comp])

theorem garToLoc_comp_locToGar (S : IsWideTerminal W x) (T : IsWideInitial W y) :
    (garToLoc W y x).comp (locToGar S T) = MonoidHom.id (LocMonoid W) :=
  locMonoid_ext fun f => locOf_pad S T f

theorem locToGar_comp_garToLoc (S : IsWideTerminal W x) (T : IsWideInitial W y) :
    (locToGar S T).comp (garToLoc W y x) = MonoidHom.id (GarsideMonoid W y x) :=
  garsideMonoid_ext fun h => by
    change garOf W (pad S T h) = garOf W h
    simp only [pad, T.to_self, S.from_self, Category.id_comp, Category.comp_id]

/-- **The localization monoid is presented by the interval `y ⟶ x`**: generators the simples,
relations the factorisations through the category. -/
def locEquivGarside (S : IsWideTerminal W x) (T : IsWideInitial W y) :
    LocMonoid W ≃* GarsideMonoid W y x where
  toFun := locToGar S T
  invFun := garToLoc W y x
  left_inv p := DFunLike.congr_fun (garToLoc_comp_locToGar S T) p
  right_inv q := DFunLike.congr_fun (locToGar_comp_garToLoc S T) q
  map_mul' := map_mul (locToGar S T)

/-- **The endomorphisms of the localization at the basepoint are the interval's monoid.** -/
noncomputable def endEquivGarside (S : IsWideTerminal W x) (T : IsWideInitial W y) :
    GarsideMonoid W y x ≃* End (W.Q.obj x) :=
  (locEquivGarside S T).symm.trans (endEquiv S)

end Comparison

end CategoryTheory
