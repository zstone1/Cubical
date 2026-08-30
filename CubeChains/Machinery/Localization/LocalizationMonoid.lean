import CubeChains.Machinery.Presentation.FreeGroupoidPresentation
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Widesubcategory

/-!
# Machinery/Localization/LocalizationMonoid — the monoid of a category modulo an inverted class

`LocMonoid W` is presented by the **arrows** of `C`: one generator per arrow, functoriality as the
relations, and the inverted class `W` made trivial.  Nothing is encoded — the presentation is the
category itself.

`IsWideTerminal W x` is terminality of `x` in the wide subcategory `W` (`IsWideInitial` the dual);
conjugating an arrow by the canonical `W`-arrows at its two ends turns it into a loop at `x`
(`loopOf`), and `locToEnd` is the resulting monoid map, defined for *any* functor inverting `W`.
At the localization it is an isomorphism (`endEquiv`), so `End` there is exactly `LocMonoid W`.

The monoid analogue of `Machinery/Presentation/FreeGroupoidPresentation`, where the class inverted
is everything and the answer is a group.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-! ### The presentation -/

/-- The relations: functoriality, and triviality on the inverted class. -/
inductive LocRel : FreeMonoid (Arr C) → FreeMonoid (Arr C) → Prop
  | comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
      LocRel (FreeMonoid.of ⟨b, c, g⟩ * FreeMonoid.of ⟨a, b, f⟩) (FreeMonoid.of ⟨a, c, f ≫ g⟩)
  | triv {a b : C} (w : a ⟶ b) (hw : W w) : LocRel (FreeMonoid.of ⟨a, b, w⟩) 1

/-- **The monoid of `C` modulo `W`**: one generator per arrow, functoriality, `W` trivial. -/
def LocMonoid : Type max u v := PresentedMonoid (LocRel W)

instance : Monoid (LocMonoid W) := inferInstanceAs (Monoid (PresentedMonoid (LocRel W)))

/-- An arrow, as a generator. -/
def locOf {a b : C} (f : a ⟶ b) : LocMonoid W := PresentedMonoid.of _ ⟨a, b, f⟩

variable {W}

theorem locOf_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    locOf W g * locOf W f = locOf W (f ≫ g) :=
  PresentedMonoid.mk_eq_mk_of_rel (LocRel.comp f g)

theorem locOf_triv {a b : C} {w : a ⟶ b} (hw : W w) : locOf W w = 1 :=
  PresentedMonoid.mk_eq_mk_of_rel (LocRel.triv w hw)

@[simp] theorem locOf_id [W.ContainsIdentities] (a : C) : locOf W (𝟙 a) = 1 :=
  locOf_triv (W.id_mem a)

theorem locOf_closure : Submonoid.closure (Set.range fun e : Arr C => locOf W e.hom) = ⊤ :=
  PresentedMonoid.closure_range_of _

theorem locMonoid_ext {M : Type*} [Monoid M] {φ ψ : LocMonoid W →* M}
    (h : ∀ {a b : C} (f : a ⟶ b), φ (locOf W f) = ψ (locOf W f)) : φ = ψ :=
  PresentedMonoid.ext _ fun e => h e.hom

variable (W)

/-- **The universal property**: a functorial assignment that kills `W` extends to `LocMonoid W`. -/
def LocMonoid.lift {M : Type*} [Monoid M] (g : ∀ {a b : C}, (a ⟶ b) → M)
    (hcomp : ∀ {a b c : C} (f : a ⟶ b) (h : b ⟶ c), g h * g f = g (f ≫ h))
    (htriv : ∀ {a b : C} {w : a ⟶ b}, W w → g w = 1) : LocMonoid W →* M :=
  PresentedMonoid.lift (fun e => g e.hom) (by
    rintro x y (⟨f, h⟩ | ⟨w, hw⟩)
    · simpa using hcomp f h
    · simpa using htriv hw)

@[simp] theorem LocMonoid.lift_locOf {M : Type*} [Monoid M] {g : ∀ {a b : C}, (a ⟶ b) → M}
    {hcomp htriv} {a b : C} (f : a ⟶ b) :
    LocMonoid.lift W g hcomp htriv (locOf W f) = g f := rfl

/-- **`LocMonoid W` receives `C`** — the relations are exactly the two functor laws. -/
def toLocMonoid [W.ContainsIdentities] : C ⥤ SingleObj (LocMonoid W) where
  obj _ := SingleObj.star _
  map f := locOf W f
  map_id a := locOf_id a
  map_comp f g := (locOf_comp f g).symm

theorem toLocMonoid_inverts [W.ContainsIdentities] : W.IsInvertedBy (toLocMonoid W) := by
  intro a b w hw
  refine ⟨⟨locOf W w, ?_, ?_⟩⟩ <;>
    · change locOf W w * locOf W w = 1
      rw [locOf_triv hw, mul_one]

/-! ### Wide-terminal objects

A wide-terminal object collapses the component onto `x` once `W` is inverted.  It is exactly a
terminal object of mathlib's `WideSubcategory W`, so the compatibility `comp_from` — what makes
`⟨w⟩ = 1` consistent — is `IsTerminal.comp_from`, and `from_self` is `IsTerminal.from_self`. -/

/-- **`x` is terminal among the `W`-arrows**: every object has exactly one `W`-arrow to `x`. -/
abbrev IsWideTerminal [W.IsMultiplicative] (x : C) :=
  Limits.IsTerminal (WideSubcategory.mk x : WideSubcategory W)

variable {W} {x : C} {D : Type*} [Category D]

namespace IsWideTerminal

variable [W.IsMultiplicative] (S : IsWideTerminal W x)

/-- The canonical `W`-arrow into the basepoint. -/
def «from» (a : C) : a ⟶ x := (Limits.IsTerminal.from S (WideSubcategory.mk a)).hom

theorem mem (a : C) : W (S.from a) := (Limits.IsTerminal.from S (WideSubcategory.mk a)).property

/-- Travelling by `W` first changes nothing. -/
theorem comp_from {a b : C} (w : a ⟶ b) (hw : W w) : w ≫ S.from b = S.from a := by
  have h := Limits.IsTerminal.comp_from S
    (⟨w, hw⟩ : (WideSubcategory.mk a : WideSubcategory W) ⟶ WideSubcategory.mk b)
  exact congrArg InducedWideCategory.Hom.hom h

/-- The basepoint is its own — what makes the retraction fix the loops at `x`. -/
theorem from_self : S.from x = 𝟙 x :=
  congrArg InducedWideCategory.Hom.hom (Limits.IsTerminal.from_self S)

end IsWideTerminal

/-! ### Wide-initial objects

The mirror of `IsWideTerminal`: `to_comp` is `IsInitial.to_comp` and `to_self` is
`IsInitial.to_self`. -/

section WideInitial

variable (W) [W.IsMultiplicative]

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

/-- The basepoint is its own — what makes the merge at `y` invisible. -/
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

variable [W.IsMultiplicative]

theorem isIso_map_from (F : C ⥤ D) (hF : W.IsInvertedBy F) (S : IsWideTerminal W x) (a : C) :
    IsIso (F.map (S.from a)) := hF _ (S.mem a)

instance isIso_Q_map_from (S : IsWideTerminal W x) (a : C) : IsIso (W.Q.map (S.from a)) :=
  W.Q_inverts _ (S.mem a)

/-- **The loop an arrow makes** once the canonical `W`-arrows are inverted. -/
noncomputable def loopOf (F : C ⥤ D) (hF : W.IsInvertedBy F) (S : IsWideTerminal W x) {a b : C}
    (f : a ⟶ b) : End (F.obj x) :=
  haveI := isIso_map_from F hF S a
  inv (F.map (S.from a)) ≫ F.map f ≫ F.map (S.from b)

variable (F : C ⥤ D) (hF : W.IsInvertedBy F) (S : IsWideTerminal W x)

/-- **Loops compose along composition** — the inner arrows cancel. -/
theorem loopOf_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    loopOf F hF S (f ≫ g) = loopOf F hF S f ≫ loopOf F hF S g := by
  haveI := isIso_map_from F hF S a
  haveI := isIso_map_from F hF S b
  simp only [loopOf, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]

/-- **A `W`-arrow makes the trivial loop** — this is `IsWideTerminal.comp_from`. -/
theorem loopOf_triv {a b : C} {w : a ⟶ b} (hw : W w) : loopOf F hF S w = 𝟙 _ := by
  haveI := isIso_map_from F hF S a
  rw [loopOf, ← Functor.map_comp, S.comp_from w hw, IsIso.inv_hom_id]

/-- **`LocMonoid W` is realised in the loops**, at every functor inverting `W`. -/
noncomputable def locToEnd : LocMonoid W →* End (F.obj x) :=
  LocMonoid.lift W (loopOf F hF S) (fun f g => (loopOf_comp F hF S f g).symm)
    (fun hw => loopOf_triv F hF S hw)

@[simp] theorem locToEnd_locOf {a b : C} (f : a ⟶ b) :
    locToEnd F hF S (locOf W f) = loopOf F hF S f := rfl

/-! ### At the localization itself

`W.Q` inverts `W`, so it is one of the `F`s above, and `locFunctor` reads a localized morphism back
as an element of `LocMonoid W`.  One composite is `Construction.fac`; the other is the retraction
the wide-terminal object provides. -/

variable (W) in
/-- The comparison out of the localization — `LocMonoid W` receives `C` and kills `W`. -/
noncomputable def locFunctor :
    W.Localization ⥤ SingleObj (LocMonoid W) :=
  Localization.Construction.lift (toLocMonoid W) (toLocMonoid_inverts W)

@[simp] theorem locFunctor_map_Q {a b : C} (f : a ⟶ b) :
    (locFunctor W).map (W.Q.map f) = locOf W f := by
  have h := Functor.congr_hom
    (Localization.Construction.fac (toLocMonoid W) (toLocMonoid_inverts W)) f
  rw [Functor.comp_map] at h
  rw [locFunctor, h]
  change (1 : LocMonoid W) * ((1 : LocMonoid W) * locOf W f) = locOf W f
  rw [one_mul, one_mul]

/-- **Reading a loop back gives the arrow it came from.** -/
theorem locFunctor_loopOf (S : IsWideTerminal W x) {a b : C} (f : a ⟶ b) :
    (locFunctor W).map (loopOf W.Q W.Q_inverts S f) = locOf W f := by
  haveI := isIso_map_from W.Q W.Q_inverts S a
  have hinv : (locFunctor W).map (inv (W.Q.map (S.from a))) = 𝟙 _ := by
    rw [Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, locFunctor_map_Q,
      locOf_triv (S.mem a), mul_one]
  rw [loopOf, Functor.map_comp, Functor.map_comp, hinv]
  simp only [SingleObj.comp_as_mul, SingleObj.id_as_one, locFunctor_map_Q,
    locOf_triv (S.mem b), one_mul, mul_one]

/-- **The realization is split injective at the localization.** -/
theorem locFunctor_comp_locToEnd (S : IsWideTerminal W x) :
    ((locFunctor W).mapEnd (W.Q.obj x)).comp (locToEnd W.Q W.Q_inverts S)
      = MonoidHom.id (LocMonoid W) :=
  locMonoid_ext fun f => locFunctor_loopOf S f

theorem locToEnd_injective (S : IsWideTerminal W x) :
    Function.Injective (locToEnd W.Q W.Q_inverts S) := by
  refine Function.Injective.of_comp (f := (locFunctor W).mapEnd (W.Q.obj x)) ?_
  have h : ((locFunctor W).mapEnd (W.Q.obj x)) ∘ (locToEnd W.Q W.Q_inverts S) = id := by
    ext p
    exact congrArg (fun φ : LocMonoid W →* LocMonoid W => φ p) (locFunctor_comp_locToEnd S)
  rw [h]
  exact Function.injective_id

/-! ### The retraction onto the basepoint

The wide-terminal object collapses the localization onto `x`: `locSingleFunctor` sends everything
there, and `locInvNat` is the natural transformation putting each object back, whose components are
the inverted canonical arrows.  `Construction.natTransExtension` transports it off `W.Q`, and
`Construction.objEquiv` says every object is in the image of `W.Q`, so it is a natural
isomorphism. -/

/-- The localization, collapsed onto the basepoint. -/
noncomputable def locSingleFunctor (S : IsWideTerminal W x) :
    SingleObj (LocMonoid W) ⥤ W.Localization where
  obj _ := W.Q.obj x
  map p := locToEnd W.Q W.Q_inverts S p
  map_id _ := (locToEnd W.Q W.Q_inverts S).map_one
  map_comp p q := by
    rw [SingleObj.comp_as_mul, map_mul]
    rfl

/-- The canonical arrow's inverse in the localization — the *definitional* one, so nothing has to
be searched for. -/
noncomputable def locInv (S : IsWideTerminal W x) (a : C) : W.Q.obj x ⟶ W.Q.obj a :=
  (Localization.Construction.wIso (S.from a) (S.mem a)).inv

instance isIso_locInv (S : IsWideTerminal W x) (a : C) : IsIso (locInv S a) := Iso.isIso_inv _

theorem inv_Q_map_from (S : IsWideTerminal W x) (a : C) :
    @inv _ _ _ _ (W.Q.map (S.from a)) (isIso_Q_map_from S a) = locInv S a :=
  IsIso.inv_eq_of_hom_inv_id (Localization.Construction.wIso (S.from a) (S.mem a)).hom_inv_id

theorem Q_map_from_comp_locInv (S : IsWideTerminal W x) (a : C) :
    W.Q.map (S.from a) ≫ locInv S a = 𝟙 _ :=
  (Localization.Construction.wIso (S.from a) (S.mem a)).hom_inv_id

theorem loopOf_Q (S : IsWideTerminal W x) {a b : C} (f : a ⟶ b) :
    loopOf W.Q W.Q_inverts S f = locInv S a ≫ W.Q.map f ≫ W.Q.map (S.from b) := by
  rw [loopOf, ← inv_Q_map_from S a]

/-- Putting each object back where it came from. -/
noncomputable def locInvNat (S : IsWideTerminal W x) :
    W.Q ⋙ (locFunctor W ⋙ locSingleFunctor S) ⟶ W.Q ⋙ 𝟭 W.Localization where
  app a := locInv S a
  naturality a b f := by
    change (locSingleFunctor S).map ((locFunctor W).map (W.Q.map f)) ≫ _ = _
    rw [locFunctor_map_Q]
    change loopOf W.Q W.Q_inverts S f ≫ locInv S b = _
    rw [loopOf_Q, Category.assoc, Category.assoc, Q_map_from_comp_locInv, Category.comp_id]
    rfl

theorem natTransExtension_locInvNat_app (S : IsWideTerminal W x) (a : C) :
    (Localization.Construction.natTransExtension (locInvNat S)).app (W.Q.obj a)
      = locInv S a := by
  simp only [Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq]
  rfl

instance natTransExtension_locInvNat_isIso (S : IsWideTerminal W x) :
    IsIso (Localization.Construction.natTransExtension (locInvNat S)) := by
  haveI : ∀ X, IsIso ((Localization.Construction.natTransExtension (locInvNat S)).app X) := by
    intro X
    obtain ⟨a, rfl⟩ : ∃ a, W.Q.obj a = X :=
      ⟨(Localization.Construction.objEquiv W).invFun X,
        (Localization.Construction.objEquiv W).right_inv X⟩
    rw [natTransExtension_locInvNat_app]
    exact isIso_locInv S a
  exact NatIso.isIso_of_isIso_app _

/-- **Every loop at the basepoint is the loop of an arrow.**  Naturality of the retraction at `γ`,
where the canonical arrow at the basepoint is the identity (`IsWideTerminal.from_self`). -/
theorem locToEnd_locFunctor (S : IsWideTerminal W x) (γ : End (W.Q.obj x)) :
    locToEnd W.Q W.Q_inverts S ((locFunctor W).mapEnd (W.Q.obj x) γ) = γ := by
  have hroot : (Localization.Construction.natTransExtension (locInvNat S)).app (W.Q.obj x)
      = 𝟙 (W.Q.obj x) := by
    rw [natTransExtension_locInvNat_app, ← Q_map_from_comp_locInv S x, S.from_self,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat := (Localization.Construction.natTransExtension (locInvNat S)).naturality γ
  rw [hroot] at hnat
  exact ((Category.comp_id _).symm.trans hnat).trans (Category.id_comp _)

theorem locToEnd_surjective (S : IsWideTerminal W x) :
    Function.Surjective (locToEnd W.Q W.Q_inverts S) :=
  fun γ => ⟨(locFunctor W).mapEnd (W.Q.obj x) γ, locToEnd_locFunctor S γ⟩

/-- **The endomorphisms of the localization at the basepoint are `LocMonoid W`** — the category
modulo the inverted class, presented by its own arrows. -/
noncomputable def endEquiv (S : IsWideTerminal W x) :
    LocMonoid W ≃* End (W.Q.obj x) :=
  MulEquiv.ofBijective (locToEnd W.Q W.Q_inverts S)
    ⟨locToEnd_injective S, locToEnd_surjective S⟩

end CategoryTheory
