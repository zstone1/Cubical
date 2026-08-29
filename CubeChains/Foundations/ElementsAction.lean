import Mathlib.CategoryTheory.Action
import CubeChains.Foundations.FibrationLocalize

/-!
# Foundations/ElementsAction — a functor on one object is an action

`SingleObj M`'s composition is `f ≫ g = g * f`, so a **covariant** `F : SingleObj M ⥤ Type` is
already a left `M`-set — no `ᵐᵒᵖ` anywhere.  The twist appears in the contravariant reading, where
a presheaf is a *right* action; `invActionPresheaf` is the presheaf a group-valued action supplies,
and `(∫ -)ᵒᵖ` puts it back.
-/

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

open Opposite

/-! ### Covariant: a functor on `SingleObj M` is an `M`-set -/

namespace SingleObj

variable {M : Type*} [Monoid M]

/-- A functor out of `SingleObj M` is an `M`-set — `f ≫ g = g * f` supplies the reversal. -/
instance mulActionOfFunctor (F : SingleObj M ⥤ Type u) :
    MulAction M (F.obj (SingleObj.star M)) where
  smul m x := F.map m x
  one_smul x := F.map_id_apply (SingleObj.star M) x
  mul_smul m₁ m₂ x := F.map_comp_apply (m₂ : SingleObj.star M ⟶ SingleObj.star M) m₁ x

end SingleObj

/-! ### Contravariant: the presheaf a group action supplies -/

/-- The label of an arrow of an action category, at the type `SingleObj` hides from elaboration
(`f.val` is inferred at the hom type, where `•` and numerals do not resolve). -/
abbrev ActionCategory.label {M : Type*} [Monoid M] {A : Type u} [MulAction M A]
    {p q : ActionCategory M A} (f : p ⟶ q) : M := f.val

theorem ActionCategory.label_smul {M : Type*} [Monoid M] {A : Type u} [MulAction M A]
    {p q : ActionCategory M A} (f : p ⟶ q) : label f • p.back = q.back := f.2

section InvAction

variable {M : Type*} [Monoid M] {Γ : Type*} [Group Γ] (A : Type u) [MulAction Γ A] (φ : M →* Γ)

/-- The presheaf on `SingleObj M` carried by a `Γ`-set along `φ`: restriction along `m` is `φ m⁻¹`.
The inverse is what makes `(∫ -)ᵒᵖ` the action category rather than its opposite. -/
def invActionPresheaf : (SingleObj M)ᵒᵖ ⥤ Type u where
  obj _ := A
  map f := TypeCat.ofHom fun x => (φ f.unop)⁻¹ • x
  map_id _ := by ext x; change (φ (1 : M))⁻¹ • x = x; simp
  map_comp f g := by
    ext x
    change (φ ((f ≫ g).unop : M))⁻¹ • x = (φ (g.unop : M))⁻¹ • (φ (f.unop : M))⁻¹ • x
    have h : ((f ≫ g).unop : M) = f.unop * g.unop := rfl
    rw [h, map_mul, mul_inv_rev, mul_smul]

theorem invActionPresheaf_map {p q : (SingleObj M)ᵒᵖ} (f : p ⟶ q) (x : A) :
    (invActionPresheaf A φ).map f x = (φ (f.unop : M))⁻¹ • x := rfl

variable [MulAction M A]

/-- Reading an arrow of `∫(invActionPresheaf)` backwards is the action condition. -/
private theorem smul_eq_of_inv_smul_eq (hφ : ∀ (m : M) (x : A), m • x = φ m • x) {m : M} {x y : A}
    (h : (φ m)⁻¹ • y = x) : m • x = y := by
  rw [hφ, ← h, smul_smul, mul_inv_cancel, one_smul]

/-- The comparison functor: an arrow of `∫P`, read backwards, is its own label. -/
def toActionCategory (hφ : ∀ (m : M) (x : A), m • x = φ m • x) :
    ((invActionPresheaf A φ).Elements)ᵒᵖ ⥤ ActionCategory M A where
  obj p := ActionCategory.objEquiv M A p.unop.2
  map {_ _} f := ⟨(f.unop.val.unop : M),
    smul_eq_of_inv_smul_eq A φ hφ (m := (f.unop.val.unop : M)) f.unop.property⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- The inverse comparison. -/
def ofActionCategory (hφ : ∀ (m : M) (x : A), m • x = φ m • x) :
    ActionCategory M A ⥤ ((invActionPresheaf A φ).Elements)ᵒᵖ where
  obj x := op ⟨op (SingleObj.star M), x.back⟩
  map {x y} f := (CategoryOfElements.homMk
      (F := invActionPresheaf A φ) ⟨op (SingleObj.star M), y.back⟩
      ⟨op (SingleObj.star M), x.back⟩ (op (ActionCategory.label f)) (by
        change (φ (ActionCategory.label f))⁻¹ • y.back = x.back
        rw [inv_smul_eq_iff, ← hφ]
        exact (ActionCategory.label_smul f).symm)).op
  map_id _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

/-- **`(∫P)ᵒᵖ` is the action category**, for `P` the presheaf a group-valued action supplies. -/
def elementsOpEquivActionCategory (hφ : ∀ (m : M) (x : A), m • x = φ m • x) :
    ((invActionPresheaf A φ).Elements)ᵒᵖ ≌ ActionCategory M A where
  functor := toActionCategory A φ hφ
  inverse := ofActionCategory A φ hφ
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := (Category.comp_id _).trans ((toActionCategory A φ hφ).map_id X)

end InvAction

/-! ### Restricting the base of a category of elements -/

namespace CategoryOfElements

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Base transport is an equivalence** as soon as the base functor is fully faithful and every
object carrying an element is in its essential image. -/
theorem isEquivalence_pre (P : C ⥤ Type w) (G : D ⥤ C) [G.Full] [G.Faithful]
    (hcov : ∀ c : C, P.obj c → ∃ d : D, Nonempty (G.obj d ≅ c)) :
    (pre P G).IsEquivalence := by
  haveI : (pre P G).Faithful :=
    ⟨fun h => Subtype.ext (G.map_injective (congrArg Subtype.val h))⟩
  haveI : (pre P G).Full :=
    ⟨fun {x y} k => ⟨⟨G.preimage k.val, by
      change P.map (G.map (G.preimage k.val)) x.2 = y.2
      rw [G.map_preimage]
      exact k.property⟩, CategoryOfElements.ext _ _ _ (G.map_preimage k.val)⟩⟩
  haveI : (pre P G).EssSurj := ⟨fun z => by
    obtain ⟨d, ⟨e⟩⟩ := hcov z.1 z.2
    refine ⟨⟨d, P.map e.inv z.2⟩, ⟨CategoryOfElements.isoMk _ _ e ?_⟩⟩
    change P.map e.hom (P.map e.inv z.2) = z.2
    rw [← P.map_comp_apply, e.inv_hom_id, P.map_id_apply]⟩
  exact { }

end CategoryOfElements

end CategoryTheory
