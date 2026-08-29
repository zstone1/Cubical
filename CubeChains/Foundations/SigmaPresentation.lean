import CubeChains.Foundations.ElementsPresentation
import CubeChains.Foundations.LocalizationSigma

/-!
# Foundations/SigmaPresentation — presentations add up over a coproduct

The free category on a coproduct of quivers is the coproduct of the free categories, and a
coproduct of quotients is the quotient by the summandwise relation.  Hence a presentation of each
summand presents `Σ i, C i` — and, taking opposites summandwise, `(Σ i, C i)ᵒᵖ`.
-/

universe w v u

open CategoryTheory Quiver

namespace CategoryTheory.Sigma

/-! ## The coproduct quiver -/

variable {I : Type w} {V : I → Type u}

/-- The coproduct of a family of quivers.  A type synonym: a summand may carry a category of its
own, whose `Sigma` structure is a different quiver on the same type. -/
def Quiv (V : I → Type u) : Type max w u := Σ i, V i

namespace Quiv

variable [∀ i, Quiver.{v} (V i)]

/-- The vertex `x` of the `i`-th summand. -/
abbrev mk (i : I) (x : V i) : Quiv V := ⟨i, x⟩

/-- An edge of the coproduct quiver is an edge of one summand. -/
inductive Hom : Quiv V → Quiv V → Type max w v u
  | mk {i : I} {x y : V i} : (x ⟶ y) → Hom (mk i x) (mk i y)

instance : Quiver (Quiv V) := ⟨Hom⟩

/-- The `i`-th summand, as a subquiver. -/
@[simps] def incl (i : I) : V i ⥤q Quiv V where
  obj x := mk i x
  map e := Hom.mk e

end Quiv

/-! ## Paths -/

variable [∀ i, Quiver.{v} (V i)]

/-- A path of one summand, as a path of the coproduct quiver. -/
def descPaths : (Σ i, Paths (V i)) ⥤ Paths (Quiv V) :=
  Sigma.desc fun i => Paths.lift ((Quiv.incl i).comp (Paths.of (Quiv V)))

/-- A path of the coproduct quiver stays in one summand. -/
def toSigmaPaths : Paths (Quiv V) ⥤ (Σ i, Paths (V i)) :=
  Paths.lift
    { obj := fun p => ⟨p.1, p.2⟩
      map := fun {_ _} e => match e with | Quiv.Hom.mk f => Sigma.SigmaHom.mk f.toPath }

theorem descPaths_toSigmaPaths : (descPaths (V := V)) ⋙ toSigmaPaths = 𝟭 _ :=
  Sigma.functor_ext fun _ => Paths.ext_functor rfl fun _ _ _ => rfl

theorem toSigmaPaths_descPaths : (toSigmaPaths (V := V)) ⋙ descPaths = 𝟭 _ :=
  Paths.ext_functor rfl fun _ _ e => by obtain ⟨_⟩ := e; rfl

/-- **The free category on a coproduct of quivers is the coproduct of the free categories.** -/
noncomputable def pathsEquiv : (Σ i, Paths (V i)) ≌ Paths (Quiv V) :=
  .mk descPaths toSigmaPaths (eqToIso descPaths_toSigmaPaths.symm)
    (eqToIso toSigmaPaths_descPaths)

instance : (toSigmaPaths (V := V)).IsEquivalence :=
  inferInstanceAs (pathsEquiv (V := V)).inverse.IsEquivalence

theorem toSigmaPaths_obj_surjective :
    Function.Surjective (toSigmaPaths (V := V)).obj := fun p => ⟨⟨p.1, p.2⟩, rfl⟩

/-! ## Quotients -/

variable {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- The summands' relations, on the coproduct. -/
def homRel (r : ∀ i, HomRel (C i)) : HomRel (Σ i, C i) := fun _ _ f g =>
  match f, g with | SigmaHom.mk f', SigmaHom.mk g' => r _ f' g'

variable (r : ∀ i, HomRel (C i))

@[simp] theorem homRel_mk {i : I} {x y : C i} (f g : x ⟶ y) :
    homRel r (SigmaHom.mk f) (SigmaHom.mk g) ↔ r i f g := Iff.rfl

/-- The quotients of the summands, assembled. -/
def quotientDesc : (Σ i, Quotient (r i)) ⥤ Quotient (homRel r) :=
  Sigma.desc fun i =>
    Quotient.lift (r i) (Sigma.incl i ⋙ Quotient.functor (homRel r))
      fun _ _ _ _ h => Quotient.sound _ h

/-- …and its inverse, the summandwise quotient map. -/
def quotientLift : Quotient (homRel r) ⥤ (Σ i, Quotient (r i)) :=
  Quotient.lift _ (Sigma.Functor.sigma' fun i => Quotient.functor (r i)) <| by
    rintro _ _ ⟨f⟩ ⟨g⟩ h
    exact congrArg SigmaHom.mk (Quotient.sound _ h)

theorem quotientDesc_lift : quotientDesc r ⋙ quotientLift r = 𝟭 _ :=
  Sigma.functor_ext fun i => Quotient.lift_unique' (r i) _ _ rfl

theorem quotientLift_desc : quotientLift r ⋙ quotientDesc r = 𝟭 _ :=
  Quotient.lift_unique' _ _ _ (Sigma.functor_ext fun _ => rfl)

/-- **A coproduct of quotients is the quotient by the summandwise relation.** -/
noncomputable def quotientEquiv : (Σ i, Quotient (r i)) ≌ Quotient (homRel r) :=
  .mk (quotientDesc r) (quotientLift r) (eqToIso (quotientDesc_lift r).symm)
    (eqToIso (quotientLift_desc r))

/-! ## Opposites -/

/-- The coproduct of the opposites, in the opposite of the coproduct. -/
def opDesc : (Σ i, (C i)ᵒᵖ) ⥤ (Σ i, C i)ᵒᵖ := Sigma.desc fun i => (Sigma.incl i).op

instance : (opDesc (C := C)).Faithful where
  map_injective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨g⟩ h
    obtain rfl : f = g :=
      Quiver.Hom.unop_inj ((Sigma.incl i).map_injective (Quiver.Hom.op_inj h))
    rfl

instance : (opDesc (C := C)).Full where
  map_surjective := by
    rintro ⟨i, ⟨X⟩⟩ ⟨j, ⟨Y⟩⟩ ⟨⟨f⟩⟩
    exact ⟨SigmaHom.mk (Quiver.Hom.op f), rfl⟩

instance : (opDesc (C := C)).EssSurj where
  mem_essImage Y := ⟨⟨Y.unop.1, Opposite.op Y.unop.2⟩, ⟨Iso.refl _⟩⟩

instance : (opDesc (C := C)).IsEquivalence where

/-- **Opposites commute with coproducts.** -/
noncomputable def opEquiv : (Σ i, (C i)ᵒᵖ) ≌ (Σ i, C i)ᵒᵖ := opDesc.asEquivalence

/-! ## The presentation -/

/-- The summands' relations, read on paths of the coproduct quiver. -/
def pathRel (r : ∀ i, HomRel (Paths (V i))) : HomRel (Paths (Quiv V)) :=
  (toSigmaPaths (V := V)).pullbackRel (homRel r)

/-- **A presentation of each summand presents the coproduct.** -/
noncomputable def presentation (r : ∀ i, HomRel (Paths (V i))) :
    Quotient (pathRel r) ≌ Σ i, Quotient (r i) :=
  (quotientPullbackEquiv _ _ toSigmaPaths_obj_surjective).trans (quotientEquiv r).symm

end CategoryTheory.Sigma
