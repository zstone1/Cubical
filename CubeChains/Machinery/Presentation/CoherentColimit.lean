import CubeChains.Machinery.Presentation.SliceColimit

/-!
# Machinery/Presentation/CoherentColimit — the naming is what `hP` asks for

`presentsSliceColimit` wants `(P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f`.  Split it:
the **morphism** half is free as soon as the localized slices are thin (`hP_of_obj`), and the
**object** half is a strictly natural choice of the slice object each 0-cell names — a `Naming`.
A colimit of polygraphs is a colimit of *cells*, so a 0-cell names one object of the target on the
nose; no thinness and no 3-cell weakens that, and a natural *isomorphism* `(P.map f).functor ⋙
(p d).E ≅ (p d').E ⋙ overMapLoc W f` is exactly `hP` with the naming removed.

`Naming.ofFullyFaithful` is how a naming is normally produced: an explicit invariant of the slice
that separates its objects up to isomorphism, evaluated on both sides.
-/

universe u

namespace CategoryTheory

namespace Presents

variable {P : Polygraph.{u, u, u}} {C : Type u} [Category.{u} C]

/-- **A presentation, renamed**: the same polygraph and the same equivalence class of comparison
functors, with the object map replaced by a chosen one. -/
def copyObj (p : Presents P C) (r : P.presented → C) (θ : ∀ a, p.E.obj a ≅ r a) : Presents P C :=
  ⟨p.E.copyObj r θ, Functor.isEquivalence_of_iso (p.E.isoCopyObj r θ)⟩

@[simp] theorem copyObj_obj (p : Presents P C) (r : P.presented → C) (θ : ∀ a, p.E.obj a ≅ r a)
    (a : P.presented) : (p.copyObj r θ).E.obj a = r a := rfl

end Presents

/-- **A poset-valued invariant turns a natural isomorphism into an equality of values.**  This is
what a chain of `Localization.uniq`s — which supplies only `compUniqFunctor`, a natural iso — can
still be read through: the comparison need not be upgraded where it lives (a localized slice is
thin, never skeletal), only after the invariant. -/
theorem Functor.obj_eq_of_natIso {A : Type*} [Category A] {B : Type*} [Category B]
    {Z : Type*} [PartialOrder Z] {F G : A ⥤ B} (S : B ⥤ Z) (e : F ≅ G) (a : A) :
    S.obj (F.obj a) = S.obj (G.obj a) :=
  le_antisymm (leOfHom (S.map (e.hom.app a))) (leOfHom (S.map (e.inv.app a)))

namespace Polygraph

open Limits

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))

/-- **In a thin slice, `hP` is its object half.**  Two parallel functors into a preorder agree as
soon as they agree on objects, so `Functor.ext`'s morphism obligation is `Subsingleton.elim`. -/
theorem hP_of_obj [∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization)]
    (hobj : ∀ {d' d : D} (f : d' ⟶ d) (a : (P.obj d').presented),
      (p d).E.obj ((P.map f).functor.obj a) = (overMapLoc W f).obj ((p d').E.obj a))
    {d' d : D} (f : d' ⟶ d) :
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f :=
  Functor.ext (hobj f) fun _ _ _ => Subsingleton.elim _ _

/-- **The colimit of the slice presentations presents `(∫X)[W⁻¹]`, from the object half alone.**
-/
noncomputable def presentsSliceColimitOfObj
    [∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization)]
    (hobj : ∀ {d' d : D} (f : d' ⟶ d) (a : (P.obj d').presented),
      (p d).E.obj ((P.map f).functor.obj a) = (overMapLoc W f).obj ((p d').E.obj a)) :
    Presents (colimit (elementsPoly X P))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  presentsSliceColimit X W p fun {_ _} f => hP_of_obj W p hobj f

/-- **Any presentation of the colimit names its 0-cells strictly naturally.**  A 0-cell of a copy
and its push-forward are *one* 0-cell of the colimit polygraph, so they name one object of whatever
category is presented: the strictness is a property of the colimit, not of the proof, and no
weakening of `hP` and no 2-cell datum removes it. -/
theorem Presents.colimNaming_natural {C : Type u} [Category.{u} C]
    (q : Presents (colimit (elementsPoly X P)) C)
    {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) (a : (P.obj (eltBase X c')).presented) :
    q.E.obj ((colimInclFun X P c).obj
        ((P.map ((CategoryOfElements.π X).leftOp.map u)).functor.obj a))
      = q.E.obj ((colimInclFun X P c').obj a) :=
  congrArg q.E.obj (Functor.congr_obj (colimInclFun_naturality X P u) a)

/-! ## The naming

Everything `hP` asks that thinness does not give: a slice object for each 0-cell, isomorphic to the
one its own presentation names, and pushed forward by `Over.map` on the nose. -/

/-- **A strictly natural naming of slice objects by 0-cells.** -/
structure Naming where
  /-- the slice object a 0-cell names -/
  obj : ∀ d : D, (P.obj d).presented → (W.over (X := d)).Localization
  /-- …the one its own presentation names -/
  iso : ∀ (d : D) (a : (P.obj d).presented), (p d).E.obj a ≅ obj d a
  /-- …and pushing the 0-cell pushes it -/
  push : ∀ {d' d : D} (f : d' ⟶ d) (a : (P.obj d').presented),
    obj d ((P.map f).functor.obj a) = (overMapLoc W f).obj (obj d' a)

namespace Naming

variable {X W p}

/-- The strict `hP` is a naming — the one that names nothing. -/
noncomputable def ofStrict (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f) : Naming W p where
  obj d := (p d).E.obj
  iso _ _ := Iso.refl _
  push f a := Functor.congr_obj (hP f) a

/-- **A naming from an invariant that separates the slice's objects up to isomorphism.**  `G d` is
typically explicit where `(p d).E` is not: the naming obligation then becomes a *computation* of
`G d` on both sides, and no comparison of opaque objects is needed. -/
noncomputable def ofFullyFaithful {E : D → Type u} [∀ d, Category.{u} (E d)]
    (G : ∀ d : D, (W.over (X := d)).Localization ⥤ E d)
    [∀ d, (G d).Full] [∀ d, (G d).Faithful]
    (obj : ∀ d : D, (P.obj d).presented → (W.over (X := d)).Localization)
    (hG : ∀ (d : D) (a : (P.obj d).presented), (G d).obj ((p d).E.obj a) = (G d).obj (obj d a))
    (push : ∀ {d' d : D} (f : d' ⟶ d) (a : (P.obj d').presented),
      obj d ((P.map f).functor.obj a) = (overMapLoc W f).obj (obj d' a)) :
    Naming W p where
  obj := obj
  iso d a := (G d).preimageIso (eqToIso (hG d a))
  push := push

variable (ν : Naming W p)

/-- The presentations, renamed. -/
noncomputable def presents (d : D) : Presents (P.obj d) ((W.over (X := d)).Localization) :=
  (p d).copyObj (ν.obj d) (ν.iso d)

/-- **The colimit of the slice presentations presents `(∫X)[W⁻¹]`, given a naming.**  The polygraph
is untouched — `elementsPoly X P` never sees a comparison functor — so this is the *same* colimit
`presentsSliceColimit` would present, reached without asking `(p d).E` for anything strict. -/
noncomputable def presentsColimit
    [∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization)] (X : Dᵒᵖ ⥤ Type u) :
    Presents (colimit (elementsPoly X P))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  presentsSliceColimitOfObj X W ν.presents fun {_ _} f a => ν.push f a

end Naming

end Polygraph

end CategoryTheory
