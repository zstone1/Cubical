import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Machinery/Localization/PresentedLocalization — inverting some of the generators

A category presented by a quiver modulo relations, localized at some of its **generators**, is
presented by the same quiver with those generators formally inverted, modulo the same relations
plus the two inverse laws.

Nothing relates the inverted generators to the relations: adjoining an inverse never constrains an
existing arrow, and being a two-sided inverse is a property, not data.  The statement lives on
`Quotient rel` rather than on a category merely equivalent to it, because `fac` is an equality of
functors and those do not transport across an equivalence.
-/

universe w v u

namespace CategoryTheory

open Quiver

variable {V : Type u} [Quiver.{v} V]

/-! ## The quiver with some edges formally inverted -/

/-- An edge of the quiver with the `S`-edges formally inverted. -/
inductive InvEdge (S : ∀ ⦃a b : V⦄, (a ⟶ b) → Prop) : V → V → Type (max u v)
  | fwd {a b : V} (e : a ⟶ b) : InvEdge S a b
  | bwd {a b : V} (e : b ⟶ a) (he : S e) : InvEdge S a b

/-- The quiver with the `S`-edges formally inverted.  A structure, not a synonym: a synonym would
leak this `Quiver` instance back onto `V`. -/
structure InvQuiver (V : Type u) [Quiver.{v} V] (S : ∀ ⦃a b : V⦄, (a ⟶ b) → Prop) where
  /-- The underlying vertex. -/
  as : V

instance invQuiver (S : ∀ ⦃a b : V⦄, (a ⟶ b) → Prop) :
    Quiver.{max u v} (InvQuiver V S) := ⟨fun a b => InvEdge S a.as b.as⟩

variable (S : ∀ ⦃a b : V⦄, (a ⟶ b) → Prop)

/-- A vertex, read in the inverted quiver. -/
def toInv (a : V) : InvQuiver V S := ⟨a⟩

/-- A generator, as a forward edge. -/
def fwdE {a b : V} (e : a ⟶ b) : toInv S a ⟶ toInv S b := InvEdge.fwd e

/-- A chosen generator, as its formal inverse. -/
def bwdE {a b : V} (e : b ⟶ a) (he : S e) : toInv S a ⟶ toInv S b := InvEdge.bwd e he

/-- The inclusion of the original quiver. -/
def invPre : V ⥤q Paths (InvQuiver V S) where
  obj a := toInv S a
  map e := Hom.toPath (fwdE S e)

/-- The inclusion on path categories. -/
def invIncl : Paths V ⥤ Paths (InvQuiver V S) := Paths.lift (invPre S)

theorem invIncl_toPath {a b : V} (e : a ⟶ b) :
    (invIncl S).map (Hom.toPath e) = Hom.toPath (fwdE S e) :=
  Paths.lift_toPath _ _

variable (rel : HomRel (Paths V))

/-- The relations of the inverted presentation: the original ones, plus the two inverse laws. -/
inductive InvRel : HomRel (Paths (InvQuiver V S))
  | base {a b : V} {P Q : Path a b} (h : rel P Q) :
      InvRel ((invIncl S).map P) ((invIncl S).map Q)
  | hom_inv {a b : V} (e : a ⟶ b) (he : S e) :
      InvRel (Hom.toPath (fwdE S e) ≫ Hom.toPath (bwdE S e he))
        (Path.nil (a := toInv S a))
  | inv_hom {a b : V} (e : a ⟶ b) (he : S e) :
      InvRel (Hom.toPath (bwdE S e he) ≫ Hom.toPath (fwdE S e))
        (Path.nil (a := toInv S b))

/-- The presented category with the `S`-generators inverted. -/
abbrev InvQuot : Type u := Quotient (InvRel S rel)

/-- The comparison from the original presented category. -/
noncomputable def quotIncl : Quotient rel ⥤ InvQuot S rel :=
  Quotient.lift rel (invIncl S ⋙ Quotient.functor (InvRel S rel))
    fun _ _ _ _ h => Quotient.sound _ (InvRel.base h)

theorem functor_comp_quotIncl :
    Quotient.functor rel ⋙ quotIncl S rel = invIncl S ⋙ Quotient.functor (InvRel S rel) :=
  Quotient.lift_spec _ _ _

/-- The class inverted: the generators named by `S`. -/
def genProperty : MorphismProperty (Quotient rel) := fun x y f =>
  ∃ e : @Quiver.Hom V _ x.as y.as, S e ∧ f = (Quotient.functor rel).map (Hom.toPath e)

theorem quotIncl_map_gen {a b : V} (e : a ⟶ b) :
    (quotIncl S rel).map ((Quotient.functor rel).map (Hom.toPath e))
      = (Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)) := by
  change (invIncl S ⋙ Quotient.functor (InvRel S rel)).map (Hom.toPath e) = _
  rw [Functor.comp_map, invIncl_toPath]
  rfl

/-! ## `quotIncl` inverts the chosen generators -/

theorem isIso_fwd {a b : V} (e : a ⟶ b) (he : S e) :
    IsIso ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e))) :=
  ⟨(Quotient.functor (InvRel S rel)).map (Hom.toPath (bwdE S e he)),
    by rw [← (Quotient.functor (InvRel S rel)).map_comp]
       exact Quotient.sound _ (InvRel.hom_inv e he),
    by rw [← (Quotient.functor (InvRel S rel)).map_comp]
       exact Quotient.sound _ (InvRel.inv_hom e he)⟩

theorem quotIncl_inverts : (genProperty S rel).IsInvertedBy (quotIncl S rel) := by
  rintro x y f ⟨e, he, rfl⟩
  have h := isIso_fwd S rel e he
  rwa [← quotIncl_map_gen S rel e] at h

/-! ## The universal property -/

section Lift

variable {E : Type w} [Category.{max u v} E]
  (F : Quotient rel ⥤ E) (hF : (genProperty S rel).IsInvertedBy F)

/-- A `genProperty`-inverting functor, read on the inverted quiver. -/
noncomputable def liftPre : InvQuiver V S ⥤q E where
  obj a := F.obj ((Quotient.functor rel).obj a.as)
  map {_ _} e := match e with
    | InvEdge.fwd e => F.map ((Quotient.functor rel).map (Hom.toPath e))
    | InvEdge.bwd e he =>
        haveI := hF ((Quotient.functor rel).map (Hom.toPath e)) ⟨e, he, rfl⟩
        inv (F.map ((Quotient.functor rel).map (Hom.toPath e)))

/-- …and on paths. -/
noncomputable def liftPaths : Paths (InvQuiver V S) ⥤ E := Paths.lift (liftPre S rel F hF)

theorem liftPaths_fwd {a b : V} (e : a ⟶ b) :
    (liftPaths S rel F hF).map (fwdE S e).toPath
      = F.map ((Quotient.functor rel).map (Hom.toPath e)) :=
  Paths.lift_toPath _ _

theorem liftPaths_bwd {a b : V} (e : a ⟶ b) (he : S e) :
    haveI := hF ((Quotient.functor rel).map (Hom.toPath e)) ⟨e, he, rfl⟩
    (liftPaths S rel F hF).map (Hom.toPath (bwdE S e he))
      = inv (F.map ((Quotient.functor rel).map (Hom.toPath e))) :=
  Paths.lift_toPath _ _

theorem liftPaths_map_path {a b : V} (P : Path a b) :
    (liftPaths S rel F hF).map ((invIncl S).map P)
      = F.map ((Quotient.functor rel).map P) := by
  induction P with
  | nil =>
      rw [show (invIncl S).map (Path.nil (a := a)) = Path.nil from (invIncl S).map_id a,
        show (Quotient.functor rel).map (Path.nil (a := a)) = 𝟙 _ from
          (Quotient.functor rel).map_id a, F.map_id]
      exact (liftPaths S rel F hF).map_id _
  | cons P e ih =>
      show (liftPaths S rel F hF).map ((invIncl S).map (P ≫ Hom.toPath e))
        = F.map ((Quotient.functor rel).map (P ≫ Hom.toPath e))
      rw [(invIncl S).map_comp, (liftPaths S rel F hF).map_comp, ih, invIncl_toPath,
        (Quotient.functor rel).map_comp, F.map_comp]
      exact congrArg (fun t => F.map ((Quotient.functor rel).map P) ≫ t)
        (liftPaths_fwd S rel F hF e)

theorem liftPaths_invIncl : invIncl S ⋙ liftPaths S rel F hF = Quotient.functor rel ⋙ F :=
  Functor.ext (fun _ => rfl) fun _ _ P =>
    (liftPaths_map_path S rel F hF P).trans
      ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The lift, on the quotient. -/
noncomputable def liftInv : InvQuot S rel ⥤ E := by
  refine Quotient.lift (InvRel S rel) (liftPaths S rel F hF) ?_
  intro x y P Q h
  induction h with
  | base h₀ =>
      rw [liftPaths_map_path, liftPaths_map_path]
      exact congrArg F.map (Quotient.sound rel h₀)
  | @hom_inv a b e he =>
      have hi : IsIso (F.map ((Quotient.functor rel).map (Hom.toPath e))) :=
        hF ((Quotient.functor rel).map (Hom.toPath e)) ⟨e, he, rfl⟩
      rw [Functor.map_comp, liftPaths_fwd S rel F hF e, liftPaths_bwd S rel F hF e he,
        show (liftPaths S rel F hF).map (Path.nil (a := toInv S a)) = 𝟙 _ from
          (liftPaths S rel F hF).map_id _]
      exact @IsIso.hom_inv_id _ _ _ _ _ hi
  | @inv_hom a b e he =>
      have hi : IsIso (F.map ((Quotient.functor rel).map (Hom.toPath e))) :=
        hF ((Quotient.functor rel).map (Hom.toPath e)) ⟨e, he, rfl⟩
      rw [Functor.map_comp, liftPaths_bwd S rel F hF e he, liftPaths_fwd S rel F hF e,
        show (liftPaths S rel F hF).map (Path.nil (a := toInv S b)) = 𝟙 _ from
          (liftPaths S rel F hF).map_id _]
      exact @IsIso.inv_hom_id _ _ _ _ _ hi

theorem functor_comp_liftInv :
    Quotient.functor (InvRel S rel) ⋙ liftInv S rel F hF = liftPaths S rel F hF :=
  Quotient.lift_spec _ _ _

theorem quotIncl_comp_liftInv : quotIncl S rel ⋙ liftInv S rel F hF = F := by
  have hrel : ∀ (x y : Paths V) (f₁ f₂ : x ⟶ y), rel f₁ f₂ →
      (Quotient.functor rel ⋙ F).map f₁ = (Quotient.functor rel ⋙ F).map f₂ :=
    fun _ _ _ _ h => congrArg F.map (Quotient.sound rel h)
  have key : Quotient.functor rel ⋙ (quotIncl S rel ⋙ liftInv S rel F hF)
      = Quotient.functor rel ⋙ F := by
    rw [← Functor.assoc, functor_comp_quotIncl, Functor.assoc, functor_comp_liftInv,
      liftPaths_invIncl]
  exact (Quotient.lift_unique rel _ hrel _ key).trans
    (Quotient.lift_unique rel _ hrel _ rfl).symm

end Lift

/-! ## Uniqueness -/

section Uniq

variable {E : Type w} [Category.{max u v} E] (F₁ F₂ : InvQuot S rel ⥤ E)

private theorem map_bwd_eq_inv (G : InvQuot S rel ⥤ E) {a b : V} (e : a ⟶ b) (he : S e) :
    haveI : IsIso (G.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)))) :=
      haveI := isIso_fwd S rel e he; Functor.map_isIso _ _
    G.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (bwdE S e he)))
      = inv (G.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)))) := by
  haveI := isIso_fwd S rel e he
  haveI : IsIso (G.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)))) :=
    Functor.map_isIso _ _
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [← G.map_comp, ← (Quotient.functor (InvRel S rel)).map_comp,
    Quotient.sound _ (InvRel.hom_inv e he),
    show (Quotient.functor (InvRel S rel)).map (Path.nil (a := toInv S a)) = 𝟙 _ from
      (Quotient.functor (InvRel S rel)).map_id _,
    G.map_id]

theorem uniq_of_comp (h : quotIncl S rel ⋙ F₁ = quotIncl S rel ⋙ F₂) : F₁ = F₂ := by
  have hobj : ∀ a : InvQuiver V S,
      (Quotient.functor (InvRel S rel) ⋙ F₁).obj a
        = (Quotient.functor (InvRel S rel) ⋙ F₂).obj a :=
    fun a => Functor.congr_obj h ((Quotient.functor rel).obj a.as)
  have hfwd : ∀ {a b : V} (e : a ⟶ b),
      F₁.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)))
        = eqToHom (hobj (toInv S a)) ≫
          F₂.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (fwdE S e)))
            ≫ eqToHom (hobj (toInv S b)).symm := by
    intro a b e
    have h1 := Functor.congr_hom h ((Quotient.functor rel).map (Hom.toPath e))
    rw [Functor.comp_map, Functor.comp_map, quotIncl_map_gen] at h1
    exact h1
  have hpaths : Quotient.functor (InvRel S rel) ⋙ F₁ = Quotient.functor (InvRel S rel) ⋙ F₂ := by
    refine Paths.ext_functor (funext hobj) ?_
    rintro a b (e | ⟨e, he⟩)
    · change F₁.map _ = _ ≫ F₂.map _ ≫ _
      exact hfwd e
    · haveI := isIso_fwd S rel e he
      haveI i₁ : IsIso (F₁.map ((Quotient.functor (InvRel S rel)).map
        (Hom.toPath (fwdE S e)))) := Functor.map_isIso _ _
      haveI i₂ : IsIso (F₂.map ((Quotient.functor (InvRel S rel)).map
        (Hom.toPath (fwdE S e)))) := Functor.map_isIso _ _
      show F₁.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (bwdE S e he)))
          = eqToHom (hobj a) ≫
            F₂.map ((Quotient.functor (InvRel S rel)).map (Hom.toPath (bwdE S e he)))
              ≫ eqToHom (hobj b).symm
      rw [map_bwd_eq_inv S rel F₁ e he, map_bwd_eq_inv S rel F₂ e he]
      rw [IsIso.eq_inv_comp, ← Category.assoc, ← Category.assoc, IsIso.eq_comp_inv]
      rw [hfwd e]
      simp
  exact (Quotient.lift_unique (InvRel S rel) _
      (fun _ _ _ _ hr => congrArg F₁.map (Quotient.sound _ hr)) _ rfl).trans
    (Quotient.lift_unique (InvRel S rel) _
      (fun _ _ _ _ hr => congrArg F₁.map (Quotient.sound _ hr)) _ hpaths.symm).symm

end Uniq

/-- **The strict universal property**: inverting the chosen generators is the localization. -/
noncomputable def strictUniversalProperty (E : Type w) [Category.{max u v} E] :
    Localization.StrictUniversalPropertyFixedTarget (quotIncl S rel) (genProperty S rel) E where
  inverts := quotIncl_inverts S rel
  lift F hF := liftInv S rel F hF
  fac F hF := quotIncl_comp_liftInv S rel F hF
  uniq F₁ F₂ h := uniq_of_comp S rel F₁ F₂ h

/-- **A presented category localized at some of its generators** is presented by the same quiver
with those generators formally inverted, modulo the same relations plus the inverse laws. -/
theorem isLocalization_quotIncl :
    (quotIncl S rel).IsLocalization (genProperty S rel) :=
  Functor.IsLocalization.mk' _ _ (strictUniversalProperty S rel _)
    (strictUniversalProperty S rel _)

/-- …as an equivalence with the abstract localization. -/
noncomputable def quotientEquivLocalization :
    (genProperty S rel).Localization ≌ InvQuot S rel :=
  haveI := isLocalization_quotIncl S rel
  Localization.equivalenceFromModel (quotIncl S rel) (genProperty S rel)

end CategoryTheory
