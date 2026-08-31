import CubeChains.Machinery.Localization.FibrationLocalize
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Machinery/Localization/ElementsPresentation — a presented base presents the total category

`∫P` over a presented base is presented by the **total quiver** — vertices the elements, edges the
base's generators acting on them — modulo the base's own relations, read on projected paths.
Two halves: the total quiver's projection is a covering, so paths lift uniquely
(`Prefunctor.pathStar_bijective`); and a relation imposed downstairs imposes exactly its lifts
upstairs (`gen_onElements`), for which the presheaf must respect the relation.

`HomRel` binds its objects strictly implicitly, so `Relation.EqvGen` cannot eat it directly:
`HomRel.Gen` is the hom-set-at-a-time spelling everything here uses.
-/

universe w v u v' u'

namespace CategoryTheory

open CategoryOfElements

/-- Two arrows of `C` that become equal in `Quotient r`. -/
abbrev HomRel.Gen {C : Type u} [Category.{v} C] (r : HomRel C) {X Y : C} (f g : X ⟶ Y) : Prop :=
  Relation.EqvGen (@HomRel.CompClosure C _ r X Y) f g

theorem HomRel.gen_iff_functor_map_eq {C : Type u} [Category.{v} C] (r : HomRel C) {X Y : C}
    (f g : X ⟶ Y) :
    HomRel.Gen r f g ↔ (Quotient.functor r).map f = (Quotient.functor r).map g :=
  (Quotient.functor_homRel_eq_compClosure_eqvGen r f g).symm

/-! ## Relations lift along a discrete fibration -/

section Fibration

variable {C : Type u} [Category.{v} C] {G : C ⥤ Type w}

/-- `r`, read on the category of elements: the same relation on the underlying arrows. -/
def HomRel.onElements (r : HomRel C) (G : C ⥤ Type w) : HomRel G.Elements :=
  fun _ _ f g => r f.val g.val

variable {r : HomRel C}

/-- A presheaf respecting `r` respects the congruence `r` generates. -/
theorem map_eq_of_gen (hG : ∀ {a b : C} {f g : a ⟶ b}, r f g → ∀ x, G.map f x = G.map g x)
    {a b : C} {u v : a ⟶ b} (h : HomRel.Gen r u v) (x : G.obj a) : G.map u x = G.map v x := by
  induction h with
  | rel _ _ huv =>
      obtain ⟨_, _, f, m₁, m₂, g, hm⟩ := huv
      simp only [Functor.map_comp_apply, hG hm]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The base's relations lift.**  A chain of `r`-moves between the underlying arrows of two
parallel morphisms of elements is the image of a chain upstairs: the cartesian lifts of an
`r`-related pair are parallel exactly because `G` respects `r`. -/
theorem gen_onElements (hG : ∀ {a b : C} {f g : a ⟶ b}, r f g → ∀ x, G.map f x = G.map g x)
    {p : G.Elements} {c : C} {u v : p.1 ⟶ c} (h : HomRel.Gen r u v) :
    ∀ (y : G.obj c) (hu : G.map u p.2 = y) (hv : G.map v p.2 = y),
      HomRel.Gen (HomRel.onElements r G) (⟨u, hu⟩ : p ⟶ ⟨c, y⟩) ⟨v, hv⟩ := by
  induction h with
  | rel _ _ huv =>
      obtain ⟨a, b, f, m₁, m₂, g, hm⟩ := huv
      intro y hu hv
      refine Relation.EqvGen.rel _ _ ?_
      have hz : G.map m₂ (G.map f p.2) = G.map m₁ (G.map f p.2) := (hG hm _).symm
      have hy : G.map g (G.map m₁ (G.map f p.2)) = y := by
        simpa only [Functor.map_comp_apply] using hu
      exact HomRel.CompClosure.intro (r := HomRel.onElements r G)
        (G.elementsMk a (G.map f p.2))
        (G.elementsMk b (G.map m₁ (G.map f p.2)))
        (homMk _ _ f rfl) (homMk _ _ m₁ rfl) (homMk _ _ m₂ hz)
        (homMk _ (G.elementsMk c y) g hy) hm
  | refl _ => intro y hu hv; exact Relation.EqvGen.refl _
  | symm _ _ _ ih => intro y hu hv; exact Relation.EqvGen.symm _ _ (ih y hv hu)
  | trans _ _ _ huv _ ih₁ ih₂ =>
      intro y hu hv
      have hmid : G.map _ p.2 = y := (map_eq_of_gen hG huv p.2).symm.trans hu
      exact Relation.EqvGen.trans _ _ _ (ih₁ y hu hmid) (ih₂ y hmid hv)

/-- The converse: a chain upstairs projects to a chain downstairs. -/
theorem gen_val {p q : G.Elements} {f g : p ⟶ q}
    (h : HomRel.Gen (HomRel.onElements r G) f g) : HomRel.Gen r f.val g.val := by
  induction h with
  | rel _ _ huv =>
      obtain ⟨_, _, x, m₁, m₂, y, hm⟩ := huv
      exact Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ x.val m₁.val m₂.val y.val hm)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end Fibration

/-! ## The base's quotient -/

section Descent

variable {C : Type u} [Category.{v} C] (r : HomRel C) (P : Quotient r ⥤ Type w)

/-- A presheaf on `Quotient r`, read on `C`. -/
abbrev basePsh : C ⥤ Type w := Quotient.functor r ⋙ P

theorem basePsh_respects {a b : C} {f g : a ⟶ b} (h : r f g) (x : (basePsh r P).obj a) :
    (basePsh r P).map f x = (basePsh r P).map g x := by
  rw [show (basePsh r P).map f = (basePsh r P).map g from congrArg P.map (Quotient.sound r h)]

/-- **`∫P` is `∫` of the base presheaf modulo the base's relations.** -/
def elementsQuotient : Quotient (HomRel.onElements r (basePsh r P)) ⥤ P.Elements :=
  Quotient.lift _ (pre P (Quotient.functor r))
    fun _ _ _ _ h => ext P _ _ (Quotient.sound r h)

instance : (elementsQuotient r P).Full where
  map_surjective {X Y} h := by
    obtain ⟨f, hf⟩ := Quot.exists_rep h.val
    have hp : (basePsh r P).map f X.as.2 = Y.as.2 := by
      change P.map ((Quotient.functor r).map f) X.as.2 = Y.as.2
      rw [show (Quotient.functor r).map f = h.val from hf]
      exact h.property
    exact ⟨(Quotient.functor _).map ⟨f, hp⟩, Subtype.ext hf⟩

instance : (elementsQuotient r P).Faithful where
  map_injective {_ Y} :=
    Quot.ind fun f => Quot.ind fun g => fun h =>
      Quot.eq.mpr (gen_onElements (basePsh_respects r P)
        (Quot.eq.mp (congrArg Subtype.val h)) Y.as.2 f.property g.property)

instance : (elementsQuotient r P).EssSurj where
  mem_essImage Y := ⟨⟨⟨Y.1.as, Y.2⟩⟩, ⟨Iso.refl _⟩⟩

instance : (elementsQuotient r P).IsEquivalence where

/-- `∫P ≌ ∫(base presheaf) / r`. -/
noncomputable def elementsQuotientEquiv :
    Quotient (HomRel.onElements r (basePsh r P)) ≌ P.Elements :=
  (elementsQuotient r P).asEquivalence

end Descent

/-! ## Transporting a quotient along an isomorphism of categories -/

section Pullback

variable {A : Type u} [Category.{v} A] {A' : Type u'} [Category.{v'} A']

/-- A hom relation pulled back along a functor. -/
def Functor.pullbackRel (F : A ⥤ A') (s : HomRel A') : HomRel A :=
  fun _ _ f g => s (F.map f) (F.map g)

variable (F : A ⥤ A') [F.Full] [F.Faithful] (s : HomRel A')
  (hobj : Function.Surjective F.obj)

include hobj in
private theorem gen_pullbackRel_aux {a b : A} :
    ∀ {u v : F.obj a ⟶ F.obj b}, HomRel.Gen s u v →
      ∀ (f g : a ⟶ b), F.map f = u → F.map g = v →
        HomRel.Gen (F.pullbackRel s) f g := by
  intro u v h
  induction h with
  | rel _ _ huv =>
      obtain ⟨X, Y, x, m₁, m₂, y, hm⟩ := huv
      obtain ⟨X, rfl⟩ := hobj X
      obtain ⟨Y, rfl⟩ := hobj Y
      obtain ⟨x, rfl⟩ := F.map_surjective x
      obtain ⟨m₁, rfl⟩ := F.map_surjective m₁
      obtain ⟨m₂, rfl⟩ := F.map_surjective m₂
      obtain ⟨y, rfl⟩ := F.map_surjective y
      intro f g hf hg
      obtain rfl : f = x ≫ m₁ ≫ y := F.map_injective (by simpa using hf)
      obtain rfl : g = x ≫ m₂ ≫ y := F.map_injective (by simpa using hg)
      exact Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ x m₁ m₂ y hm)
  | refl _ =>
      intro f g hf hg
      exact F.map_injective (hf.trans hg.symm) ▸ Relation.EqvGen.refl _
  | symm _ _ _ ih => intro f g hf hg; exact (ih g f hg hf).symm
  | trans _ v _ _ _ ih₁ ih₂ =>
      intro f g hf hg
      obtain ⟨m, hm⟩ := F.map_surjective v
      exact Relation.EqvGen.trans _ _ _ (ih₁ f m hf hm) (ih₂ m g hm hg)

include hobj in
/-- An isomorphism of categories reflects the congruence generated by a relation. -/
theorem gen_pullbackRel {a b : A} {f g : a ⟶ b} (h : HomRel.Gen s (F.map f) (F.map g)) :
    HomRel.Gen (F.pullbackRel s) f g :=
  gen_pullbackRel_aux F s hobj h f g rfl rfl

/-- The comparison of quotients along `F`. -/
def quotientPullback : Quotient (F.pullbackRel s) ⥤ Quotient s :=
  Quotient.lift _ (F ⋙ Quotient.functor s) fun _ _ _ _ h => Quotient.sound s h

instance : (quotientPullback F s).Full where
  map_surjective {X Y} h := by
    obtain ⟨h, rfl⟩ := Quot.exists_rep h
    obtain ⟨f, rfl⟩ := F.map_surjective h
    exact ⟨(Quotient.functor _).map f, rfl⟩

include hobj in
theorem quotientPullback_faithful : (quotientPullback F s).Faithful where
  map_injective {_ _} :=
    Quot.ind fun _ => Quot.ind fun _ => fun h =>
      Quot.eq.mpr (gen_pullbackRel F s hobj (Quot.eq.mp h))

omit [F.Full] [F.Faithful] in
include hobj in
theorem quotientPullback_essSurj : (quotientPullback F s).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, hX⟩ := hobj Y.as
    exact ⟨⟨X⟩, ⟨eqToIso (by obtain ⟨y⟩ := Y; exact congrArg Quotient.mk hX)⟩⟩

include hobj in
theorem quotientPullback_isEquivalence : (quotientPullback F s).IsEquivalence :=
  haveI := quotientPullback_faithful F s hobj
  haveI := quotientPullback_essSurj F s hobj
  { }

include hobj in
/-- **A quotient transports along an isomorphism of categories.** -/
noncomputable def quotientPullbackEquiv : Quotient (F.pullbackRel s) ≌ Quotient s :=
  haveI := quotientPullback_isEquivalence F s hobj
  (quotientPullback F s).asEquivalence

end Pullback

/-- Two spellings of one relation give one quotient — the identity on generators. -/
def quotientEqEquiv {C : Type u} [Category.{v} C] {r r' : HomRel C} (h : r = r') :
    Quotient r ≌ Quotient r' where
  functor := Quotient.lift _ (Quotient.functor r') fun _ _ _ _ hf => Quotient.sound _ (h ▸ hf)
  inverse := Quotient.lift _ (Quotient.functor r) fun _ _ _ _ hf => Quotient.sound _ (h ▸ hf)
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun {_ _} f => by
    obtain ⟨f, rfl⟩ := (Quotient.functor r).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun {_ _} f => by
    obtain ⟨f, rfl⟩ := (Quotient.functor r').map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp X := (Category.comp_id _).trans (Functor.map_id _ X)

/-! ## The total quiver

A discrete fibration over a free category is free. -/

section Total

variable {V : Type u} [Quiver.{v} V] (G : Paths V ⥤ Type w)

/-- The **total quiver**: vertices the elements, edges the base's edges acting on them. -/
def Total : Type max u w := Σ x : V, G.obj x

instance totalQuiver : Quiver.{v} (Total G) where
  Hom p q := {e : p.1 ⟶ q.1 // G.map (Quiver.Hom.toPath e) p.2 = q.2}

/-- The total quiver lies over the base quiver. -/
@[simps] def totalProj : Total G ⥤q V where
  obj p := p.1
  map e := e.1

/-- The element a lifted path lands on. -/
theorem map_mapPath {p q : Total G} (P : Quiver.Path p q) :
    G.map ((totalProj G).mapPath P) p.2 = q.2 := by
  induction P with
  | nil => exact G.map_id_apply _ _
  | cons P e ih =>
      rw [Prefunctor.mapPath_cons]
      change G.map ((totalProj G).mapPath P ≫ Quiver.Hom.toPath e.1) p.2 = _
      rw [Functor.map_comp_apply, ih]
      exact e.2

/-- **Paths of the total quiver are morphisms of elements.** -/
@[simps] def totalToElements : Paths (Total G) ⥤ G.Elements where
  obj p := p
  map P := ⟨(totalProj G).mapPath P, map_mapPath G P⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext (Prefunctor.mapPath_comp _ _ _)

/-- The projection is a covering: an edge and a source element determine the target. -/
theorem totalProj_star_bijective (p : Total G) :
    Function.Bijective ((totalProj G).star p) := by
  constructor
  · rintro ⟨⟨x₁, y₁⟩, e₁, h₁⟩ ⟨⟨x₂, y₂⟩, e₂, h₂⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl : e₁ = e₂ := eq_of_heq h
    obtain rfl : y₁ = y₂ := h₁.symm.trans h₂
    rfl
  · rintro ⟨x, e⟩
    exact ⟨⟨⟨x, G.map (Quiver.Hom.toPath e) p.2⟩, ⟨e, rfl⟩⟩, rfl⟩

instance : (totalToElements G).Faithful where
  map_injective {p q} {P₁ P₂} h := by
    have hs : (totalProj G).pathStar p ⟨q, P₁⟩ = (totalProj G).pathStar p ⟨q, P₂⟩ :=
      Sigma.ext rfl (heq_of_eq (congrArg Subtype.val h))
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      ((totalProj G).pathStar_injective (fun u => (totalProj_star_bijective G u).1) p hs)).2

instance : (totalToElements G).Full where
  map_surjective {p q} f := by
    obtain ⟨⟨q', P⟩, hP⟩ := (totalProj G).pathStar_surjective
      (fun u => (totalProj_star_bijective G u).2) p ⟨q.1, f.val⟩
    obtain ⟨q₁, q₂⟩ := q'
    obtain ⟨rfl, hP⟩ := Sigma.mk.inj_iff.mp hP
    have hval : (totalProj G).mapPath P = f.val := eq_of_heq hP
    obtain rfl : q₂ = q.2 :=
      (map_mapPath G P).symm.trans (by rw [hval]; exact f.property)
    exact ⟨P, Subtype.ext hval⟩

instance : (totalToElements G).EssSurj where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩

instance : (totalToElements G).IsEquivalence where

theorem totalToElements_obj_surjective :
    Function.Surjective (totalToElements G).obj := fun Y => ⟨Y, rfl⟩

end Total

/-! ## The theorem -/

section Presentation

variable {V : Type u} [Quiver.{v} V] (r : HomRel (Paths V)) (P : Quotient r ⥤ Type w)

/-- The relations of the total quiver: the base's relations, read on projected paths. -/
def totalRel : HomRel (Paths (Total (basePsh r P))) :=
  (totalToElements _).pullbackRel (HomRel.onElements r (basePsh r P))

theorem totalRel_iff {p q : Paths (Total (basePsh r P))} (P₁ P₂ : p ⟶ q) :
    totalRel r P P₁ P₂ ↔
      r ((totalProj (basePsh r P)).mapPath P₁) ((totalProj (basePsh r P)).mapPath P₂) :=
  Iff.rfl

/-- **A presentation of the base presents the category of elements**: generators the base's
generators acting on the fibre, relations the base's relations on the projected paths. -/
noncomputable def elementsPresentation : Quotient (totalRel r P) ≌ P.Elements :=
  (quotientPullbackEquiv (totalToElements (basePsh r P)) _
      (totalToElements_obj_surjective _)).trans (elementsQuotientEquiv r P)

/-- **A generator path lies over the base path it projects to** — the arrow of `∫P` it names is the
cartesian lift of that. -/
theorem val_elementsPresentation_map {p q : Paths (Total (basePsh r P))} (P₁ : p ⟶ q) :
    ((elementsPresentation r P).functor.map ((Quotient.functor (totalRel r P)).map P₁)).val
      = (Quotient.functor r).map ((totalProj (basePsh r P)).mapPath P₁) := rfl

end Presentation

end CategoryTheory
