import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Machinery/Presentation/Elements — a presented base presents the total category

`∫P` over a presented `C` is presented by the **total quiver** — 0-cells the elements, 1-cells the
base's generators acting on one, 2-cells the base's relations read on projected words.  Two halves:
the projection of generating quivers is a covering, so words lift uniquely
(`Prefunctor.pathStar_bijective`); and a relation imposed downstairs imposes exactly its lifts
upstairs (`gen_onElements`), for which the presheaf must respect the relation.

`HomRel` binds its objects strictly implicitly, so `Relation.EqvGen` cannot eat it directly:
`HomRel.Gen` is the hom-set-at-a-time spelling everything here uses.
-/

universe w' w v u

namespace CategoryTheory

open CategoryOfElements

/-! ## The congruence a relation generates -/

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

end Fibration

/-! ## Reflecting a congruence along an isomorphism of categories -/

section Pullback

variable {A : Type u} [Category.{v} A] {A' : Type w} [Category.{w'} A']

/-- A hom relation pulled back along a functor. -/
def Functor.pullbackRel (F : A ⥤ A') (s : HomRel A') : HomRel A :=
  fun _ _ f g => s (F.map f) (F.map g)

variable (F : A ⥤ A') [F.Full] [F.Faithful] (s : HomRel A')
  (hmid : ∀ {a b : A} {X : A'}, (F.obj a ⟶ X) → (X ⟶ F.obj b) → ∃ a', F.obj a' = X)

include hmid in
private theorem gen_pullbackRel_aux {a b : A} :
    ∀ {u v : F.obj a ⟶ F.obj b}, HomRel.Gen s u v →
      ∀ (f g : a ⟶ b), F.map f = u → F.map g = v →
        HomRel.Gen (F.pullbackRel s) f g := by
  intro u v h
  induction h with
  | rel _ _ huv =>
      obtain ⟨X, Y, x, m₁, m₂, y, hm⟩ := huv
      obtain ⟨X, rfl⟩ := hmid x (m₁ ≫ y)
      obtain ⟨Y, rfl⟩ := hmid (x ≫ m₁) y
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

include hmid in
/-- **A fully faithful functor reflects the congruence generated by a relation**, provided every
object factoring an arrow between images is itself an image (`hmid`) — surjectivity on objects is
the special case, and convexity of the image is the general one. -/
theorem gen_pullbackRel {a b : A} {f g : a ⟶ b} (h : HomRel.Gen s (F.map f) (F.map g)) :
    HomRel.Gen (F.pullbackRel s) f g :=
  gen_pullbackRel_aux F s hmid h f g rfl rfl

end Pullback


/-! ## The total quiver of a presentation -/

namespace Presentation

variable {C : Type u} [Category.{v} C] (p : Presentation C) (F : C ⥤ Type w')

/-- **The cells of `∫F`**: a 0-cell carrying an element, and a 1-cell carrying it on. -/
def elementsGens : Gens F.Elements where
  V := Σ x : p.V, F.obj (p.ob x)
  ob z := ⟨p.ob z.1, z.2⟩
  Gen z z' := {e : p.Gen z.1 z'.1 // F.map (p.arrow e) z.2 = z'.2}
  arrow e := ⟨p.arrow e.1, e.2⟩

/-- The generating quiver of `∫F` lies over that of `C`. -/
def elementsProj : GenObj (p.elementsGens F).Gen ⥤q GenObj p.Gen where
  obj x := ⟨x.as.1⟩
  map e := e.1

/-- **A lifted word spells the cartesian lift of the word it projects to.** -/
theorem val_eval {X Y : GenObj (p.elementsGens F).Gen} (R : Quiver.Path X Y) :
    ((p.elementsGens F).eval.map R).val = p.toGens.eval.map ((p.elementsProj F).mapPath R) := by
  induction R with
  | nil => rfl
  | cons R e ih =>
      rw [Gens.eval_cons, comp_val, ih, Prefunctor.mapPath_cons, Gens.eval_cons]
      rfl

/-- **A base word lifts, from any element over its source.**  Its target is forced: the covering
is discrete, so the lift is the sequence of cartesian lifts. -/
theorem exists_lift {a : p.V} (t : F.obj (p.ob a)) :
    ∀ {z : GenObj p.Gen} (P : Quiver.Path (p.toGens.pt a) z) (s : F.obj (p.ob z.as)),
      F.map (p.toGens.eval.map P) t = s →
        ∃ R : Quiver.Path ((p.elementsGens F).pt ⟨a, t⟩) ((p.elementsGens F).pt ⟨z.as, s⟩),
          (p.elementsProj F).mapPath R = P := by
  intro z P
  induction P with
  | nil =>
      intro s hs
      obtain rfl : t = s := by simpa using hs
      exact ⟨Quiver.Path.nil, rfl⟩
  | @cons y z P e ih =>
      intro s hs
      obtain ⟨R, hR⟩ := ih (F.map (p.toGens.eval.map P) t) rfl
      refine ⟨R.cons ⟨e, ?_⟩, ?_⟩
      · rw [← hs, Gens.eval_cons]; exact (Functor.map_comp_apply F _ _ t).symm
      · rw [Prefunctor.mapPath_cons, hR]; rfl

/-- The projection is a covering: a base generator and a source element determine the target. -/
theorem elementsProj_star_injective (x : GenObj (p.elementsGens F).Gen) :
    Function.Injective ((p.elementsProj F).star x) := by
  rintro ⟨⟨⟨c₁, t₁⟩⟩, e₁, h₁⟩ ⟨⟨⟨c₂, t₂⟩⟩, e₂, h₂⟩ h
  obtain ⟨hc, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : c₁ = c₂ := congrArg GenObj.as hc
  obtain rfl : e₁ = e₂ := eq_of_heq he
  obtain rfl : t₁ = t₂ := h₁.symm.trans h₂
  rfl

theorem elementsTotal_prop {X Y : GenObj (p.elementsGens F).Gen} (R : Quiver.Path X Y) :
    (p.toGens.eval ⋙ F).map ((p.elementsProj F).mapPath R) X.as.2 = Y.as.2 := by
  have h := ((p.elementsGens F).eval.map R).property
  rwa [val_eval] at h

/-- **Words of the total quiver are morphisms of elements over the base's word category.** -/
def elementsTotal : Paths (GenObj (p.elementsGens F).Gen) ⥤ (p.toGens.eval ⋙ F).Elements where
  obj X := ⟨⟨X.as.1⟩, X.as.2⟩
  map {_ _} R := ⟨(p.elementsProj F).mapPath R, elementsTotal_prop p F R⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext (Prefunctor.mapPath_comp _ _ _)

theorem elementsTotal_obj_surjective : Function.Surjective (p.elementsTotal F).obj :=
  fun Y => ⟨⟨⟨Y.1.as, Y.2⟩⟩, rfl⟩

instance : (p.elementsTotal F).Faithful where
  map_injective {X Y} {R₁ R₂} h := by
    have hs : (p.elementsProj F).pathStar X ⟨Y, R₁⟩ = (p.elementsProj F).pathStar X ⟨Y, R₂⟩ :=
      Sigma.ext rfl (heq_of_eq (congrArg Subtype.val h))
    exact eq_of_heq (Sigma.mk.inj_iff.mp
      ((p.elementsProj F).pathStar_injective (elementsProj_star_injective p F) X hs)).2

instance : (p.elementsTotal F).Full where
  map_surjective {X Y} f := by
    obtain ⟨R, hR⟩ := exists_lift p F X.as.2 f.val Y.as.2 f.property
    exact ⟨R, Subtype.ext hR⟩

/-! ## The presentation -/

/-- **A presentation of `C` presents `∫F`** — 0-cells a 0-cell carrying an element, 1-cells the
base's acting on it, 2-cells the base's read on projected words. -/
def elements : Presentation F.Elements where
  toGens := p.elementsGens F
  rel := (p.elementsTotal F).pullbackRel (HomRel.onElements p.rel (p.toGens.eval ⋙ F))
  sound h := Subtype.ext ((val_eval p F _).trans ((p.sound h).trans (val_eval p F _).symm))
  spans {x y} f := by
    set P := p.word (x := p.toGens.pt x.as.1) (y := p.toGens.pt y.as.1) f.val with hPdef
    have hval : p.toGens.eval.map P = f.val := by rw [hPdef]; exact p.eval_word _
    obtain ⟨R, hR⟩ := exists_lift p F x.as.2 P y.as.2 (by rw [hval]; exact f.property)
    exact ⟨R, Subtype.ext ((val_eval p F R).trans (by rw [hR]; exact hval))⟩
  complete {X Y} {R₁ R₂} h := by
    refine (HomRel.gen_iff_functor_map_eq _ _ _).mp
      (gen_pullbackRel (p.elementsTotal F) _ (fun _ _ => elementsTotal_obj_surjective p F _) ?_)
    refine gen_onElements (fun {_ _} {u v} hr t => ?_)
      ((HomRel.gen_iff_functor_map_eq p.rel _ _).mpr (p.complete ?_)) _ _ _
    · change F.map (p.toGens.eval.map u) t = F.map (p.toGens.eval.map v) t
      rw [p.sound hr]
    · exact (val_eval p F R₁).symm.trans ((congrArg Subtype.val h).trans (val_eval p F R₂))
  covers z := by
    obtain ⟨x, ⟨i⟩⟩ := p.covers z.1
    refine ⟨(p.elementsGens F).pt ⟨x.as, F.map i.inv z.2⟩,
      ⟨CategoryOfElements.isoMk _ _ i ?_⟩⟩
    change F.map i.hom (F.map i.inv z.2) = z.2
    rw [← Functor.map_comp_apply, i.inv_hom_id, F.map_id_apply]

end Presentation

end CategoryTheory
