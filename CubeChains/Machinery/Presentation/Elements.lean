import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Machinery/Presentation/Elements — a presented base presents the total category

`∫F` over a presented `C` is presented by the **total quiver** — 0-cells the elements, 1-cells the
base's generators acting on one, 2-cells the base's read on projected words (`Polygraph.comap`).
Two halves: the projection of generating quivers is a discrete covering, so a word is pinned by its
projection (`Prefunctor.pathStar_injective`) and lifts from any element over its source
(`exists_lift`); and a relation imposed downstairs imposes exactly its lifts upstairs
(`gen_onElements`), for which the presheaf must respect the relation.

`HomRel` binds its objects strictly implicitly, so `Relation.EqvGen` cannot eat it directly:
`HomRel.Gen` is the hom-set-at-a-time spelling.
-/

universe w₂ w'' w' w v u'' u' u

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

/-- **The congruence is monotone in the relation** — the bridge between two spellings of the same
2-cells, which is all `comap_homRel_iff` gives. -/
theorem HomRel.Gen.mono {C : Type u} [Category.{v} C] {r s : HomRel C}
    (hrs : ∀ {X Y : C} {f g : X ⟶ Y}, r f g → s f g) {X Y : C} {f g : X ⟶ Y}
    (h : HomRel.Gen r f g) : HomRel.Gen s f g :=
  Relation.EqvGen.mono (fun _ _ hr => by
    obtain ⟨a, b, x, m₁, m₂, y, hm⟩ := hr
    exact HomRel.CompClosure.intro a b x m₁ m₂ y (hrs hm)) h

/-- A hom relation pulled back along a functor. -/
def Functor.pullbackRel {A : Type u} [Category.{v} A] {A' : Type u''} [Category.{w'} A']
    (F : A ⥤ A') (s : HomRel A') : HomRel A :=
  fun _ _ f g => s (F.map f) (F.map g)

/-! ## Relations lift along a discrete fibration

A relation on `C`, read on `∫G`, is its pullback along the projection. -/

section Fibration

variable {C : Type u} [Category.{v} C] {G : C ⥤ Type w} {r : HomRel C}

/-- A presheaf respecting `r` respects the congruence `r` generates: "acts alike on every element"
is already an equivalence, so the closure collapses. -/
theorem map_eq_of_gen (hG : ∀ {a b : C} {f g : a ⟶ b}, r f g → ∀ x, G.map f x = G.map g x)
    {a b : C} {u v : a ⟶ b} (h : HomRel.Gen r u v) (x : G.obj a) : G.map u x = G.map v x :=
  ConcreteCategory.congr_hom (HomRel.map_eq_of_gen r G
    (fun hm => ConcreteCategory.hom_ext _ _ (hG hm)) h) x

/-- **The base's relations lift.**  A chain of `r`-moves between the underlying arrows of two
parallel morphisms of elements is the image of a chain upstairs: the cartesian lifts of an
`r`-related pair are parallel exactly because `G` respects `r`. -/
theorem gen_onElements (hG : ∀ {a b : C} {f g : a ⟶ b}, r f g → ∀ x, G.map f x = G.map g x)
    {p : G.Elements} {c : C} {u v : p.1 ⟶ c} (h : HomRel.Gen r u v) :
    ∀ (y : G.obj c) (hu : G.map u p.2 = y) (hv : G.map v p.2 = y),
      HomRel.Gen ((CategoryOfElements.π G).pullbackRel r) (⟨u, hu⟩ : p ⟶ ⟨c, y⟩) ⟨v, hv⟩ := by
  induction h with
  | rel _ _ huv =>
      obtain ⟨a, b, f, m₁, m₂, g, hm⟩ := huv
      intro y hu hv
      refine Relation.EqvGen.rel _ _ ?_
      have hz : G.map m₂ (G.map f p.2) = G.map m₁ (G.map f p.2) := (hG hm _).symm
      have hy : G.map g (G.map m₁ (G.map f p.2)) = y := by
        simpa only [Functor.map_comp_apply] using hu
      exact HomRel.CompClosure.intro (r := (CategoryOfElements.π G).pullbackRel r)
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
  (F : A ⥤ A') [F.Full] [F.Faithful] (s : HomRel A')
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

/-- **Words of a comap agree in the presented category as soon as their projections are
congruent** — `comap_homRel_iff`, propagated along `HomRel.Gen`. -/
theorem Polygraph.comap_quot_map_eq_of_gen {P : Polygraph.{w, u', w₂}} {V : Type u''}
    {Gen : V → V → Type w''} (π : GenObj Gen ⥤q GenObj P.Gen) {x y : Paths (GenObj Gen)}
    {u v : x ⟶ y} (h : HomRel.Gen (π.pathsFunctor.pullbackRel P.homRel) u v) :
    (P.comap Gen π).quot.map u = (P.comap Gen π).quot.map v := by
  refine (HomRel.gen_iff_functor_map_eq (P.comap Gen π).homRel u v).mp (HomRel.Gen.mono ?_ h)
  intro _ _ f g hr
  exact (P.comap_homRel_iff Gen π f g).mpr hr

/-! ## The total polygraph of a presentation -/

namespace Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)

/-- **A comap's 2-cells hold in `C`.** -/
theorem comap_sound {V : Type u''} {Gen : V → V → Type w''} (π : GenObj Gen ⥤q GenObj P.Gen)
    {x y : GenObj Gen} (α : (P.comap Gen π).Rel x y) :
    p.eval.map (π.mapPath ((P.comap Gen π).src α))
      = p.eval.map (π.mapPath ((P.comap Gen π).tgt α)) :=
  p.sound' ((P.comap_homRel_iff Gen π _ _).mp ⟨α, rfl, rfl⟩)

/-- **Words agreeing in `C` are congruent** — completeness, before passing to the quotient, which
is the form every `comap` needs. -/
theorem gen_of_eval_eq {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : p.eval.map u = p.eval.map v) : HomRel.Gen P.homRel u v :=
  (HomRel.gen_iff_functor_map_eq P.homRel u v).mpr (p.E.map_injective h)

variable (F : C ⥤ Type w')

/-- **The 0-cells of `∫F`**: a 0-cell of `P` carrying an element. -/
abbrev elementsV : Type max u' w' := Σ x : P.V, F.obj (p.at' (P.pt x))

/-- **The 1-cells of `∫F`**: a 1-cell of `P`, carrying its element on. -/
abbrev elementsGen (z z' : p.elementsV F) : Type w :=
  {e : P.pt z.1 ⟶ P.pt z'.1 // F.map (p.arrow e) z.2 = z'.2}

/-- The generating quiver of `∫F` lies over that of `P`. -/
def elementsProj : GenObj (p.elementsGen F) ⥤q GenObj P.Gen where
  obj x := P.pt x.as.1
  map e := e.1

/-- **The cells of `∫F`** — `P`'s 2-cells, read on projected words. -/
def elementsPoly : Polygraph := P.comap (p.elementsGen F) (p.elementsProj F)

/-- …interpreted: a 1-cell is the cartesian lift of the arrow it names. -/
def elementsInterp : GenObj (p.elementsGen F) ⥤q F.Elements where
  obj z := ⟨p.at' (P.pt z.as.1), z.as.2⟩
  map e := ⟨p.arrow e.1, e.2⟩

/-- **A lifted word spells the cartesian lift of the word it projects to.** -/
theorem val_eval {X Y : GenObj (p.elementsGen F)} (R : Quiver.Path X Y) :
    ((Paths.lift (p.elementsInterp F)).map R).val
      = p.eval.map ((p.elementsProj F).mapPath R) :=
  (Paths.lift_comp_map (p.elementsInterp F) (CategoryOfElements.π F) R).trans
    (p.eval_mapPath (p.elementsProj F) R).symm

/-- **A base word lifts, from any element over its source.**  Its target is forced: the covering
is discrete, so the lift is the sequence of cartesian lifts. -/
theorem exists_lift {a : P.V} (t : F.obj (p.at' (P.pt a))) :
    ∀ {z : GenObj P.Gen} (R : Quiver.Path (P.pt a) z) (s : F.obj (p.at' z)),
      F.map (p.eval.map R) t = s →
        ∃ R' : Quiver.Path (⟨⟨a, t⟩⟩ : GenObj (p.elementsGen F)) ⟨⟨z.as, s⟩⟩,
          (p.elementsProj F).mapPath R' = R := by
  intro z R
  induction R with
  | nil =>
      intro s hs
      rw [eval_nil, F.map_id_apply] at hs
      subst hs
      exact ⟨Quiver.Path.nil, rfl⟩
  | @cons y z R e ih =>
      intro s hs
      obtain ⟨R', hR'⟩ := ih (F.map (p.eval.map R) t) rfl
      refine ⟨R'.cons ⟨e, ?_⟩, ?_⟩
      · rw [← hs, eval_cons]; exact (Functor.map_comp_apply F _ _ t).symm
      · rw [Prefunctor.mapPath_cons, hR']; rfl

/-- The projection is a covering: a base generator and a source element determine the target. -/
theorem elementsProj_star_injective (x : GenObj (p.elementsGen F)) :
    Function.Injective ((p.elementsProj F).star x) := by
  rintro ⟨⟨⟨c₁, t₁⟩⟩, e₁, h₁⟩ ⟨⟨⟨c₂, t₂⟩⟩, e₂, h₂⟩ h
  obtain ⟨hc, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : c₁ = c₂ := congrArg GenObj.as hc
  obtain rfl : e₁ = e₂ := eq_of_heq he
  obtain rfl : t₁ = t₂ := h₁.symm.trans h₂
  rfl

theorem elementsTotal_prop {X Y : GenObj (p.elementsGen F)} (R : Quiver.Path X Y) :
    (p.eval ⋙ F).map ((p.elementsProj F).mapPath R) X.as.2 = Y.as.2 := by
  have h := ((Paths.lift (p.elementsInterp F)).map R).property
  rwa [val_eval] at h

/-- **Words of the total quiver are morphisms of elements over the base's word category.** -/
def elementsTotal : Paths (GenObj (p.elementsGen F)) ⥤ (p.eval ⋙ F).Elements where
  obj X := ⟨P.pt X.as.1, X.as.2⟩
  map {_ _} R := ⟨(p.elementsProj F).mapPath R, elementsTotal_prop p F R⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext (Prefunctor.mapPath_comp _ _ _)

theorem elementsTotal_obj_surjective : Function.Surjective (p.elementsTotal F).obj :=
  fun Y => ⟨⟨⟨Y.1.as, Y.2⟩⟩, rfl⟩

/-- Faithful because the projection is: a lifted word is its projection. -/
instance : (p.elementsTotal F).Faithful where
  map_injective {_ _} {_ _} h :=
    haveI := Prefunctor.pathsFunctor_faithful (p.elementsProj F)
      (elementsProj_star_injective p F)
    (p.elementsProj F).pathsFunctor.map_injective (congrArg Subtype.val h)

instance : (p.elementsTotal F).Full where
  map_surjective {X Y} f := by
    obtain ⟨R, hR⟩ := exists_lift p F X.as.2 f.val Y.as.2 f.property
    exact ⟨R, Subtype.ext hR⟩

/-! ## The presentation -/

/-- **A presentation of `C` presents `∫F`** — 0-cells a 0-cell carrying an element, 1-cells the
base's acting on it, 2-cells the base's read on projected words. -/
def elements : Presents (p.elementsPoly F) F.Elements :=
  Presents.ofDesc (p.elementsInterp F)
    (fun α => Subtype.ext ((val_eval p F _).trans
      ((p.comap_sound (p.elementsProj F) α).trans (val_eval p F _).symm)))
    (fun {X Y} {R₁ R₂} h => by
      refine Polygraph.comap_quot_map_eq_of_gen (p.elementsProj F)
        (gen_pullbackRel (p.elementsTotal F)
          ((CategoryOfElements.π (p.eval ⋙ F)).pullbackRel P.homRel)
          (fun _ _ => elementsTotal_obj_surjective p F _) ?_)
      refine gen_onElements (fun {_ _} {u v} hr t => ?_)
        (p.gen_of_eval_eq ?_) _ _ _
      · change F.map (p.eval.map u) t = F.map (p.eval.map v) t
        rw [p.sound' hr]
      · exact (val_eval p F R₁).symm.trans ((congrArg Subtype.val h).trans (val_eval p F R₂)))
    { map_surjective := fun {x y} f => by
        obtain ⟨R, hR⟩ := exists_lift p F x.as.2 (p.eval.preimage f.val) y.as.2
          (by rw [p.eval.map_preimage]; exact f.property)
        exact ⟨R, Subtype.ext ((val_eval p F R).trans
          (by rw [hR]; exact p.eval.map_preimage f.val))⟩ }
    { mem_essImage := fun z => by
        obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := p.eval) z.1
        refine ⟨⟨⟨x.as, F.map i.inv z.2⟩⟩, ⟨CategoryOfElements.isoMk _ _ i ?_⟩⟩
        change F.map i.hom (F.map i.inv z.2) = z.2
        rw [← Functor.map_comp_apply, i.inv_hom_id, F.map_id_apply] }

/-- A 1-cell of `∫F` names the cartesian lift of the arrow it acts by. -/
@[simp] theorem elements_arrow {z z' : GenObj (p.elementsGen F)} (e : z ⟶ z') :
    (p.elements F).arrow e = (p.elementsInterp F).map e :=
  Paths.lift_toPath (p.elementsInterp F) e

/-- **A 1-cell of `∫F` is picked when the base 1-cell it acts by is.** -/
def elementsPicked (S : ∀ {a b : P.V}, P.Gen a b → Prop) :
    ∀ {z z' : p.elementsV F}, (p.elementsPoly F).Gen z z' → Prop := fun e => S e.1

/-! ## The total polygraph is functorial in the presheaf

A map of presheaves moves an element without moving the base 1-cell it acts by, so it is a map of
generating quivers *over* `P`'s — and `comapOver` carries the 2-cells along with no choice. -/

section Reindex

variable {F F' F'' : C ⥤ Type w'}

/-- **A map of presheaves moves an element and nothing else.** -/
def elementsQuiver (τ : F ⟶ F') :
    GenObj (p.elementsGen F) ⥤q GenObj (p.elementsGen F') where
  obj z := ⟨⟨z.as.1, τ.app _ z.as.2⟩⟩
  map {_ z'} e := ⟨e.1, (NatTrans.naturality_apply τ (p.arrow e.1) _).symm.trans
    (congrArg (τ.app (p.at' (P.pt z'.as.1))) e.2)⟩

/-- **The total polygraph, on a map of presheaves** — a `comap` over the identity of `P`. -/
def elementsPolyMap (τ : F ⟶ F') : p.elementsPoly F ⟶ p.elementsPoly F' :=
  Polygraph.comapOver (p.elementsProj F') (p.elementsQuiver τ)

/-- **The total polygraph of a presentation, as a functor of the presheaf.** -/
def elementsPolyFunctor : (C ⥤ Type w') ⥤ Polygraph.{w, max u' w', max u' w' w w₂} where
  obj F := p.elementsPoly F
  map τ := p.elementsPolyMap τ
  map_id F := Polygraph.comapOver_id (p.elementsProj F)
  map_comp {_ _ F₃} τ σ :=
    Polygraph.comapOver_comp (p.elementsProj F₃) (p.elementsQuiver τ) (p.elementsQuiver σ)

/-- **Reindexing carries a picked 1-cell to a picked 1-cell** — the base 1-cell does not move. -/
theorem elementsPicked_map (S : ∀ {a b : P.V}, P.Gen a b → Prop) (τ : F ⟶ F')
    {z z' : p.elementsV F} (e : (p.elementsPoly F).Gen z z') (he : p.elementsPicked F S e) :
    p.elementsPicked F' S ((p.elementsPolyMap τ).pre.map (Polygraph.cell e)) := he

/-- A 1-cell of `∫F` names the cartesian lift of a base arrow that reindexing does not move. -/
theorem elements_E_map_quot (τ : F ⟶ F') {X Y : GenObj (p.elementsGen F)} (e : X ⟶ Y) :
    (p.elements F').E.map
        ((p.elementsPolyMap τ).functor.map ((p.elementsPoly F).quot.map e.toPath))
      = (NatTrans.mapElements τ).map
          ((p.elements F).E.map ((p.elementsPoly F).quot.map e.toPath)) := by
  change (Paths.lift (p.elementsInterp F')).map ((p.elementsQuiver τ).map e).toPath
      = (NatTrans.mapElements τ).map ((Paths.lift (p.elementsInterp F)).map e.toPath)
  rw [Paths.lift_toPath, Paths.lift_toPath]
  exact Subtype.ext rfl

/-- **The presentation of `∫F` is natural in the presheaf** — on the nose, no coherence. -/
theorem elements_E_naturality (τ : F ⟶ F') :
    (p.elementsPolyMap τ).functor ⋙ (p.elements F').E
      = (p.elements F).E ⋙ NatTrans.mapElements τ :=
  Polygraph.presented_ext_of_gen (fun _ => rfl) fun e =>
    heq_of_eq (p.elements_E_map_quot τ e)

end Reindex

/-! ## Lifting a word

A word of the base lifts uniquely from an element over its source: `elementsTotal` is fully
faithful, so the lift is its `preimage` and is pinned by its projection. -/

section WordLift

/-- A base word together with its action on an element, as an arrow of `∫(eval ⋙ F)`. -/
def wordElt {x y : GenObj P.Gen} (u : Quiver.Path x y) {s : F.obj (p.at' x)}
    {t : F.obj (p.at' y)} (h : F.map (p.eval.map u) s = t) :
    (p.elementsTotal F).obj (⟨⟨x.as, s⟩⟩ : Paths (GenObj (p.elementsGen F)))
      ⟶ (p.elementsTotal F).obj ⟨⟨y.as, t⟩⟩ := ⟨u, h⟩

/-- **The lift of a base word from an element over its source.** -/
noncomputable def wordLift {x y : GenObj P.Gen} (u : Quiver.Path x y)
    {s : F.obj (p.at' x)} {t : F.obj (p.at' y)} (h : F.map (p.eval.map u) s = t) :
    Quiver.Path (⟨⟨x.as, s⟩⟩ : GenObj (p.elementsGen F)) ⟨⟨y.as, t⟩⟩ :=
  (p.elementsTotal F).preimage (p.wordElt F u h)

@[simp] theorem elementsProj_mapPath_wordLift {x y : GenObj P.Gen} (u : Quiver.Path x y)
    {s : F.obj (p.at' x)} {t : F.obj (p.at' y)} (h : F.map (p.eval.map u) s = t) :
    (p.elementsProj F).mapPath (p.wordLift F u h) = u :=
  congrArg Subtype.val ((p.elementsTotal F).map_preimage (p.wordElt F u h))

/-- **A lifted word is pinned by its projection.** -/
theorem eq_wordLift {x y : GenObj P.Gen} {u : Quiver.Path x y} {s : F.obj (p.at' x)}
    {t : F.obj (p.at' y)} (h : F.map (p.eval.map u) s = t)
    (R : Quiver.Path (⟨⟨x.as, s⟩⟩ : GenObj (p.elementsGen F)) ⟨⟨y.as, t⟩⟩)
    (hR : (p.elementsProj F).mapPath R = u) : R = p.wordLift F u h :=
  (p.elementsTotal F).map_injective
    (Subtype.ext (hR.trans (p.elementsProj_mapPath_wordLift F u h).symm))

/-- **A word of `∫F` is pinned by its projection** — the covering is discrete. -/
theorem eq_of_elementsProj_mapPath_eq {X Y : GenObj (p.elementsGen F)} {R R' : Quiver.Path X Y}
    (h : (p.elementsProj F).mapPath R = (p.elementsProj F).mapPath R') : R = R' :=
  (p.elementsTotal F).map_injective (Subtype.ext h)

/-- **…so a prefunctor into its words is pinned by its 0-cells and the projections of its words.**
Substituting the 0-cell map is what keeps the statement free of transports. -/
theorem prefunctor_ext_of_elementsProj {V : Type u''} [Quiver.{w''} V]
    {G H : V ⥤q (p.elementsPoly F).Word} (hobj : ∀ x, G.obj x = H.obj x)
    (hmap : ∀ (x y : V) (e : x ⟶ y),
      (p.elementsProj F).mapPath (G.map e) ≍ (p.elementsProj F).mapPath (H.map e)) : G = H := by
  obtain ⟨Gobj, Gmap⟩ := G
  obtain ⟨Hobj, Hmap⟩ := H
  obtain rfl : Gobj = Hobj := funext hobj
  simp only [Prefunctor.mk.injEq, heq_eq_eq, true_and]
  funext x y e
  exact p.eq_of_elementsProj_mapPath_eq F (eq_of_heq (hmap x y e))

/-- A 1-cell of `∫F` names the arrow it acts by, underneath. -/
theorem elements_arrow_val {z z' : GenObj (p.elementsGen F)} (e : z ⟶ z') :
    ((p.elements F).arrow e).val = p.arrow e.1 :=
  congrArg Subtype.val (p.elements_arrow F e)

/-- **A word of `∫F`, evaluated** — its underlying arrow is the projected word, evaluated. -/
theorem elements_eval_val {X Y : GenObj (p.elementsGen F)} (R : Quiver.Path X Y) :
    ((p.elements F).eval.map R).val = p.eval.map ((p.elementsProj F).mapPath R) := by
  induction R with
  | nil =>
      exact (congrArg Subtype.val ((p.elements F).eval.map_id X)).trans
        (p.eval.map_id (P.pt X.as.1)).symm
  | cons R e ih =>
      have h1 : ((p.elements F).eval.map (R.cons e)).val
          = ((p.elements F).eval.map R).val ≫ ((p.elements F).arrow e).val :=
        congrArg Subtype.val ((p.elements F).eval_cons R e)
      rw [h1, ih, p.elements_arrow_val F e, Prefunctor.mapPath_cons, p.eval_cons]
      rfl

/-- **Reindexing a lifted word lifts the same word** — reindexing does not move the base 1-cells,
and a word upstairs is pinned by its projection. -/
theorem elementsQuiver_mapPath_wordLift {F' : C ⥤ Type w'} (τ : F ⟶ F')
    {x y : GenObj P.Gen} (u : Quiver.Path x y) {s : F.obj (p.at' x)} {t : F.obj (p.at' y)}
    (h : F.map (p.eval.map u) s = t)
    (h' : F'.map (p.eval.map u) (τ.app (p.at' x) s) = τ.app (p.at' y) t) :
    (p.elementsQuiver τ).mapPath (p.wordLift F u h) = p.wordLift F' u h' :=
  p.eq_wordLift F' h' _
    ((Prefunctor.mapPath_comp_apply (p.elementsQuiver τ) (p.elementsProj F')
      (p.wordLift F u h)).symm.trans (p.elementsProj_mapPath_wordLift F u h))

/-- **A lift of a word of picked arrows is a word of picked 1-cells.** -/
theorem all_elementsPicked_wordLift (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} {u : Quiver.Path x y} {s : F.obj (p.at' x)} {t : F.obj (p.at' y)}
    (h : F.map (p.eval.map u) s = t) (hu : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    Quiver.Path.All (fun ⦃_ _⦄ e => p.elementsPicked F S e) (p.wordLift F u h) :=
  Quiver.Path.All.of_mapPath (p.elementsProj F)
    (by rw [p.elementsProj_mapPath_wordLift F u h]; exact hu)

end WordLift

end Presents

end CategoryTheory
