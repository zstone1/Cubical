import CubeChains.Foundations.Polygraph.Basic
import CubeChains.Machinery.StrictInverse
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Machinery/Presentation/Basic — what a polygraph presents

`presented` is the free category on a polygraph's 1-cells modulo the congruence its 2-cells
generate; the polygraph itself, and its morphisms, are `Foundations/Polygraph/Basic`.

That a polygraph presents `C` is `Presents P C`: a functor `P.presented ⥤ C` which is an
equivalence.  `ofDesc` is the only place its obligations appear; after it, spanning and covering
are `Full` and `EssSurj` of `eval = quot ⋙ E`, completeness is `E.map_injective`, and `transport`
is a composition.
-/

universe w' w u'' u' v u w₂' w₂ v₂ u₂

namespace CategoryTheory

/-- **A functor killing a relation kills the congruence it generates** — the quotient's universal
property, read at one arrow. -/
theorem HomRel.map_eq_of_gen {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    (r : HomRel C) (F : C ⥤ D)
    (H : ∀ {x y : C} {f g : x ⟶ y}, r f g → F.map f = F.map g)
    {x y : C} {u v : x ⟶ y}
    (h : Relation.EqvGen (@HomRel.CompClosure C _ r x y) u v) : F.map u = F.map v :=
  have H' : ∀ (x y : C) (f g : x ⟶ y), r f g → F.map f = F.map g := fun _ _ _ _ => H
  (Quotient.lift_map_functor_map r F H' u).symm.trans
    ((congrArg (Quotient.lift r F H').map (Quot.eq.mpr h)).trans
      (Quotient.lift_map_functor_map r F H' v))

/-! ## Words along a map of generating quivers

`Paths.lift` into another path category is `Prefunctor.mapPath`; mathlib states this for the
prefunctor, not for the words. -/

/-- **Equal prefunctors agree on 1-cells**, up to the transport their 0-cells carry. -/
theorem _root_.Prefunctor.map_of_eq {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {F G : V ⥤q W} (h : F = G) {x y : V} (e : x ⟶ y) :
    F.map e = Quiver.homOfEq (G.map e)
      (congrArg (fun φ : V ⥤q W => φ.obj x) h).symm
      (congrArg (fun φ : V ⥤q W => φ.obj y) h).symm := by
  subst h; rfl

/-- **…and its converse**: `Prefunctor.ext'` with the two quivers free to sit in different
universes, which is what a reading of a polygraph in a category needs. -/
theorem _root_.Prefunctor.ext_homOfEq {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {F G : V ⥤q W} (h_obj : ∀ x, F.obj x = G.obj x)
    (h_map : ∀ (x y : V) (e : x ⟶ y),
      F.map e = Quiver.homOfEq (G.map e) (h_obj _).symm (h_obj _).symm) : F = G := by
  obtain ⟨Fobj, Fmap⟩ := F
  obtain ⟨Gobj, Gmap⟩ := G
  obtain rfl : Fobj = Gobj := funext h_obj
  simp only [Prefunctor.mk.injEq, heq_eq_eq, true_and]
  ext x y e
  simpa only [Quiver.homOfEq_rfl] using h_map x y e

/-- **…and the form for prefunctors whose 0-cell maps agree on the nose** — then the 1-cells live in
one type and the `homOfEq` of `Prefunctor.ext_homOfEq` is noise. -/
theorem _root_.Prefunctor.ext_of_obj_eq {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {F G : V ⥤q W} (h_obj : F.obj = G.obj)
    (h_map : ∀ (x y : V) (e : x ⟶ y), F.map e ≍ G.map e) : F = G :=
  Prefunctor.ext_homOfEq (congrFun h_obj) fun x y e =>
    eq_of_heq ((h_map x y e).trans (Quiver.homOfEq_heq _ _ _).symm)

/-- **Words along a map of quivers**, as a functor — mathlib's free category on a quiver, under the
name the cells of a polygraph are read with. -/
abbrev _root_.Prefunctor.pathsFunctor {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    (π : V ⥤q W) : Paths V ⥤ Paths W := Cat.freeMap π

section Covering

variable {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W] (π : V ⥤q W)

/-- **A covering is faithful on words**: a word is determined by its projection, because each step
is (`Prefunctor.pathStar_injective`). -/
theorem _root_.Prefunctor.pathsFunctor_faithful
    (hπ : ∀ x : V, Function.Injective (π.star x)) : π.pathsFunctor.Faithful where
  map_injective {x y} {u v} h := by
    have hval : π.mapPath u = π.mapPath v := h
    have hs : π.pathStar x ⟨y, u⟩ = π.pathStar x ⟨y, v⟩ := Sigma.ext rfl (heq_of_eq hval)
    exact eq_of_heq (Sigma.mk.inj_iff.mp (π.pathStar_injective hπ x hs)).2

/-- **A covering is full on words**: every word between projected 0-cells is projected, because
each step is (`Prefunctor.pathStar_surjective`). -/
theorem _root_.Prefunctor.pathsFunctor_full (hπ : ∀ x : V, Function.Surjective (π.star x))
    (hobj : Function.Injective π.obj) : π.pathsFunctor.Full where
  map_surjective {x y} u := by
    obtain ⟨⟨y', u'⟩, h⟩ := π.pathStar_surjective hπ x ⟨π.obj y, u⟩
    obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := hobj h₁
    exact ⟨u', eq_of_heq h₂⟩

end Covering

namespace Paths

variable {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]

/-! `Paths.lift_unique` is the universal property; every fact below is it at a different
instantiation, read back pointwise through `Functor.congr_hom` (whose `eqToHom`s are `𝟙` here, so
`exact` closes them). -/

/-- **Words along a map of quivers is the lift of its letters.** -/
theorem lift_comp_of (π : V ⥤q W) : Paths.lift (π ⋙q Paths.of W) = π.pathsFunctor :=
  (Paths.lift_unique (π ⋙q Paths.of W) π.pathsFunctor rfl).symm

theorem lift_comp_of_map (π : V ⥤q W) {x y : V} (u : Quiver.Path x y) :
    (Paths.lift (π ⋙q Paths.of W)).map u = π.mapPath u :=
  (Functor.congr_hom (lift_comp_of π) u).trans ((Category.id_comp _).trans (Category.comp_id _))

/-- …spelling a word by itself. -/
theorem lift_of : Paths.lift (Paths.of V) = 𝟭 (Paths V) :=
  (lift_comp_of (𝟭q V)).trans (Cat.freeMap_id V)

theorem lift_of_map {x y : V} (u : Quiver.Path x y) : (Paths.lift (Paths.of V)).map u = u :=
  (lift_comp_of_map (𝟭q V) u).trans (Prefunctor.mapPath_id u)

/-- **A word lifted then pushed forward is a word lifted once.** -/
theorem lift_comp_map {D : Type*} [Category* D] {E : Type*} [Category* E]
    (φ : V ⥤q D) (U : D ⥤ E) {x y : V} (u : Quiver.Path x y) :
    U.map ((Paths.lift φ).map u) = (Paths.lift (φ ⋙q U.toPrefunctor)).map u :=
  (Functor.congr_hom (Paths.lift_unique (φ ⋙q U.toPrefunctor) (Paths.lift φ ⋙ U)
    (congrArg (· ⋙q U.toPrefunctor) (Paths.lift_spec φ))) u).trans
      ((Category.id_comp _).trans (Category.comp_id _))

/-- **Substituting a map of quivers into a lift.** -/
theorem pathsFunctor_comp_lift {D : Type*} [Category* D] (π : V ⥤q W) (φ : W ⥤q D) :
    π.pathsFunctor ⋙ Paths.lift φ = Paths.lift (π ⋙q φ) :=
  Paths.lift_unique _ _ (Prefunctor.ext (fun _ => rfl) (fun _ _ _ => by simp))

/-- **A word pushed forward then interpreted is the word interpreted along the composite** — the
same `lift_unique`, with `lift_comp_of` naming the pushforward. -/
theorem lift_mapPath {D : Type*} [Category* D] (π : V ⥤q W) (φ : W ⥤q D) {x y : V}
    (u : Quiver.Path x y) :
    (Paths.lift φ).map (π.mapPath u) = (Paths.lift (π ⋙q φ)).map u :=
  (Functor.congr_hom (pathsFunctor_comp_lift π φ) u).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- **A concatenation of words is a composite** — `Functor.map_comp` said with `Quiver.Path.comp`,
the spelling a word built by hand carries. -/
theorem lift_map_comp {C : Type*} [Category* C] (φ : V ⥤q C) {x y z : V} (p : Quiver.Path x y)
    (q : Quiver.Path y z) :
    (Paths.lift φ).map (p.comp q) = (Paths.lift φ).map p ≫ (Paths.lift φ).map q :=
  (Paths.lift φ).map_comp p q

/-- **A word read at other names for both endpoints**, through any functor out of the words — the
only transport a cell ever carries. -/
theorem map_cellCongr₂ {D : Type*} [Category* D] (G : Paths V ⥤ D) {x x' y y' : V} (hx : x = x')
    (hy : y = y') (p : Quiver.Path x y) :
    G.map (cellCongr Quiver.Path hx hy p)
      = eqToHom (congrArg G.obj hx).symm ≫ G.map p ≫ eqToHom (congrArg G.obj hy) := by
  subst hx; subst hy; rw [cellCongr_self]; simp

/-- …and the common case, where only the target is renamed. -/
theorem map_cellCongr {D : Type*} [Category* D] (G : Paths V ⥤ D) {x y y' : V} (h : y = y')
    (p : Quiver.Path x y) :
    G.map (cellCongr Quiver.Path rfl h p) = G.map p ≫ eqToHom (congrArg G.obj h) :=
  (map_cellCongr₂ G rfl h p).trans (Category.id_comp _)

end Paths

namespace Polygraph

section Basic

variable (P : Polygraph.{w, u', w₂})

/-- The generating words. -/
abbrev Word : Type u' := Paths (GenObj P.Gen)

/-- A 0-cell, as a vertex of the generating quiver. -/
abbrev pt (a : P.V) : GenObj P.Gen := ⟨a⟩

/-- **The congruence the 2-cells generate**: the relation a `CategoryTheory.Quotient` consumes. -/
def homRel : HomRel P.Word :=
  fun x y u v => ∃ α : P.Rel x y, P.src α = u ∧ P.tgt α = v

/-- **The category `P` presents**: the generating words modulo the 2-cells. -/
abbrev presented : Type u' := Quotient P.homRel

/-- A word, in the presented category. -/
abbrev quot : P.Word ⥤ P.presented := Quotient.functor P.homRel

/-- **A 2-cell's two sides spell one arrow.** -/
theorem quot_src_tgt {x y : GenObj P.Gen} (α : P.Rel x y) :
    P.quot.map (P.src α) = P.quot.map (P.tgt α) :=
  Quotient.sound _ ⟨α, rfl, rfl⟩

/-- **The empty word is the identity** — `Functor.map_id` said with `Quiver.Path.nil`, the spelling
a word built by hand carries. -/
theorem quot_map_nil (x : GenObj P.Gen) :
    P.quot.map (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (P.quot.obj x) := P.quot.map_id x

/-- **…and a concatenation is a composite** — `Paths.lift_map_comp` for `quot`. -/
theorem quot_map_comp {x y z : GenObj P.Gen} (u : Quiver.Path x y) (v : Quiver.Path y z) :
    P.quot.map (u.comp v) = P.quot.map u ≫ P.quot.map v := P.quot.map_comp u v

/-- …one letter at a time. -/
theorem quot_map_cons {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) :
    P.quot.map (u.cons e) = P.quot.map u ≫ P.quot.map e.toPath := P.quot.map_comp u e.toPath

/-- A word read at another name for its endpoint, in the presented category. -/
theorem quot_map_cellCongr {x y y' : GenObj P.Gen} (h : y = y') (p : Quiver.Path x y) :
    P.quot.map (cellCongr Quiver.Path rfl h p)
      = P.quot.map p ≫ eqToHom (congrArg (fun z => (⟨z⟩ : P.presented)) h) :=
  Paths.map_cellCongr P.quot h p

end Basic

/-! ## A 2-cell between functors out of `presented`

Every arrow of `presented` is a word, so a family given on 0-cells and natural against the
*generators* is already natural: path induction does the rest. -/

section NatTrans

variable {P : Polygraph.{w, u', w₂}} {E : Type*} [Category* E]

/-- **A family natural on generators is natural on words** — path induction. -/
theorem naturality_of_gen {F G : P.presented ⥤ E} (app : ∀ x : GenObj P.Gen, F.obj ⟨x⟩ ⟶ G.obj ⟨x⟩)
    (nat : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
      F.map (P.quot.map e.toPath) ≫ app y = app x ≫ G.map (P.quot.map e.toPath))
    {x y : GenObj P.Gen} (w : Quiver.Path x y) :
    F.map (P.quot.map w) ≫ app y = app x ≫ G.map (P.quot.map w) := by
  -- `app` spells a 0-cell `⟨x⟩` where `quot.map` spells it `P.quot.obj x`, so no `rw` matches
  induction w with
  | nil =>
      exact ((congrArg (· ≫ app x) ((congrArg F.map (P.quot_map_nil x)).trans
        (F.map_id _))).trans (Category.id_comp _)).trans ((Category.comp_id _).symm.trans
          (congrArg (app x ≫ ·) ((congrArg G.map (P.quot_map_nil x)).trans (G.map_id _)).symm))
  | @cons b c w e ih =>
      have h : ∀ H : P.presented ⥤ E, H.map (P.quot.map (w.cons e))
          = H.map (P.quot.map w) ≫ H.map (P.quot.map e.toPath) :=
        fun H => (congrArg H.map (P.quot_map_cons w e)).trans (H.map_comp _ _)
      exact (congrArg (· ≫ app c) (h F)).trans ((Category.assoc _ _ _).trans
        ((congrArg (F.map (P.quot.map w) ≫ ·) (nat e)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.map (P.quot.map e.toPath)) ih).trans
            ((Category.assoc _ _ _).trans (congrArg (app x ≫ ·) (h G).symm))))))

/-- …packaged. -/
def natTransOfGen (F G : P.presented ⥤ E) (app : ∀ x : GenObj P.Gen, F.obj ⟨x⟩ ⟶ G.obj ⟨x⟩)
    (nat : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
      F.map (P.quot.map e.toPath) ≫ app y = app x ≫ G.map (P.quot.map e.toPath)) :
    F ⟶ G where
  app X := app X.as
  naturality _ _ f := by
    obtain ⟨w, rfl⟩ := P.quot.map_surjective f
    exact naturality_of_gen app nat w

/-- **Two functors out of `presented` agreeing on the generators are equal** — each composite with
`quot` is a `Paths.lift`, so `Paths.lift_unique` turns this into a prefunctor equality.  The 0-cells
must agree on the nose: a transport there is not a prefunctor. -/
theorem presented_ext_of_gen {F G : P.presented ⥤ E}
    (hobj : ∀ x : GenObj P.Gen, F.obj ⟨x⟩ = G.obj ⟨x⟩)
    (hmap : ∀ {x y : GenObj P.Gen} (e : x ⟶ y),
      F.map (P.quot.map e.toPath) ≍ G.map (P.quot.map e.toPath)) : F = G :=
  Quotient.lift_unique' _ _ _
    ((Paths.lift_unique _ (P.quot ⋙ F) rfl).trans
      ((congrArg Paths.lift (Prefunctor.ext_of_obj_eq (funext hobj) fun _ _ e => hmap e)).trans
        (Paths.lift_unique _ (P.quot ⋙ G) rfl).symm))

end NatTrans

/-! ## Descending a functor on words

Every functor out of `P.presented` is a functor on *words* killing `P`'s 2-cells; a morphism of
polygraphs, a spelling and an interpretation differ only in the data that produces it.  Both laws
take that functor as an argument with an equation, so no caller transports a `Prop`. -/

section DescWords

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

/-- **A functor on words that kills `P`'s 2-cells descends to `P.presented`.** -/
def descWords (W : P.Word ⥤ C)
    (h : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), W.map (P.src α) = W.map (P.tgt α)) :
    P.presented ⥤ C :=
  Quotient.lift P.homRel W fun _ _ _ _ hr => by
    obtain ⟨α, rfl, rfl⟩ := hr; exact h α

theorem quot_comp_descWords (W : P.Word ⥤ C) (h) : P.quot ⋙ descWords W h = W :=
  Quotient.lift_spec _ _ _

/-- **The descent of `quot` itself is the identity.** -/
theorem descWords_id {W : P.Word ⥤ P.presented} {h} (e : W = P.quot) :
    descWords W h = 𝟭 P.presented := by
  subst e; exact Quotient.lift_unique' _ _ _ (by rw [quot_comp_descWords, Functor.comp_id])

/-- **Post-composing a descent descends the post-composite.** -/
theorem descWords_comp {W : P.Word ⥤ C} {h} (U : C ⥤ D) {W' : P.Word ⥤ D} {h'}
    (e : W' = W ⋙ U) : descWords W' h' = descWords W h ⋙ U := by
  subst e; exact (Quotient.lift_unique' _ _ _
    (by rw [← Functor.assoc, quot_comp_descWords, quot_comp_descWords])).symm

end DescWords

/-! ## What a morphism of polygraphs does to words -/

namespace Hom

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}

/-- The word a word spells. -/
abbrev words (F : Hom P Q) : P.Word ⥤ Q.Word := F.pre.pathsFunctor

/-- **A morphism kills the congruence its 2-cells generate.** -/
theorem homRel_two (F : Hom P Q) {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : P.homRel u v) : Q.homRel (F.words.map u) (F.words.map v) := by
  obtain ⟨α, rfl, rfl⟩ := h
  exact ⟨F.two α, F.src_two α, F.tgt_two α⟩

/-- **The functor a morphism of polygraphs induces.** -/
def functor (F : Hom P Q) : P.presented ⥤ Q.presented :=
  descWords (F.words ⋙ Q.quot) fun α => Quotient.sound _ (F.homRel_two ⟨α, rfl, rfl⟩)

theorem quot_comp_functor (F : Hom P Q) : P.quot ⋙ F.functor = F.words ⋙ Q.quot :=
  quot_comp_descWords _ _

/-- **The functor sees only the prefunctor** — the 2-cells enter a `Hom` solely through the
soundness obligation, which is a `Prop`.  So a naturality square of prefunctors is already a
naturality square of functors. -/
theorem functor_congr {F G : Hom P Q} (h : F.pre = G.pre) : F.functor = G.functor :=
  Quotient.lift_unique' _ _ _ (F.quot_comp_functor.trans
    ((congrArg (fun π : GenObj P.Gen ⥤q GenObj Q.Gen => π.pathsFunctor ⋙ Q.quot) h).trans
      G.quot_comp_functor.symm))

end Hom

section Functoriality

variable {P Q R : Polygraph.{w, u', w₂}}

@[simp] theorem functor_id : (𝟙 P : P ⟶ P).functor = 𝟭 P.presented :=
  descWords_id (by
    rw [show Hom.words (𝟙 P) = 𝟭 P.Word from Cat.freeMap_id _, Functor.id_comp])

@[simp] theorem functor_comp (F : P ⟶ Q) (G : Q ⟶ R) :
    (F ≫ G).functor = F.functor ⋙ G.functor :=
  descWords_comp G.functor (by
    rw [show Hom.words (F ≫ G) = F.words ⋙ G.words from
      Cat.freeMap_comp F.pre G.pre, Functor.assoc, ← Hom.quot_comp_functor G,
      ← Functor.assoc])

/-- **A square of prefunctors is a square of functors** — `Hom.functor_congr` at a composite, which
is the only way a naturality square of polygraphs is ever used. -/
theorem functor_naturality {P Q P' Q' : Polygraph.{w, u', w₂}} (F : P ⟶ Q) (G : Q ⟶ Q')
    (F' : P ⟶ P') (G' : P' ⟶ Q') (h : F.pre ⋙q G.pre = F'.pre ⋙q G'.pre) :
    F.functor ⋙ G.functor = F'.functor ⋙ G'.functor :=
  ((functor_comp F G).symm.trans (Hom.functor_congr (F := F ≫ G) (G := F' ≫ G') h)).trans
    (functor_comp F' G')

/-- **A functor into `Polygraph` carries an identity to the identity functor** — what a coherence at
the unit needs. -/
theorem functor_map_id {D : Type*} [Category* D] (G : D ⥤ Polygraph.{w, u', w₂}) (d : D) :
    (G.map (𝟙 d)).functor = 𝟭 (G.obj d).presented :=
  (congrArg Hom.functor (G.map_id d)).trans functor_id

/-- **An isomorphism of polygraphs is an equivalence of the categories they present** — the two
composites are the identity on the nose, so the unit and counit are `eqToIso`. -/
def presentedEquiv (e : P ≅ Q) : P.presented ≌ Q.presented :=
  Equivalence.mk e.hom.functor e.inv.functor
    (eqToIso (by rw [← functor_comp, e.hom_inv_id, functor_id])).symm
    (eqToIso (by rw [← functor_comp, e.inv_hom_id, functor_id]))

end Functoriality

/-! ## Spelling a generator by a word

The gadget a *comparison of presentations* needs, and the one thing a morphism of polygraphs is
not: a generator of `P` may spell a whole word of `Q` — an Artin generator as a product of Garside
atoms.  It induces a functor and nothing more.  There is no category of spellings here: `refl` and
`trans` (`Comparison`) are the unit and the Kleisli composition of the monad carrying `Q` to the
polygraph on its words, not `Polygraph`'s identity and composition. -/

/-- **A spelling of `P`'s generators by words of `Q`.** -/
structure Spelling (P : Polygraph.{w, u', w₂}) (Q : Polygraph.{w', u'', w₂'}) where
  /-- the word a 1-cell spells -/
  cells : GenObj P.Gen ⥤q Q.Word
  /-- each 2-cell of `P` holds downstream -/
  sound {x y : GenObj P.Gen} (α : P.Rel x y) :
    Q.quot.map ((Paths.lift cells).map (P.src α)) = Q.quot.map ((Paths.lift cells).map (P.tgt α))

namespace Spelling

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}

/-- The word a word spells. -/
abbrev words (F : Spelling P Q) : P.Word ⥤ Q.Word := Paths.lift F.cells

/-- **The functor a spelling induces.** -/
def functor (F : Spelling P Q) : P.presented ⥤ Q.presented :=
  descWords (F.words ⋙ Q.quot) F.sound

theorem quot_comp_functor (F : Spelling P Q) : P.quot ⋙ F.functor = F.words ⋙ Q.quot :=
  quot_comp_descWords _ _

end Spelling

/-! ## Pulling a polygraph back

A generating quiver over `P`'s, carrying `P`'s 2-cells with their boundaries lifted: the shape of
every presentation obtained by restricting, or by acting. -/

section Comap

variable (P : Polygraph.{w, u', w₂}) {V : Type u''} (Gen : V → V → Type w')
  (π : GenObj Gen ⥤q GenObj P.Gen)

/-- **A 2-cell of `P` whose boundary is lifted along `π`.** -/
structure ComapRel (x y : GenObj Gen) where
  /-- the source, upstairs -/
  src : Quiver.Path x y
  /-- the target, upstairs -/
  tgt : Quiver.Path x y
  /-- the 2-cell, downstairs -/
  cell : P.Rel (π.obj x) (π.obj y)
  /-- …whose source it lifts -/
  src_eq : π.mapPath src = P.src cell
  /-- …and whose target it lifts -/
  tgt_eq : π.mapPath tgt = P.tgt cell

/-- **`P`'s 2-cells, read on a quiver over `P`'s.** -/
def comap : Polygraph.{w', u'', max u'' w' w₂} where
  V := V
  Gen := Gen
  Rel := ComapRel P Gen π
  src := ComapRel.src
  tgt := ComapRel.tgt

/-- **A map of generating quivers over `P` is a map of comaps** — the 2-cells are `P`'s and do
not move, only the words above them. -/
def comapOver {P : Polygraph.{w, u', w₂}} {V : Type u''} {Gen : V → V → Type w'}
    {V' : Type*} {Gen' : V' → V' → Type*} (π' : GenObj Gen' ⥤q GenObj P.Gen)
    (φ : GenObj Gen ⥤q GenObj Gen') :
    Hom (P.comap Gen (φ ⋙q π')) (P.comap Gen' π') where
  pre := φ
  two α :=
    { src := φ.mapPath α.src
      tgt := φ.mapPath α.tgt
      cell := α.cell
      src_eq := (Prefunctor.mapPath_comp_apply φ π' α.src).symm.trans α.src_eq
      tgt_eq := (Prefunctor.mapPath_comp_apply φ π' α.tgt).symm.trans α.tgt_eq }
  src_two _ := rfl
  tgt_two _ := rfl

/-- **A 2-cell of a comap is its two words and the cell below them** — the rest is proofs. -/
theorem ComapRel.ext {P : Polygraph.{w, u', w₂}} {V : Type u''} {Gen : V → V → Type w'}
    {π : GenObj Gen ⥤q GenObj P.Gen} {x y : GenObj Gen} {α β : ComapRel P Gen π x y} :
    α.src = β.src → α.tgt = β.tgt → α.cell = β.cell → α = β := by
  obtain ⟨s, t, c, -, -⟩ := α
  obtain ⟨s', t', c', -, -⟩ := β
  rintro rfl rfl rfl
  rfl

/-- **A comap over the identity is the comap** — a 2-cell never moves, only the words above it. -/
@[simp] theorem comapOver_id {P : Polygraph.{w, u', w₂}} {V : Type u''} {Gen : V → V → Type w'}
    (π' : GenObj Gen ⥤q GenObj P.Gen) :
    comapOver (P := P) π' (𝟭q _) = 𝟙 (P.comap Gen π') :=
  Hom.ext' rfl fun _ =>
    heq_of_eq (ComapRel.ext (Prefunctor.mapPath_id _) (Prefunctor.mapPath_id _) rfl)

/-- **…and a comap over a composite is the composite.** -/
theorem comapOver_comp {P : Polygraph.{w, u', w₂}} {V : Type u''} {Gen : V → V → Type w'}
    {V' : Type u''} {Gen' : V' → V' → Type w'} {V'' : Type u''} {Gen'' : V'' → V'' → Type w'}
    (π' : GenObj Gen'' ⥤q GenObj P.Gen) (φ : GenObj Gen ⥤q GenObj Gen')
    (ψ : GenObj Gen' ⥤q GenObj Gen'') :
    comapOver (P := P) π' (φ ⋙q ψ)
      = (comapOver (ψ ⋙q π') φ ≫ comapOver π' ψ :
          P.comap Gen (φ ⋙q ψ ⋙q π') ⟶ P.comap Gen'' π') :=
  Hom.ext' rfl fun α => heq_of_eq (ComapRel.ext (Prefunctor.mapPath_comp_apply φ ψ α.src)
    (Prefunctor.mapPath_comp_apply φ ψ α.tgt) rfl)

/-- **A word of a comap is related exactly when its projection is.** -/
theorem comap_homRel_iff {x y : GenObj Gen} (u v : Quiver.Path x y) :
    (P.comap Gen π).homRel u v ↔ P.homRel (π.mapPath u) (π.mapPath v) := by
  constructor
  · rintro ⟨α, rfl, rfl⟩
    exact ⟨α.cell, α.src_eq.symm, α.tgt_eq.symm⟩
  · rintro ⟨α, hu, hv⟩
    exact ⟨⟨u, v, α, hu.symm, hv.symm⟩, rfl, rfl⟩

end Comap

/-! ## Polygraphs whose 2-cells are their boundary

A 2-cell carrying no data beyond the pair of words it spans — a *relation* rather than a chosen
filler — makes a morphism into it determined by its 1-cells, exactly as a thin one does. -/

/-- **A polygraph whose 2-cells are pinned by their boundary.** -/
def BoundaryDetermined (P : Polygraph.{w, u', w₂}) : Prop :=
  ∀ {x y : GenObj P.Gen} (α β : P.Rel x y), P.src α = P.src β → P.tgt α = P.tgt β → α = β

/-- **A morphism into a boundary-determined polygraph is pinned by its 1-cells** — the two 2-cells
span the same boundary by `src_two`/`tgt_two`, so there is nothing left to choose. -/
theorem hom_ext_of_boundaryDetermined {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
    (hQ : Q.BoundaryDetermined) {f g : Hom P Q} (h : f.pre = g.pre) : f = g := by
  obtain ⟨p, t, hs, ht⟩ := f
  obtain ⟨p', t', hs', ht'⟩ := g
  cases h
  exact Hom.ext' rfl fun α =>
    heq_of_eq (hQ _ _ ((hs α).trans (hs' α).symm) ((ht α).trans (ht' α).symm))

/-- **Equal words stay equal downstream** — `Hom.functor` on a word, with both sides read as words
rather than as arrows of `presented`. -/
theorem Hom.quot_map_congr {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
    (F : Hom P Q) {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : P.quot.map u = P.quot.map v) :
    Q.quot.map (F.pre.mapPath u) = Q.quot.map (F.pre.mapPath v) :=
  congrArg F.functor.map h

/-! ## A category's own arrows, as a generating quiver

The shared shape of the two germs of a category, `taut` and `catPoly`, which differ only in which
parallel pairs of words they relate. -/

/-- The generating quiver of a category: its own arrows. -/
def catGen (C : Type u) [Category.{v} C] : C → C → Type v := fun X Y => X ⟶ Y

/-- The tautological interpretation of a category's own arrows. -/
def catPre (C : Type u) [Category.{v} C] : GenObj (catGen C) ⥤q C where
  obj x := x.as
  map f := f

/-- A functor, read on the generating quivers. -/
def catPreMap {C : Type u} [Category.{v} C] {D : Type u''} [Category.{w'} D] (F : C ⥤ D) :
    GenObj (catGen C) ⥤q GenObj (catGen D) where
  obj x := ⟨F.obj x.as⟩
  map f := F.map f

/-- **A word of arrows, pushed forward, composes to the pushforward of the composite.** -/
theorem lift_catPreMap {C : Type u} [Category.{v} C] {D : Type u''} [Category.{w'} D] (F : C ⥤ D)
    {x y : GenObj (catGen C)} (u : Quiver.Path x y) :
    (Paths.lift (catPre D)).map ((catPreMap F).mapPath u)
      = F.map ((Paths.lift (catPre C)).map u) :=
  (Paths.lift_mapPath (catPreMap F) (catPre D) u).trans (Paths.lift_comp_map (catPre C) F u).symm

end Polygraph

/-! ## Presenting a category -/

/-- **`P` presents `C`**: a functor from the presented category, an equivalence. -/
structure Presents (P : Polygraph.{w, u', w₂}) (C : Type u) [Category.{v} C] where
  /-- the comparison functor -/
  E : P.presented ⥤ C
  /-- …an equivalence -/
  isEquiv : E.IsEquivalence

attribute [instance] Presents.isEquiv

namespace Presents

/-- **A polygraph presents what it presents.** -/
def self (P : Polygraph.{w, u', w₂}) : Presents P P.presented := ⟨𝟭 _, inferInstance⟩

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)

/-- **`C ≌ ⟨generators | relations⟩`.** -/
noncomputable def equiv : P.presented ≌ C := p.E.asEquivalence

/-- The arrow a generating word spells.  It is `Full` and `EssSurj`: the generators span and the
0-cells cover. -/
abbrev eval : P.Word ⥤ C := P.quot ⋙ p.E

/-- The object a 0-cell names. -/
abbrev at' (x : GenObj P.Gen) : C := p.eval.obj x

/-- The arrow a 1-cell names. -/
abbrev arrow {x y : GenObj P.Gen} (e : x ⟶ y) : p.at' x ⟶ p.at' y := p.eval.map e.toPath

/-- The cells, interpreted. -/
abbrev evalPre : GenObj P.Gen ⥤q C where
  obj := p.at'
  map {_ _} e := p.arrow e

/-- Evaluating a word *is* lifting the interpretation of the cells.  Stated on morphisms, not on
the functors: `p.eval` occurs applied, so rewriting the functor breaks the motive. -/
theorem eval_map_eq_lift {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    p.eval.map u = (Paths.lift p.evalPre).map u := by
  conv_lhs => rw [← Paths.lift_of_map u]
  exact Paths.lift_comp_map _ p.eval u

/-- **The projected word, evaluated** — every word of a `comap` is read downstairs this way. -/
theorem eval_mapPath {V : Type u''} {Gen : V → V → Type w'} (π : GenObj Gen ⥤q GenObj P.Gen)
    {x y : GenObj Gen} (u : Quiver.Path x y) :
    p.eval.map (π.mapPath u) = (Paths.lift (π ⋙q p.evalPre)).map u :=
  (p.eval_map_eq_lift _).trans (Paths.lift_mapPath π p.evalPre u)

/-- **…as an equality of functors** — `eval_mapPath` with the word abstracted, which is what a
descent along `π` has to be compared with. -/
theorem lift_comp_evalPre {V : Type u''} {Gen : V → V → Type w'}
    (π : GenObj Gen ⥤q GenObj P.Gen) :
    Paths.lift (π ⋙q p.evalPre) = π.pathsFunctor ⋙ p.eval :=
  (Paths.lift_unique (π ⋙q p.evalPre) (π.pathsFunctor ⋙ p.eval) rfl).symm

/-- **`P`'s cells interpreted through `F`, on a whole word** — the step every copy of `P` inside a
bigger polygraph takes: `rw [Paths.lift_mapPath]`, then this. -/
theorem lift_evalPre_comp {E : Type*} [Category* E] (F : C ⥤ E) {x y : GenObj P.Gen}
    (u : Quiver.Path x y) :
    (Paths.lift (p.evalPre ⋙q F.toPrefunctor)).map u = F.map (p.eval.map u) := by
  rw [p.eval_map_eq_lift]
  exact (Paths.lift_comp_map p.evalPre F u).symm

@[simp] theorem eval_nil (x : GenObj P.Gen) :
    p.eval.map (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (p.at' x) := p.eval.map_id x

@[simp] theorem eval_cons {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) :
    p.eval.map (u.cons e) = p.eval.map u ≫ p.arrow e := p.eval.map_comp u e.toPath

/-- **A 2-cell's two sides spell the same arrow.**  Its converse is `p.E.map_injective`. -/
theorem sound {x y : GenObj P.Gen} (α : P.Rel x y) :
    p.eval.map (P.src α) = p.eval.map (P.tgt α) :=
  congrArg p.E.map (P.quot_src_tgt α)

/-- **Related words spell the same arrow.** -/
theorem sound' {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : P.homRel u v) :
    p.eval.map u = p.eval.map v := by
  obtain ⟨α, rfl, rfl⟩ := h; exact p.sound α

/-- **A presentation transports along an equivalence** — the *same* polygraph, read on `D`. -/
def transport {D : Type*} [Category D] (e : C ≌ D) : Presents P D :=
  ⟨p.E ⋙ e.functor, inferInstance⟩

/-- **…and along an isomorphism of polygraphs** — the *same* category, read on `Q`. -/
def ofPolyIso {Q : Polygraph.{w, u', w₂}} (e : P ≅ Q) : Presents Q C :=
  haveI : e.inv.functor.IsEquivalence := (Polygraph.presentedEquiv e).symm.isEquivalence_functor
  ⟨e.inv.functor ⋙ p.E, inferInstance⟩

end Presents

/-! ## Building one

An interpretation of the cells is a prefunctor out of the generating quiver; `sound` descends it to
`presented`, and the remaining obligations are that the descent is an equivalence. -/

section Build

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (φ : GenObj P.Gen ⥤q C)
  (sound : ∀ {x y : GenObj P.Gen} (α : P.Rel x y),
    (Paths.lift φ).map (P.src α) = (Paths.lift φ).map (P.tgt α))

/-- The functor an interpretation of the cells descends to, when it respects the 2-cells. -/
def Polygraph.desc : P.presented ⥤ C := descWords (Paths.lift φ) sound

theorem Polygraph.quot_comp_desc : P.quot ⋙ P.desc φ sound = Paths.lift φ :=
  quot_comp_descWords _ _

include sound in
/-- **Words equal in `presented` have equal interpretations** — the converse of `sound`, and how a
completeness proof carries a normal form across. -/
theorem Polygraph.lift_map_eq_of_quot_eq {x y : GenObj P.Gen} {u v : Quiver.Path x y}
    (h : P.quot.map u = P.quot.map v) :
    (Paths.lift φ).map u = (Paths.lift φ).map v :=
  congrArg (P.desc φ sound).map h

/-- **The obligations**: `sound` to descend, `complete` for faithful, and fullness and essential
surjectivity of the interpretation itself. -/
def Presents.ofDesc
    (complete : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      (Paths.lift φ).map u = (Paths.lift φ).map v → P.quot.map u = P.quot.map v)
    (full : (Paths.lift φ).Full) (essSurj : (Paths.lift φ).EssSurj) :
    Presents P C :=
  haveI : (P.desc φ sound).Full :=
    { map_surjective := by
        rintro ⟨x⟩ ⟨y⟩ f
        obtain ⟨u, hu⟩ := full.map_surjective f
        exact ⟨P.quot.map u, hu⟩ }
  haveI : (P.desc φ sound).Faithful :=
    { map_injective := by
        intro X Y f g h
        obtain ⟨u, rfl⟩ := P.quot.map_surjective f
        obtain ⟨v, rfl⟩ := P.quot.map_surjective g
        exact complete h }
  haveI : (P.desc φ sound).EssSurj :=
    { mem_essImage := fun c => by
        obtain ⟨x, ⟨i⟩⟩ := essSurj.mem_essImage c
        exact ⟨⟨x⟩, ⟨i⟩⟩ }
  ⟨P.desc φ sound, { }⟩

end Build

/-! ## Presenting a thin category

The cellular extension by *every* parallel pair of words leaves no word problem: soundness and
completeness are `Subsingleton.elim` and `Quotient.sound`, so a presentation of a preorder is
exactly a spanning family of generators on a covering family of 0-cells. -/

/-- **The polygraph on a generating quiver with a 2-cell for every parallel pair of words.**  What
it presents is the preorder the quiver generates: a hom is a path, and there is at most one. -/
def Polygraph.thin {V : Type u'} (Gen : V → V → Type w) : Polygraph.{w, u', max u' w} where
  V := V
  Gen := Gen
  Rel x y := Quiver.Path x y × Quiver.Path x y
  src p := p.1
  tgt p := p.2

/-- **Every parallel pair of words of `thin Gen` is a 2-cell.** -/
theorem Polygraph.thin_homRel {V : Type u'} {Gen : V → V → Type w} {x y : GenObj Gen}
    (u v : Quiver.Path x y) : (Polygraph.thin Gen).homRel u v :=
  ⟨show Quiver.Path x y × Quiver.Path x y from (u, v), rfl, rfl⟩

/-- **A morphism into a thin polygraph is determined by its 1-cells**: a 2-cell there *is* its
boundary. -/
theorem Polygraph.thin_hom_ext {P : Polygraph.{w, u', w₂}} {V' : Type u''}
    {Gen' : V' → V' → Type w'} {f g : Polygraph.Hom P (Polygraph.thin Gen')}
    (h : f.pre = g.pre) : f = g :=
  Polygraph.hom_ext_of_boundaryDetermined (fun _ _ => Prod.ext) h

/-- **A prefunctor of generating quivers is a morphism into the thin polygraph** — the transpose
of "cells ⊣ thin", so a thin target sees only the 1-cells. -/
def Polygraph.toThin {P : Polygraph.{w, u', w₂}} {V' : Type u''} {Gen' : V' → V' → Type w'}
    (π : GenObj P.Gen ⥤q GenObj Gen') : Polygraph.Hom P (Polygraph.thin Gen') where
  pre := π
  two α := (π.mapPath (P.src α), π.mapPath (P.tgt α))
  src_two _ := rfl
  tgt_two _ := rfl

instance {V : Type u'} (Gen : V → V → Type w) :
    Quiver.IsThin (Polygraph.thin Gen).presented :=
  fun _ _ => ⟨by rintro ⟨f⟩ ⟨g⟩; exact Quotient.sound _ (Polygraph.thin_homRel f g)⟩

/-- **All relations present a thin category**, given that the generating words span the arrows and
the 0-cells cover the objects.  Nothing else is left: for a thin target `Full` says only that a hom
is spelled by *some* path, and faithfulness is free on either side. -/
def Presents.ofThin {V : Type u'} {Gen : V → V → Type w} {C : Type u} [Category.{v} C]
    [Quiver.IsThin C] (φ : GenObj Gen ⥤q C)
    (full : ∀ x y : GenObj Gen, (φ.obj x ⟶ φ.obj y) → Nonempty (Quiver.Path x y))
    (essSurj : ∀ c : C, ∃ x : GenObj Gen, Nonempty (φ.obj x ≅ c)) :
    Presents (Polygraph.thin Gen) C :=
  Presents.ofDesc (P := Polygraph.thin Gen)
    (show GenObj (Polygraph.thin Gen).Gen ⥤q C from φ) (fun _ => Subsingleton.elim _ _)
    (fun {_ _ u v} _ => Quotient.sound _ (Polygraph.thin_homRel u v))
    ⟨fun {x y} f => ⟨(full x y f).some, Subsingleton.elim _ _⟩⟩
    ⟨fun c => essSurj c⟩

end CategoryTheory
