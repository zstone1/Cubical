import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Machinery/Presentation/Basic — polygraphs, and what they present

A `Polygraph` is combinatorial data alone: 0-cells, 1-cells, and 2-cells on the words they spell.
It presents `presented` while naming no other category, so constructions on polygraphs (`comap`,
gluing) stay combinatorial and what they present is a separate theorem.

That theorem is `Presents P C`: a functor `P.presented ⥤ C` which is an equivalence.  `ofDesc` is
the only place its obligations appear; after it, spanning and covering are `Full` and `EssSurj` of
`eval = quot ⋙ E`, completeness is `E.map_injective`, and `transport` is a composition.  `GenObj`
re-quivers `V`, so `Paths` does not pick up a quiver `V` already carries.
-/

universe w' w u'' u' v u

namespace CategoryTheory

/-- A 0-cell: an index for an object, carrying the generating quiver rather than any quiver its
index type already has. -/
structure GenObj {V : Type u'} (Gen : V → V → Type w) where
  /-- the index it names -/
  as : V

instance genObjQuiver {V : Type u'} (Gen : V → V → Type w) : Quiver.{w} (GenObj Gen) :=
  ⟨fun x y => Gen x.as y.as⟩

/-! ## Words along a map of generating quivers

`Paths.lift` into another path category is `Prefunctor.mapPath`; mathlib states this for the
prefunctor, not for the words. -/

namespace Paths

variable {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]

theorem lift_comp_of_map (π : V ⥤q W) {x y : V} (u : Quiver.Path x y) :
    (Paths.lift (π ⋙q Paths.of W)).map u = π.mapPath u := by
  induction u with
  | nil => rfl
  | cons u e ih => rw [Paths.lift_cons, ih]; rfl

theorem lift_of_map {x y : V} (u : Quiver.Path x y) : (Paths.lift (Paths.of V)).map u = u :=
  (lift_comp_of_map (𝟭q V) u).trans (Prefunctor.mapPath_id u)

/-- **A word lifted then pushed forward is a word lifted once** — the pointwise `Paths.lift_unique`,
which is what a proof about words of a `comap` always needs. -/
theorem lift_comp_map {D : Type*} [Category* D] {E : Type*} [Category* E]
    (φ : V ⥤q D) (U : D ⥤ E) {x y : V} (u : Quiver.Path x y) :
    U.map ((Paths.lift φ).map u) = (Paths.lift (φ ⋙q U.toPrefunctor)).map u := by
  induction u with
  | nil => exact U.map_id _
  | cons u e ih => rw [Paths.lift_cons, Paths.lift_cons, ← ih]; exact U.map_comp _ _

end Paths

/-- **A 2-polygraph**: 0-cells, 1-cells between them, and 2-cells relating the words they spell.
The cells are *indices* — nothing here names a category. -/
structure Polygraph where
  /-- the 0-cells -/
  V : Type u'
  /-- the 1-cells -/
  Gen : V → V → Type w
  /-- the 2-cells: parallel pairs of generating words -/
  rel : HomRel (Paths (GenObj Gen))

namespace Polygraph

section Basic

variable (P : Polygraph.{w, u'})

/-- The generating words. -/
abbrev Word : Type u' := Paths (GenObj P.Gen)

/-- A 0-cell, as a vertex of the generating quiver. -/
abbrev pt (a : P.V) : GenObj P.Gen := ⟨a⟩

/-- **The category `P` presents**: the generating words modulo the 2-cells. -/
abbrev presented : Type u' := Quotient P.rel

/-- A word, in the presented category. -/
abbrev quot : P.Word ⥤ P.presented := Quotient.functor P.rel

end Basic

/-! ## Maps of polygraphs

A 1-cell of `P` goes to a *word* of `Q`, and the 2-cells of `P` need only become identities. -/

/-- **A morphism of polygraphs**: each 1-cell spells a word, and each 2-cell holds downstream. -/
structure Hom (P : Polygraph.{w, u'}) (Q : Polygraph.{w', u''}) where
  /-- the word a 1-cell spells -/
  cells : GenObj P.Gen ⥤q Q.Word
  /-- each 2-cell of `P` is an identity in `Q` -/
  rel {x y : GenObj P.Gen} {u v : Quiver.Path x y} :
    P.rel u v → Q.quot.map ((Paths.lift cells).map u) = Q.quot.map ((Paths.lift cells).map v)

namespace Hom

variable {P : Polygraph.{w, u'}} {Q : Polygraph.{w', u''}}

/-- The word a word spells. -/
abbrev words (F : Hom P Q) : P.Word ⥤ Q.Word := Paths.lift F.cells

theorem ext' {F G : Hom P Q} (h : F.cells = G.cells) : F = G := by
  cases F; cases G; subst h; rfl

/-- **The functor a morphism of polygraphs induces.** -/
def functor (F : Hom P Q) : P.presented ⥤ Q.presented :=
  Quotient.lift P.rel (F.words ⋙ Q.quot) fun _ _ _ _ h => F.rel h

theorem quot_comp_functor (F : Hom P Q) : P.quot ⋙ F.functor = F.words ⋙ Q.quot :=
  Quotient.lift_spec _ _ _

/-- The identity. -/
def id (P : Polygraph.{w, u'}) : Hom P P where
  cells := Paths.of _
  rel h := by rw [Paths.lift_of_map, Paths.lift_of_map]; exact Quotient.sound _ h

theorem words_id (P : Polygraph.{w, u'}) : (Hom.id P).words = 𝟭 P.Word :=
  (Paths.lift_unique (Paths.of _) (𝟭 P.Word) rfl).symm

variable {R : Polygraph.{w', u''}}

/-- Composition: substitute the words of `F` into those of `G`. -/
def comp (F : Hom P Q) (G : Hom Q R) : Hom P R where
  cells := F.cells ⋙q G.words.toPrefunctor
  rel h := by
    rw [← Paths.lift_comp_map, ← Paths.lift_comp_map]
    exact congrArg G.functor.map (F.rel h)

theorem words_comp (F : Hom P Q) (G : Hom Q R) : (F.comp G).words = F.words ⋙ G.words :=
  (Paths.lift_unique (F.cells ⋙q G.words.toPrefunctor) (F.words ⋙ G.words)
    (congrArg (· ⋙q G.words.toPrefunctor) (Paths.lift_spec F.cells))).symm

end Hom

instance : Category Polygraph.{w, u'} where
  Hom P Q := Hom P Q
  id := Hom.id
  comp := Hom.comp
  id_comp F := Hom.ext' (Paths.lift_spec F.cells)
  comp_id F := Hom.ext' (by
    change F.cells ⋙q (Hom.words (Hom.id _)).toPrefunctor = F.cells
    rw [Hom.words_id]
    rfl)
  assoc F G H := Hom.ext' (by
    change (F.cells ⋙q _) ⋙q _ = F.cells ⋙q (Hom.words (Hom.comp G H)).toPrefunctor
    rw [Hom.words_comp]
    rfl)

section Functoriality

variable {P Q R : Polygraph.{w, u'}}

@[simp] theorem functor_id : (𝟙 P : P ⟶ P).functor = 𝟭 P.presented :=
  Quotient.lift_unique' _ _ _ (by
    rw [show (𝟙 P : P ⟶ P) = Hom.id P from rfl, Hom.quot_comp_functor, Hom.words_id,
      Functor.id_comp, Functor.comp_id])

@[simp] theorem functor_comp (F : P ⟶ Q) (G : Q ⟶ R) :
    (F ≫ G).functor = F.functor ⋙ G.functor :=
  Quotient.lift_unique' _ _ _ (by
    rw [show (F ≫ G) = Hom.comp F G from rfl, Hom.quot_comp_functor, Hom.words_comp,
      Functor.assoc, ← Hom.quot_comp_functor G, ← Functor.assoc, ← Hom.quot_comp_functor F,
      Functor.assoc])

end Functoriality

/-! ## Pulling a polygraph back

A generating quiver over `P`'s, carrying `P`'s 2-cells on projected words: the shape of every
presentation obtained by restricting, or by acting. -/

section Comap

variable (P : Polygraph.{w, u'}) {V : Type u''} (Gen : V → V → Type w')
  (π : GenObj Gen ⥤q GenObj P.Gen)

/-- Words along a map of generating quivers — `Prefunctor.mapPath`, as a functor. -/
def comapIncl : Paths (GenObj Gen) ⥤ P.Word where
  obj x := π.obj x
  map u := π.mapPath u
  map_id _ := rfl
  map_comp _ _ := Prefunctor.mapPath_comp _ _ _

/-- **`P`'s 2-cells, read on a quiver over `P`'s.** -/
def comap : Polygraph.{w', u''} where
  V := V
  Gen := Gen
  rel := fun _ _ u v => P.rel ((P.comapIncl Gen π).map u) ((P.comapIncl Gen π).map v)

/-- The projection of a `comap`, as a morphism of polygraphs. -/
def comapHom : Hom (P.comap Gen π) P where
  cells := π ⋙q Paths.of _
  rel h := by
    rw [Paths.lift_comp_of_map, Paths.lift_comp_of_map]
    exact Quotient.sound _ h

theorem comapHom_words : (P.comapHom Gen π).words = P.comapIncl Gen π :=
  (Paths.lift_unique (π ⋙q Paths.of _) (P.comapIncl Gen π) rfl).symm

/-- **A comap along a covering is faithful on words**: a word is determined by its projection,
because each step is (`Prefunctor.pathStar_injective`). -/
theorem comapIncl_faithful (hπ : ∀ x : GenObj Gen, Function.Injective (π.star x)) :
    (P.comapIncl Gen π).Faithful where
  map_injective {x y} {u v} h := by
    have hval : π.mapPath u = π.mapPath v := h
    have hs : π.pathStar x ⟨y, u⟩ = π.pathStar x ⟨y, v⟩ := Sigma.ext rfl (heq_of_eq hval)
    exact eq_of_heq (Sigma.mk.inj_iff.mp (π.pathStar_injective hπ x hs)).2

end Comap

end Polygraph

/-! ## Presenting a category -/

/-- **`P` presents `C`**: a functor from the presented category, an equivalence. -/
structure Presents (P : Polygraph.{w, u'}) (C : Type u) [Category.{v} C] where
  /-- the comparison functor -/
  E : P.presented ⥤ C
  /-- …an equivalence -/
  isEquiv : E.IsEquivalence

attribute [instance] Presents.isEquiv

namespace Presents

variable {P : Polygraph.{w, u'}} {C : Type u} [Category.{v} C] (p : Presents P C)

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

/-- **The projected word, evaluated** — every word of a `comap` is read downstairs this way. -/
theorem eval_mapPath {V : Type u''} {Gen : V → V → Type w'} (π : GenObj Gen ⥤q GenObj P.Gen)
    {x y : GenObj Gen} (u : Quiver.Path x y) :
    p.eval.map (π.mapPath u) = (Paths.lift (π ⋙q p.evalPre)).map u := by
  rw [← Paths.lift_comp_of_map π u]
  exact Paths.lift_comp_map _ p.eval u

@[simp] theorem eval_nil (x : GenObj P.Gen) :
    p.eval.map (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (p.at' x) := p.eval.map_id x

@[simp] theorem eval_cons {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) :
    p.eval.map (u.cons e) = p.eval.map u ≫ p.arrow e := p.eval.map_comp u e.toPath

/-- **Related words spell the same arrow.**  Its converse is `p.E.map_injective`. -/
theorem sound {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : P.rel u v) :
    p.eval.map u = p.eval.map v :=
  congrArg p.E.map (Quotient.sound _ h)

/-- **A presentation transports along an equivalence** — the *same* polygraph, read on `D`. -/
def transport {D : Type*} [Category D] (e : C ≌ D) : Presents P D :=
  ⟨p.E ⋙ e.functor, inferInstance⟩

end Presents

/-! ## Building one

An interpretation of the cells is a prefunctor out of the generating quiver; `sound` descends it to
`presented`, and the remaining obligations are that the descent is an equivalence. -/

section Build

variable {P : Polygraph.{w, u'}} {C : Type u} [Category.{v} C] (φ : GenObj P.Gen ⥤q C)
  (sound : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
    P.rel u v → (Paths.lift φ).map u = (Paths.lift φ).map v)

/-- The functor an interpretation of the cells descends to, when it respects the 2-cells. -/
def Polygraph.desc : P.presented ⥤ C :=
  Quotient.lift P.rel (Paths.lift φ) fun _ _ _ _ h => sound h

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

@[simp] theorem Presents.ofDesc_arrow {complete full essSurj} {x y : GenObj P.Gen} (e : x ⟶ y) :
    (Presents.ofDesc φ sound complete full essSurj).arrow e = φ.map e :=
  Paths.lift_toPath φ e

end Build

end CategoryTheory
