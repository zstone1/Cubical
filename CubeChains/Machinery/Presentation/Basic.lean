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

/-- **A word pushed forward then interpreted is the word interpreted along the composite** — not a
new recursion on paths, only `lift_comp_map` re-associated through `lift_spec`. -/
theorem lift_mapPath {D : Type*} [Category* D] (π : V ⥤q W) (φ : W ⥤q D) {x y : V}
    (u : Quiver.Path x y) :
    (Paths.lift φ).map (π.mapPath u) = (Paths.lift (π ⋙q φ)).map u := by
  have h : (Paths.lift φ).map (π.mapPath u)
      = (Paths.lift ((π ⋙q Paths.of W) ⋙q (Paths.lift φ).toPrefunctor)).map u := by
    rw [← Paths.lift_comp_of_map π u]
    exact Paths.lift_comp_map (π ⋙q Paths.of W) (Paths.lift φ) u
  rw [h]
  congr 1
  exact congrArg Paths.lift (congrArg (π ⋙q ·) (Paths.lift_spec φ))

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

/-- **A map of generating quivers killing `P`'s 2-cells is a morphism of polygraphs.** -/
def ofPre (π : GenObj P.Gen ⥤q GenObj Q.Gen)
    (hrel : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      P.rel u v → Q.quot.map (π.mapPath u) = Q.quot.map (π.mapPath v)) : Hom P Q where
  cells := π ⋙q Paths.of _
  rel h := by rw [Paths.lift_comp_of_map, Paths.lift_comp_of_map]; exact hrel h

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
def comapHom : Hom (P.comap Gen π) P :=
  Hom.ofPre π fun h => Quotient.sound _ h

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

/-- **A comap along a covering is full on words**: every word between projected 0-cells is
projected, because each step is (`Prefunctor.pathStar_surjective`). -/
theorem comapIncl_full (hπ : ∀ x : GenObj Gen, Function.Surjective (π.star x))
    (hobj : Function.Injective π.obj) : (P.comapIncl Gen π).Full where
  map_surjective {x y} u := by
    obtain ⟨⟨y', u'⟩, h⟩ := π.pathStar_surjective hπ x ⟨π.obj y, u⟩
    obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := hobj h₁
    exact ⟨u', eq_of_heq h₂⟩

/-- **Every word out of a lifted 0-cell lifts** — star-surjectivity, read on words. -/
theorem exists_comapIncl_map_out (hπ : ∀ x : GenObj Gen, Function.Surjective (π.star x))
    {x : Paths (GenObj Gen)} {z : P.Word} (f : (P.comapIncl Gen π).obj x ⟶ z) :
    ∃ (z' : Paths (GenObj Gen)) (_ : (P.comapIncl Gen π).obj z' = z) (f' : x ⟶ z'),
      (P.comapIncl Gen π).map f' ≍ f := by
  obtain ⟨⟨z', f'⟩, hf⟩ := π.pathStar_surjective hπ x ⟨z, f⟩
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp hf
  exact ⟨z', h₁, f', h₂⟩

/-- A word of a comap, read in the presented category downstairs. -/
theorem comapHom_functor_map {x y : Paths (GenObj Gen)} (u : x ⟶ y) :
    (P.comapHom Gen π).functor.map ((P.comap Gen π).quot.map u)
      = P.quot.map ((P.comapIncl Gen π).map u) :=
  congrArg P.quot.map (Paths.lift_comp_of_map π u)

variable (hsurj : ∀ x : GenObj Gen, Function.Surjective (π.star x))
  (hinj : ∀ x : GenObj Gen, Function.Injective (π.star x))
  (hobj : Function.Injective π.obj)

include hsurj hinj hobj in
/-- One rewriting step downstairs between lifted words is one rewriting step upstairs.  The
endpoints are quantified *inside* so that `cases` sees `CompClosure`'s indices as variables, and
they are spelled in `P.Word` rather than in `GenObj P.Gen` for the same reason. -/
theorem compClosure_reflect {X Y : P.Word} {U U' : X ⟶ Y}
    (h : HomRel.CompClosure P.rel U U') :
    ∀ {x y : Paths (GenObj Gen)}, (P.comapIncl Gen π).obj x = X →
      (P.comapIncl Gen π).obj y = Y → ∀ {u v : x ⟶ y},
      (P.comapIncl Gen π).map u ≍ U → (P.comapIncl Gen π).map v ≍ U' →
        HomRel.CompClosure (P.comap Gen π).rel u v := by
  haveI := P.comapIncl_full Gen π hsurj hobj
  haveI := P.comapIncl_faithful Gen π hinj
  cases h with
  | intro a b f m₁ m₂ g hr =>
    rintro x y rfl rfl u v hu hv
    obtain ⟨a', rfl, f', hf⟩ := P.exists_comapIncl_map_out Gen π hsurj f
    obtain rfl := eq_of_heq hf
    obtain ⟨b', rfl, m₁', hm₁⟩ := P.exists_comapIncl_map_out Gen π hsurj m₁
    obtain rfl := eq_of_heq hm₁
    obtain ⟨m₂', rfl⟩ := (P.comapIncl Gen π).map_surjective m₂
    obtain ⟨g', rfl⟩ := (P.comapIncl Gen π).map_surjective g
    obtain rfl : u = f' ≫ m₁' ≫ g' := by
      refine (P.comapIncl Gen π).map_injective ?_
      rw [Functor.map_comp, Functor.map_comp]
      exact eq_of_heq hu
    obtain rfl : v = f' ≫ m₂' ≫ g' := by
      refine (P.comapIncl Gen π).map_injective ?_
      rw [Functor.map_comp, Functor.map_comp]
      exact eq_of_heq hv
    exact HomRel.CompClosure.intro a' b' f' m₁' m₂' g' hr

include hsurj hinj hobj in
/-- **A comap along a covering reflects equality of presented arrows.**  A chain of rewrites
downstairs lifts step by step, because each of its terms is a word between lifted 0-cells, hence
itself lifted. -/
theorem comap_quot_map_injective {x y : Paths (GenObj Gen)} {u v : x ⟶ y}
    (h : P.quot.map ((P.comapIncl Gen π).map u) = P.quot.map ((P.comapIncl Gen π).map v)) :
    (P.comap Gen π).quot.map u = (P.comap Gen π).quot.map v := by
  haveI := P.comapIncl_full Gen π hsurj hobj
  haveI := P.comapIncl_faithful Gen π hinj
  refine (Quotient.functor_homRel_eq_compClosure_eqvGen (P.comap Gen π).rel u v).mpr ?_
  have h' := (Quotient.functor_homRel_eq_compClosure_eqvGen P.rel
    ((P.comapIncl Gen π).map u) ((P.comapIncl Gen π).map v)).mp h
  suffices H : ∀ U U' : (P.comapIncl Gen π).obj x ⟶ (P.comapIncl Gen π).obj y,
      Relation.EqvGen (@HomRel.CompClosure P.Word _ P.rel _ _) U U' →
      ∀ u v : x ⟶ y, (P.comapIncl Gen π).map u = U → (P.comapIncl Gen π).map v = U' →
        Relation.EqvGen (@HomRel.CompClosure _ _ (P.comap Gen π).rel x y) u v from
    H _ _ h' u v rfl rfl
  intro U U' hUU'
  induction hUU' with
  | rel U U' hr =>
      exact fun u v hu hv => Relation.EqvGen.rel _ _
        (P.compClosure_reflect Gen π hsurj hinj hobj hr rfl rfl (heq_of_eq hu) (heq_of_eq hv))
  | refl U =>
      intro u v hu hv
      obtain rfl := (P.comapIncl Gen π).map_injective (hu.trans hv.symm)
      exact Relation.EqvGen.refl _
  | symm U U' _ ih => exact fun u v hu hv => (ih v u hv hu).symm
  | trans U U' U'' _ _ ih₁ ih₂ =>
      intro u v hu hv
      obtain ⟨w, hw⟩ := (P.comapIncl Gen π).map_surjective U'
      exact Relation.EqvGen.trans _ _ _ (ih₁ u w hu hw) (ih₂ w v hw hv)

include hsurj hobj in
/-- **A comap along a covering is full on the presented categories.** -/
theorem comapHom_functor_full : (P.comapHom Gen π).functor.Full where
  map_surjective {X Y} f := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    obtain ⟨U, rfl⟩ := P.quot.map_surjective f
    obtain ⟨u, rfl⟩ := (P.comapIncl_full Gen π hsurj hobj).map_surjective U
    exact ⟨(P.comap Gen π).quot.map u, P.comapHom_functor_map Gen π u⟩

include hsurj hinj hobj in
/-- **…and faithful.** -/
theorem comapHom_functor_faithful : (P.comapHom Gen π).functor.Faithful where
  map_injective {X Y} {f g} h := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    obtain ⟨u, rfl⟩ := (P.comap Gen π).quot.map_surjective f
    obtain ⟨v, rfl⟩ := (P.comap Gen π).quot.map_surjective g
    refine P.comap_quot_map_injective Gen π hsurj hinj hobj ?_
    rw [← P.comapHom_functor_map Gen π u, ← P.comapHom_functor_map Gen π v]
    exact h

end Comap

/-- **A map of generating quivers respecting the 2-cells respects the congruence they generate** —
the `Hom.ofPre` hypothesis, upgraded from `rel` to equality of words in the quotient. -/
theorem quot_mapPath_congr (P : Polygraph.{w, u'}) (Q : Polygraph.{w', u''})
    (π : GenObj P.Gen ⥤q GenObj Q.Gen)
    (hrel : ∀ {x y : GenObj P.Gen} {u v : Quiver.Path x y},
      P.rel u v → Q.quot.map (π.mapPath u) = Q.quot.map (π.mapPath v))
    {x y : GenObj P.Gen} {u v : Quiver.Path x y} (h : P.quot.map u = P.quot.map v) :
    Q.quot.map (π.mapPath u) = Q.quot.map (π.mapPath v) := by
  have H : ∀ (a b : P.Word) (f g : a ⟶ b), P.rel f g →
      (Q.comapIncl P.Gen π ⋙ Q.quot).map f = (Q.comapIncl P.Gen π ⋙ Q.quot).map g :=
    fun _ _ _ _ hr => hrel hr
  have e : ∀ w : Quiver.Path x y,
      Q.quot.map (π.mapPath w) = (Quotient.lift P.rel _ H).map (P.quot.map w) := fun _ => rfl
  rw [e, e, h]

/-! ## The full subpolygraph on a set of 0-cells

A comap along the inclusion of a set of 0-cells.  When no 1-cell leaves the set, that inclusion is
a covering, so the subpolygraph presents a full subcategory. -/

section Restrict

variable (P : Polygraph.{w, u'}) (S : P.V → Prop)

/-- The 1-cells between 0-cells satisfying `S`. -/
def restrictGen : {a : P.V // S a} → {a : P.V // S a} → Type w := fun x y => P.Gen x.1 y.1

/-- The inclusion of the 0-cells satisfying `S`. -/
def restrictPre : GenObj (P.restrictGen S) ⥤q GenObj P.Gen where
  obj x := ⟨x.as.1⟩
  map e := e

/-- **The full subpolygraph on the 0-cells satisfying `S`.** -/
def restrict : Polygraph.{w, u'} := P.comap (P.restrictGen S) (P.restrictPre S)

/-- The inclusion of a full subpolygraph. -/
def restrictHom : Hom (P.restrict S) P := P.comapHom (P.restrictGen S) (P.restrictPre S)

theorem restrictPre_obj_injective : Function.Injective (P.restrictPre S).obj := by
  rintro ⟨⟨x, hx⟩⟩ ⟨⟨y, hy⟩⟩ h
  obtain rfl : x = y := congrArg GenObj.as h
  rfl

theorem restrictPre_star_injective (x : GenObj (P.restrictGen S)) :
    Function.Injective ((P.restrictPre S).star x) := by
  rintro ⟨⟨⟨y, hy⟩⟩, e⟩ ⟨⟨⟨z, hz⟩⟩, e'⟩ h
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : y = z := congrArg GenObj.as h₁
  exact congrArg (Sigma.mk _) (eq_of_heq h₂)

variable (hS : ∀ {a b : P.V}, S a → P.Gen a b → S b)

include hS in
theorem restrictPre_star_surjective (x : GenObj (P.restrictGen S)) :
    Function.Surjective ((P.restrictPre S).star x) := by
  rintro ⟨⟨y⟩, e⟩
  exact ⟨⟨⟨⟨y, hS x.as.2 e⟩⟩, e⟩, rfl⟩

include hS in
/-- **A full subpolygraph no 1-cell leaves is full on the presented categories.** -/
theorem restrictHom_functor_full : (P.restrictHom S).functor.Full :=
  P.comapHom_functor_full _ _ (P.restrictPre_star_surjective S hS) (P.restrictPre_obj_injective S)

include hS in
/-- **…and faithful**: a word of `P` between its 0-cells is one of its own, and so is every
rewriting of one. -/
theorem restrictHom_functor_faithful : (P.restrictHom S).functor.Faithful :=
  P.comapHom_functor_faithful _ _ (P.restrictPre_star_surjective S hS)
    (P.restrictPre_star_injective S) (P.restrictPre_obj_injective S)

end Restrict

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

@[simp] theorem Presents.ofDesc_arrow {complete full essSurj} {x y : GenObj P.Gen} (e : x ⟶ y) :
    (Presents.ofDesc φ sound complete full essSurj).arrow e = φ.map e :=
  Paths.lift_toPath φ e

end Build

end CategoryTheory
