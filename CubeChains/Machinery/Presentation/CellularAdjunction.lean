import CubeChains.Machinery.Presentation.Coproduct
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Machinery/Presentation/CellularAdjunction — `presented` is a left adjoint

A `Polygraph.Hom` spells a 1-cell by a *word*, so it is a map into the free category on the
target's generators; a `CellHom` spells it by a 1-cell.  On the cellular category `PolyCell`,
`presented` acquires a right adjoint `catPoly` — a category read as the polygraph of all its
arrows, related when they compose alike — and therefore preserves every colimit.

`Polygraph.desc` is the transpose: its `φ : GenObj P.Gen ⥤q C` is exactly a cellular map
`P ⟶ catPoly C`, and its `sound` hypothesis is exactly `CellHom.rel` read through `catEval`.

The colimits preserved are the **strict** ones of `Cat`, and those do not see levelwise
equivalence: the coequalizer of `1 ⇉ (walking iso)` is `SingleObj ℤ` while the coequalizer of the
levelwise-equivalent `1 ⇉ 1` is `1`.  So `presentsColimit` asks for the colimit of the *presented*
categories themselves, not of a diagram merely equivalent to them.
-/

universe w'' w' w u''' u'' u' u v

namespace CategoryTheory

/-- **Equal prefunctors agree on 1-cells**, up to the transport their 0-cells carry. -/
theorem Prefunctor.map_of_eq {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {F G : V ⥤q W} (h : F = G) {x y : V} (e : x ⟶ y) :
    F.map e = Quiver.homOfEq (G.map e)
      (congrArg (fun φ : V ⥤q W => φ.obj x) h).symm
      (congrArg (fun φ : V ⥤q W => φ.obj y) h).symm := by
  subst h; rfl

namespace Polygraph

/-! ## Cellular maps -/

/-- **A cellular map of polygraphs**: a 1-cell goes to a 1-cell, not to a word. -/
structure CellHom (P : Polygraph.{w, u'}) (Q : Polygraph.{w', u''}) where
  /-- the 1-cell a 1-cell spells -/
  pre : GenObj P.Gen ⥤q GenObj Q.Gen
  /-- each 2-cell of `P` is an identity in `Q` -/
  rel {x y : GenObj P.Gen} {u v : Quiver.Path x y} :
    P.rel u v → Q.quot.map (pre.mapPath u) = Q.quot.map (pre.mapPath v)

namespace CellHom

variable {P : Polygraph.{w, u'}} {Q : Polygraph.{w', u''}}

theorem ext' {f g : CellHom P Q} (h : f.pre = g.pre) : f = g := by
  cases f; cases g; subst h; rfl

/-- The word-valued map a cellular map spells. -/
def toHom (f : CellHom P Q) : Hom P Q := Hom.ofPre f.pre f.rel

/-- The identity. -/
def id (P : Polygraph.{w, u'}) : CellHom P P where
  pre := 𝟭q _
  rel h := by
    rw [Prefunctor.mapPath_id, Prefunctor.mapPath_id]; exact Quotient.sound _ h

/-- Composition. -/
def comp {R : Polygraph.{w'', u'''}} (f : CellHom P Q) (g : CellHom Q R) : CellHom P R where
  pre := f.pre ⋙q g.pre
  rel h := by
    rw [Prefunctor.mapPath_comp_apply, Prefunctor.mapPath_comp_apply]
    exact quot_mapPath_congr Q R g.pre (fun hr => g.rel hr) (f.rel h)

end CellHom

end Polygraph

/-- **Polygraphs and cellular maps.** -/
def PolyCell : Type max (u' + 1) (w + 1) := Polygraph.{w, u'}

namespace PolyCell

/-- The polygraph a 0-cell of `PolyCell` is. -/
def toPoly (P : PolyCell.{w, u'}) : Polygraph.{w, u'} := P

/-- A polygraph, read in `PolyCell`. -/
def of (P : Polygraph.{w, u'}) : PolyCell.{w, u'} := P

instance : Category PolyCell.{w, u'} where
  Hom P Q := Polygraph.CellHom P.toPoly Q.toPoly
  id P := Polygraph.CellHom.id P.toPoly
  comp f g := f.comp g
  id_comp _ := Polygraph.CellHom.ext' rfl
  comp_id _ := Polygraph.CellHom.ext' rfl
  assoc _ _ _ := Polygraph.CellHom.ext' rfl

@[simp] theorem id_pre (P : PolyCell.{w, u'}) : (𝟙 P : P ⟶ P).pre = 𝟭q _ := rfl

@[simp] theorem comp_pre {P Q R : PolyCell.{w, u'}} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).pre = f.pre ⋙q g.pre := rfl

end PolyCell

namespace Polygraph

/-! ## A category, read as a polygraph

Its 0-cells are the objects, its 1-cells *all* the arrows, and its 2-cells "the two words have the
same composite".  Nothing is free here: `catPre` is the tautological interpretation. -/

variable (C : Type u) [Category.{v} C]

/-- The generating quiver of a category: its own arrows. -/
def catGen : C → C → Type v := fun X Y => X ⟶ Y

/-- The tautological interpretation of a category's own arrows. -/
def catPre : GenObj (catGen C) ⥤q C where
  obj x := x.as
  map f := f

/-- **A category, as a polygraph**: every arrow a 1-cell, related when they compose alike. -/
def catPoly : Polygraph.{v, u} where
  V := C
  Gen := catGen C
  rel := fun _ _ u v => (Paths.lift (catPre C)).map u = (Paths.lift (catPre C)).map v

/-- **The composite of a word of arrows**, on the presented category — the counit. -/
def catEval : (catPoly C).presented ⥤ C :=
  Quotient.lift _ (Paths.lift (catPre C)) fun _ _ _ _ h => h

@[simp] theorem catEval_quot {x y : GenObj (catGen C)} (u : Quiver.Path x y) :
    (catEval C).map ((catPoly C).quot.map u) = (Paths.lift (catPre C)).map u := rfl

variable {C} {D : Type u} [Category.{v} D]

/-- A functor, read on the generating quivers. -/
def catPreMap (F : C ⥤ D) : GenObj (catGen C) ⥤q GenObj (catGen D) where
  obj x := ⟨F.obj x.as⟩
  map f := F.map f

theorem catPreMap_comp_catPre (F : C ⥤ D) :
    catPreMap F ⋙q catPre D = catPre C ⋙q F.toPrefunctor := rfl

/-- **A word of arrows, pushed forward, composes to the pushforward of the composite.** -/
theorem lift_catPreMap (F : C ⥤ D) {x y : GenObj (catGen C)} (u : Quiver.Path x y) :
    (Paths.lift (catPre D)).map ((catPreMap F).mapPath u)
      = F.map ((Paths.lift (catPre C)).map u) :=
  (Paths.lift_mapPath (catPreMap F) (catPre D) u).trans (Paths.lift_comp_map (catPre C) F u).symm

/-- A functor is a cellular map of the polygraphs it and its target are. -/
def catCell (F : C ⥤ D) : CellHom (catPoly C) (catPoly D) where
  pre := show GenObj (catGen C) ⥤q GenObj (catGen D) from catPreMap F
  rel := @fun _ _ u v h => Quotient.sound _
    ((lift_catPreMap F u).trans
      ((congrArg F.map (h : (Paths.lift (catPre C)).map u = _)).trans
        (lift_catPreMap F v).symm))


/-! ## The transpose

`Polygraph.desc` is the forward direction of the hom-set bijection: its interpretation of the
cells is exactly a cellular map into `catPoly C`, and its `sound` hypothesis is exactly
`CellHom.rel` read through `catEval`. -/

section Transpose

variable {P : Polygraph.{w, u'}} {C : Type u} [Category.{v} C]

/-- The cells of `P`, interpreted in `C` by a cellular map into `catPoly C`. -/
def cellEval (f : CellHom P (catPoly C)) : GenObj P.Gen ⥤q C := f.pre ⋙q catPre C

/-- **`CellHom.rel` *is* `desc`'s `sound`** — read through `catEval`, which is where a 2-cell of
`catPoly C` says the two words compose alike. -/
theorem cellEval_sound (f : CellHom P (catPoly C)) {x y : GenObj P.Gen}
    {u v : Quiver.Path x y} (h : P.rel u v) :
    (Paths.lift (cellEval f)).map u = (Paths.lift (cellEval f)).map v := by
  have h' : (Paths.lift (catPre C)).map (f.pre.mapPath u)
      = (Paths.lift (catPre C)).map (f.pre.mapPath v) := congrArg (catEval C).map (f.rel h)
  exact (Paths.lift_mapPath f.pre (catPre C) u).symm.trans
    (h'.trans (Paths.lift_mapPath f.pre (catPre C) v))

/-- **The transpose**, forwards: `Polygraph.desc` at a cellular map. -/
def homToFun (f : CellHom P (catPoly C)) : P.presented ⥤ C :=
  P.desc (cellEval f) (cellEval_sound f)

/-- The cells of `P` named by a functor out of `presented`. -/
def homInvPre (F : P.presented ⥤ C) : GenObj P.Gen ⥤q GenObj (catGen C) where
  obj x := ⟨F.obj (P.quot.obj x)⟩
  map e := F.map (P.quot.map e.toPath)

theorem homInvPre_comp_catPre (F : P.presented ⥤ C) :
    homInvPre F ⋙q catPre C = Paths.of (GenObj P.Gen) ⋙q (P.quot ⋙ F).toPrefunctor := rfl

/-- **A word, read through a functor out of `presented`, is that functor on the word.** -/
theorem lift_homInvPre (F : P.presented ⥤ C) {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift (homInvPre F ⋙q catPre C)).map u = F.map (P.quot.map u) :=
  (Paths.lift_comp_map (Paths.of (GenObj P.Gen)) (P.quot ⋙ F) u).symm.trans
    (congrArg (P.quot ⋙ F).map (Paths.lift_of_map u))

/-- **The transpose**, backwards. -/
def homInvFun (F : P.presented ⥤ C) : CellHom P (catPoly C) where
  pre := show GenObj P.Gen ⥤q GenObj (catGen C) from homInvPre F
  rel := @fun _ _ u v h => Quotient.sound _
    ((Paths.lift_mapPath (homInvPre F) (catPre C) u).trans
      ((lift_homInvPre F u).trans
        ((congrArg F.map (Quotient.sound P.rel h)).trans
          ((lift_homInvPre F v).symm.trans
            (Paths.lift_mapPath (homInvPre F) (catPre C) v).symm))))

/-- **`⟨generators | relations⟩ ⊣ arrows`, on hom-sets**: a cellular map into the polygraph of a
category's own arrows is a functor out of the presented category. -/
def cellHomEquiv (P : Polygraph.{w, u'}) (C : Type u) [Category.{v} C] :
    CellHom P (catPoly C) ≃ (P.presented ⥤ C) where
  toFun := homToFun
  invFun := homInvFun
  left_inv f := CellHom.ext' (Prefunctor.ext (fun _ => rfl)
    (fun _ _ e => Paths.lift_toPath (cellEval f) e))
  right_inv F := by
    refine Quotient.lift_unique' P.rel _ F ?_
    have h1 : P.quot ⋙ homToFun (homInvFun F) = Paths.lift (homInvPre F ⋙q catPre C) :=
      Quotient.lift_spec P.rel (Paths.lift (cellEval (homInvFun F)))
        (fun _ _ _ _ h => cellEval_sound (homInvFun F) h)
    exact h1.trans (Paths.lift_unique _ (P.quot ⋙ F) (homInvPre_comp_catPre F).symm).symm

end Transpose

/-! ## Substituting words

`Paths.lift` turns a map of generating quivers into a functor of word categories; substituting
one word map into a lift is the lift of the composite. -/

theorem lift_comp_lift {V : Type u'} [Quiver.{w} V] {W : Type u''} [Quiver.{w'} W]
    {D : Type u} [Category.{v} D] (π : V ⥤q W) (φ : W ⥤q D) :
    Paths.lift (π ⋙q Paths.of W) ⋙ Paths.lift φ = Paths.lift (π ⋙q φ) :=
  Paths.lift_unique _ _
    ((congrArg (· ⋙q (Paths.lift φ).toPrefunctor) (Paths.lift_spec (π ⋙q Paths.of W))).trans
      (congrArg (π ⋙q ·) (Paths.lift_spec φ)))

/-! ## The adjunction

`presented` is a left adjoint on the cellular category, so it preserves every colimit: a colimit
of presentations presents the colimit. -/

section Adj

/-- `presented`, as a functor on cellular maps. -/
def presentedFunctor : PolyCell.{max u v, u} ⥤ Cat.{max u v, u} where
  obj P := Cat.of P.toPoly.presented
  map f := Functor.toCatHom (CellHom.toHom f).functor
  map_id P := Cat.ext (by
    refine Eq.trans (congrArg Hom.functor (Hom.ext' (rfl : _ = (Hom.id P.toPoly).cells))) ?_
    exact functor_id)
  map_comp f g := Cat.ext (by
    refine Eq.trans (congrArg Hom.functor
      (Hom.ext' (?_ : _ = ((CellHom.toHom f).comp (CellHom.toHom g)).cells))) ?_
    · exact (congrArg (f.pre ⋙q ·) (Paths.lift_spec (g.pre ⋙q Paths.of _))).symm
    · exact functor_comp _ _)

/-- A category, as a polygraph, functorially. -/
def catPolyFunctor : Cat.{max u v, u} ⥤ PolyCell.{max u v, u} where
  obj C := PolyCell.of (catPoly C)
  map G := catCell G.toFunctor
  map_id _ := CellHom.ext' rfl
  map_comp _ _ := CellHom.ext' rfl

/-- **`⟨generators | relations⟩ ⊣ arrows`.**  Hence `presented` preserves all colimits: the
colimit of a family of presentations presents the colimit of what they present. -/
def presentedAdj : presentedFunctor.{u, v} ⊣ catPolyFunctor.{u, v} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P C => (Cat.Hom.equivFunctor _ C).trans (cellHomEquiv P.toPoly C).symm
      homEquiv_naturality_left_symm := fun {P' P C} f g => Cat.ext (by
        refine Quotient.lift_unique' P'.toPoly.rel (homToFun (f.comp g))
          ((CellHom.toHom f).functor ⋙ homToFun g) ?_
        have h1 : P'.toPoly.quot ⋙ homToFun (f.comp g)
            = Paths.lift (f.pre ⋙q cellEval g) :=
          Quotient.lift_spec P'.toPoly.rel (Paths.lift (cellEval (f.comp g)))
            (fun _ _ _ _ h => cellEval_sound (f.comp g) h)
        have h2 : P'.toPoly.quot ⋙ (CellHom.toHom f).functor ⋙ homToFun g
            = Paths.lift (f.pre ⋙q Paths.of _) ⋙ P.toPoly.quot ⋙ homToFun g := by
          rw [← Functor.assoc, Hom.quot_comp_functor]
          rfl
        have h3 : P.toPoly.quot ⋙ homToFun g = Paths.lift (cellEval g) :=
          Quotient.lift_spec P.toPoly.rel (Paths.lift (cellEval g))
            (fun _ _ _ _ h => cellEval_sound g h)
        rw [h1, h2, h3, lift_comp_lift])
      homEquiv_naturality_right := fun _ _ => CellHom.ext' rfl }

/-- `presented` preserves every colimit. -/
instance : Limits.PreservesColimitsOfSize.{v', u'''} presentedFunctor.{u, v} :=
  presentedAdj.leftAdjoint_preservesColimits


/-! ## What the adjunction gives

The counit is a presentation, a tautological one: every arrow a generator.  So a presentation
always exists and the content is in replacing it by a *compact* polygraph.  What transports for
free is `presentsColimit`: a colimit of polygraphs presents the colimit of what they present. -/

/-- **A category presents itself**, by all its arrows.  The counit of the adjunction. -/
def presentsCatPoly (C : Type u) [Category.{v} C] : Presents (catPoly C) C :=
  Presents.ofDesc (catPre C) id (fun h => Quotient.sound _ h)
    { map_surjective := fun {x y} f =>
        ⟨@Quiver.Hom.toPath (GenObj (catGen C)) _ x y f, Paths.lift_toPath (catPre C) f⟩ }
    { mem_essImage := fun X => ⟨⟨X⟩, ⟨Iso.refl _⟩⟩ }

/-- **A colimit of polygraphs presents the colimit of what they present** — the whole content of
`presented ⊣ catPoly`, in the form a presentation of a glued category needs. -/
noncomputable def presentsColimit {J : Type u''} [Category.{w''} J]
    (D : J ⥤ PolyCell.{max u v, u}) [Limits.HasColimit D]
    [Limits.HasColimit (D ⋙ presentedFunctor.{u, v})] :
    Presents (Limits.colimit D).toPoly ↥(Limits.colimit (D ⋙ presentedFunctor.{u, v})) where
  E := (preservesColimitIso presentedFunctor.{u, v} D).hom.toFunctor
  isEquiv := (Cat.equivOfIso (preservesColimitIso presentedFunctor.{u, v} D)).isEquivalence_functor
end Adj

end Polygraph


namespace PolyCell

open Limits Polygraph

/-! ## Coproducts

`Polygraph.coproduct` is the coproduct in `PolyCell`: a 1-cell of the disjoint union lies in one
fibre and a 2-cell is a fibre's own, so a cellular map out of it is exactly a family. -/

variable {ι : Type u} (P : ι → PolyCell.{max u v, u})

/-- The disjoint union, in `PolyCell`. -/
def coprodObj : PolyCell.{max u v, u} := PolyCell.of (coproduct fun i => (P i).toPoly)

/-- The fibre inclusion, cellular. -/
def coprodInj (i : ι) : P i ⟶ coprodObj P where
  pre := coproductPre _ i
  rel := coproductRel_sound _ i

variable {R : PolyCell.{max u v, u}} (m : ∀ i, P i ⟶ R)

/-- The arrow a 1-cell of the coproduct is sent to: the fibre it lies in decides. -/
def coprodDescMap : ∀ (a b : Σ i, (P i).toPoly.V),
    CoproductGen (fun i => (P i).toPoly) a b →
      ((m a.1).pre.obj ⟨a.2⟩ ⟶ (m b.1).pre.obj ⟨b.2⟩)
  | _, _, .mk g => (m _).pre.map g

/-- The cells of the coproduct, read by a family. -/
def coprodDescPre : GenObj (CoproductGen fun i => (P i).toPoly) ⥤q GenObj R.toPoly.Gen where
  obj x := (m x.as.1).pre.obj ⟨x.as.2⟩
  map {x y} e := coprodDescMap P m x.as y.as e

theorem coproductPre_comp_descPre (i : ι) :
    coproductPre (fun i => (P i).toPoly) i ⋙q coprodDescPre P m = (m i).pre := rfl

/-- **A fibre's word, read by the descent, is that fibre's own reading.**  An induction, not a
`rfl`: `mapPath` on a variable word is stuck even though the two prefunctors are the same. -/
theorem descPre_mapPath (i : ι) {a b : GenObj (P i).toPoly.Gen} (w : Quiver.Path a b) :
    (coprodDescPre P m).mapPath ((coproductPre (fun i => (P i).toPoly) i).mapPath w)
      = (m i).pre.mapPath w := by
  induction w with
  | nil => rfl
  | cons w' g ih => exact congrArg (fun p => Quiver.Path.cons p ((m i).pre.map g)) ih

/-- The descent of a family. -/
def coprodDesc : coprodObj P ⟶ R where
  pre := coprodDescPre P m
  rel := @fun _ _ _ _ h => by
    cases h with
    | @mk i _ _ u v hr =>
      exact (congrArg R.toPoly.quot.map (descPre_mapPath P m i u)).trans
        (((m i).rel hr).trans (congrArg R.toPoly.quot.map (descPre_mapPath P m i v)).symm)

theorem coprodInj_desc (i : ι) : coprodInj P i ≫ coprodDesc P m = m i :=
  Polygraph.CellHom.ext' rfl

theorem coprodDesc_uniq (n : coprodObj P ⟶ R) (hn : ∀ i, coprodInj P i ≫ n = m i) :
    n = coprodDesc P m := by
  have key : ∀ i, coproductPre (fun i => (P i).toPoly) i ⋙q n.pre = (m i).pre :=
    fun i => congrArg Polygraph.CellHom.pre (hn i)
  refine Polygraph.CellHom.ext' (Prefunctor.ext' ?_ ?_)
  · rintro ⟨⟨i, a⟩⟩
    exact congrArg (fun φ : GenObj (P i).toPoly.Gen ⥤q GenObj R.toPoly.Gen => φ.obj ⟨a⟩) (key i)
  · rintro ⟨⟨i, a⟩⟩ ⟨⟨j, b⟩⟩ e
    cases e with
    | @mk _ _ _ g =>
      exact Prefunctor.map_of_eq (F := coproductPre (fun i => (P i).toPoly) i ⋙q n.pre)
        (G := (m i).pre) (key i) g

/-- **The disjoint union is the coproduct.** -/
def coprodIsColimit : IsColimit (Cofan.mk (coprodObj P) (coprodInj P)) :=
  Cofan.IsColimit.mk _ (fun t => coprodDesc P t.inj) (fun t => coprodInj_desc P t.inj)
    (fun t n hn => coprodDesc_uniq P t.inj n hn)

instance : HasCoproduct P := HasColimit.mk ⟨_, coprodIsColimit P⟩

end PolyCell

end CategoryTheory
