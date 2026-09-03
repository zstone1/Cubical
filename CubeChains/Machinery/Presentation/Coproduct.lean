import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.SigmaComponents
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Machinery/Presentation/Coproduct — coproducts of polygraphs, and their components

`Polygraph.coproduct P` is the disjoint union: a 1-cell lives in one fibre, a 2-cell is a fibre's
own.  The fibre constraint is carried by an **indexed inductive** (`CoproductGen`, mirroring
mathlib's `Sigma.SigmaHom`) rather than by `Σ' h : i = j, …`: `cases` then reads the fibre off a
1-cell and no transport is ever spelled, at the price of a universe bump on `Gen`.

The fibre inclusion of generating quivers is star-surjective and injective on 0-cells, so a word of
the coproduct between 0-cells of one fibre is that fibre's word (`comapIncl_full`); that, plus the
absence of cross-fibre words, is the whole content of `Presents.coproduct`.  `Presents.component`
is the converse, for an *arbitrary* presentation of a hom-disjointly covered category.
-/

universe t w u' v u

namespace CategoryTheory

namespace Polygraph

variable {ι : Type t} (P : ι → Polygraph.{w, u'})

/-- 1-cells of a coproduct: a fibre's own, and nothing across fibres. -/
inductive CoproductGen : (Σ i, (P i).V) → (Σ i, (P i).V) → Type (max t u' w)
  | mk {i : ι} {x y : (P i).V} : (P i).Gen x y → CoproductGen ⟨i, x⟩ ⟨i, y⟩

/-- The fibre a 0-cell belongs to is preserved by a 1-cell. -/
theorem CoproductGen.fst_eq {a b : Σ i, (P i).V} (e : CoproductGen P a b) : a.1 = b.1 := by
  cases e; rfl

/-- The inclusion of one fibre's generating quiver. -/
def coproductPre (i : ι) : GenObj (P i).Gen ⥤q GenObj (CoproductGen P) where
  obj x := ⟨⟨i, x.as⟩⟩
  map e := CoproductGen.mk e

/-- 2-cells of a coproduct: a fibre's own, read on the coproduct's words. -/
inductive CoproductRel : ∀ {a b : Paths (GenObj (CoproductGen P))}, (a ⟶ b) → (a ⟶ b) → Prop
  | mk {i : ι} {x y : GenObj (P i).Gen} {u v : Quiver.Path x y} :
      (P i).rel u v → CoproductRel ((coproductPre P i).mapPath u) ((coproductPre P i).mapPath v)

/-- **The coproduct of polygraphs.** -/
def coproduct : Polygraph.{max t u' w, max t u'} where
  V := Σ i, (P i).V
  Gen := CoproductGen P
  rel := fun _ _ => CoproductRel P

/-- A word of the coproduct stays in the fibre it starts in. -/
theorem coproduct_path_fst {a b : GenObj (CoproductGen P)} (u : Quiver.Path a b) :
    a.as.1 = b.as.1 := by
  induction u with
  | nil => rfl
  | cons _ e ih => exact ih.trans (CoproductGen.fst_eq P e)

theorem coproductPre_obj_injective (i : ι) : Function.Injective (coproductPre P i).obj := by
  rintro ⟨x⟩ ⟨y⟩ h
  have hx : (⟨i, x⟩ : Σ i, (P i).V) = ⟨i, y⟩ := congrArg GenObj.as h
  simpa using hx

theorem coproductPre_star_surjective (i : ι) (x : GenObj (P i).Gen) :
    Function.Surjective ((coproductPre P i).star x) := by
  rintro ⟨⟨⟨j, y⟩⟩, e⟩
  cases e with
  | mk g => exact ⟨⟨⟨_⟩, g⟩, rfl⟩

theorem coproductPre_comapIncl_full (i : ι) :
    ((coproduct P).comapIncl (P i).Gen (coproductPre P i)).Full :=
  (coproduct P).comapIncl_full _ _ (coproductPre_star_surjective P i)
    (coproductPre_obj_injective P i)

/-- **A word of the coproduct between 0-cells of one fibre is that fibre's word.** -/
theorem coproduct_exists_mapPath (i : ι) {x y : (P i).V}
    (u : Quiver.Path (⟨⟨i, x⟩⟩ : GenObj (CoproductGen P)) ⟨⟨i, y⟩⟩) :
    ∃ u' : Quiver.Path (⟨x⟩ : GenObj (P i).Gen) ⟨y⟩, (coproductPre P i).mapPath u' = u :=
  (coproductPre_comapIncl_full P i).map_surjective (X := ⟨x⟩) (Y := ⟨y⟩) u

/-- A fibre's 2-cells hold in the coproduct. -/
theorem coproductRel_sound (i : ι) {x y : GenObj (P i).Gen} {u v : Quiver.Path x y}
    (h : (P i).rel u v) :
    (coproduct P).quot.map ((coproductPre P i).mapPath u)
      = (coproduct P).quot.map ((coproductPre P i).mapPath v) :=
  Quotient.sound _ (CoproductRel.mk h)

/-- The coproduct injection.  `Hom`, not `⟶`: the coproduct sits a universe up. -/
def coproductIncl (i : ι) : Hom (P i) (coproduct P) :=
  Hom.ofPre (coproductPre P i) (coproductRel_sound P i)

end Polygraph

namespace Presents

variable {ι : Type t} {P : ι → Polygraph.{w, u'}} {C : ι → Type u} [∀ i, Category.{v} (C i)]
  (p : ∀ i, Presents (P i) (C i))

/-- The arrow a 1-cell of the coproduct names. -/
def coproductArrow : ∀ (a b : Σ i, (P i).V), Polygraph.CoproductGen P a b →
    ((⟨a.1, (p a.1).at' ⟨a.2⟩⟩ : Σ i, C i) ⟶ ⟨b.1, (p b.1).at' ⟨b.2⟩⟩)
  | _, _, .mk g => Sigma.SigmaHom.mk ((p _).arrow g)

/-- The cells of the coproduct, interpreted in the disjoint union of the categories. -/
def coproductEval : GenObj (Polygraph.CoproductGen P) ⥤q (Σ i, C i) where
  obj x := ⟨x.as.1, (p x.as.1).at' ⟨x.as.2⟩⟩
  map e := coproductArrow p _ _ e

/-- **A fibre's word, evaluated in the coproduct** — the fibre's own evaluation, included. -/
theorem coproductEval_mapPath (i : ι) {x y : GenObj (P i).Gen} (u : Quiver.Path x y) :
    (Paths.lift (coproductEval p)).map ((Polygraph.coproductPre P i).mapPath u)
      = (Sigma.incl i).map ((p i).eval.map u) := by
  rw [Paths.lift_mapPath]
  exact (p i).lift_evalPre_comp (Sigma.incl i) u

theorem coproduct_sound {a b : GenObj (Polygraph.CoproductGen P)} {u v : Quiver.Path a b}
    (h : Polygraph.CoproductRel P u v) :
    (Paths.lift (coproductEval p)).map u = (Paths.lift (coproductEval p)).map v := by
  cases h with
  | mk hr =>
    rw [coproductEval_mapPath, coproductEval_mapPath]
    exact congrArg _ ((p _).sound hr)

theorem coproduct_complete {a b : GenObj (Polygraph.CoproductGen P)} {u v : Quiver.Path a b}
    (h : (Paths.lift (coproductEval p)).map u = (Paths.lift (coproductEval p)).map v) :
    (Polygraph.coproduct P).quot.map u = (Polygraph.coproduct P).quot.map v := by
  obtain ⟨⟨i, x⟩⟩ := a
  obtain ⟨⟨j, y⟩⟩ := b
  obtain rfl : i = j := Polygraph.coproduct_path_fst P u
  obtain ⟨u', rfl⟩ := Polygraph.coproduct_exists_mapPath P i u
  obtain ⟨v', rfl⟩ := Polygraph.coproduct_exists_mapPath P i v
  have h' : (p i).E.map ((P i).quot.map u') = (p i).E.map ((P i).quot.map v') :=
    (Sigma.incl i).map_injective
      ((coproductEval_mapPath p i u').symm.trans (h.trans (coproductEval_mapPath p i v')))
  exact Polygraph.quot_mapPath_congr (P i) (Polygraph.coproduct P) (Polygraph.coproductPre P i)
    (Polygraph.coproductRel_sound P i) ((p i).E.map_injective h')

theorem coproduct_full : (Paths.lift (coproductEval p)).Full where
  map_surjective := by
    rintro ⟨⟨i, x⟩⟩ ⟨⟨j, y⟩⟩ f
    cases f with
    | mk g =>
      obtain ⟨w, hw⟩ := (p i).eval.map_surjective (X := ⟨x⟩) (Y := ⟨y⟩) g
      exact ⟨(Polygraph.coproductPre P i).mapPath w,
        (coproductEval_mapPath p i w).trans (congrArg (Sigma.incl i).map hw)⟩

theorem coproduct_essSurj : (Paths.lift (coproductEval p)).EssSurj where
  mem_essImage := by
    rintro ⟨i, c⟩
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := (p i).eval) c
    exact ⟨⟨⟨i, x.as⟩⟩, ⟨(Sigma.incl i).mapIso e⟩⟩

/-- **A family of presentations presents the disjoint union.** -/
def coproduct : Presents (Polygraph.coproduct P) (Σ i, C i) :=
  Presents.ofDesc (coproductEval p) (coproduct_sound p) (coproduct_complete p) (coproduct_full p)
    (coproduct_essSurj p)

end Presents

/-! ## …and the converse

A hom-disjoint cover is a coproduct only up to `ObjectProperty.sigmaEquiv`, so the component of a
presentation is stated for the cover itself; the sigma form is that equivalence, `transport`ed. -/

namespace Presents

variable {P : Polygraph.{w, u'}} {C : Type u} [Category.{v} C] {ι : Type t}
  (p : Presents P C) (Q : ι → ObjectProperty C)

/-- A 0-cell lies in the `i`-th member of a cover when the object it names does. -/
def inComponent (i : ι) : P.V → Prop := fun a => Q i (p.at' (P.pt a))

variable (hcover : ∀ X : C, ∃ i, Q i X)
  (hdisj : ∀ {i j : ι} {X Y : C}, Q i X → Q j Y → (X ⟶ Y) → i = j)

include hcover hdisj in
/-- No 1-cell leaves a member of a hom-disjoint cover. -/
theorem inComponent_closed (i : ι) {a b : P.V} (ha : p.inComponent Q i a) (e : P.Gen a b) :
    p.inComponent Q i b :=
  ObjectProperty.prop_of_hom Q hcover hdisj ha (p.arrow (x := P.pt a) (y := P.pt b) e)

include hcover hdisj in
/-- **A presentation of a hom-disjointly covered category restricts to a presentation of each
member** — the converse of `Presents.coproduct`. -/
def component (i : ι) :
    Presents (P.restrict (p.inComponent Q i)) ((Q i).FullSubcategory) := by
  haveI := P.restrictHom_functor_full _ (p.inComponent_closed Q hcover hdisj i)
  haveI := P.restrictHom_functor_faithful _ (p.inComponent_closed Q hcover hdisj i)
  haveI : ((Q i).lift ((P.restrictHom (p.inComponent Q i)).functor ⋙ p.E)
      fun X => X.as.as.2).EssSurj := by
    constructor
    rintro ⟨c, hc⟩
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) c
    obtain ⟨x⟩ := X
    obtain ⟨a⟩ := x
    have hQ : p.inComponent Q i a := ObjectProperty.prop_of_hom Q hcover hdisj hc e.inv
    exact ⟨⟨⟨⟨a, hQ⟩⟩⟩, ⟨(Q i).isoMk e⟩⟩
  exact ⟨(Q i).lift ((P.restrictHom (p.inComponent Q i)).functor ⋙ p.E) fun X => X.as.as.2, { }⟩

end Presents

end CategoryTheory
