import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Machinery/Presentation/Coproduct — the coproduct of polygraphs

`Polygraph.coproduct P` is the disjoint union in every dimension: a 1-cell lives in one fibre, a
2-cell is a fibre's own.  The fibre constraint is carried by **indexed inductives**
(`CoproductGen`, `CoproductRel`, mirroring mathlib's `Sigma.SigmaHom`) rather than by
`Σ' h : i = j, …`: `cases` then reads the fibre off a cell and no transport is ever spelled, at
the price of a universe bump.

The fibre inclusion of generating quivers is star-surjective and injective on 0-cells, so a word of
the coproduct between 0-cells of one fibre is that fibre's word (`pathsFunctor_full`); that, plus
the absence of cross-fibre words, is the whole content of `Presents.coproduct`.  The converse — a
presentation cut down to one member — is `Presents.restrict` in `Machinery/Presentation/Partial`.
-/

universe t w u' v u w₂

namespace CategoryTheory

namespace Polygraph

variable {ι : Type t} (P : ι → Polygraph.{w, u', w₂})

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

/-- 2-cells of a coproduct: a fibre's own. -/
inductive CoproductRel : GenObj (CoproductGen P) → GenObj (CoproductGen P) → Type (max t u' w w₂)
  | mk {i : ι} {x y : GenObj (P i).Gen} :
      (P i).Rel x y → CoproductRel ((coproductPre P i).obj x) ((coproductPre P i).obj y)

/-- The source of a coproduct 2-cell: its fibre's, included. -/
def CoproductRel.src : ∀ {a b : GenObj (CoproductGen P)}, CoproductRel P a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (coproductPre P i).mapPath ((P i).src α)

/-- The target of a coproduct 2-cell: its fibre's, included. -/
def CoproductRel.tgt : ∀ {a b : GenObj (CoproductGen P)}, CoproductRel P a b → Quiver.Path a b
  | _, _, .mk (i := i) α => (coproductPre P i).mapPath ((P i).tgt α)

/-- **The coproduct of polygraphs.** -/
def coproduct : Polygraph.{max t u' w, max t u', max t u' w w₂} where
  V := Σ i, (P i).V
  Gen := CoproductGen P
  Rel := CoproductRel P
  src := CoproductRel.src P
  tgt := CoproductRel.tgt P

/-- The coproduct injection. -/
def coproductIncl (i : ι) : Hom (P i) (coproduct P) where
  pre := coproductPre P i
  two α := CoproductRel.mk α
  src_two _ := rfl
  tgt_two _ := rfl

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

theorem coproductPre_pathsFunctor_full (i : ι) :
    (coproductPre P i).pathsFunctor.Full :=
  Prefunctor.pathsFunctor_full _ (coproductPre_star_surjective P i)
    (coproductPre_obj_injective P i)

/-- **A word of the coproduct between 0-cells of one fibre is that fibre's word.** -/
theorem coproduct_exists_mapPath (i : ι) {x y : (P i).V}
    (u : Quiver.Path (⟨⟨i, x⟩⟩ : GenObj (CoproductGen P)) ⟨⟨i, y⟩⟩) :
    ∃ u' : Quiver.Path (⟨x⟩ : GenObj (P i).Gen) ⟨y⟩, (coproductPre P i).mapPath u' = u :=
  (coproductPre_pathsFunctor_full P i).map_surjective (X := ⟨x⟩) (Y := ⟨y⟩) u

end Polygraph

/-! ## The disjoint union is the coproduct

A morphism out of the disjoint union is exactly a family: `cases` on a 1-cell or a 2-cell reads
off the fibre it came from. -/

namespace Polygraph

open Limits

variable {ι : Type t} (P : ι → Polygraph.{max t u' w, max t u', max t u' w w₂})
  {R : Polygraph.{max t u' w, max t u', max t u' w w₂}} (m : ∀ i, P i ⟶ R)

/-- The 1-cell of `R` that a 1-cell of the coproduct is sent to: the fibre it lies in decides. -/
def coprodDescMap : ∀ (a b : Σ i, (P i).V), CoproductGen P a b →
    ((m a.1).pre.obj ⟨a.2⟩ ⟶ (m b.1).pre.obj ⟨b.2⟩)
  | _, _, .mk g => (m _).pre.map g

/-- The cells of the coproduct, read by a family. -/
def coprodDescPre : GenObj (CoproductGen P) ⥤q GenObj R.Gen where
  obj x := (m x.as.1).pre.obj ⟨x.as.2⟩
  map {x y} e := coprodDescMap P m x.as y.as e

theorem coproductPre_comp_descPre (i : ι) :
    coproductPre P i ⋙q coprodDescPre P m = (m i).pre := rfl

/-- **A fibre's word, read by the descent, is that fibre's own reading.**  An induction, not a
`rfl`: `mapPath` on a variable word is stuck even though the two prefunctors are the same. -/
theorem descPre_mapPath (i : ι) {a b : GenObj (P i).Gen} (w : Quiver.Path a b) :
    (coprodDescPre P m).mapPath ((coproductPre P i).mapPath w) = (m i).pre.mapPath w := by
  induction w with
  | nil => rfl
  | cons w' g ih => exact congrArg (fun p => Quiver.Path.cons p ((m i).pre.map g)) ih

/-- The 2-cell of `R` that a 2-cell of the coproduct is sent to. -/
def coprodDescTwo : ∀ {a b : GenObj (CoproductGen P)}, CoproductRel P a b →
    R.Rel ((coprodDescPre P m).obj a) ((coprodDescPre P m).obj b)
  | _, _, .mk (i := i) α => (m i).two α

/-- The descent of a family. -/
def coprodDesc : coproduct P ⟶ R where
  pre := coprodDescPre P m
  two := coprodDescTwo P m
  src_two := by rintro _ _ ⟨α⟩; exact ((m _).src_two α).trans (descPre_mapPath P m _ _).symm
  tgt_two := by rintro _ _ ⟨α⟩; exact ((m _).tgt_two α).trans (descPre_mapPath P m _ _).symm

theorem coprodIncl_desc (i : ι) : coproductIncl P i ≫ coprodDesc P m = m i := rfl

theorem coprodDesc_uniq (n : coproduct P ⟶ R) (hn : ∀ i, coproductIncl P i ≫ n = m i) :
    n = coprodDesc P m := by
  have key : ∀ i, coproductPre P i ⋙q n.pre = (m i).pre :=
    fun i => congrArg Polygraph.Hom.pre (hn i)
  have hpre : n.pre = coprodDescPre P m := by
    refine Prefunctor.ext' ?_ ?_
    · rintro ⟨⟨i, a⟩⟩
      exact congrArg (fun φ : GenObj (P i).Gen ⥤q GenObj R.Gen => φ.obj ⟨a⟩) (key i)
    · rintro ⟨⟨i, a⟩⟩ ⟨⟨j, b⟩⟩ e
      cases e with
      | @mk _ _ _ g =>
        exact Prefunctor.map_of_eq (F := coproductPre P i ⋙q n.pre) (G := (m i).pre) (key i) g
  refine Polygraph.Hom.ext' hpre ?_
  intro x y α
  cases α with
  | mk β => exact Polygraph.Hom.two_heq_of_eq (hn _) β

/-- **The disjoint union is the coproduct.** -/
def coprodIsColimit : IsColimit (Cofan.mk (coproduct P) (coproductIncl P)) :=
  Cofan.IsColimit.mk _ (fun t => coprodDesc P t.inj) (fun t => coprodIncl_desc P t.inj)
    (fun t n hn => coprodDesc_uniq P t.inj n hn)

instance : HasCoproduct P := HasColimit.mk ⟨_, coprodIsColimit P⟩

end Polygraph

namespace Presents

variable {ι : Type t} {P : ι → Polygraph.{w, u', w₂}} {C : ι → Type u} [∀ i, Category.{v} (C i)]
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

theorem coproduct_sound {a b : GenObj (Polygraph.CoproductGen P)}
    (α : (Polygraph.coproduct P).Rel a b) :
    (Paths.lift (coproductEval p)).map ((Polygraph.coproduct P).src α)
      = (Paths.lift (coproductEval p)).map ((Polygraph.coproduct P).tgt α) := by
  cases α with
  | @mk i _ _ hr =>
    change (Paths.lift (coproductEval p)).map ((Polygraph.coproductPre P i).mapPath ((P i).src hr))
      = (Paths.lift (coproductEval p)).map ((Polygraph.coproductPre P i).mapPath ((P i).tgt hr))
    rw [coproductEval_mapPath, coproductEval_mapPath]
    exact congrArg _ ((p i).sound hr)

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
  exact (Polygraph.coproductIncl P i).quot_map_congr ((p i).E.map_injective h')

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

end CategoryTheory
