import CubeChains.Foundations.Polygraph.PathCoords
import Mathlib.CategoryTheory.Category.Basic

/-!
# Foundations/Polygraph/Basic — 2-polygraphs and their morphisms

A `Polygraph` is a 2-polygraph (Street's 2-computad) in the standard sense: 0-cells, 1-cells
between them, and 2-cells carrying a *source* and a *target* word.  A morphism sends a cell to a
cell in every dimension, commuting with the boundaries.

`GenObj` re-quivers `V`, so `Paths` does not pick up a quiver `V` already carries.  Nothing here
names a category: what a polygraph *presents* lives downstream.
-/

universe w' w u'' u' w₂' w₂

namespace CategoryTheory

/-- A 0-cell: an index for an object, carrying the generating quiver rather than any quiver its
index type already has. -/
@[ext] structure GenObj {V : Type u'} (Gen : V → V → Type w) where
  /-- the index it names -/
  as : V

instance genObjQuiver {V : Type u'} (Gen : V → V → Type w) : Quiver.{w} (GenObj Gen) :=
  ⟨fun x y => Gen x.as y.as⟩

/-- **A 0-cell is its index** — the re-quivering, as an equivalence. -/
def genObjEquiv {V : Type u'} (Gen : V → V → Type w) : V ≃ GenObj Gen where
  toFun := GenObj.mk
  invFun := GenObj.as
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A 2-polygraph**: 0-cells, 1-cells between them, and 2-cells with a source and a target word.
The cells are *indices* — nothing here names a category. -/
structure Polygraph where
  /-- the 0-cells -/
  V : Type u'
  /-- the 1-cells -/
  Gen : V → V → Type w
  /-- the 2-cells, fibred over the 0-cells their boundary spans -/
  Rel : GenObj Gen → GenObj Gen → Type w₂
  /-- the source of a 2-cell -/
  src : ∀ {x y : GenObj Gen}, Rel x y → Quiver.Path x y
  /-- the target of a 2-cell -/
  tgt : ∀ {x y : GenObj Gen}, Rel x y → Quiver.Path x y

namespace Polygraph

/-- A 1-cell, read as a 1-cell of the generating quiver — what `toPath` and `mapPath` want. -/
def cell {P : Polygraph.{w, u', w₂}} {a b : P.V} (e : P.Gen a b) :
    (⟨a⟩ : GenObj P.Gen) ⟶ ⟨b⟩ := e

/-! ## Maps of polygraphs

A morphism sends a cell to a cell in every dimension: a 1-cell to a 1-cell, a 2-cell to a 2-cell
with the pushed-forward boundary.  Both boundary conditions are equations of *words*, on the nose;
nothing here is stated up to a congruence. -/

/-- **A morphism of polygraphs.** -/
structure Hom (P : Polygraph.{w, u', w₂}) (Q : Polygraph.{w', u'', w₂'}) where
  /-- the 1-cell a 1-cell spells -/
  pre : GenObj P.Gen ⥤q GenObj Q.Gen
  /-- the 2-cell a 2-cell spells -/
  two {x y : GenObj P.Gen} : P.Rel x y → Q.Rel (pre.obj x) (pre.obj y)
  /-- …with the pushed-forward source -/
  src_two {x y : GenObj P.Gen} (α : P.Rel x y) : Q.src (two α) = pre.mapPath (P.src α)
  /-- …and the pushed-forward target -/
  tgt_two {x y : GenObj P.Gen} (α : P.Rel x y) : Q.tgt (two α) = pre.mapPath (P.tgt α)

namespace Hom

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}

theorem ext' {F G : Hom P Q} (hpre : F.pre = G.pre)
    (htwo : ∀ {x y : GenObj P.Gen} (α : P.Rel x y), F.two α ≍ G.two α) : F = G := by
  obtain ⟨p, t, _, _⟩ := F
  obtain ⟨p', t', _, _⟩ := G
  cases hpre
  have : @t = @t' := by
    funext x y α; exact eq_of_heq (htwo α)
  cases this; rfl

/-- **Equal morphisms agree on 2-cells.** -/
theorem two_heq_of_eq {F G : Hom P Q} (h : F = G) {x y : GenObj P.Gen} (α : P.Rel x y) :
    F.two α ≍ G.two α := by cases h; rfl

/-- The identity. -/
def id (P : Polygraph.{w, u', w₂}) : Hom P P where
  pre := 𝟭q _
  two α := α
  src_two _ := (Prefunctor.mapPath_id _).symm
  tgt_two _ := (Prefunctor.mapPath_id _).symm

variable {R : Polygraph.{w', u'', w₂'}}

/-- Composition. -/
def comp (F : Hom P Q) (G : Hom Q R) : Hom P R where
  pre := F.pre ⋙q G.pre
  two α := G.two (F.two α)
  src_two α := ((G.src_two (F.two α)).trans (congrArg G.pre.mapPath (F.src_two α))).trans
    (Prefunctor.mapPath_comp_apply _ _ _).symm
  tgt_two α := ((G.tgt_two (F.two α)).trans (congrArg G.pre.mapPath (F.tgt_two α))).trans
    (Prefunctor.mapPath_comp_apply _ _ _).symm

end Hom

instance : Category Polygraph.{w, u', w₂} where
  Hom P Q := Hom P Q
  id := Hom.id
  comp := Hom.comp

@[simp] theorem id_pre (P : Polygraph.{w, u', w₂}) : (𝟙 P : P ⟶ P).pre = 𝟭q _ := rfl

@[simp] theorem comp_pre {P Q R : Polygraph.{w, u', w₂}} (F : P ⟶ Q) (G : Q ⟶ R) :
    (F ≫ G).pre = F.pre ⋙q G.pre := rfl

/-! ## Polygraphs with no 0-cells

No 0-cells means no cells in any dimension, so every field of a morphism out is vacuous.  This is
initiality, said before any limit vocabulary is in scope. -/

instance isEmpty_genObj {P : Polygraph.{w, u', w₂}} [h : IsEmpty P.V] : IsEmpty (GenObj P.Gen) :=
  ⟨fun x => h.elim x.as⟩

/-- The map out of a polygraph with no 0-cells. -/
def homOfIsEmpty (P : Polygraph.{w, u', w₂}) [h : IsEmpty P.V] (Q : Polygraph.{w', u'', w₂'}) :
    Hom P Q where
  pre := { obj := fun x => h.elim x.as, map := fun {x _} _ => h.elim x.as }
  two := fun {x _} _ => h.elim x.as
  src_two := fun {x _} _ => h.elim x.as
  tgt_two := fun {x _} _ => h.elim x.as

/-- **…and it is the only one.** -/
instance uniqueHomOfIsEmpty (P : Polygraph.{w, u', w₂}) [h : IsEmpty P.V]
    (Q : Polygraph.{w, u', w₂}) : Unique (P ⟶ Q) where
  default := homOfIsEmpty P Q
  uniq _ := Hom.ext' (Prefunctor.ext' (fun x => h.elim x.as) (fun x _ _ => h.elim x.as))
    fun {x _} _ => h.elim x.as

end Polygraph

end CategoryTheory
