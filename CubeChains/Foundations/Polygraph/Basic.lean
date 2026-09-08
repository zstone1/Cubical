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

/-! ## Cells read at other names for their boundary

A cell is fibred over the two indices its boundary spans, so a proof that renames those indices
must carry the cell across.  `cellCongr` is that transport — `Quiver.homOfEq` is the 1-cell case;
words and 2-cells have no mathlib version — and it is the *only* one a 2-cell ever carries. -/

/-- A cell of a family fibred over a boundary, read at indices its boundary is equal to. -/
def cellCongr {ι : Sort*} (F : ι → ι → Sort*) :
    ∀ {a b A B : ι}, a = A → b = B → F a b → F A B
  | _, _, _, _, rfl, rfl, c => c

/-- Which proofs name the indices is irrelevant, so `cellCongr` descends to a quotient. -/
theorem cellCongr_heq {ι : Sort*} (F : ι → ι → Sort*) {a b A B : ι} (ha : a = A) (hb : b = B)
    (c : F a b) : cellCongr F ha hb c ≍ c := by subst ha; subst hb; rfl

theorem cellCongr_trans {ι : Sort*} (F : ι → ι → Sort*) {a b A B A' B' : ι} (ha : a = A)
    (hb : b = B) (ha' : A = A') (hb' : B = B') (c : F a b) :
    cellCongr F ha' hb' (cellCongr F ha hb c) = cellCongr F (ha.trans ha') (hb.trans hb') c := by
  subst ha; subst hb; subst ha'; subst hb'; rfl

/-- **A prefunctor carries a transported word to the transported word.** -/
theorem Prefunctor.mapPath_cellCongr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') (p : Quiver.Path x y) :
    π.mapPath (cellCongr Quiver.Path hx hy p)
      = cellCongr Quiver.Path (congrArg π.obj hx) (congrArg π.obj hy) (π.mapPath p) := by
  subst hx; subst hy; rfl

/-- **Equal prefunctors agree on 1-cells** — `Prefunctor.map_of_eq`, said with `HEq`. -/
theorem Prefunctor.map_heq_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (e : x ⟶ y) : π.map e ≍ σ.map e := by subst h; rfl

/-- **A prefunctor respects a heterogeneous equality of 1-cells.** -/
theorem Prefunctor.map_heq_congr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') {e : x ⟶ y} {e' : x' ⟶ y'} (h : e ≍ e') :
    π.map e ≍ π.map e' := by subst hx; subst hy; cases h; rfl

namespace CategoryTheory

/-- A 0-cell: an index for an object, carrying the generating quiver rather than any quiver its
index type already has. -/
@[ext] structure GenObj {V : Type u'} (Gen : V → V → Type w) where
  /-- the index it names -/
  as : V

instance genObjQuiver {V : Type u'} (Gen : V → V → Type w) : Quiver.{w} (GenObj Gen) :=
  ⟨fun x y => Gen x.as y.as⟩

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

/-- **A morphism respects a heterogeneous equality of 2-cells.** -/
theorem two_heq_congr (F : Hom P Q) {x y x' y' : GenObj P.Gen} (hx : x = x') (hy : y = y')
    {α : P.Rel x y} {α' : P.Rel x' y'} (h : α ≍ α') : F.two α ≍ F.two α' := by
  subst hx; subst hy; cases h; rfl

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

end Polygraph

end CategoryTheory
