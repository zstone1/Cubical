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

/-- **A cell read at its own indices is itself** — proof irrelevance, so neither equation need be
`rfl` on the nose.  This is what makes `rintro … rfl rfl` leave no transport behind. -/
theorem cellCongr_self {ι : Sort*} (F : ι → ι → Sort*) {a b : ι} (ha : a = a)
    (hb : b = b) (c : F a b) : cellCongr F ha hb c = c := rfl

/-- Which proofs name the indices is irrelevant, so `cellCongr` descends to a quotient. -/
theorem cellCongr_heq {ι : Sort*} (F : ι → ι → Sort*) {a b A B : ι} (ha : a = A) (hb : b = B)
    (c : F a b) : cellCongr F ha hb c ≍ c := by subst ha; subst hb; rfl

theorem cellCongr_trans {ι : Sort*} (F : ι → ι → Sort*) {a b A B A' B' : ι} (ha : a = A)
    (hb : b = B) (ha' : A = A') (hb' : B = B') (c : F a b) :
    cellCongr F ha' hb' (cellCongr F ha hb c) = cellCongr F (ha.trans ha') (hb.trans hb') c := by
  subst ha; subst hb; subst ha'; subst hb'; rfl

/-! `cellCongr` on words is blind to which proof names an index, so it commutes with the way a word
is built: an empty word is pinned by its endpoints, and concatenation passes through. -/

section Path

variable {V : Type*} [Quiver V]

/-- **A transported empty word is pinned by its endpoints.** -/
theorem cellCongr_nil_eq {x x' A B : V} (h₁ : x = A) (h₂ : x = B) (h₁' : x' = A) (h₂' : x' = B) :
    cellCongr Quiver.Path h₁ h₂ (Quiver.Path.nil : Quiver.Path x x)
      = cellCongr Quiver.Path h₁' h₂' (Quiver.Path.nil : Quiver.Path x' x') := by
  subst h₁; subst h₂; subst h₁'; rfl

/-- **Transport distributes over concatenation.** -/
theorem cellCongr_comp {x y z A B C : V} (h₁ : x = A) (h₂ : y = B) (h₃ : z = C)
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    (cellCongr Quiver.Path h₁ h₂ p).comp (cellCongr Quiver.Path h₂ h₃ q)
      = cellCongr Quiver.Path h₁ h₃ (p.comp q) := by
  subst h₁; subst h₂; subst h₃; rfl

/-- **…and a transported one-letter word is the transported letter.** -/
theorem cellCongr_toPath {x y A B : V} (h₁ : x = A) (h₂ : y = B) (e : x ⟶ y) :
    cellCongr Quiver.Path h₁ h₂ e.toPath = (Quiver.homOfEq e h₁ h₂).toPath := by
  subst h₁; subst h₂; rfl

/-- …so a transported word's last letter is the transported letter. -/
theorem cellCongr_cons {x m y A M B : V} (h₁ : x = A) (hm : m = M) (h₂ : y = B)
    (p : Quiver.Path x m) (e : m ⟶ y) :
    cellCongr Quiver.Path h₁ h₂ (p.cons e)
      = (cellCongr Quiver.Path h₁ hm p).cons (Quiver.homOfEq e hm h₂) := by
  subst h₁; subst hm; subst h₂; rfl

end Path

/-- **A prefunctor carries a transported word to the transported word.** -/
theorem Prefunctor.mapPath_cellCongr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') (p : Quiver.Path x y) :
    π.mapPath (cellCongr Quiver.Path hx hy p)
      = cellCongr Quiver.Path (congrArg π.obj hx) (congrArg π.obj hy) (π.mapPath p) := by
  subst hx; subst hy; rfl

/-- **Reading a 1-cell at other names for its endpoints is a bijection.** -/
theorem Quiver.homOfEq_bijective {V : Type*} [Quiver V] {a b a' b' : V} (h : a = a')
    (h' : b = b') : Function.Bijective (fun f : a ⟶ b => Quiver.homOfEq f h h') := by
  subst h; subst h'; exact Function.bijective_id

/-- **Equal prefunctors agree on 1-cells** — `Prefunctor.map_of_eq`, said with `HEq`. -/
theorem Prefunctor.map_heq_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (e : x ⟶ y) : π.map e ≍ σ.map e := by subst h; rfl

/-- **Equal prefunctors agree on words.** -/
theorem Prefunctor.mapPath_heq_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (u : Quiver.Path x y) : π.mapPath u ≍ σ.mapPath u := by subst h; rfl

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
