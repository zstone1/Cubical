import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Precubical sets (ClaudeSetup.md §1)

A *precubical set* is a graded family of cell types `cells : ℕ → Type*` together
with face maps `face ε i : cells (n+1) → cells n` satisfying the precubical
identities.  See `DESIGN.md` §1 for the conventions:

* `face : Bool → Fin (n+1) → cells (n+1) → cells n`;
* `ε : Bool` with `false = d⁰` (source) and `true = d¹` (target), fixed once and
  never deviated from;
* the identity mirrors mathlib's `SimplicialObject.δ_comp_δ`.

We provide the `Category` instance of precubical sets, the iterated *extremal
vertices* `vertex₀`, `vertex₁ : cells n → cells 0` (the paper's `vertex⁰`,
`vertex¹`; we use subscripts because superscript digits are not legal Lean
identifier characters), and the rewriting lemmas everything downstream needs.
-/

universe u v

open CategoryTheory

/-- A precubical set: a graded family of cells with face maps satisfying the
precubical identity.  `face ε i : cells (n+1) → cells n`, with `ε = false` the
source (`d⁰`) face and `ε = true` the target (`d¹`) face. -/
structure PrecubicalConstructions where
  /-- The `n`-cells. -/
  cells : ℕ → Type u
  /-- Face maps. `face ε i c` removes the `i`-th coordinate of `c`, setting it to
  `ε` (`false = 0 = d⁰`, `true = 1 = d¹`). -/
  face : ∀ {n : ℕ}, Bool → Fin (n + 1) → cells (n + 1) → cells n
  /-- Precubical identity, in mathlib's `δ_comp_δ` idiom: for `i ≤ j`,
  `face ε i ∘ face η j.succ = face η j ∘ face ε i.castSucc`. -/
  face_face : ∀ {n : ℕ} (ε η : Bool) {i j : Fin (n + 1)}, i ≤ j →
    ∀ (c : cells (n + 2)),
      face ε i (face η j.succ c) = face η j (face ε i.castSucc c)

namespace PrecubicalConstructions

/-- The precubical identity in the opposite orientation: `face_face` read
right-to-left, packaged for `rw`. -/
theorem face_face' (K : PrecubicalConstructions.{u}) {n : ℕ} (ε η : Bool) {i j : Fin (n + 1)}
    (h : i ≤ j) (c : K.cells (n + 2)) :
    K.face η j (K.face ε i.castSucc c) = K.face ε i (K.face η j.succ c) :=
  (K.face_face ε η h c).symm

/-! ### Morphisms and the category structure -/

/-- A morphism of precubical sets: a dimension-wise family of maps commuting with
all face maps. -/
@[ext]
structure Hom (K L : PrecubicalConstructions.{u}) where
  /-- The underlying map in each dimension. -/
  app : ∀ n, K.cells n → L.cells n
  /-- Commutation with faces. -/
  app_face : ∀ {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : K.cells (n + 1)),
    app n (K.face ε i c) = L.face ε i (app (n + 1) c)

namespace Hom

variable {K L M : PrecubicalConstructions.{u}}

/-- The identity morphism. -/
protected def id (K : PrecubicalConstructions.{u}) : Hom K K where
  app _ c := c
  app_face _ _ _ := rfl

/-- Composition of morphisms (diagrammatic order: `f` then `g`). -/
protected def comp (f : Hom K L) (g : Hom L M) : Hom K M where
  app n := g.app n ∘ f.app n
  app_face ε i c := by simp only [Function.comp_apply, f.app_face, g.app_face]

end Hom

instance : Category PrecubicalConstructions.{u} where
  Hom K L := Hom K L
  id K := Hom.id K
  comp f g := Hom.comp f g

@[simp]
theorem id_app (K : PrecubicalConstructions.{u}) (n : ℕ) (c : K.cells n) :
    Hom.app (𝟙 K) n c = c := rfl

@[simp]
theorem comp_app {K L M : PrecubicalConstructions.{u}} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ)
    (c : K.cells n) : Hom.app (f ≫ g) n c = Hom.app g n (Hom.app f n c) := rfl

/-- Two morphisms agree iff they agree in every dimension (an `app`-level `ext`). -/
@[ext]
theorem hom_ext {K L : PrecubicalConstructions.{u}} {f g : K ⟶ L}
    (h : ∀ n c, Hom.app f n c = Hom.app g n c) : f = g := by
  apply Hom.ext
  funext n c
  exact h n c

/-! ### Iterated faces and extremal vertices -/

/-- The `ε`-extremal vertex map `cells n → cells 0`, obtained by repeatedly
applying the `ε`-face at coordinate `0`.  `vertex false` is the source vertex
`vertex₀`, `vertex true` the target vertex `vertex₁`. -/
def vertex (K : PrecubicalConstructions.{u}) (ε : Bool) : ∀ {n : ℕ}, K.cells n → K.cells 0
  | 0,     c => c
  | _ + 1, c => vertex K ε (K.face ε 0 c)

@[simp] theorem vertex_zero (K : PrecubicalConstructions.{u}) (ε : Bool) (c : K.cells 0) :
    K.vertex ε c = c := rfl

theorem vertex_succ (K : PrecubicalConstructions.{u}) (ε : Bool) {n : ℕ} (c : K.cells (n + 1)) :
    K.vertex ε c = K.vertex ε (K.face ε 0 c) := by
  simp only [vertex]

/-- Order independence of the extremal vertex (well-definedness, ClaudeSetup.md
§1): applying *any* `ε`-face before taking the `ε`-vertex does not change the
result.  Proved by the finite computation with `face_face`. -/
theorem vertex_face (K : PrecubicalConstructions.{u}) (ε : Bool) :
    ∀ {n : ℕ} (i : Fin (n + 1)) (c : K.cells (n + 1)),
      K.vertex ε (K.face ε i c) = K.vertex ε c := by
  intro n
  induction n with
  | zero =>
      intro i c
      refine Fin.cases ?_ (fun j => j.elim0) i
      rfl
  | succ n ih =>
      intro i c
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rw [K.vertex_succ ε (K.face ε j.succ c), K.face_face ε ε (Fin.zero_le j) c,
          Fin.castSucc_zero, ih j (K.face ε 0 c), ← K.vertex_succ ε c]

/-- The source (`d⁰`) extremal vertex (paper: `vertex⁰`). -/
def vertex₀ (K : PrecubicalConstructions.{u}) {n : ℕ} (c : K.cells n) : K.cells 0 :=
  K.vertex false c

/-- The target (`d¹`) extremal vertex (paper: `vertex¹`). -/
def vertex₁ (K : PrecubicalConstructions.{u}) {n : ℕ} (c : K.cells n) : K.cells 0 :=
  K.vertex true c

@[simp] theorem vertex₀_zero (K : PrecubicalConstructions.{u}) (c : K.cells 0) :
    K.vertex₀ c = c := rfl
@[simp] theorem vertex₁_zero (K : PrecubicalConstructions.{u}) (c : K.cells 0) :
    K.vertex₁ c = c := rfl

/-- Taking a source face commutes with the source vertex. -/
theorem vertex₀_face (K : PrecubicalConstructions.{u}) {n : ℕ} (i : Fin (n + 1))
    (c : K.cells (n + 1)) : K.vertex₀ (K.face false i c) = K.vertex₀ c :=
  K.vertex_face false i c

/-- Taking a target face commutes with the target vertex. -/
theorem vertex₁_face (K : PrecubicalConstructions.{u}) {n : ℕ} (i : Fin (n + 1))
    (c : K.cells (n + 1)) : K.vertex₁ (K.face true i c) = K.vertex₁ c :=
  K.vertex_face true i c

/-- Morphisms commute with the extremal vertices. -/
theorem map_vertex {K L : PrecubicalConstructions.{u}} (f : Hom K L) (ε : Bool) :
    ∀ {n : ℕ} (c : K.cells n), f.app 0 (K.vertex ε c) = L.vertex ε (f.app n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      rw [K.vertex_succ ε c, ih (K.face ε 0 c), f.app_face, ← L.vertex_succ ε (f.app _ c)]

theorem map_vertex₀ {K L : PrecubicalConstructions.{u}} (f : Hom K L) {n : ℕ} (c : K.cells n) :
    f.app 0 (K.vertex₀ c) = L.vertex₀ (f.app n c) := map_vertex f false c

theorem map_vertex₁ {K L : PrecubicalConstructions.{u}} (f : Hom K L) {n : ℕ} (c : K.cells n) :
    f.app 0 (K.vertex₁ c) = L.vertex₁ (f.app n c) := map_vertex f true c

end PrecubicalConstructions
