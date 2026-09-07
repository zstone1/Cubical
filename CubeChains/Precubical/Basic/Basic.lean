import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Precubical/Basic/Basic

The concrete/computable model of precubical sets: a graded family of cells with
face maps `face ε i` obeying the precubical identity, plus the `Category` instance.

Conventions: `ε : Bool` with `false = d⁰` (source) and `true = d¹` (target), fixed
once and never deviated from; the precubical identity mirrors mathlib's
`SimplicialObject.δ_comp_δ`.  The extremal vertices are `PrecubicalSet.vertexEnd`
(`Precubical/Basic/Bipointed`), by pullback along `endVertexMap` rather than by iterated faces.
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

end PrecubicalConstructions
