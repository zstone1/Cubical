import CubeChains.Precubical.Basic

/-!
# Bi-pointed precubical sets (ClaudeSetup.md §2)

A *bi-pointed* precubical set is a precubical set with two distinguished
`0`-cells `init` and `final`.  Morphisms preserve them.  We give `BPSet` a
`Category` instance; mathlib's `Aut` then yields the automorphism group `Aut K`
for free.
-/

universe u

open CategoryTheory

/-- A bi-pointed precubical set: a precubical set with distinguished initial and
final `0`-cells. -/
structure BPSet extends PrecubicalSet.{u} where
  /-- The initial `0`-cell. -/
  init : cells 0
  /-- The final `0`-cell. -/
  final : cells 0

namespace BPSet

/-- A morphism of bi-pointed precubical sets: a precubical morphism preserving
`init` and `final`. -/
@[ext]
structure Hom (K L : BPSet.{u}) extends PrecubicalSet.Hom K.toPrecubicalSet L.toPrecubicalSet where
  /-- The map preserves the initial vertex. -/
  app_init : toHom.app 0 K.init = L.init
  /-- The map preserves the final vertex. -/
  app_final : toHom.app 0 K.final = L.final

namespace Hom

variable {K L M : BPSet.{u}}

/-- The identity bi-pointed morphism. -/
protected def id (K : BPSet.{u}) : Hom K K where
  toHom := PrecubicalSet.Hom.id K.toPrecubicalSet
  app_init := rfl
  app_final := rfl

/-- Composition of bi-pointed morphisms. -/
protected def comp (f : Hom K L) (g : Hom L M) : Hom K M where
  toHom := PrecubicalSet.Hom.comp f.toHom g.toHom
  app_init := by
    change g.toHom.app 0 (f.toHom.app 0 K.init) = M.init
    rw [f.app_init, g.app_init]
  app_final := by
    change g.toHom.app 0 (f.toHom.app 0 K.final) = M.final
    rw [f.app_final, g.app_final]

end Hom

instance : Category BPSet.{u} where
  Hom K L := Hom K L
  id K := Hom.id K
  comp f g := Hom.comp f g

/-- Apply a bi-pointed morphism in a fixed dimension. -/
@[simp]
theorem id_app (K : BPSet.{u}) (n : ℕ) (c : K.cells n) :
    PrecubicalSet.Hom.app (𝟙 K : Hom K K).toHom n c = c := rfl

@[simp]
theorem comp_app {K L M : BPSet.{u}} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ)
    (c : K.cells n) :
    PrecubicalSet.Hom.app ((f ≫ g : Hom K M).toHom) n c
      = PrecubicalSet.Hom.app (g : Hom L M).toHom n
          (PrecubicalSet.Hom.app (f : Hom K L).toHom n c) := rfl

/-- Two bi-pointed morphisms agree iff their underlying maps agree dimensionwise. -/
@[ext]
theorem hom_ext {K L : BPSet.{u}} {f g : K ⟶ L}
    (h : ∀ n c, PrecubicalSet.Hom.app (f : Hom K L).toHom n c
        = PrecubicalSet.Hom.app (g : Hom K L).toHom n c) : f = g := by
  apply Hom.ext
  funext n c
  exact h n c

/-- The underlying precubical morphism of a bi-pointed morphism. -/
abbrev Hom.app' {K L : BPSet.{u}} (f : K ⟶ L) (n : ℕ) : K.cells n → L.cells n :=
  PrecubicalSet.Hom.app (f : Hom K L).toHom n

end BPSet
