import CubeChains.Salvetti.ConeRelations
import Mathlib.CategoryTheory.Groupoid.Subgroupoid

/-!
# Salvetti/WallGen — generation by wall crossings, stated

`WallGenerated n` is the one missing input to `(Conc (□ⁿ)).Faithful`.

Why this and not something weaker: generation by *arbitrary* chamber comparisons is vacuous, since
`homMk_eq_coneCmp_chamber` already makes every generator one.  The content is generation by
**adjacent** crossings — one arrow per (top cell, wall).  That is what makes the braid letters
biject with the zigzag letters, so a free reduction `σᵢσᵢ⁻¹` on the braid word is `g ≫ inv g` on
the zigzag and lifts on the nose.  The surviving moves are then R3 and commutation, which are
`cross_hexagon` and `cross_square`.
-/

open CategoryTheory FreeGroupoid

namespace CubeChains

open COM SignVec

variable {n : ℕ}

/-! ## The two kinds of generator -/

/-- **Every cell lies under the top cell of its own tope** — a tope absorbs, so the wall-crossing
clause is free.  This is the canonical way up out of any object. -/
theorem le_topeCell (a : Sal (braidCOM n)) : a ≤ topeCell ⟨a.tope, a.2.2.1⟩ :=
  ⟨a.2.2.2, (comp_eq_left_of_isTope a.2.2.1 a.2.2.1.1).symm⟩

/-- Two topes are **adjacent** when they disagree at exactly one wall. -/
def Adjacent (T T' : Tope n) : Prop := ∃ e : BraidGround n, ∀ f, T.1 f ≠ T'.1 f ↔ f = e

/-- The generating arrows: the canonical way up to one's own top cell, and the crossings between
adjacent top cells. -/
inductive IsWallGen : ∀ {c d : FreeGroupoid (Sal (braidCOM n))}, (c ⟶ d) → Prop
  /-- Up to the top cell of one's own tope. -/
  | up (a : Sal (braidCOM n)) : IsWallGen (homMk (homOfLE (le_topeCell a)))
  /-- Across one wall, through any apex below both top cells. -/
  | wall {T T' : Tope n} (_ : Adjacent T T') {b : Sal (braidCOM n)}
      (hb : b ≤ topeCell T) (hb' : b ≤ topeCell T') :
      IsWallGen (coneCmp (homOfLE hb) (homOfLE hb'))

/-- The same, as a set of arrows, for `Subgroupoid.generated`. -/
def wallGens (n : ℕ) : ∀ c d : FreeGroupoid (Sal (braidCOM n)), Set (c ⟶ d) :=
  fun _ _ => {γ | IsWallGen γ}

/-! ## The statement -/

/-- **Generation by wall crossings.**  Every morphism of the free groupoid on the execution poset
is a finite composite of canonical up-arrows and adjacent wall crossings, and their inverses.

This is the whole remaining content of `(Conc (□ⁿ)).Faithful`: with it, a loop becomes a *gallery*
word whose braid letters correspond one-to-one with its own letters, so every move relating two
braid words lifts — free reduction because a letter determines its arrow, R3 by `cross_hexagon`,
commutation by `cross_square`. -/
def WallGenerated (n : ℕ) : Prop := Subgroupoid.generated (wallGens n) = ⊤

/-! ## What is already available towards it -/

/-- The up-arrows are generators. -/
theorem up_mem_generated (a : Sal (braidCOM n)) :
    homMk (homOfLE (le_topeCell a)) ∈
      (Subgroupoid.generated (wallGens n)).arrows _ _ :=
  Subgroupoid.subset_generated (wallGens n) _ _ (IsWallGen.up a)

/-- Every arrow of the poset *is* a comparison at a chamber, so reducing a zigzag to chamber
comparisons is already available; what `WallGenerated` adds is that the resulting chamber
transitions factor through **adjacent** ones. -/
theorem exists_coneCmp_chamber {a b : Sal (braidCOM n)} (hab : a ≤ b) :
    ∃ (σ : Equiv.Perm (Fin n)) (hc : chamber σ ≤ a) (hd : chamber σ ≤ b),
      homMk (homOfLE hab) = coneCmp (homOfLE hc) (homOfLE hd) :=
  ⟨wordTopeEquiv.symm ⟨a.tope, a.2.2.1⟩, chamber_le (wordTope_symm _),
    (chamber_le (wordTope_symm _)).trans hab,
    homMk_eq_coneCmp_chamber (wordTope_symm _) hab⟩

end CubeChains
