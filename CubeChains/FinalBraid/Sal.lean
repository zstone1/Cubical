import CubeChains.FinalBraid.Lines
import CubeChains.FinalBraid.Elements

/-!
# FinalBraid/Sal — the braid Salvetti complex `Sal n = ∫ Lines(□ⁿ)`

The **definition** of the braid Salvetti complex, intrinsically from cube chains:

> `Sal n := (Lines (□ⁿ)).Elements`

the category of elements (Grothendieck construction) of the chamber presheaf `Lines (□ⁿ)`
(`FinalBraid/Lines.lean`). An object is a pair `(x, C)` — a chain `x` in `□ⁿ` with a chamber
`C` refining it — and the induced order is the Salvetti/Paris order. Both base and elements
are thin, so `Sal n` is a poset (`instThinSal`).

**Layer:** FinalBraid.  **Imports:** `FinalBraid.Lines`, `FinalBraid.Elements`.
-/

open CategoryTheory Opposite CubeChain

namespace FinalBraid

/-- Thinness passes to the opposite category. -/
instance instThinOp {C : Type*} [Category C] [Quiver.IsThin C] : Quiver.IsThin Cᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-- **The braid Salvetti complex** of `□ⁿ`: the category of elements of the chamber presheaf
`Lines (□ⁿ)` — pairs `(x, C)` of a chain and a chamber refining it, in the Salvetti/Paris
order. -/
abbrev Sal (n : ℕ) : Type := (Lines (BPSet.cube n)).Elements

/-- `Sal n` is a poset (thin). -/
instance instThinSal (n : ℕ) : Quiver.IsThin (Sal n) := inferInstance

/-- The forgetful functor `Sal n ⥤ (ChainCat.Obj (□ⁿ))ᵒᵖ`, `(x, C) ↦ x` (the
category-of-elements projection `π`). -/
noncomputable def salToChain (n : ℕ) :
    Sal n ⥤ (ChainCat.Obj (BPSet.cube n))ᵒᵖ :=
  CategoryOfElements.π (Lines (BPSet.cube n))

end FinalBraid
