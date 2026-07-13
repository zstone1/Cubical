import CubeChains.Arrangements.COM
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Arrangements/Sal — the Salvetti face poset of a COM (the definition of `Sal`)

**This is the authoritative definition of the Salvetti complex `Sal`.**  For a complex of
oriented matroids `L` (`Arrangements/COM.lean`) the **Salvetti (face) poset** `Sal L` has cells
`(X, T)` — a covector (face) `X` and a tope `T` above it (`X ⊑ T`) — ordered by the
Salvetti/Paris wall-crossing order

> `(X, T) ≤ (X', T')  ⟺  X ⊑ X'  ∧  T' = X' ⊙ T`

(`X'` a finer face, `T'` the projection `X' ⊙ T` of `T` onto it).  This is exactly the
Salvetti poset of Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional
oriented matroids* (arXiv:2507.06365); classically Salvetti (1987) for arrangements and
Gel'fand–Rybnikov / Björner–Ziegler for oriented matroids.

`Sal L` is a `PartialOrder`, hence a thin category, so its Salvetti simplicial set is the free
`nerve (Sal L)` (`salNerve`).

The braid arrangement is assembled as a COM in `Arrangements/Braid.lean`; the intrinsic
cube-chain model `Int(Lines(□ⁿ)) := (Lines □ⁿ).Elements` (`Salvetti/Lines.lean`) is the other
side of the target comparison `Sal (braidCOM n) ≌ Int(Lines(□ⁿ))`.

-/

open CategoryTheory

namespace CubeChains

namespace SignVec
variable {E : Type*}

/-- The face order is reflexive. -/
theorem faceLE_refl (X : SignVec E) : X ⊑ X := fun _ => Or.inr rfl

/-- The face order is transitive. -/
theorem faceLE_trans {X Y Z : SignVec E} (hxy : X ⊑ Y) (hyz : Y ⊑ Z) : X ⊑ Z := by
  intro e
  rcases hxy e with h1 | h1
  · exact Or.inl h1
  · rcases hyz e with h2 | h2
    · exact Or.inl (h1.trans h2)
    · exact Or.inr (h1.trans h2)

/-- The face order is antisymmetric. -/
theorem faceLE_antisymm {X Y : SignVec E} (hxy : X ⊑ Y) (hyx : Y ⊑ X) : X = Y := by
  funext e
  rcases hxy e with h1 | h1
  · rcases hyx e with h2 | h2
    · rw [h1, h2]
    · exact h2.symm
  · exact h1

/-- Composing a face into a tope above it recovers the tope: `X ⊑ T ⟹ X ⊙ T = T`. -/
theorem comp_eq_right_of_faceLE {X T : SignVec E} (h : X ⊑ T) : X ⊙ T = T := by
  funext e
  simp only [comp]
  rcases h e with he | he
  · rw [if_pos he]
  · by_cases h0 : X e = 0
    · rw [if_pos h0]
    · rw [if_neg h0, he]

/-- Projecting onto a finer face absorbs a coarser one: `X ⊑ Y ⟹ Y ⊙ (X ⊙ T) = Y ⊙ T`. -/
theorem comp_comp_of_faceLE {X Y T : SignVec E} (h : X ⊑ Y) :
    Y ⊙ (X ⊙ T) = Y ⊙ T := by
  funext e
  simp only [comp]
  by_cases hY : Y e = 0
  · rw [if_pos hY, if_pos hY]
    rcases h e with hx | hx
    · rw [if_pos hx]
    · rw [if_pos (hx.trans hY)]
  · rw [if_neg hY, if_neg hY]

end SignVec

namespace COM
variable {E : Type*}

open SignVec

/-- A **Salvetti cell** of `L`: a covector (face) `X` together with a tope `T` above it
(`X ⊑ T`). -/
def SalCell (L : COM E) : Type _ :=
  { p : SignVec E × SignVec E // p.1 ∈ L.covectors ∧ L.IsTope p.2 ∧ p.1 ⊑ p.2 }

namespace SalCell
variable {L : COM E}

/-- The face component `X` of a Salvetti cell. -/
abbrev face (a : SalCell L) : SignVec E := a.1.1

/-- The tope component `T` of a Salvetti cell. -/
abbrev tope (a : SalCell L) : SignVec E := a.1.2

/-- `a.face ⊑ a.tope`. -/
theorem faceLE_face_tope (a : SalCell L) : a.face ⊑ a.tope := a.2.2.2

/-- The **Salvetti (Paris) order** on cells: `(X, T) ≤ (X', T')` iff `X ⊑ X'` and `T'` is the
wall-crossing projection `X' ⊙ T` of `T` onto the finer face `X'`. -/
instance : PartialOrder (SalCell L) where
  le a b := a.face ⊑ b.face ∧ b.tope = b.face ⊙ a.tope
  le_refl a := ⟨faceLE_refl _, (comp_eq_right_of_faceLE a.faceLE_face_tope).symm⟩
  le_trans a b c hab hbc :=
    ⟨faceLE_trans hab.1 hbc.1, by rw [hbc.2, hab.2, comp_comp_of_faceLE hbc.1]⟩
  le_antisymm a b hab hba := by
    have hface : a.face = b.face := faceLE_antisymm hab.1 hba.1
    have htope : a.tope = b.tope := by
      rw [hab.2, ← hface, comp_eq_right_of_faceLE a.faceLE_face_tope]
    exact Subtype.ext (Prod.ext_iff.mpr ⟨hface, htope⟩)

/-- Unfolding of the Salvetti order. -/
theorem le_iff (a b : SalCell L) :
    a ≤ b ↔ a.face ⊑ b.face ∧ b.tope = b.face ⊙ a.tope := Iff.rfl

end SalCell

end COM

/-- **The Salvetti face poset** of a COM `L`: its cells `(X, T)` (a face below a tope) in the
Salvetti/Paris order.  The authoritative `Sal`. -/
abbrev Sal {E : Type*} (L : COM E) : Type _ := COM.SalCell L

/-- The **Salvetti simplicial set** of `L`: the nerve of its face poset. -/
noncomputable def salNerve {E : Type*} (L : COM E) : SSet := nerve (Sal L)

end CubeChains
