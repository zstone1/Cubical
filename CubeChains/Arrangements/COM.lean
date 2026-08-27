import Mathlib.Data.Sign.Defs
import Mathlib.Data.Set.Basic

/-!
# Arrangements/COM — Complexes of Oriented Matroids

Sign-vector (covector) machinery and the **COM** axioms of Bandelt–Chepoi–Knauer
(*COMs: Complexes of oriented matroids*, JCTA 156 (2018)): a nonempty covector set closed
under **face symmetry** (FS) and **strong elimination** (SE).  Oriented matroids (`COM.IsOM`)
are the COMs containing the zero covector.

-/

namespace CubeChains

/-- A **covector** (sign vector) on ground set `E`: a sign (`-`, `0`, `+`) per element. -/
abbrev SignVec (E : Type*) := E → SignType

namespace SignVec
variable {E : Type*}

/-- **Composition** `comp X Y` (`X ∘ Y`): take `X`'s sign where nonzero, else `Y`'s. -/
def comp (X Y : SignVec E) : SignVec E := fun e => if X e = 0 then Y e else X e

/-- **Separator** `sep X Y` (`S(X, Y)`): coordinates where `X`, `Y` are opposite nonzero signs. -/
def sep (X Y : SignVec E) : Set E := {e | X e = - Y e ∧ X e ≠ 0}

/-- **Zero set** of a covector. -/
def zeroSet (X : SignVec E) : Set E := {e | X e = 0}

/-- The **face (conformal) order** `faceLE X Y` (`X ⊑ Y`): each coordinate of `X` is `0` or
equals `Y`'s (so `0 ⊑ ±`, and `+`, `−` are incomparable). -/
def faceLE (X Y : SignVec E) : Prop := ∀ e, X e = 0 ∨ X e = Y e

/-- **Reindexing** along `f : E' → E`: `SignVec` is contravariant in the ground set. -/
def restrict {E' : Type*} (f : E' → E) (Z : SignVec E) : SignVec E' := Z ∘ f

end SignVec

/-! ### Notation

Gotcha: `X ≤ Y` on `SignVec E = E → SignType` already means the **pointwise** order (mathlib's `Pi`
instance), which is *not* the face order.  So `⊑` is a dedicated notation, never an order instance.
-/

@[inherit_doc SignVec.comp] notation:65 X:65 " ⊙ " Y:66 => CubeChains.SignVec.comp X Y
@[inherit_doc SignVec.faceLE] notation:50 X:51 " ⊑ " Y:51 => CubeChains.SignVec.faceLE X Y

open SignVec

/-! ### The face order -/

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

/-! ### Reindexing

Every operation on covectors is pointwise, so reindexing is a homomorphism for all of them. -/

variable {E' : Type*} (f : E' → E)

@[simp] theorem restrict_apply (Z : SignVec E) (e : E') : restrict f Z e = Z (f e) := rfl

@[simp] theorem restrict_comp (X Y : SignVec E) :
    restrict f (X ⊙ Y) = restrict f X ⊙ restrict f Y := rfl

@[simp] theorem restrict_neg (Y : SignVec E) : restrict f (-Y) = -restrict f Y := rfl

@[simp] theorem restrict_zero : restrict f (0 : SignVec E) = 0 := rfl

/-- Reindexing reflects the separator: `f e` separates `X, Y` exactly when `e` separates the
restrictions. -/
theorem mem_sep_restrict {X Y : SignVec E} (e : E') :
    f e ∈ sep X Y ↔ e ∈ sep (restrict f X) (restrict f Y) := Iff.rfl

/-- Reindexing is monotone for the face order. -/
theorem faceLE_restrict {X Y : SignVec E} (h : X ⊑ Y) : restrict f X ⊑ restrict f Y :=
  fun e => h (f e)

end SignVec

/-- A **Complex of Oriented Matroids** (Bandelt–Chepoi–Knauer): a nonempty covector set closed
under face symmetry and strong elimination.  Closure under `comp` is a consequence of these. -/
structure COM (E : Type*) where
  /-- The covectors (the faces of the complex). -/
  covectors : Set (SignVec E)
  /-- The complex is nonempty. -/
  carrier_nonempty : covectors.Nonempty
  /-- **(FS) Face symmetry:** `X ∘ (−Y) ∈ covectors` for all covectors `X, Y`. -/
  faceSymm : ∀ X ∈ covectors, ∀ Y ∈ covectors, X ⊙ (-Y) ∈ covectors
  /-- **(SE) Strong elimination:** for each `e ∈ S(X, Y)` there is a covector `Z` with `Z e = 0`
  that agrees with `X ∘ Y` off the separator. -/
  strongElim : ∀ X ∈ covectors, ∀ Y ∈ covectors, ∀ e ∈ sep X Y,
    ∃ Z ∈ covectors, Z e = 0 ∧ ∀ f, f ∉ sep X Y → Z f = (X ⊙ Y) f

namespace COM
variable {E : Type*}

/-- `L` is an **oriented matroid**: a COM containing the zero covector (equivalently `−L = L`). -/
def IsOM (L : COM E) : Prop := (0 : SignVec E) ∈ L.covectors

/-- A **tope** (chamber) of `L`: a maximal covector in the face order. -/
def IsTope (L : COM E) (T : SignVec E) : Prop :=
  T ∈ L.covectors ∧ ∀ X ∈ L.covectors, T ⊑ X → X = T

/-- The topes (chambers) of `L`. -/
def topes (L : COM E) : Set (SignVec E) := {T | L.IsTope T}

end COM

end CubeChains
