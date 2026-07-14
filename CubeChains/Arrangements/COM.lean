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

end SignVec

/-! ### Notation

Gotcha: `X ≤ Y` on `SignVec E = E → SignType` already means the **pointwise** order (mathlib's `Pi`
instance), which is *not* the face order.  So `⊑` is a dedicated notation, never an order instance.
-/

@[inherit_doc SignVec.comp] notation:65 X:65 " ⊙ " Y:66 => CubeChains.SignVec.comp X Y
@[inherit_doc SignVec.faceLE] notation:50 X:51 " ⊑ " Y:51 => CubeChains.SignVec.faceLE X Y

open SignVec

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
