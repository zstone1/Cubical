import CubeChains.Braid.Grading

/-!
# Braid/ChGrading — the same construction over `Ch K`, and what it loses

`braidGrading` needs a *frame*: to say "event `i` crossed event `j`" you must first name the events,
and a chain names them only up to the order inside each bead.  The line supplies that order.

`Ch K` has no line — but it does have a **canonical** one.  `faceEmb` is an *order embedding*
(no axis swaps: the cubes are rigid), so ordering every bead's events by their axis index is
preserved by restriction (`linesRestrict_stdLine`).  Hence a section

    stdSection : (Ch K)ᵒᵖ ⥤ Int(Lines K)      with   stdSection ⋙ π = 𝟭

and therefore the Ch-side braid functor `chBraid = stdSection ⋙ braidGrading` **exists**.

So the line is not needed to *define* a braid functor.  What it is needed for is the **loops**:
`Ch(⋁dims)` has a terminal object (the taut chain), so its free groupoid is codiscrete and
`chBraid` has no monodromy at all there — while `ConcGrpd(□ⁿ)` is the Salvetti complex, whose vertex
group is the pure braid group.  The braid lives in the *fibre* of `π`, which `Ch K` has collapsed.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

open ChainCat CubeChain

variable {K : BPSet}

/-! ## The standard line -/

/-- The **standard chamber**: a bead fires its events in axis order. -/
def stdChamber (d : ℕ) : Chamber d where
  lt := (· < ·)
  sto := inferInstance

/-- The **standard line** of a chain: every bead in axis order. -/
def stdLine (a : Ch K) : LinesObj a := fun i => stdChamber (beadDim a i)

/-- **The standard line is coherent.**  `faceEmb` is an order embedding — the cubes are rigid, so a
face map never swaps axes — hence restricting the standard chamber gives the standard chamber. -/
theorem linesRestrict_stdLine {a b : Ch K} (f : a ⟶ b) :
    linesRestrict f (stdLine b) = stdLine a := by
  funext i
  apply Chamber.ext
  funext p q
  simp only [linesRestrict, stdLine, stdChamber, Chamber.restrict_lt]
  exact propext (faceEmb (blockFace fᵂ i)).lt_iff_lt

/-! ## The section, and the Ch-side braid functor -/

/-- **The standard-line section** — a coherent choice of line for every chain. -/
noncomputable def stdSection (K : BPSet) : (Ch K)ᵒᵖ ⥤ ConcCat K where
  obj a := ⟨a, stdLine a.unop⟩
  map {a b} f := ⟨f, linesRestrict_stdLine f.unop⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- It really is a section: forgetting the line returns the chain. -/
@[simp] theorem stdSection_π_obj (a : (Ch K)ᵒᵖ) :
    (CategoryOfElements.π (Lines K)).obj ((stdSection K).obj a) = a := rfl

@[simp] theorem stdSection_π_map {a b : (Ch K)ᵒᵖ} (f : a ⟶ b) :
    (CategoryOfElements.π (Lines K)).map ((stdSection K).map f) = f := rfl

/-- **The braid functor over `Ch K`**: the same construction, with the canonical line.

It exists — but see the module docstring: its source has no loops over a cube, so it sees no braid
there.  `braidGrading` on `Int(Lines K)` does. -/
noncomputable def chBraid (K : BPSet) : (Ch K)ᵒᵖ ⥤ Braids :=
  stdSection K ⋙ braidGrading K

@[simp] theorem chBraid_obj (a : (Ch K)ᵒᵖ) :
    (chBraid K).obj a = strands (nEvents ⟨a, stdLine a.unop⟩) := rfl

end CubeChains
