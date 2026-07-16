import CubeChains.Braid.PermWord
import CubeChains.Braid.Grading

/-!
# Braid/BraidWord — the braid word of a refinement

`braidWord f := permWord (evPerm' f)` reads a reduced Artin word off a refinement's event
permutation.  `wordToBraid (braidWord f) = ofPerm (evPerm' f)` is exactly the braid content of
`braidGrading.map f` (which is `braidHom (ofPerm (evPerm' f))`); `braidWordZ` is the signed GAP
form.  The word is non-normalized (GAP handles normalization).
-/

namespace CubeChains

open CategoryTheory

variable {K : BPSet}

/-- The reduced Artin word of a refinement's event permutation. -/
def braidWord {x y : ConcCat K} (f : x ⟶ y) : List (Fin (nEvents x - 1)) :=
  permWord (evPerm' f)

/-- The braid the word realises is the braid content of `braidGrading.map f`. -/
theorem wordToBraid_braidWord {x y : ConcCat K} (f : x ⟶ y) :
    wordToBraid (braidWord f) = ofPerm (evPerm' f) :=
  wordToBraid_permWord (evPerm' f)

/-- The word length is the writhe of the refinement. -/
theorem braidWord_length {x y : ConcCat K} (f : x ⟶ y) :
    (braidWord f).length = permLen (evPerm' f) :=
  permWord_length (evPerm' f)

/-- The signed, 1-based (GAP-ready) form of `braidWord`. -/
def braidWordZ {x y : ConcCat K} (f : x ⟶ y) : List ℤ := permWordZ (evPerm' f)

/-- **The word IS `braidGrading`'s output, printed.**  `braidGrading.map f` is exactly `braidHom`
of the braid the word represents (up to the strand-count recast): reading `braidWord f` back through
`wordToBraid` recovers the functor's value.  This is what makes the emitter a faithful evaluator of
`braidGrading`, not a parallel computation — the braid itself is an opaque `PresentedGroup` element
with no `#eval`, so the word is how it becomes readable. -/
theorem braidGrading_map_braidWord {x y : ConcCat K} (f : x ⟶ y) :
    (braidGrading K).map f
      = braidHom (wordToBraid (braidWord f)) ≫ eqToHom (congrArg strands (nEvents_eq f)) := by
  change braidHom (ofPerm (evPerm' f)) ≫ eqToHom (congrArg strands (nEvents_eq f))
    = braidHom (wordToBraid (braidWord f)) ≫ eqToHom (congrArg strands (nEvents_eq f))
  rw [wordToBraid_braidWord]

end CubeChains
