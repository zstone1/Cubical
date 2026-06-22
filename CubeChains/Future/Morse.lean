import CubeChains.Foundations.Altitude
import CubeChains.Cobordisms.Loops
import CubeChains.Cobordisms.Cobordism

/-!
# Future/Morse — directed discrete Morse theory (statement-only stubs)

**Out of scope for the current build** (spec §"Out of scope"): statements only, no
proofs.  Every theorem here is deliberately `sorry`'d scaffolding marking a research
direction; this file is *not* counted against the sorry-free target.

## The program

For a directed cobordism `W : X ⇒ Y`, the **directed-time function** is an altitude
function `alt` on `W.mid` (`PrecubicalSet.IsAltitude`): it rises by `1` across target
faces and is unchanged across source faces, so it is a *discrete Morse function* in the
sense of Forman, adapted to the directed (semicubical) setting.  The claims:

* **Acyclicity ⇔ loop-confinement.**  The discrete gradient *matching* induced by `alt`
  (pair each non-critical cell with the unique coordinate along which time strictly
  increases) is acyclic exactly when the cobordism is `LoopConfined` — every nontrivial
  strongly-connected component sits in the source `i X` or the sink `j Y`.
* **Handle / critical-cell classification.**  The unmatched (critical) cells of `alt`
  classify by their local source/target degree into **caps**, **cups**, **saddles**, and
  **cylinders** (regular handles), giving a directed handle decomposition of `W`.
* **Morse ⇒ collared.**  A cobordism carrying such a Morse function deformation-retracts
  onto a collared normal form, recovering the `SourceCollar`/`SinkCollar` data.

See `Foundations/Altitude.lean` (`IsAltitude`, `alt_vertex₀/₁`) and `Cobordisms/Loops.lean`
(`IsLoopFree`, `LoopConfined`).
-/

namespace PrecubicalSet.Future.Morse

open Precubical.Cobordism

/-- The four classes of critical cells of a directed discrete Morse function: the local
shape of the directed-time function at an unmatched cell. -/
inductive CriticalType
  | cap      -- a directed minimum (source-like): all incident time-arrows point out
  | cup      -- a directed maximum (sink-like): all incident time-arrows point in
  | saddle   -- mixed: a genuine merge/branch
  | cylinder -- a regular handle: time passes straight through
  deriving DecidableEq, Repr

/-- **The directed-time function is a discrete Morse function.**  An altitude on the apex
of a cobordism is the canonical Morse datum.  (Statement-only; the Morse structure and its
gradient matching are to be defined.) -/
theorem altitude_isMorse {X Y : PrecubicalSet} (W : DirectedCobordism X Y)
    (alt : ∀ n, W.mid.cells n → ℤ) (_ : W.mid.IsAltitude alt) :
    True := by
  -- TODO(dCob): Future stub — replace `True` with "the gradient matching of `alt` is a
  -- well-defined discrete Morse matching" once the matching is defined.
  trivial

/-- **Acyclicity ⇔ loop-confinement.**  The discrete gradient matching of the directed-time
function is acyclic iff the cobordism's nontrivial loops are confined to the boundary. -/
theorem gradientAcyclic_iff_loopConfined {X Y : PrecubicalSet} (W : DirectedCobordism X Y) :
    IsLoopFree W.mid ↔ True := by
  -- TODO(dCob): Future stub — replace the RHS with "the gradient matching is acyclic"
  -- and prove the equivalence (this is the directed Forman theorem in this setting).
  sorry

/-- **Critical cells classify.**  Every critical cell of the directed-time function carries
one of the four `CriticalType` labels (cap / cup / saddle / cylinder). -/
theorem critical_classification {X Y : PrecubicalSet} (W : DirectedCobordism X Y)
    (_alt : ∀ n, W.mid.cells n → ℤ) {n : ℕ} (_c : W.mid.cells n) :
    Nonempty CriticalType :=
  -- TODO(dCob): Future stub — restrict to *critical* cells and produce the canonical label.
  ⟨CriticalType.cylinder⟩

end PrecubicalSet.Future.Morse
