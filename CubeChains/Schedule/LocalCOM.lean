import CubeChains.Schedule.Space
import CubeChains.Arrangements.COMLocal
import CubeChains.Salvetti.SalWedge

/-!
# Schedule/LocalCOM — the local COM at a schedule

At a schedule `x`, the walls of the braid arrangement passing through `x` are exactly the
comparisons between events that `x` fires **simultaneously** — i.e. the events sharing a bead of
`x.chain`.  So the local COM is the direct sum of the beads' braid arrangements:

    localCOM x = braidDirectSum x.chain.dims

Ground set = the within-bead pairs; cross-bead comparisons are strict at `x`, hence locally
constant, hence absent.  Consequently the local COM is **trivial exactly at generic schedules**
(`localCOM_isEmpty_iff`): empty ground set iff every bead is 1-dimensional, i.e. iff no two events
are simultaneous.  **The local COM measures concurrency.**
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

variable {K : BPSet}

/-- The local COM at a schedule: the braid arrangements of its beads, summed. -/
def localCOM (x : Sched K) : COM (braidDirectSumGround x.chain.dims) :=
  braidDirectSum x.chain.dims

/-! ## The local COM is trivial exactly at generic schedules -/

/-- A braid ground set is empty iff there is no pair to compare. -/
theorem braidGround_isEmpty_iff (n : ℕ) : IsEmpty (BraidGround n) ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    rw [not_le] at hn
    exact h.elim ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩
  · intro hn
    refine ⟨fun p => ?_⟩
    have h1 : (p.1.1 : ℕ) < p.1.2 := p.2
    have h2 : (p.1.2 : ℕ) < n := p.1.2.isLt
    omega

/-- The summed ground set is empty iff every bead is 1-dimensional. -/
theorem braidDirectSumGround_isEmpty_iff :
    ∀ dims : List ℕ+, IsEmpty (braidDirectSumGround dims) ↔ ∀ d ∈ dims, (d : ℕ) ≤ 1
  | [] => by
      simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
      exact (braidGround_isEmpty_iff 0).mpr (by omega)
  | n :: rest => by
      have hrest := braidDirectSumGround_isEmpty_iff rest
      constructor
      · intro h d hd
        obtain ⟨h1, h2⟩ :=
          isEmpty_sum.mp (h : IsEmpty (BraidGround (n : ℕ) ⊕ braidDirectSumGround rest))
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact (braidGround_isEmpty_iff _).mp h1
        · exact hrest.mp h2 d hd'
      · intro h
        exact isEmpty_sum.mpr
          ⟨(braidGround_isEmpty_iff _).mpr (h n List.mem_cons_self),
            hrest.mpr (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

/-- **The local COM measures concurrency.**  Its ground set is empty — no walls through `x` —
exactly when every bead of `x.chain` is 1-dimensional, i.e. when `x` fires no two events at once. -/
theorem localCOM_isEmpty_iff (x : Sched K) :
    IsEmpty (braidDirectSumGround x.chain.dims) ↔ ∀ d ∈ x.chain.dims, (d : ℕ) = 1 := by
  rw [braidDirectSumGround_isEmpty_iff]
  exact ⟨fun h d hd => le_antisymm (h d hd) d.property, fun h d hd => (h d hd).le⟩

end CubeChains
