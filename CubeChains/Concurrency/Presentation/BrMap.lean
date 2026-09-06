import CubeChains.Concurrency.Presentation.GlueRun

/-!
# Concurrency/Presentation/BrMap — a map of braid presentations, lifted

A map `p ⟶ q` spells a generator of `p` by a **word** of `q` performing the same braid
(`braid_word`).  The action of the braid monoid on the runs is a monoid hom into the partial maps,
so a defined product is a defined *sequence* of steps: the word acts letter by letter, and its
trace is a word of the slice polygraph.  That is the whole of the lift.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-! ## A defined product is a defined sequence of steps -/

/-- **The action splits along a product** — `sliceActionAt` is a monoid hom into the partial maps,
so no weak-order argument is needed. -/
theorem sliceActionAt_mul_split {β γ : PosBraid N} {u v : RunAt d N}
    (h : (sliceActionAt d N (β * γ)).unop.val (some u) = some v) :
    ∃ w : RunAt d N, (sliceActionAt d N β).unop.val (some u) = some w ∧
      (sliceActionAt d N γ).unop.val (some w) = some v := by
  have hsplit : (sliceActionAt d N (β * γ)).unop.val (some u)
      = (sliceActionAt d N γ).unop.val ((sliceActionAt d N β).unop.val (some u)) := by
    rw [map_mul]; rfl
  rw [hsplit] at h
  cases hw : (sliceActionAt d N β).unop.val (some u) with
  | none =>
      rw [hw, (sliceActionAt d N γ).unop.2] at h
      exact absurd h (by simp)
  | some w => exact ⟨w, rfl, by rwa [hw] at h⟩

/-- The run a defined step lands on. -/
noncomputable def actTarget (β : PosBraid N) (u : RunAt d N)
    (h : (sliceActionAt d N β).unop.val (some u) ≠ none) : RunAt d N :=
  ((sliceActionAt d N β).unop.val (some u)).get (Option.ne_none_iff_isSome.mp h)

theorem act_actTarget (β : PosBraid N) (u : RunAt d N)
    (h : (sliceActionAt d N β).unop.val (some u) ≠ none) :
    (sliceActionAt d N β).unop.val (some u) = some (actTarget β u h) :=
  (Option.some_get _).symm

theorem actTarget_eq {β : PosBraid N} {u v : RunAt d N}
    (h : (sliceActionAt d N β).unop.val (some u) = some v) :
    actTarget β u (by rw [h]; exact Option.some_ne_none v) = v :=
  Option.some_inj.mp ((act_actTarget β u _).symm.trans h)

/-- **A defined product is defined at its first factor.** -/
theorem act_ne_none_left {β γ : PosBraid N} {u v : RunAt d N}
    (h : (sliceActionAt d N (β * γ)).unop.val (some u) = some v) :
    (sliceActionAt d N β).unop.val (some u) ≠ none := by
  obtain ⟨w, hw, -⟩ := sliceActionAt_mul_split h
  rw [hw]
  exact Option.some_ne_none w

/-- **…and its second factor finishes the step.** -/
theorem act_right {β γ : PosBraid N} {u v : RunAt d N}
    (h : (sliceActionAt d N (β * γ)).unop.val (some u) = some v) :
    (sliceActionAt d N γ).unop.val (some (actTarget β u (act_ne_none_left h))) = some v := by
  obtain ⟨w, hw, hv⟩ := sliceActionAt_mul_split h
  rwa [actTarget_eq hw]

/-! ## The lift

A base word acts on a run in one step per letter, and each step is a 1-cell of the slice
polygraph. -/

namespace BraidPresentation

variable (r : BraidPresentation)

/-- The braid a word of the strand-`N` component performs. -/
def wordBraid {N : ℕ} {x y : GenObj (r.P N).Gen} (w : Quiver.Path x y) : PosBraid N :=
  ((r.comp N).eval.map w).unop

@[simp] theorem wordBraid_nil (x : GenObj (r.P N).Gen) :
    r.wordBraid (Quiver.Path.nil : Quiver.Path x x) = 1 :=
  congrArg Quiver.Hom.unop (Presents.eval_nil (r.comp N) x)

@[simp] theorem wordBraid_cons {x y z : GenObj (r.P N).Gen} (w : Quiver.Path x y) (e : y ⟶ z) :
    r.wordBraid (w.cons e) = r.wordBraid w * r.braid e :=
  congrArg Quiver.Hom.unop (Presents.eval_cons (r.comp N) w e)

/-- **A word of the base acting on a run lifts to a word of the slice**, letter by letter. -/
noncomputable def runPath (r : BraidPresentation) {d : Ch Zbp} {N : ℕ} :
    ∀ {x y : GenObj (r.P N).Gen} (w : Quiver.Path x y) (u v : RunAt d N),
      (sliceActionAt d N (r.wordBraid w)).unop.val (some u) = some v →
      Quiver.Path (⟨r.runPt u⟩ : GenObj (slicePolyRaw r.base d).Gen) ⟨r.runPt v⟩
  | _, _, Quiver.Path.nil, u, v, h => by
      have h0 : (sliceActionAt d N (1 : PosBraid N)).unop.val (some u) = some u := by
        rw [map_one]; rfl
      obtain rfl : u = v :=
        Option.some_inj.mp (h0.symm.trans
          ((congrArg (fun β => (sliceActionAt d N β).unop.val (some u))
            (r.wordBraid_nil _)).symm.trans h))
      exact Quiver.Path.nil
  | _, _, Quiver.Path.cons w e, u, v, h => by
      rw [r.wordBraid_cons] at h
      exact (r.runPath w u (actTarget _ u (act_ne_none_left h)) (act_actTarget _ u _)).cons
        (r.runGen (r.toS e) (by rw [r.braid_toS]; exact act_right h))

end BraidPresentation

/-! ## What a map lifts to

A generator of `p` acting on a run is spelled, over the *same* two runs, by the `q`-word the map
gives it — the word performs the generator's own braid (`braid_word`). -/

/-- **A map of braid presentations lifts a generator's step to a word of the slice.** -/
noncomputable def BraidPresentation.Map.slicePath {p q : BraidPresentation}
    (m : BraidPresentation.Map p q) {d : Ch Zbp} {N : ℕ} (s : p.S N) {u v : RunAt d N}
    (h : (sliceActionAt d N (p.braid s)).unop.val (some u) = some v) :
    Quiver.Path (⟨q.runPt u⟩ : GenObj (slicePolyRaw q.base d).Gen) ⟨q.runPt v⟩ :=
  q.runPath (m.word s) u v
    (by rw [show q.wordBraid (m.word s) = p.braid s from m.braid_word s]; exact h)

end ChainCat
