import CubeChains.Salvetti.Normalize
import CubeChains.Events.EventMapBij
import Mathlib.GroupTheory.Perm.Basic

/-!
# Braid/Frame — the event frame of an execution and its transition permutation

An execution `(a, L)` names its events in the order of its line: `evKey` (bead first, then the bead
chamber's rank) is a total order, so `evIdx : EventObj a ≃ Fin n`.  A refinement identifies the two
event sets (`eventMap`), and the two frames differ by the **event permutation** `evPerm f`.

This is the chain/line semantics only — no arrangement, no Salvetti cell.  The braid arrangement
reads a *cell* off this frame (`Salvetti/BraidFunctor`); the germ-side braid functor reads the
*permutation* (`Braid/Functor`).  Both sit on top of this file.
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

/-! ## Executions with a fixed number of events -/

variable {K : BPSet} {n : ℕ}

/-- The executions of `K` with exactly `n` events. -/
def ConcN (K : BPSet) (n : ℕ) : ObjectProperty (ConcCat K) :=
  fun x => Fintype.card (EventObj x.chain) = n

/-- The full subcategory of executions with `n` events.  Morphisms preserve the event count
(`card_eventObj_eq_of_hom`), so this is a union of connected components of `ConcCat K`. -/
abbrev ConcCatN (K : BPSet) (n : ℕ) : Type _ := (ConcN K n).FullSubcategory

/-- The groupoidification: the `n`-event part of the concurrency braid groupoid. -/
abbrev ConcGrpdN (K : BPSet) (n : ℕ) : Type _ := FreeGroupoid (ConcCatN K n)

/-- The **event names** of an execution: its events listed in the order of its line
(`evKey` — bead first, then the bead chamber's rank). -/
noncomputable def evIdx (x : ConcCatN K n) : EventObj x.obj.chain ≃ Fin n :=
  (keyEquiv (evKey x.obj.line) (evKey_injective _)).trans (finCongr x.property)

theorem evIdx_val (x : ConcCatN K n) (e : EventObj x.obj.chain) :
    ((evIdx x e : Fin n) : ℕ) = keyRank (evKey x.obj.line) e := rfl

/-- The event names enumerate the `evKey` order. -/
theorem evIdx_lt_iff (x : ConcCatN K n) (e e' : EventObj x.obj.chain) :
    evIdx x e < evIdx x e' ↔ evKey x.obj.line e < evKey x.obj.line e' := by
  rw [Fin.lt_def, evIdx_val, evIdx_val]
  refine ⟨fun h => ?_, keyRank_strictMono _⟩
  rcases lt_trichotomy (evKey x.obj.line e) (evKey x.obj.line e') with hl | he | hg
  · exact hl
  · exact absurd (congrArg (keyRank (evKey x.obj.line)) (evKey_injective _ he)) (Nat.ne_of_lt h)
  · exact absurd (keyRank_strictMono (evKey x.obj.line) hg) (by omega)

theorem evKey_symm_lt (x : ConcCatN K n) {k l : Fin n} (h : k < l) :
    evKey x.obj.line ((evIdx x).symm k) < evKey x.obj.line ((evIdx x).symm l) := by
  rw [← evIdx_lt_iff]
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The bead of the `k`-th event of `x`. -/
noncomputable def fineBead (x : ConcCatN K n) (k : Fin n) : ChainCat.Bead x.obj.chain :=
  ((evIdx x).symm k).1

/-- Two events in `evKey` order sit in weakly increasing beads (the key is lex, bead first). -/
theorem fineBead_le (x : ConcCatN K n) {k l : Fin n} (h : k < l) : fineBead x k ≤ fineBead x l := by
  have hk := evKey_symm_lt x h
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at hk
  rcases hk with h1 | ⟨h1, _⟩
  · exact le_of_lt (Fin.lt_def.mpr h1)
  · exact le_of_eq (Fin.ext h1)

/-- Two `evKey`-consecutive events of the *same* bead are ordered by the bead's chamber. -/
theorem chamberRank_lt_of_lt (x : ConcCatN K n) {k l : Fin n} (h : k < l)
    (hb : fineBead x k = fineBead x l) :
    chamberRank (x.obj.line (fineBead x k)) ((evIdx x).symm k).2
      < chamberRank (x.obj.line (fineBead x l)) ((evIdx x).symm l).2 := by
  have hk := evKey_symm_lt x h
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at hk
  rcases hk with h1 | ⟨_, h2⟩
  · exact absurd (congrArg (fun i : ChainCat.Bead x.obj.chain => (i : ℕ)) hb) (Nat.ne_of_lt h1)
  · exact h2

/-! ## The event permutation of a morphism -/

/-- The refinement underlying a morphism of executions (`y`'s chain refines `x`'s). -/
def concRefine {x y : ConcCatN K n} (f : x ⟶ y) :
    y.obj.chain ⟶ x.obj.chain := f.hom.1.unop

theorem concRefine_line {x y : ConcCatN K n} (f : x ⟶ y) :
    linesRestrict (concRefine f) x.obj.line = y.obj.line := f.hom.2

theorem concRefine_id (x : ConcCatN K n) : concRefine (𝟙 x) = 𝟙 x.obj.chain := rfl

theorem concRefine_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    concRefine (f ≫ g) = concRefine g ≫ concRefine f := rfl

/-- **The event permutation** of a morphism: the discrepancy between the two `evKey` frames,
`eventMap` identifying the two event sets. -/
noncomputable def evPerm {x y : ConcCatN K n} (f : x ⟶ y) : Equiv.Perm (Fin n) :=
  ((evIdx x).symm.trans (eventEquiv (concRefine f)).symm).trans (evIdx y)

theorem evPerm_inv_apply {x y : ConcCatN K n} (f : x ⟶ y) (l : Fin n) :
    (evPerm f)⁻¹ l = evIdx x (eventMap (concRefine f) ((evIdx y).symm l)) := rfl

theorem evPerm_id (x : ConcCatN K n) : evPerm (𝟙 x) = 1 := by
  apply Equiv.ext
  intro k
  change evIdx x ((eventEquiv (concRefine (𝟙 x))).symm ((evIdx x).symm k)) = k
  rw [concRefine_id, eventEquiv_id]
  simp

theorem evPerm_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    evPerm (f ≫ g) = evPerm g * evPerm f := by
  apply Equiv.ext
  intro k
  change evIdx z ((eventEquiv (concRefine (f ≫ g))).symm ((evIdx x).symm k))
    = evIdx z ((eventEquiv (concRefine g)).symm
        ((evIdx y).symm (evIdx y ((eventEquiv (concRefine f)).symm ((evIdx x).symm k)))))
  rw [Equiv.symm_apply_apply, concRefine_comp, eventEquiv_comp, Equiv.symm_trans_apply]

/-- **The within-bead core.**  Two events of one bead of the finer chain land in one bead of the
coarser chain, ordered by the *same* chamber: the fine bead's chamber is the coarse one restricted
along the free-coordinate embedding (`linesRestrict`). -/
theorem evKey_eventMap_lt {x y : ConcCatN K n} (f : x ⟶ y) {e e' : EventObj y.obj.chain}
    (hb : e.1 = e'.1) (h : evKey y.obj.line e < evKey y.obj.line e') :
    evKey x.obj.line (eventMap (concRefine f) e)
      < evKey x.obj.line (eventMap (concRefine f) e') := by
  obtain ⟨i, δ⟩ := e
  obtain ⟨i', δ'⟩ := e'
  subst hb
  -- the fine chamber is the coarse chamber, restricted
  have hline : y.obj.line i
      = (x.obj.line (blockIdx (concRefine f)ᵂ i)).restrict
          (faceEmb (blockFace (concRefine f)ᵂ i))
          (faceEmb (blockFace (concRefine f)ᵂ i)).injective :=
    congrFun (concRefine_line f).symm i
  -- the fine order of the two directions
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at h
  have hfine : chamberRank (y.obj.line i) δ < chamberRank (y.obj.line i) δ' := by
    rcases h with h1 | ⟨_, h2⟩
    · exact absurd h1 (lt_irrefl _)
    · exact h2
  have hcoarse : chamberRank (x.obj.line (blockIdx (concRefine f)ᵂ i))
        (faceEmb (blockFace (concRefine f)ᵂ i) δ)
      < chamberRank (x.obj.line (blockIdx (concRefine f)ᵂ i))
        (faceEmb (blockFace (concRefine f)ᵂ i) δ') := by
    rw [chamberRank_lt_iff]
    have := (chamberRank_lt_iff (y.obj.line i) δ δ').mp hfine
    rw [hline] at this
    exact this
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, hcoarse⟩

end CubeChains
