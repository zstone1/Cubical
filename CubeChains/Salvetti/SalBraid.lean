import CubeChains.Salvetti.SalExec
import CubeChains.Braid.SalvettiConstruction

/-!
# Salvetti/SalBraid — the Salvetti grading is the chain-side one

`crossPerm a b = stepPerm f` across `braidSalEquiv`: a Salvetti cell's `topePerm` is its execution's
run word, inverted (`topePerm_eq`), because `topeRank` counts predecessors and a run word's
predecessor count at `p` is the step `w⁻¹ p` at which `p` fires.

So `crossPerm_noDoubleCross` is `permOf_noDoubleCross`, not a second proof of it, and
`salvettiGrading` is `ConcPos` read on cells.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

open COM ChStar

variable {n : ℕ}

/-! ## The rank of a run word -/

/-- A permutation has exactly `k` values below `k`. -/
theorem card_filter_lt_perm (e : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ.filter (fun j => e j < k)).card = (k : ℕ) := by
  have h : Finset.univ.filter (fun j => e j < k) = (Finset.Iio k).map e.symm.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio,
      Equiv.coe_toEmbedding]
    exact ⟨fun hj => ⟨e j, hj, e.symm_apply_apply j⟩,
      by rintro ⟨i, hi, rfl⟩; rwa [e.apply_symm_apply]⟩
  rw [h, Finset.card_map, Fin.card_Iio]

/-- `topeRank_eq_card` off a bare tope rather than a cell. -/
theorem topeRank_eq_card' {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T)
    {σ : Fin n → ℤ} (h : T = braidSign σ) (i : Fin n) :
    (topeRank T i : ℕ) = (Finset.univ.filter (fun j => σ j < σ i)).card :=
  topeRank_eq_card (a := topeCell ⟨T, hT⟩) h i

/-- **The tope rank of a run word is the step at which the coordinate fires.**  `topeRank` counts
predecessors in the tope's order, and a run word's order *is* `w⁻¹`. -/
theorem topeRank_wordTope (w : Equiv.Perm (Fin n)) (p : Fin n) :
    topeRank (wordTope w) p = w.symm p := by
  refine Fin.ext ?_
  rw [topeRank_eq_card' (isTope_wordTope w) (wordTope_eq_braidSign w) p]
  simp only [Nat.cast_lt, ← Fin.lt_def]
  exact card_filter_lt_perm w.symm (w.symm p)

/-! ## The dictionary -/

/-- The run word of a Salvetti cell: the word its tope names. -/
noncomputable abbrev cellWord (a : Sal (braidCOM n)) : Equiv.Perm (Fin n) :=
  wordTopeEquiv.symm ⟨a.tope, a.2.2.1⟩

/-- **A cell's permutation is its run word, inverted.** -/
theorem topePerm_eq (a : Sal (braidCOM n)) : topePerm a = (cellWord a).symm := by
  have hw : wordTope (cellWord a) = a.tope := wordTope_symm _
  refine Equiv.ext fun p => ?_
  rw [topePerm_apply, ← hw, topeRank_wordTope]

/-- **…and the execution it classifies runs that word.** -/
theorem runWord_salChStarEquiv (a : Sal (braidCOM n)) :
    runWord (salChStarEquiv a) = cellWord a :=
  wordTope_injective
    ((wordTope_salChStarEquiv a).trans (wordTope_symm (⟨a.tope, a.2.2.1⟩ : Tope n)).symm)

/-- **The Salvetti crossing permutation is the change of run word.**  Both sides are
`w_b⁻¹ ∘ w_a`; `crossPerm` reads it off sign vectors, `stepPerm` off the executions. -/
theorem crossPerm_eq_stepPerm {a b : Sal (braidCOM n)} (h : a ⟶ b) :
    crossPerm a b = stepPerm (braidSalEquiv.functor.map h) := by
  rw [stepPerm_eq, braidSalEquiv_functor_obj, braidSalEquiv_functor_obj,
    runWord_salChStarEquiv, runWord_salChStarEquiv, crossPerm, topePerm_eq, topePerm_eq]
  rfl

/-! ## No double crossing, transported

`permOf_noDoubleCross` is proved once, on the run side (`Salvetti/EventBraid`).  `permLen` is
invariant under `permCast`, so it reads off `stepPerm` unchanged, and `crossPerm` is `stepPerm`. -/

/-- **Length-additivity for executions** — `permOf_noDoubleCross` at the ambient strand count. -/
theorem stepPerm_noDoubleCross {x y z : Ch⋆ (□n)} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (stepPerm (f ≫ g)) = permLen (stepPerm f) + permLen (stepPerm g) := by
  rw [stepPerm, stepPerm, stepPerm, RunWedge.permLen_permCast, RunWedge.permLen_permCast,
    RunWedge.permLen_permCast, Functor.map_comp, RunWedge.permOf_noDoubleCross]

/-- **Length-additivity of the Salvetti crossing cocycle** — the germ relation, transported from
the run side rather than re-proved on sign vectors. -/
theorem crossPerm_noDoubleCross {a b c : Sal (braidCOM n)} (hab : a ⟶ b) (hbc : b ⟶ c) :
    permLen (crossPerm a c) = permLen (crossPerm a b) + permLen (crossPerm b c) := by
  rw [crossPerm_eq_stepPerm (hab ≫ hbc), crossPerm_eq_stepPerm hab, crossPerm_eq_stepPerm hbc,
    Functor.map_comp, stepPerm_noDoubleCross]

/-! ## The Salvetti construction -/

/-- **The Salvetti braid grading** — computable: a Salvetti edge `a ⟶ b` goes to the positive braid
of its crossing permutation `crossPerm a b`, read straight off the sign vectors. -/
def salvettiGrading (n : ℕ) : Sal (braidCOM n) ⥤ SingleObj (Braid n) :=
  permBraidFunctor n
    (p := fun {a b} (_ : a ⟶ b) => crossPerm a b)
    (hp1 := crossPerm_self)
    (hpc := fun {a b c} (_ : a ⟶ b) (_ : b ⟶ c) => crossPerm_comp a b c)
    (hlen := fun {_ _ _} f g => crossPerm_noDoubleCross f g)

/-- **The Salvetti construction** on the concurrency braid groupoid of the braid arrangement: the
free-groupoid lift of `salvettiGrading`.  (Noncomputable only through mathlib's `FreeGroupoid.lift`,
exactly as `braidGrpd`; braid words are computed by `salvettiGrading`.) -/
noncomputable def salvettiConstruction (n : ℕ) :
    FreeGroupoid (Sal (braidCOM n)) ⥤ SingleObj (Braid n) :=
  FreeGroupoid.lift (salvettiGrading n)

end CubeChains
