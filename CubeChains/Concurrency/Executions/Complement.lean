import CubeChains.Concurrency.Executions.RunPerm

/-!
# Concurrency/Executions/Complement — the complementary run

A chain of `K` is refined by a run bead by bead (`Lines K`), and each bead's run can be **reversed**
(`Run.rev`).  Doing that in every bead at once is the **complement**: the same chain, the run run
backwards inside it.

    X.chain ──run──▸ b          complement         X'.chain ──run──▸ b

On a bead cut into `k` pieces it acts by the longest element of `Sₖ` — so it carries the merge out
of a run (crossing nothing) to the greatest crossing onto the same chain.  Nothing is chosen:
reversal is a bijection.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

/-- **Reversal is a natural endomorphism of `runPresheaf`** — `Run.rev_restrict`. -/
def revRunPsh : runPresheaf ⟶ runPresheaf where
  app _ := TypeCat.ofHom Run.rev
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro r
    exact (Run.rev_restrict f.unop r).symm

/-! ## The complement of a run of a wedge

A run of `⋁d` is one run per bead (`runPshEquiv`), so reversing every bead at once is post-composing
its classifier with `revRunPsh`. -/

/-- **The complement of a run of a wedge**: reversed inside each bead.  On a bead cut into `k`
pieces it is the longest element of `Sₖ`, so it carries the merge to the greatest crossing. -/
noncomputable def Run.compl {d : List ℕ+} (r : Run (⋁d)) : Run (⋁d) :=
  runPshEquiv d ((runPshEquiv d).symm r ≫ revRunPsh)

/-- **The complement acts bead by bead** — `beadCell_comp`, since it is a post-composition. -/
theorem runProj_compl {d : List ℕ+} (r : Run (⋁d)) (i : Fin d.length) :
    runProj r.compl i = Run.rev (runProj r i) := by
  rw [runProj, runProj, Run.compl, Equiv.symm_apply_apply, CubeChain.beadCell_comp]
  rfl

/-- **The complement fixes exactly the runs of degree zero** — a bead it fixes is an edge, since
`Fin.revPerm` moves every order on two or more axes (`Run.rev_ne`). -/
theorem Run.compl_ne {d : List ℕ+} (r : Run (⋁d)) (hd : BPSet.degree d ≠ 0) : r.compl ≠ r := by
  intro h
  refine hd ((BPSet.degree_eq_zero_iff d).mpr fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  by_contra hne
  have hval : 2 ≤ ((d.get i : ℕ)) := by
    rcases Nat.lt_or_ge ((d.get i : ℕ)) 2 with hlt | hge
    · exact absurd (show d.get i = 1 by
        exact_mod_cast Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (d.get i).2) hne
    · exact hge
  exact Run.rev_ne (runProj r i) hval
    ((runProj_compl r i).symm.trans (congrArg (fun s => runProj s i) h))

end CubeChains
