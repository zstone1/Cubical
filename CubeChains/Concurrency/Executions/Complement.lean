import CubeChains.Precubical.Chains.Reversal
import CubeChains.Concurrency.Executions.Runs

/-!
# Concurrency/Executions/Complement — the complementary run

A chain of `K` is refined by a run bead by bead (`Lines K`), and each bead's run can be **reversed**
(`Box.rev`).  Doing that in every bead at once is the **complement**: the same chain, the run run
backwards inside it.

    X.chain ──run──▸ b          complement         X'.chain ──run──▸ b

It is an involution (`complLine_complLine`), and on a bead cut into `k` pieces it acts by the
longest element of `Sₖ` — so it carries the merge out of a run (crossing nothing) to the greatest
crossing onto the same chain.  Nothing is chosen: reversal is a bijection.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

/-! ## Reversing a run of a cube -/

/-- A run of a cube, run backwards. -/
def Run.rev {m : ℕ} (r : Run (□m)) : Run (□m) :=
  (Run.equivEdgeChain (□m)).symm (EdgeChain.rev (Run.equivEdgeChain (□m) r))

@[simp] theorem Run.rev_rev {m : ℕ} (r : Run (□m)) : r.rev.rev = r := by
  rw [Run.rev, Run.rev, Equiv.apply_symm_apply, EdgeChain.rev_rev, Equiv.symm_apply_apply]

theorem runPresheaf_map_apply {X Y : Boxᵒᵖ} (f : X ⟶ Y) (r : Run (□X.unop.dim)) :
    runPresheaf.map f r
      = (Run.equivEdgeChain _).symm
          (EdgeChain.restrict f.unop (Run.equivEdgeChain _ r)) := rfl

/-- **Reversal is a natural endomorphism of `runPresheaf`** — the all-edges case of
`revChainPsh`. -/
def revRunPsh : runPresheaf ⟶ runPresheaf where
  app _ := TypeCat.ofHom Run.rev
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro r
    change Run.rev (runPresheaf.map f r) = runPresheaf.map f (Run.rev r)
    rw [runPresheaf_map_apply, runPresheaf_map_apply, Run.rev, Run.rev,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, EdgeChain.restrict_rev]

@[simp] theorem revRunPsh_app_apply (X : Boxᵒᵖ) (r : Run (□X.unop.dim)) :
    revRunPsh.app X r = r.rev := rfl

/-- **Reversal is an involution of `runPresheaf`.** -/
@[simp] theorem revRunPsh_revRunPsh : revRunPsh ≫ revRunPsh = 𝟙 runPresheaf := by
  apply NatTrans.ext_apply
  intro X r
  exact Run.rev_rev r

/-! ## The complement of a run of a wedge

A run of `⋁d` is one run per bead (`runPshEquiv`), so reversing every bead at once is post-composing
its classifier with `revRunPsh`. -/

/-- **The complement of a run of a wedge**: reversed inside each bead.  On a bead cut into `k`
pieces it is the longest element of `Sₖ`, so it carries the merge to the greatest crossing. -/
noncomputable def Run.compl {d : List ℕ+} (r : Run (⋁d)) : Run (⋁d) :=
  runOfPsh d (pshOfRun d r ≫ revRunPsh)

/-- **The complement is an involution** — `revRunPsh` is one. -/
@[simp] theorem Run.compl_compl {d : List ℕ+} (r : Run (⋁d)) : r.compl.compl = r := by
  rw [Run.compl, Run.compl, pshOfRun_runOfPsh, Category.assoc, revRunPsh_revRunPsh,
    Category.comp_id, runOfPsh_pshOfRun]

/-- **The complement acts bead by bead** — `beadCell_comp`, since it is a post-composition. -/
theorem runProj_compl {d : List ℕ+} (r : Run (⋁d)) (i : Fin d.length) :
    runProj r.compl i = Run.rev (runProj r i) := by
  rw [runProj, runProj, Run.compl, pshOfRun_runOfPsh, CubeChain.beadCell_comp]
  rfl

/-! ## Which runs the complement fixes

Only the ones with nothing to reverse.  A run of `□m` has `m` cubes, and a chain fixed by reversal
has at most one (`length_le_one_of_revCubeChain_eq`), so a fixed bead is an edge. -/

/-- **A run of a cube of dimension at least two is moved by reversal.** -/
theorem Run.rev_ne {m : ℕ} (ρ : Run (□m)) (hm : 2 ≤ m) : Run.rev ρ ≠ ρ := by
  intro h
  have h1 : EdgeChain.rev (Run.equivEdgeChain (□m) ρ) = Run.equivEdgeChain (□m) ρ := by
    have hc := congrArg (Run.equivEdgeChain (□m)) h
    rwa [Run.rev, Equiv.apply_symm_apply] at hc
  have hlen : (Run.equivEdgeChain (□m) ρ).1.cubes.length = m := by
    rw [show (Run.equivEdgeChain (□m) ρ).1.cubes.length
        = (Run.equivEdgeChain (□m) ρ).1.dims.length from (List.length_map _).symm,
      dims_equivEdgeChain, ← dimSum_eq_length_of_ones ρ.ones]
    exact wedgeDimSum_eq ρ.chain.map
  exact absurd (hlen ▸ length_le_one_of_revCubeChain_eq (congrArg Subtype.val h1)) (by omega)

/-- **The complement fixes exactly the runs of degree zero** — a bead it fixes is an edge. -/
theorem Run.compl_ne {d : List ℕ+} (r : Run (⋁d)) (hd : BPSet.degree d ≠ 0) : r.compl ≠ r := by
  intro h
  refine hd ((BPSet.degree_eq_zero_iff d).mpr fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  by_contra hne
  have hpos := (d.get i).2
  have hval : 2 ≤ ((d.get i : ℕ)) := by
    rcases Nat.lt_or_ge ((d.get i : ℕ)) 2 with hlt | hge
    · exact absurd (show d.get i = 1 by
        exact_mod_cast Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (d.get i).2) hne
    · exact hge
  exact Run.rev_ne (runProj r i) hval
    ((runProj_compl r i).symm.trans (congrArg (fun s => runProj s i) h))

end CubeChains
