import CubeChains.Concurrency.Presentation.GarsideCells

/-!
# Concurrency/Presentation/BrBaseCells — the 1-cells of `Br p Zbp`

`brZMap` sends a letter to its crossing above the run in the copy at the one-bead shape, and
`brZEquiv` alone says nothing: any two presentations of one category are equivalent.  The content
is whether the generating data biject, and on the 1-cells that is a fact about `p`.

For the **atoms** it holds: the chart `atomComp N k` an atom is crossed in carries a unique acting
run, so every copy an atom acts in is that chart pushed forward and the letter's own cell is the
only one.  For the **Garside simples** it fails (`straightLoopZ_ne_crossedLoopZ`): a mixing simple
is crossed only in the one-bead chart, and there the run below it is remembered.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Equiv

namespace ChainCat

/-! ## The 0-cells of a copy, at the terminal base

`Zbp` is terminal, so a copy has one chart and every 0-cell of it is the strand count's. -/

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **A 0-cell of any copy is the strand count's 0-cell.** -/
theorem ιV_eq_brZPt {c : ((wedgeHoms Zbp).Elements)ᵒᵖ} {N : ℕ}
    (hc : dimSum (eltBase (wedgeHoms Zbp) c).dims = N)
    (a : (p.slicePoly (eltBase (wedgeHoms Zbp) c)).V) :
    ιV Zbp p.fam c a = p.brZPt N :=
  (p.exists_ιRun Zbp c hc a).choose_spec.trans
    (congrArg (p.ιRun Zbp) (Subsingleton.elim _ _))

/-- **A 1-cell of `Br p Zbp` joins a strand count to itself** — its two 0-cells are runs over one
chart. -/
theorem eq_of_brZPt_hom {M N : ℕ} (e : p.brZPt M ⟶ p.brZPt N) : M = N := by
  obtain ⟨c, N', _, u, v, _, hA, hB, _⟩ := p.exists_runGen Zbp e
  exact (p.brZPt_injective ((p.ιV_eq_brZPt v.strands (p.runPt v)).symm.trans hA)).symm.trans
    (p.brZPt_injective ((p.ιV_eq_brZPt u.strands (p.runPt u)).symm.trans hB))

/-! ## Distinct letters, distinct cells

A letter's cell performs the letter's permutation (`chBraid_letterCell`), so the cells of two
letters differ as soon as the permutations do. -/

/-- **A letter's 1-cell remembers its permutation.** -/
theorem letterCell_injective (hp : p.BySimples) {N : ℕ}
    (hinj : Function.Injective fun s : p.S N => p.perm s) :
    Function.Injective (p.letterCell hp (N := N)) := by
  intro s s' h
  refine hinj ?_
  have hb : posPerm (p.perm s) = posPerm (p.perm s') :=
    (p.chBraid_letterCell hp s).symm.trans
      ((congrArg (fun t : p.brZPt N ⟶ p.brZPt N =>
          chBraid ((p.presentsBr Zbp).arrow t) (p.strands_ιRun N) (p.strands_ιRun N)) h).trans
        (p.chBraid_letterCell hp s'))
  have h' := congrArg (posPermHom N) hb
  rwa [posPermHom_posPerm, posPermHom_posPerm] at h'

/-- **A 1-cell of a copy is pinned by its letter and its two runs** — nothing else about the two
germ-step witnesses is seen. -/
theorem ιE_runGen_congr (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ) {N : ℕ}
    (s : p.S N) {u v u' v' : RunAt (eltBase (wedgeHoms K) c) N} (hu : u = u') (hv : v = v')
    (h : RunGermStep (p.braid s) u v)
    (h' : RunGermStep (p.braid s) u' v')
    {A B : GenObj (p.Br K).Gen}
    (hA : ιV K p.fam c (p.runPt v) = A) (hB : ιV K p.fam c (p.runPt u) = B)
    (hA' : ιV K p.fam c (p.runPt v') = A) (hB' : ιV K p.fam c (p.runPt u') = B) :
    Quiver.homOfEq (ιE K p.fam c (p.runGen s h)) hA hB
      = Quiver.homOfEq (ιE K p.fam c (p.runGen s h')) hA' hB' := by
  subst hu; subst hv; rfl

end BraidPresentation

/-! ## Every 1-cell of `Br artinBP K` is a codimension-one chain

`exists_runGen` puts a 1-cell in a single copy as an atom acting on a run; `exists_atomComp_leg`
says that copy is the atom's own chart pushed forward, and `ιE_runGen_eq` reads the cell there. -/

/-- **A 1-cell of `Br artinBP K` is a codimension-one chain of `K`**, read from its crossing leg to
its merge leg. -/
theorem exists_atomChainCell (K : BPSet) {A B : GenObj (artinBP.Br K).Gen} (e : A ⟶ B) :
    ∃ (N : ℕ) (k : Fin (N - 1)) (w : ⋁(atomComp N k) ⟶ K)
      (hA : artinBP.ιRun K ((atomOnes N k).φ ≫ w) = A)
      (hB : artinBP.ιRun K ((mergeOnes N k).φ ≫ w) = B),
      Quiver.homOfEq (atomChainCell K w) hA hB = e := by
  obtain ⟨c, N, k, u, v, hact, hA, hB, he⟩ := artinBP.exists_runGen K e
  obtain ⟨⟨⟨d⟩, W⟩⟩ := c
  obtain ⟨t, hatom, hmerge⟩ :
      ∃ t : zObj (atomComp N k) ⟶ d,
        RunAt.push t (atomRunAt k) = v ∧ RunAt.push t (mergeRunAt k) = u :=
    exists_atomComp_leg u.strands hact
  subst hatom
  subst hmerge
  refine ⟨N, k, t.φ ≫ W, ((ιV_pushLeg artinBP K W t (atomRunAt k)).trans
      (ιV_atomLeg k K (t.φ ≫ W))).symm.trans hA,
    ((ιV_pushLeg artinBP K W t (mergeRunAt k)).trans (ιV_mergeLeg k K (t.φ ≫ W))).symm.trans hB, ?_⟩
  exact (congrArg (fun g => Quiver.homOfEq g _ _) (ιE_runGen_eq K W t).symm).trans
    ((Quiver.homOfEq_trans _ _ _ _ _).trans he)

/-! ## The atom's chart merges into the one bead

`atomTopMerge` is the leg that carries the atom's copy onto the copy a letter's cell lives in; it
crosses nothing, so it takes the merge leg to the uncrossed run and the crossing leg to the atom. -/

section AtomTop

variable {N : ℕ} (k : Fin (N - 1))

/-- The merge of the atom's chart into the one bead. -/
noncomputable def atomTopMerge : zObj (atomComp N k) ⟶ zObj (topDims N) :=
  (exists_crossPerm_eq_one (dimSum_atomComp N k)
    (nonempty_hom_top (atomComp N k) (dimSum_atomComp N k))).choose

@[simp] theorem crossPerm_atomTopMerge :
    crossPerm (dimSum_atomComp N k) (atomTopMerge k) = 1 :=
  (exists_crossPerm_eq_one (dimSum_atomComp N k)
    (nonempty_hom_top (atomComp N k) (dimSum_atomComp N k))).choose_spec

theorem push_atomTopMerge_mergeRunAt :
    RunAt.push (atomTopMerge k) (mergeRunAt k) = topRunAt N 1 := by
  rw [mergeRunAt, RunAt.push_push, topRunAt]
  refine congrArg (fun f => RunAt.push f (runAtSelf N)) (hom_ext_of_crossPerm
    (h := dimSum_replicate N) ?_)
  rw [crossPerm_comp, crossPerm_onesTopEquiv_symm, crossPerm_atomTopMerge,
    crossPerm_eq_one_of_W _ (W_mergeOnes N k), one_mul]

theorem push_atomTopMerge_atomRunAt :
    RunAt.push (atomTopMerge k) (atomRunAt k) = topRunAt N (adjT k) := by
  rw [atomRunAt, RunAt.push_push, topRunAt]
  refine congrArg (fun f => RunAt.push f (runAtSelf N)) (hom_ext_of_crossPerm
    (h := dimSum_replicate N) ?_)
  rw [crossPerm_comp, crossPerm_onesTopEquiv_symm, crossPerm_atomTopMerge, crossPerm_atomOnes,
    one_mul]

end AtomTop

/-! ## An atom's codimension-one chain of `Zbp` is its letter's cell

Both are one crossing of the copy at `atomComp N k`; the letter's is that copy pushed along
`atomTopMerge`, and at the terminal base the chart carries no further data. -/

theorem atomChainCell_eq_letterCell {N : ℕ} (k : Fin (N - 1)) (w : ⋁(atomComp N k) ⟶ Zbp)
    (hA : artinBP.ιRun Zbp ((atomOnes N k).φ ≫ w) = artinBP.brZPt N)
    (hB : artinBP.ιRun Zbp ((mergeOnes N k).φ ≫ w) = artinBP.brZPt N) :
    Quiver.homOfEq (atomChainCell Zbp w) hA hB
      = artinBP.letterCell artinBP_bySimples k := by
  obtain rfl : w = (atomTopMerge k).φ ≫ (zObj (topDims N)).map := Subsingleton.elim _ _
  have hv : RunAt.push (atomTopMerge k) (atomRunAt k)
      = topRunAt N (artinBP.perm k) :=
    (push_atomTopMerge_atomRunAt k).trans
      (congrArg (topRunAt N) (artinBP_perm k).symm)
  refine Eq.trans ((congrArg (fun g => Quiver.homOfEq g hA hB)
      (ιE_runGen_eq Zbp (zObj (topDims N)).map (atomTopMerge k)).symm).trans
    (Quiver.homOfEq_trans _ _ _ _ _)) ?_
  exact artinBP.ιE_runGen_congr Zbp (op ⟨op (zObj (topDims N)), (zObj (topDims N)).map⟩) k
    (push_atomTopMerge_mergeRunAt k) hv
    (germStep_push (atomTopMerge k) (action_atomRunAt k))
    (artinBP.action_topRunAt artinBP_bySimples k) _ _
    (artinBP.ιV_topLeg (artinBP.perm k)) (artinBP.ιV_topLeg 1)

/-! ## `Br artinBP Zbp` *is* the Artin polygraph

The 0-cells are the strand counts (`bijective_brZPt`, any `p`); the 1-cells at a strand count are
its atoms, so `brZMap` is an isomorphism of generating data and not merely a comparison. -/

/-- **Every 1-cell of `Br artinBP Zbp` is an atom's letter cell.** -/
theorem exists_letterCell {A B : GenObj (artinBP.Br Zbp).Gen} (e : A ⟶ B) :
    ∃ (N : ℕ) (k : Fin (N - 1)) (hA : artinBP.brZPt N = A) (hB : artinBP.brZPt N = B),
      Quiver.homOfEq (artinBP.letterCell artinBP_bySimples k) hA hB = e := by
  obtain ⟨N, k, w, hA, hB, he⟩ := exists_atomChainCell Zbp e
  refine ⟨N, k, ?_, ?_, ?_⟩
  · exact (congrArg (artinBP.ιRun Zbp) (Subsingleton.elim _ _)).trans hA
  · exact (congrArg (artinBP.ιRun Zbp) (Subsingleton.elim _ _)).trans hB
  · rw [← he, ← atomChainCell_eq_letterCell k w
      (congrArg (artinBP.ιRun Zbp) (Subsingleton.elim _ _)).symm
      (congrArg (artinBP.ιRun Zbp) (Subsingleton.elim _ _)).symm]
    exact Quiver.homOfEq_trans _ _ _ _ _

/-- **The letters at a strand count are the 1-cells there.** -/
theorem bijective_letterCell (N : ℕ) :
    Function.Bijective (artinBP.letterCell artinBP_bySimples (N := N)) := by
  refine ⟨artinBP.letterCell_injective artinBP_bySimples fun s s' h => ?_, fun e => ?_⟩
  · exact Fin.ext (adjT_inj ((artinBP_perm s).symm.trans (h.trans (artinBP_perm s'))))
  · obtain ⟨M, k, hA, hB, he⟩ := exists_letterCell e
    obtain rfl : M = N := artinBP.brZPt_injective hA
    exact ⟨k, he⟩

/-- **`brZMap` matches the Artin polygraph with `Br artinBP Zbp` generator for generator**: the
0-cells are the strand counts (`bijective_brZPt`) and the 1-cells at one are its atoms.  So the
comparison is an isomorphism of generating data, which `brZEquiv` alone does not say. -/
theorem bijective_brZGen (x y : GenObj (artinBP.poly.op).Gen) :
    Function.Bijective (artinBP.brZGen artinBP_bySimples (x := x) (y := y)) := by
  obtain ⟨M⟩ := x
  obtain ⟨N⟩ := y
  by_cases hMN : N = M
  · subst hMN
    refine ⟨fun e e' h => ?_, fun t => ?_⟩
    · cases e with
      | mk s => cases e' with
        | mk s' => exact congrArg Polygraph.StrandGen.mk ((bijective_letterCell N).1 h)
    · obtain ⟨k, hk⟩ := (bijective_letterCell N).2 t
      exact ⟨Polygraph.StrandGen.mk k, hk⟩
  · exact ⟨fun e _ _ => absurd (show N = M from Polygraph.StrandGen.index_eq e) hMN,
      fun t => absurd (show N = M from (artinBP.eq_of_brZPt_hom t).symm) hMN⟩

/-! ## …and the Garside letters do not

A letter's 1-cell is crossed above the *uncrossed* run, so `sepCells` reads `1` off it; a mixing
simple crossed above a longer run is a 1-cell `sepCells` reads that run off
(`straightLoopZ_ne_crossedLoopZ`), and no letter names it. -/

/-- **A letter's 1-cell remembers nothing** — it is crossed above the uncrossed run. -/
theorem sepCells_letterCell (p : BraidPresentation) (hp : p.BySimples) {n N : ℕ}
    {σ : Equiv.Perm (Fin n)} (hmix : Mixes σ) (s : p.S N) :
    (sepCells Zbp p σ hmix).map (p.letterCell hp s) = some 1
      ∨ (sepCells Zbp p σ hmix).map (p.letterCell hp s) = none := by
  rw [BraidPresentation.letterCell, map_homOfEq_const, sepCells_ιE, sepVal]
  split_ifs with hc hcase
  · obtain rfl : N = n := (dimSum_topDims N).symm.trans hc
    exact Or.inl (congrArg some
      ((crossOver_sliceCellOver_runPt p hc (topRunAt N 1)).trans (perm_topRunAt N 1)))
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- **A mixing simple's cell above a crossed run is no letter's** — `crossedLoopZ` remembers
`swap3`. -/
theorem not_surjective_brZGen_germBP :
    ¬ Function.Surjective (germBP.brZGen germBP_bySimples (x := ⟨(3 : ℕ)⟩) (y := ⟨(3 : ℕ)⟩)) := by
  intro hsurj
  obtain ⟨e, he⟩ := hsurj crossedLoopZ
  have hsep : (sepCells Zbp germBP rot3 mixes_rot3).map crossedLoopZ = some swap3 := by
    rw [crossedLoopZ, map_homOfEq_const, sepCells_germTopRaw]
  cases e with
  | mk s =>
    rcases sepCells_letterCell germBP germBP_bySimples mixes_rot3 s with h | h <;>
      rw [show germBP.letterCell germBP_bySimples s = crossedLoopZ from he,
        hsep] at h
    · exact swap3_ne_one (Option.some_injective _ h)
    · exact absurd h (Option.some_ne_none _)

end ChainCat
