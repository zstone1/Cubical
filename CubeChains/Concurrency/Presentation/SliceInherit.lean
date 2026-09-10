import CubeChains.Concurrency.Presentation.SliceGerm

/-!
# Concurrency/Presentation/SliceInherit — the slice family, and what its cells are

The **cell dictionary** of the slice family: a 0-cell of the copy over `d` *is* a run over `d`
(`runPtEquiv`), a 1-cell between two of them *is* a generator of `p` making a germ step
(`gen_action`), and a merge moves a 0-cell by pushing its run (`famV_runPt`).  All of it is the
coproduct's own disjointness: `runObjEquiv` on the 0-cells, star-bijectivity of a leg on the
1-cells, and `sliceIncl_push` on the merges.  `slicePoly_hP` is what the colimit route consumes.

The `ᵒᵖ` is the orientation: a braid *raises* the weak order where an arrow of the localized slice
lowers it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d' d : Ch Zbp} {N : ℕ}

/-! ## The 0-cells are the runs -/

/-- The runs over `d`, tagged with their strand count — what the slice polygraph's 0-cells are
(`runObjEquiv`).  The count is data rather than a proof, so a merge keeps it on the nose. -/
abbrev SliceV (d : Ch Zbp) : Type := Σ N : ℕ, RunAt d N

/-- **A braid carries one run over `d` to another**: the germ step, read on runs.  `Ch Zbp[W⁻¹]`'s
partiality is exactly its failure. -/
abbrev RunGermStep {d : Ch Zbp} {N : ℕ} (β : PosBraid N) (u v : RunAt d N) : Prop :=
  CubeChains.GermStep β u.perm v.perm

/-- **A generator's germ step, prefixed** — the run at the halfway point, which the down-closure
of the runs supplies. -/
theorem runGermStep_prefix {β γ : PosBraid N} {u v : RunAt d N}
    (h : GermStep (β * γ) u.perm v.perm) :
    ∃ w : RunAt d N, GermStep β u.perm w.perm ∧ GermStep γ w.perm v.perm :=
  (runDownset d N).exists_mid h

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **The 0-cell of the slice polygraph a run names** — the leg of its own strand count. -/
noncomputable def runPt (u : RunAt d N) : (p.slicePoly d).V := ((p.slicePre d N).obj ⟨u⟩).as

/-- **The 0-cells of the slice polygraph *are* the runs, tagged with the strand count** — the legs
of a coproduct are jointly surjective and disjoint. -/
noncomputable def runObjEquiv (d : Ch Zbp) : SliceV d ≃ GenObj (p.slicePoly d).Gen :=
  (Equiv.sigmaCongrRight fun N => genObjEquiv (p.GermGen (runDownset d N))).trans
    (Polygraph.coprodObjEquiv fun N => p.germPoly (runDownset d N))

@[simp] theorem runObjEquiv_apply (u : RunAt d N) :
    p.runObjEquiv d ⟨N, u⟩ = ⟨p.runPt u⟩ := rfl

/-- The run a 0-cell names, as an object of the slice. -/
noncomputable def sliceCellOver (a : (p.slicePoly d).V) : Over d :=
  ((p.runObjEquiv d).symm ⟨a⟩).2.1.1

@[simp] theorem sliceCellOver_runPt (u : RunAt d N) : p.sliceCellOver (p.runPt u) = u.1.1 :=
  congrArg (fun t : SliceV d => t.2.1.1) ((p.runObjEquiv d).symm_apply_apply ⟨N, u⟩)

/-- **Every 0-cell of the slice polygraph is a run's.** -/
theorem exists_runPt (a : (p.slicePoly d).V) : ∃ (N : ℕ) (u : RunAt d N), a = p.runPt u := by
  obtain ⟨⟨N, u⟩, hu⟩ := (p.runObjEquiv d).surjective (⟨a⟩ : GenObj (p.slicePoly d).Gen)
  exact ⟨N, u, (congrArg GenObj.as hu).symm⟩

/-- **Every 0-cell is a run's, at a known strand count.** -/
theorem exists_runPt_of_strands (hd : dimSum d.dims = N) (a : (p.slicePoly d).V) :
    ∃ u : RunAt d N, a = p.runPt u := by
  obtain ⟨M, u, rfl⟩ := p.exists_runPt a
  obtain rfl : M = N := (RunAt.strands u).symm.trans hd
  exact ⟨u, rfl⟩

theorem runPt_injective : Function.Injective (p.runPt (d := d) (N := N)) := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj_iff.mp ((p.runObjEquiv d).injective (congrArg GenObj.mk h))).2

/-- **The 0-cells of the slice polygraph *are* the runs over the chain.** -/
noncomputable def runPtEquiv (d : Ch Zbp) : RunAt d (dimSum d.dims) ≃ (p.slicePoly d).V :=
  Equiv.ofBijective p.runPt
    ⟨p.runPt_injective, fun a => (p.exists_runPt_of_strands rfl a).imp fun _ hu => hu.symm⟩

@[simp] theorem runPtEquiv_apply (u : RunAt d (dimSum d.dims)) :
    p.runPtEquiv d u = p.runPt u := rfl

/-- **A 0-cell is its run's** — `runPtEquiv` read as a cancellation. -/
theorem eq_runPt {a : (p.slicePoly d).V} {u : RunAt d N} (h : p.sliceCellOver a = u.1.1) :
    a = p.runPt u := by
  obtain ⟨w, rfl⟩ := p.exists_runPt_of_strands u.strands a
  rw [p.sliceCellOver_runPt] at h
  exact congrArg p.runPt (Subtype.ext (Subtype.ext h))

/-! ## The 1-cells are the generators where they act -/

/-- **The germ 1-cell a generator acting on a run names**, at its own strand count. -/
def runGenFibre {u v : RunAt d N} (s : p.S N) (h : p.GermStep s u.perm v.perm) :
    (⟨u⟩ : GenObj (p.GermGen (runDownset d N))) ⟶ ⟨v⟩ := ⟨s, h⟩

/-- **The 1-cell a generator acting on a run names.** -/
noncomputable def runGen {u v : RunAt d N} (s : p.S N) (h : p.GermStep s u.perm v.perm) :
    (⟨p.runPt u⟩ : GenObj (p.slicePoly d).Gen) ⟶ ⟨p.runPt v⟩ :=
  (p.slicePre d N).map (p.runGenFibre s h)

/-- **A 1-cell between two runs is a generator acting on the first** — a leg of a coproduct is
star-bijective, so the strand count is read off the 0-cells and no transport is carried: read a
1-cell between *unnamed* 0-cells by naming them first with `exists_runPt`. -/
theorem gen_action {u v : RunAt d N}
    (g : (⟨p.runPt u⟩ : GenObj (p.slicePoly d).Gen) ⟶ ⟨p.runPt v⟩) :
    ∃ (s : p.S N) (h : p.GermStep s u.perm v.perm), g = p.runGen s h := by
  obtain ⟨⟨w, e⟩, he⟩ := Polygraph.coprod_star_surjective
    (fun M => p.germPoly (runDownset d M)) N ⟨u⟩ ⟨⟨p.runPt v⟩, g⟩
  obtain ⟨hw, hg⟩ := Sigma.mk.inj_iff.mp he
  obtain rfl : w = ⟨v⟩ :=
    Polygraph.coprod_pre_obj_injective (fun M => p.germPoly (runDownset d M)) N hw
  exact ⟨e.1, e.2, (eq_of_heq hg).symm⟩

/-! ## The family, and what it presents -/

/-- **The 0-cells name their own slice objects.** -/
theorem slicePresentation_at (d : Ch Zbp) (a : (p.slicePoly d).V) :
    (p.slicePresentation d).at' ⟨a⟩ = ((W Zbp).over (X := d)).Q.obj (p.sliceCellOver a) := rfl

/-- The 0-cell map of a merge: it pushes the run and keeps the strand count. -/
noncomputable def slicePushV (f : d' ⟶ d) (a : (p.slicePoly d').V) : (p.slicePoly d).V :=
  ((p.fam.map f).pre.obj ⟨a⟩).as

/-- **A merge moves a 0-cell by pushing its run.** -/
theorem famV_eq (f : d' ⟶ d) (a : (p.slicePoly d').V) :
    ((p.fam.map f).pre.obj ⟨a⟩).as = p.slicePushV f a := rfl

/-- …so it moves a run's 0-cell to the pushed run's. -/
theorem famV_runPt (f : d' ⟶ d) (u : RunAt d' N) :
    ((p.fam.map f).pre.obj ⟨p.runPt u⟩).as = p.runPt (RunAt.push f u) :=
  congrArg (fun m : p.germPoly (runDownset d' N) ⟶ p.slicePoly d => (m.pre.obj ⟨u⟩).as)
    (p.sliceIncl_push f N)

/-- **Pushing a run's 0-cell pushes the run.** -/
@[simp] theorem slicePushV_runPt (f : d' ⟶ d) (u : RunAt d' N) :
    p.slicePushV f (p.runPt u) = p.runPt (RunAt.push f u) := p.famV_runPt f u

/-- **Pushing a copy along a merge pushes its generator**, run and all — the leg factors through
the down-set push, and the down-set push moves only the run. -/
theorem fam_map_runGen (f : d' ⟶ d) {u v : RunAt d' N} (s : p.S N)
    (h : p.GermStep s u.perm v.perm) :
    Quiver.homOfEq ((p.fam.map f).pre.map (p.runGen s h))
        (congrArg GenObj.mk (p.famV_runPt f v)) (congrArg GenObj.mk (p.famV_runPt f u))
      = p.runGen s (germStep_push f h) :=
  eq_of_heq ((Quiver.homOfEq_heq _ _ _).trans
    (Prefunctor.map_heq_of_eq (congrArg Polygraph.Hom.pre (p.sliceIncl_push f N))
      (p.runGenFibre s h)))

@[simp] theorem sliceCellOver_push (f : d' ⟶ d) (a : (p.slicePoly d').V) :
    p.sliceCellOver (p.slicePushV f a) = (Over.map f).obj (p.sliceCellOver a) := by
  obtain ⟨N, u, rfl⟩ := p.exists_runPt a
  rw [p.slicePushV_runPt, p.sliceCellOver_runPt, p.sliceCellOver_runPt]
  rfl

/-- **The slice presentations are compatible with the base**: a 0-cell names its own slice object,
and pushing it is `Over.map`.  Only the naming is asked — `hP_of_naming`, on `locOver_isThin`,
which is the only thinness the whole route spends. -/
theorem slicePoly_hP (f : d' ⟶ d) :
    (p.fam.map f).functor ⋙ (p.slicePresentation d).E
      = (p.slicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  hP_of_naming (W Zbp) p.slicePresentation (fun {d' d} f a => by
    obtain ⟨⟨a⟩⟩ := a
    change (p.slicePresentation d).at' ⟨p.slicePushV f a⟩
      = (overMapLoc (W Zbp) f).obj ((p.slicePresentation d').at' ⟨a⟩)
    rw [p.slicePresentation_at, p.slicePresentation_at, p.sliceCellOver_push]
    exact (overMapLoc_obj (W Zbp) f _).symm) f

end BraidPresentation

/-! ### What a generator does to a run

A generator acts by *length-additive* right multiplication of the crossing permutation, so the step
it makes is read off its own braid: a germ generator is a simple (`germBP_braid`) and crosses it, an
Artin generator is an atom (`artinBP_braid`) and crosses one pair. -/

/-- **A simple is crossed above a run exactly when the lengths add.** -/
theorem runGermStep_posPerm_iff (σ : Perm (Fin N)) (u v : RunAt d N) :
    GermStep (posPerm σ) u.perm v.perm ↔
      v.perm = u.perm * σ ∧ permLen u.perm + permLen σ = permLen v.perm :=
  germStep_posPerm_iff σ u.perm v.perm

/-- …and an atom is crossed by one pair — codimension one, on the nose. -/
theorem runGermStep_adjT_iff (k : Fin (N - 1)) (u v : RunAt d N) :
    GermStep (posPerm (adjT k)) u.perm v.perm ↔
      v.perm = u.perm * adjT k ∧ permLen u.perm + 1 = permLen v.perm :=
  germStep_adjT_iff k u.perm v.perm

end ChainCat
