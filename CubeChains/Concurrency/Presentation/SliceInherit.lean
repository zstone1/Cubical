import CubeChains.Concurrency.Presentation.SliceGerm
import CubeChains.Concurrency.Presentation.SlicePresentation

/-!
# Concurrency/Presentation/SliceInherit — the slice family, and what its cells are

`Ch(K)[W⁻¹]` is presented by the colimit of the germ slices (`presentsBr`), for every `K` and with
no hypothesis on `K`.  This file is the **cell dictionary** for that polygraph: a 0-cell of the
copy over `d` *is* a run over `d` (`runPtEquiv`), a 1-cell between two of them *is* a generator of
`p` making a germ step (`gen_action`), and a merge moves a 0-cell by pushing its run
(`famV_runPt`).

The `ᵒᵖ` is the orientation: a braid *raises* the weak order where an arrow of the localized slice
lowers it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

variable {d' d : Ch Zbp} {N : ℕ}

/-! ## The 0-cells are the runs -/

/-- The 0-cells of the slice polygraph over `d`: the runs over `d`, tagged with their strand
count.  The count is data rather than a proof, which is what makes a merge strictly functorial. -/
abbrev SliceV (d : Ch Zbp) : Type := Σ N : ℕ, RunAt d N

/-- The run a 0-cell names, as an object of the slice. -/
def sliceCellOver (a : SliceV d) : Over d := a.2.1.1

/-- The 0-cell map of a merge: it pushes the run and keeps the strand count. -/
def slicePushV (f : d' ⟶ d) (a : SliceV d') : SliceV d := ⟨a.1, RunAt.push f a.2⟩

@[simp] theorem sliceCellOver_push (f : d' ⟶ d) (a : SliceV d') :
    sliceCellOver (slicePushV f a) = (Over.map f).obj (sliceCellOver a) := rfl

/-- **A braid carries one run over `d` to another**: the germ step, read on runs.  `Ch Zbp[W⁻¹]`'s
partiality is exactly its failure. -/
abbrev RunGermStep {d : Ch Zbp} {N : ℕ} (β : PosBraid N) (u v : RunAt d N) : Prop :=
  CubeChains.GermStep β u.perm v.perm

/-- **A generator's germ step, prefixed** — the run at the halfway point, which the down-closure
of the runs supplies. -/
theorem runGermStep_prefix {β γ : PosBraid N} {u v : RunAt d N}
    (h : GermStep (β * γ) u.perm v.perm) :
    ∃ w : RunAt d N, GermStep β u.perm w.perm ∧ GermStep γ w.perm v.perm :=
  (runGermChart d N).exists_mid h

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **The 0-cell of the slice polygraph a run names.** -/
def runPt (u : RunAt d N) : (p.slicePoly d).V := ⟨N, u⟩

@[simp] theorem sliceCellOver_runPt (u : RunAt d N) : sliceCellOver (p.runPt u) = u.1.1 := rfl

/-- **Every 0-cell of the slice polygraph is a run's.** -/
theorem exists_runPt (a : (p.slicePoly d).V) : ∃ (N : ℕ) (u : RunAt d N), a = p.runPt u :=
  ⟨a.1, a.2, rfl⟩

/-- **Every 0-cell is a run's, at a known strand count.** -/
theorem exists_runPt_of_strands (hd : dimSum d.dims = N) (a : (p.slicePoly d).V) :
    ∃ u : RunAt d N, a = p.runPt u := by
  obtain ⟨M, u⟩ := a
  obtain rfl : M = N := (RunAt.strands u).symm.trans hd
  exact ⟨u, rfl⟩

/-- **The 0-cells of the slice polygraph *are* the runs over the chain.** -/
noncomputable def runPtEquiv (d : Ch Zbp) : RunAt d (dimSum d.dims) ≃ (p.slicePoly d).V :=
  Equiv.ofBijective p.runPt
    ⟨fun _ _ h => by obtain ⟨-, he⟩ := Sigma.mk.inj_iff.mp h; exact eq_of_heq he,
      fun a => (p.exists_runPt_of_strands rfl a).imp fun _ hu => hu.symm⟩

@[simp] theorem runPtEquiv_apply (u : RunAt d (dimSum d.dims)) :
    p.runPtEquiv d u = p.runPt u := rfl

/-- **A 0-cell is its run's** — `runPtEquiv` read as a cancellation. -/
theorem eq_runPt {a : (p.slicePoly d).V} {u : RunAt d N} (h : sliceCellOver a = u.1.1) :
    a = p.runPt u := by
  obtain ⟨w, rfl⟩ := p.exists_runPt_of_strands u.strands a
  exact congrArg p.runPt (Subtype.ext (Subtype.ext h))

/-- **Pushing a run's 0-cell pushes the run.** -/
@[simp] theorem slicePushV_runPt (f : d' ⟶ d) (u : RunAt d' N) :
    slicePushV f (p.runPt u) = p.runPt (RunAt.push f u) := rfl

/-! ## The 1-cells are the generators where they act -/

/-- **The germ 1-cell a generator acting on a run names**, in the chart of its own strand count. -/
def runGenFibre {u v : RunAt d N} (s : p.S N) (h : p.GermStep s u.perm v.perm) :
    (⟨u⟩ : GenObj (p.GermGen (runGermChart d N))) ⟶ ⟨v⟩ := ⟨s, h⟩

/-- **The 1-cell a generator acting on a run names.** -/
def runGen {u v : RunAt d N} (s : p.S N) (h : p.GermStep s u.perm v.perm) :
    (⟨p.runPt u⟩ : GenObj (p.slicePoly d).Gen) ⟶ ⟨p.runPt v⟩ :=
  Polygraph.CoproductGen.mk (p.runGenFibre s h)

theorem runGen_eq {u v : RunAt d N} (s : p.S N) (h : p.GermStep s u.perm v.perm) :
    p.runGen s h
      = (Polygraph.coproductPre (fun M => p.germPoly (runGermChart d M)) N).map
          (p.runGenFibre s h) := rfl

/-- **A 1-cell between two runs is a generator acting on the first** — `runGen`, on the nose.  The
two 0-cells are given as runs, so `CoproductGen`'s index reads the strand count off the cell and
there is no transport to carry: read a 1-cell between *unnamed* 0-cells by naming them first with
`exists_runPt`. -/
theorem gen_action {u v : RunAt d N}
    (g : (⟨p.runPt u⟩ : GenObj (p.slicePoly d).Gen) ⟶ ⟨p.runPt v⟩) :
    ∃ (s : p.S N) (h : p.GermStep s u.perm v.perm), g = p.runGen s h := by
  cases g with
  | @mk _ _ _ e => exact ⟨e.1, e.2, rfl⟩

/-! ## The family, and what it presents -/

/-- **The 0-cells name their own slice objects** — no transport is left. -/
theorem slicePresentation_at (d : Ch Zbp) (a : (p.slicePoly d).V) :
    (p.slicePresentation d).at' ⟨a⟩ = ((W Zbp).over (X := d)).Q.obj (sliceCellOver a) := rfl

/-- **A merge moves a 0-cell by pushing its run.** -/
theorem famV_eq (f : d' ⟶ d) (a : (p.slicePoly d').V) :
    ((p.fam.map f).pre.obj ⟨a⟩).as = slicePushV f a := rfl

/-- …so it moves a run's 0-cell to the pushed run's. -/
theorem famV_runPt (f : d' ⟶ d) (u : RunAt d' N) :
    ((p.fam.map f).pre.obj ⟨p.runPt u⟩).as = p.runPt (RunAt.push f u) := rfl

/-- **The slice presentations are compatible with the base**: a 0-cell names its own slice object,
and pushing it is `Over.map`.  The morphism half is `Subsingleton.elim` — `locOver_isThin` — which
is the only thinness the whole route spends. -/
theorem slicePoly_hP (f : d' ⟶ d) :
    (p.fam.map f).functor ⋙ (p.slicePresentation d).E
      = (p.slicePresentation d').E ⋙ overMapLoc (W Zbp) f :=
  CategoryTheory.Functor.ext (fun a => by
      obtain ⟨⟨a⟩⟩ := a
      change (p.slicePresentation d).at' ⟨slicePushV f a⟩
        = (overMapLoc (W Zbp) f).obj ((p.slicePresentation d').at' ⟨a⟩)
      rw [p.slicePresentation_at, p.slicePresentation_at, sliceCellOver_push]
      exact (overMapLoc_obj (W Zbp) f _).symm)
    fun _ _ _ => Subsingleton.elim _ _

/-- **The polygraph a braid presentation induces on `Ch(K)[W⁻¹]`** — one copy of `p`'s germ per
chain of `K`, assembled over the elements. -/
noncomputable def Br (K : BPSet) : Polygraph.{0, 0, 0} :=
  Limits.colimit (elementsPoly (wedgeHoms K) p.fam)

/-- **…and it presents `Ch(K)[W⁻¹]`**, with no side hypothesis. -/
noncomputable def presentsBr (K : BPSet) : Presents (p.Br K) ((W K).Localization) :=
  presentsChainsColimit K p.slicePresentation fun {_ _} f => p.slicePoly_hP f

end BraidPresentation

/-- **`Ch(K)[W⁻¹]` presented by the colimit of the germ-inherited slices**, for every `K`. -/
noncomputable def presentsChainsGarsideColimit (K : BPSet) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) germBP.fam)) ((W K).Localization) :=
  germBP.presentsBr K

/-- **…and by the Artin-inherited ones** — the same lemma at a different base presentation, and
the 1- and 2-cells of the colimit move with it. -/
noncomputable def presentsChainsArtinColimit (K : BPSet) :
    Presents (Limits.colimit (elementsPoly (wedgeHoms K) artinBP.fam)) ((W K).Localization) :=
  artinBP.presentsBr K

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
