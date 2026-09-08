import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.RouteComparison
import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Concurrency.Presentation.LiftPresentation

/-!
# Concurrency/Presentation/BrBase — `p`'s own polygraph, mapped into `Br p Zbp`

Plugging the base back in changes nothing: a 0-cell of `Br p Zbp` is a strand count and every
letter names a 1-cell there, so `p`'s coproduct of monoid polygraphs maps into it generator by
generator.  Whether the letters *exhaust* the 1-cells is a fact about `p` (`BrBaseCells`).

The `ᵒᵖ` is unavoidable — `p.poly` presents the localized base and `Br p Zbp` presents its opposite
— and so is `BySimples`: the braid monoid acts on the runs by *length-additive* multiplication, so
a letter longer than its permutation acts nowhere and names no 1-cell.
-/

universe v u w

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Localization

/-! ## The projection of a pointwise-singleton category of elements -/

namespace CategoryTheory.CategoryOfElements

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

instance full_π [∀ c, Subsingleton (F.obj c)] : (CategoryOfElements.π F).Full where
  map_surjective f := ⟨⟨f, Subsingleton.elim _ _⟩, rfl⟩

instance essSurj_π [∀ c, Nonempty (F.obj c)] : (CategoryOfElements.π F).EssSurj where
  mem_essImage c := ⟨⟨c, Classical.arbitrary _⟩, ⟨Iso.refl _⟩⟩

end CategoryTheory.CategoryOfElements

namespace ChainCat

/-! ## `Ch Zbp[W⁻¹]` is its own base

`Zbp` is terminal, so the fibre of `wedgeHoms Zbp` over every chain is a point and the projection
`chLocBase Zbp` — which for a general `K` is only faithful — is an equivalence. -/

theorem isSegal_Zbp : IsSegal Zbp.toPsh := isSegal_Z

instance (a : (Ch Zbp)ᵒᵖ) : Unique ((wedgeHoms Zbp).obj a) := uniqueToZbp _

instance subsingletonWedgeHomsDescend (c : ((W Zbp).op).Localization) :
    Subsingleton ((wedgeHomsDescend Zbp isSegal_Zbp).obj c) := by
  obtain ⟨X, rfl⟩ : ∃ X, ((W Zbp).op).Q.obj X = c :=
    ⟨_, (Localization.Construction.objEquiv ((W Zbp).op)).right_inv c⟩
  rw [show X = op X.unop from rfl, wedgeHomsDescend_obj_Q]
  infer_instance

instance nonemptyWedgeHomsDescend (c : ((W Zbp).op).Localization) :
    Nonempty ((wedgeHomsDescend Zbp isSegal_Zbp).obj c) := by
  obtain ⟨X, rfl⟩ : ∃ X, ((W Zbp).op).Q.obj X = c :=
    ⟨_, (Localization.Construction.objEquiv ((W Zbp).op)).right_inv c⟩
  rw [show X = op X.unop from rfl, wedgeHomsDescend_obj_Q]
  infer_instance

instance : (CategoryOfElements.π (wedgeHomsDescend Zbp isSegal_Zbp)).IsEquivalence := { }

instance isEquivalence_chLocBase_Zbp : (chLocBase Zbp).IsEquivalence :=
  haveI : (chDescent Zbp isSegal_Zbp).IsLocalization (W Zbp) := isLocalization_chDescent _ _
  haveI : (chLocBaseModel Zbp isSegal_Zbp).IsEquivalence :=
    inferInstanceAs (((Localization.equivalenceFromModel
      (chDescent Zbp isSegal_Zbp) (W Zbp)).functor) ⋙
        (CategoryOfElements.π (wedgeHomsDescend Zbp isSegal_Zbp)).op).IsEquivalence
  Functor.isEquivalence_of_iso (chLocBaseModelIso Zbp isSegal_Zbp).symm

/-- **`Ch(Z)[W⁻¹]` and the localized base are one category**, read across the variance. -/
noncomputable def zLocOpEquiv : (W Zbp).Localization ≌ (((W Zbp).op).Localization)ᵒᵖ :=
  (chLocBase Zbp).asEquivalence

/-! ## The one-bead copy

Every simple is crossed once, above the run, in the copy at the one-bead shape `topDims N`, where
every permutation is a run (`onesTopEquiv`).  That copy is the witness a letter's 1-cell needs. -/

/-- The unique map of the run into the terminal `Zbp`. -/
def zRun (n : ℕ) : ⋁(𝟙^n) ⟶ Zbp := isTerminalZbp.from _

/-- The run over the one-bead shape whose crossing permutation is `σ`. -/
noncomputable def topRunAt (N : ℕ) (σ : Equiv.Perm (Fin N)) : RunAt (zObj (topDims N)) N :=
  RunAt.push ((onesTopEquiv N).symm σ) (runAtSelf N)

@[simp] theorem perm_topRunAt (N : ℕ) (σ : Equiv.Perm (Fin N)) : (topRunAt N σ).perm = σ := by
  rw [topRunAt, RunAt.push_perm _ (dimSum_replicate N), perm_runAtSelf, mul_one,
    crossPerm_onesTopEquiv_symm]

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **A simple letter is crossed at the run** — length-additivity is free above the identity. -/
theorem action_topRunAt (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    RunGermStep (p.braid s) (topRunAt N 1) (topRunAt N (p.perm s)) := by
  refine ⟨hp N s, ?_, ?_⟩
  · rw [perm_topRunAt, perm_topRunAt, one_mul]; rfl
  · rw [perm_topRunAt, perm_topRunAt, permLen_one, Nat.zero_add]; rfl

/-- **The one-bead copy's 0-cells are all the run's** — `Zbp` is terminal, so the leg down to the
run's own copy lands on the same 0-cell whatever the crossing was. -/
theorem ιV_topLeg {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ιV Zbp p.fam ((toElements Zbp).obj (zObj (topDims N))) (p.runPt (topRunAt N σ))
      = p.ιRun Zbp (zRun N) :=
  ((congrArg (ιV Zbp p.fam ((toElements Zbp).obj (zObj (topDims N))))
        (p.famV_runPt ((onesTopEquiv N).symm σ) (runAtSelf N)).symm).trans
      (ιV_leg Zbp p.fam (eltLeg Zbp ((onesTopEquiv N).symm σ) ((zObj (topDims N)).map))
        (p.runPt (runAtSelf N)))).trans
    (congrArg (p.ιRun Zbp) (Subsingleton.elim _ _))

/-- **The 1-cell a letter names**: its permutation, crossed once above the run, in the copy at the
one-bead shape.  The slice polygraph is the base's reversed, so the letter runs run-to-crossing and
the cell runs crossing-to-run. -/
noncomputable def letterCell (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    p.ιRun Zbp (zRun N) ⟶ p.ιRun Zbp (zRun N) :=
  Quiver.homOfEq
    (ιE Zbp p.fam ((toElements Zbp).obj (zObj (topDims N)))
        (a := p.runPt (topRunAt N (p.perm s))) (b := p.runPt (topRunAt N 1))
        (p.runGen s (p.action_topRunAt hp s)))
    (p.ιV_topLeg (p.perm s)) (p.ιV_topLeg 1)

/-! ## The dictionary

A 0-cell of `Br p Zbp` is a strand count, a 1-cell is a letter there, and both name what `p`'s own
polygraph names.  `chLocBase Zbp` is the comparison of the two variances, and it is an equivalence,
so the braid an arrow performs decides equality on both sides. -/

/-- The strand count of a run's 0-cell. -/
theorem strands_ιRun (N : ℕ) :
    dimSum (chOf ((p.presentsBr Zbp).at' (p.ιRun Zbp (zRun N)))).dims = N :=
  (strandsEq_loc ((chLocBase Zbp).mapIso (p.ιRunIso Zbp (zRun N))).hom.unop).trans
    (dimSum_replicate N)

/-- The 0-cell of `Br p Zbp` at strand count `N`. -/
noncomputable def brZPt (N : ℕ) : GenObj (p.Br Zbp).Gen := p.ιRun Zbp (zRun N)

/-- **The 0-cell dictionary**: a strand count names the run's own 0-cell. -/
noncomputable def brZOb (x : GenObj (p.poly.op).Gen) : GenObj (p.Br Zbp).Gen := p.brZPt x.as

/-- **…and they name the same object.** -/
noncomputable def brZTheta (N : ℕ) :
    ((p.presentsBr Zbp).transport zLocOpEquiv).at' (p.brZPt N)
      ≅ op (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
  (chLocBase Zbp).mapIso (p.ιRunIso Zbp (zRun N))

/-- **The braid a letter's 1-cell performs is the letter's own permutation** — the cell is a single
crossing above the run, and `chBraid_colimSliceEval` reads it in the copy it lives in. -/
theorem chBraid_letterCell (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    chBraid ((p.presentsBr Zbp).arrow (p.letterCell hp s))
        (p.strands_ιRun N) (p.strands_ιRun N) = posPerm (p.perm s) := by
  have hA : dimSum (chOf ((p.presentsBr Zbp).at'
      (ιV Zbp p.fam ((toElements Zbp).obj (zObj (topDims N)))
        (p.runPt (topRunAt N (p.perm s)))))).dims = N :=
    (congrArg (fun v => dimSum (chOf ((p.presentsBr Zbp).at' v)).dims)
      (p.ιV_topLeg (p.perm s))).trans (p.strands_ιRun N)
  have hB : dimSum (chOf ((p.presentsBr Zbp).at'
      (ιV Zbp p.fam ((toElements Zbp).obj (zObj (topDims N)))
        (p.runPt (topRunAt N 1))))).dims = N :=
    (congrArg (fun v => dimSum (chOf ((p.presentsBr Zbp).at' v)).dims)
      (p.ιV_topLeg 1)).trans (p.strands_ιRun N)
  rw [letterCell, Presents.arrow_homOfEq]
  refine (chBraid_eqToHom_sandwich _ _ _ (p.strands_ιRun N) hA hB
    (p.strands_ιRun N)).trans ?_
  exact p.chBraid_runGen Zbp ((toElements Zbp).obj (zObj (topDims N))) s
    (p.action_topRunAt hp s) (perm_topRunAt N 1) hA hB

/-- **A letter and its 1-cell name the same arrow** — both perform the letter's permutation, and
the localized base is faithful on braids. -/
theorem hgen_letter (hp : p.BySimples) {N : ℕ} (s : p.S N) :
    ((p.presentsBr Zbp).transport zLocOpEquiv).arrow (p.letterCell hp s)
      = (p.brZTheta N).hom ≫ (p.base.arrow (p.gen s)).op ≫ (p.brZTheta N).inv := by
  have hX := p.strands_ιRun N
  have hA : dimSum (zObj (chOf ((p.presentsBr Zbp).at' (p.ιRun Zbp (zRun N)))).dims).dims = N :=
    hX
  haveI h1 : IsIso ((p.brZTheta N).inv.unop) := inferInstanceAs (IsIso ((p.brZTheta N).unop).inv)
  haveI h2 : IsIso ((p.brZTheta N).hom.unop) := inferInstanceAs (IsIso ((p.brZTheta N).unop).hom)
  refine Quiver.Hom.unop_inj ((homEquivPosBraid hA hA).injective ?_)
  have hL : homEquivPosBraid hA hA
      (((p.presentsBr Zbp).transport zLocOpEquiv).arrow (p.letterCell hp s)).unop
      = chBraid ((p.presentsBr Zbp).arrow (p.letterCell hp s)) hX hX := rfl
  have hR : ((p.brZTheta N).hom ≫ (p.base.arrow (p.gen s)).op ≫ (p.brZTheta N).inv).unop
      = (p.brZTheta N).inv.unop ≫ p.base.arrow (p.gen s) ≫ (p.brZTheta N).hom.unop := by
    rw [unop_comp, unop_comp, Category.assoc]
    rfl
  rw [hL, p.chBraid_letterCell hp s]
  refine Eq.trans ?_ (congrArg (fun t => homEquivPosBraid hA hA t) hR).symm
  -- `rw` cannot fire: the middle object is spelled `p.base.at' (p.pt N)` on one side and
  -- `Q.obj (op (zObj (𝟙^N)))` on the other, `rfl`-equal but not syntactically so.
  exact ((homEquivPosBraid_sandwich hA hA (dimSum_replicate N) (dimSum_replicate N)
        ((p.brZTheta N).inv.unop) h1 (p.base.arrow (p.gen s)) ((p.brZTheta N).hom.unop) h2).trans
      ((congrArg (fun t => homEquivPosBraid (dimSum_replicate N) (dimSum_replicate N) t)
          (p.base_arrow_of_simple hp s)).trans (homEquivPosBraid_runLoop N (p.perm s)))).symm

/-- **The 1-cell dictionary**, read on a cell of the coproduct: a letter goes to its own crossing
above the run. -/
noncomputable def brZGenAux (hp : p.BySimples) :
    ∀ a b : ℕ,
      Polygraph.StrandGen p.Gen a b → (p.brZPt b ⟶ p.brZPt a)
  | _, _, .mk (i := _) s => p.letterCell hp s

/-- …as a map of the generating quivers. -/
noncomputable def brZGen (hp : p.BySimples) {x y : GenObj (p.poly.op).Gen} (e : x ⟶ y) :
    p.brZOb x ⟶ p.brZOb y :=
  p.brZGenAux hp y.as x.as e

theorem brZ_hgen (hp : p.BySimples) {x y : GenObj (p.poly.op).Gen} (e : x ⟶ y) :
    ((p.presentsBr Zbp).transport zLocOpEquiv).arrow (p.brZGen hp e)
      = (p.brZTheta x.as).hom ≫ (p.base.op).arrow e ≫ (p.brZTheta y.as).inv := by
  obtain ⟨i⟩ := x
  obtain ⟨j⟩ := y
  cases e with
  | mk s => rw [Presents.op_arrow]; exact p.hgen_letter hp s

/-- **`p`'s own polygraph, mapped into `Br p Zbp` generator by generator.**  A 0-cell goes to a
strand count and a letter to its own crossing; no word is chosen, and the comparison is
automatically an equivalence (`Presents.Map.isEquivalence`).  `BySimples` is not a convenience: a
letter longer than its permutation acts on no run and names no 1-cell. -/
noncomputable def brZMap (hp : p.BySimples) :
    Presents.Map (p.base.op) ((p.presentsBr Zbp).transport zLocOpEquiv) :=
  Presents.Map.ofGenerators p.brZOb (fun {_ _} e => p.brZGen hp e)
    (fun x => p.brZTheta x.as) fun {_ _} e => p.brZ_hgen hp e

/-- **The spelling is one letter long** — a generator goes to a generator, not to a word. -/
theorem brZMap_cells (hp : p.BySimples) {x y : GenObj (p.poly.op).Gen} (e : x ⟶ y) :
    (p.brZMap hp).hom.cells.map e = (p.brZGen hp e).toPath := rfl

/-- **…so `p`'s polygraph and `Br p Zbp` present `Ch(Z)[W⁻¹]` compatibly.**  On its own this says
nothing: any two presentations of one category are equivalent.  The content is the generating
data — `bijective_brZPt`, and the 1-cells in `BrBaseCells`. -/
noncomputable def brZEquiv (hp : p.BySimples) : (p.poly.op).presented ≌ (p.Br Zbp).presented :=
  (p.brZMap hp).equiv

/-! ## The 0-cells are the strand counts

Unconditionally, and with no reference to the letters: a 0-cell of `Br p Zbp` is a run over some
chain, hence the run's own 0-cell, and distinct strand counts name distinct objects. -/

theorem exists_brZPt (A : GenObj (p.Br Zbp).Gen) : ∃ N, A = p.brZPt N := by
  obtain ⟨c, w, hw⟩ := Polygraph.exists_colimit_ι_obj (elementsPoly (wedgeHoms Zbp) p.fam) A
  obtain ⟨z, hz⟩ := p.exists_ιRun Zbp c rfl w.as
  exact ⟨_, (hw.symm.trans hz).trans (congrArg (p.ιRun Zbp) (Subsingleton.elim _ _))⟩

theorem brZPt_injective : Function.Injective p.brZPt := fun M N h =>
  (p.strands_ιRun M).symm.trans
    ((congrArg (fun v => dimSum (chOf ((p.presentsBr Zbp).at' v)).dims) h).trans
      (p.strands_ιRun N))

/-- **The 0-cells of `Br p Zbp` are the strand counts.** -/
theorem bijective_brZPt : Function.Bijective p.brZPt :=
  ⟨p.brZPt_injective, fun A => (p.exists_brZPt A).imp fun _ h => h.symm⟩

end BraidPresentation

end ChainCat
