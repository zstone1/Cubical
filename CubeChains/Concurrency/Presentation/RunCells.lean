import CubeChains.Concurrency.Presentation.GarsidePresentation

/-!
# Concurrency/Presentation/RunCells — a run's own 0-cell in `runPoly K`

Every 0-cell of `runPoly K` is a run's, read in the copy indexed by the run's own chain
(`exists_ιRun`): a 0-cell of a copy over `d` is a run over `d`, and a run over `d` is the
identity run pushed along its own arrow, so the colimit's leg carries it down.  Every 1-cell is a
Garside simple crossed above a run (`exists_runGen`), with no word chosen.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Localization

namespace ChainCat

/-- The chain of `K` a run of `n` events is. -/
def runCh {K : BPSet} {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) : Ch K := ⟨𝟙^n, z⟩

/-- A run, as a run-arrow over its own chain. -/
def runAtSelf (n : ℕ) : RunAt (zObj (𝟙^n)) n :=
  ⟨⟨Over.mk (𝟙 _), fun _ hd => List.eq_of_mem_replicate hd⟩, dimSum_replicate n⟩

@[simp] theorem perm_runAtSelf (n : ℕ) : (runAtSelf n).perm = 1 :=
  crossPerm_id (zObj (𝟙^n)) _

/-- **The comparison with the localized category of elements, at a `Q`-image.** -/
noncomputable def elementsUnitIso (K : BPSet) (a : Ch K) :
    (locEquivElements K).inverse.obj
        (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
          ((toElements K).obj a))
      ≅ (W K).Q.obj a :=
  (locEquivElements K).inverse.mapIso
      ((Localization.compUniqFunctor (W K).Q
        (toElements K ⋙ ((W Zbp).inverseImage
          (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)).app a).symm ≪≫
    ((locEquivElements K).unitIso.app ((W K).Q.obj a)).symm

/-! ## The cells of the colimit -/

/-- **The object a 0-cell of `runPoly K` names** — `ChainCat.at_ιV`, at the Garside colimit. -/
theorem garside_at_ιV (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (germBP.slicePoly (eltBase (wedgeHoms K) c)).V) :
    (runPresents K).at' (ιV K germBP.fam c a)
      = (locEquivElements K).inverse.obj
          ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).obj
            ((germBP.slicePresentation (eltBase (wedgeHoms K) c)).at' ⟨a⟩)) :=
  ChainCat.at_ιV K germBP.fam germBP.slicePresentation
    (fun {_ _} f => germBP.slicePoly_hP f) c a

/-- …and the arrow a word of a copy names — what a *spelling* of `runPoly K` meets. -/
theorem garside_eval_ιWord (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : GenObj (germBP.fam.obj (eltBase (wedgeHoms K) c)).Gen} (w : Quiver.Path a b) :
    (runPresents K).eval.map
        ((colimit.ι (elementsPoly (wedgeHoms K) germBP.fam) c).words.map w)
      = eqToHom (garside_at_ιV K c a.as) ≫ (locEquivElements K).inverse.map
            ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((germBP.slicePresentation (eltBase (wedgeHoms K) c)).eval.map w))
          ≫ eqToHom (garside_at_ιV K c b.as).symm :=
  ChainCat.eval_ιWord K germBP.fam germBP.slicePresentation
    (fun {_ _} f => germBP.slicePoly_hP f) c w

/-- …and the arrow a 1-cell names: `eval_ιWord` at its length-one word, spelled so that a caller
holding a 1-cell of `germBP.fam` need not fix the quiver by hand. -/
theorem garside_arrow_ιE (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a b : (germBP.slicePoly (eltBase (wedgeHoms K) c)).V)
    (g : (⟨a⟩ : GenObj (germBP.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (runPresents K).arrow (ιE K germBP.fam c g)
      = eqToHom (garside_at_ιV K c a) ≫ (locEquivElements K).inverse.map
            ((colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((germBP.slicePresentation (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (garside_at_ιV K c b).symm :=
  garside_eval_ιWord K c g.toPath

/-- **The 0-cell of `runPoly K` a run names**: itself, in its own copy. -/
noncomputable def ιRun (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) : GenObj (runPoly K).Gen :=
  ιV K germBP.fam ((toElements K).obj (runCh z)) (germBP.runPt (runAtSelf n))

theorem at_ιRun (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (runPresents K).at' (ιRun K z)
      = (locEquivElements K).inverse.obj
          (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
            ((toElements K).obj (runCh z))) := by
  refine (ChainCat.at_ιV K germBP.fam germBP.slicePresentation
    (fun {_ _} f => germBP.slicePoly_hP f)
    ((toElements K).obj (runCh z)) (germBP.runPt (runAtSelf n))).trans
      (congrArg (locEquivElements K).inverse.obj ?_)
  refine Eq.trans (congrArg
    (colimSliceEval (wedgeHoms K) (W Zbp) (zObj (𝟙^n)) z).obj
    ((germBP.slicePresentation_at _ (germBP.runPt (runAtSelf n))).trans
      (congrArg ((W Zbp).over (X := zObj (𝟙^n))).Q.obj
        (germBP.sliceCellOver_runPt (runAtSelf n))))) ?_
  refine (Functor.congr_obj
    (colimSliceEval_fac (wedgeHoms K) (W Zbp) (zObj (𝟙^n)) z) (Over.mk (𝟙 _))).trans ?_
  exact congrArg (fun t => ((W Zbp).inverseImage
    (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj (op ⟨op (zObj (𝟙^n)), t⟩))
    ((wedgeHoms K).map_id_apply (op (zObj (𝟙^n))) z)

/-- **The colimit route names the localized run chain.** -/
noncomputable def ιRunIso (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (runPresents K).at' (ιRun K z) ≅ (W K).Q.obj (runCh z) :=
  eqToIso (at_ιRun K z) ≪≫ elementsUnitIso K (runCh z)

/-- **Every 0-cell of a copy is a run's own 0-cell** — a run over `d` is entered from its own
chain, and the leg down to it is an arrow of the elements. -/
theorem exists_ιRun (K : BPSet) {n : ℕ} (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (hc : dimSum (eltBase (wedgeHoms K) c).dims = n)
    (a : (germBP.slicePoly (eltBase (wedgeHoms K) c)).V) :
    ∃ z : ⋁(𝟙^n) ⟶ K, ιV K germBP.fam c a = ιRun K z := by
  obtain ⟨u, rfl⟩ := germBP.exists_runPt_of_strands hc a
  obtain ⟨⟨⟨l, ⟨⟩, h⟩, hrun⟩, hN⟩ := u
  obtain rfl : l = zObj (𝟙^n) := RunOver.left_eq hc ⟨Over.mk h, hrun⟩
  refine ⟨(wedgeHoms K).map h.op c.unop.2, Eq.trans (congrArg (ιV K germBP.fam c) ?_)
    ((congrArg (ιV K germBP.fam c) (germBP.famV_runPt h (runAtSelf n)).symm).trans
      (ιV_leg K germBP.fam (eltLeg K h c.unop.2) (germBP.runPt (runAtSelf n))))⟩
  exact congrArg germBP.runPt
    (Subtype.ext (Subtype.ext (congrArg Over.mk (Category.id_comp h).symm)))

/-- **Every 1-cell of `runPoly K` is a Garside simple crossed above a run.**  A 1-cell lives in
a single copy (`exists_colimit_ι_map`) and inside a copy it is a generator acting (`gen_action`); no
word is involved, and the 1-cell is recovered on the nose.  The slice polygraph is the base's
reversed, so the simple runs `u ⟶ v` and the 1-cell runs `v ⟶ u`. -/
theorem exists_runGen (K : BPSet) {A B : GenObj (runPoly K).Gen} (e : A ⟶ B) :
    ∃ (c : ((wedgeHoms K).Elements)ᵒᵖ) (N : ℕ) (σ : Equiv.Perm (Fin N))
      (u v : RunAt (eltBase (wedgeHoms K) c) N)
      (hact : RunGermStep (posPerm σ) u v)
      (hA : ιV K germBP.fam c (germBP.runPt v) = A)
      (hB : ιV K germBP.fam c (germBP.runPt u) = B),
      Quiver.homOfEq (ιE K germBP.fam c (germBP.runGen σ hact)) hA hB = e := by
  obtain ⟨c, a, b, g, hA, hB, he⟩ :=
    Polygraph.exists_colimit_ι_map (elementsPoly (wedgeHoms K) germBP.fam) e
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  obtain ⟨N, v, rfl⟩ := germBP.exists_runPt a
  obtain ⟨M, u, rfl⟩ := germBP.exists_runPt b
  obtain rfl : M = N := u.strands.symm.trans v.strands
  obtain ⟨s, hact, rfl⟩ := germBP.gen_action
    (g : (⟨germBP.runPt u⟩ : GenObj (germBP.slicePoly (eltBase (wedgeHoms K) c)).Gen)
      ⟶ ⟨germBP.runPt v⟩)
  exact ⟨c, M, s, u, v, hact, hA, hB, he⟩

end ChainCat
