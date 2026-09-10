import CubeChains.Concurrency.Presentation.RunCells

/-!
# Concurrency/Presentation/GarsideFunctor — `runPoly` is a functor on `BPSet`

A map `K ⟶ K'` moves an element of `wedgeHoms K` without moving its chain, so the two colimit
diagrams are one diagram read over two index categories and the comparison is `colimit.pre`.  Both
functor laws are then the colimit's, because `≫ 𝟙` and `≫`-associativity are *definitional* in
`BPSet` — `runElt` is strictly functorial.

What pins the functor down is its action on the runs: it sends a run's 0-cell to the
pushed-forward run's, which is what `Ch f` does.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

/-- `⋁- ⟶ K`, moved along a map of `K`. -/
def wedgeHomsMap {K K' : BPSet} (f : K ⟶ K') : wedgeHoms K ⟶ wedgeHoms K' :=
  Functor.whiskerLeft serialWedgeInclusion.op (yoneda.map f)

/-- **A map of `K` moves an element without moving its chain** — the copies of the colimit are
re-indexed and nothing else. -/
def runElt {K K' : BPSet} (f : K ⟶ K') :
    ((wedgeHoms K).Elements)ᵒᵖ ⥤ ((wedgeHoms K').Elements)ᵒᵖ :=
  (NatTrans.mapElements (wedgeHomsMap f)).op

theorem W_pushforward {K K' : BPSet} (f : K ⟶ K') {a b : Ch K} {g : a ⟶ b} (hg : W K g) :
    W K' ((ChainCat.pushforward f).map g) :=
  (W_iff_monotone_coordMap _).mpr ((W_iff_monotone_coordMap g).mp hg)

/-- **`Ch f`, localized.** -/
noncomputable def chLocMap {K K' : BPSet} (f : K ⟶ K') :
    (W K).Localization ⥤ (W K').Localization :=
  Localization.Construction.lift (ChainCat.pushforward f ⋙ (W K').Q)
    fun _ _ _ hg => Localization.inverts (W K').Q (W K') _ (W_pushforward f hg)

@[simp] theorem chLocMap_obj_Q {K K' : BPSet} (f : K ⟶ K') (a : Ch K) :
    (chLocMap f).obj ((W K).Q.obj a) = (W K').Q.obj ((ChainCat.pushforward f).obj a) := rfl

theorem chLocMap_id (K : BPSet) : chLocMap (𝟙 K) = 𝟭 _ :=
  Localization.Construction.uniq _ _ (Localization.Construction.fac _ _)

theorem chLocMap_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    chLocMap (f ≫ g) = chLocMap f ⋙ chLocMap g :=
  Localization.Construction.uniq _ _ (by
    have h2 : (W K').Q ⋙ chLocMap g = ChainCat.pushforward g ⋙ (W K'').Q :=
      Localization.Construction.fac _ _
    have h3 : (W K).Q ⋙ chLocMap f = ChainCat.pushforward f ⋙ (W K').Q :=
      Localization.Construction.fac _ _
    calc (W K).Q ⋙ chLocMap (f ≫ g)
        = ChainCat.pushforward f ⋙ (ChainCat.pushforward g ⋙ (W K'').Q) :=
          Localization.Construction.fac _ _
      _ = ChainCat.pushforward f ⋙ ((W K').Q ⋙ chLocMap g) := by rw [h2]
      _ = ((W K).Q ⋙ chLocMap f) ⋙ chLocMap g := by rw [h3]; exact (Functor.assoc _ _ _).symm
      _ = (W K).Q ⋙ chLocMap f ⋙ chLocMap g := Functor.assoc _ _ _)

/-- **The run polygraph on a map of `K`**: the copies, re-indexed. -/
noncomputable def runMap {K K' : BPSet} (f : K ⟶ K') : runPoly K ⟶ runPoly K' :=
  colimit.pre (elementsPoly (wedgeHoms K') germBP.fam) (runElt f)

/-- **…and it is the colimit's own comparison**: a copy goes to the copy it is re-indexed to. -/
theorem ι_runMap {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    colimit.ι (elementsPoly (wedgeHoms K) germBP.fam) c ≫ runMap f
      = colimit.ι (elementsPoly (wedgeHoms K') germBP.fam) ((runElt f).obj c) :=
  colimit.ι_pre (elementsPoly (wedgeHoms K') germBP.fam) (runElt f) c

/-- **The run polygraph is a functor on `BPSet`.**  Both laws are the colimit's own:
`runElt` is *strictly* functorial, `≫ 𝟙` and associativity being definitional in `BPSet`. -/
noncomputable def runFunctor : BPSet ⥤ Polygraph.{0, 0, 0} where
  obj K := runPoly K
  map f := runMap f
  map_id K := colimit.hom_ext fun c => (ι_runMap (𝟙 K) c).trans (Category.comp_id _).symm
  map_comp f g := colimit.hom_ext fun c =>
    (ι_runMap (f ≫ g) c).trans
      (((ι_runMap g ((runElt f).obj c)).symm.trans
        (congrArg (fun m : (elementsPoly (wedgeHoms _) germBP.fam).obj ((runElt f).obj c)
            ⟶ runPoly _ => m ≫ runMap g) (ι_runMap f c).symm)).trans
        (Category.assoc _ _ _))

@[simp] theorem runFunctor_obj (K : BPSet) : runFunctor.obj K = runPoly K := rfl

@[simp] theorem runFunctor_map {K K' : BPSet} (f : K ⟶ K') :
    runFunctor.map f = runMap f := rfl

/-! ## What the functor does

A 0-cell of a copy stays in its copy, and a run's 0-cell goes to the pushed-forward run's — so the
functor is `Ch f` on the runs, and `at_ιRun` reads that off. -/

theorem runMap_ιV {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (germBP.slicePoly (eltBase (wedgeHoms K) c)).V) :
    (runMap f).pre.obj (ιV K germBP.fam c a) = ιV K' germBP.fam ((runElt f).obj c) a :=
  congrArg (fun m : (elementsPoly (wedgeHoms K) germBP.fam).obj c ⟶ runPoly K' => m.pre.obj ⟨a⟩)
    (ι_runMap f c)

/-- **The functor is `Ch f` on the runs.** -/
theorem runMap_ιRun {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (runMap f).pre.obj (ιRun K z) = ιRun K' (z ≫ f) :=
  runMap_ιV f ((toElements K).obj (runCh z)) (germBP.runPt (runAtSelf n))

/-- **…read on the objects**: the run's chain, pushed forward. -/
noncomputable def runMapRunIso {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (runPresents K').at' ((runMap f).pre.obj (ιRun K z))
      ≅ (W K').Q.obj ((ChainCat.pushforward f).obj (runCh z)) :=
  eqToIso (congrArg (runPresents K').at' (runMap_ιRun f z)) ≪≫ ιRunIso K' (z ≫ f)

/-- **…and that is exactly `Ch f` localized**: the square of 0-cells commutes up to the
presentations' own comparisons, and every 0-cell is a run's (`exists_ιRun`). -/
noncomputable def runMapRunNat {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (runPresents K').at' ((runMap f).pre.obj (ιRun K z))
      ≅ (chLocMap f).obj ((runPresents K).at' (ιRun K z)) :=
  runMapRunIso f z ≪≫ (chLocMap f).mapIso (ιRunIso K z).symm

end ChainCat
