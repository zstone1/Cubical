import CubeChains.Concurrency.Presentation.GlueRun

/-!
# Concurrency/Presentation/BrFunctor — `Br p` is a functor on `BPSet`

A map `K ⟶ K'` moves an element of `wedgeHoms K` without moving its chain, so the two colimit
diagrams are one diagram read over two index categories and the comparison is `colimit.pre`.  Both
functor laws are then the colimit's, because `≫ 𝟙` and `≫`-associativity are *definitional* in
`BPSet` — `brElt` is strictly functorial.

What pins the functor down is its action on the runs: `Br p f` sends a run's 0-cell to the
pushed-forward run's, which is what `Ch f` does.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits

namespace ChainCat

/-- `⋁- ⟶ K`, moved along a map of `K`. -/
def wedgeHomsMap {K K' : BPSet} (f : K ⟶ K') : wedgeHoms K ⟶ wedgeHoms K' :=
  Functor.whiskerLeft serialWedgeInclusion.op (yoneda.map f)

/-- **A map of `K` moves an element without moving its chain** — the copies of the colimit are
re-indexed and nothing else. -/
def brElt {K K' : BPSet} (f : K ⟶ K') :
    ((wedgeHoms K).Elements)ᵒᵖ ⥤ ((wedgeHoms K').Elements)ᵒᵖ :=
  (NatTrans.mapElements (wedgeHomsMap f)).op

theorem brElt_id (K : BPSet) : brElt (𝟙 K) = 𝟭 _ := rfl

theorem brElt_comp {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') :
    brElt (f ≫ g) = brElt f ⋙ brElt g := rfl

theorem brElt_comp_eltBase {K K' : BPSet} (f : K ⟶ K') :
    brElt f ⋙ (CategoryOfElements.π (wedgeHoms K')).leftOp
      = (CategoryOfElements.π (wedgeHoms K)).leftOp := rfl

/-- **A merge stays a merge downstream** — `W` is a condition on the wedge map alone. -/
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

namespace BraidPresentation

variable (p : BraidPresentation)

/-- **`Br p` on a map of `K`**: the copies, re-indexed. -/
noncomputable def brMap {K K' : BPSet} (f : K ⟶ K') : p.Br K ⟶ p.Br K' :=
  colimit.pre (elementsPoly (wedgeHoms K') p.fam) (brElt f)

/-- **…and it is the colimit's own comparison**: a copy goes to the copy it is re-indexed to. -/
theorem ι_brMap {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    colimit.ι (elementsPoly (wedgeHoms K) p.fam) c ≫ p.brMap f
      = colimit.ι (elementsPoly (wedgeHoms K') p.fam) ((brElt f).obj c) :=
  colimit.ι_pre (elementsPoly (wedgeHoms K') p.fam) (brElt f) c

/-- **`Br p` is a functor on `BPSet`.**  Both laws are the colimit's own: `brElt` is *strictly*
functorial, `≫ 𝟙` and associativity being definitional in `BPSet`. -/
noncomputable def brFunctor : BPSet ⥤ Polygraph.{0, 0, 0} where
  obj K := p.Br K
  map f := p.brMap f
  map_id K := colimit.hom_ext fun c => (p.ι_brMap (𝟙 K) c).trans (Category.comp_id _).symm
  map_comp f g := colimit.hom_ext fun c =>
    (p.ι_brMap (f ≫ g) c).trans
      (((p.ι_brMap g ((brElt f).obj c)).symm.trans
        (congrArg (fun m : (elementsPoly (wedgeHoms _) p.fam).obj ((brElt f).obj c) ⟶ p.Br _ =>
          m ≫ p.brMap g) (p.ι_brMap f c).symm)).trans (Category.assoc _ _ _))

@[simp] theorem brFunctor_obj (K : BPSet) : p.brFunctor.obj K = p.Br K := rfl

@[simp] theorem brFunctor_map {K K' : BPSet} (f : K ⟶ K') : p.brFunctor.map f = p.brMap f := rfl

/-! ## What the functor does

A 0-cell of a copy stays in its copy, and a run's 0-cell goes to the pushed-forward run's — so the
functor is `Ch f` on the runs, and `at_glueRunV` reads that off. -/

theorem brMap_glueV {K K' : BPSet} (f : K ⟶ K') (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (slicePolyRaw p.base (eltBase (wedgeHoms K) c)).V) :
    (p.brMap f).pre.obj (glueV K p.fam c a) = glueV K' p.fam ((brElt f).obj c) a :=
  congrArg (fun m : (elementsPoly (wedgeHoms K) p.fam).obj c ⟶ p.Br K' => m.pre.obj ⟨a⟩)
    (p.ι_brMap f c)

/-- **`Br p f` is `Ch f` on the runs.** -/
theorem brMap_glueRunV {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.brMap f).pre.obj (p.glueRunV K z) = p.glueRunV K' (z ≫ f) :=
  p.brMap_glueV f ((toElements K).obj (runCh z)) (p.runPt (runAtSelf n))

/-- **…read on the objects**: the run's chain, pushed forward. -/
noncomputable def brMapRunIso {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.presentsBr K').at' ((p.brMap f).pre.obj (p.glueRunV K z))
      ≅ (W K').Q.obj ((ChainCat.pushforward f).obj (runCh z)) :=
  eqToIso (congrArg (p.presentsBr K').at' (p.brMap_glueRunV f z)) ≪≫
    p.glueRunIso K' (z ≫ f)

/-- **…and that is exactly `Ch f` localized**: the square of 0-cells commutes up to the
presentations' own comparisons, and every 0-cell is a run's (`exists_glueRunV`). -/
noncomputable def brMapRunNat {K K' : BPSet} (f : K ⟶ K') {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.presentsBr K').at' ((p.brMap f).pre.obj (p.glueRunV K z))
      ≅ (chLocMap f).obj ((p.presentsBr K).at' (p.glueRunV K z)) :=
  p.brMapRunIso f z ≪≫ (chLocMap f).mapIso (p.glueRunIso K z).symm

end BraidPresentation

end ChainCat
