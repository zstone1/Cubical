import CubeChains.Concurrency.Presentation.Retraction

/-!
# Concurrency/Presentation/BaseComponent — `Ch Zbp[W⁻¹]`, presented per strand count

The strand count is the only thing separating components (`isEmpty_loc_hom`), and inside one
component every chain is its run (`runIso`) with `PosBraid N` for endomorphisms
(`runBraidEquiv`).  So each component is a single object carrying the Artin monoid on `N−1`
generators: `strandComponentArtin`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain ChainCat

namespace ChainCat

/-! ## The run, as a one-object base -/

/-- The run of `N` events, as a one-object piece of the localized base. -/
noncomputable def runBase (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ⥤ ((W Zbp).op).Localization where
  obj _ := ((W Zbp).op).Q.obj (op (zObj (𝟙^N)))
  map {_ _} f := (runBraid N (f.unop : PosBraid N)).unop
  map_id x := by
    have h := SingleObj.id_as_one (M := PosBraid N) x.unop
    change (runBraid N (𝟙 x).unop).unop = _
    rw [unop_id, h, map_one]
    rfl
  map_comp {_ _ _} f g := by
    have h := SingleObj.comp_as_mul (M := PosBraid N) g.unop f.unop
    change (runBraid N (f ≫ g).unop).unop = _
    rw [unop_comp, h, map_mul]
    rfl

/-! ## …and the whole base at once

`runBase N` is one degree of a single functor out of `FullPosBraidᵒᵖ`: strand counts as objects,
braids as loops, each read at the run it grades.  It is an equivalence, so the localized base *is*
the graded braid monoid — no coproduct, no component-by-component assembly. -/

/-- **The localized base, read on the braids**: the strand count `N` names the run of `N` events,
and a braid names the loop it performs there. -/
noncomputable def runFullBase : FullPosBraidᵒᵖ ⥤ ((W Zbp).op).Localization :=
  Graded.descOp (fun N => ((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) runBraid

@[simp] theorem runFullBase_obj (N : ℕ) :
    runFullBase.obj (op N) = ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) := rfl

/-- A braid, as a loop of the graded braid monoid read backwards. -/
def braidLoop (N : ℕ) (β : PosBraid N) : (op N : FullPosBraidᵒᵖ) ⟶ op N :=
  Quiver.Hom.op (⟨rfl, β⟩ : @Quiver.Hom FullPosBraid _ N N)

@[simp] theorem runFullBase_braidLoop (N : ℕ) (β : PosBraid N) :
    runFullBase.map (braidLoop N β) = (runBraid N β).unop :=
  Category.id_comp _

@[simp] theorem braidLoop_one (N : ℕ) : braidLoop N 1 = 𝟙 (op N : FullPosBraidᵒᵖ) := rfl

theorem braidLoop_mul (N : ℕ) (β γ : PosBraid N) :
    braidLoop N (β * γ) = braidLoop N β ≫ braidLoop N γ := rfl

instance runFullBase_faithful : runFullBase.Faithful where
  map_injective {X Y f g} h :=
    Quiver.Hom.unop_inj (GradedHom.ext (runBraid_injective Y.unop (MulOpposite.unop_inj.mp
      ((cancel_epi (eqToHom (congrArg (fun N => ((W Zbp).op).Q.obj (op (zObj (𝟙^N))))
        f.unop.deg.symm))).mp h))))

instance runFullBase_full : runFullBase.Full where
  map_surjective {X Y} t := by
    obtain ⟨m⟩ := X
    obtain ⟨n⟩ := Y
    obtain hmn : n = m :=
      (dimSum_replicate n).symm.trans ((strandsEq_loc t).trans (dimSum_replicate m))
    subst hmn
    refine ⟨braidLoop n (runGrade n (MulOpposite.op t)), ?_⟩
    rw [runFullBase_braidLoop, runBraid_runGrade]
    rfl

instance runFullBase_essSurj : runFullBase.EssSurj where
  mem_essImage c := by
    obtain ⟨a, ha⟩ : ∃ a : Ch Zbp, ((W Zbp).op).Q.obj (op a) = c :=
      ⟨((Localization.Construction.objEquiv ((W Zbp).op)).symm c).unop, by
        rw [Opposite.op_unop]
        exact (Localization.Construction.objEquiv ((W Zbp).op)).right_inv c⟩
    exact ⟨op (dimSum a.dims), ⟨(runIso a rfl).symm ≪≫ eqToIso ha⟩⟩

instance runFullBase_isEquivalence : runFullBase.IsEquivalence where

/-- **`Ch Zbp[W⁻¹]` *is* the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands. -/
noncomputable def fullBaseEquiv : FullPosBraidᵒᵖ ≌ ((W Zbp).op).Localization :=
  runFullBase.asEquivalence

/-- A braid, as an arrow of its one-object component — the spelling `runBase` consumes. -/
def posArrow (N : ℕ) (β : PosBraid N) :
    (op (SingleObj.star (PosBraid N)) : (SingleObj (PosBraid N))ᵒᵖ)
      ⟶ op (SingleObj.star (PosBraid N)) :=
  Quiver.Hom.op β

@[simp] theorem runBase_map_posArrow (N : ℕ) (β : PosBraid N) :
    (runBase N).map (posArrow N β) = (runBraid N β).unop := rfl

theorem bijective_runBase_map (N : ℕ) (X Y : (SingleObj (PosBraid N))ᵒᵖ) :
    Function.Bijective fun f : X ⟶ Y => (runBase N).map f := by
  constructor
  · intro f g h
    exact Quiver.Hom.unop_inj
      ((runBraidEquiv N).injective (MulOpposite.unop_inj.mp h))
  · intro t
    refine ⟨Quiver.Hom.op
      (show SingleObj.star (PosBraid N) ⟶ SingleObj.star (PosBraid N) from
        (runBraidEquiv N).symm (MulOpposite.op t)), ?_⟩
    change (runBraid N ((runBraidEquiv N).symm (MulOpposite.op t))).unop = t
    rw [show runBraid N ((runBraidEquiv N).symm (MulOpposite.op t))
      = (runBraidEquiv N) ((runBraidEquiv N).symm (MulOpposite.op t)) from rfl,
      MulEquiv.apply_symm_apply]
    rfl

instance (N : ℕ) : (runBase N).Full where
  map_surjective g := (bijective_runBase_map N _ _).2 g

instance (N : ℕ) : (runBase N).Faithful where
  map_injective h := (bijective_runBase_map N _ _).1 h

/-! ## One component -/

/-- The objects of the localized base at strand count `N`. -/
def AtStrands (N : ℕ) : ObjectProperty (((W Zbp).op).Localization) :=
  fun c => ∃ a : Ch Zbp, dimSum a.dims = N ∧ ((W Zbp).op).Q.obj (op a) = c

theorem atStrands_run (N : ℕ) : AtStrands N (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
  ⟨zObj (𝟙^N), dimSum_replicate N, rfl⟩

/-- The run, as the single object of the strand-`N` component. -/
noncomputable def runBaseAt (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ⥤ (AtStrands N).FullSubcategory :=
  (AtStrands N).lift (runBase N) fun _ => atStrands_run N

instance (N : ℕ) : (runBaseAt N).Full :=
  inferInstanceAs ((AtStrands N).lift (runBase N) (fun _ => atStrands_run N)).Full

instance (N : ℕ) : (runBaseAt N).Faithful :=
  inferInstanceAs ((AtStrands N).lift (runBase N) (fun _ => atStrands_run N)).Faithful

instance (N : ℕ) : (runBaseAt N).EssSurj where
  mem_essImage := by
    rintro ⟨c, a, ha, rfl⟩
    exact ⟨op (SingleObj.star (PosBraid N)),
      ⟨(ObjectProperty.fullyFaithfulι _).preimageIso (runIso a ha).symm⟩⟩

instance (N : ℕ) : (runBaseAt N).IsEquivalence where

/-- **The strand-`N` part of `Ch Zbp[W⁻¹]` is one object carrying the positive braid monoid.** -/
noncomputable def strandComponentGarside (N : ℕ) :
    (SingleObj (PosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory :=
  (runBaseAt N).asEquivalence

/-- **`Ch Zbp[W⁻¹]` at strand count `N` is one object whose endomorphisms are the Artin monoid on
`N−1` generators** — `ArtinPosBraid N` is `PresentedMonoid (ArtinRel N)`, so this names the
generators (the atoms) and the relations (commutation and braid). -/
noncomputable def strandComponentArtin (N : ℕ) :
    (SingleObj (ArtinPosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory :=
  ((MulEquiv.toSingleObjEquiv (posBraid_equiv_artinPos N)).op).symm.trans
    (strandComponentGarside N)

end ChainCat
