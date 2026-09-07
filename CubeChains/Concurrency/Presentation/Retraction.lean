import CubeChains.Concurrency.Presentation.LocPresentation
import CubeChains.Machinery.Graded
import CubeChains.Machinery.Braid.Matsumoto

/-!
# Concurrency/Presentation/Retraction — `Ch Zbp` with the bead merges inverted

The crossing permutations are a length-additive cocycle, so `posGerm` turns them into a functor
`Ch Zbp ⥤ FullPosBraid` inverting the merges (`posGrade`), hence into a map on the localization
that retracts `runLoop`.  `runLoop` generates, so the two are inverse (`runBraidEquiv`), and
conjugating by `runIso` reads every hom-set the same way (`homEquivPosBraid`).

`ᵐᵒᵖ` is the composition order: `End` multiplies backwards, and `x * y = x ≫ y` only after `op`.
-/

open CategoryTheory Equiv Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## The braid a refinement performs -/

/-- **The positive braid a refinement performs** — its crossing permutation, as a germ simple. -/
def posGrade : Ch Zbp ⥤ FullPosBraid where
  obj a := dimSum a.dims
  map f := Graded.Germ.hom posGerm (strandsEq f) (crossPerm rfl f)
  map_id a := by
    refine GradedHom.ext ?_
    change posGerm.val (crossPerm rfl (𝟙 a)) = 1
    rw [crossPerm_id]
    exact posGerm.val_one _
  map_comp {a b c} f g := by
    have hrec : (finCongr (strandsEq f)).permCongr (crossPerm (tgtStrands f rfl) g)
        = crossPerm rfl g := (crossPerm_recount (tgtStrands f rfl) rfl g).symm
    have h := Graded.Germ.hom_comp posGerm (M := PosBraid) (strandsEq f) (strandsEq g)
      (σ := crossPerm rfl f) (τ := crossPerm (tgtStrands f rfl) g)
      (crossPerm_noDoubleCross rfl f g)
    rw [hrec] at h
    refine Eq.trans ?_ h.symm
    refine GradedHom.ext ?_
    change posGerm.val (crossPerm rfl (f ≫ g)) = posGerm.val _
    rw [crossPerm_comp rfl f g]

@[simp] theorem posGrade_map {a b : Ch Zbp} (f : a ⟶ b) :
    posGrade.map f = Graded.Germ.hom posGerm (strandsEq f) (crossPerm rfl f) := rfl

/-- **A merge performs nothing** — it crosses nothing, and the trivial simple is the degree
identification. -/
theorem posGrade_map_of_W {a b : Ch Zbp} {f : a ⟶ b} (hf : W Zbp f) :
    posGrade.map f = Graded.ofDeg (strandsEq f) := by
  rw [posGrade_map, (W_iff_crossPerm_eq_one rfl f).mp hf]
  exact Graded.Germ.hom_one_eq_ofDeg posGerm (strandsEq f)

theorem posGrade_inverts : (W Zbp).IsInvertedBy posGrade := fun _ _ f hf => by
  rw [posGrade_map_of_W hf]
  exact Graded.isIso_ofDeg _

theorem posGradeOp_inverts : ((W Zbp).op).IsInvertedBy posGrade.op := fun _ _ f hf => by
  haveI := posGrade_inverts f.unop hf
  exact inferInstanceAs (IsIso (posGrade.map f.unop).op)

/-! ## The braid a loop at the run performs -/

/-- The braid grading, on the localization: the merges are inverted, so it descends. -/
noncomputable def posGradeLoc : ((W Zbp).op).Localization ⥤ (FullPosBraid)ᵒᵖ :=
  Localization.Construction.lift posGrade.op posGradeOp_inverts

theorem posGradeLoc_map_Q {x y : (Ch Zbp)ᵒᵖ} (f : x ⟶ y) :
    posGradeLoc.map (((W Zbp).op).Q.map f) = posGrade.op.map f :=
  Category.id_comp _

/-! ## Every chain is its run

The merge out of the run is inverted, so it becomes an isomorphism — the workhorse for everything
below. -/

/-- The merge into the run, in the localization. -/
noncomputable def runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    ((W Zbp).op).Q.obj (op b) ⟶ ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) :=
  ((W Zbp).op).Q.map (runMerge b hb).op

instance isIso_runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    IsIso (runArrow b hb) := isIso_Q_op_of_W (W_runMerge b hb)

/-- **A chain is its own run in the localization** — the merge out of the run is inverted. -/
noncomputable def runIso {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    ((W Zbp).op).Q.obj (op b) ≅ ((W Zbp).op).Q.obj (op (zObj (𝟙^N))) :=
  asIso (runArrow b hb)

/-- **The strand count is constant along the localization** — the grading's morphisms carry their
degree equality. -/
theorem strandsEq_loc {a b : Ch Zbp}
    (f : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b)) :
    dimSum b.dims = dimSum a.dims :=
  (posGradeLoc.map f).unop.deg

/-- **…so chains of different strand counts are not connected**, even after inverting. -/
theorem isEmpty_loc_hom {a b : Ch Zbp} (h : dimSum a.dims ≠ dimSum b.dims) :
    IsEmpty (((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b)) :=
  ⟨fun f => h (strandsEq_loc f).symm⟩

/-- **The loops at the run of `N` events**, multiplied in composition order — `End` multiplies
backwards, so the `ᵐᵒᵖ` is what makes `x * y = x ≫ y`. -/
abbrev RunLoops (N : ℕ) : Type :=
  (@End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))))ᵐᵒᵖ

/-- Transport a positive braid along an equality of strand counts. -/
def posBraidCongr {m n : ℕ} (h : m = n) : PosBraid m ≃* PosBraid n := by
  subst h; exact MulEquiv.refl _

theorem posBraidCongr_posPerm {m n : ℕ} (h : m = n) (σ : Perm (Fin m)) :
    posBraidCongr h (posPerm σ) = posPerm ((finCongr h).permCongr σ) := by
  subst h
  exact congrArg posPerm (Equiv.ext fun _ => rfl)

/-- **The braid a loop at the run performs**, in composition order. -/
noncomputable def runGrade (N : ℕ) : RunLoops N →* PosBraid N where
  toFun x := posBraidCongr (dimSum_replicate N) (posGradeLoc.map x.unop).unop.val
  map_one' := by
    change posBraidCongr (dimSum_replicate N)
      (posGradeLoc.map (𝟙 (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))))).unop.val = 1
    rw [CategoryTheory.Functor.map_id]
    exact map_one _
  map_mul' x y := by
    change posBraidCongr (dimSum_replicate N)
      (posGradeLoc.map (x.unop ≫ y.unop)).unop.val = _
    rw [CategoryTheory.Functor.map_comp]
    exact map_mul _ _ _

/-! ### The grade of a loop is its crossing permutation

The two merges `conj` conjugates by are degree identifications, so only the middle factor
survives. -/

private theorem ofDeg_comp_ofDeg_symm {M : ℕ → Type*} [∀ n, Monoid (M n)] {m n : ℕ} (h : m = n) :
    (Graded.ofDeg h.symm : @Quiver.Hom (Graded M) _ n m) ≫ Graded.ofDeg h
      = @CategoryStruct.id (Graded M) _ n := by
  subst h; exact GradedHom.ext (one_mul _)

private theorem val_comp_ofDeg {M : ℕ → Type*} [∀ n, Monoid (M n)] {m n p : ℕ}
    (x : @Quiver.Hom (Graded M) _ m n) (h : n = p) : (x ≫ Graded.ofDeg h).val = x.val := by
  obtain ⟨hd, v⟩ := x
  subst hd
  subst h
  exact one_mul _

/-- **The braid a loop at the run performs is the simple of its crossing permutation.** -/
theorem runGrade_runLoop (N : ℕ) (σ : Perm (Fin N)) :
    runGrade N (MulOpposite.op (runLoop N σ)) = posPerm σ := by
  set g : zObj (𝟙^N) ⟶ zObj (topDims N) := (onesTopEquiv N).symm σ with hgdef
  have hb : dimSum (zObj (topDims N)).dims = N := tgtStrands g (dimSum_replicate N)
  haveI := isIso_Q_op_of_W (W_runMerge (zObj (topDims N)) hb)
  have hconj : runLoop N σ
      = inv (((W Zbp).op).Q.map (runMerge (zObj (topDims N)) hb).op)
          ≫ ((W Zbp).op).Q.map g.op := by
    rw [runLoop, conj, show runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ from endo_eq_id _,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hu : posGradeLoc.map (((W Zbp).op).Q.map (runMerge (zObj (topDims N)) hb).op)
      = Quiver.Hom.op (Graded.ofDeg (strandsEq (runMerge (zObj (topDims N)) hb))) := by
    rw [posGradeLoc_map_Q]
    exact congrArg Quiver.Hom.op (posGrade_map_of_W (W_runMerge (zObj (topDims N)) hb))
  have hinv : posGradeLoc.map (inv (((W Zbp).op).Q.map (runMerge (zObj (topDims N)) hb).op))
      = Quiver.Hom.op (Graded.ofDeg (strandsEq (runMerge (zObj (topDims N)) hb)).symm) := by
    rw [CategoryTheory.Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [hu]
    exact Quiver.Hom.unop_inj (ofDeg_comp_ofDeg_symm (M := PosBraid) _)
  change posBraidCongr (dimSum_replicate N) (posGradeLoc.map (runLoop N σ)).unop.val = posPerm σ
  rw [hconj, CategoryTheory.Functor.map_comp, hinv, posGradeLoc_map_Q]
  change posBraidCongr (dimSum_replicate N)
    (posGrade.map g ≫ Graded.ofDeg (strandsEq (runMerge (zObj (topDims N)) hb)).symm).val
      = posPerm σ
  rw [val_comp_ofDeg]
  change posBraidCongr (dimSum_replicate N) (posPerm (crossPerm rfl g)) = posPerm σ
  rw [posBraidCongr_posPerm]
  exact congrArg posPerm
    ((crossPerm_recount rfl (dimSum_replicate N) g).symm.trans
      (hgdef ▸ crossPerm_onesTopEquiv_symm N σ))

/-- **The grade of any refinement's loop is its crossing permutation.** -/
theorem runGrade_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    runGrade N (MulOpposite.op (conj ha f)) = posPerm (crossPerm ha f) := by
  rw [conj_eq_runLoop ha f, runGrade_runLoop]

/-! ## A positive braid, read as a loop -/

theorem runLoop_adjT (N : ℕ) (k : Fin (N - 1)) : runLoop N (adjT k) = atomLoop N k := by
  rw [atomLoop, conj_eq_runLoop, crossPerm_atomOnes]

/-- **A positive braid, as a loop at the run** — only the atom relations are asked, and
`runLoop_mul_adjT` is exactly them. -/
noncomputable def runBraid (N : ℕ) : PosBraid N →* RunLoops N :=
  PosBraid.liftAtom (fun σ => MulOpposite.op (runLoop N σ))
    (congrArg MulOpposite.op (runLoop_one N))
    fun β i hlen => by
      change MulOpposite.op (runLoop N β ≫ runLoop N (adjT i))
        = MulOpposite.op (runLoop N (β * adjT i))
      rw [runLoop_adjT, ← runLoop_mul_adjT (ascent_of_permLen_mul_adjT hlen)]
      rfl

@[simp] theorem runBraid_posPerm (N : ℕ) (σ : Perm (Fin N)) :
    runBraid N (posPerm σ) = MulOpposite.op (runLoop N σ) := rfl

/-- **The grading retracts**: reading a positive braid as a loop and grading it back changes
nothing. -/
theorem runGrade_comp_runBraid (N : ℕ) :
    (runGrade N).comp (runBraid N) = MonoidHom.id (PosBraid N) :=
  posPerm_ext fun σ => runGrade_runLoop N σ

theorem runBraid_injective (N : ℕ) : Function.Injective (runBraid N) :=
  Function.LeftInverse.injective (g := runGrade N) fun β => by
    rw [← MonoidHom.comp_apply, runGrade_comp_runBraid, MonoidHom.id_apply]

/-! ## The loops are exhausted

Every arrow of the localization is a composite of refinements and inverted merges; conjugating each
step to the run turns the composite into a product of `conj`s, and a merge conjugates to the
identity. -/

/-- Conjugated to the run, an arrow of the localization is a positive braid. -/
private def genProp (N : ℕ) : MorphismProperty (((W Zbp).op).Localization) := fun X Y g =>
  ∀ (b a : Ch Zbp) (hb : dimSum b.dims = N) (ha : dimSum a.dims = N)
    (hX : ((W Zbp).op).Q.obj (op b) = X) (hY : ((W Zbp).op).Q.obj (op a) = Y),
    (MulOpposite.op (inv (runArrow b hb) ≫ eqToHom hX ≫ g ≫ eqToHom hY.symm ≫ runArrow a ha) :
      RunLoops N) ∈ MonoidHom.mrange (runBraid N)

private theorem mem_mrange_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    (MulOpposite.op (conj ha f) : RunLoops N) ∈ MonoidHom.mrange (runBraid N) :=
  ⟨posPerm (crossPerm ha f), by rw [runBraid_posPerm, conj_eq_runLoop]⟩

private instance genProp_comp (N : ℕ) : (genProp N).IsStableUnderComposition where
  comp_mem {X Y Z} g₁ g₂ h₁ h₂ := by
    intro b a hb ha hX hZ
    set c : Ch Zbp := ((Localization.Construction.objEquiv ((W Zbp).op)).symm Y).unop with hcdef
    have hY : ((W Zbp).op).Q.obj (op c) = Y := by
      rw [hcdef, Opposite.op_unop]
      exact (Localization.Construction.objEquiv ((W Zbp).op)).right_inv Y
    have hc : dimSum c.dims = N :=
      ((posGradeLoc.map (eqToHom hX ≫ g₁ ≫ eqToHom hY.symm)).unop.deg).trans hb
    have hsplit :
        inv (runArrow b hb) ≫ eqToHom hX ≫ (g₁ ≫ g₂) ≫ eqToHom hZ.symm ≫ runArrow a ha
          = (inv (runArrow b hb) ≫ eqToHom hX ≫ g₁ ≫ eqToHom hY.symm ≫ runArrow c hc)
            ≫ (inv (runArrow c hc) ≫ eqToHom hY ≫ g₂ ≫ eqToHom hZ.symm ≫ runArrow a ha) := by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
    rw [hsplit]
    exact Submonoid.mul_mem _ (h₁ b c hb hc hX hY) (h₂ c a hc ha hY hZ)

private theorem genProp_Q (N : ℕ) : ∀ ⦃x y : (Ch Zbp)ᵒᵖ⦄ (f : x ⟶ y),
    genProp N (((W Zbp).op).Q.map f) := by
  intro x y f b a hb ha hX hY
  obtain rfl : x = op b := ((Localization.Construction.objEquiv ((W Zbp).op)).injective hX).symm
  obtain rfl : y = op a := ((Localization.Construction.objEquiv ((W Zbp).op)).injective hY).symm
  simp only [eqToHom_refl, Category.id_comp]
  have hval : inv (runArrow b hb) ≫ ((W Zbp).op).Q.map f ≫ runArrow a ha = conj ha f.unop := rfl
  rw [hval]
  exact mem_mrange_conj ha f.unop

private theorem genProp_wInv (N : ℕ) : ∀ ⦃x y : (Ch Zbp)ᵒᵖ⦄ (w : x ⟶ y) (hw : ((W Zbp).op) w),
    genProp N (Localization.Construction.wInv w hw) := by
  intro x y w hw b a hb ha hX hY
  obtain rfl : y = op b := ((Localization.Construction.objEquiv ((W Zbp).op)).injective hX).symm
  obtain rfl : x = op a := ((Localization.Construction.objEquiv ((W Zbp).op)).injective hY).symm
  have hone : inv (runArrow a ha) ≫ ((W Zbp).op).Q.map w ≫ runArrow b hb = 𝟙 _ :=
    conj_eq_id hb (show W Zbp w.unop from hw)
  have h1 : ((W Zbp).op).Q.map w ≫ runArrow b hb = runArrow a ha := by
    have h2 := congrArg (fun t => runArrow a ha ≫ t) hone
    simpa using h2
  have hIH : Localization.Construction.wInv w hw ≫ ((W Zbp).op).Q.map w = 𝟙 _ :=
    (Localization.Construction.wIso w hw).inv_hom_id
  have hkey : inv (runArrow b hb) ≫ Localization.Construction.wInv w hw ≫ runArrow a ha
      = 𝟙 _ := by
    rw [← h1, ← Category.assoc (Localization.Construction.wInv w hw), hIH, Category.id_comp,
      IsIso.inv_hom_id]
  simp only [eqToHom_refl, Category.id_comp]
  rw [hkey]
  exact one_mem _

/-- **The loops at a run are exactly the positive braids.** -/
theorem runBraid_surjective (N : ℕ) : Function.Surjective (runBraid N) := by
  have htop : genProp N = ⊤ :=
    Localization.Construction.morphismProperty_eq_top (genProp N) (genProp_Q N) (genProp_wInv N)
  intro x
  have hx : genProp N x.unop := by rw [htop]; exact MorphismProperty.top_apply _
  obtain ⟨β, hβ⟩ := hx (zObj (𝟙^N)) (zObj (𝟙^N)) (dimSum_replicate N) (dimSum_replicate N) rfl rfl
  have hid : runArrow (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ := by
    rw [runArrow, show runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ from endo_eq_id _]
    exact CategoryTheory.Functor.map_id _ _
  have hinvid : inv (runArrow (zObj (𝟙^N)) (dimSum_replicate N)) = 𝟙 _ :=
    IsIso.inv_eq_of_hom_inv_id (by rw [Category.comp_id]; exact hid)
  refine ⟨β, hβ.trans (congrArg MulOpposite.op ?_)⟩
  rw [hinvid, hid]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **The loops at the run of `N` events are the positive braid monoid** — the grading is the
inverse, so the presentation of `PosBraid N` is a presentation of them. -/
noncomputable def runBraidEquiv (N : ℕ) : PosBraid N ≃* RunLoops N :=
  MulEquiv.ofBijective (runBraid N) ⟨runBraid_injective N, runBraid_surjective N⟩

/-- **The loops at the run are the Artin monoid on `N−1` generators** — the same monoid named by
its presentation.  `Machinery/Braid/Matsumoto` supplies the comparison; nothing above uses it. -/
noncomputable def runArtinEquiv (N : ℕ) : ArtinPosBraid N ≃* RunLoops N :=
  (posBraid_equiv_artinPos N).symm.trans (runBraidEquiv N)

theorem runGrade_runBraid (N : ℕ) (β : PosBraid N) : runGrade N (runBraid N β) = β := by
  rw [← MonoidHom.comp_apply, runGrade_comp_runBraid, MonoidHom.id_apply]

theorem runBraid_runGrade (N : ℕ) (x : RunLoops N) : runBraid N (runGrade N x) = x := by
  obtain ⟨β, rfl⟩ := runBraid_surjective N x
  rw [runGrade_runBraid]

theorem runBraidEquiv_symm (N : ℕ) (x : RunLoops N) :
    (runBraidEquiv N).symm x = runGrade N x :=
  (MulEquiv.symm_apply_eq _).mpr (runBraid_runGrade N x).symm

/-! ## The whole localization, on the shapes themselves

The localization is identity on objects, so its objects are still the shapes.  Conjugating both
ends by `runIso` reads every hom-set as `PosBraid N`, compatibly with composition and with `conj`;
`isEmpty_loc_hom` says the strand count is the only thing separating the components. -/

/-- **A hom-set of the localization is the positive braid monoid** — conjugate both ends to the
run. -/
noncomputable def homEquivPosBraid {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) :
    (((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b)) ≃ PosBraid N :=
  ((runIso a ha).homCongr (runIso b hb)).trans
    (MulOpposite.opEquiv.trans (runBraidEquiv N).toEquiv.symm)

theorem homEquivPosBraid_apply {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N)
    (f : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b)) :
    homEquivPosBraid ha hb f
      = runGrade N (MulOpposite.op (inv (runArrow a ha) ≫ f ≫ runArrow b hb)) :=
  runBraidEquiv_symm N _

/-- **Composition is multiplication.** -/
theorem homEquivPosBraid_comp {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (hc : dimSum c.dims = N)
    (f : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b))
    (g : ((W Zbp).op).Q.obj (op b) ⟶ ((W Zbp).op).Q.obj (op c)) :
    homEquivPosBraid ha hc (f ≫ g)
      = homEquivPosBraid ha hb f * homEquivPosBraid hb hc g := by
  have hsplit : inv (runArrow a ha) ≫ (f ≫ g) ≫ runArrow c hc
      = (inv (runArrow a ha) ≫ f ≫ runArrow b hb)
        ≫ (inv (runArrow b hb) ≫ g ≫ runArrow c hc) := by
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [homEquivPosBraid_apply, homEquivPosBraid_apply, homEquivPosBraid_apply, hsplit]
  exact map_mul (runGrade N) _ _

@[simp] theorem homEquivPosBraid_id {N : ℕ} {a : Ch Zbp} (ha : dimSum a.dims = N) :
    homEquivPosBraid ha ha (𝟙 _) = 1 := by
  rw [homEquivPosBraid_apply, Category.id_comp, IsIso.inv_hom_id]
  exact map_one (runGrade N)

/-- **…and on a refinement it is the crossing permutation** — the equivalence extends `conj`, so
nothing new is named. -/
theorem homEquivPosBraid_Q {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (f : a ⟶ b) :
    homEquivPosBraid hb ha (((W Zbp).op).Q.map f.op) = posPerm (crossPerm ha f) := by
  rw [homEquivPosBraid_apply]
  exact runGrade_conj ha f

/-- **Undoing a merge performs nothing**: an arrow absorbed by the merge `m` into the common target
of `t` performs `t`'s crossing.  This is the one computation a codimension-one step ever needs — the
square that witnesses it has an atom leg `t` and a merge leg `m`. -/
theorem homEquivPosBraid_of_merge {N : ℕ} {a b e : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (he : dimSum e.dims = N) {m : b ⟶ e} (hm : W Zbp m) {t : a ⟶ e}
    {f : ((W Zbp).op).Q.obj (op b) ⟶ ((W Zbp).op).Q.obj (op a)}
    (h : ((W Zbp).op).Q.map m.op ≫ f = ((W Zbp).op).Q.map t.op) :
    homEquivPosBraid hb ha f = posPerm (crossPerm ha t) := by
  have h1 : homEquivPosBraid he hb (((W Zbp).op).Q.map m.op) = 1 := by
    rw [homEquivPosBraid_Q hb he m, crossPerm_eq_one_of_W hb hm, posPerm_one]
  rw [← one_mul (homEquivPosBraid hb ha f), ← h1, ← homEquivPosBraid_comp he hb ha, h,
    homEquivPosBraid_Q ha he t]

/-- The merge out of the run into itself is the identity. -/
theorem runArrow_ones (N : ℕ) : runArrow (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ := by
  rw [runArrow, show runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ from endo_eq_id _, op_id]
  exact CategoryTheory.Functor.map_id _ _

theorem inv_runArrow_ones (N : ℕ) :
    inv (runArrow (zObj (𝟙^N)) (dimSum_replicate N)) = 𝟙 _ :=
  IsIso.inv_eq_of_hom_inv_id (by rw [Category.comp_id, runArrow_ones])

/-- **A loop at the run performs its own crossing permutation** — nothing to conjugate. -/
theorem homEquivPosBraid_runLoop (N : ℕ) (σ : Perm (Fin N)) :
    homEquivPosBraid (dimSum_replicate N) (dimSum_replicate N) (runLoop N σ) = posPerm σ := by
  rw [homEquivPosBraid_apply, inv_runArrow_ones, runArrow_ones, Category.id_comp, Category.comp_id]
  exact runGrade_runLoop N σ

/-- **An isomorphism performs nothing** — `PosBraid N` has no non-trivial units. -/
theorem homEquivPosBraid_eq_one_of_isIso {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (f : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b))
    (hf : IsIso f) : homEquivPosBraid ha hb f = 1 := by
  haveI := hf
  refine eq_one_of_mul_eq_one (b := homEquivPosBraid hb ha (inv f)) ?_
  rw [← homEquivPosBraid_comp ha hb ha, IsIso.hom_inv_id, homEquivPosBraid_id]

/-- **Isomorphisms on either side do not change the braid** — the shape every comparison of two
readings of the localization produces.  The `IsIso` witnesses are explicit: the object spellings a
comparison functor produces are not the ones instance search matches. -/
theorem homEquivPosBraid_sandwich {N : ℕ} {a b a' b' : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (ha' : dimSum a'.dims = N) (hb' : dimSum b'.dims = N)
    (u : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op a')) (hu : IsIso u)
    (f : ((W Zbp).op).Q.obj (op a') ⟶ ((W Zbp).op).Q.obj (op b'))
    (v : ((W Zbp).op).Q.obj (op b') ⟶ ((W Zbp).op).Q.obj (op b)) (hv : IsIso v) :
    homEquivPosBraid ha hb (u ≫ f ≫ v) = homEquivPosBraid ha' hb' f := by
  rw [homEquivPosBraid_comp ha ha' hb, homEquivPosBraid_comp ha' hb' hb,
    homEquivPosBraid_eq_one_of_isIso ha ha' u hu, homEquivPosBraid_eq_one_of_isIso hb' hb v hv,
    one_mul, mul_one]

end ChainCat
