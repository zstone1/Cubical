import CubeChains.Concurrency.Presentation.SimpleSupport
import CubeChains.Concurrency.Presentation.BrCube
import CubeChains.Concurrency.Presentation.BrBase

/-!
# Concurrency/Presentation/GarsideCells — the Garside generators, and what they remember

The **hand-written** Garside presentation of `Ch(H□ⁿ)[W⁻¹]` is the germ presentation of the braid
monoid acting on the runs (`germActionPresentation`): 0-cells the `n!` runs, 1-cells a run with a
simple, 2-cells the germ relations there.

`Br germBP (Hbp □ⁿ)` agrees on the 0-cells (`ιRun_bijective`) and not on the 1-cells: a simple
is crossed in the one-bead chart, and there the run it was crossed above is remembered
(`SimpleSupport`), so a simple that mixes all `n` events names **two** 1-cells between one pair of
0-cells — naming one arrow (`arrow_straightCell_eq_crossedCell`), so a redundant generating set.
Already at the base (`straightLoopZ_ne_crossedLoopZ`): no feature of the cube.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Equiv

namespace ChainCat

/-! ## The one-bead chart above a run

`atomComp n k` is the codimension-one chart the `k`-th atom is crossed in; `topDims n` is the
chart *every* simple is crossed in, and `topWitness` is the chart above a given run there. -/

/-- The merge from the run into the one bead. -/
noncomputable def mergeTop (n : ℕ) : zObj (𝟙^n) ⟶ zObj (topDims n) :=
  runMerge (zObj (topDims n)) (dimSum_topDims n)

theorem W_mergeTop (n : ℕ) : W Zbp (mergeTop n) := W_runMerge _ _

theorem onesTopEquiv_symm_one (n : ℕ) : (onesTopEquiv n).symm 1 = mergeTop n :=
  eq_runMerge (dimSum_topDims n)
    ((W_iff_crossPerm_eq_one _ _).mpr (crossPerm_onesTopEquiv_symm n 1))

/-- **A simple's loop is its own two legs** — the one-bead refinement, then the merge inverted;
`atomLoop_eq_legs` at an arbitrary simple. -/
theorem runLoop_eq_legs (n : ℕ) (σ : Perm (Fin n)) :
    runLoop n σ = @inv _ _ _ _ _ (isIso_Q_op_of_W (W_mergeTop n))
      ≫ ((W Zbp).op).Q.map ((onesTopEquiv n).symm σ).op := by
  have hrun : runMerge (zObj (𝟙^n)) (dimSum_replicate n) = 𝟙 _ := endo_eq_id _
  rw [runLoop, conj, hrun, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

section Cube

variable {n : ℕ}

/-- **The one-bead chart above a run** — the run, un-merged into a single bead.  Nothing is
chosen: the merge is inverted in the localized base. -/
noncomputable def topWitness (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) : ⋁(topDims n) ⟶ Hbp.obj (□n) :=
  haveI := isIso_Q_op_of_W (W_mergeTop n)
  (hFibre n).map (inv (((W Zbp).op).Q.map (mergeTop n).op)) z

/-- **Each leg of the one-bead chart restricts to the run its simple acts to.** -/
theorem onesTop_topWitness (σ : Perm (Fin n)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    ((onesTopEquiv n).symm σ).φ ≫ topWitness z = (hFibre n).map (runLoop n σ) z := by
  haveI := isIso_Q_op_of_W (W_mergeTop n)
  rw [runLoop_eq_legs, (hFibre n).map_comp_apply, hFibre_map_Q]
  rfl

/-- **…and the merge leg restricts to the run itself.** -/
theorem mergeTop_topWitness (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    (mergeTop n).φ ≫ topWitness z = z := by
  have h := onesTop_topWitness (1 : Perm (Fin n)) z
  rw [onesTopEquiv_symm_one, runLoop_one, (hFibre n).map_id_apply] at h
  exact h

/-- **A simple's loop acts on the runs by its own permutation** — `runFibreEquiv_runBraid` at a
simple. -/
theorem runFibreEquiv_runLoop (σ : Perm (Fin n)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    runFibreEquiv n ((hFibre n).map (runLoop n σ) z) = σ⁻¹ * runFibreEquiv n z := by
  have h := runFibreEquiv_runBraid (posPerm σ) z
  rwa [show ((runBraid n (posPerm σ)).unop) = runLoop n σ from
    congrArg MulOpposite.unop (runBraid_posPerm n σ), posPermHom_posPerm] at h

end Cube

/-! ## A simple's 1-cell in the one-bead copy -/

/-- **The 0-cell of the one-bead copy a run over it names** — the run its own leg restricts the
chart to. -/
theorem ιV_topRunAt (p : BraidPresentation) (K : BPSet) {n : ℕ}
    (X : ⋁(topDims n) ⟶ K) (σ : Perm (Fin n)) :
    ιV K p.fam (op ⟨op (zObj (topDims n)), X⟩) (p.runPt (topRunAt n σ))
      = p.ιRun K (((onesTopEquiv n).symm σ).φ ≫ X) :=
  (congrArg (ιV K p.fam (op ⟨op (zObj (topDims n)), X⟩))
      (p.famV_runPt ((onesTopEquiv n).symm σ) (runAtSelf n)).symm).trans
    (ιV_leg K p.fam (eltLeg K ((onesTopEquiv n).symm σ) X) (p.runPt (runAtSelf n)))

/-- **A simple is crossed above every run its length allows** — length-additivity is the whole
condition, and the one bead realises it. -/
theorem action_topRunAt_eq {n : ℕ} (ρ σ ν : Perm (Fin n)) (hν : ν = ρ * σ)
    (h : permLen ρ + permLen σ = permLen ν) :
    (sliceActionAt (zObj (topDims n)) n (posPerm σ)).unop.val (some (topRunAt n ρ))
      = some (topRunAt n ν) :=
  (sliceActionAt_posPerm_iff σ _ _).mpr
    ⟨by rw [perm_topRunAt, perm_topRunAt, hν], by rw [perm_topRunAt, perm_topRunAt]; exact h⟩

theorem action_topRunAt_mul {n : ℕ} (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) :
    (sliceActionAt (zObj (topDims n)) n (posPerm σ)).unop.val (some (topRunAt n ρ))
      = some (topRunAt n (ρ * σ)) :=
  action_topRunAt_eq ρ σ (ρ * σ) rfl h

/-- **The 1-cell a simple names in the one-bead copy**, above the run `ρ` of that copy.  The slice
polygraph is the base's reversed, so the cell runs crossing-to-run. -/
noncomputable def germTopRaw (K : BPSet) {n : ℕ} (X : ⋁(topDims n) ⟶ K) (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) :
    ιV K germBP.fam (op ⟨op (zObj (topDims n)), X⟩) (germBP.runPt (topRunAt n (ρ * σ)))
      ⟶ ιV K germBP.fam (op ⟨op (zObj (topDims n)), X⟩) (germBP.runPt (topRunAt n ρ)) :=
  ιE K germBP.fam (op ⟨op (zObj (topDims n)), X⟩)
    (germBP.runGen σ (action_topRunAt_mul ρ σ h))

/-- …read at the runs of `K` its two legs restrict the chart to. -/
noncomputable def germTopCell (K : BPSet) {n : ℕ} (X : ⋁(topDims n) ⟶ K) (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) :
    germBP.ιRun K (((onesTopEquiv n).symm (ρ * σ)).φ ≫ X)
      ⟶ germBP.ιRun K (((onesTopEquiv n).symm ρ).φ ≫ X) :=
  Quiver.homOfEq (germTopRaw K X ρ σ h)
    (ιV_topRunAt germBP K X (ρ * σ)) (ιV_topRunAt germBP K X ρ)

/-! ## What the 1-cell remembers -/

theorem crossOver_sliceCellOver_runPt (p : BraidPresentation) {d : Ch Zbp} {N : ℕ}
    (hd : dimSum d.dims = N) (u : RunAt d N) :
    crossOver hd (sliceCellOver (p.runPt u)) = u.perm := by
  rw [p.sliceCellOver_runPt u]
  rfl

/-- **A prefunctor into a one-object quiver ignores a transport of the endpoints.** -/
theorem map_homOfEq_const {V : Type*} [Quiver V] {T : Type*}
    (φ : V ⥤q GenObj (fun _ _ : PUnit.{1} => T)) {a a' b b' : V}
    (g : a ⟶ b) (hx : a = a') (hy : b = b') :
    φ.map (Quiver.homOfEq g hx hy) = φ.map g := by
  subst hx; subst hy; rfl

/-- **The one-bead cell remembers its own run.** -/
theorem sepCells_germTopRaw (K : BPSet) {n : ℕ} (X : ⋁(topDims n) ⟶ K) (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) (hmix : Mixes σ) :
    (sepCells K germBP σ hmix).map (germTopRaw K X ρ σ h) = some ρ := by
  have hc : dimSum (eltBase (wedgeHoms K) (op ⟨op (zObj (topDims n)), X⟩)).dims = n :=
    dimSum_topDims n
  have hA : crossOver hc (sliceCellOver (germBP.runPt (topRunAt n ρ))) = ρ :=
    (crossOver_sliceCellOver_runPt germBP _ (topRunAt n ρ)).trans (perm_topRunAt n ρ)
  have hB : crossOver hc (sliceCellOver (germBP.runPt (topRunAt n (ρ * σ)))) = ρ * σ :=
    (crossOver_sliceCellOver_runPt germBP _ (topRunAt n (ρ * σ))).trans (perm_topRunAt n (ρ * σ))
  rw [germTopRaw, sepCells_ιE, sepVal, dif_pos hc]
  simp only [hA, hB]
  rw [if_pos (by rw [← mul_assoc, inv_mul_cancel, one_mul])]

theorem sepCells_germTopCell (K : BPSet) {n : ℕ} (X : ⋁(topDims n) ⟶ K) (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) (hmix : Mixes σ) :
    (sepCells K germBP σ hmix).map (germTopCell K X ρ σ h) = some ρ := by
  rw [germTopCell, map_homOfEq_const]
  exact sepCells_germTopRaw K X ρ σ h hmix

/-! ## The braid a one-bead cell performs

`chBraid_runGen` reads a cell whose source run is uncrossed.  A cell above a *crossed* run is that
one with the crossing itself appended, inside a single copy — where the localized slice is a poset,
so the composite is the cell it has to be — and `eq_posPerm_of_posLen` divides the answer out. -/

@[simp] theorem germBP_perm {N : ℕ} {x y : (germBP.P N).V} (σ : (germBP.P N).Gen x y) :
    germBP.perm σ = σ := posPermHom_posPerm σ

/-- Composing two transported images is transporting the composite — the eqToHom algebra, stated
where the categories are variables so that `simp` can see the compositions. -/
theorem conj_comp_of_eq {C : Type*} [Category C] {D : Type*} [Category D] (F : D ⥤ C)
    {A B E : C} {A' B' E' : D} (hA : A = F.obj A') (hB : B = F.obj B') (hE : E = F.obj E')
    (u : A' ⟶ B') (v : B' ⟶ E') (w : A' ⟶ E') (huv : u ≫ v = w) :
    (eqToHom hA ≫ F.map u ≫ eqToHom hB.symm) ≫ (eqToHom hB ≫ F.map v ≫ eqToHom hE.symm)
      = eqToHom hA ≫ F.map w ≫ eqToHom hE.symm := by
  subst hA; subst hB; subst hE; subst huv
  simp

/-- **Cells of one copy compose as their slice arrows do** — the localized slice is a poset, so
there is nothing to choose. -/
theorem arrow_ιE_comp (p : BraidPresentation) (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b e : (p.fam.obj (eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩)
    (g' : (⟨b⟩ : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨e⟩)
    (g'' : (⟨a⟩ : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨e⟩) :
    (p.presentsBr K).arrow (ιE K p.fam c g) ≫ (p.presentsBr K).arrow (ιE K p.fam c g')
      = (p.presentsBr K).arrow (ιE K p.fam c g'') := by
  have hslice : (slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g
      ≫ (slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g'
      = (slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g'' :=
    Subsingleton.elim _ _
  rw [p.arrow_ιE K c a b g, p.arrow_ιE K c b e g', p.arrow_ιE K c a e g'']
  exact conj_comp_of_eq
    (colimSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2
      ⋙ (locEquivElements K).inverse)
    (p.at_ιV K c a) (p.at_ιV K c b) (p.at_ιV K c e) _ _ _ hslice

section CubeBraid

variable {n : ℕ} (X : ⋁(topDims n) ⟶ Hbp.obj (□n))

/-- **A one-bead cell performs its own simple**, whatever the run it is crossed above. -/
theorem chBraid_germTopRaw (ρ σ : Perm (Fin n))
    (h : permLen ρ + permLen σ = permLen (ρ * σ)) :
    chBraid ((germBP.presentsBr (Hbp.obj (□n))).arrow (germTopRaw (Hbp.obj (□n)) X ρ σ h))
        (hbpStrands _) (hbpStrands _) = posPerm σ := by
  have hB0 : permLen (1 : Perm (Fin n)) + permLen ρ = permLen ρ := by
    rw [permLen_one, Nat.zero_add]
  have hA0 : permLen (1 : Perm (Fin n)) + permLen (ρ * σ) = permLen (ρ * σ) := by
    rw [permLen_one, Nat.zero_add]
  set c := (op ⟨op (zObj (topDims n)), X⟩ : ((wedgeHoms (Hbp.obj (□n))).Elements)ᵒᵖ) with hc
  have hcomp := arrow_ιE_comp germBP (Hbp.obj (□n)) c
    (germBP.runGen σ (action_topRunAt_mul ρ σ h))
    (germBP.runGen ρ (action_topRunAt_eq 1 ρ ρ (one_mul ρ).symm hB0))
    (germBP.runGen (ρ * σ) (action_topRunAt_eq 1 (ρ * σ) (ρ * σ) (one_mul _).symm hA0))
  have hA := germBP.chBraid_runGen (Hbp.obj (□n)) c (ρ * σ)
    (action_topRunAt_eq 1 (ρ * σ) (ρ * σ) (one_mul _).symm hA0) (perm_topRunAt n 1)
    (hbpStrands _) (hbpStrands _)
  have hB := germBP.chBraid_runGen (Hbp.obj (□n)) c ρ
    (action_topRunAt_eq 1 ρ ρ (one_mul ρ).symm hB0) (perm_topRunAt n 1)
    (hbpStrands _) (hbpStrands _)
  rw [germBP_perm] at hA hB
  have hkey : posPerm ρ * chBraid ((germBP.presentsBr (Hbp.obj (□n))).arrow
      (germTopRaw (Hbp.obj (□n)) X ρ σ h)) (hbpStrands _) (hbpStrands _) = posPerm (ρ * σ) := by
    rw [← hA, ← hcomp,
      chBraid_comp _ _ (hbpStrands _) (hbpStrands _) (hbpStrands _), hB]
    rfl
  set Xb := chBraid ((germBP.presentsBr (Hbp.obj (□n))).arrow
    (germTopRaw (Hbp.obj (□n)) X ρ σ h)) (hbpStrands _) (hbpStrands _) with hXb
  have hperm : posPermHom n Xb = σ := by
    have hh := congrArg (posPermHom n) hkey
    rw [map_mul, posPermHom_posPerm, posPermHom_posPerm] at hh
    exact mul_left_cancel hh
  have hlen : Multiplicative.toAdd (posLen n Xb) = permLen (posPermHom n Xb) := by
    have hh := congrArg (fun b => Multiplicative.toAdd (posLen n b)) hkey
    simp only [map_mul, toAdd_mul, posLen_posPerm, toAdd_ofAdd] at hh
    rw [hperm]
    omega
  rw [eq_posPerm_of_posLen hlen, hperm]

end CubeBraid

/-! ## The 0-cells are the runs

A 0-cell of `Br p K` is a run's (`exists_ιRun`), and at the decorated cube distinct runs give
distinct ones: the localized chains read as the chambers (`chToAction`), where `PosBraid n` has no
non-trivial units, so isomorphic run chains are equal.  This is the dimension in which the two
Garside polygraphs *do* agree. -/

/-- **A merge acts trivially on the chambers**, so the reading descends. -/
theorem chToAction_inverts (n : ℕ) : (W (Hbp.obj (□n))).IsInvertedBy (chToAction n) := by
  intro a b f hf
  have hcross : chainCross f = 1 := (W_iff_crossPerm_eq_one (hbpCubeStrands a.map) f).mp hf
  have hperm : chainPerm a = chainPerm b := by
    have h := chainCross_smul f
    rwa [hcross, one_mul] at h
  have hval : ((chToAction n).map f).val = (1 : PosBraid n) := by
    rw [chToAction_map_val, hcross, posPerm_one]
  have hinv : posPermHom n (1 : PosBraid n) * ActionCategory.back ((chToAction n).obj b)
      = ActionCategory.back ((chToAction n).obj a) := by
    rw [map_one, one_mul]
    exact hperm.symm
  have hmul : ∀ u v : PosBraid n, u = 1 → v = 1 → u * v = 1 := by
    intro u v hu hv; rw [hu, hv, one_mul]
  refine ⟨⟨⟨(1 : PosBraid n), hinv⟩, Subtype.ext ?_, Subtype.ext ?_⟩⟩
  · rw [ActionCategory.comp_val, ActionCategory.id_val]
    exact hmul _ _ rfl hval
  · rw [ActionCategory.comp_val, ActionCategory.id_val]
    exact hmul _ _ hval rfl

/-- **The localized chains of the decorated cube, read as the chambers.** -/
noncomputable def locToAction (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ⥤ PosBraidAction n :=
  Localization.Construction.lift (chToAction n) (chToAction_inverts n)

theorem locToAction_fac (n : ℕ) :
    (W (Hbp.obj (□n))).Q ⋙ locToAction n = chToAction n :=
  Localization.Construction.fac _ _

/-- **Isomorphic chambers are equal** — `PosBraid n` has no non-trivial units. -/
theorem eq_of_iso_posBraidAction {n : ℕ} {x y : PosBraidAction n} (α : x ≅ y) : x = y := by
  have key : ∀ u v : PosBraid n, u * v = 1 →
      posPermHom n u * ActionCategory.back x = ActionCategory.back y → x = y := by
    intro u v huv hu
    rw [eq_one_of_mul_eq_one huv, map_one, one_mul] at hu
    exact (ActionCategory.back_coe x).symm.trans
      ((congrArg (fun t : Equiv.Perm (Fin n) => (t : PosBraidAction n)) hu).trans
        (ActionCategory.back_coe y))
  refine key α.hom.val α.inv.val ?_ α.hom.2
  have hval := congrArg Subtype.val α.inv_hom_id
  rw [ActionCategory.comp_val] at hval
  exact hval.trans (ActionCategory.id_val y)

/-- **Distinct runs stay distinct in `Ch(H□ⁿ)[W⁻¹]`.** -/
theorem eq_of_locIso_runCh {n : ℕ} {z z' : ⋁(𝟙^n) ⟶ Hbp.obj (□n)}
    (α : (W (Hbp.obj (□n))).Q.obj (runCh z) ≅ (W (Hbp.obj (□n))).Q.obj (runCh z')) : z = z' := by
  have hobj : ∀ w : ⋁(𝟙^n) ⟶ Hbp.obj (□n),
      (locToAction n).obj ((W (Hbp.obj (□n))).Q.obj (runCh w)) = (chToAction n).obj (runCh w) :=
    fun w => Functor.congr_obj (locToAction_fac n) (runCh w)
  have h := eq_of_iso_posBraidAction ((locToAction n).mapIso α)
  rw [hobj z, hobj z'] at h
  exact (bijective_fibrePerm_ones n).1 (congrArg ActionCategory.back h)

theorem ιRun_injective (p : BraidPresentation) (n : ℕ) :
    Function.Injective (p.ιRun (Hbp.obj (□n)) (n := n)) := fun _ _ h =>
  eq_of_locIso_runCh ((p.ιRunIso (Hbp.obj (□n)) _).symm
    ≪≫ eqToIso (congrArg (p.presentsBr (Hbp.obj (□n))).at' h)
    ≪≫ p.ιRunIso (Hbp.obj (□n)) _)

theorem ιRun_surjective (p : BraidPresentation) (n : ℕ) :
    Function.Surjective (p.ιRun (Hbp.obj (□n)) (n := n)) := by
  intro A
  obtain ⟨c, w, hw⟩ := Polygraph.exists_colimit_ι_obj
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) p.fam) A
  obtain ⟨z, hz⟩ := p.exists_ιRun (Hbp.obj (□n)) c (hbpCubeStrands c.unop.2) w.as
  exact ⟨z, hz.symm.trans hw⟩

/-- **The 0-cells of `Br p (Hbp □ⁿ)` are the runs**, whatever the base presentation. -/
theorem ιRun_bijective (p : BraidPresentation) (n : ℕ) :
    Function.Bijective (p.ιRun (Hbp.obj (□n)) (n := n)) :=
  ⟨ιRun_injective p n, ιRun_surjective p n⟩

end ChainCat

/-! ## The hand-written Garside presentation

The braid monoid's germ presentation, acting on the runs.  No chart, no chain of `Zbp`, no Segal
condition enters: `Presents.elements` says a presented monoid presents its action category, and
`chainActionEquiv` says that category is `Ch(H□ⁿ)[W⁻¹]` — itself a corollary of the Artin
presentation, not of the descent. -/

namespace CubeChains

open ChainCat

/-- **The hand-written Garside polygraph of `Ch(H□ⁿ)[W⁻¹]`**: 0-cells the runs, 1-cells a run with
a simple, 2-cells the germ relations read there. -/
noncomputable def germActionPoly (n : ℕ) : Polygraph :=
  (germPresentation n).elementsPoly (permPresheaf n)

/-- **…presenting the positive braid action on the runs.** -/
noncomputable def germActionPresents (n : ℕ) :
    Presents (germActionPoly n) ((permPresheaf n).Elements) :=
  (germPresentation n).elements (permPresheaf n)

/-- **…that is, `Ch(H□ⁿ)[W⁻¹]`.** -/
noncomputable def germActionPresentation (n : ℕ) :
    Presents (germActionPoly n) (((W (Hbp.obj (□n))).Localization)ᵒᵖ) :=
  (germActionPresents n).transport
    ((opOpEquivalence ((permPresheaf n).Elements)).symm.trans
      (permPresheafElementsEquiv.trans (chainActionEquiv n).symm).op)

/-- **The 0-cells are the runs.** -/
def germActionV (n : ℕ) : (germActionPoly n).V ≃ Equiv.Perm (Fin n) where
  toFun x := x.2
  invFun σ := ⟨SingleObj.star (PosBraid n), σ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The two polygraphs present the same category**, read across the variance — so the surplus
generators of `Br germBP (Hbp □ⁿ)` are a redundant generating set and not a different category. -/
noncomputable def germActionEquivBr (n : ℕ) :
    (germActionPoly n).presented ≌ ((germBP.Br (Hbp.obj (□n))).presented)ᵒᵖ :=
  (germActionPresentation n).equiv.trans (germBP.presentsBr (Hbp.obj (□n))).equiv.symm.op

/-- **The 0-cells of the two Garside polygraphs biject** — both are the `n!` runs.  It is the one
dimension in which they agree. -/
noncomputable def germObEquiv (n : ℕ) :
    (germActionPoly n).V ≃ GenObj (germBP.Br (Hbp.obj (□n))).Gen :=
  (germActionV n).trans
    ((runFibreEquiv n).symm.trans (Equiv.ofBijective _ (ιRun_bijective germBP n)))

/-- The Garside simple a 1-cell of the hand-written polygraph carries. -/
def germActionSimple {n : ℕ} {z z' : (germActionPoly n).V} (e : (germActionPoly n).Gen z z') :
    Equiv.Perm (Fin n) := e.1

/-- **A 1-cell is its simple** — between one pair of runs there is at most one 1-cell per Garside
simple.  This is what `Br germBP (Hbp □ⁿ)` fails (`straightCell_ne_crossedCell`). -/
theorem germActionSimple_injective (n : ℕ) (z z' : (germActionPoly n).V) :
    Function.Injective (germActionSimple (n := n) (z := z) (z' := z')) :=
  fun _ _ h => Subtype.ext h

/-- **…and every simple is one** — the 1-cells out of a run are all `n!` simples. -/
theorem germActionSimple_surjective (n : ℕ) (z : (germActionPoly n).V)
    (σ : Equiv.Perm (Fin n)) :
    ∃ (z' : (germActionPoly n).V) (e : (germActionPoly n).Gen z z'), germActionSimple e = σ :=
  ⟨⟨SingleObj.star (PosBraid n), (permPresheaf n).map ((germPresentation n).arrow σ) z.2⟩,
    ⟨σ, rfl⟩, rfl⟩

/-! ## The three-cycle names two generators

At `n = 3` the two 3-cycles are the simples that **mix** all three events; each is crossed only in
the one-bead chart, and there the run it is crossed above is remembered.  So the same simple names
two 1-cells between one pair of 0-cells, and `germActionGen_injective` has no counterpart. -/

section Witness

/-- The three-cycle: the simple that mixes all three events. -/
def rot3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- …and the transposition that completes it to the longest element. -/
def swap3 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem mixes_rot3 : Mixes rot3 := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    first
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩

theorem addLen_one_rot3 : permLen (1 : Equiv.Perm (Fin 3)) + permLen rot3
    = permLen (1 * rot3) := by decide

theorem addLen_swap3_rot3 : permLen swap3 + permLen rot3 = permLen (swap3 * rot3) := by decide

theorem swap3_ne_one : swap3 ≠ 1 := by decide

/-- A run of the decorated cube, and the run one `swap3` above it. -/
noncomputable def wRun : ⋁(𝟙^3) ⟶ Hbp.obj (□3) := (runFibreEquiv 3).symm 1

noncomputable def wRun' : ⋁(𝟙^3) ⟶ Hbp.obj (□3) := (hFibre 3).map (runLoop 3 swap3) wRun

/-- **The two copies cross to the same run.** -/
theorem hFibre_rot3_eq :
    (hFibre 3).map (runLoop 3 (1 * rot3)) wRun'
      = (hFibre 3).map (runLoop 3 (swap3 * rot3)) wRun := by
  refine (runFibreEquiv 3).injective ?_
  rw [runFibreEquiv_runLoop, runFibreEquiv_runLoop, wRun', runFibreEquiv_runLoop, one_mul,
    mul_inv_rev, mul_assoc]

/-- The 0-cell both 1-cells run from — the run `rot3` is crossed to. -/
noncomputable def wSrc : GenObj (germBP.Br (Hbp.obj (□3))).Gen :=
  germBP.ιRun (Hbp.obj (□3)) ((hFibre 3).map (runLoop 3 (swap3 * rot3)) wRun)

/-- …and the one they run to. -/
noncomputable def wTgt : GenObj (germBP.Br (Hbp.obj (□3))).Gen :=
  germBP.ιRun (Hbp.obj (□3)) wRun'

/-- **`rot3` crossed above the uncrossed run of its own copy.** -/
noncomputable def straightCell : wSrc ⟶ wTgt :=
  Quiver.homOfEq (germTopCell (Hbp.obj (□3)) (topWitness wRun') 1 rot3 addLen_one_rot3)
    (congrArg (germBP.ιRun (Hbp.obj (□3)))
      ((onesTop_topWitness (1 * rot3) wRun').trans hFibre_rot3_eq))
    (congrArg (germBP.ιRun (Hbp.obj (□3)))
      ((congrArg (fun f : zObj (𝟙^3) ⟶ zObj (topDims 3) => f.φ ≫ topWitness wRun')
        (onesTopEquiv_symm_one 3)).trans (mergeTop_topWitness wRun')))

/-- **…and above the run `swap3` of the copy one crossing below.** -/
noncomputable def crossedCell : wSrc ⟶ wTgt :=
  Quiver.homOfEq (germTopCell (Hbp.obj (□3)) (topWitness wRun) swap3 rot3 addLen_swap3_rot3)
    (congrArg (germBP.ιRun (Hbp.obj (□3))) (onesTop_topWitness (swap3 * rot3) wRun))
    (congrArg (germBP.ιRun (Hbp.obj (□3))) (onesTop_topWitness swap3 wRun))

/-- **The Garside generators of `Br germBP (Hbp □³)` are not ⟨run, simple⟩**: one simple, one pair
of 0-cells, two 1-cells.  The copy a simple is crossed in remembers the run it was crossed above,
and a mixing simple has no coarser copy to forget it in.  Contrast the atoms, whose copy has a
unique run (`bijective_genQuiver`), and the hand-written `germActionPoly`, where a 1-cell **is** its
simple (`germActionGen_injective`). -/
theorem straightCell_ne_crossedCell : straightCell ≠ crossedCell := by
  intro hc
  have h : (sepCells (Hbp.obj (□3)) germBP rot3 mixes_rot3).map straightCell
      = (sepCells (Hbp.obj (□3)) germBP rot3 mixes_rot3).map crossedCell := by
    rw [hc]
  rw [straightCell, crossedCell, map_homOfEq_const, map_homOfEq_const,
    sepCells_germTopCell, sepCells_germTopCell] at h
  exact swap3_ne_one (Option.some_injective _ h).symm

/-! …yet they name **one arrow**: both perform the three-cycle, and the projection to the localized
base is faithful.  So the surplus generator is redundant — the two polygraphs present the same
category with different generating sets, not different categories. -/

theorem chBraid_straightCell :
    chBraid ((germBP.presentsBr (Hbp.obj (□3))).arrow straightCell)
        (hbpStrands _) (hbpStrands _) = posPerm rot3 := by
  rw [straightCell, Presents.arrow_homOfEq]
  refine (chBraid_eqToHom_sandwich _ _ _ (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans ?_
  rw [germTopCell, Presents.arrow_homOfEq]
  refine (chBraid_eqToHom_sandwich _ _ _ (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans ?_
  exact chBraid_germTopRaw (topWitness wRun') 1 rot3 addLen_one_rot3

theorem chBraid_crossedCell :
    chBraid ((germBP.presentsBr (Hbp.obj (□3))).arrow crossedCell)
        (hbpStrands _) (hbpStrands _) = posPerm rot3 := by
  rw [crossedCell, Presents.arrow_homOfEq]
  refine (chBraid_eqToHom_sandwich _ _ _ (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans ?_
  rw [germTopCell, Presents.arrow_homOfEq]
  refine (chBraid_eqToHom_sandwich _ _ _ (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans ?_
  exact chBraid_germTopRaw (topWitness wRun) swap3 rot3 addLen_swap3_rot3

/-- **Two generators, one arrow.**  `Br germBP (Hbp □³)` carries a redundant Garside generating
set: the two 1-cells are distinct cells of the polygraph and the same morphism of
`Ch(H□³)[W⁻¹]`. -/
theorem arrow_straightCell_eq_crossedCell :
    (germBP.presentsBr (Hbp.obj (□3))).arrow straightCell
      = (germBP.presentsBr (Hbp.obj (□3))).arrow crossedCell :=
  eq_of_chBraid_eq (isSegal_H_of_symFree_repr (symFreeCube 3)) (N := 3)
    (hbpStrands _) (hbpStrands _) (chBraid_straightCell.trans chBraid_crossedCell.symm)

/-! ## …and already at the base

`Zbp` has one chart per chain, so the whole one-bead copy sits at the strand count's single 0-cell
(`ιV_topLeg`) and the two cells are parallel with nothing to construct.  So `brZMap` is not a
bijection of 1-cells for `germBP`, and the surplus is not a feature of the cube. -/

/-- **`rot3` crossed above the uncrossed run of the base's one-bead copy.** -/
noncomputable def straightLoopZ :
    germBP.ιRun Zbp (zRun 3) ⟶ germBP.ιRun Zbp (zRun 3) :=
  Quiver.homOfEq (germTopRaw (n := 3) Zbp (zObj (topDims 3)).map 1 rot3 addLen_one_rot3)
    (germBP.ιV_topLeg (N := 3) (1 * rot3)) (germBP.ιV_topLeg (N := 3) 1)

/-- **…and above the run `swap3` of that same copy.** -/
noncomputable def crossedLoopZ :
    germBP.ιRun Zbp (zRun 3) ⟶ germBP.ιRun Zbp (zRun 3) :=
  Quiver.homOfEq (germTopRaw (n := 3) Zbp (zObj (topDims 3)).map swap3 rot3 addLen_swap3_rot3)
    (germBP.ιV_topLeg (N := 3) (swap3 * rot3)) (germBP.ιV_topLeg (N := 3) swap3)

/-- **At the base a Garside simple already names two generators**, between one pair of 0-cells —
`germBP`'s own polygraph has one letter per simple, so `brZMap` duplicates. -/
theorem straightLoopZ_ne_crossedLoopZ : straightLoopZ ≠ crossedLoopZ := by
  intro hc
  have h : (sepCells Zbp germBP rot3 mixes_rot3).map straightLoopZ
      = (sepCells Zbp germBP rot3 mixes_rot3).map crossedLoopZ := by rw [hc]
  rw [straightLoopZ, crossedLoopZ, map_homOfEq_const, map_homOfEq_const,
    sepCells_germTopRaw, sepCells_germTopRaw] at h
  exact swap3_ne_one (Option.some_injective _ h).symm

end Witness

end CubeChains
