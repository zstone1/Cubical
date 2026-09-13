import CubeChains.Concurrency.Presentation.LocPresentation
import CubeChains.Machinery.Graded
import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Machinery.Localization.HomInduction

/-!
# Concurrency/Presentation/Retraction — `Ch Zbp` with the bead merges inverted

The crossing permutations are a length-additive cocycle, so `posGerm` turns them into a functor
`Ch Zbp ⥤ FullPosBraid` inverting the merges (`posGrade`), hence into a map on the localization
that retracts `runLoop`.  `runLoop` generates, so the two are inverse (`runBraidEquiv`).

`ᵐᵒᵖ` is the composition order: `End` multiplies backwards, and `x * y = x ≫ y` only after `op`.
-/

open CategoryTheory Equiv Opposite BPSet CubeChains CubeChain

namespace ChainCat

set_option quotPrecheck false in
/-- The localization functor of the base. -/
local notation "Qz" => ((W Zbp).op).Q

/-! ## The braid a refinement performs -/

/-- **The positive braid a refinement performs** — its crossing permutation, as a germ simple. -/
def posGrade : Ch Zbp ⥤ FullPosBraid where
  obj a := dimSum a.dims
  map f := Graded.Germ.hom posGerm (dimSum_eq_of_hom f) (crossPerm rfl f)
  map_id a := by
    refine GradedHom.ext ?_
    change posGerm.val (crossPerm rfl (𝟙 a)) = 1
    rw [crossPerm_id]
    exact posGerm.val_one _
  map_comp {a b c} f g := by
    have hrec : (finCongr (dimSum_eq_of_hom f)).permCongr (crossPerm (tgtStrands f rfl) g)
        = crossPerm rfl g := (crossPerm_recount (tgtStrands f rfl) rfl g).symm
    have h := Graded.Germ.hom_comp posGerm (M := PosBraid) (dimSum_eq_of_hom f) (dimSum_eq_of_hom g)
      (σ := crossPerm rfl f) (τ := crossPerm (tgtStrands f rfl) g)
      (crossPerm_noDoubleCross rfl f g)
    rw [hrec] at h
    refine Eq.trans ?_ h.symm
    refine GradedHom.ext ?_
    change posGerm.val (crossPerm rfl (f ≫ g)) = posGerm.val _
    rw [crossPerm_comp rfl f g]

@[simp] theorem posGrade_map {a b : Ch Zbp} (f : a ⟶ b) :
    posGrade.map f = Graded.Germ.hom posGerm (dimSum_eq_of_hom f) (crossPerm rfl f) := rfl

/-- **A merge performs nothing** — it crosses nothing, and the trivial simple is the degree
identification. -/
theorem posGrade_map_of_W {a b : Ch Zbp} {f : a ⟶ b} (hf : W Zbp f) :
    posGrade.map f = Graded.ofDeg (dimSum_eq_of_hom f) := by
  rw [posGrade_map, (W_iff_crossPerm_eq_one rfl f).mp hf]
  exact Graded.Germ.hom_one_eq_ofDeg posGerm (dimSum_eq_of_hom f)

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
    posGradeLoc.map ((Qz).map f) = posGrade.op.map f :=
  Category.id_comp _

/-- **The merge out of a run grades to the degree identification** — it crosses nothing. -/
theorem posGradeLoc_runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    posGradeLoc.map (runArrow b hb)
      = Quiver.Hom.op (Graded.ofDeg (dimSum_eq_of_hom (runMerge b hb))) :=
  (posGradeLoc_map_Q _).trans
    (congrArg Quiver.Hom.op (posGrade_map_of_W (W_runMerge b hb)))

/-- …and so does its inverse. -/
theorem posGradeLoc_inv_runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    posGradeLoc.map (inv (runArrow b hb))
      = Quiver.Hom.op (Graded.ofDeg (dimSum_eq_of_hom (runMerge b hb)).symm) := by
  rw [CategoryTheory.Functor.map_inv]
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [posGradeLoc_runArrow]
  exact Quiver.Hom.unop_inj
    (Graded.isoOfDeg (M := PosBraid) (dimSum_eq_of_hom (runMerge b hb))).inv_hom_id

/-! ## Every chain is its run

The merge out of the run is inverted, so it becomes an isomorphism — the workhorse for everything
below (`runIso`, in `LocPresentation`). -/

/-- **The strand count is constant along the localization** — every refinement preserves it and a
formal inverse reverses the equation, so no grading is needed to see it. -/
theorem strandsEq_loc {a b : Ch Zbp} (f : (Qz).obj (op a) ⟶ (Qz).obj (op b)) :
    dimSum b.dims = dimSum a.dims :=
  Localization.Construction.hom_induction ((W Zbp).op)
    (fun x y _ => dimSum y.unop.dims = dimSum x.unop.dims)
    (fun _ _ _ _ _ hg hg' => hg'.trans hg)
    (fun f => dimSum_eq_of_hom f.unop)
    (fun w _ => (dimSum_eq_of_hom w.unop).symm) f

/-- **The loops at the run of `N` events**, multiplied in composition order — `End` multiplies
backwards, so the `ᵐᵒᵖ` is what makes `x * y = x ≫ y`. -/
abbrev RunLoops (N : ℕ) : Type :=
  (@End (((W Zbp).op).Localization) _ ((Qz).obj (op (zObj (𝟙^N)))))ᵐᵒᵖ

/-- **The braid a loop at the run performs**, in composition order. -/
noncomputable def runGrade (N : ℕ) : RunLoops N →* PosBraid N where
  toFun x := Graded.congrDeg (dimSum_replicate N) (posGradeLoc.map x.unop).unop.val
  map_one' := by
    change Graded.congrDeg (dimSum_replicate N)
      (posGradeLoc.map (𝟙 ((Qz).obj (op (zObj (𝟙^N)))))).unop.val = 1
    rw [CategoryTheory.Functor.map_id]
    exact map_one _
  map_mul' x y := by
    change Graded.congrDeg (dimSum_replicate N)
      (posGradeLoc.map (x.unop ≫ y.unop)).unop.val = _
    rw [CategoryTheory.Functor.map_comp]
    exact map_mul _ _ _

/-- **The braid a loop at the run performs is the simple of its crossing permutation.** -/
theorem runGrade_runLoop (N : ℕ) (σ : Perm (Fin N)) :
    runGrade N (MulOpposite.op (runLoop N σ)) = posPerm σ := by
  set g : zObj (𝟙^N) ⟶ zObj (topDims N) := (onesTopEquiv N).symm σ with hgdef
  have hb : dimSum (zObj (topDims N)).dims = N := dimSum_topDims N
  change Graded.congrDeg (dimSum_replicate N) (posGradeLoc.map (runLoop N σ)).unop.val = posPerm σ
  rw [runLoop, conj_ones hb g, show (runIso (zObj (topDims N)) hb).inv
      = inv (runArrow (zObj (topDims N)) hb) from rfl,
    CategoryTheory.Functor.map_comp, posGradeLoc_inv_runArrow, posGradeLoc_map_Q]
  change Graded.congrDeg (dimSum_replicate N) (posGrade.map g
    ≫ Graded.ofDeg (dimSum_eq_of_hom (runMerge (zObj (topDims N)) hb)).symm).val = posPerm σ
  rw [show (posGrade.map g
      ≫ Graded.ofDeg (dimSum_eq_of_hom (runMerge (zObj (topDims N)) hb)).symm).val
      = (posGrade.map g).val from by
    rw [Graded.val_comp, Graded.ofDeg_val, map_one, one_mul]]
  change Graded.congrDeg (dimSum_replicate N) (posPerm (crossPerm rfl g)) = posPerm σ
  rw [congrDeg_posPerm]
  exact congrArg posPerm
    ((crossPerm_recount rfl (dimSum_replicate N) g).symm.trans
      (hgdef ▸ crossPerm_onesTopEquiv_symm N σ))

/-! ## A positive braid, read as a loop -/

/-- **A positive braid, as a loop at the run** — only the atom relations are asked, and
`runLoop_mul_adjT` is exactly them. -/
noncomputable def runBraid (N : ℕ) : PosBraid N →* RunLoops N :=
  PosBraid.liftAtom (fun σ => MulOpposite.op (runLoop N σ))
    (congrArg MulOpposite.op (runLoop_one N))
    fun β i hlen => by
      change MulOpposite.op (runLoop N β ≫ runLoop N (adjT i))
        = MulOpposite.op (runLoop N (β * adjT i))
      exact congrArg MulOpposite.op (runLoop_comp (ascent_of_permLen_mul_adjT hlen))

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

Every arrow of the localization is a composite of refinements and inverted merges; `runConjEquiv` is
multiplicative (`Iso.homCongr_comp`), a refinement conjugates to its crossing permutation, and an
inverted merge conjugates to nothing.  The localization keeps the objects *on the nose*, so the
conjugation is written at the chain an object already is and no endpoint is transported. -/

/-- **An inverted merge conjugates to nothing** — cancel it against the merge, which does. -/
theorem runConjEquiv_wInv {N : ℕ} {x y : (Ch Zbp)ᵒᵖ} (w : x ⟶ y) (hw : ((W Zbp).op) w)
    (hy : dimSum y.unop.dims = N) (hx : dimSum x.unop.dims = N) :
    runConjEquiv hy hx (Localization.Construction.wInv w hw) = 𝟙 _ := by
  have hone : inv (runArrow x.unop hx) ≫ (Qz).map w ≫ runArrow y.unop hy = 𝟙 _ :=
    conj_eq_id hy (show W Zbp w.unop from hw)
  have h1 : (Qz).map w ≫ runArrow y.unop hy = runArrow x.unop hx := by
    have h2 := congrArg (fun t => runArrow x.unop hx ≫ t) hone
    simpa using h2
  have hIH : Localization.Construction.wInv w hw ≫ (Qz).map w = 𝟙 _ :=
    (Localization.Construction.wIso w hw).inv_hom_id
  change inv (runArrow y.unop hy) ≫ Localization.Construction.wInv w hw
    ≫ runArrow x.unop hx = 𝟙 _
  rw [← h1, ← Category.assoc (Localization.Construction.wInv w hw), hIH, Category.id_comp,
    IsIso.inv_hom_id]

/-- **The loops at a run are exactly the positive braids** — every arrow of the localized base
conjugates to one, and a loop at the run conjugates to itself. -/
theorem runBraid_surjective (N : ℕ) : Function.Surjective (runBraid N) := by
  have key : ∀ {x y : (Ch Zbp)ᵒᵖ} (g : (Qz).obj x ⟶ (Qz).obj y)
      (hx : dimSum x.unop.dims = N) (hy : dimSum y.unop.dims = N),
      MulOpposite.op (runConjEquiv hx hy g) ∈ MonoidHom.mrange (runBraid N) := by
    refine Localization.Construction.hom_induction ((W Zbp).op)
      (fun x y g => ∀ (hx : dimSum x.unop.dims = N) (hy : dimSum y.unop.dims = N),
        MulOpposite.op (runConjEquiv hx hy g) ∈ MonoidHom.mrange (runBraid N))
      (fun x y z g g' hg hg' hx hz => ?_)
      (fun f hx hy => ⟨posPerm (crossPerm hy f.unop),
        congrArg MulOpposite.op (conj_eq_runLoop hy f.unop).symm⟩)
      (fun w hw hy hx => by rw [runConjEquiv_wInv w hw hy hx]; exact one_mem _)
    have hy : dimSum y.unop.dims = N := (strandsEq_loc g).trans hx
    have hsplit : runConjEquiv hx hz (g ≫ g') = runConjEquiv hx hy g ≫ runConjEquiv hy hz g' :=
      Iso.homCongr_comp (runIso x.unop hx) (runIso y.unop hy) (runIso z.unop hz) g g'
    rw [show MulOpposite.op (runConjEquiv hx hz (g ≫ g'))
        = MulOpposite.op (runConjEquiv hx hy g) * MulOpposite.op (runConjEquiv hy hz g') from
      congrArg MulOpposite.op hsplit]
    exact Submonoid.mul_mem _ (hg hx hy) (hg' hy hz)
  intro t
  obtain ⟨β, hβ⟩ := key (x := op (zObj (𝟙^N))) (y := op (zObj (𝟙^N))) t.unop
    (dimSum_replicate N) (dimSum_replicate N)
  refine ⟨β, hβ.trans (congrArg MulOpposite.op ?_)⟩
  change inv (runArrow (zObj (𝟙^N)) (dimSum_replicate N)) ≫ t.unop
      ≫ runArrow (zObj (𝟙^N)) (dimSum_replicate N) = t.unop
  rw [inv_runArrow_ones, runArrow_ones, Category.id_comp, Category.comp_id]

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

end ChainCat
