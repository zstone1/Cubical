import CubeChains.Braid.PosAction
import CubeChains.Foundations.ElementsAction
import CubeChains.Chains.ElementsFibration
import CubeChains.Salvetti.HSegal
import CubeChains.Salvetti.SymReorient

/-!
# Salvetti/HPosAction — `Ch (H □ⁿ)` localized at the merges is the positive braid action

`Ch (Hbp □ⁿ)` is the category of elements of `wedgeHoms (Hbp □ⁿ)` over `Ch Zbp`, and the merges
are invertible on the fibre (`invertsMerges_Hbp_cube`), so localizing it only localizes the base —
whose localization is `FullPosBraid`.  A chain of `Hbp □ⁿ` has `dimSum = n`, so only the degree-`n`
component carries a fibre, and there the fibre is the orderings of the `n` axes: `fibrePerm` reads
the step at which each axis is performed, and a refinement shifts it by its crossing permutation.
-/

open CategoryTheory Opposite BPSet CubeChains StdCube CategoryTheory.Localization

namespace CubeChains

variable {n : ℕ}

/-! ### A decorated cell is a symmetric cube map

`cellDir` reads an `H`-cell as an `SBox` map `▪m ⟶ ▪n` and returns its `pos`.  Restriction along a
`Box` face is then precomposition there, so the axis a step performs never changes — only which
step performs it. -/

/-- Restricting a decorated cell of `□ⁿ` is precomposition in `SBox`. -/
theorem sHomEquiv_symm_Hbp_map {k m : ℕ} (f : ▫k ⟶ ▫m)
    (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) :
    sHomEquiv.symm ((Hbp.obj (□n)).toPsh.map f.op p) = J.map f ≫ sHomEquiv.symm p := by
  have key : symHom (SHom.sortPerm (J.map f) p.1) ≫ J.map (SHom.sortFace (J.map f) p.1)
      = J.map f ≫ symHom p.1 := SHom.symm_sortPerm_sortFace (J.map f) p.1
  show symHom (SHom.sortPerm (J.map f) p.1) ≫ J.map (SHom.sortFace (J.map f) p.1 ≫ p.2)
      = J.map f ≫ symHom p.1 ≫ J.map p.2
  rw [J.map_comp, ← Category.assoc, ← key]
  exact (Category.assoc _ _ _).symm

theorem cellDir_Hbp_map {k m : ℕ} (f : ▫k ⟶ ▫m) (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n))
    (j : Fin k) :
    cellDir ((Hbp.obj (□n)).toPsh.map f.op p) j = cellDir p (faceEmb f j) := by
  change SHom.pos (sHomEquiv.symm ((Hbp.obj (□n)).toPsh.map f.op p)) j = _
  rw [sHomEquiv_symm_Hbp_map]
  exact SBox.comp_pos (J.map f) (sHomEquiv.symm p) j

/-! ### The direction an event performs -/

/-- **The events of a decorated chain of `□ⁿ` are its axes**: each bead's own order, followed by
the underlying chain's coordinate bijection. -/
def eventDirEquiv {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : beadEvent d ≃ Fin n :=
  (Equiv.sigmaCongrRight fun i => (bead d α i).1).trans (coordFlip (und (□n) α))

@[simp] theorem eventDirEquiv_mk {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length)
    (j : Fin (d.get i : ℕ)) : eventDirEquiv α ⟨i, j⟩ = beadDir α i j :=
  coordFlip_und α i j

/-- **A refinement relabels events, not directions**: an event of `φ ≫ α` performs the axis `α`
performs at its image. -/
theorem eventDirEquiv_comp {a d : List ℕ+} (φ : ⋁a ⟶ ⋁d) (α : ⋁d ⟶ Hbp.obj (□n))
    (e : beadEvent a) : eventDirEquiv (φ ≫ α) e = eventDirEquiv α (coordMap φ e) := by
  obtain ⟨i, j⟩ := e
  rw [eventDirEquiv_mk, coordMap_eq, eventDirEquiv_mk]
  show cellDir (bead a (φ ≫ α) i) j = _
  rw [bead_comp_block, cellDir_Hbp_map]
  rfl

/-! ### The fibre: the order in which the axes are run -/

open ChainCat in
/-- **The order a decorated chain of `□ⁿ` runs its axes in**: axis `q` is performed at the step
`fibrePerm hA α q`. -/
def fibrePerm {A : Ch Zbp} (hA : dimSum A.dims = n) (α : ⋁A.dims ⟶ Hbp.obj (□n)) :
    Equiv.Perm (Fin n) :=
  ((eventDirEquiv α).symm.trans (strand A)).trans (finCongr hA)

open ChainCat in
/-- **A refinement shifts the order by its crossing permutation** — the whole content of the
fibre being the positive braid action. -/
theorem fibrePerm_comp {A B : Ch Zbp} (hA : dimSum A.dims = n) (hB : dimSum B.dims = n)
    (f : A ⟶ B) (α : ⋁B.dims ⟶ Hbp.obj (□n)) :
    fibrePerm hA (f.φ ≫ α) = (crossPermAt hA f)⁻¹ * fibrePerm hB α := by
  refine Equiv.ext fun q => ?_
  set e : beadEvent A.dims := (eventDirEquiv (f.φ ≫ α)).symm q with he
  have h2 : (eventDirEquiv α).symm q = coordMap f.φ e := by
    refine (Equiv.symm_apply_eq _).2 ?_
    rw [← eventDirEquiv_comp, he, Equiv.apply_symm_apply]
  have key : crossPermAt hA f (fibrePerm hA (f.φ ≫ α) q) = fibrePerm hB α q := by
    show crossPermAt hA f (finCongr hA (strand A e))
      = finCongr hB (strand B ((eventDirEquiv α).symm q))
    rw [h2, ← finCongr_crossPerm f e]
    exact Fin.ext rfl
  rw [Equiv.Perm.mul_apply]
  exact Equiv.Perm.eq_inv_iff_eq.2 key

/-! ### The fibre is the orderings

The merge out of the all-edges chain is invertible on the fibre and crosses nothing, so every
`n`-strand chain has the same fibre as the run of `n` edges — where `runHbpCubeEquivPerm` already
says it is `Perm (Fin n)`. -/

/-- Forgetting the order leaves a chain of `□ⁿ`, whose events are the `n` coordinates. -/
theorem dimSum_of_hbpCubeHom {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : dimSum d = n :=
  wedgeDimSum_eq (und (□n) α)

/-- **A run of the decorated cube is a wedge map out of the `n` edges.** -/
def onesHomEquivRunHbp (n : ℕ) : (⋁(𝟙^n) ⟶ Hbp.obj (□n)) ≃ Run (Hbp.obj (□n)) :=
  onesHomEquivRun fun α => dimSum_of_hbpCubeHom α

/-- On an all-edges chain each bead's order is trivial, so the events *are* the axes. -/
theorem eventDirEquiv_ones {d : List ℕ+} (hd : ∀ x ∈ d, x = 1) (β : ⋁d ⟶ Hbp.obj (□n)) :
    eventDirEquiv β = coordFlip (und (□n) β) := by
  refine Equiv.ext fun e => ?_
  obtain ⟨i, j⟩ := e
  have hsub : Subsingleton (Fin ((d.get i : ℕ+) : ℕ)) := by
    rw [show ((d.get i : ℕ+) : ℕ) = 1 from congrArg PNat.val (hd _ (List.get_mem d i))]
    infer_instance
  rw [eventDirEquiv_mk]
  exact (coordFlip_und β i j).symm.trans
    (congrArg (coordFlip (und (□n) β)) (congrArg (Sigma.mk i) (Subsingleton.elim _ _)))

/-- **On a run the fibre order is the run's own step order.** -/
theorem fibrePerm_ones (β : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n) β
      = runHbpCubeEquivPerm n (onesHomEquivRunHbp n β) := by
  have h : eventDirEquiv β = coordFlip (und (□n) β) :=
    eventDirEquiv_ones (fun _ hx => List.eq_of_mem_replicate hx) β
  refine Equiv.ext fun q => Fin.ext ?_
  have hq : (eventDirEquiv β).symm q = (coordFlip (und (□n) β)).symm q := by rw [h]
  show (pos ((eventDirEquiv β).symm q) : ℕ) = _
  rw [hq]
  rfl

theorem bijective_fibrePerm_ones (n : ℕ) :
    Function.Bijective (fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n)) := by
  rw [show (fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n))
      = (runHbpCubeEquivPerm n) ∘ (onesHomEquivRunHbp n) from funext fibrePerm_ones]
  exact (runHbpCubeEquivPerm n).bijective.comp (onesHomEquivRunHbp n).bijective

open ChainCat in
/-- **Every `n`-strand chain has the orderings for its fibre.** -/
theorem bijective_fibrePerm (A : ChZn n) : Function.Bijective (fibrePerm A.property) := by
  obtain ⟨u, hu⟩ := exists_WinfN_from_ones A
  have hbij : Function.Bijective (fun β : ⋁A.obj.dims ⟶ Hbp.obj (□n) => u.hom.φ ≫ β) :=
    (isIso_iff_bijective _).mp (invertsMerges_Hbp_cube n u.hom.op hu)
  have hone : crossPermAt (dimSum_replicate n) u.hom = 1 := crossPermN_eq_one_of_WinfN hu
  have heq : fibrePerm A.property
      = (fibrePerm (A := zObj (𝟙^n)) (dimSum_replicate n)) ∘
        (fun β : ⋁A.obj.dims ⟶ Hbp.obj (□n) => u.hom.φ ≫ β) := by
    refine funext fun β => ?_
    have hstep := fibrePerm_comp (dimSum_replicate n) A.property u.hom β
    rw [hone, inv_one, one_mul] at hstep
    exact hstep.symm
  rw [heq]
  exact (bijective_fibrePerm_ones n).comp hbij

/-- **The fibre of `Ch (Hbp □ⁿ)` over an `n`-strand chain: the orderings of its axes.** -/
noncomputable def fibreEquiv (A : ChainCat.ChZn n) :
    (⋁A.obj.dims ⟶ Hbp.obj (□n)) ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (bijective_fibrePerm A)

end CubeChains

namespace ChainCat

variable {n : ℕ}

/-! ### The degree-`n` component of the localized serial wedges -/

/-- The degree-`n` component of the localized serial wedges: one object, `PosBraid n` on it. -/
noncomputable def degreeIncl (n : ℕ) :
    (SingleObj (PosBraid n))ᵒᵖ ⥤ ((Winf Zbp).op).Localization :=
  (Graded.single n).op ⋙ locFullOpEquiv.inverse

instance (n : ℕ) : (degreeIncl n).Full :=
  inferInstanceAs (((Graded.single n).op ⋙ locFullOpEquiv.inverse).Full)

instance (n : ℕ) : (degreeIncl n).Faithful :=
  inferInstanceAs (((Graded.single n).op ⋙ locFullOpEquiv.inverse).Faithful)

/-! ### The orderings, as a `PosBraid n`-set -/

/-- The presheaf on the degree-`n` component carried by the orderings: `β` restricts by
`posPermHom β⁻¹`, the variance `(∫ -)ᵒᵖ` needs. -/
abbrev permPresheaf (n : ℕ) : (SingleObj (PosBraid n))ᵒᵖ ⥤ Type :=
  invActionPresheaf (Equiv.Perm (Fin n)) (posPermHom n)

/-- **`(∫ permPresheaf)ᵒᵖ` is the positive braid action.** -/
def permPresheafElementsEquiv : (((permPresheaf n).Elements)ᵒᵖ) ≌ PosBraidAction n :=
  elementsOpEquivActionCategory _ _ fun _ _ => rfl

/-! ### The comparison -/

/-- Only the degree-`n` component of the localized base carries a fibre. -/
private theorem degreeIncl_cover (n : ℕ) (c : ((Winf Zbp).op).Localization)
    (x : (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)).obj c) :
    ∃ d, Nonempty ((degreeIncl n).obj d ≅ c) := by
  haveI := Localization.essSurj ((Winf Zbp).op).Q ((Winf Zbp).op)
  obtain ⟨b, ⟨e⟩⟩ : ∃ b, Nonempty (((Winf Zbp).op).Q.obj b ≅ c) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ c⟩⟩
  have hty : (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)).obj
      (((Winf Zbp).op).Q.obj b) = (wedgeHoms (Hbp.obj (□n))).obj b :=
    Functor.congr_obj (Localization.Construction.fac (wedgeHoms (Hbp.obj (□n)))
      (invertsMerges_Hbp_cube n)) b
  have hα : (wedgeHoms (Hbp.obj (□n))).obj b :=
    hty ▸ (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)).map e.inv x
  have hdim : dimSum (unop b).dims = n := dimSum_of_hbpCubeHom hα
  refine ⟨op (SingleObj.star (PosBraid n)), ⟨?_⟩⟩
  have hq : locFullOpEquiv.functor.obj (((Winf Zbp).op).Q.obj b) ≅ ((chPos Zbp).op).obj b :=
    (Localization.qCompEquivalenceFromModelFunctorIso ((chPos Zbp).op) ((Winf Zbp).op)).app b
  have hdeg : ((Graded.single n).op.obj (op (SingleObj.star (PosBraid n))) : FullPosBraidᵒᵖ)
      = ((chPos Zbp).op).obj b := congrArg op hdim.symm
  exact locFullOpEquiv.inverse.mapIso (eqToIso hdeg ≪≫ hq.symm) ≪≫
    (locFullOpEquiv.unitIso.app (((Winf Zbp).op).Q.obj b)).symm ≪≫ e

/-! ### The fibre presheaf, descended

`chPosN n` localizes the degree-`n` component, so the fibre presheaf descends by uniqueness of
lifts: it is enough to identify it *before* localizing, which is `fibrePerm_comp`. -/

/-- **The fibre presheaf on the degree-`n` component is the `PosBraid n`-set of orderings.** -/
noncomputable def fibreNatIso (n : ℕ) :
    (StrandCount n).ι.op ⋙ wedgeHoms (Hbp.obj (□n)) ≅ (chPosN n).op ⋙ permPresheaf n :=
  NatIso.ofComponents (fun A => (fibreEquiv A.unop).toIso)
    fun {_ _} g => by ext α; exact fibrePerm_comp _ _ g.unop.hom α

/-- The model `(chPos Zbp)ᵒᵖ` of the localized serial wedges, transported back. -/
private noncomputable def qOpIso :
    (chPos Zbp).op ⋙ locFullOpEquiv.inverse ≅ ((Winf Zbp).op).Q :=
  (Functor.isoWhiskerRight
      (Localization.qCompEquivalenceFromModelFunctorIso ((chPos Zbp).op) ((Winf Zbp).op))
      locFullOpEquiv.inverse).symm ≪≫
    Functor.isoWhiskerLeft ((Winf Zbp).op).Q locFullOpEquiv.unitIso.symm

/-- `degreeIncl` is the degree-`n` component's own localization functor. -/
private noncomputable def degreeInclQIso (n : ℕ) :
    (chPosN n).op ⋙ degreeIncl n ≅ (StrandCount n).ι.op ⋙ ((Winf Zbp).op).Q :=
  Functor.isoWhiskerRight (NatIso.op (chPosNIso n)).symm locFullOpEquiv.inverse ≪≫
    Functor.isoWhiskerLeft ((StrandCount n).ι.op) qOpIso

/-- **The descended fibre is the `PosBraid n`-set of orderings.** -/
noncomputable def degreeInclFibreIso (n : ℕ) :
    degreeIncl n ⋙ wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)
      ≅ permPresheaf n := by
  haveI := chPosN_isLocalization n
  have liftIso : (chPosN n).op ⋙
        (degreeIncl n ⋙ wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n))
      ≅ (StrandCount n).ι.op ⋙ wedgeHoms (Hbp.obj (□n)) :=
    Functor.isoWhiskerRight (degreeInclQIso n)
        (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)) ≪≫
      eqToIso (congrArg (fun F => (StrandCount n).ι.op ⋙ F)
        (Localization.Construction.fac (wedgeHoms (Hbp.obj (□n))) (invertsMerges_Hbp_cube n)))
  haveI : Localization.Lifting ((chPosN n).op) ((WinfN n).op)
      ((StrandCount n).ι.op ⋙ wedgeHoms (Hbp.obj (□n)))
      (degreeIncl n ⋙ wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)) := ⟨liftIso⟩
  exact Localization.liftNatIso ((chPosN n).op) ((WinfN n).op)
    ((StrandCount n).ι.op ⋙ wedgeHoms (Hbp.obj (□n)))
    ((chPosN n).op ⋙ permPresheaf n) _ (permPresheaf n) (fibreNatIso n)

/-- **`Ch (Hbp □ⁿ)` localized at the bead merges is the positive braid action**: objects the
orderings of the strands, arrows the positive braids realising the change of ordering. -/
noncomputable def localizationEquivPosBraidAction (n : ℕ) :
    (Winf (Hbp.obj (□n))).Localization ≌ PosBraidAction n := by
  haveI : (chDescent (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)).IsLocalization
      (Winf (Hbp.obj (□n))) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre
      (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n))
      (degreeIncl n)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (degreeIncl_cover n)
  exact (Localization.uniq (Winf (Hbp.obj (□n))).Q
      (chDescent (Hbp.obj (□n)) (invertsMerges_Hbp_cube n)) (Winf (Hbp.obj (□n)))).trans
    ((((CategoryOfElements.pre (wedgeHomsDescend (Hbp.obj (□n)) (invertsMerges_Hbp_cube n))
        (degreeIncl n)).asEquivalence.symm.op).trans
      ((CategoryOfElements.mapEquivalence (degreeInclFibreIso n)).op)).trans
      permPresheafElementsEquiv)

/-- **The loops of the localization are the positive pure braids**: an ordering returns to itself
only along a braid that returns every strand to its own position. -/
noncomputable def endEquivPosPureOfLocalization (n : ℕ)
    (X : (Winf (Hbp.obj (□n))).Localization) : End X ≃* PosPureBraid n :=
  ((localizationEquivPosBraidAction n).fullyFaithfulFunctor.mulEquivEnd X).trans
    (endEquivPosPure _)

end ChainCat
