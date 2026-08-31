import CubeChains.Machinery.Braid.PosAction
import CubeChains.Machinery.Localization.ElementsAction
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Complexification.HSegal
import CubeChains.Concurrency.Complexification.SymReorient

/-!
# Concurrency/Complexification/HPosAction — `Ch (H □ⁿ)` localized at the merges is the positive
braid action

Every chain of `Hbp □ⁿ` fires `n` events, so `Ch (Hbp □ⁿ)` is the category of elements of
`wedgeHoms (Hbp □ⁿ)` over the **strand-`n` component** of `Ch Zbp` — one strand count, no grading.
The merges are invertible on the fibre (`isSegal_H_cube`), so localizing only localizes that
component, whose localization is `PosBraid n` on one object.  The fibre there is the orderings of
the `n` axes: `fibrePerm` reads the step at which each axis is performed, and a refinement shifts
it by its crossing permutation.
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
  (Equiv.sigmaCongrRight fun i => (bead d α i).1).trans (coordFlip (chainOf (□n) α))

@[simp] theorem eventDirEquiv_mk {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (i : Fin d.length)
    (j : Fin (d.get i : ℕ)) : eventDirEquiv α ⟨i, j⟩ = beadDir α i j :=
  coordFlip_chainOf α i j

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
  (eventDirEquiv α).symm.trans (strand A hA)

open ChainCat in
/-- **A refinement shifts the order by its crossing permutation** — the whole content of the
fibre being the positive braid action. -/
theorem fibrePerm_comp {A B : Ch Zbp} (hA : dimSum A.dims = n) (hB : dimSum B.dims = n)
    (f : A ⟶ B) (α : ⋁B.dims ⟶ Hbp.obj (□n)) :
    fibrePerm hA (f.φ ≫ α) = (crossPerm hA f)⁻¹ * fibrePerm hB α := by
  refine Equiv.ext fun q => ?_
  set e : beadEvent A.dims := (eventDirEquiv (f.φ ≫ α)).symm q with he
  have h2 : (eventDirEquiv α).symm q = coordMap f.φ e := by
    refine (Equiv.symm_apply_eq _).2 ?_
    rw [← eventDirEquiv_comp, he, Equiv.apply_symm_apply]
  have key : crossPerm hA f (fibrePerm hA (f.φ ≫ α) q) = fibrePerm hB α q := by
    show crossPerm hA f (strand A hA e) = strand B hB ((eventDirEquiv α).symm q)
    rw [h2]
    exact crossPerm_strand hA f e
  rw [Equiv.Perm.mul_apply]
  exact Equiv.Perm.eq_inv_iff_eq.2 key

/-! ### The fibre is the orderings

The merge out of the all-edges chain is invertible on the fibre and crosses nothing, so every
`n`-strand chain has the same fibre as the run of `n` edges — where `runHbpCubeEquivPerm` already
says it is `Perm (Fin n)`. -/

/-- Forgetting the order leaves a chain of `□ⁿ`, whose events are the `n` coordinates. -/
theorem dimSum_of_hbpCubeHom {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : dimSum d = n :=
  wedgeDimSum_eq (chainOf (□n) α)

/-- **A run of the decorated cube is a wedge map out of the `n` edges.** -/
def onesHomEquivRunHbp (n : ℕ) : (⋁(𝟙^n) ⟶ Hbp.obj (□n)) ≃ Run (Hbp.obj (□n)) :=
  onesHomEquivRun fun α => dimSum_of_hbpCubeHom α

/-- On an all-edges chain each bead's order is trivial, so the events *are* the axes. -/
theorem eventDirEquiv_ones {d : List ℕ+} (hd : ∀ x ∈ d, x = 1) (β : ⋁d ⟶ Hbp.obj (□n)) :
    eventDirEquiv β = coordFlip (chainOf (□n) β) := by
  refine Equiv.ext fun e => ?_
  obtain ⟨i, j⟩ := e
  have hsub : Subsingleton (Fin ((d.get i : ℕ+) : ℕ)) := by
    rw [show ((d.get i : ℕ+) : ℕ) = 1 from congrArg PNat.val (hd _ (List.get_mem d i))]
    infer_instance
  rw [eventDirEquiv_mk]
  exact (coordFlip_chainOf β i j).symm.trans
    (congrArg (coordFlip (chainOf (□n) β)) (congrArg (Sigma.mk i) (Subsingleton.elim _ _)))

/-- **On a run the fibre order is the run's own step order.** -/
theorem fibrePerm_ones (β : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    fibrePerm (A := ChainCat.zObj (𝟙^n)) (dimSum_replicate n) β
      = runHbpCubeEquivPerm n (onesHomEquivRunHbp n β) := by
  have h : eventDirEquiv β = coordFlip (chainOf (□n) β) :=
    eventDirEquiv_ones (fun _ hx => List.eq_of_mem_replicate hx) β
  refine Equiv.ext fun q => Fin.ext ?_
  have hq : (eventDirEquiv β).symm q = (coordFlip (chainOf (□n) β)).symm q := by rw [h]
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
theorem bijective_fibrePerm (A : ChStrands Zbp n) : Function.Bijective (fibrePerm A.property) := by
  obtain ⟨u, hu⟩ := exists_WStrands_from_ones A
  have hbij : Function.Bijective (fun β : ⋁A.obj.dims ⟶ Hbp.obj (□n) => u.hom.φ ≫ β) :=
    (isIso_iff_bijective _).mp (invertsMerges_of_isSegal _ (isSegal_H_cube n) u.hom.op hu)
  have hone : crossPerm (dimSum_replicate n) u.hom = 1 := crossPermN_eq_one_of_WStrands hu
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
noncomputable def fibreEquiv (A : ChainCat.ChStrands Zbp n) :
    (⋁A.obj.dims ⟶ Hbp.obj (□n)) ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (bijective_fibrePerm A)

end CubeChains

namespace ChainCat

variable {n : ℕ}

/-! ### The orderings, as a `PosBraid n`-set -/

/-- The presheaf on the degree-`n` component carried by the orderings: `β` restricts by
`posPermHom β⁻¹`, the variance `(∫ -)ᵒᵖ` needs. -/
abbrev permPresheaf (n : ℕ) : (SingleObj (PosBraid n))ᵒᵖ ⥤ Type :=
  invActionPresheaf (Equiv.Perm (Fin n)) (posPermHom n)

/-- **`(∫ permPresheaf)ᵒᵖ` is the positive braid action.** -/
def permPresheafElementsEquiv : (((permPresheaf n).Elements)ᵒᵖ) ≌ PosBraidAction n :=
  elementsOpEquivActionCategory _ _ fun _ _ => rfl

/-! ### One strand count

Every decorated chain of `□ⁿ` fires `n` events, so `Ch (Hbp □ⁿ)` lies over the strand-`n`
component of `Ch Zbp` and over nothing else — there is no strand splitting to do. -/

/-- **Every decorated chain of `□ⁿ` fires `n` events.** -/
theorem hbpCubeStrands : ∀ {d : List ℕ+}, (⋁d ⟶ Hbp.obj (□n)) → dimSum d = n :=
  fun α => dimSum_of_hbpCubeHom α

/-! ### The chains, acting on the orderings

The same data as the localization comparison, but written down: a chain goes to the order its
events perform the axes in, a refinement to the simple of its crossing permutation.  `fibrePerm_comp`
is exactly the action condition. -/

/-- The ordering a decorated chain performs its axes in. -/
noncomputable def chainPerm (a : Ch (Hbp.obj (□n))) : Equiv.Perm (Fin n) :=
  fibrePerm (A := ChainCat.zObj a.dims) (hbpCubeStrands a.map) a.map

/-- The crossing permutation of a refinement of decorated chains. -/
noncomputable def chainCross {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) : Equiv.Perm (Fin n) :=
  crossPerm (hbpCubeStrands a.map) f

theorem chainCross_comp {a b c : Ch (Hbp.obj (□n))} (f : a ⟶ b) (g : b ⟶ c) :
    chainCross (f ≫ g) = chainCross g * chainCross f :=
  crossPerm_comp (hbpCubeStrands a.map) f g

/-- **Crossings add along a composite** — a crossing made is never undone. -/
theorem permLen_chainCross_comp {a b c : Ch (Hbp.obj (□n))} (f : a ⟶ b) (g : b ⟶ c) :
    permLen (chainCross g * chainCross f) = permLen (chainCross g) + permLen (chainCross f) := by
  rw [← chainCross_comp]
  exact (permLen_crossPerm_comp (hbpCubeStrands a.map) f g).trans (Nat.add_comm _ _)

theorem posPerm_mul_chainCross {a b c : Ch (Hbp.obj (□n))} (f : a ⟶ b) (g : b ⟶ c) :
    posPerm (chainCross g) * posPerm (chainCross f) = posPerm (chainCross (f ≫ g)) := by
  rw [posPerm_mul (permLen_chainCross_comp f g), chainCross_comp]

/-- **A merge crosses nothing.** -/
theorem chainCross_eq_one_of_W {a b : Ch (Hbp.obj (□n))} {f : a ⟶ b}
    (h : W (Hbp.obj (□n)) f) : chainCross f = 1 :=
  (W_iff_crossPerm_eq_one (hbpCubeStrands a.map) f).mp h

theorem chainCross_smul {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) :
    chainCross f * chainPerm a = chainPerm b := by
  have h := fibrePerm_comp (A := ChainCat.zObj a.dims) (B := ChainCat.zObj b.dims)
    (hbpCubeStrands a.map) (hbpCubeStrands b.map) (ChainCat.zHom f.φ) b.map
  have h3 : chainPerm a = (chainCross f)⁻¹ * chainPerm b :=
    (congrArg (fibrePerm (A := ChainCat.zObj a.dims) (hbpCubeStrands a.map)) f.w).symm.trans h
  rw [h3, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The chains of the decorated cube, acting on the orderings.** -/
noncomputable def chToAction (n : ℕ) : Ch (Hbp.obj (□n)) ⥤ PosBraidAction n where
  obj a := ActionCategory.objEquiv (PosBraid n) (Equiv.Perm (Fin n)) (chainPerm a)
  map {a b} f := ⟨posPerm (chainCross f), chainCross_smul f⟩
  map_id a := Subtype.ext (by
    change posPerm (crossPerm (hbpCubeStrands a.map) (𝟙 a)) = _
    rw [crossPerm_id]; exact posPerm_one)
  map_comp {a b c} f g := Subtype.ext (by
    change posPerm (chainCross (f ≫ g)) = _
    rw [ActionCategory.comp_val]
    exact (posPerm_mul_chainCross f g).symm)

@[simp] theorem chToAction_map_val {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) :
    ((chToAction n).map f).val = posPerm (chainCross f) := rfl

/-- **A merge acts as the identity** — it crosses nothing. -/
theorem chToAction_map_of_W {a b : Ch (Hbp.obj (□n))} {f : a ⟶ b} (h : W (Hbp.obj (□n)) f) :
    chainPerm a = chainPerm b := by
  rw [← chainCross_smul f, chainCross_eq_one_of_W h, one_mul]

/-! ### The fibre presheaf, descended

`posBraidGrading n` localizes the strand component, so the fibre presheaf descends by uniqueness of
lifts: it is enough to identify it *before* localizing, which is `fibrePerm_comp`. -/

/-- **The fibre presheaf on the strand component is the `PosBraid n`-set of orderings.** -/
noncomputable def fibreNatIso (n : ℕ) :
    wedgeHomsN (Hbp.obj (□n)) n ≅ (posBraidGrading n).op ⋙ permPresheaf n :=
  NatIso.ofComponents (fun A => (fibreEquiv A.unop).toIso)
    fun {_ _} g => by ext α; exact fibrePerm_comp _ _ g.unop.hom α

/-- The strand component's localization, on the opposite: `PosBraid n` on one object. -/
noncomputable def posBraidLocOp (n : ℕ) :
    ((WStrands Zbp n).op).Localization ≌ (SingleObj (PosBraid n))ᵒᵖ :=
  haveI := posBraidGrading_isLocalization n
  Localization.uniq ((WStrands Zbp n).op).Q ((posBraidGrading n).op) ((WStrands Zbp n).op)

/-- **The descended fibre is the `PosBraid n`-set of orderings.** -/
noncomputable def descendFibreIso (n : ℕ) :
    wedgeHomsNDescend (Hbp.obj (□n)) n (isSegal_H_cube n)
      ≅ (posBraidLocOp n).functor ⋙ permPresheaf n := by
  haveI := posBraidGrading_isLocalization n
  haveI : Localization.Lifting ((WStrands Zbp n).op).Q ((WStrands Zbp n).op)
      (wedgeHomsN (Hbp.obj (□n)) n)
      (wedgeHomsNDescend (Hbp.obj (□n)) n (isSegal_H_cube n)) :=
    ⟨eqToIso (Localization.Construction.fac _ _)⟩
  haveI : Localization.Lifting ((WStrands Zbp n).op).Q ((WStrands Zbp n).op)
      (wedgeHomsN (Hbp.obj (□n)) n) ((posBraidLocOp n).functor ⋙ permPresheaf n) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Localization.compUniqFunctor ((WStrands Zbp n).op).Q
        ((posBraidGrading n).op) ((WStrands Zbp n).op)) (permPresheaf n) ≪≫
      (fibreNatIso n).symm⟩
  exact Localization.liftNatIso ((WStrands Zbp n).op).Q ((WStrands Zbp n).op)
    (wedgeHomsN (Hbp.obj (□n)) n) (wedgeHomsN (Hbp.obj (□n)) n) _ _ (Iso.refl _)

/-- **`Ch (Hbp □ⁿ)` localized at the bead merges is the positive braid action**: objects the
orderings of the strands, arrows the positive braids realising the change of ordering. -/
noncomputable def localizationEquivPosBraidAction (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ PosBraidAction n :=
  haveI := isLocalization_chDescentN (Hbp.obj (□n)) n hbpCubeStrands (isSegal_H_cube n)
  (Localization.uniq (W (Hbp.obj (□n))).Q
      (chDescentN (Hbp.obj (□n)) n hbpCubeStrands (isSegal_H_cube n))
      (W (Hbp.obj (□n)))).trans
    (((CategoryOfElements.mapEquivalence (descendFibreIso n)).trans
        (CategoryOfElements.preEquivalenceComp (permPresheaf n) (posBraidLocOp n))).op.trans
      permPresheafElementsEquiv)

/-- **The loops of the localization are the positive pure braids**: an ordering returns to itself
only along a braid that returns every strand to its own position. -/
noncomputable def endEquivPosPureOfLocalization (n : ℕ)
    (X : (W (Hbp.obj (□n))).Localization) : End X ≃* PosPureBraid n :=
  ((localizationEquivPosBraidAction n).fullyFaithfulFunctor.mulEquivEnd X).trans
    (endEquivPosPure _)

end ChainCat
