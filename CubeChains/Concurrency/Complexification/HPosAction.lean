import CubeChains.Machinery.Braid.PosAction
import CubeChains.Machinery.Localization.ElementsAction
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Complexification.HSegal
import CubeChains.Concurrency.Complexification.SymReorient

/-!
# Concurrency/Complexification/HPosAction — the decorated chains of `□ⁿ` act on the orderings

The fibre of `Ch (Hbp □ⁿ)` over a chain of `Ch Zbp` is the orderings of the `n` axes: `fibrePerm`
reads the step at which each axis is performed, and a refinement shifts it by its crossing
permutation (`fibrePerm_comp`).  `chToAction` writes that action down, and the runs exhaust the
orderings it acts on (`chToAction_obj_surjective`).
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
theorem eventDirEquiv_comp_apply {a d : List ℕ+} (φ : ⋁a ⟶ ⋁d) (α : ⋁d ⟶ Hbp.obj (□n))
    (e : beadEvent a) : eventDirEquiv (φ ≫ α) e = eventDirEquiv α (coordMap φ e) := by
  obtain ⟨i, j⟩ := e
  rw [eventDirEquiv_mk, coordMap_eq, eventDirEquiv_mk]
  show cellDir (bead a (φ ≫ α) i) j = _
  rw [bead_comp_block, cellDir_Hbp_map]
  rfl

theorem eventDirEquiv_comp {a d : List ℕ+} (φ : ⋁a ⟶ ⋁d) (α : ⋁d ⟶ Hbp.obj (□n)) :
    eventDirEquiv (φ ≫ α) = (coordMapEquiv φ).trans (eventDirEquiv α) :=
  Equiv.ext (eventDirEquiv_comp_apply φ α)

/-! ### The fibre: the order in which the axes are run -/

open ChainCat in
/-- **The order a decorated chain of `□ⁿ` runs its axes in**: axis `q` is performed at the step
`fibrePerm hA α q`.  Same shape as a chart's `flatten` — the direction order compared with the
lexicographic one — with `eventDirEquiv` in place of `coordFlip`. -/
def fibrePerm {A : Ch Zbp} (hA : dimSum A.dims = n) (α : ⋁A.dims ⟶ Hbp.obj (□n)) :
    Equiv.Perm (Fin n) :=
  conjPerm (eventDirEquiv α) (strand A.dims hA) (Equiv.refl _)

open ChainCat in
/-- **A refinement shifts the order by its crossing permutation** — the whole content of the
fibre being the positive braid action, and the same cocycle law as `crossPerm_mul_flatten`. -/
theorem crossPerm_mul_fibrePerm {A B : Ch Zbp} (hA : dimSum A.dims = n) (hB : dimSum B.dims = n)
    (f : A ⟶ B) (α : ⋁B.dims ⟶ Hbp.obj (□n)) :
    crossPerm hA f * fibrePerm hA (f.φ ≫ α) = fibrePerm hB α :=
  (congrArg (crossPerm hA f * conjPerm · (strand A.dims hA) (Equiv.refl _))
      (eventDirEquiv_comp f.φ α)).trans
    (conjPerm_mul_pullback (strand A.dims hA) (strand B.dims hB) (eventDirEquiv α)
      (coordMapEquiv f.φ))

open ChainCat in
theorem fibrePerm_comp {A B : Ch Zbp} (hA : dimSum A.dims = n) (hB : dimSum B.dims = n)
    (f : A ⟶ B) (α : ⋁B.dims ⟶ Hbp.obj (□n)) :
    fibrePerm hA (f.φ ≫ α) = (crossPerm hA f)⁻¹ * fibrePerm hB α := by
  rw [← crossPerm_mul_fibrePerm hA hB f α, inv_mul_cancel_left]

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
/-- **Restriction along a merge is bijective on the charts of the decorated cube.**  This is the
one thing the whole development spends the Segal condition on. -/
theorem invertsMerges_Hbp_cube (n : ℕ) : InvertsMerges (Hbp.obj (□n)) :=
  invertsMerges_of_isSegal _ (isSegal_H_cube n)

open ChainCat in
/-- **Every `n`-strand chain has the orderings for its fibre.** -/
theorem bijective_fibrePerm {d : List ℕ+} (hd : dimSum d = n) :
    Function.Bijective (fibrePerm (A := zObj d) hd) := by
  obtain ⟨u, hu⟩ := exists_W_from_ones (zObj d) hd
  have hbij : Function.Bijective (fun β : ⋁d ⟶ Hbp.obj (□n) => u.φ ≫ β) :=
    (isIso_iff_bijective _).mp (invertsMerges_Hbp_cube n u.op hu)
  have hone : crossPerm (dimSum_replicate n) u = 1 := crossPerm_eq_one_of_W _ hu
  have heq : fibrePerm (A := zObj d) hd
      = (fibrePerm (A := zObj (𝟙^n)) (dimSum_replicate n)) ∘
        (fun β : ⋁d ⟶ Hbp.obj (□n) => u.φ ≫ β) := by
    refine funext fun β => ?_
    have hstep := fibrePerm_comp (dimSum_replicate n) hd u β
    rw [hone, inv_one, one_mul] at hstep
    exact hstep.symm
  rw [heq]
  exact (bijective_fibrePerm_ones n).comp hbij

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
events perform the axes in, a refinement to the simple of its crossing permutation.
`fibrePerm_comp` is exactly the action condition. -/

/-- The ordering a decorated chain performs its axes in. -/
noncomputable def chainPerm (a : Ch (Hbp.obj (□n))) : Equiv.Perm (Fin n) :=
  fibrePerm (A := ChainCat.zObj a.dims) (hbpCubeStrands a.map) a.map

/-- The crossing permutation of a refinement of decorated chains. -/
noncomputable def chainCross {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) : Equiv.Perm (Fin n) :=
  crossPerm (hbpCubeStrands a.map) f

theorem chainCross_comp {a b c : Ch (Hbp.obj (□n))} (f : a ⟶ b) (g : b ⟶ c) :
    chainCross (f ≫ g) = chainCross g * chainCross f :=
  crossPerm_comp (hbpCubeStrands a.map) f g

/-- **Crossings add along a composite**, so the positive braids multiply — a crossing made is never
undone. -/
theorem posPerm_mul_chainCross {a b c : Ch (Hbp.obj (□n))} (f : a ⟶ b) (g : b ⟶ c) :
    posPerm (chainCross g) * posPerm (chainCross f) = posPerm (chainCross (f ≫ g)) := by
  have hlen : permLen (chainCross g * chainCross f)
      = permLen (chainCross g) + permLen (chainCross f) := by
    rw [← chainCross_comp]
    exact (permLen_crossPerm_comp (hbpCubeStrands a.map) f g).trans (Nat.add_comm _ _)
  rw [posPerm_mul hlen, chainCross_comp]

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

/-! ### The runs exhaust the orderings

The fibre over the all-edges chain is the orderings, and an all-edges chain *is* a run — so the
chambers are the whole object set the positive braids act on. -/

/-- **Every ordering is performed by some run.** -/
theorem chainPerm_surjective (n : ℕ) :
    Function.Surjective fun r : Run (Hbp.obj (□n)) => chainPerm r.chain := by
  intro σ
  obtain ⟨β, hβ⟩ := (bijective_fibrePerm_ones n).2 σ
  exact ⟨⟨⟨𝟙^n, β⟩, fun _ hd => List.eq_of_mem_replicate hd⟩, hβ⟩

/-- **…so the runs exhaust the objects the positive braids act on.** -/
theorem chToAction_obj_surjective (n : ℕ) :
    Function.Surjective fun r : Run (Hbp.obj (□n)) => (chToAction n).obj r.chain := by
  intro x
  obtain ⟨r, hr⟩ := chainPerm_surjective n x.back
  have hr' : chainPerm r.chain = ActionCategory.back x := hr
  refine ⟨r, show (chToAction n).obj r.chain = x from ?_⟩
  rw [show (chToAction n).obj r.chain
    = ((chainPerm r.chain : Equiv.Perm (Fin n)) : PosBraidAction n) from rfl, hr',
    ActionCategory.back_coe x]

end ChainCat
