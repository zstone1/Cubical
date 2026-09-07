import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.SlicePresentation

/-!
# Concurrency/Presentation/SimpleSupport — which chart a generator's 1-cell lives over

An arrow of `Ch Zbp` permutes each bead of its target and no more (`index_crossPerm`), so the
braid joining two runs over a chain fixes every bead index of it.  A generator whose permutation
**mixes** all `n` events therefore acts only over the one-bead chart, where nothing may be crossed
below it — so its 1-cell in `Br p K` remembers the run it acted on.  `sepCells` is that memory,
descended to the colimit by `colimitCells`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Equiv

namespace ChainCat

/-! ## A chart's beads are preserved -/

/-- **An object of the slice crosses inside `d`'s beads and no more** — `index_crossPerm`, read on
`crossOver`. -/
theorem index_crossOver {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (y : Over d) (r : Fin N) :
    ((dimComp d.dims hd).index (crossOver hd y r) : ℕ) = ((dimComp d.dims hd).index r : ℕ) :=
  index_crossPerm hd (over_left_dimSum hd y) y.hom r

theorem index_crossOver_inv {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (y : Over d)
    (r : Fin N) :
    ((dimComp d.dims hd).index ((crossOver hd y)⁻¹ r) : ℕ)
      = ((dimComp d.dims hd).index r : ℕ) := by
  have h := index_crossOver hd y ((crossOver hd y)⁻¹ r)
  rw [show (crossOver hd y) ((crossOver hd y)⁻¹ r) = r from
    Equiv.apply_symm_apply (crossOver hd y) r] at h
  exact h.symm

/-- **The braid between two objects of the slice fixes every bead index** — both cross inside the
beads, so their ratio does. -/
theorem index_crossOver_ratio {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (x y : Over d)
    (r : Fin N) :
    ((dimComp d.dims hd).index (((crossOver hd y)⁻¹ * crossOver hd x) r) : ℕ)
      = ((dimComp d.dims hd).index r : ℕ) := by
  rw [Perm.mul_apply]
  exact (index_crossOver_inv hd y _).trans (index_crossOver hd x r)

/-- **Pushing an object of the slice prefixes the arrow's crossing.** -/
theorem crossOver_over_map {d' d : Ch Zbp} {N : ℕ} (hd' : dimSum d'.dims = N)
    (hd : dimSum d.dims = N) (t : d' ⟶ d) (y : Over d') :
    crossOver hd ((Over.map t).obj y) = crossPerm hd' t * crossOver hd' y :=
  crossPerm_comp (over_left_dimSum hd' y) y.hom t

/-! ## A mixing permutation forces the one-bead chart -/

/-- **`σ` mixes the events**: its own powers reach everything from everything, so no proper chain
of beads is `σ`-stable. -/
def Mixes {n : ℕ} (σ : Perm (Fin n)) : Prop := ∀ r s : Fin n, ∃ k : ℕ, (σ ^ k) r = s

theorem index_pow {n : ℕ} {d : List ℕ+} (hd : dimSum d = n) {σ : Perm (Fin n)}
    (hσ : ∀ r, ((dimComp d hd).index (σ r) : ℕ) = ((dimComp d hd).index r : ℕ)) :
    ∀ (k : ℕ) (r : Fin n),
      ((dimComp d hd).index ((σ ^ k) r) : ℕ) = ((dimComp d hd).index r : ℕ)
  | 0, r => by rw [pow_zero, Perm.one_apply]
  | (k + 1), r => by
      rw [pow_succ, Perm.mul_apply]
      exact (index_pow hd hσ k (σ r)).trans (hσ r)

/-- **A shape with at most one bead is the one-bead shape.** -/
theorem eq_topDims_of_length_le_one {n : ℕ} {d : List ℕ+} (hd : dimSum d = n)
    (hlen : d.length ≤ 1) : d = topDims n := by
  match d with
  | [] =>
      obtain rfl : n = 0 := hd.symm
      rfl
  | [a] =>
      obtain ⟨m, hm⟩ : ∃ m, (a : ℕ) = m + 1 := ⟨(a : ℕ) - 1, by have := a.pos; omega⟩
      have hn : n = m + 1 := by rw [← hd, dimSum_single, hm]
      subst hn
      exact congrArg (fun c : ℕ+ => [c]) (PNat.coe_injective hm)
  | _ :: _ :: _ => simp at hlen

/-- **A constant bead index means one bead** — every block is inhabited (`index_embedding`). -/
theorem eq_topDims_of_index_const {n : ℕ} {d : List ℕ+} (hd : dimSum d = n)
    (h : ∀ r s : Fin n, ((dimComp d hd).index r : ℕ) = ((dimComp d hd).index s : ℕ)) :
    d = topDims n := by
  refine eq_topDims_of_length_le_one hd ?_
  by_contra hc
  rw [Nat.not_le] at hc
  have hlen : 1 < (dimComp d hd).length := by rwa [dimComp_length]
  have h0 : (0 : ℕ) < (dimComp d hd).length := by omega
  have hkey := h ((dimComp d hd).embedding ⟨0, h0⟩ ⟨0, (dimComp d hd).one_le_blocksFun ⟨0, h0⟩⟩)
    ((dimComp d hd).embedding ⟨1, hlen⟩ ⟨0, (dimComp d hd).one_le_blocksFun ⟨1, hlen⟩⟩)
  rw [Composition.index_embedding, Composition.index_embedding] at hkey
  simp at hkey

/-- **A mixing generator is crossed only in the one-bead chart** — it fixes every bead index, and
a transitive one is constant. -/
theorem dims_eq_topDims_of_mixes {n : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = n) (x y : Over d)
    {σ : Perm (Fin n)} (hσ : (crossOver hd y)⁻¹ * crossOver hd x = σ) (hmix : Mixes σ) :
    d.dims = topDims n :=
  eq_topDims_of_index_const hd fun r s => by
    obtain ⟨k, rfl⟩ := hmix r s
    exact (index_pow hd (fun t => by rw [← hσ]; exact index_crossOver_ratio hd x y t) k r).symm

/-- **The one-bead chart is rigid**: an arrow between one-bead chains crosses nothing, `Ch Zbp`
having no endomorphism but the identity. -/
theorem crossPerm_eq_one_of_topDims {n : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = n)
    (hda : a.dims = topDims n) (hdb : b.dims = topDims n) (t : a ⟶ b) : crossPerm ha t = 1 := by
  obtain rfl : a = b := (eq_zObj a).symm.trans (by rw [hda, ← hdb]; exact eq_zObj b)
  rw [endo_eq_id t]
  exact crossPerm_id a ha

/-! ## The memory a mixing generator leaves

A 1-cell of a copy names two objects of the slice; their ratio is the braid its generator
performs, and when that braid mixes, the copy it is read in and every copy it pushes to are both
the one-bead chart, so the push crosses nothing and the run survives. -/

section Sep

variable (K : BPSet) (p : BraidPresentation) {n : ℕ} (σ : Perm (Fin n))

open Classical in
/-- The run a 1-cell of a copy acted on, recorded only where the generator performs `σ`.  Off `σ`'s
own strand count there is nothing to record. -/
noncomputable def sepVal (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (x y : GenObj ((elementsPoly (wedgeHoms K) p.fam).obj c).Gen) : Option (Perm (Fin n)) :=
  if hc : dimSum (eltBase (wedgeHoms K) c).dims = n then
    if (crossOver hc (sliceCellOver y.as))⁻¹ * crossOver hc (sliceCellOver x.as) = σ then
      some (crossOver hc (sliceCellOver y.as))
    else none
  else none

/-- …as a prefunctor into the one-object quiver whose 1-cells are the records. -/
noncomputable def sepFam (c : ((wedgeHoms K).Elements)ᵒᵖ) :
    GenObj ((elementsPoly (wedgeHoms K) p.fam).obj c).Gen
      ⥤q GenObj (fun _ _ : PUnit.{1} => Option (Perm (Fin n))) where
  obj _ := ⟨PUnit.unit⟩
  map {x y} _ := sepVal K p σ c x y

variable (hmix : Mixes σ)

include hmix in
/-- **The record survives every push.** -/
theorem sepFam_naturality {c' c : ((wedgeHoms K).Elements)ᵒᵖ} (u : c' ⟶ c) :
    ((elementsPoly (wedgeHoms K) p.fam).map u).pre ⋙q sepFam K p σ c = sepFam K p σ c' := by
  refine Prefunctor.ext' (fun _ => rfl) fun x y _ => ?_
  show sepVal K p σ c _ _ = sepVal K p σ c' x y
  by_cases hc' : dimSum (eltBase (wedgeHoms K) c').dims = n
  · have hc : dimSum (eltBase (wedgeHoms K) c).dims = n :=
      (dimSum_eq_of_hom ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)).symm.trans hc'
    have hpush : ∀ a : GenObj ((elementsPoly (wedgeHoms K) p.fam).obj c').Gen,
        crossOver hc (sliceCellOver (((elementsPoly (wedgeHoms K) p.fam).map u).pre.obj a).as)
          = crossPerm hc' ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)
              * crossOver hc' (sliceCellOver a.as) := fun a =>
      (congrArg (crossOver hc)
          (sliceCellOver_push ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u) a.as)).trans
        (crossOver_over_map hc' hc _ (sliceCellOver a.as))
    have hcancel : ∀ t A B : Perm (Fin n), (t * A)⁻¹ * (t * B) = A⁻¹ * B := fun t A B => by
      rw [mul_inv_rev, mul_assoc, ← mul_assoc t⁻¹ t B, inv_mul_cancel, one_mul]
    rw [sepVal, sepVal, dif_pos hc, dif_pos hc', hpush x, hpush y, hcancel]
    by_cases hcase : (crossOver hc' (sliceCellOver y.as))⁻¹
        * crossOver hc' (sliceCellOver x.as) = σ
    · have hone : crossPerm hc' ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u) = 1 := by
        refine crossPerm_eq_one_of_topDims hc'
          (dims_eq_topDims_of_mixes hc' (sliceCellOver x.as) (sliceCellOver y.as) hcase hmix)
          (dims_eq_topDims_of_mixes hc
            (sliceCellOver (((elementsPoly (wedgeHoms K) p.fam).map u).pre.obj x).as)
            (sliceCellOver (((elementsPoly (wedgeHoms K) p.fam).map u).pre.obj y).as) ?_ hmix) _
        rw [hpush x, hpush y, hcancel]
        exact hcase
      rw [hone, one_mul]
    · rw [if_neg hcase, if_neg hcase]
  · have hc : ¬ dimSum (eltBase (wedgeHoms K) c).dims = n := fun h =>
      hc' ((dimSum_eq_of_hom ((CategoryOfElements.π (wedgeHoms K)).leftOp.map u)).trans h)
    rw [sepVal, sepVal, dif_neg hc, dif_neg hc']

/-- **The record, on the whole of `Br p K`** — a compatible family of prefunctors descends to the
colimit's cells (`colimitCells`), and no 0-cell is examined. -/
noncomputable def sepCells :
    GenObj (p.Br K).Gen ⥤q GenObj (fun _ _ : PUnit.{1} => Option (Perm (Fin n))) :=
  Polygraph.colimitCells (elementsPoly (wedgeHoms K) p.fam) (sepFam K p σ)
    fun u => sepFam_naturality K p σ hmix u

/-- **…read on a 1-cell of a copy.** -/
theorem sepCells_ιE (c : ((wedgeHoms K).Elements)ᵒᵖ)
    {a b : (p.fam.obj (eltBase (wedgeHoms K) c)).V}
    (g : (⟨a⟩ : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (sepCells K p σ hmix).map (ιE K p.fam c g) = sepVal K p σ c ⟨a⟩ ⟨b⟩ :=
  congrArg (fun φ : GenObj ((elementsPoly (wedgeHoms K) p.fam).obj c).Gen
      ⥤q GenObj (fun _ _ : PUnit.{1} => Option (Perm (Fin n))) => φ.map g)
    (Polygraph.ι_pre_comp_colimitCells (elementsPoly (wedgeHoms K) p.fam) (sepFam K p σ)
      (fun u => sepFam_naturality K p σ hmix u) c)

end Sep

end ChainCat
