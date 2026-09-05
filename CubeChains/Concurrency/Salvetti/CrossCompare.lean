import CubeChains.Concurrency.Complexification.HPosAction
import CubeChains.Concurrency.Salvetti.WallCrossing

/-!
# Concurrency/Salvetti/CrossCompare — the flattening order and the arrangement's order label the
same arrow

A morphism of `Ch (Hbp □ⁿ)` carries two crossing permutations: `ChainCat.crossPerm`, its wedge map
read through the lexicographic flattening `pos`, and `topeCross`, the change of tope order across
`hbpBraidSalEquiv`.  They agree, because both are the coboundary of one function on objects —
`fibrePerm`, the step at which each axis is performed, which is what the Salvetti tope's `topePerm`
records.  Hence `W` is readable in the arrangement: a leg of a wall span crossing no wall is a
bead merge.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain

namespace CubeChains

variable {n : ℕ}

/-! ## The tope is the order the axes are run in

The tope of a decorated chain's Salvetti cell is the braid face of `runLine`, the all-edges chain
its run performs; the step at which an axis is performed is that chain's `beadOf`, and it is
`fibrePerm` by construction. -/

/-- **Step `pos e` of the run performs axis `q`** exactly when `fibrePerm` sends `q` to `pos e`. -/
theorem beadOf_runLine {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) (q : Fin n) :
    (beadOf (runLine α) q : ℕ)
      = (fibrePerm (A := zObj d) (dimSum_of_hbpCubeHom α) α q : ℕ) := by
  have hd : ∑ i : Fin d.length, ((d.get i : ℕ+) : ℕ) = n :=
    (dimSum_eq_sum_get d).trans (dimSum_of_hbpCubeHom α)
  have hr : ∑ i : Fin (chainRun α).dims.length, (((chainRun α).dims.get i : ℕ+) : ℕ) = n :=
    (dimSum_eq_sum_get _).trans (wedgeDimSum_eq (runLine α).map)
  set f : beadEvent d := (eventDirEquiv α).symm q with hf
  have hdir : beadDir α f.1 f.2 = q :=
    (eventDirEquiv_mk α f.1 f.2).symm.trans (by rw [hf, Equiv.apply_symm_apply])
  set e : beadEvent (chainRun α).dims := strandTransfer hd hr f with he
  have hpos : (pos e : ℕ) = (pos f : ℕ) := pos_strandTransfer hd hr f
  rw [beadOf_eq_of_coordFlip (C := runLine α) (p := e)
      ((coordFlip_runLine α e f.1 f.2 (hpos.trans (pos_val f))).trans hdir),
    ← pos_ones (chainRun α).ones e, hpos]
  rfl

/-- **The Salvetti tope of a decorated chain is the order it runs its axes in.** -/
theorem tope_eq_wordTope (a : Ch (Hbp.obj (□n))) :
    ((hbpBraidSalEquiv n).functor.obj a).unop.tope
      = wordTope (fibrePerm (A := zObj a.dims) (dimSum_of_hbpCubeHom a.map) a.map)⁻¹ := by
  rw [tope_hbpBraidSalEquiv, chFace_val, wordTope_eq_braidSign, Equiv.Perm.inv_def,
    Equiv.symm_symm]
  exact congrArg braidSign (funext fun q => congrArg Nat.cast (beadOf_runLine a.map q))

/-- **…so the cell's `topePerm` is the chain's `fibrePerm`** — the two readings of "which step
performs which axis". -/
theorem topePerm_hbpBraidSalEquiv (a : Ch (Hbp.obj (□n))) :
    topePerm ((hbpBraidSalEquiv n).functor.obj a).unop
      = fibrePerm (A := zObj a.dims) (dimSum_of_hbpCubeHom a.map) a.map := by
  rw [topePerm_of_tope _ _ (tope_eq_wordTope a), inv_inv]

/-! ## The comparison -/

/-- **The two crossing permutations of a decorated chain morphism agree**: the flattening order
`ChainCat.crossPerm` and the arrangement's `topeCross` are both `fibrePerm`'s coboundary. -/
theorem crossPerm_eq_topeCross {a b : Ch (Hbp.obj (□n))} (f : a ⟶ b) :
    crossPerm (dimSum_of_hbpCubeHom a.map) f
      = topeCross ((hbpBraidSalEquiv n).functor.obj a).unop
          ((hbpBraidSalEquiv n).functor.obj b).unop := by
  have hstep : fibrePerm (A := zObj a.dims) (dimSum_of_hbpCubeHom a.map) a.map
      = (crossPerm (dimSum_of_hbpCubeHom a.map) f)⁻¹
        * fibrePerm (A := zObj b.dims) (dimSum_of_hbpCubeHom b.map) b.map := by
    rw [← crossPerm_zHom (dimSum_of_hbpCubeHom a.map) f,
      ← fibrePerm_comp (A := zObj a.dims) (B := zObj b.dims) (dimSum_of_hbpCubeHom a.map)
        (dimSum_of_hbpCubeHom b.map) (zHom f.φ) b.map]
    exact congrArg (fibrePerm (A := zObj a.dims) (dimSum_of_hbpCubeHom a.map)) f.w.symm
  rw [topeCross, topePerm_hbpBraidSalEquiv, topePerm_hbpBraidSalEquiv, hstep, mul_inv_rev,
    inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

/-! ## The wall span, labelled on both sides

`topeCross_wallCross` and `topeCross_wallCross_flip` label the two legs `σₖ` and `1` in the
arrangement's order; the comparison carries those labels to the order `W` is defined by. -/

/-- A Salvetti cell is the cell of the decorated chain it names. -/
theorem functor_cellObj (a : Sal (braidCOM n)) :
    ((hbpBraidSalEquiv n).functor.obj (cellObj a)).unop = a :=
  congrArg unop (hbpBraidSalEquiv_functor_inverse (op a))

/-- **The atom leg of a wall span crosses the `k`-th wall**, in the flattening order. -/
@[simp] theorem crossPerm_wallLeg (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    crossPerm (dimSum_of_hbpCubeHom (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩)).map)
        (wallLeg w k) = adjT k := by
  rw [crossPerm_eq_topeCross, functor_cellObj, functor_cellObj, topeCross_wallCross]

/-- **The other leg is a bead merge** — it crosses nothing, and `W` is exactly that
(`W_iff_crossPerm_eq_one`).  This is what makes the wall span an arrow of chambers after one
inversion. -/
theorem W_wallLegFlip (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    W (Hbp.obj (□n)) (wallLegFlip w k) :=
  (W_iff_crossPerm_eq_one (dimSum_of_hbpCubeHom
      (cellObj (topeCell ⟨wordTope (w * adjT k), isTope_wordTope _⟩)).map) _).mpr
    (by rw [crossPerm_eq_topeCross, functor_cellObj, functor_cellObj, topeCross_wallCross_flip])

end CubeChains
