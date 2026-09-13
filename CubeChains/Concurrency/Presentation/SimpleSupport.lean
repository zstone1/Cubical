import CubeChains.Concurrency.Presentation.SlicePresentation

/-!
# Concurrency/Presentation/SimpleSupport — which chain a simple can be crossed over

An arrow of `Ch Zbp` permutes each bead of its target and no more (`index_crossPerm`), so the
braid joining two runs over a chain fixes every bead index of it.  A simple whose permutation
**mixes** all `n` events is therefore crossed only over the one-bead chain, where nothing may be
crossed below it.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Equiv

namespace ChainCat

/-! ## A chain's beads are preserved -/

/-- **An object of the slice crosses inside `d`'s beads and no more** — `index_crossPerm`, read on
`crossOver`. -/
theorem index_crossOver {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (y : Over d) (r : Fin N) :
    ((dimComp d.dims hd).index (crossOver hd y r) : ℕ) = ((dimComp d.dims hd).index r : ℕ) :=
  index_crossPerm hd (over_left_dimSum hd y) y.hom r

/-- **The braid between two objects of the slice fixes every bead index** — both cross inside the
beads, so their ratio does. -/
theorem index_crossOver_ratio {d : Ch Zbp} {N : ℕ} (hd : dimSum d.dims = N) (x y : Over d)
    (r : Fin N) :
    ((dimComp d.dims hd).index (((crossOver hd y)⁻¹ * crossOver hd x) r) : ℕ)
      = ((dimComp d.dims hd).index r : ℕ) := by
  rw [Perm.mul_apply]
  refine Eq.trans ?_ (index_crossOver hd x r)
  have h := index_crossOver hd y ((crossOver hd y)⁻¹ (crossOver hd x r))
  rw [show (crossOver hd y) ((crossOver hd y)⁻¹ (crossOver hd x r)) = crossOver hd x r from
    Equiv.apply_symm_apply (crossOver hd y) _] at h
  exact h.symm

/-! ## A mixing permutation forces the one-bead chain -/

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
  | [] => obtain rfl : n = 0 := hd.symm; rfl
  | [a] => rw [← hd, dimSum_single]; exact (topDims_coe a).symm
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

/-- **A mixing generator is crossed only in the one-bead chain** — it fixes every bead index, and
a transitive one is constant. -/
theorem dims_eq_topDims_of_mixes {n : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = n) (x y : Over d)
    {σ : Perm (Fin n)} (hσ : (crossOver hd y)⁻¹ * crossOver hd x = σ) (hmix : Mixes σ) :
    d.dims = topDims n :=
  eq_topDims_of_index_const hd fun r s => by
    obtain ⟨k, rfl⟩ := hmix r s
    exact (index_pow hd (fun t => by rw [← hσ]; exact index_crossOver_ratio hd x y t) k r).symm

end ChainCat
