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

/-- **A mixing generator is crossed only in the one-bead chain** — it fixes every bead index, and
a transitive one is constant. -/
theorem dims_eq_topDims_of_mixes {n : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = n) (x y : Over d)
    {σ : Perm (Fin n)} (hσ : (crossOver hd y)⁻¹ * crossOver hd x = σ) (hmix : Mixes σ) :
    d.dims = topDims n :=
  eq_topDims_of_index_const hd fun r s => by
    obtain ⟨k, rfl⟩ := hmix r s
    exact (index_pow hd (fun t => by rw [← hσ]; exact index_crossOver_ratio hd x y t) k r).symm

/-- **The one-bead chain is rigid**: an arrow between one-bead chains crosses nothing, `Ch Zbp`
having no endomorphism but the identity. -/
theorem crossPerm_eq_one_of_topDims {n : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = n)
    (hda : a.dims = topDims n) (hdb : b.dims = topDims n) (t : a ⟶ b) : crossPerm ha t = 1 := by
  obtain rfl : a = b := (eq_zObj a).symm.trans (by rw [hda, ← hdb]; exact eq_zObj b)
  rw [endo_eq_id t]
  exact crossPerm_id a ha

end ChainCat
