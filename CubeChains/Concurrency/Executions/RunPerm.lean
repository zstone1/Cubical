import CubeChains.Concurrency.Executions.RunSegal
import CubeChains.Precubical.Chains.Reversal
import CubeChains.Machinery.SortPerm

/-!
# Concurrency/Executions/RunPerm — running a run backwards

`Run.rev` is the geometric reversal: `Box.rev` on every bead, the beads in reverse order
(`Precubical/Chains/Reversal`).  What it does to the bijection `runPermEquiv` — the order a run of
`□n` fires its axes in — is `Fin.revPerm`, and that is a theorem (`runPermEquiv_rev`): `Box.rev`
leaves a cube free exactly where it was (`noneSet_flipFun`), so a bead keeps the **axis** it flips
and only the **step** at which it fires changes.

The chase runs on the flat cube list rather than the shape-indexed `Beads`: reversal *is* a
`List.reverse`, and `(Box.sign c.2).val q : Option Bool` does not depend on `c.1`, so the whole
argument is transport-free.  Reversal then survives restriction because restriction is a rank map
and `Fin.rev` is antitone.
-/

open CategoryTheory Opposite CubeChain BPSet StdCube

namespace CubeChains

variable {n : ℕ}

/-- **A run, run backwards** — `Box.rev` on every bead, the beads in reverse order. -/
def Run.rev (ρ : Run (□n)) : Run (□n) :=
  (Run.equivEdgeChain (□n)).symm (EdgeChain.rev (Run.equivEdgeChain (□n) ρ))

@[simp] theorem Run.rev_rev (ρ : Run (□n)) : ρ.rev.rev = ρ := by
  rw [Run.rev, Run.rev, Equiv.apply_symm_apply, EdgeChain.rev_rev, Equiv.symm_apply_apply]

/-! ### Reversal reflects the bead an axis is flipped by -/

/-- **Reversal keeps a cube free exactly where it was** — it only flips fixed signs. -/
theorem sign_revCube_eq_none_iff (c : Σ d : ℕ+, (□n).cells (d : ℕ)) (q : Fin n) :
    (Box.sign (revCube c).2).val q = none ↔ (Box.sign c.2).val q = none := by
  rw [show Box.sign (revCube c).2 = flipCell (Box.sign c.2) from sign_rev_cell c.2, flipCell_val]
  cases h : (Box.sign c.2).val q <;> simp [flipFun, h]

@[simp] theorem length_revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) :
    (revCubes cubes).length = cubes.length := by simp [revCubes]

/-- Bead `j` of a reversed cube list is the reversal of bead `length - 1 - j`. -/
theorem getElem_revCubes (cubes : List (Σ d : ℕ+, (□n).cells (d : ℕ))) {j : ℕ}
    (hj : j < cubes.length) :
    (revCubes cubes)[j]'(by simpa using hj)
      = revCube (cubes[cubes.length - 1 - j]'(by omega)) := by
  simp only [revCubes]
  rw [List.getElem_reverse, List.getElem_map]
  simp

/-- **`beadOf` read off the flat cube list**: entry `i` is free at `q` exactly when `q`'s bead is
`i` — `ev_beadFace_eq_none_iff` with the shape-indexed bead replaced by the list entry, which is
what a `List.reverse` can be applied to. -/
theorem getElem_toList_eq_none_iff (b : Ch (□n)) (q : Fin n) (i : ℕ)
    (hi : i < (beadCell b.map.hom).toList.length) :
    (Box.sign ((beadCell b.map.hom).toList[i]).2).val q = none ↔ (beadOf b q : ℕ) = i := by
  have hi' : i < b.dims.length := by simpa using hi
  have hget := Beads.toList_get (beadCell b.map.hom) ⟨i, hi⟩
  rw [List.get_eq_getElem] at hget
  rw [congrArg (fun c : Σ d : ℕ+, (□n).cells (d : ℕ) => (Box.sign c.2).val q) hget]
  exact (ev_beadFace_eq_none_iff b ⟨i, hi'⟩ q).trans
    ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-- **The cube list of a reversed run is the reversed cube list** — the only thing needed from
inside the sealed `Run.equivEdgeChain`, and `cubes_equivEdgeChain` is stated for exactly this. -/
theorem toList_beadCell_rev (ρ : Run (□n)) :
    (beadCell ρ.rev.chain.map.hom).toList = revCubes ((beadCell ρ.chain.map.hom).toList) := by
  have h : Run.equivEdgeChain (□n) ρ.rev = EdgeChain.rev (Run.equivEdgeChain (□n) ρ) :=
    (Run.equivEdgeChain (□n)).apply_symm_apply _
  rw [← cubes_equivEdgeChain ρ.rev, h]
  exact congrArg revCubes (cubes_equivEdgeChain ρ)

/-- **Reversal reflects the bead an axis is flipped by.**  Stated on `ℕ` values, so that no
`Fin.cast` across `dims.reverse` appears. -/
theorem beadOf_rev (ρ : Run (□n)) (q : Fin n) :
    (beadOf ρ.rev.chain q : ℕ) + (beadOf ρ.chain q : ℕ) + 1 = n := by
  have hLρ : (beadCell ρ.chain.map.hom).toList.length = n :=
    (Beads.length_toList _).trans (runCubeLength ρ)
  have hLr : (beadCell ρ.rev.chain.map.hom).toList.length = n :=
    (Beads.length_toList _).trans (runCubeLength ρ.rev)
  have hin : (beadOf ρ.chain q : ℕ) < n := by
    have h1 := (beadOf ρ.chain q).isLt
    have h2 : ρ.chain.dims.length = n := runCubeLength ρ
    omega
  have hfree :
      (Box.sign ((beadCell ρ.chain.map.hom).toList[(beadOf ρ.chain q : ℕ)]'(by omega)).2).val q
        = none :=
    (getElem_toList_eq_none_iff ρ.chain q (beadOf ρ.chain q : ℕ) (by omega)).mpr rfl
  have key : (beadOf ρ.rev.chain q : ℕ) = n - 1 - (beadOf ρ.chain q : ℕ) := by
    have hj :
        n - 1 - (beadOf ρ.chain q : ℕ) < (beadCell ρ.rev.chain.map.hom).toList.length := by omega
    have hj' : n - 1 - (beadOf ρ.chain q : ℕ) < (beadCell ρ.chain.map.hom).toList.length := by omega
    refine (getElem_toList_eq_none_iff ρ.rev.chain q _ hj).mp ?_
    rw [List.getElem_of_eq (toList_beadCell_rev ρ) hj, getElem_revCubes _ hj']
    refine (sign_revCube_eq_none_iff _ q).mpr ?_
    rw [getElem_congr_idx (by omega : (beadCell ρ.chain.map.hom).toList.length - 1 -
      (n - 1 - (beadOf ρ.chain q : ℕ)) = (beadOf ρ.chain q : ℕ))]
    exact hfree
  omega

/-- …so it fires the axes in the reverse order. -/
theorem flatten_rev (ρ : Run (□n)) (q : Fin n) :
    flatten ρ.rev.chain q = Fin.rev (flatten ρ.chain q) :=
  Fin.ext <| by
    rw [Fin.val_rev, flatten_eq_beadOf_of_ones ρ.rev.ones q, flatten_eq_beadOf_of_ones ρ.ones q]
    have := beadOf_rev ρ q
    omega

/-! ### Reversal on the two readings of a run -/

/-- **Reversing a run reverses the order it fires its axes in.** -/
@[simp] theorem runPermEquiv_rev (ρ : Run (□n)) :
    runPermEquiv n ρ.rev = Fin.revPerm * runPermEquiv n ρ :=
  Equiv.ext fun q => (flatten_rev ρ q).trans (Fin.revPerm_apply _).symm

/-- …which on the word reading — step to axis — is reversal acting on the right. -/
@[simp] theorem runWordEquiv_rev (ρ : Run (□n)) :
    runWordEquiv n ρ.rev = runWordEquiv n ρ * Fin.revPerm := by
  change (flatten ρ.rev.chain)⁻¹ = (flatten ρ.chain)⁻¹ * Fin.revPerm
  rw [show flatten ρ.rev.chain = Fin.revPerm * flatten ρ.chain from runPermEquiv_rev ρ,
    mul_inv_rev, show (Fin.revPerm : Equiv.Perm (Fin n))⁻¹ = Fin.revPerm from Fin.revPerm_symm]

/-- …so the run of a word, reversed, is the run of the reversed word. -/
@[simp] theorem rev_wordRun (w : Equiv.Perm (Fin n)) :
    (wordRun w).rev = wordRun (w * Fin.revPerm) :=
  (runWordEquiv n).injective (by rw [runWordEquiv_rev, runWordEquiv_wordRun, runWordEquiv_wordRun])

/-- …and the same on chains. -/
@[simp] theorem chain_rev_wordRun (w : Equiv.Perm (Fin n)) :
    (wordRun w).rev.chain = wordChain (w * Fin.revPerm) := congrArg Run.chain (rev_wordRun w)

/-- **A run of a cube of dimension at least two is moved by reversal** — `Fin.revPerm` acts freely,
and above dimension one it is not the identity. -/
theorem Run.rev_ne (ρ : Run (□n)) (hn : 2 ≤ n) : ρ.rev ≠ ρ := fun h => by
  have h1 : (Fin.revPerm : Equiv.Perm (Fin n)) = 1 :=
    mul_right_cancel ((runPermEquiv_rev ρ).symm.trans
      ((congrArg (runPermEquiv n) h).trans (one_mul _).symm))
  have h0 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨0, by omega⟩ : ℕ)) h1
  simp only [Fin.revPerm_apply, Fin.val_rev, Equiv.Perm.coe_one, id_eq] at h0
  omega

/-- **Reversal survives restriction along a face.**  Restricting a run is the *rank* map of its
firing order (`runPermEquiv_runFace`); `Fin.rev` is strictly antitone, so reversing every rank
reverses the sort (`Tuple.sort_comp_strictAnti`). -/
theorem Run.rev_restrict {k m : ℕ} (g : ▫k ⟶ ▫m) (ρ : Run (□m)) :
    runPresheaf.map g.op ρ.rev = (runPresheaf.map g.op ρ).rev := by
  refine (runPermEquiv k).injective ?_
  have hfun : (fun i => runPermEquiv m ρ.rev (faceEmb g i))
      = Fin.rev ∘ fun i => runPermEquiv m ρ (faceEmb g i) := by
    funext i; rw [runPermEquiv_rev]; rfl
  change runPermEquiv k (runFace g ρ.rev) = runPermEquiv k (runFace g ρ).rev
  rw [runPermEquiv_runFace, hfun,
    Tuple.sort_comp_strictAnti (injective_faceOrder g ρ) Fin.rev_strictAnti,
    runPermEquiv_rev, runPermEquiv_runFace, mul_inv_rev,
    show (Fin.revPerm : Equiv.Perm (Fin k))⁻¹ = Fin.revPerm from Fin.revPerm_symm]

end CubeChains
