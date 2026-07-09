import CubeChains.FinalBraid.Elements
import CubeChains.FinalBraid.Lines
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# FinalBraid/SalBraidPartition — the ordered-set-partition of a cube chain of `□ⁿ`

Foundation for the cube-chain side of `Sal(braidCOM n) ≃o Int(Lines(cube n))`: a
`RefineObj (cube n).init (cube n).final` is an ordered set partition of `Fin n`. Bead
`i`'s block `blockOf x i` is the flipped-coordinate set `noneSet (toStar (bead i))`; the
blocks are pairwise disjoint and cover `Fin n` (`blockIndex`/`mem_block_iff`), and their
sizes sum to `n` (`cubes_dims_sum`). Also transports `Lines` onto the `RefineObj` side of
its category of elements (`refineLinesEquiv`).

**Layer:** FinalBraid.  **Imports:** `FinalBraid/Elements`, `FinalBraid/Lines`, mathlib.
Not part of the default `CubeChains` target.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace FinalBraid

/-! ## Part 1 — transport `Lines` onto the `RefineObj` side of its elements -/

/-- `Lines (cube n)` pulled back onto the refinement category via `cubeChainRefineEquiv`. -/
noncomputable def RefineLines (n : ℕ) :
    (RefineObj (BPSet.cube n).init (BPSet.cube n).final)ᵒᵖ ⥤ Type :=
  (cubeChainRefineEquiv n).functor.op ⋙ FinalBraid.Lines (BPSet.cube n)

/-- **Base-change of `Lines` onto `RefineObj`.** The categories of elements of `Lines (cube n)`
on the `RefineObj` side and on the `ChainCat` side are equivalent. -/
noncomputable def refineLinesEquiv (n : ℕ) :
    (RefineLines n).Elements ≌ (FinalBraid.Lines (BPSet.cube n)).Elements :=
  CategoryOfElements.preEquivalence (FinalBraid.Lines (BPSet.cube n)) ((cubeChainRefineEquiv n).op)

/-! ## A list-sum helper -/

/-- The `Fin`-indexed sum of `g` over a list's entries equals the sum of the mapped list. -/
theorem sum_get_eq_sum_map {α : Type*} {M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  rw [← List.sum_ofFn (f := fun i => g (l.get i)), List.ofFn_comp', List.ofFn_get]

/-! ## `toStar` of the extremal vertices -/

variable {n : ℕ}

/-- The concrete reading of the source vertex: the free coordinates are set to `0`. -/
theorem toStar_vertex₀ {d : ℕ} (c : (BPSet.cube n).toPsh.cells d) :
    toStar ((BPSet.cube n).toPsh.vertex₀ c)
      = StdCube.app (K := StdCube.stdPre n) (toStar c) (StdCube.constVertex d false) := by
  have h : (BPSet.cube n).toPsh.vertex₀ c
      = ((BPSet.cube n).toPsh.cubeMap c).app (op (Box.ob 0)) (PrecubicalSet.initVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.initVertexMap, toStar_canonicalMap]

/-- The concrete reading of the target vertex: the free coordinates are set to `1`. -/
theorem toStar_vertex₁ {d : ℕ} (c : (BPSet.cube n).toPsh.cells d) :
    toStar ((BPSet.cube n).toPsh.vertex₁ c)
      = StdCube.app (K := StdCube.stdPre n) (toStar c) (StdCube.constVertex d true) := by
  have h : (BPSet.cube n).toPsh.vertex₁ c
      = ((BPSet.cube n).toPsh.cubeMap c).app (op (Box.ob 0)) (PrecubicalSet.finalVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.finalVertexMap, toStar_canonicalMap]

/-- Value of `app w (constVertex ε)`: free coordinates of `w` take `ε`, fixed ones keep `w`. -/
theorem app_constVertex_val {N d : ℕ} (w : StdCube.cells N d) (ε : Bool) (p : Fin N) :
    (StdCube.app (K := StdCube.stdPre N) w (StdCube.constVertex d ε)).val p
      = if p ∈ StdCube.noneSet w.val then some ε else w.val p := by
  rw [app_val]
  by_cases h : p ∈ StdCube.noneSet w.val
  · rw [dif_pos h, if_pos h]; rfl
  · rw [dif_neg h, if_neg h]

/-! ## The block sizes sum to `n` -/

variable (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final)

/-- **The block sizes of a cube chain of `□ⁿ` sum to `n`.** Each bead contributes its dimension
(its altitude jump), and the chain runs from altitude `0` to altitude `n`. -/
theorem cubes_dims_sum : (x.cubes.map (fun c => (c.1 : ℕ))).sum = n := by
  have hax : (BPSet.cube n).toPsh.IsAltitude (BPSet.cubeAlt n) :=
    fun {_} ε i c => BPSet.cube_alt_axiom n ε i c
  have h := CubeChain.isCubeChain_alt_final (BPSet.cubeAlt n) hax x.cubes
    (BPSet.cube n).init (BPSet.cube n).final x.isChain
  have hinit : BPSet.cubeAlt n 0 (BPSet.cube n).init = 0 := by
    change (StdCube.trueCount (StdCube.ev ((BPSet.cube n).init)) : ℤ) = 0
    rw [show (BPSet.cube n).init = StdCube.canonicalMap (StdCube.constVertex n false) from rfl,
      StdCube.ev_canonicalMap, StdCube.trueCount_constVertex_false]
    rfl
  have hfinal : BPSet.cubeAlt n 0 (BPSet.cube n).final = (n : ℤ) := by
    change (StdCube.trueCount (StdCube.ev ((BPSet.cube n).final)) : ℤ) = (n : ℤ)
    rw [show (BPSet.cube n).final = StdCube.canonicalMap (StdCube.constVertex n true) from rfl,
      StdCube.ev_canonicalMap, StdCube.trueCount_constVertex_true]
  rw [hinit, hfinal, zero_add] at h
  exact_mod_cast h.symm

/-! ## Blocks and the partition of `Fin n` -/

/-- The **block** of bead `i`: the flipped (`none`/star) coordinates of the `i`-th cube. -/
noncomputable def blockOf (i : Fin x.cubes.length) : Finset (Fin n) :=
  StdCube.noneSet (toStar (x.cubes.get i).2).val

/-- The `p`-value of junction `i` (the source of bead `i`): `0` on the block, else fixed. -/
theorem toStar_junc_castSucc (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes (BPSet.cube n).final i.castSucc)).val p
      = if p ∈ blockOf x i then some false else (toStar (x.cubes.get i).2).val p := by
  rw [vtxCanon_castSucc, toStar_vertex₀]
  exact app_constVertex_val (toStar (x.cubes.get i).2) false p

/-- The `p`-value of junction `i+1` (the target of bead `i`): `1` on the block, else fixed. -/
theorem toStar_junc_succ (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes (BPSet.cube n).final i.succ)).val p
      = if p ∈ blockOf x i then some true else (toStar (x.cubes.get i).2).val p := by
  rw [← isCubeChain_vtx_tgt (BPSet.cube n).init (BPSet.cube n).final x.cubes x.isChain i,
    toStar_vertex₁]
  exact app_constVertex_val (toStar (x.cubes.get i).2) true p

/-- The boolean "coordinate `p` is already flipped to `1` at junction `j`". -/
noncomputable def Fval (p : Fin n) : Fin (x.cubes.length + 1) → Bool :=
  fun j => decide ((toStar (vtxCanon x.cubes (BPSet.cube n).final j)).val p = some true)

/-- **A coordinate never un-flips.** Once flipped to `1`, it stays `1` along the chain. -/
theorem Fval_mono (p : Fin n) : Monotone (Fval x p) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  by_cases hb : p ∈ blockOf x i
  · have hcs : Fval x p i.castSucc = false := by
      simp only [Fval]; rw [toStar_junc_castSucc x i p, if_pos hb]; rfl
    rw [hcs]; exact Bool.false_le _
  · have heq : Fval x p i.castSucc = Fval x p i.succ := by
      simp only [Fval]
      rw [toStar_junc_castSucc x i p, toStar_junc_succ x i p, if_neg hb, if_neg hb]
    exact le_of_eq heq

/-- **Blocks of distinct beads are disjoint** (in chain order): a coordinate flips at most once. -/
theorem blockOf_disjoint {i j : Fin x.cubes.length} (hij : i < j) :
    Disjoint (blockOf x i) (blockOf x j) := by
  rw [Finset.disjoint_left]
  intro p hi hj
  have h1 : Fval x p i.succ = true := by
    simp only [Fval]; rw [toStar_junc_succ x i p, if_pos hi]; rfl
  have h2 : Fval x p j.castSucc = false := by
    simp only [Fval]; rw [toStar_junc_castSucc x j p, if_pos hj]; rfl
  have hle : i.succ ≤ j.castSucc := by
    have hlt : (i : ℕ) < (j : ℕ) := hij
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
  have hmono := Fval_mono x p hle
  rw [h1, h2] at hmono
  exact absurd hmono (by decide)

/-- Blocks of distinct beads are disjoint. -/
theorem blockOf_disjoint_ne {i j : Fin x.cubes.length} (hij : i ≠ j) :
    Disjoint (blockOf x i) (blockOf x j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact blockOf_disjoint x h
  · exact (blockOf_disjoint x h).symm

/-- A coordinate lies in at most one block. -/
theorem blockOf_unique {i j : Fin x.cubes.length} {p : Fin n}
    (hi : p ∈ blockOf x i) (hj : p ∈ blockOf x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hj (Finset.disjoint_left.mp (blockOf_disjoint x h) hi)
  · exact h
  · exact absurd hi (Finset.disjoint_left.mp (blockOf_disjoint x h) hj)

/-- The block cardinalities sum to `n` (block `i` has `dims.get i` coordinates). -/
theorem sum_blockOf_card : ∑ i : Fin x.cubes.length, (blockOf x i).card = n := by
  have hc : ∀ i : Fin x.cubes.length, (blockOf x i).card = ((x.cubes.get i).1 : ℕ) :=
    fun i => (toStar (x.cubes.get i).2).prop
  simp_rw [hc]
  rw [sum_get_eq_sum_map x.cubes (fun c => (c.1 : ℕ))]
  exact cubes_dims_sum x

/-- **Every coordinate lies in some block** (the blocks cover `Fin n`, by counting). -/
theorem exists_blockOf (p : Fin n) : ∃ i : Fin x.cubes.length, p ∈ blockOf x i := by
  have hpd : ((Finset.univ : Finset (Fin x.cubes.length)) :
      Set (Fin x.cubes.length)).PairwiseDisjoint (blockOf x) :=
    fun i _ j _ hij => blockOf_disjoint_ne x hij
  have hcard : (Finset.univ.biUnion (blockOf x)).card = Fintype.card (Fin n) := by
    rw [Finset.card_biUnion hpd, Fintype.card_fin]
    exact sum_blockOf_card x
  have huniv : Finset.univ.biUnion (blockOf x) = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hmem : p ∈ Finset.univ.biUnion (blockOf x) := by rw [huniv]; exact Finset.mem_univ p
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨i, _, hp⟩ := hmem
  exact ⟨i, hp⟩

/-- **The blocks partition `Fin n`:** every coordinate lies in exactly one block. -/
theorem blockIndex_existsUnique (p : Fin n) : ∃! i : Fin x.cubes.length, p ∈ blockOf x i := by
  obtain ⟨i, hi⟩ := exists_blockOf x p
  exact ⟨i, hi, fun j hj => blockOf_unique x hj hi⟩

/-- **The block index of a coordinate:** the unique bead whose block flips it. -/
noncomputable def blockIndex : Fin n → Fin x.cubes.length :=
  fun p => (blockIndex_existsUnique x p).choose

/-- The block index lands in the block that contains the coordinate. -/
theorem blockIndex_mem (p : Fin n) : p ∈ blockOf x (blockIndex x p) :=
  (blockIndex_existsUnique x p).choose_spec.1

/-- Any bead whose block contains `p` is the block index of `p`. -/
theorem blockIndex_unique {i : Fin x.cubes.length} {p : Fin n} (h : p ∈ blockOf x i) :
    blockIndex x p = i :=
  ((blockIndex_existsUnique x p).choose_spec.2 i h).symm

/-- **Membership characterisation:** `p` lies in block `i` iff `i` is `p`'s block index. -/
theorem mem_block_iff {i : Fin x.cubes.length} {p : Fin n} :
    p ∈ blockOf x i ↔ blockIndex x p = i :=
  ⟨fun h => blockIndex_unique x h, fun h => h ▸ blockIndex_mem x p⟩

/-- The **covector height** of a coordinate: its block index as an integer. Feeds `braidSign`
downstream. -/
noncomputable def covectorHeight : Fin n → ℤ :=
  fun c => ((blockIndex x c).val : ℤ)

end FinalBraid
