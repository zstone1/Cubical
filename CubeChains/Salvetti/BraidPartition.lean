import CubeChains.Chains.Correspondence
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
import CubeChains.Arrangements.BraidPreorder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Inv

/-!
# Salvetti/BraidPartition — the ordered set partition of a cube chain of `□ⁿ`

A cube chain of `□ⁿ` *is* an ordered set partition of `Fin n`: bead `i`'s block is the set of
coordinates it flips, `noneSet (toStar (bead i))`.  The blocks are pairwise disjoint (a coordinate
never un-flips) and cover `Fin n` (their sizes sum to `n`, by altitude), so every coordinate has a
`blockIndex`; `covectorHeight` is that index as an integer, feeding `braidSign` downstream.

The partition is functorial: a refinement of chains induces `⊑` between the `braidSign` covectors
(`faceLE_of_chainRefine`).
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType

namespace CubeChains

variable {n : ℕ}

/-! ## Part 0 — list-sum bookkeeping and the `toStar` transport laws -/

/-- `toStar` intertwines a cube-map pullback with the iterated-face map: pulling `c` back along a
box morphism `φ` reads concretely as `act (toStar c) (toStar φ)`. -/
theorem toStar_map_op {dy dx : ℕ} (φ : ▫dy ⟶ ▫dx) (c : (□n).cells dx) :
    toStar ((□n).toPsh.map φ.op c)
      = act (K := stdPre n) (toStar c) (toStar (φ : (□dx).cells dy)) := by
  have h : (□n).toPsh.map φ.op c = ((□n).toPsh.cubeMap c)⟪dy⟫ φ := by
    rw [PrecubicalSet.cubeMap]
    exact (yonedaEquiv_symm_app_apply c (op ▫dy) φ).symm
  rw [h, toStar_cubeMap_app]

/-- The concrete reading of the source vertex: the free coordinates are set to `0`. -/
theorem toStar_vertex₀ {d : ℕ} (c : (□n).cells d) :
    toStar ((□n).toPsh.vertex₀ c)
      = act (K := stdPre n) (toStar c) (constVertex d false) := by
  have h : (□n).toPsh.vertex₀ c
      = ((□n).toPsh.cubeMap c)⟪0⟫ (PrecubicalSet.initVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.initVertexMap, toStar_canonicalMap]

/-- The concrete reading of the target vertex: the free coordinates are set to `1`. -/
theorem toStar_vertex₁ {d : ℕ} (c : (□n).cells d) :
    toStar ((□n).toPsh.vertex₁ c)
      = act (K := stdPre n) (toStar c) (constVertex d true) := by
  have h : (□n).toPsh.vertex₁ c
      = ((□n).toPsh.cubeMap c)⟪0⟫ (PrecubicalSet.finalVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.finalVertexMap, toStar_canonicalMap]

/-- Value of `act w (constVertex ε)`: free coordinates of `w` take `ε`, fixed ones keep `w`. -/
theorem app_constVertex_val {N d : ℕ} (w : Cell N d) (ε : Bool) (p : Fin N) :
    (act (K := stdPre N) w (constVertex d ε)).val p
      = if p ∈ noneSet w.val then some ε else w.val p := by
  rw [app_val]
  by_cases h : p ∈ noneSet w.val
  · rw [dif_pos h, if_pos h]; rfl
  · rw [dif_neg h, if_neg h]

/-! ## Part 1 — blocks and disjointness (arbitrary endpoints)

Disjointness holds for a chain between *any* two vertices of `□ⁿ`; only the junction
monotonicity of the chain is used. -/

section
variable {u w : (□n).cells 0} (x : RefineObj u w)

/-- The **block** of bead `i`: the flipped (`none`/star) coordinates of the `i`-th cube. -/
def blockOf (i : Fin x.cubes.length) : Finset (Fin n) :=
  noneSet (toStar (x.cubes.get i).2).val

/-- The `p`-value of junction `i` (the source of bead `i`): `0` on the block, else fixed. -/
theorem toStar_junc_castSucc (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes w i.castSucc)).val p
      = if p ∈ blockOf x i then some false else (toStar (x.cubes.get i).2).val p := by
  rw [vtxCanon_castSucc, toStar_vertex₀]
  exact app_constVertex_val (toStar (x.cubes.get i).2) false p

/-- The `p`-value of junction `i+1` (the target of bead `i`): `1` on the block, else fixed. -/
theorem toStar_junc_succ (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes w i.succ)).val p
      = if p ∈ blockOf x i then some true else (toStar (x.cubes.get i).2).val p := by
  rw [← isCubeChain_vtx_tgt u w x.cubes x.isChain i, toStar_vertex₁]
  exact app_constVertex_val (toStar (x.cubes.get i).2) true p

/-- The boolean "coordinate `p` is already flipped to `1` at junction `j`". -/
def Fval (p : Fin n) : Fin (x.cubes.length + 1) → Bool :=
  fun j => decide ((toStar (vtxCanon x.cubes w j)).val p = some true)

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

end

/-! ## Part 2 — the cover: block sizes sum to `n` (`init → final`) -/

variable (x : RefineObj (□n).init (□n).final)

/-- **The block sizes of a cube chain of `□ⁿ` sum to `n`.** Each bead contributes its dimension
(its altitude jump), and the chain runs from altitude `0` to altitude `n`. -/
theorem cubes_dims_sum : (x.cubes.map (fun c => (c.1 : ℕ))).sum = n := by
  have hax : (□n).toPsh.IsAltitude (cubeAlt n) :=
    fun {_} ε i c => BPSet.cube_alt_axiom n ε i c
  have h := CubeChain.isCubeChain_alt_final (cubeAlt n) hax x.cubes
    (□n).init (□n).final x.isChain
  have hinit : cubeAlt n 0 (□n).init = 0 := by
    change (trueCount (ev ((□n).init)) : ℤ) = 0
    rw [show (□n).init = canonicalMap (constVertex n false) from rfl,
      ev_canonicalMap, trueCount_constVertex_false]
    rfl
  have hfinal : cubeAlt n 0 (□n).final = (n : ℤ) := by
    change (trueCount (ev ((□n).final)) : ℤ) = (n : ℤ)
    rw [show (□n).final = canonicalMap (constVertex n true) from rfl,
      ev_canonicalMap, trueCount_constVertex_true]
  rw [hinit, hfinal, zero_add] at h
  exact_mod_cast h.symm

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

/-! ## Part 3 — `blockIndex` and `covectorHeight` -/

/-- **The block index of a coordinate:** the unique bead whose block flips it. -/
def blockIndex : Fin n → Fin x.cubes.length :=
  fun p => Fintype.choose (fun i => p ∈ blockOf x i) (blockIndex_existsUnique x p)

/-- The block index lands in the block that contains the coordinate. -/
theorem blockIndex_mem (p : Fin n) : p ∈ blockOf x (blockIndex x p) :=
  Fintype.choose_spec (fun i => p ∈ blockOf x i) (blockIndex_existsUnique x p)

/-- Any bead whose block contains `p` is the block index of `p`. -/
theorem blockIndex_unique {i : Fin x.cubes.length} {p : Fin n} (h : p ∈ blockOf x i) :
    blockIndex x p = i :=
  blockOf_unique x (blockIndex_mem x p) h

/-- **Membership characterisation:** `p` lies in block `i` iff `i` is `p`'s block index. -/
theorem mem_block_iff {i : Fin x.cubes.length} {p : Fin n} :
    p ∈ blockOf x i ↔ blockIndex x p = i :=
  ⟨fun h => blockIndex_unique x h, fun h => h ▸ blockIndex_mem x p⟩

/-- Membership in the `none`-set of the `j`-th bead is exactly having block index `j`. -/
theorem mem_noneSet_get_iff (j : Fin x.cubes.length) (p : Fin n) :
    p ∈ noneSet (toStar (x.cubes.get j).2).val ↔ blockIndex x p = j :=
  mem_block_iff x

/-- The **covector height** of a coordinate: its block index as an integer. Feeds `braidSign`
downstream. -/
def covectorHeight : Fin n → ℤ :=
  fun c => ((blockIndex x c).val : ℤ)

/-- Strict comparison of covector heights is strict comparison of block indices. -/
theorem covectorHeight_lt_iff (p q : Fin n) :
    covectorHeight x p < covectorHeight x q ↔ blockIndex x p < blockIndex x q := by
  simp only [covectorHeight, Nat.cast_lt]
  exact Fin.lt_def.symm

/-- Equality of covector heights is equality of block indices. -/
theorem covectorHeight_eq_iff (p q : Fin n) :
    covectorHeight x p = covectorHeight x q ↔ blockIndex x p = blockIndex x q := by
  simp only [covectorHeight, Nat.cast_inj]
  exact Fin.val_injective.eq_iff

/-! ## Part 4 — functoriality: a refinement induces `⊑` on `braidSign` covectors -/

/-- **The bridge along a refinement.** If `yf` refines `xc`, then `xc`'s block index factors
through `yf`'s along the reindexing map. -/
theorem blockIndex_comp_refinement (xc yf : RefineObj (□n).init (□n).final)
    (g : ChainRefine (□n).init (□n).final yf.cubes xc.cubes) (p : Fin n) :
    blockIndex xc p = g.refinement (blockIndex yf p) := by
  have hpn : (toStar (yf.cubes.get (blockIndex yf p)).2).val p = none :=
    mem_noneSet.mp (blockIndex_mem yf p)
  rw [g.inclSpec (blockIndex yf p), toStar_map_op, app_val] at hpn
  by_cases hp : p ∈ noneSet (toStar (xc.cubes.get (g.refinement (blockIndex yf p))).2).val
  · exact (mem_noneSet_get_iff xc (g.refinement (blockIndex yf p)) p).mp hp
  · rw [dif_neg hp] at hpn
    exact absurd (mem_noneSet.mpr hpn) hp

/-- **Refinement ⟹ `faceLE`.** A `ChainRefine` from `yf` to `xc` (`yf` finer) yields
`braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)` (coarse ⊑ fine). -/
theorem faceLE_of_chainRefine (xc yf : RefineObj (□n).init (□n).final)
    (g : ChainRefine (□n).init (□n).final yf.cubes xc.cubes) :
    braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf) := by
  have hbridge := blockIndex_comp_refinement xc yf g
  rw [faceLE_braidSign_iff_refinesTies]
  intro e hne
  have hxc_ne : blockIndex xc e.1.1 ≠ blockIndex xc e.1.2 :=
    fun h => hne ((covectorHeight_eq_iff xc e.1.1 e.1.2).mpr h)
  have hyf_ne : blockIndex yf e.1.1 ≠ blockIndex yf e.1.2 := by
    intro h; apply hxc_ne; rw [hbridge e.1.1, hbridge e.1.2, h]
  rw [braidSign_apply, braidSign_apply]
  rcases lt_or_gt_of_ne hyf_ne with h | h
  · have hxlt : blockIndex xc e.1.1 < blockIndex xc e.1.2 :=
      lt_of_le_of_ne (by rw [hbridge e.1.1, hbridge e.1.2]; exact g.refinementMono _ _ (le_of_lt h))
        hxc_ne
    rw [sign_neg (by have := (covectorHeight_lt_iff yf e.1.1 e.1.2).mpr h; linarith),
        sign_neg (by have := (covectorHeight_lt_iff xc e.1.1 e.1.2).mpr hxlt; linarith)]
  · have hxgt : blockIndex xc e.1.2 < blockIndex xc e.1.1 :=
      lt_of_le_of_ne (by rw [hbridge e.1.1, hbridge e.1.2]; exact g.refinementMono _ _ (le_of_lt h))
        (Ne.symm hxc_ne)
    rw [sign_pos (by have := (covectorHeight_lt_iff yf e.1.2 e.1.1).mpr h; linarith),
        sign_pos (by have := (covectorHeight_lt_iff xc e.1.2 e.1.1).mpr hxgt; linarith)]

/-! ## Part 5 — the two order-transfer facts of a `faceLE` (the converse direction) -/

section
variable {xc yf : RefineObj (□n).init (□n).final}

/-- On an ordered pair `e`, a `faceLE` transfers the sign of the (nonzero) height difference. -/
theorem faceLE_sign_pair
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf))
    (e : BraidGround n) (hne : covectorHeight xc e.1.1 ≠ covectorHeight xc e.1.2) :
    sign (covectorHeight xc e.1.1 - covectorHeight xc e.1.2)
      = sign (covectorHeight yf e.1.1 - covectorHeight yf e.1.2) := by
  have h := (faceLE_braidSign_iff (covectorHeight xc) (covectorHeight yf)).mp hle e
    ((braidSign_ne_zero_iff (covectorHeight xc) e).mpr hne)
  rw [braidSign_apply, braidSign_apply] at h
  exact h

/-- The unordered version: for any distinct-height pair, the sign of the height difference is
preserved by the finer chain. -/
theorem faceLE_sign
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf))
    (p q : Fin n) (hne : covectorHeight xc p ≠ covectorHeight xc q) :
    sign (covectorHeight xc p - covectorHeight xc q)
      = sign (covectorHeight yf p - covectorHeight yf q) := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact faceLE_sign_pair hle ⟨(p, q), hpq⟩ hne
  · exact absurd (congrArg (covectorHeight xc) hpq) hne
  · have h : sign (covectorHeight xc q - covectorHeight xc p)
        = sign (covectorHeight yf q - covectorHeight yf p) :=
      faceLE_sign_pair hle ⟨(q, p), hpq⟩ (Ne.symm hne)
    rw [show covectorHeight xc p - covectorHeight xc q
          = -(covectorHeight xc q - covectorHeight xc p) by ring,
        show covectorHeight yf p - covectorHeight yf q
          = -(covectorHeight yf q - covectorHeight yf p) by ring,
        Left.sign_neg, Left.sign_neg, h]

/-- **Tie transfer.** A tie of the finer chain forces a tie of the coarser chain. -/
theorem faceLE_eq_of_eq
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf))
    (p q : Fin n) (h : blockIndex yf p = blockIndex yf q) :
    blockIndex xc p = blockIndex xc q := by
  by_contra hxne
  have hvxne : covectorHeight xc p ≠ covectorHeight xc q :=
    fun he => hxne ((covectorHeight_eq_iff xc p q).mp he)
  have hs := faceLE_sign hle p q hvxne
  have hlhs : sign (covectorHeight xc p - covectorHeight xc q) ≠ 0 :=
    sign_ne_zero.mpr (sub_ne_zero.mpr hvxne)
  rw [hs] at hlhs
  exact (sub_ne_zero.mp (sign_ne_zero.mp hlhs)) ((covectorHeight_eq_iff yf p q).mpr h)

/-- **Order transfer.** A strict order of the finer chain implies a weak order of the coarser. -/
theorem faceLE_le_of_lt
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf))
    (p q : Fin n) (h : blockIndex yf p < blockIndex yf q) :
    blockIndex xc p ≤ blockIndex xc q := by
  by_contra hlt
  rw [not_le] at hlt
  have hvxne : covectorHeight xc p ≠ covectorHeight xc q := by
    intro he; rw [(covectorHeight_eq_iff xc p q).mp he] at hlt; exact lt_irrefl _ hlt
  have hs := faceLE_sign hle p q hvxne
  have hvxq : covectorHeight xc q < covectorHeight xc p := (covectorHeight_lt_iff xc q p).mpr hlt
  have hvyp : covectorHeight yf p < covectorHeight yf q := (covectorHeight_lt_iff yf p q).mpr h
  rw [sign_pos (by linarith), sign_neg (by linarith)] at hs
  exact absurd hs (by decide)

end

/-! ## Part 6 — the `Ch (□ⁿ)`-facing layer

`Lines` is a presheaf on `Ch K`, so the covector must be readable off a `Ch` object.  A `Ch`
object carries only `⟨dims, map⟩`; its beads — which is what the partition reads — are recovered by
`wedgeToRefineObj`, which needs no side condition on `K` and stays computable. -/

/-- The **covector height of a `Ch (□ⁿ)` object**: read its beads off the wedge map, then take the
block index. -/
def chCovectorHeight (a : Ch (□n)) : Fin n → ℤ :=
  covectorHeight (wedgeToRefineObj a)

/-- **A `Ch (□ⁿ)` morphism is a refinement**, hence induces `⊑` on covectors: `a ⟶ b` means `a`
subdivides `b`, so `b`'s covector is the coarser (smaller) one. -/
theorem faceLE_of_chHom {a b : Ch (□n)} (g : a ⟶ b) :
    braidSign (chCovectorHeight b) ⊑ braidSign (chCovectorHeight a) :=
  faceLE_of_chainRefine (wedgeToRefineObj b) (wedgeToRefineObj a) (wedgeToRefineMap g)

end CubeChains
