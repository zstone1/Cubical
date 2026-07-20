import CubeChains.Chains.Correspondence
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.Flips
import CubeChains.Arrangements.BraidPreorder

/-!
# Salvetti/BraidPartition — the ordered set partition of a cube chain of `□ⁿ`

A cube chain of `□ⁿ` *is* an ordered set partition of `Fin n`: bead `i`'s block is the set of
coordinates it flips, `noneSet (toStar (bead i))`.  The blocks are pairwise disjoint (a coordinate
never un-flips) and cover `Fin n` (a chain from `init` to `final` flips everything), so `flipIdx`
never returns its sentinel and `blockIndex` is it as a `Fin`; `covectorHeight` is it as an integer,
feeding `braidSign` downstream.
The partition is functorial: a refinement of chains induces `⊑` between the `braidSign` covectors
(`faceLE_of_chainRefine`).
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType

namespace CubeChains

variable {n : ℕ}

/-! ## Part 1 — the cover: every coordinate is flipped (`init → final`) -/

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

/-! ## Part 2 — `blockIndex` and `covectorHeight`

`flipIdx` already names the bead that flips a coordinate, on a raw cube list and with `length` as
its not-found sentinel.  Between `init` and `final` nothing is ever not found, so `blockIndex` is
that same number packaged as a `Fin`. -/

/-- **The block index of a coordinate:** the bead whose block flips it. -/
def blockIndex : Fin n → Fin x.cubes.length :=
  fun p => ⟨flipIdx x.cubes p, flips_of_init_final x p⟩

@[simp] theorem blockIndex_val (p : Fin n) : ((blockIndex x p : ℕ)) = flipIdx x.cubes p := rfl

/-- The block index lands in the block that contains the coordinate. -/
theorem blockIndex_mem (p : Fin n) : p ∈ blockOf x (blockIndex x p) := by
  change p ∈ noneSet (toStar (x.cubes.get (blockIndex x p)).2).val
  rw [List.get_eq_getElem]
  exact mem_noneSet_flipIdx (flips_of_init_final x p)

/-- Any bead whose block contains `p` is the block index of `p`. -/
theorem blockIndex_unique {i : Fin x.cubes.length} {p : Fin n} (h : p ∈ blockOf x i) :
    blockIndex x p = i :=
  Fin.ext (flipIdx_eq_of_mem_blockOf x i h)

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

/-! ## Part 3 — functoriality: a refinement induces `⊑` on `braidSign` covectors -/

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

/-! ## Part 4 — the two order-transfer facts of a `faceLE` (the converse direction) -/

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

/-! ## Part 5 — the `Ch (□ⁿ)`-facing layer

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
