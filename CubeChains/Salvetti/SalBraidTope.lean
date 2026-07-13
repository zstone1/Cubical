import CubeChains.Salvetti.SalBraidPartition
import CubeChains.Salvetti.SalBraidChamberRank
import CubeChains.Arrangements.BraidPreorder

/-!
# Salvetti/SalBraidTope — chamber tuples on a cube chain ↔ topes above its covector

The **objectwise half of STEP E** of `Sal(braidCOM n) ≌ Int(Lines(cube n))`: for a cube
chain `x` of `□ⁿ` (a `RefineObj`, i.e. an ordered set partition of `Fin n`), the chambers
`(RefineLines n).obj (op x)` (one per bead) are in bijection with the topes of `braidCOM n`
lying above `x`'s covector `braidSign (covectorHeight x)`.

The bijection is the **height function**: a chamber tuple `L` sends coordinate `p` to
`heightOf x L p = n · blockIndex(p) + chamberRank(L, p)`.  The `n · blockIndex` term dominates
the bounded chamber rank (`0 ≤ chamberRank < dᵢ ≤ n`), so `heightOf` is injective (a tope) and
refines the block order (`faceLE`).  The inverse reads a chamber off the linear order induced by
an injective height on each block.
-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace CubeChains

open SignVec

/-! ## A domination lemma for `ℤ`

If `0 ≤ v, v' < N` then `N · a + v = N · b + v'` forces `a = b`: the `N`-multiple dominates the
bounded remainders. -/

/-- Domination: with bounded remainders `0 ≤ vₐ, v_b < N`, `N·a + vₐ = N·b + v_b ⟹ a = b`. -/
theorem eq_of_domination {N a b va vb : ℤ} (hN : 0 < N)
    (ha : 0 ≤ va) (ha' : va < N) (hb : 0 ≤ vb) (hb' : vb < N)
    (h : N * a + va = N * b + vb) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have h1 : N * a ≤ N * (b - 1) := mul_le_mul_of_nonneg_left (by omega) hN.le
    have h2 : N * (b - 1) = N * b - N := by ring
    linarith
  · exact heq
  · exfalso
    have h1 : N * b ≤ N * (a - 1) := mul_le_mul_of_nonneg_left (by omega) hN.le
    have h2 : N * (a - 1) = N * a - N := by ring
    linarith

variable {n : ℕ}
variable (x : RefineObj (□n).init (□n).final)

/-! ## STEP 0 — the index bridge

`(RefineLines n).obj (op x)` unfolds to `LinesObj ((cubeChainRefineEquiv n).functor.obj x)`,
whose index type is `Fin (x.cubes.map (·.1)).length` and whose `i`-th bead dimension is
`(x.cubes.map (·.1)).get i`.  These lemmas relate that to `Fin x.cubes.length` /
`(x.cubes.get i).1`. -/

/-- The dimension sequence of the chain associated to `x` has the same length as `x.cubes`. -/
theorem dseqLen : ((cubeChainRefineEquiv n).functor.obj x).dims.length = x.cubes.length :=
  List.length_map _

/-- Its `i`-th entry is the `i`-th bead's dimension (as `ℕ`). -/
theorem dseqGetNat (i : Fin x.cubes.length) :
    (((cubeChainRefineEquiv n).functor.obj x).dims.get (Fin.cast (dseqLen x).symm i) : ℕ)
      = ((x.cubes.get i).1 : ℕ) := by
  have key : ((cubeChainRefineEquiv n).functor.obj x).dims.get (Fin.cast (dseqLen x).symm i)
           = (x.cubes.get i).1 := by
    have e1 : ((cubeChainRefineEquiv n).functor.obj x).dims.get (Fin.cast (dseqLen x).symm i)
            = (x.cubes.map (·.1))[(i : ℕ)]'(by rw [List.length_map]; exact i.isLt) := rfl
    rw [e1, List.getElem_map, List.get_eq_getElem]
  rw [key]

/-- Every bead of a cube chain of `□ⁿ` has dimension at most `n`. -/
theorem beadDim_le (i : Fin x.cubes.length) : ((x.cubes.get i).1 : ℕ) ≤ n :=
  cells_card_le (toStar (x.cubes.get i).2)

/-! ## The local (within-bead) rank of a coordinate -/

/-- The **local rank** of coordinate `p` in block `i` under the chamber tuple `L`: the chamber
rank of `p`'s position among the free directions of bead `i`.  Lands in `[0, dᵢ)`. -/
noncomputable def localRank (L : (RefineLines n).obj (op x)) (i : Fin x.cubes.length)
    (p : Fin n) (hp : p ∈ blockOf x i) : ℤ :=
  chamberRank (L (Fin.cast (dseqLen x).symm i))
    (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp))

/-- The local rank is nonnegative. -/
theorem localRank_nonneg (L : (RefineLines n).obj (op x)) (i : Fin x.cubes.length)
    (p : Fin n) (hp : p ∈ blockOf x i) : 0 ≤ localRank x L i p hp :=
  (chamberRank_bounded (L (Fin.cast (dseqLen x).symm i))
    (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp))).1

/-- The local rank is `< n` (bounded by the bead dimension, which is `≤ n`). -/
theorem localRank_lt (L : (RefineLines n).obj (op x)) (i : Fin x.cubes.length)
    (p : Fin n) (hp : p ∈ blockOf x i) : localRank x L i p hp < n := by
  have hb := (chamberRank_bounded (L (Fin.cast (dseqLen x).symm i))
    (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp))).2
  have hD : (((cubeChainRefineEquiv n).functor.obj x).dims.get (Fin.cast (dseqLen x).symm i) : ℕ)
      ≤ n := by rw [dseqGetNat]; exact beadDim_le x i
  calc localRank x L i p hp
      < (((cubeChainRefineEquiv n).functor.obj x).dims.get (Fin.cast (dseqLen x).symm i) : ℕ) := hb
    _ ≤ (n : ℤ) := by exact_mod_cast hD

/-- The local rank at a fixed bead `i` is injective in the coordinate. -/
theorem localRank_inj (L : (RefineLines n).obj (op x)) (i : Fin x.cubes.length)
    {p q : Fin n} (hp : p ∈ blockOf x i) (hq : q ∈ blockOf x i)
    (h : localRank x L i p hp = localRank x L i q hq) : p = q := by
  have h' : chamberRank (L (Fin.cast (dseqLen x).symm i))
        (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp))
      = chamberRank (L (Fin.cast (dseqLen x).symm i))
        (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) q hq)) := h
  have hci := chamberRank_injective (L (Fin.cast (dseqLen x).symm i)) h'
  have hidx : nonesIdx (toStar (x.cubes.get i).2) p hp
            = nonesIdx (toStar (x.cubes.get i).2) q hq := by
    apply Fin.ext
    have := congrArg Fin.val hci
    simpa using this
  calc p = nones (toStar (x.cubes.get i).2) (nonesIdx (toStar (x.cubes.get i).2) p hp) :=
        (nones_nonesIdx _ _ _).symm
    _ = nones (toStar (x.cubes.get i).2) (nonesIdx (toStar (x.cubes.get i).2) q hq) := by rw [hidx]
    _ = q := nones_nonesIdx _ _ _

/-- The local rank does not depend on the block index up to equality (proof irrelevance). -/
theorem localRank_idx_congr (L : (RefineLines n).obj (op x)) {i j : Fin x.cubes.length}
    (hij : i = j) (p : Fin n) (hp : p ∈ blockOf x i) (hq : p ∈ blockOf x j) :
    localRank x L i p hp = localRank x L j p hq := by
  subst hij; rfl

/-! ## DELIVERABLE 1 — the height function -/

/-- The **height function** of a chamber tuple `L`: coordinate `p` gets `n · blockIndex(p)` plus
the local rank of `p` in its block. -/
noncomputable def heightOf (L : (RefineLines n).obj (op x)) : Fin n → ℤ :=
  fun p => (n : ℤ) * (blockIndex x p : ℤ) + localRank x L (blockIndex x p) p (blockIndex_mem x p)

/-! ## DELIVERABLE 2 — injectivity -/

/-- **The height function is injective.**  The `n · blockIndex` term dominates the bounded local
ranks, so equal heights force equal blocks; within a block `localRank` is injective. -/
theorem heightOf_injective (L : (RefineLines n).obj (op x)) :
    Function.Injective (heightOf x L) := by
  intro p q hpq
  have hnN : 0 < n := by have := p.isLt; omega
  have hn : 0 < (n : ℤ) := by exact_mod_cast hnN
  have hpq' : (n : ℤ) * (blockIndex x p : ℤ)
        + localRank x L (blockIndex x p) p (blockIndex_mem x p)
      = (n : ℤ) * (blockIndex x q : ℤ)
        + localRank x L (blockIndex x q) q (blockIndex_mem x q) := hpq
  have hidxeq : (blockIndex x p : ℤ) = (blockIndex x q : ℤ) :=
    eq_of_domination hn
      (localRank_nonneg x L (blockIndex x p) p (blockIndex_mem x p))
      (localRank_lt x L (blockIndex x p) p (blockIndex_mem x p))
      (localRank_nonneg x L (blockIndex x q) q (blockIndex_mem x q))
      (localRank_lt x L (blockIndex x q) q (blockIndex_mem x q)) hpq'
  have hbeq : blockIndex x p = blockIndex x q := Fin.ext (by exact_mod_cast hidxeq)
  have hlr : localRank x L (blockIndex x p) p (blockIndex_mem x p)
           = localRank x L (blockIndex x q) q (blockIndex_mem x q) := by
    have hmul : (n : ℤ) * (blockIndex x p : ℤ) = (n : ℤ) * (blockIndex x q : ℤ) := by rw [hidxeq]
    linarith [hpq', hmul]
  have hqmem : q ∈ blockOf x (blockIndex x p) := (mem_block_iff x).mpr hbeq.symm
  have hlr2 : localRank x L (blockIndex x p) p (blockIndex_mem x p)
            = localRank x L (blockIndex x p) q hqmem := by
    rw [hlr]
    exact localRank_idx_congr x L hbeq.symm q (blockIndex_mem x q) hqmem
  exact localRank_inj x L (blockIndex x p) (blockIndex_mem x p) hqmem hlr2

/-! ## DELIVERABLE 3 — the height is a tope -/

/-- **The height covector is a tope of `braidCOM n`** (immediate from injectivity). -/
theorem isTope_braidSign_heightOf (L : (RefineLines n).obj (op x)) :
    (braidCOM n).IsTope (braidSign (heightOf x L)) :=
  (braidCOM_isTope_iff_injective _).mpr ⟨heightOf x L, heightOf_injective x L, rfl⟩

/-! ## DELIVERABLE 4 — the height refines the block covector -/

/-- **The height tope lies above `x`'s covector.**  Across two different blocks the
`n · blockIndex` term dominates the bounded local-rank difference, so `heightOf` reproduces the
sign of the block comparison — exactly the face-order condition. -/
theorem faceLE_covectorHeight_heightOf (L : (RefineLines n).obj (op x)) :
    braidSign (covectorHeight x) ⊑ braidSign (heightOf x L) := by
  rw [faceLE_braidSign_iff_refinesTies]
  intro e hne
  have hnN : 0 < n := by have := e.1.1.isLt; omega
  have hn : 0 < (n : ℤ) := by exact_mod_cast hnN
  rw [braidSign_apply, braidSign_apply]
  have hcov : covectorHeight x e.1.1 - covectorHeight x e.1.2
      = (blockIndex x e.1.1 : ℤ) - (blockIndex x e.1.2 : ℤ) := rfl
  rw [hcov]
  have he1 : heightOf x L e.1.1 = (n : ℤ) * (blockIndex x e.1.1 : ℤ)
      + localRank x L (blockIndex x e.1.1) e.1.1 (blockIndex_mem x e.1.1) := rfl
  have he2 : heightOf x L e.1.2 = (n : ℤ) * (blockIndex x e.1.2 : ℤ)
      + localRank x L (blockIndex x e.1.2) e.1.2 (blockIndex_mem x e.1.2) := rfl
  rw [he1, he2]
  have hu : (blockIndex x e.1.1 : ℤ) - (blockIndex x e.1.2 : ℤ) ≠ 0 := sub_ne_zero.mpr hne
  have hli := localRank_nonneg x L (blockIndex x e.1.1) e.1.1 (blockIndex_mem x e.1.1)
  have hli' := localRank_lt x L (blockIndex x e.1.1) e.1.1 (blockIndex_mem x e.1.1)
  have hlj := localRank_nonneg x L (blockIndex x e.1.2) e.1.2 (blockIndex_mem x e.1.2)
  have hlj' := localRank_lt x L (blockIndex x e.1.2) e.1.2 (blockIndex_mem x e.1.2)
  rw [show ((n : ℤ) * (blockIndex x e.1.1 : ℤ)
        + localRank x L (blockIndex x e.1.1) e.1.1 (blockIndex_mem x e.1.1))
      - ((n : ℤ) * (blockIndex x e.1.2 : ℤ)
        + localRank x L (blockIndex x e.1.2) e.1.2 (blockIndex_mem x e.1.2))
      = (n : ℤ) * ((blockIndex x e.1.1 : ℤ) - (blockIndex x e.1.2 : ℤ))
        - (localRank x L (blockIndex x e.1.2) e.1.2 (blockIndex_mem x e.1.2)
          - localRank x L (blockIndex x e.1.1) e.1.1 (blockIndex_mem x e.1.1)) from by ring]
  rw [SignInt.sign_dom_sub hn (by linarith) (by linarith) hu]

/-! ## DELIVERABLE 5 — the inverse: chambers from an injective height -/

/-- A strict total order on `Fin d` pulled back from an injective `f : Fin d → ℤ`. -/
def chamberOfInj {d : ℕ} (f : Fin d → ℤ) (hf : Function.Injective f) : Chamber d where
  lt a b := f a < f b
  sto :=
    { irrefl := fun a => lt_irrefl (f a)
      trans := fun _ _ _ hab hbc => lt_trans hab hbc
      trichotomous := fun _ _ h1 h2 => hf (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) }

@[simp] theorem chamberOfInj_lt {d : ℕ} (f : Fin d → ℤ) (hf : Function.Injective f) (a b : Fin d) :
    (chamberOfInj f hf).lt a b = (f a < f b) := rfl

/-- `nones a i` lies in the free set of `a`. -/
theorem nones_mem {N k : ℕ} (a : Cell N k) (i : Fin k) :
    nones a i ∈ noneSet a.val :=
  Finset.orderEmbOfFin_mem _ a.prop i

/-- `nonesIdx` inverts `nones` (the other round trip). -/
theorem nonesIdx_nones {N k : ℕ} (a : Cell N k) (i : Fin k) :
    nonesIdx a (nones a i) (nones_mem a i) = i :=
  (nones a).injective (nones_nonesIdx a (nones a i) (nones_mem a i))

/-- **The chamber tuple of an injective height `σ`.**  Bead `i` gets the chamber whose direction
order compares the `σ`-values of the corresponding coordinates (`nones` maps directions to
coordinates); a strict total order because `σ` is injective. -/
noncomputable def chambersOf (σ : Fin n → ℤ) (hσ : Function.Injective σ) :
    (RefineLines n).obj (op x) :=
  fun j =>
    chamberOfInj
      (fun a => σ (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)
        (Fin.cast (dseqGetNat x (j.cast (dseqLen x))) a)))
      (fun a b h => by
        apply Fin.ext
        have h1 := (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)).injective (hσ h)
        have := congrArg Fin.val h1
        simpa using this)

/-! ## Round-trip helpers -/

/-- **The height at the `a`-th free direction of bead `i`.**  Coordinate
`nones (bead i) a` gets `n · i` plus the chamber rank of `a`. -/
theorem heightOf_nones (L : (RefineLines n).obj (op x)) (i : Fin x.cubes.length)
    (a : Fin ((x.cubes.get i).1 : ℕ)) :
    heightOf x L (nones (toStar (x.cubes.get i).2) a)
      = (n : ℤ) * (i : ℤ)
        + chamberRank (L (Fin.cast (dseqLen x).symm i)) (Fin.cast (dseqGetNat x i).symm a) := by
  have hp : nones (toStar (x.cubes.get i).2) a ∈ blockOf x i := nones_mem _ a
  have hbi : blockIndex x (nones (toStar (x.cubes.get i).2) a) = i := blockIndex_unique x hp
  have hval : heightOf x L (nones (toStar (x.cubes.get i).2) a)
      = (n : ℤ) * (blockIndex x (nones (toStar (x.cubes.get i).2) a) : ℤ)
        + localRank x L (blockIndex x (nones (toStar (x.cubes.get i).2) a))
            (nones (toStar (x.cubes.get i).2) a)
            (blockIndex_mem x (nones (toStar (x.cubes.get i).2) a)) := rfl
  rw [hval,
    localRank_idx_congr x L hbi (nones (toStar (x.cubes.get i).2) a)
      (blockIndex_mem x (nones (toStar (x.cubes.get i).2) a)) hp, hbi]
  congr 1
  change chamberRank (L (Fin.cast (dseqLen x).symm i))
        (Fin.cast (dseqGetNat x i).symm
          (nonesIdx (toStar (x.cubes.get i).2) (nones (toStar (x.cubes.get i).2) a) hp))
      = chamberRank (L (Fin.cast (dseqLen x).symm i)) (Fin.cast (dseqGetNat x i).symm a)
  congr 2
  exact nonesIdx_nones (toStar (x.cubes.get i).2) a

/-! ## DELIVERABLE 6 — the round trips -/

/-- **Round trip (chambers).**  Reading the height of `L` back into a chamber tuple recovers `L`:
`heightOf` at bead `i` compares the chamber ranks, whose order is exactly `L i`'s. -/
theorem chambersOf_heightOf (L : (RefineLines n).obj (op x)) :
    chambersOf x (heightOf x L) (heightOf_injective x L) = L := by
  funext j
  apply Chamber.ext
  funext a b
  change (heightOf x L (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)
            (Fin.cast (dseqGetNat x (j.cast (dseqLen x))) a))
          < heightOf x L (nones (toStar (x.cubes.get (j.cast (dseqLen x))).2)
            (Fin.cast (dseqGetNat x (j.cast (dseqLen x))) b)))
        = (L j).lt a b
  rw [heightOf_nones, heightOf_nones, add_lt_add_iff_left]
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  exact propext (chamberRank_lt_iff (L j) a b)

/-- Sign of a difference of distinct integers recovers their order. -/
theorem sign_sub_of_ne {a b : ℤ} (h : a ≠ b) :
    SignType.sign (a - b) = if a < b then -1 else 1 := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · rw [if_pos hlt, sign_neg (by omega)]
  · exact absurd heq h
  · rw [if_neg (by omega), sign_pos (by omega)]

/-- The height of `chambersOf σ` at a coordinate `p` of block `i`: `n · i` plus the chamber rank
of `p`'s free-direction index. -/
theorem heightOf_chambersOf_block (σ : Fin n → ℤ) (hσ : Function.Injective σ)
    (i : Fin x.cubes.length) (p : Fin n) (hp : p ∈ blockOf x i) :
    heightOf x (chambersOf x σ hσ) p
      = (n : ℤ) * (i : ℤ) + chamberRank (chambersOf x σ hσ (Fin.cast (dseqLen x).symm i))
          (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp)) := by
  have hbi : blockIndex x p = i := blockIndex_unique x hp
  have hval : heightOf x (chambersOf x σ hσ) p
      = (n : ℤ) * (blockIndex x p : ℤ)
        + localRank x (chambersOf x σ hσ) (blockIndex x p) p (blockIndex_mem x p) := rfl
  rw [hval, localRank_idx_congr x (chambersOf x σ hσ) hbi p (blockIndex_mem x p) hp, hbi]
  rfl

/-- The chamber `chambersOf σ` puts on bead `i` orders directions by `σ` of their coordinates. -/
theorem chambersOf_lt (σ : Fin n → ℤ) (hσ : Function.Injective σ)
    (i : Fin x.cubes.length) (u v : Fin ((x.cubes.get i).1 : ℕ)) :
    (chambersOf x σ hσ (Fin.cast (dseqLen x).symm i)).lt
        (Fin.cast (dseqGetNat x i).symm u) (Fin.cast (dseqGetNat x i).symm v)
      ↔ σ (nones (toStar (x.cubes.get i).2) u) < σ (nones (toStar (x.cubes.get i).2) v) := Iff.rfl

/-- **Within a block, `heightOf (chambersOf σ)` recovers the order of `σ`.**  The `n · i` term
cancels, leaving the chamber-rank comparison, which is exactly the `σ`-comparison. -/
theorem sign_heightOf_chambersOf_block (σ : Fin n → ℤ) (hσ : Function.Injective σ)
    (i : Fin x.cubes.length) (p q : Fin n) (hp : p ∈ blockOf x i) (hq : q ∈ blockOf x i)
    (hpq : p ≠ q) :
    SignType.sign (heightOf x (chambersOf x σ hσ) p - heightOf x (chambersOf x σ hσ) q)
      = SignType.sign (σ p - σ q) := by
  rw [heightOf_chambersOf_block x σ hσ i p hp, heightOf_chambersOf_block x σ hσ i q hq,
    add_sub_add_left_eq_sub]
  have hne : Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp)
           ≠ Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) q hq) := by
    intro h
    apply hpq
    have h2 : nonesIdx (toStar (x.cubes.get i).2) p hp
            = nonesIdx (toStar (x.cubes.get i).2) q hq := by
      apply Fin.ext; have := congrArg Fin.val h; simpa using this
    calc p = nones (toStar (x.cubes.get i).2) (nonesIdx (toStar (x.cubes.get i).2) p hp) :=
          (nones_nonesIdx _ _ _).symm
      _ = nones (toStar (x.cubes.get i).2) (nonesIdx (toStar (x.cubes.get i).2) q hq) := by rw [h2]
      _ = q := nones_nonesIdx _ _ _
  have key := sign_chamberRank_sub (chambersOf x σ hσ (Fin.cast (dseqLen x).symm i))
        (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) p hp))
        (Fin.cast (dseqGetNat x i).symm (nonesIdx (toStar (x.cubes.get i).2) q hq)) hne
  rw [key, sign_sub_of_ne (fun h => hpq (hσ h))]
  simp only [chambersOf_lt, nones_nonesIdx]

/-- **Round trip (topes).**  `heightOf (chambersOf σ)` has the same braid covector as `σ`, provided
`σ`'s tope refines `x`'s block covector (`hface`).  Within a block the orders agree
(`sign_heightOf_chambersOf_block`); across blocks both reproduce the block covector — for
`heightOf` by domination, for `σ` by `hface`. -/
theorem braidSign_heightOf_chambersOf (σ : Fin n → ℤ) (hσ : Function.Injective σ)
    (hface : braidSign (covectorHeight x) ⊑ braidSign σ) :
    braidSign (heightOf x (chambersOf x σ hσ)) = braidSign σ := by
  funext e
  by_cases hb : blockIndex x e.1.1 = blockIndex x e.1.2
  · rw [braidSign_apply, braidSign_apply]
    exact sign_heightOf_chambersOf_block x σ hσ (blockIndex x e.1.1) e.1.1 e.1.2
      (blockIndex_mem x e.1.1) ((mem_block_iff x).mpr hb.symm) (ne_of_lt e.2)
  · have h4 := faceLE_covectorHeight_heightOf x (chambersOf x σ hσ)
    rw [faceLE_braidSign_iff_refinesTies] at h4 hface
    have hcov : covectorHeight x e.1.1 ≠ covectorHeight x e.1.2 := by
      intro h
      apply hb
      have h' : ((blockIndex x e.1.1 : ℕ) : ℤ) = ((blockIndex x e.1.2 : ℕ) : ℤ) := h
      exact Fin.ext (by exact_mod_cast h')
    rw [h4 e hcov, hface e hcov]

end CubeChains
