import CubeChains.Arrangements.Braid
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Filter

/-!
# Arrangements/BraidCovector — a canonical normal form for braid covectors

A covector `braidSign w` of the braid arrangement records only the *relative order* of the values
of `w`.  The dense rank `denseRank w` (see `Arrangements/Braid.lean`) — the number of distinct
values of `w` strictly below `w i` — is the canonical representative: its values are exactly
`{0, 1, …, k-1}` where `k` is the number of distinct values.  This file packages that data as an
**ordered set partition**, i.e. a surjection `blockMap w : Fin n → Fin (numBlocks w)`, and proves
the round trips between covectors and surjections.

-/

open SignType

namespace CubeChains

variable {n : ℕ}

/-! ### Transfer of comparisons through `braidSign` -/

/-- `braidSign w = braidSign w'` determines, for every ordered pair, the sign of the difference. -/
theorem braidSign_sign_transfer {w w' : Fin n → ℤ} (h : braidSign w = braidSign w') (a b : Fin n) :
    sign (w a - w b) = sign (w' a - w' b) := by
  rw [← signAt_braidSign, ← signAt_braidSign, h]

/-- `braidSign` reflects strict comparisons. -/
theorem lt_iff_of_braidSign_eq {w w' : Fin n → ℤ} (h : braidSign w = braidSign w') (a b : Fin n) :
    w a < w b ↔ w' a < w' b := by
  rw [← sub_neg, ← sub_neg (a := w' a)]
  exact (sign_eq_sign_iff.mp (braidSign_sign_transfer h a b)).1

/-- `braidSign` reflects ties (equalities). -/
theorem eq_iff_of_braidSign_eq {w w' : Fin n → ℤ} (h : braidSign w = braidSign w') (a b : Fin n) :
    w a = w b ↔ w' a = w' b := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := w' a), ← sign_eq_zero_iff (a := w a - w b),
    ← sign_eq_zero_iff (a := w' a - w' b), braidSign_sign_transfer h a b]

/-! ### `denseRank` is determined by `braidSign` -/

/-- **Dense rank is a `braidSign` invariant.**  If `w` and `w'` induce the same covector, their
dense ranks agree pointwise.  Proof: `denseRank v i` counts the distinct values of `v` below `v i`,
and this count equals the number of *minimal-index representatives* of those values — a subset of
`Fin n` cut out purely by the strict comparisons and ties of `v`, hence transported by `braidSign`.
-/
theorem denseRank_eq_of_braidSign_eq {w w' : Fin n → ℤ}
    (h : braidSign w = braidSign w') : denseRank w = denseRank w' := by
  classical
  funext i
  have key : ∀ v : Fin n → ℤ, denseRank v i
      = ((Finset.univ.filter
            (fun j => v j < v i ∧ ∀ j', v j' = v j → j ≤ j')).card : ℤ) := by
    intro v
    have hc : ((Finset.univ.image v).filter (· < v i)).card
        = (Finset.univ.filter (fun j => v j < v i ∧ ∀ j', v j' = v j → j ≤ j')).card := by
      symm
      apply Finset.card_bij (fun j _ => v j)
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨Finset.mem_image_of_mem v (Finset.mem_univ a), ha.2.1⟩
      · intro a ha b hb hab
        rw [Finset.mem_filter] at ha hb
        exact le_antisymm (ha.2.2 b hab.symm) (hb.2.2 a hab)
      · intro y hy
        rw [Finset.mem_filter, Finset.mem_image] at hy
        obtain ⟨⟨j0, -, hj0⟩, hylt⟩ := hy
        have hAne : (Finset.univ.filter (fun j => v j = y)).Nonempty :=
          ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩⟩
        have hmemA := Finset.min'_mem (Finset.univ.filter (fun j => v j = y)) hAne
        rw [Finset.mem_filter] at hmemA
        refine ⟨(Finset.univ.filter (fun j => v j = y)).min' hAne, ?_, hmemA.2⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [hmemA.2]; exact hylt
        · intro j' hj'
          exact Finset.min'_le _ j'
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.trans hmemA.2⟩)
    unfold denseRank
    rw [hc]
  rw [key w, key w']
  have hfilter :
      Finset.univ.filter (fun j => w j < w i ∧ ∀ j', w j' = w j → j ≤ j')
        = Finset.univ.filter (fun j => w' j < w' i ∧ ∀ j', w' j' = w' j → j ≤ j') := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨hlt, hmin⟩
      exact ⟨(lt_iff_of_braidSign_eq h j i).mp hlt,
        fun j' hj' => hmin j' ((eq_iff_of_braidSign_eq h j' j).mpr hj')⟩
    · rintro ⟨hlt, hmin⟩
      exact ⟨(lt_iff_of_braidSign_eq h j i).mpr hlt,
        fun j' hj' => hmin j' ((eq_iff_of_braidSign_eq h j' j).mp hj')⟩
  rw [hfilter]

/-- **Idempotence.**  `denseRank` is a projection onto normal forms. -/
theorem denseRank_idem (w : Fin n → ℤ) : denseRank (denseRank w) = denseRank w :=
  denseRank_eq_of_braidSign_eq (braidSign_denseRank w)

/-! ### Density: the image of `denseRank` is an initial segment `{0, …, k-1}` -/

/-- The rank of a value `v` inside a finite set `S ⊆ ℤ`: how many elements of `S` are `< v`. -/
private def rankOn (S : Finset ℤ) (v : ℤ) : ℤ := ((S.filter (· < v)).card : ℤ)

/-- **Density.**  The image of `denseRank w` is exactly `{0, 1, …, k-1}` (as integers), where `k`
is the number of distinct values of `w`.  Equivalently, the rank map is a bijection from the value
set onto `range k`. -/
theorem image_denseRank_eq (w : Fin n → ℤ) :
    Finset.univ.image (denseRank w)
      = (Finset.range (Finset.univ.image w).card).image (fun m : ℕ => (m : ℤ)) := by
  classical
  have castInj : Function.Injective (fun m : ℕ => (m : ℤ)) := Nat.cast_injective
  set S := Finset.univ.image w with hS
  have hdr : Finset.univ.image (denseRank w) = S.image (rankOn S) := by
    have hcomp : denseRank w = rankOn S ∘ w := rfl
    rw [hcomp, ← Finset.image_image, ← hS]
  rw [hdr]
  have hmono : ∀ a b : ℤ, a ∈ S → a < b → rankOn S a < rankOn S b := by
    intro a b haS hab
    change ((S.filter (· < a)).card : ℤ) < ((S.filter (· < b)).card : ℤ)
    exact_mod_cast card_filter_lt_mono' haS hab
  have hInjOn : Set.InjOn (rankOn S) ↑S := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact absurd hab (ne_of_lt (hmono a b (Finset.mem_coe.mp ha) hlt))
    · exact heq
    · exact absurd hab.symm (ne_of_lt (hmono b a (Finset.mem_coe.mp hb) hlt))
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨v, hvS, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨(S.filter (· < v)).card, ?_, rfl⟩
    rw [Finset.mem_range]
    exact card_filter_lt_lt_card' hvS
  · rw [Finset.card_image_of_injective _ castInj, Finset.card_range]
    exact le_of_eq (Finset.card_image_of_injOn hInjOn).symm

/-! ### The block map (ordered set partition) -/

/-- The **number of blocks** of `w`: the number of distinct dense ranks. -/
def numBlocks (w : Fin n → ℤ) : ℕ := (Finset.univ.image (denseRank w)).card

/-- `numBlocks w` is the number of distinct values of `w`. -/
theorem numBlocks_eq_image_card (w : Fin n → ℤ) :
    numBlocks w = (Finset.univ.image w).card := by
  classical
  have castInj : Function.Injective (fun m : ℕ => (m : ℤ)) := Nat.cast_injective
  unfold numBlocks
  rw [image_denseRank_eq, Finset.card_image_of_injective _ castInj, Finset.card_range]

/-- Each dense rank lands below `numBlocks w` (density). -/
theorem denseRank_toNat_lt_numBlocks (w : Fin n → ℤ) (p : Fin n) :
    (denseRank w p).toNat < numBlocks w := by
  classical
  have hmem : denseRank w p ∈ Finset.univ.image (denseRank w) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ p)
  rw [image_denseRank_eq, Finset.mem_image] at hmem
  obtain ⟨m, hm, hmeq⟩ := hmem
  rw [Finset.mem_range] at hm
  have hmeq' : (m : ℤ) = denseRank w p := hmeq
  rw [numBlocks_eq_image_card]
  omega

/-- The **block map**: the ordered-set-partition surjection `Fin n → Fin (numBlocks w)`. -/
def blockMap (w : Fin n → ℤ) (p : Fin n) : Fin (numBlocks w) :=
  ⟨(denseRank w p).toNat, denseRank_toNat_lt_numBlocks w p⟩

/-- The block map is surjective (density). -/
theorem blockMap_surjective (w : Fin n → ℤ) : Function.Surjective (blockMap w) := by
  classical
  intro m
  have hmem : ((m : ℕ) : ℤ) ∈ Finset.univ.image (denseRank w) := by
    rw [image_denseRank_eq, Finset.mem_image]
    exact ⟨(m : ℕ), Finset.mem_range.mpr (by rw [← numBlocks_eq_image_card]; exact m.isLt), rfl⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨p, -, hp⟩ := hmem
  refine ⟨p, ?_⟩
  apply Fin.ext
  change (denseRank w p).toNat = (m : ℕ)
  omega

/-- The canonical realisation `p ↦ blockMap w p` induces the same covector as `w`. -/
theorem braidSign_blockMap (w : Fin n → ℤ) :
    braidSign (fun p => ((blockMap w p : ℕ) : ℤ)) = braidSign w := by
  have hfun : (fun p => ((blockMap w p : ℕ) : ℤ)) = denseRank w := by
    funext p
    change ((denseRank w p).toNat : ℤ) = denseRank w p
    have := denseRank_nonneg w p
    omega
  rw [hfun, braidSign_denseRank]

/-- The block map depends only on the covector. -/
theorem blockMap_congr {w w' : Fin n → ℤ} (h : braidSign w = braidSign w') (p : Fin n) :
    (blockMap w p : ℕ) = (blockMap w' p : ℕ) := by
  change (denseRank w p).toNat = (denseRank w' p).toNat
  rw [denseRank_eq_of_braidSign_eq h]

/-- The number of blocks depends only on the covector. -/
theorem numBlocks_congr {w w' : Fin n → ℤ} (h : braidSign w = braidSign w') :
    numBlocks w = numBlocks w' := by
  unfold numBlocks
  rw [denseRank_eq_of_braidSign_eq h]

/-! ### Converse: recovering a surjection from its canonical height -/

/-- The dense rank of the canonical height `q ↦ β q` of a surjection recovers `β`. -/
theorem denseRank_natCast_val {k : ℕ} (β : Fin n → Fin k) (hβ : Function.Surjective β)
    (p : Fin n) :
    denseRank (fun q => ((β q : ℕ) : ℤ)) p = ((β p : ℕ) : ℤ) := by
  classical
  have castInj : Function.Injective (fun m : ℕ => (m : ℤ)) := Nat.cast_injective
  set w : Fin n → ℤ := fun q => ((β q : ℕ) : ℤ) with hw
  have hbp : (β p : ℕ) < k := (β p).isLt
  have hset : (Finset.univ.image w).filter (· < w p)
      = (Finset.range (β p : ℕ)).image (fun m : ℕ => (m : ℤ)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range,
      hw]
    constructor
    · rintro ⟨⟨q, hqy⟩, hylt⟩
      refine ⟨(β q : ℕ), ?_, hqy⟩
      rw [← hqy] at hylt
      exact_mod_cast hylt
    · rintro ⟨m, hmlt, hmy⟩
      have hmk : m < k := lt_trans hmlt hbp
      obtain ⟨q, hq⟩ := hβ ⟨m, hmk⟩
      refine ⟨⟨q, ?_⟩, ?_⟩
      · rw [hq]; exact hmy
      · rw [← hmy]; exact_mod_cast hmlt
  unfold denseRank
  rw [hset, Finset.card_image_of_injective _ castInj, Finset.card_range]

/-- **Converse round trip (blocks).**  For a surjection `β`, the block map of its canonical height
recovers `β`. -/
theorem blockMap_of_surjective {k : ℕ} (β : Fin n → Fin k) (hβ : Function.Surjective β)
    (p : Fin n) :
    (blockMap (fun q => ((β q : ℕ) : ℤ)) p : ℕ) = (β p : ℕ) := by
  change (denseRank (fun q => ((β q : ℕ) : ℤ)) p).toNat = (β p : ℕ)
  rw [denseRank_natCast_val β hβ p]
  omega

/-- **Converse round trip (count).**  For a surjection `β : Fin n → Fin k`, the canonical height
has exactly `k` blocks.  (When `n = 0` and `k > 0` there is no surjection, so the hypothesis is
false and the statement holds vacuously; when `n = 0` surjectivity forces `k = 0`.) -/
theorem numBlocks_of_surjective {k : ℕ} (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    numBlocks (fun q => ((β q : ℕ) : ℤ)) = k := by
  classical
  have hcastFin : Function.Injective (fun i : Fin k => ((i : ℕ) : ℤ)) :=
    Nat.cast_injective.comp Fin.val_injective
  have himβ : Finset.univ.image β = (Finset.univ : Finset (Fin k)) := by
    rw [Finset.eq_univ_iff_forall]
    intro b
    obtain ⟨q, hq⟩ := hβ b
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩
  rw [numBlocks_eq_image_card]
  have hcomp : (fun q => ((β q : ℕ) : ℤ)) = (fun i : Fin k => ((i : ℕ) : ℤ)) ∘ β := rfl
  rw [hcomp, ← Finset.image_image, Finset.card_image_of_injective _ hcastFin, himβ,
    Finset.card_univ, Fintype.card_fin]

/-- Reindexing a height function by a permutation reindexes its dense rank: the set of values
below is unchanged, only which coordinate reads it. -/
theorem denseRank_comp_perm (w : Fin n → ℤ) (π : Equiv.Perm (Fin n)) (p : Fin n) :
    denseRank (fun q => w (π q)) p = denseRank w (π p) := by
  classical
  have himg : Finset.univ.image (fun q => w (π q)) = Finset.univ.image w := by
    rw [show (fun q => w (π q)) = w ∘ π from rfl, ← Finset.image_image,
      Finset.image_univ_equiv π]
  simp only [denseRank, himg]

/-! ### Covectors → canonical heights (computable)

A covector `Y` names, for every ordered pair, whether `p` ranks below `q` (`covectorBelow`, read
off the sign at that pair).  Summing gives a **computable** canonical height `covectorHeight`
realising `Y` — the `Classical.choice`-free inverse to `braidSign`, so the chain↔face equiv is
computable. -/

/-- `p` ranks strictly below `q` in the covector `Y`, read off the sign of the ordered pair. -/
def covectorBelow (Y : SignVec (BraidGround n)) (p q : Fin n) : Bool := decide (signAt Y p q = -1)

/-- A **computable canonical height** realising `Y`: `q ↦ #{p : p ranks below q}`. -/
def covectorHeight (Y : SignVec (BraidGround n)) (q : Fin n) : ℤ :=
  ((Finset.univ.filter (fun p => covectorBelow Y p q = true)).card : ℤ)

/-- No coordinate ranks below itself. -/
@[simp] theorem covectorBelow_self (Y : SignVec (BraidGround n)) (p : Fin n) :
    covectorBelow Y p p = false := by
  simp [covectorBelow, signAt_self]

/-- On a realised covector, `covectorBelow` is exactly the height order. -/
theorem covectorBelow_braidSign (x : Fin n → ℤ) (p q : Fin n) :
    covectorBelow (braidSign x) p q = decide (x p < x q) := by
  simp only [covectorBelow, signAt_braidSign, sign_eq_neg_one_iff, sub_neg]

/-- `covectorHeight` of a realised covector counts the coordinates strictly below. -/
theorem covectorHeight_braidSign (x : Fin n → ℤ) (q : Fin n) :
    covectorHeight (braidSign x) q = ((Finset.univ.filter (fun p => x p < x q)).card : ℤ) := by
  rw [covectorHeight]
  refine congrArg (fun s : Finset (Fin n) => (s.card : ℤ)) ?_
  ext p
  simp [Finset.mem_filter, covectorBelow_braidSign]

/-- The strict-below count is strictly monotone in the threshold value. -/
theorem covectorHeight_strictMono (x : Fin n → ℤ) {i j : Fin n} (hij : x i < x j) :
    covectorHeight (braidSign x) i < covectorHeight (braidSign x) j := by
  rw [covectorHeight_braidSign, covectorHeight_braidSign]
  exact_mod_cast card_filter_lt_mono (f := x) (Finset.mem_univ i) rfl hij

/-- **The realization.**  The canonical height of a covector realises it: `braidSign` of the height
is the covector back — the strict-below count order-matches `x`. -/
theorem braidSign_covectorHeight (x : Fin n → ℤ) :
    braidSign (covectorHeight (braidSign x)) = braidSign x :=
  braidSign_eq_of_mono (fun _ _ h => covectorHeight_strictMono x h)
    (fun _ _ h => by rw [covectorHeight_braidSign, covectorHeight_braidSign, h])

/-- `covectorHeight` realises any covector of the arrangement. -/
theorem braidSign_covectorHeight_mem {Y : SignVec (BraidGround n)}
    (h : Y ∈ Set.range braidSign) : braidSign (covectorHeight Y) = Y := by
  obtain ⟨x, rfl⟩ := h
  exact braidSign_covectorHeight x

end CubeChains
