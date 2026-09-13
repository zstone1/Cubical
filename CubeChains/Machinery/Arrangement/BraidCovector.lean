import CubeChains.Machinery.Arrangement.Braid
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Hom.Set

/-!
# Machinery/Arrangement/BraidCovector — the ordered set partition of a braid covector

A covector `braidSign w` records only the *relative order* of the values of `w`, i.e. the **ordered
set partition** of `Fin n` into `w`'s level sets.  `blockMap w q` names it — the rank of `w q` among
`w`'s values, read off `Finset.orderIsoOfFin`, so density and order-reflection come from that order
iso and not from a counting argument.

It is the normal form (`blockMap_eq_of_braidSign`), because a surjection onto `Fin L` is pinned by
the order it induces (`eq_of_lt_iff`): the induced map on blocks is a strictly monotone surjection,
hence *the* order iso, hence the identity.
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

/-! ### An ordered set partition is pinned by the order it induces -/

/-- **Two surjections onto a `Fin` that agree on every strict comparison are equal.**  They induce
a strictly monotone surjection `Fin L → Fin L'` on blocks, and that is an order iso — of which
`Fin L` admits exactly one, the identity. -/
theorem eq_of_lt_iff {L L' : ℕ} {β : Fin n → Fin L} {β' : Fin n → Fin L'}
    (hβ : Function.Surjective β) (hβ' : Function.Surjective β')
    (hord : ∀ p q, (β p : ℕ) < (β q : ℕ) ↔ (β' p : ℕ) < (β' q : ℕ)) :
    L = L' ∧ ∀ p, (β p : ℕ) = (β' p : ℕ) := by
  classical
  have hcong : ∀ p q, β p = β q → β' p = β' q := fun p q h =>
    Fin.val_injective (Nat.le_antisymm
      (not_lt.mp fun hc => absurd ((hord q p).mpr hc) (by rw [h]; exact lt_irrefl _))
      (not_lt.mp fun hc => absurd ((hord p q).mpr hc) (by rw [h]; exact lt_irrefl _)))
  set g : Fin L → Fin L' := fun j => β' (hβ j).choose with hgdef
  have hgβ : ∀ p, g (β p) = β' p := fun p => hcong _ _ (hβ (β p)).choose_spec
  have hmono : StrictMono g := by
    intro i j hij
    obtain ⟨p, rfl⟩ := hβ i
    obtain ⟨q, rfl⟩ := hβ j
    rw [hgβ, hgβ, Fin.lt_def]
    exact (hord p q).mp hij
  have hsurj : Function.Surjective g := fun j' =>
    (hβ' j').elim fun p hp => ⟨β p, (hgβ p).trans hp⟩
  obtain rfl : L = L' := by
    simpa using Fintype.card_of_bijective (f := g) ⟨hmono.injective, hsurj⟩
  refine ⟨rfl, fun p => ?_⟩
  have hid : g = (OrderIso.refl (Fin L) : Fin L → Fin L) := by
    rw [← StrictMono.coe_orderIsoOfSurjective g hmono hsurj,
      Subsingleton.elim (StrictMono.orderIsoOfSurjective g hmono hsurj) (OrderIso.refl (Fin L))]
  rw [← hgβ p, hid]
  rfl

/-! ### The block map -/

/-- The **number of blocks** of `w`: the number of distinct values. -/
def numBlocks (w : Fin n → ℤ) : ℕ := (Finset.univ.image w).card

/-- The **block map** of `w`: the rank of `w q` among `w`'s values — the ordered set partition of
`Fin n` into `w`'s level sets, as a surjection `Fin n → Fin (numBlocks w)`. -/
def blockMap (w : Fin n → ℤ) (q : Fin n) : Fin (numBlocks w) :=
  ((Finset.univ.image w).orderIsoOfFin rfl).symm
    ⟨w q, Finset.mem_image_of_mem w (Finset.mem_univ q)⟩

/-- The block map reflects the order: it *is* the rank of the value. -/
theorem blockMap_lt_iff (w : Fin n → ℤ) (p q : Fin n) : blockMap w p < blockMap w q ↔ w p < w q :=
  ((Finset.univ.image w).orderIsoOfFin rfl).symm.lt_iff_lt

/-- The block map reflects ties. -/
theorem blockMap_eq_iff (w : Fin n → ℤ) (p q : Fin n) : blockMap w p = blockMap w q ↔ w p = w q :=
  ((Finset.univ.image w).orderIsoOfFin rfl).symm.injective.eq_iff.trans Subtype.mk_eq_mk

/-- The block map is surjective: every value of `w` is attained, and the rank is a bijection. -/
theorem blockMap_surjective (w : Fin n → ℤ) : Function.Surjective (blockMap w) := by
  intro j
  obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (((Finset.univ.image w).orderIsoOfFin rfl) j).2
  refine ⟨q, ?_⟩
  rw [blockMap, show (⟨w q, Finset.mem_image_of_mem w (Finset.mem_univ q)⟩ :
      {x // x ∈ Finset.univ.image w}) = ((Finset.univ.image w).orderIsoOfFin rfl) j from
    Subtype.ext hq, OrderIso.symm_apply_apply]

/-- The canonical realisation `q ↦ blockMap w q` induces the same covector as `w`. -/
theorem braidSign_blockMap (w : Fin n → ℤ) :
    braidSign (fun q => ((blockMap w q : ℕ) : ℤ)) = braidSign w :=
  braidSign_eq_of_mono
    (fun i j h => by exact_mod_cast (blockMap_lt_iff w i j).mpr h)
    (fun i j h => by rw [(blockMap_eq_iff w i j).mpr h])

/-- **The ordered set partition is the normal form**: any surjection realising `w`'s covector *is*
`w`'s block map. -/
theorem blockMap_eq_of_braidSign {L : ℕ} {w : Fin n → ℤ} {β : Fin n → Fin L}
    (hβ : Function.Surjective β) (h : braidSign (fun q => ((β q : ℕ) : ℤ)) = braidSign w) :
    numBlocks w = L ∧ ∀ q, (blockMap w q : ℕ) = (β q : ℕ) :=
  eq_of_lt_iff (blockMap_surjective w) hβ fun p q => by
    have hb := lt_iff_of_braidSign_eq ((braidSign_blockMap w).trans h.symm) p q
    exact_mod_cast hb

end CubeChains
