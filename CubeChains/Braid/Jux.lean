import CubeChains.Braid.BlockPerm
import CubeChains.Braid.Germ
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Braid/Jux — juxtaposition of braids

Placing an `n`-braid beside an `m`-braid gives an `(n+m)`-braid, and **no strand of one block ever
crosses a strand of the other**.  That is the whole content: cross-block pairs are never inverted,
so `permLen` adds (`permLen_blockPerm`), so juxtaposition respects the germ relations.

`juxHom` is the tensor of the braid category, and `permLen_blockPerm` is why concatenating
executions *juxtaposes* their braids rather than mixing them.
-/

namespace CubeChains

open Equiv

variable {n m : ℕ}

/-! ## Cross-block pairs are never inverted -/

/-- A strand of block 1, named. -/
private theorem blockPerm_lt_of_lt (σ : Perm (Fin n)) (τ : Perm (Fin m)) (a : Fin (n + m))
    (h : (a : ℕ) < n) : ((blockPerm σ τ a : Fin (n + m)) : ℕ) < n := by
  rw [blockPerm_val_lt σ τ a ⟨(a : ℕ), h⟩ rfl]
  exact (σ ⟨(a : ℕ), h⟩).isLt

/-- A strand of block 2, named. -/
private theorem blockPerm_ge_of_ge (σ : Perm (Fin n)) (τ : Perm (Fin m)) (a : Fin (n + m))
    (h : ¬ (a : ℕ) < n) : n ≤ ((blockPerm σ τ a : Fin (n + m)) : ℕ) := by
  have ha : (a : ℕ) = n + ((a : ℕ) - n) := by omega
  have hlt : (a : ℕ) - n < m := by have := a.isLt; omega
  rw [blockPerm_val_ge σ τ a ⟨(a : ℕ) - n, hlt⟩ ha]
  omega

/-- **Juxtaposition adds lengths**: within each block the crossings are the block's own, and a pair
straddling the two blocks is never inverted — block 1 finishes before block 2 begins. -/
theorem permLen_blockPerm (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    permLen (blockPerm σ τ) = permLen σ + permLen τ := by
  classical
  set L : Finset (Fin (n + m) × Fin (n + m)) :=
    (inversions σ).image (fun p => (Fin.castAdd m p.1, Fin.castAdd m p.2)) with hLdef
  set R : Finset (Fin (n + m) × Fin (n + m)) :=
    (inversions τ).image (fun p => (Fin.natAdd n p.1, Fin.natAdd n p.2)) with hRdef
  -- the two images are disjoint: block 1 lives below `n`, block 2 at or above it
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ haL haR
    rw [hLdef, Finset.mem_image] at haL
    rw [hRdef, Finset.mem_image] at haR
    obtain ⟨⟨i, j⟩, -, hij⟩ := haL
    obtain ⟨⟨i', j'⟩, -, hij'⟩ := haR
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp hij
    obtain ⟨ha, -⟩ := Prod.ext_iff.mp hij'
    have := congrArg Fin.val ha
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    omega
  have hcardL : L.card = permLen σ := by
    rw [hLdef, Finset.card_image_of_injective, permLen]
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    exact Prod.ext (Fin.ext (by simpa using congrArg Fin.val h1))
      (Fin.ext (by simpa using congrArg Fin.val h2))
  have hcardR : R.card = permLen τ := by
    rw [hRdef, Finset.card_image_of_injective, permLen]
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    exact Prod.ext (Fin.ext (by simpa using congrArg Fin.val h1))
      (Fin.ext (by simpa using congrArg Fin.val h2))
  have hkey : inversions (blockPerm σ τ) = L ∪ R := by
    ext ⟨a, b⟩
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hLdef,
      hRdef, Finset.mem_image, Prod.exists, Prod.mk.injEq, Fin.lt_def]
    constructor
    · rintro ⟨hab, hinv⟩
      by_cases hb : (b : ℕ) < n
      · -- both in block 1
        have ha : (a : ℕ) < n := by omega
        refine Or.inl ⟨⟨(a : ℕ), ha⟩, ⟨(b : ℕ), hb⟩, ⟨hab, ?_⟩, Fin.ext rfl, Fin.ext rfl⟩
        rw [← blockPerm_val_lt σ τ b ⟨(b : ℕ), hb⟩ rfl, ← blockPerm_val_lt σ τ a ⟨(a : ℕ), ha⟩ rfl]
        exact hinv
      · by_cases ha : (a : ℕ) < n
        · -- straddling: block 1 finishes before block 2 begins, so never an inversion
          exact absurd hinv (by
            have h1 := blockPerm_lt_of_lt σ τ a ha
            have h2 := blockPerm_ge_of_ge σ τ b hb
            omega)
        · -- both in block 2
          have hai : (a : ℕ) - n < m := by have := a.isLt; omega
          have hbi : (b : ℕ) - n < m := by have := b.isLt; omega
          have hae : (a : ℕ) = n + ((a : ℕ) - n) := by omega
          have hbe : (b : ℕ) = n + ((b : ℕ) - n) := by omega
          have h1 := blockPerm_val_ge σ τ a ⟨(a : ℕ) - n, hai⟩ hae
          have h2 := blockPerm_val_ge σ τ b ⟨(b : ℕ) - n, hbi⟩ hbe
          refine Or.inr ⟨⟨(a : ℕ) - n, hai⟩, ⟨(b : ℕ) - n, hbi⟩, ⟨?_, ?_⟩,
            Fin.ext (by simpa using hae.symm), Fin.ext (by simpa using hbe.symm)⟩
          · change (a : ℕ) - n < (b : ℕ) - n
            omega
          · change ((τ ⟨(b : ℕ) - n, hbi⟩ : Fin m) : ℕ) < ((τ ⟨(a : ℕ) - n, hai⟩ : Fin m) : ℕ)
            omega
    · rintro (⟨i, j, ⟨hij, hinv⟩, rfl, rfl⟩ | ⟨i, j, ⟨hij, hinv⟩, rfl, rfl⟩)
      · refine ⟨by simpa using hij, ?_⟩
        rw [blockPerm_val_lt σ τ (Fin.castAdd m j) j (by simp),
          blockPerm_val_lt σ τ (Fin.castAdd m i) i (by simp)]
        exact hinv
      · have hi : ((Fin.natAdd n i : Fin (n + m)) : ℕ) = n + (i : ℕ) := by simp
        have hj : ((Fin.natAdd n j : Fin (n + m)) : ℕ) = n + (j : ℕ) := by simp
        refine ⟨by omega, ?_⟩
        rw [blockPerm_val_ge σ τ (Fin.natAdd n j) j hj, blockPerm_val_ge σ τ (Fin.natAdd n i) i hi]
        omega
  rw [permLen, hkey, Finset.card_union_of_disjoint hdisj, hcardL, hcardR]

/-! ## Juxtaposition of braids -/

/-- A braid on `n` strands, sitting in the first block of `n + m`. -/
def juxL (n m : ℕ) : Braid n →* Braid (n + m) :=
  PresentedGroup.toGroup (f := fun σ => ofPerm (blockPerm σ (1 : Perm (Fin m)))) (by
    rintro r ⟨σ, τ, hlen, rfl⟩
    have hmul : blockPerm σ (1 : Perm (Fin m)) * blockPerm τ (1 : Perm (Fin m))
        = blockPerm (σ * τ) (1 : Perm (Fin m)) := by
      rw [← blockPerm_mul, one_mul]
    have h : permLen (blockPerm σ (1 : Perm (Fin m)) * blockPerm τ (1 : Perm (Fin m)))
        = permLen (blockPerm σ (1 : Perm (Fin m))) + permLen (blockPerm τ (1 : Perm (Fin m))) := by
      rw [hmul]
      simp only [permLen_blockPerm, permLen_one]
      omega
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [ofPerm_mul h, hmul, mul_inv_cancel])

/-- A braid on `m` strands, sitting in the second block of `n + m`. -/
def juxR (n m : ℕ) : Braid m →* Braid (n + m) :=
  PresentedGroup.toGroup (f := fun τ => ofPerm (blockPerm (1 : Perm (Fin n)) τ)) (by
    rintro r ⟨σ, τ, hlen, rfl⟩
    have hmul : blockPerm (1 : Perm (Fin n)) σ * blockPerm (1 : Perm (Fin n)) τ
        = blockPerm (1 : Perm (Fin n)) (σ * τ) := by
      rw [← blockPerm_mul, one_mul]
    have h : permLen (blockPerm (1 : Perm (Fin n)) σ * blockPerm (1 : Perm (Fin n)) τ)
        = permLen (blockPerm (1 : Perm (Fin n)) σ) + permLen (blockPerm (1 : Perm (Fin n)) τ) := by
      rw [hmul]
      simp only [permLen_blockPerm, permLen_one]
      omega
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [ofPerm_mul h, hmul, mul_inv_cancel])

@[simp] theorem juxL_ofPerm (σ : Perm (Fin n)) :
    juxL n m (ofPerm σ) = ofPerm (blockPerm σ (1 : Perm (Fin m))) :=
  PresentedGroup.toGroup.of _

@[simp] theorem juxR_ofPerm (τ : Perm (Fin m)) :
    juxR n m (ofPerm τ) = ofPerm (blockPerm (1 : Perm (Fin n)) τ) :=
  PresentedGroup.toGroup.of _

/-- Anything true of the generators and closed under the group operations is true of every braid. -/
theorem braid_mem_of_gens {H : Subgroup (Braid n)} (hgen : ∀ σ, ofPerm σ ∈ H) (x : Braid n) :
    x ∈ H := by
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : Perm (Fin n) → Braid n)) := by
    rw [PresentedGroup.closure_range_of]; trivial
  exact (Subgroup.closure_le H).mpr (by rintro _ ⟨σ, rfl⟩; exact hgen σ) hx

/-- **The blocks do not interact**: a simple braid of block 1 commutes with one of block 2, because
each of the two products is the same juxtaposition. -/
private theorem commute_gens (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    Commute (ofPerm (blockPerm σ (1 : Perm (Fin m))))
      (ofPerm (blockPerm (1 : Perm (Fin n)) τ)) := by
  have h1 : blockPerm σ (1 : Perm (Fin m)) * blockPerm (1 : Perm (Fin n)) τ = blockPerm σ τ := by
    rw [← blockPerm_mul, mul_one, one_mul]
  have h2 : blockPerm (1 : Perm (Fin n)) τ * blockPerm σ (1 : Perm (Fin m)) = blockPerm σ τ := by
    rw [← blockPerm_mul, mul_one, one_mul]
  have hL : permLen (blockPerm σ (1 : Perm (Fin m)) * blockPerm (1 : Perm (Fin n)) τ)
      = permLen (blockPerm σ (1 : Perm (Fin m))) + permLen (blockPerm (1 : Perm (Fin n)) τ) := by
    rw [h1]
    simp only [permLen_blockPerm, permLen_one]
    omega
  have hR : permLen (blockPerm (1 : Perm (Fin n)) τ * blockPerm σ (1 : Perm (Fin m)))
      = permLen (blockPerm (1 : Perm (Fin n)) τ) + permLen (blockPerm σ (1 : Perm (Fin m))) := by
    rw [h2]
    simp only [permLen_blockPerm, permLen_one]
    omega
  change _ * _ = _ * _
  rw [ofPerm_mul hL, ofPerm_mul hR, h1, h2]

theorem juxL_commute_juxR (a : Braid n) (b : Braid m) :
    Commute (juxL n m a) (juxR n m b) := by
  -- a generator of block 1 commutes with *every* block-2 braid …
  have hgenL : ∀ (σ : Perm (Fin n)) (y : Braid m),
      Commute (juxL n m (ofPerm σ)) (juxR n m y) := by
    intro σ y
    have hy : y ∈ (Subgroup.centralizer {juxL n m (ofPerm σ)}).comap (juxR n m) :=
      braid_mem_of_gens (fun τ => by
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        rintro g rfl
        simpa using commute_gens σ τ) y
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hy
    exact hy _ rfl
  -- … hence so does every block-1 braid.
  have ha : a ∈ (Subgroup.centralizer {juxR n m b}).comap (juxL n m) :=
    braid_mem_of_gens (fun σ => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro g rfl
      exact (hgenL σ b).symm) a
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at ha
  exact (ha _ rfl).symm

/-- **The tensor of the braid category**: juxtapose, and strand counts add. -/
def juxHom (n m : ℕ) : Braid n × Braid m →* Braid (n + m) :=
  (juxL n m).noncommCoprod (juxR n m) juxL_commute_juxR

theorem juxHom_eq (a : Braid n) (b : Braid m) :
    juxHom n m (a, b) = juxL n m a * juxR n m b :=
  MonoidHom.noncommCoprod_apply _ _ _ _

@[simp] theorem juxHom_one_right (a : Braid n) : juxHom n m (a, (1 : Braid m)) = juxL n m a := by
  rw [juxHom_eq, map_one, mul_one]

@[simp] theorem juxHom_one_left (b : Braid m) : juxHom n m ((1 : Braid n), b) = juxR n m b := by
  rw [juxHom_eq, map_one, one_mul]

@[simp] theorem juxHom_ofPerm (σ : Perm (Fin n)) (τ : Perm (Fin m)) :
    juxHom n m (ofPerm σ, ofPerm τ) = ofPerm (blockPerm σ τ) := by
  have h1 : blockPerm σ (1 : Perm (Fin m)) * blockPerm (1 : Perm (Fin n)) τ = blockPerm σ τ := by
    rw [← blockPerm_mul, mul_one, one_mul]
  have hL : permLen (blockPerm σ (1 : Perm (Fin m)) * blockPerm (1 : Perm (Fin n)) τ)
      = permLen (blockPerm σ (1 : Perm (Fin m))) + permLen (blockPerm (1 : Perm (Fin n)) τ) := by
    rw [h1]
    simp only [permLen_blockPerm, permLen_one]
    omega
  rw [juxHom, MonoidHom.noncommCoprod_apply, juxL_ofPerm, juxR_ofPerm, ofPerm_mul hL, h1]

end CubeChains
