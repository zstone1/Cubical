import CubeChains.Machinery.Braid.PosGerm
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Machinery/Braid/Sum — juxtaposition of permutations and of braids

A permutation of `m` letters set beside one of `n` letters is the block-diagonal
`permSum : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n))` (first `m` coordinates by `σ`, last
`n` by `τ`, transported along `finSumFinEquiv`).

The crossing count adds — `permLen_permSum` — because the two blocks never interact: a low strand
and a high strand keep their order, so no cross-block pair is ever inverted.  That is what makes
the crossing permutation of a concatenation a block sum (`Concurrency/Grading/WedgeBraid`), and it
is also what lets `permSum` be read in the *monoid*: `posSum` is a monoid homomorphism because
length-additivity is exactly the germ relation.
-/

namespace CubeChains

open Equiv

variable {m n : ℕ}

/-! ## The block-diagonal permutation -/

/-- The block-diagonal permutation: `σ` on the first `m` strands, `τ` on the last `n`. -/
def permSum (m n : ℕ) : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin m) (Fin n))

theorem permSum_apply_inl (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin m) :
    permSum m n (σ, τ) (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (σ i)) := by
  simp only [permSum, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.Perm.sumCongrHom_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]

theorem permSum_apply_inr (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin n) :
    permSum m n (σ, τ) (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr (τ i)) := by
  simp only [permSum, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.Perm.sumCongrHom_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr]

theorem permSum_apply_castAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin m) :
    permSum m n (σ, τ) (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  have := permSum_apply_inl σ τ i
  rwa [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left] at this

theorem permSum_apply_natAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin n) :
    permSum m n (σ, τ) (Fin.natAdd m i) = Fin.natAdd m (τ i) := by
  have := permSum_apply_inr σ τ i
  rwa [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right] at this

/-- **The blocks never interact**: a block-diagonal permutation is trivial exactly when both
blocks are. -/
theorem permSum_eq_one_iff {σ : Perm (Fin m)} {τ : Perm (Fin n)} :
    permSum m n (σ, τ) = 1 ↔ σ = 1 ∧ τ = 1 := by
  refine ⟨fun h => ⟨Equiv.ext fun i => ?_, Equiv.ext fun i => ?_⟩, ?_⟩
  · have hi := Equiv.ext_iff.mp h (Fin.castAdd n i)
    rw [permSum_apply_castAdd] at hi
    exact Fin.castAdd_injective m n hi
  · have hi := Equiv.ext_iff.mp h (Fin.natAdd m i)
    rw [permSum_apply_natAdd] at hi
    exact Fin.natAdd_injective _ _ hi
  · rintro ⟨rfl, rfl⟩
    exact map_one _

/-- The pair `(x, y)` is an inversion of `ρ` iff `x < y` yet `ρ` reverses them. -/
theorem mem_inversions {N : ℕ} {ρ : Perm (Fin N)} {x y : Fin N} :
    (x, y) ∈ inversions ρ ↔ x < y ∧ ρ y < ρ x := by
  simp [inversions]

theorem castAdd_lt_castAdd_iff {i j : Fin m} :
    (Fin.castAdd n i : Fin (m + n)) < Fin.castAdd n j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp

/-- **The crossing count adds.**  The inversions of the block-diagonal permutation split as the
`σ`-inversions (both strands low) and the `τ`-inversions (both high); no cross-block pair inverts,
because every low strand stays below every high one. -/
theorem permLen_permSum (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    permLen (permSum m n (σ, τ)) = permLen σ + permLen τ := by
  classical
  set gL : Fin m × Fin m → Fin (m + n) × Fin (m + n) :=
    fun p => (Fin.castAdd n p.1, Fin.castAdd n p.2) with hgL
  set gR : Fin n × Fin n → Fin (m + n) × Fin (m + n) :=
    fun p => (Fin.natAdd m p.1, Fin.natAdd m p.2) with hgR
  have hinjL : Function.Injective gL := fun ⟨a, b⟩ ⟨c, d⟩ h => by
    simp only [hgL, Prod.mk.injEq] at h
    exact Prod.ext (Fin.castAdd_injective _ _ h.1) (Fin.castAdd_injective _ _ h.2)
  have hinjR : Function.Injective gR := fun ⟨a, b⟩ ⟨c, d⟩ h => by
    simp only [hgR, Prod.mk.injEq] at h
    exact Prod.ext (Fin.natAdd_injective _ _ h.1) (Fin.natAdd_injective _ _ h.2)
  have hset : inversions (permSum m n (σ, τ)) =
      (inversions σ).image gL ∪ (inversions τ).image gR := by
    ext ⟨x, y⟩
    constructor
    · intro hxy
      rw [mem_inversions] at hxy
      obtain ⟨hlt, hinv⟩ := hxy
      revert hlt hinv
      refine x.addCases (fun a => ?_) (fun a => ?_)
      · refine y.addCases (fun b => ?_) (fun b => ?_) <;> intro hlt hinv
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩)
          rw [mem_inversions]
          rw [permSum_apply_castAdd, permSum_apply_castAdd, castAdd_lt_castAdd_iff] at hinv
          exact ⟨castAdd_lt_castAdd_iff.mp hlt, hinv⟩
        · exfalso
          rw [permSum_apply_castAdd, permSum_apply_natAdd, Fin.lt_def] at hinv
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hinv
          have := (σ a).2; omega
      · refine y.addCases (fun b => ?_) (fun b => ?_) <;> intro hlt hinv
        · exfalso
          rw [Fin.lt_def] at hlt
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hlt
          have := b.2; omega
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩)
          rw [mem_inversions]
          rw [permSum_apply_natAdd, permSum_apply_natAdd, Fin.natAdd_lt_natAdd_iff] at hinv
          exact ⟨(Fin.natAdd_lt_natAdd_iff m).mp hlt, hinv⟩
    · intro h
      rw [Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨⟨a, b⟩, hp, hgp⟩ := Finset.mem_image.mp h
        rw [mem_inversions] at hp
        obtain ⟨hlt, hinv⟩ := hp
        simp only [hgL] at hgp
        rw [← hgp, mem_inversions, permSum_apply_castAdd, permSum_apply_castAdd,
          castAdd_lt_castAdd_iff, castAdd_lt_castAdd_iff]
        exact ⟨hlt, hinv⟩
      · obtain ⟨⟨a, b⟩, hp, hgp⟩ := Finset.mem_image.mp h
        rw [mem_inversions] at hp
        obtain ⟨hlt, hinv⟩ := hp
        simp only [hgR] at hgp
        rw [← hgp, mem_inversions, permSum_apply_natAdd, permSum_apply_natAdd,
          Fin.natAdd_lt_natAdd_iff, Fin.natAdd_lt_natAdd_iff]
        exact ⟨hlt, hinv⟩
  have hdisj : Disjoint ((inversions σ).image gL) ((inversions τ).image gR) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxL hxR
    obtain ⟨⟨a, b⟩, -, hx⟩ := Finset.mem_image.mp hxL
    obtain ⟨⟨c, d⟩, -, hx'⟩ := Finset.mem_image.mp hxR
    simp only [hgL, hgR, Prod.mk.injEq] at hx hx'
    have hval : (Fin.castAdd n a : Fin (m + n)).val = (Fin.natAdd m c : Fin (m + n)).val := by
      rw [hx.1, ← hx'.1]
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    have := a.2; omega
  rw [permLen, hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]
  rfl

/-! ## The block-diagonal braid

`permLen` adds across the blocks, and the germ relation *is* length-additivity, so `permSum`
descends to the positive braid monoids.  Nothing is chosen: `posSum` is the unique monoid
homomorphism sending a pair of simples to the simple of their juxtaposition. -/

theorem permSum_left_mul_right (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    permSum m n (σ, 1) * permSum m n (1, τ) = permSum m n (σ, τ) := by
  rw [← map_mul]; exact congrArg _ (Prod.ext (mul_one σ) (one_mul τ))

theorem permSum_right_mul_left (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    permSum m n (1, τ) * permSum m n (σ, 1) = permSum m n (σ, τ) := by
  rw [← map_mul]; exact congrArg _ (Prod.ext (one_mul σ) (mul_one τ))

@[simp] theorem permLen_permSum_left (σ : Perm (Fin m)) :
    permLen (permSum m n (σ, 1)) = permLen σ := by
  rw [permLen_permSum, permLen_one, Nat.add_zero]

@[simp] theorem permLen_permSum_right (τ : Perm (Fin n)) :
    permLen (permSum m n (1, τ)) = permLen τ := by rw [permLen_permSum, permLen_one, Nat.zero_add]

@[simp] theorem permSum_one_one : permSum m n (1, 1) = 1 := map_one _

/-- A braid on the **first** `m` of `m + n` strands. -/
def posSumL (m n : ℕ) : PosBraid m →* PosBraid (m + n) :=
  PosBraid.lift (fun σ => posPerm (permSum m n (σ, 1)))
    (by simp)
    fun σ τ h => by
      have hmul : permSum m n (σ, 1) * permSum m n (τ, 1) = permSum m n (σ * τ, 1) := by
        rw [← map_mul]; exact congrArg _ (Prod.ext rfl (mul_one 1))
      refine (posPerm_mul ?_).trans (congrArg posPerm hmul)
      rw [hmul, permLen_permSum_left, permLen_permSum_left, permLen_permSum_left, h]

/-- …and one on the **last** `n`. -/
def posSumR (m n : ℕ) : PosBraid n →* PosBraid (m + n) :=
  PosBraid.lift (fun τ => posPerm (permSum m n (1, τ)))
    (by simp)
    fun σ τ h => by
      have hmul : permSum m n (1, σ) * permSum m n (1, τ) = permSum m n (1, σ * τ) := by
        rw [← map_mul]; exact congrArg _ (Prod.ext (mul_one 1) rfl)
      refine (posPerm_mul ?_).trans (congrArg posPerm hmul)
      rw [hmul, permLen_permSum_right, permLen_permSum_right, permLen_permSum_right, h]

@[simp] theorem posSumL_posPerm (σ : Perm (Fin m)) :
    posSumL m n (posPerm σ) = posPerm (permSum m n (σ, 1)) := rfl

@[simp] theorem posSumR_posPerm (τ : Perm (Fin n)) :
    posSumR m n (posPerm τ) = posPerm (permSum m n (1, τ)) := rfl

/-- **The blocks commute**, on simples: either order juxtaposes them. -/
theorem commute_posSumL_posSumR_posPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    Commute (posSumL m n (posPerm σ)) (posSumR m n (posPerm τ)) := by
  have hl : permLen (permSum m n (σ, 1) * permSum m n (1, τ))
      = permLen (permSum m n (σ, 1)) + permLen (permSum m n (1, τ)) := by
    rw [permSum_left_mul_right, permLen_permSum, permLen_permSum_left, permLen_permSum_right]
  have hr : permLen (permSum m n (1, τ) * permSum m n (σ, 1))
      = permLen (permSum m n (1, τ)) + permLen (permSum m n (σ, 1)) := by
    rw [permSum_right_mul_left, permLen_permSum, permLen_permSum_left, permLen_permSum_right,
      Nat.add_comm]
  change posPerm _ * posPerm _ = posPerm _ * posPerm _
  rw [posPerm_mul hl, posPerm_mul hr, permSum_left_mul_right, permSum_right_mul_left]

theorem commute_posSumL_posPerm_posSumR (σ : Perm (Fin m)) (b : PosBraid n) :
    Commute (posSumL m n (posPerm σ)) (posSumR m n b) := by
  induction b using PosBraid.induction with
  | one => rw [map_one]; exact Commute.one_right _
  | mul b τ hb => rw [map_mul]; exact hb.mul_right (commute_posSumL_posSumR_posPerm σ τ)

theorem commute_posSumL_posSumR (a : PosBraid m) (b : PosBraid n) :
    Commute (posSumL m n a) (posSumR m n b) := by
  induction a using PosBraid.induction with
  | one => rw [map_one]; exact Commute.one_left _
  | mul a σ ha => rw [map_mul]; exact ha.mul_left (commute_posSumL_posPerm_posSumR σ b)

/-- **Braids in disjoint blocks juxtapose** — `permSum`, read in the monoid where length-additivity
is the germ relation. -/
def posSum (m n : ℕ) : PosBraid m × PosBraid n →* PosBraid (m + n) :=
  (posSumL m n).noncommCoprod (posSumR m n) fun _ _ => commute_posSumL_posSumR _ _

theorem posSum_apply (a : PosBraid m) (b : PosBraid n) :
    posSum m n (a, b) = posSumL m n a * posSumR m n b := rfl

@[simp] theorem posSum_posPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    posSum m n (posPerm σ, posPerm τ) = posPerm (permSum m n (σ, τ)) := by
  rw [posSum_apply, posSumL_posPerm, posSumR_posPerm,
    posPerm_mul (by rw [permSum_left_mul_right, permLen_permSum, permLen_permSum_left,
      permLen_permSum_right]), permSum_left_mul_right]

@[simp] theorem posSum_left (a : PosBraid m) : posSum m n (a, 1) = posSumL m n a := by
  rw [posSum_apply, map_one, mul_one]

@[simp] theorem posSum_right (b : PosBraid n) : posSum m n (1, b) = posSumR m n b := by
  rw [posSum_apply, map_one, one_mul]

/-! ### Bracketing and empty blocks

Three blocks side by side are the same permutation however they are bracketed, and an empty block
changes nothing — the coherence of the juxtaposition, at the level of permutations. -/

theorem permSum_assoc {m n p : ℕ} (σ : Perm (Fin m)) (τ : Perm (Fin n)) (ρ : Perm (Fin p)) :
    (finCongr (Nat.add_assoc m n p)).permCongr (permSum (m + n) p (permSum m n (σ, τ), ρ))
      = permSum m (n + p) (σ, permSum n p (τ, ρ)) := by
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Equiv.permCongr_apply]
  simp only [finCongr_apply, Fin.coe_cast]
  refine x.addCases (fun i => ?_) (fun y => ?_)
  · have hx : (finCongr (Nat.add_assoc m n p)).symm (Fin.castAdd (n + p) i)
        = Fin.castAdd p (Fin.castAdd n i) := Fin.ext (by simp)
    rw [hx, permSum_apply_castAdd, permSum_apply_castAdd, permSum_apply_castAdd]
    simp
  · refine y.addCases (fun j => ?_) (fun k => ?_)
    · have hx : (finCongr (Nat.add_assoc m n p)).symm (Fin.natAdd m (Fin.castAdd p j))
          = Fin.castAdd p (Fin.natAdd m j) := Fin.ext (by simp)
      rw [hx, permSum_apply_castAdd, permSum_apply_natAdd, permSum_apply_natAdd,
        permSum_apply_castAdd]
      simp
    · have hx : (finCongr (Nat.add_assoc m n p)).symm (Fin.natAdd m (Fin.natAdd n k))
          = Fin.natAdd (m + n) k := Fin.ext (by simp; omega)
      rw [hx, permSum_apply_natAdd, permSum_apply_natAdd, permSum_apply_natAdd]
      simp [Nat.add_assoc]

/-- **An empty block on the right changes nothing** — `m + 0` is already `m`. -/
theorem permSum_zero_right (σ : Perm (Fin m)) : permSum m 0 (σ, 1) = σ := by
  refine Equiv.ext fun x => Fin.ext ?_
  refine x.addCases (fun i => ?_) (fun j => j.elim0)
  rw [permSum_apply_castAdd]
  exact congrArg Fin.val (congrArg σ (Fin.ext rfl)).symm ▸ rfl

/-- …and on the left it only renumbers. -/
theorem permSum_zero_left (τ : Perm (Fin n)) :
    permSum 0 n (1, τ) = (finCongr (Nat.zero_add n)).symm.permCongr τ := by
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Equiv.permCongr_apply]
  refine x.addCases (fun i => i.elim0) (fun j => ?_)
  rw [permSum_apply_natAdd]
  have hj : (finCongr (Nat.zero_add n)).symm.symm (Fin.natAdd 0 j) = j := Fin.ext (by simp)
  rw [hj]
  simp

/-! ### Atoms

An atom of a block is an atom of the whole: block sums carry the Artin generators to Artin
generators, which is what makes the block inclusion a map of *generators* and not merely of
words. -/

/-- **An atom of the left block is an atom** — the `k`-th adjacent transposition of `m` strands,
set beside `n` idle ones, is the `k`-th of `m + n`. -/
theorem permSum_adjT_left (k : Fin (m - 1)) (k' : Fin (m + n - 1)) (hk : (k' : ℕ) = (k : ℕ)) :
    permSum m n (adjT k, 1) = adjT k' := by
  refine Equiv.ext fun x => Fin.ext ?_
  refine x.addCases (fun i => ?_) (fun j => ?_)
  · rw [permSum_apply_castAdd]
    simp only [Fin.val_castAdd, adjT_val, hk]
  · rw [permSum_apply_natAdd]
    simp only [Fin.val_natAdd, adjT_val, hk, Equiv.Perm.coe_one, id_eq]
    have h1 := k.2
    split_ifs <;> omega

/-- …and an atom of the right block is the same atom, shifted past the left one. -/
theorem permSum_adjT_right (k : Fin (n - 1)) (k' : Fin (m + n - 1)) (hk : (k' : ℕ) = m + (k : ℕ)) :
    permSum m n (1, adjT k) = adjT k' := by
  refine Equiv.ext fun x => Fin.ext ?_
  refine x.addCases (fun i => ?_) (fun j => ?_)
  · rw [permSum_apply_castAdd]
    simp only [Fin.val_castAdd, adjT_val, hk, Equiv.Perm.coe_one, id_eq]
    have h1 := i.2
    split_ifs <;> omega
  · rw [permSum_apply_natAdd]
    simp only [Fin.val_natAdd, adjT_val, hk]
    split_ifs <;> omega

/-- **Two homomorphisms out of a product of braid monoids agreeing on the two blocks agree** —
`(a, b) = (a, 1) * (1, b)`, and each factor is pinned on the simples. -/
theorem posProd_hom_ext {Q : Type*} [Monoid Q] {φ ψ : PosBraid m × PosBraid n →* Q}
    (hl : ∀ σ : Perm (Fin m), φ (posPerm σ, 1) = ψ (posPerm σ, 1))
    (hr : ∀ τ : Perm (Fin n), φ (1, posPerm τ) = ψ (1, posPerm τ)) : φ = ψ := by
  have hL : φ.comp (MonoidHom.inl _ _) = ψ.comp (MonoidHom.inl _ _) := posPerm_ext hl
  have hR : φ.comp (MonoidHom.inr _ _) = ψ.comp (MonoidHom.inr _ _) := posPerm_ext hr
  refine MonoidHom.ext fun x => ?_
  have hx : x = (x.1, 1) * ((1 : PosBraid m), x.2) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  rw [hx, map_mul, map_mul]
  exact congrArg₂ (· * ·) (congrFun (congrArg DFunLike.coe hL) x.1)
    (congrFun (congrArg DFunLike.coe hR) x.2)

end CubeChains
