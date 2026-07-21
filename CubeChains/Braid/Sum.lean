import CubeChains.Braid.Generated
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Fin.Basic

/-!
# Braid/Sum — juxtaposition of braids

A braid on `m` strands set beside a braid on `n` strands is a braid on `m + n`.  On permutations
this is the block-diagonal `permSum : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n))` (first `m`
coordinates by `σ`, last `n` by `τ`, transported along `finSumFinEquiv`).

The crossing count adds — `permLen_permSum` — because the two blocks never interact: a low strand
and a high strand keep their order, so no cross-block pair is ever inverted.  That single fact makes
`ofPerm ∘ permSum(·, 1)` and `ofPerm ∘ permSum(1, ·)` respect the germ relations, giving two braid
homs `braidInl`, `braidInr` with commuting images (disjoint blocks), coprod'd into `braidSum`.
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

/-! ## Juxtaposition of braids -/

/-- A crossing-count-preserving hom of permutations lifts to a braid hom: `ofPerm` is functorial in
inclusions that keep the germ relations (length-additive products stay length-additive). -/
def ofPermMap {a b : ℕ} (φ : Perm (Fin a) →* Perm (Fin b))
    (hφ : ∀ σ, permLen (φ σ) = permLen σ) : Braid a →* Braid b :=
  PresentedGroup.toGroup (f := fun σ => ofPerm (φ σ)) (by
    rintro r ⟨σ, τ, hlen, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have hlenφ : permLen (φ σ * φ τ) = permLen (φ σ) + permLen (φ τ) := by
      rw [← map_mul, hφ, hφ, hφ, hlen]
    rw [ofPerm_mul hlenφ, ← map_mul, mul_inv_cancel])

@[simp] theorem ofPermMap_ofPerm {a b : ℕ} (φ : Perm (Fin a) →* Perm (Fin b))
    (hφ : ∀ σ, permLen (φ σ) = permLen σ) (σ : Perm (Fin a)) :
    ofPermMap φ hφ (ofPerm σ) = ofPerm (φ σ) :=
  PresentedGroup.toGroup.of _

theorem permLen_permSum_inl (σ : Perm (Fin m)) :
    permLen ((permSum m n).comp (MonoidHom.inl _ _) σ) = permLen σ := by
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, permLen_permSum, permLen_one, add_zero]

theorem permLen_permSum_inr (τ : Perm (Fin n)) :
    permLen ((permSum m n).comp (MonoidHom.inr _ _) τ) = permLen τ := by
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, permLen_permSum, permLen_one, zero_add]

/-- Juxtapose on the left: a braid on the first `m` of `m + n` strands. -/
def braidInl (m n : ℕ) : Braid m →* Braid (m + n) :=
  ofPermMap ((permSum m n).comp (MonoidHom.inl _ _)) permLen_permSum_inl

/-- Juxtapose on the right: a braid on the last `n` of `m + n` strands. -/
def braidInr (m n : ℕ) : Braid n →* Braid (m + n) :=
  ofPermMap ((permSum m n).comp (MonoidHom.inr _ _)) permLen_permSum_inr

@[simp] theorem braidInl_ofPerm (σ : Perm (Fin m)) :
    braidInl m n (ofPerm σ) = ofPerm (permSum m n (σ, 1)) := by
  rw [braidInl, ofPermMap_ofPerm]; rfl

@[simp] theorem braidInr_ofPerm (τ : Perm (Fin n)) :
    braidInr m n (ofPerm τ) = ofPerm (permSum m n (1, τ)) := by
  rw [braidInr, ofPermMap_ofPerm]; rfl

theorem closure_range_ofPerm :
    Subgroup.closure (Set.range (fun σ : Perm (Fin n) => ofPerm σ)) = ⊤ :=
  PresentedGroup.closure_range_of (germRels n)

/-- On generators, the two blocks commute: both orders build `ofPerm (permSum (σ, τ))`. -/
theorem braidInl_commute_braidInr_gen (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    Commute (braidInl m n (ofPerm σ)) (braidInr m n (ofPerm τ)) := by
  rw [braidInl_ofPerm, braidInr_ofPerm]
  have e1 : ((σ, 1) : Perm (Fin m) × Perm (Fin n)) * (1, τ) = (σ, τ) := by simp
  have e2 : ((1, τ) : Perm (Fin m) × Perm (Fin n)) * (σ, 1) = (σ, τ) := by simp
  have hL : permLen (permSum m n (σ, 1) * permSum m n (1, τ))
      = permLen (permSum m n (σ, 1)) + permLen (permSum m n (1, τ)) := by
    rw [← map_mul, e1]; simp [permLen_permSum]
  have hR : permLen (permSum m n (1, τ) * permSum m n (σ, 1))
      = permLen (permSum m n (1, τ)) + permLen (permSum m n (σ, 1)) := by
    rw [← map_mul, e2]; simp [permLen_permSum, add_comm]
  change ofPerm (permSum m n (σ, 1)) * ofPerm (permSum m n (1, τ))
     = ofPerm (permSum m n (1, τ)) * ofPerm (permSum m n (σ, 1))
  rw [ofPerm_mul hL, ofPerm_mul hR, ← map_mul, ← map_mul, e1, e2]

/-- **Disjoint strand blocks commute.**  Generators commute (`braidInl_commute_braidInr_gen`); the
statement extends to all of `Braid m`, `Braid n` because each side's centralizer is a subgroup and
the `ofPerm`s generate (`closure_range_ofPerm`). -/
theorem braidInl_commute_braidInr (b : Braid m) (c : Braid n) :
    Commute (braidInl m n b) (braidInr m n c) := by
  have step1 : ∀ (σ : Perm (Fin m)) (c : Braid n),
      Commute (braidInl m n (ofPerm σ)) (braidInr m n c) := by
    intro σ c
    have hsub : Set.range (fun τ : Perm (Fin n) => ofPerm τ) ⊆
        (Subgroup.comap (braidInr m n)
          (Subgroup.centralizer {braidInl m n (ofPerm σ)}) : Set (Braid n)) := by
      rintro _ ⟨τ, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (braidInl_commute_braidInr_gen σ τ).symm
    have hmem : c ∈ Subgroup.comap (braidInr m n)
        (Subgroup.centralizer {braidInl m n (ofPerm σ)}) := by
      have hle := (Subgroup.closure_le _).mpr hsub
      rw [closure_range_ofPerm] at hle
      exact hle (Subgroup.mem_top c)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmem
    exact hmem.symm
  have hsub : Set.range (fun σ : Perm (Fin m) => ofPerm σ) ⊆
      (Subgroup.comap (braidInl m n)
        (Subgroup.centralizer {braidInr m n c}) : Set (Braid m)) := by
    rintro _ ⟨σ, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact step1 σ c
  have hmem : b ∈ Subgroup.comap (braidInl m n) (Subgroup.centralizer {braidInr m n c}) := by
    have hle := (Subgroup.closure_le _).mpr hsub
    rw [closure_range_ofPerm] at hle
    exact hle (Subgroup.mem_top b)
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmem
  exact hmem

/-- **Juxtaposition of braids**: `Braid m × Braid n → Braid (m + n)`, the blocks side by side. -/
def braidSum (m n : ℕ) : Braid m × Braid n →* Braid (m + n) :=
  MonoidHom.noncommCoprod (braidInl m n) (braidInr m n) braidInl_commute_braidInr

theorem braidSum_apply (b : Braid m) (c : Braid n) :
    braidSum m n (b, c) = braidInl m n b * braidInr m n c :=
  MonoidHom.noncommCoprod_apply _ _ _ _

/-! ## Compatibility -/

/-- Juxtaposition agrees with `ofPerm`: `braidSum` of two simple braids is the simple braid of the
block-diagonal permutation. -/
theorem braidSum_ofPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    braidSum m n (ofPerm σ, ofPerm τ) = ofPerm (permSum m n (σ, τ)) := by
  rw [braidSum_apply, braidInl_ofPerm, braidInr_ofPerm]
  have e1 : ((σ, 1) : Perm (Fin m) × Perm (Fin n)) * (1, τ) = (σ, τ) := by simp
  have hL : permLen (permSum m n (σ, 1) * permSum m n (1, τ))
      = permLen (permSum m n (σ, 1)) + permLen (permSum m n (1, τ)) := by
    rw [← map_mul, e1]; simp [permLen_permSum]
  rw [ofPerm_mul hL, ← map_mul, e1]

theorem permHom_braidInl (b : Braid m) :
    permHom (m + n) (braidInl m n b) = permSum m n (permHom m b, 1) := by
  have h : (permHom (m + n)).comp (braidInl m n)
      = (permSum m n).comp ((MonoidHom.inl _ _).comp (permHom m)) := by
    ext σ
    simp only [MonoidHom.comp_apply]
    rw [show (PresentedGroup.of σ : Braid m) = ofPerm σ from rfl, braidInl_ofPerm,
      permHom_ofPerm, permHom_ofPerm, MonoidHom.inl_apply]
  exact DFunLike.congr_fun h b

theorem permHom_braidInr (c : Braid n) :
    permHom (m + n) (braidInr m n c) = permSum m n (1, permHom n c) := by
  have h : (permHom (m + n)).comp (braidInr m n)
      = (permSum m n).comp ((MonoidHom.inr _ _).comp (permHom n)) := by
    ext τ
    simp only [MonoidHom.comp_apply]
    rw [show (PresentedGroup.of τ : Braid n) = ofPerm τ from rfl, braidInr_ofPerm,
      permHom_ofPerm, permHom_ofPerm, MonoidHom.inr_apply]
  exact DFunLike.congr_fun h c

/-- **Juxtaposition covers the block-diagonal on permutations.** -/
theorem permHom_braidSum (b : Braid m) (c : Braid n) :
    permHom (m + n) (braidSum m n (b, c)) = permSum m n (permHom m b, permHom n c) := by
  rw [braidSum_apply, map_mul, permHom_braidInl, permHom_braidInr, ← map_mul]
  congr 1

/-- **Pure ⊕ pure is pure.**  A corollary of `permHom_braidSum`: block-diagonal of two identities is
the identity. -/
theorem braidSum_pure {b : Braid m} {c : Braid n}
    (hb : b ∈ PureBraid m) (hc : c ∈ PureBraid n) :
    braidSum m n (b, c) ∈ PureBraid (m + n) := by
  rw [MonoidHom.mem_ker] at hb hc ⊢
  rw [permHom_braidSum, hb, hc]
  exact map_one _

end CubeChains
