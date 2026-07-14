import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Braid/Germ — the braid group, presented by its simple elements

One generator `[σ]` per permutation, and one relation `[σ]·[τ] = [στ]` for each *length-additive*
product — i.e. each product in which **no pair of strands crosses twice**.

The Artin relations are consequences, not axioms: `sᵢsᵢ₊₁sᵢ` and `sᵢ₊₁sᵢsᵢ₊₁` are the *same*
permutation, and both factorisations are length-additive, so both collapse to its single generator.
Commutation is the same argument on `sᵢsⱼ`.  (That the converse holds — that no relation beyond
Artin's is imposed — is Matsumoto's theorem; it is what identifies this group with `Bₙ`.)

Length-additivity is exactly the composition law of refinements (`salCross_add`), which is why the
Salvetti geometry hands us this presentation and not Artin's.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-- The inversions of `σ`: the strand pairs it crosses. -/
def inversions (σ : Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- The length of `σ`: how many pairs it crosses.  The germ reads nothing else. -/
def permLen (σ : Perm (Fin n)) : ℕ := (inversions σ).card

@[simp] theorem permLen_one : permLen (1 : Perm (Fin n)) = 0 := by
  rw [permLen, inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  simp only [Perm.coe_one, id_eq] at h2
  exact absurd h1 (asymm h2)

/-- A permutation and its inverse cross the same pairs, read from the other end. -/
theorem permLen_inv (σ : Perm (Fin n)) : permLen σ⁻¹ = permLen σ := by
  classical
  refine Finset.card_bij' (fun p _ => (σ⁻¹ p.2, σ⁻¹ p.1)) (fun q _ => (σ q.2, σ q.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · rintro ⟨a, b⟩ hq
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨hq.2, by simpa using hq.1⟩
  · rintro ⟨a, b⟩ -
    simp
  · rintro ⟨a, b⟩ -
    simp

/-- The germ relations: a product of simples is their composite exactly when the lengths add. -/
def germRels (n : ℕ) : Set (FreeGroup (Perm (Fin n))) :=
  {r | ∃ σ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ ∧
    r = FreeGroup.of σ * FreeGroup.of τ * (FreeGroup.of (σ * τ))⁻¹}

/-- **The braid group on `n` strands.** -/
abbrev Braid (n : ℕ) : Type := PresentedGroup (germRels n)

/-- The **simple** braid of a permutation — the positive braid realising it with no repeated
crossing.  Here it is a *generator*: there is nothing to construct, and no Matsumoto to prove. -/
def ofPerm (σ : Perm (Fin n)) : Braid n := PresentedGroup.of σ

/-- **The germ relation.**  Refinements compose this way: `writhe` is a functor. -/
theorem ofPerm_mul {σ τ : Perm (Fin n)} (h : permLen (σ * τ) = permLen σ + permLen τ) :
    ofPerm σ * ofPerm τ = ofPerm (σ * τ) := by
  have hr : FreeGroup.of σ * FreeGroup.of τ * (FreeGroup.of (σ * τ))⁻¹ ∈ germRels n :=
    ⟨σ, τ, h, rfl⟩
  simpa [ofPerm, PresentedGroup.of, map_mul] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := germRels n) hr

@[simp] theorem ofPerm_one : ofPerm (1 : Perm (Fin n)) = 1 := by
  have h : ofPerm (1 : Perm (Fin n)) * ofPerm 1 = ofPerm 1 :=
    (ofPerm_mul (σ := (1 : Perm (Fin n))) (τ := 1) (by simp)).trans (by rw [one_mul])
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- The underlying permutation of a braid: `Bₙ ↠ Sₙ`. -/
def permHom (n : ℕ) : Braid n →* Perm (Fin n) :=
  PresentedGroup.toGroup (f := id) (by rintro r ⟨σ, τ, -, rfl⟩; simp)

@[simp] theorem permHom_ofPerm (σ : Perm (Fin n)) : permHom n (ofPerm σ) = σ :=
  PresentedGroup.toGroup.of _

/-- `ofPerm` is a set-section of `permHom`, so every permutation is realised by a simple braid. -/
theorem permHom_surjective : Function.Surjective (permHom n) :=
  fun σ => ⟨ofPerm σ, permHom_ofPerm σ⟩

/-- The **pure** braids: those returning every strand to its own position. -/
abbrev PureBraid (n : ℕ) : Subgroup (Braid n) := (permHom n).ker

end CubeChains
