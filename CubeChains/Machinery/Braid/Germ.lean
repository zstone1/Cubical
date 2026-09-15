import CubeChains.Machinery.Braid.Length
import Mathlib.GroupTheory.PresentedGroup

/-!
# Machinery/Braid/Germ — the braid group, presented by its simple elements

One generator `[σ]` per permutation, and one relation `[σ]·[τ] = [στ]` for each *length-additive*
product (`Machinery/Braid/Length`) — each product in which **no pair of strands crosses twice**.

The Artin relation is a consequence, not an axiom: its two words are reduced words of one
permutation, so both collapse to its generator.  That nothing beyond it is imposed is Matsumoto's
theorem (`Machinery/Braid/Matsumoto`).  Length-additivity is exactly the composition law of
refinements (`salCross_add`), which is why the Salvetti geometry hands us this presentation.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

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

/-- …with the geometric input in its usual shape: `H` says no pair is crossed twice. -/
theorem ofPerm_mul_of_noDoubleCross {A B : Perm (Fin n)}
    (H : ∀ i j : Fin n, i < j → B j < B i → A (B j) < A (B i)) :
    ofPerm A * ofPerm B = ofPerm (A * B) :=
  ofPerm_mul ((permLen_mul_of_noDoubleCross (σ := B) (ρ := A) H).trans (Nat.add_comm _ _))

/-- The germ relation in **cocycle order**, as a functor's `map_comp` wants it: a composite whose
length splits is the product of its factors, later one first. -/
theorem ofPerm_eq_mul {ρ σ τ : Perm (Fin n)} (hmul : ρ = τ * σ)
    (hlen : permLen ρ = permLen σ + permLen τ) : ofPerm ρ = ofPerm τ * ofPerm σ := by
  rw [hmul, ofPerm_mul (by rw [← hmul]; omega)]

@[simp] theorem ofPerm_one : ofPerm (1 : Perm (Fin n)) = 1 := by
  have h : ofPerm (1 : Perm (Fin n)) * ofPerm 1 = ofPerm 1 :=
    (ofPerm_mul (σ := (1 : Perm (Fin n))) (τ := 1) (by simp)).trans (by rw [one_mul])
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- **The universal property**: a map on simples that is multiplicative on every length-additive
product extends to `Bₙ`. -/
def Braid.lift {G : Type*} [Group G] (g : Perm (Fin n) → G)
    (hmul : ∀ σ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ →
      g σ * g τ = g (σ * τ)) : Braid n →* G :=
  PresentedGroup.toGroup (f := g) (by
    rintro r ⟨σ, τ, h, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hmul σ τ h, mul_inv_cancel])

@[simp] theorem Braid.lift_ofPerm {G : Type*} [Group G] {g : Perm (Fin n) → G} {hmul}
    (σ : Perm (Fin n)) : Braid.lift g hmul (ofPerm σ) = g σ :=
  PresentedGroup.toGroup.of _

/-- The underlying permutation of a braid: `Bₙ ↠ Sₙ`. -/
def permHom (n : ℕ) : Braid n →* Perm (Fin n) := Braid.lift id fun _ _ _ => rfl

@[simp] theorem permHom_ofPerm (σ : Perm (Fin n)) : permHom n (ofPerm σ) = σ :=
  Braid.lift_ofPerm σ

/-- **`Bₙ ↠ Sₙ`** — `ofPerm` is a set-section, so every permutation is realised by a simple
braid, and `PureBraid` below is the kernel of a surjection. -/
theorem permHom_surjective : Function.Surjective (permHom n) :=
  fun σ => ⟨ofPerm σ, permHom_ofPerm σ⟩

/-- The simple braids generate: they are the generators of the presentation. -/
theorem closure_range_ofPerm :
    Subgroup.closure (Set.range (ofPerm : Perm (Fin n) → Braid n)) = ⊤ :=
  PresentedGroup.closure_range_of (germRels n)

/-- The **pure** braids: those returning every strand to its own position. -/
abbrev PureBraid (n : ℕ) : Subgroup (Braid n) := (permHom n).ker

/-! ## The writhe

`Bₙ` abelianises to `ℤ`, and the map is forced: a generator crosses `permLen σ` pairs, and the germ
relation is *exactly* additivity of that count.  So the writhe is a two-line consequence of the
presentation — no arrangement, no Salvetti cell, no `Sₙ`-invariance argument. -/

/-- **The writhe**: the signed crossing count.  A simple braid crosses each inverted pair once. -/
def writheHom (n : ℕ) : Braid n →* Multiplicative ℤ :=
  Braid.lift (fun σ => Multiplicative.ofAdd ((permLen σ : ℤ)))
    (by
      intro σ τ h
      simp only [h]
      push_cast
      rw [ofAdd_add])

@[simp] theorem writheHom_ofPerm (σ : Perm (Fin n)) :
    writheHom n (ofPerm σ) = Multiplicative.ofAdd ((permLen σ : ℤ)) :=
  Braid.lift_ofPerm σ

end CubeChains
