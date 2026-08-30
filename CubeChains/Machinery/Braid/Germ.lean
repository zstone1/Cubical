import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Machinery/Braid/Germ — the braid group, presented by its simple elements

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

/-- **Induction on the writhe**: prove `P σ` from `P` at every strictly shorter permutation. -/
theorem permLen_strongRec {P : Perm (Fin n) → Prop}
    (ih : ∀ σ : Perm (Fin n), (∀ τ : Perm (Fin n), permLen τ < permLen σ → P τ) → P σ)
    (σ : Perm (Fin n)) : P σ := by
  suffices H : ∀ k, ∀ σ : Perm (Fin n), permLen σ < k → P σ from H _ σ (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ k hk => exact fun σ h => ih σ fun τ hτ => hk τ (by omega)

@[simp] theorem permLen_one : permLen (1 : Perm (Fin n)) = 0 := by
  rw [permLen, inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  simp only [Perm.coe_one, id_eq] at h2
  exact absurd h1 (asymm h2)

/-- Recounting the strands changes no crossing: `Fin.cast` is an order isomorphism. -/
@[simp] theorem permLen_permCongr_finCongr {m n : ℕ} (h : m = n) (σ : Perm (Fin m)) :
    permLen ((finCongr h).permCongr σ) = permLen σ := by
  subst h
  exact congrArg permLen ((Equiv.apply_eq_iff_eq_symm_apply (finCongr rfl).permCongr).mpr rfl)

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

/-- **Crossings only cancel, never appear**: a pair inverted by `α * β` is inverted by `β`, or its
`β`-image is inverted by `α`. -/
theorem permLen_mul_le (α β : Perm (Fin n)) : permLen (α * β) ≤ permLen α + permLen β := by
  classical
  set f : Fin n × Fin n → Fin n × Fin n := fun q => (β⁻¹ q.1, β⁻¹ q.2) with hf
  have hsub : inversions (α * β) ⊆ inversions β ∪ (inversions α).image f := by
    rintro ⟨i, j⟩ hp
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Perm.mul_apply] at hp
    obtain ⟨hij, hαβ⟩ := hp
    rcases lt_trichotomy (β i) (β j) with hlt | heq | hgt
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(β i, β j), ?_, ?_⟩)
      · simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, hαβ⟩
      · simp [hf]
    · exact absurd (β.injective heq) (ne_of_lt hij)
    · refine Finset.mem_union_left _ ?_
      simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, hgt⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (inversions β) ((inversions α).image f)
  have h3 : ((inversions α).image f).card ≤ (inversions α).card := Finset.card_image_le
  simp only [permLen]
  omega

/-- **Lengths add when no pair is crossed twice.**  `H` says every pair `σ` crosses stays crossed
by `ρσ` — the composite never *un*-crosses it — which forces the inversion sets of `σ` and `ρ` to
combine without overlap.  This is the whole content of the germ relation `[σ][τ] = [στ]`; the
geometry only has to supply `H`. -/
theorem permLen_mul_of_noDoubleCross {σ ρ : Perm (Fin n)}
    (H : ∀ i j : Fin n, i < j → σ j < σ i → ρ (σ j) < ρ (σ i)) :
    permLen (ρ * σ) = permLen σ + permLen ρ := by
  classical
  -- Every `σ`-inversion is a `ρσ`-inversion (this is exactly `H`).
  have hsub : inversions σ ⊆ inversions (ρ * σ) := by
    rintro ⟨a, b⟩ hp
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Perm.mul_apply] at hp ⊢
    exact ⟨hp.1, H a b hp.1 hp.2⟩
  -- The extra `ρσ`-inversions biject with the `ρ`-inversions via `σ`.
  have hbij : (inversions (ρ * σ) \ inversions σ).card = (inversions ρ).card := by
    refine Finset.card_bij' (fun p _ => (σ p.1, σ p.2)) (fun q _ => (σ⁻¹ q.1, σ⁻¹ q.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_sdiff, inversions, Finset.mem_filter, Finset.mem_univ, true_and,
        Perm.mul_apply, not_and, not_lt] at hp ⊢
      obtain ⟨⟨hab, hρ⟩, hσ⟩ := hp
      exact ⟨lt_of_le_of_ne (hσ hab) (σ.injective.ne (ne_of_lt hab)), hρ⟩
    · rintro ⟨a, b⟩ hq
      have hsa : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
      have hsb : σ (σ⁻¹ b) = b := σ.apply_symm_apply b
      simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨hab, hρ⟩ := hq
      have hlt : σ⁻¹ a < σ⁻¹ b := by
        by_contra hc
        rw [not_lt] at hc
        have hne : σ⁻¹ b ≠ σ⁻¹ a := fun h => (ne_of_lt hab) (σ⁻¹.injective h).symm
        have hcond : σ (σ⁻¹ a) < σ (σ⁻¹ b) := by rw [hsa, hsb]; exact hab
        have := H (σ⁻¹ b) (σ⁻¹ a) (lt_of_le_of_ne hc hne) (by rw [hsa, hsb]; exact hab)
        rw [hsa, hsb] at this
        exact absurd hρ (asymm this)
      simp only [Finset.mem_sdiff, inversions, Finset.mem_filter, Finset.mem_univ, true_and,
        Perm.mul_apply, hsa, hsb, not_and, not_lt]
      exact ⟨⟨hlt, hρ⟩, fun _ => le_of_lt hab⟩
    · rintro ⟨a, b⟩ -
      simp
    · rintro ⟨a, b⟩ -
      simp
  rw [permLen, permLen, permLen, ← hbij, add_comm, Finset.card_sdiff_add_card_eq_card hsub]

/-- **Lengths add along a cocycle** whose middle count is only propositionally the source's: `ρ` is
the composite (`hmul`) and no pair crosses twice (`H`). -/
theorem permLen_of_cocycle_noDoubleCross {m n : ℕ} (hmn : m = n) {σ ρ : Perm (Fin m)}
    {τ : Perm (Fin n)} (hmul : ∀ i, finCongr hmn (ρ i) = τ (finCongr hmn (σ i)))
    (H : ∀ i j : Fin m, i < j → σ j < σ i →
      τ (finCongr hmn (σ j)) < τ (finCongr hmn (σ i))) :
    permLen ρ = permLen σ + permLen τ := by
  subst hmn
  simp only [finCongr_refl, Equiv.refl_apply] at hmul H
  have hρ : ρ = τ * σ := Equiv.ext hmul
  rw [hρ]
  exact permLen_mul_of_noDoubleCross H

/-- **The reversal crosses every pair**, so any factorisation of it is length-additive — the
length-additivity behind Garside's `Δ`. -/
theorem permLen_mul_of_eq_rev {σ τ : Perm (Fin n)} (h : σ * τ = Fin.revPerm) :
    permLen (σ * τ) = permLen σ + permLen τ :=
  (permLen_mul_of_noDoubleCross (σ := τ) (ρ := σ) fun i j hij _ => by
    have hk : ∀ k, σ (τ k) = k.rev := fun k => by
      rw [← Perm.mul_apply, h, Fin.revPerm_apply]
    rw [hk, hk]
    exact Fin.rev_strictAnti hij).trans (Nat.add_comm _ _)

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

/-- `ofPerm` is a set-section of `permHom`, so every permutation is realised by a simple braid. -/
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
