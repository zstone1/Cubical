import CubeChains.Braid.Germ
import Mathlib.GroupTheory.Perm.Support

/-!
# Braid/Artin — the Artin presentation versus the Garside germ

`GarsideBraid n` is `Braid n`, the germ presentation of `Braid/Germ`.  `ArtinBraid n` is the
classical Artin presentation (adjacent transpositions, braid + commutation relations).

There is an *easy* group homomorphism `garsideOfArtin : ArtinBraid n →* GarsideBraid n` (the Artin
relations are length-additive facts, discharged by `permLen_mul_of_noDoubleCross`).  Upgrading it to
an isomorphism is exactly **Matsumoto's theorem for `Sₙ`** — the well-definedness of the positive
lift `σ ↦ σ̂`.  Mathlib does not provide it (`Coxeter/Basic` lists it as an open TODO and has no
type-A instance), so we state it as an explicit hypothesis `Matsumoto n` and derive the isomorphism
`garside_equiv_artin : Matsumoto n → (GarsideBraid n ≃* ArtinBraid n)` from it.
-/

namespace CubeChains

open Equiv

/-- The Garside (germ) braid group, under a name that pairs with `ArtinBraid`. -/
abbrev GarsideBraid (n : ℕ) : Type := Braid n

variable {n : ℕ}

/-! ## Adjacent transpositions -/

/-- Low endpoint of the `k`-th adjacent transposition. -/
def adjLo (k : Fin (n - 1)) : Fin n := ⟨k.1, by have := k.2; omega⟩

/-- High endpoint of the `k`-th adjacent transposition. -/
def adjHi (k : Fin (n - 1)) : Fin n := ⟨k.1 + 1, by have := k.2; omega⟩

@[simp] theorem adjLo_val (k : Fin (n - 1)) : (adjLo k).1 = k.1 := rfl
@[simp] theorem adjHi_val (k : Fin (n - 1)) : (adjHi k).1 = k.1 + 1 := rfl

/-- The `k`-th adjacent transposition, swapping `k` and `k+1`. -/
def adjT (k : Fin (n - 1)) : Perm (Fin n) := Equiv.swap (adjLo k) (adjHi k)

theorem adjT_lo (k : Fin (n - 1)) : adjT k (adjLo k) = adjHi k := swap_apply_left _ _
theorem adjT_hi (k : Fin (n - 1)) : adjT k (adjHi k) = adjLo k := swap_apply_right _ _

theorem adjT_of_ne (k : Fin (n - 1)) {x : Fin n} (h1 : x.1 ≠ k.1) (h2 : x.1 ≠ k.1 + 1) :
    adjT k x = x :=
  swap_apply_of_ne_of_ne (fun heq => h1 (congrArg Fin.val heq))
    (fun heq => h2 (congrArg Fin.val heq))

/-- The value of `adjT k x`: it swaps the values `k` and `k+1`, and fixes everything else. -/
theorem adjT_val (k : Fin (n - 1)) (x : Fin n) :
    (adjT k x).1 = if x.1 = k.1 then k.1 + 1 else if x.1 = k.1 + 1 then k.1 else x.1 := by
  by_cases h1 : x.1 = k.1
  · rw [if_pos h1]
    have hx : x = adjLo k := Fin.ext h1
    rw [hx, adjT_lo, adjHi_val]
  · rw [if_neg h1]
    by_cases h2 : x.1 = k.1 + 1
    · rw [if_pos h2]
      have hx : x = adjHi k := Fin.ext h2
      rw [hx, adjT_hi, adjLo_val]
    · rw [if_neg h2, adjT_of_ne k h1 h2]

/-- **A simple swap inverts only its own pair.**  If a refinement of the order by an adjacent
transposition reverses the pair `p < q`, then `p, q` are exactly the two swapped points. -/
theorem adjT_inverts (k : Fin (n - 1)) {p q : Fin n} (hpq : p < q)
    (hinv : adjT k q < adjT k p) : p = adjLo k ∧ q = adjHi k := by
  rw [Fin.lt_def] at hpq hinv
  rw [adjT_val, adjT_val] at hinv
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [adjLo_val, adjHi_val] <;>
    (split_ifs at hinv <;> omega)

/-! ## Length-additivity for adjacent transpositions -/

/-- `ofPerm` is multiplicative on length-additive products; the geometric input is the crossing
criterion `H` (no pair crossed twice). -/
theorem ofPerm_mul_of_noDoubleCross {A B : Perm (Fin n)}
    (H : ∀ i j : Fin n, i < j → B j < B i → A (B j) < A (B i)) :
    ofPerm A * ofPerm B = ofPerm (A * B) :=
  ofPerm_mul ((permLen_mul_of_noDoubleCross (σ := B) (ρ := A) H).trans (Nat.add_comm _ _))

/-! ## The two Artin relations, at the permutation and germ levels -/

/-- Far-apart adjacent transpositions have disjoint support. -/
theorem adjT_disjoint (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) :
    Equiv.Perm.Disjoint (adjT i) (adjT j) := fun x => by
  by_cases hx : x.1 = i.1 ∨ x.1 = i.1 + 1
  · exact Or.inr (adjT_of_ne j (by omega) (by omega))
  · rw [not_or] at hx
    exact Or.inl (adjT_of_ne i hx.1 hx.2)

/-- Commutation of far-apart adjacent transpositions. -/
theorem adjT_comm (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) : adjT i * adjT j = adjT j * adjT i :=
  (adjT_disjoint i j h).commute

/-- The braid relation among consecutive adjacent transpositions.  Both sides are the reversal
`swap (adjLo i) (adjHi j)`, via the swap-conjugation identity. -/
theorem adjT_braid (i j : Fin (n - 1)) (h : j.1 = i.1 + 1) :
    adjT i * adjT j * adjT i = adjT j * adjT i * adjT j := by
  have hmid : adjLo j = adjHi i := Fin.ext (by rw [adjLo_val, adjHi_val, h])
  have hne1 : adjHi j ≠ adjHi i := Fin.ne_of_val_ne (by rw [adjHi_val, adjHi_val]; omega)
  have hne2 : adjHi j ≠ adjLo i := Fin.ne_of_val_ne (by rw [adjHi_val, adjLo_val]; omega)
  have hne3 : adjLo i ≠ adjHi i := Fin.ne_of_val_ne (by rw [adjLo_val, adjHi_val]; omega)
  have hL : adjT i * adjT j * adjT i = swap (adjLo i) (adjHi j) := by
    unfold adjT
    rw [hmid, swap_comm (adjLo i) (adjHi i), swap_comm (adjHi i) (adjHi j),
      swap_mul_swap_mul_swap hne1 hne2]
  have hR : adjT j * adjT i * adjT j = swap (adjLo i) (adjHi j) := by
    unfold adjT
    rw [hmid, swap_mul_swap_mul_swap hne3 hne2.symm, swap_comm (adjHi j) (adjLo i)]
  rw [hL, hR]

/-- **Commutation holds in the germ.** -/
theorem ofPerm_adjT_comm (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) :
    ofPerm (adjT i) * ofPerm (adjT j) = ofPerm (adjT j) * ofPerm (adjT i) := by
  rw [ofPerm_mul_of_noDoubleCross (A := adjT i) (B := adjT j) ?hA,
      ofPerm_mul_of_noDoubleCross (A := adjT j) (B := adjT i) ?hB, adjT_comm i j h]
  case hA =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts j hpq hB
    simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega
  case hB =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts i hpq hB
    simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega

/-- **The braid relation holds in the germ.** -/
theorem ofPerm_adjT_braid (i j : Fin (n - 1)) (h : j.1 = i.1 + 1) :
    ofPerm (adjT i) * ofPerm (adjT j) * ofPerm (adjT i)
      = ofPerm (adjT j) * ofPerm (adjT i) * ofPerm (adjT j) := by
  rw [ofPerm_mul_of_noDoubleCross (A := adjT i) (B := adjT j) ?hA,
      ofPerm_mul_of_noDoubleCross (A := adjT i * adjT j) (B := adjT i) ?hB,
      ofPerm_mul_of_noDoubleCross (A := adjT j) (B := adjT i) ?hC,
      ofPerm_mul_of_noDoubleCross (A := adjT j * adjT i) (B := adjT j) ?hD,
      adjT_braid i j h]
  case hA =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts j hpq hB
    simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega
  case hB =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts i hpq hB
    simp only [Fin.lt_def, Perm.mul_apply, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega
  case hC =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts i hpq hB
    simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega
  case hD =>
    intro p q hpq hB
    obtain ⟨rfl, rfl⟩ := adjT_inverts j hpq hB
    simp only [Fin.lt_def, Perm.mul_apply, adjT_val, adjLo_val, adjHi_val] at hpq ⊢
    split_ifs <;> omega

/-! ## The Artin presentation and the comparison homomorphism -/

/-- The Artin relations on adjacent transpositions: commutation (far apart) and the braid
relation (consecutive). -/
def artinRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | (∃ i j : Fin (n - 1), i.1 + 1 < j.1 ∧
          r = FreeGroup.of i * FreeGroup.of j * (FreeGroup.of j * FreeGroup.of i)⁻¹) ∨
       (∃ i j : Fin (n - 1), j.1 = i.1 + 1 ∧
          r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
                (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)}

/-- **The Artin braid group** on `n` strands. -/
abbrev ArtinBraid (n : ℕ) : Type := PresentedGroup (artinRels n)

/-- The `i`-th Artin generator. -/
def artinGen (i : Fin (n - 1)) : ArtinBraid n := PresentedGroup.of i

/-- **The easy direction**: the Artin group maps to the germ, sending each generator to its simple
braid.  The Artin relations hold in the germ because they are length-additive. -/
def garsideOfArtin (n : ℕ) : ArtinBraid n →* GarsideBraid n :=
  PresentedGroup.toGroup (f := fun i => ofPerm (adjT i)) (by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [ofPerm_adjT_comm i j hij, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [ofPerm_adjT_braid i j hij, mul_inv_cancel])

@[simp] theorem garsideOfArtin_gen (i : Fin (n - 1)) :
    garsideOfArtin n (artinGen i) = ofPerm (adjT i) :=
  PresentedGroup.toGroup.of _

/-- **Matsumoto's theorem for `Sₙ`**, as an explicit hypothesis: the positive lift `σ ↦ σ̂` is a
well-defined section of `garsideOfArtin`, multiplicative on length-additive products and sending
adjacent transpositions to the Artin generators.  This is precisely the content Mathlib is missing
(`Coxeter/Basic` lists Matsumoto as a TODO). -/
def Matsumoto (n : ℕ) : Prop :=
  ∃ f : Perm (Fin n) → ArtinBraid n,
    (∀ σ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ → f (σ * τ) = f σ * f τ) ∧
    (∀ i : Fin (n - 1), f (adjT i) = artinGen i) ∧
    (∀ σ : Perm (Fin n), garsideOfArtin n (f σ) = ofPerm σ)

/-- The lift `GarsideBraid → ArtinBraid` supplied by Matsumoto's theorem. -/
noncomputable def garsideToArtin (n : ℕ) (pf : Matsumoto n) : GarsideBraid n →* ArtinBraid n :=
  PresentedGroup.toGroup (f := pf.choose) (by
    rintro r ⟨σ, τ, hlen, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [pf.choose_spec.1 σ τ hlen, mul_inv_cancel])

/-- **The isomorphism.**  Given Matsumoto's theorem for `Sₙ`, the Garside germ presentation is the
Artin braid group. -/
noncomputable def garside_equiv_artin (pf : Matsumoto n) : GarsideBraid n ≃* ArtinBraid n where
  toFun := garsideToArtin n pf
  invFun := garsideOfArtin n
  map_mul' := (garsideToArtin n pf).map_mul'
  left_inv := by
    have h : (garsideOfArtin n).comp (garsideToArtin n pf) = MonoidHom.id (GarsideBraid n) := by
      apply PresentedGroup.ext
      intro σ
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [show garsideToArtin n pf (PresentedGroup.of σ) = pf.choose σ from
        PresentedGroup.toGroup.of _]
      exact pf.choose_spec.2.2 σ
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (garsideToArtin n pf).comp (garsideOfArtin n) = MonoidHom.id (ArtinBraid n) := by
      apply PresentedGroup.ext
      intro i
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [show garsideOfArtin n (PresentedGroup.of i) = ofPerm (adjT i) from
        PresentedGroup.toGroup.of _,
        show ofPerm (adjT i) = PresentedGroup.of (adjT i) from rfl,
        show garsideToArtin n pf (PresentedGroup.of (adjT i)) = pf.choose (adjT i) from
        PresentedGroup.toGroup.of _]
      exact pf.choose_spec.2.1 i
    exact DFunLike.congr_fun h

end CubeChains
