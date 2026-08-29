import CubeChains.Braid.Germ
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Braid/Artin — the adjacent transpositions, and the Artin presentation

`GarsideBraid n` is `Braid n`, the germ presentation of `Braid/Germ`.  `ArtinBraid n` is the
classical Artin presentation on the adjacent transpositions `adjT k`, whose two relation families
`ArtinRel` present the braid *monoid* as well.

The Artin relations are length-additive facts, so they hold in **any** germ
(`isArtinFamily_of_atom`), which gives the easy `garsideOfArtin : ArtinBraid n →* GarsideBraid n`.
Upgrading it to an isomorphism is **Matsumoto's theorem for `Sₙ`**, in `Braid/Matsumoto`; mathlib
does not supply it (`Coxeter/Basic` lists Matsumoto as a TODO and has no type-A instance).
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

/-- Consecutive indices share an endpoint. -/
theorem adjLo_eq_adjHi {i j : Fin (n - 1)} (h : (j : ℕ) = (i : ℕ) + 1) : adjLo j = adjHi i :=
  Fin.ext (by rw [adjLo_val, adjHi_val, h])

/-- The `k`-th adjacent transposition, swapping `k` and `k+1`. -/
def adjT (k : Fin (n - 1)) : Perm (Fin n) := Equiv.swap (adjLo k) (adjHi k)

theorem adjT_lo (k : Fin (n - 1)) : adjT k (adjLo k) = adjHi k := swap_apply_left _ _
theorem adjT_hi (k : Fin (n - 1)) : adjT k (adjHi k) = adjLo k := swap_apply_right _ _

theorem adjT_of_ne (k : Fin (n - 1)) {x : Fin n} (h1 : x.1 ≠ k.1) (h2 : x.1 ≠ k.1 + 1) :
    adjT k x = x :=
  swap_apply_of_ne_of_ne (fun heq => h1 (congrArg Fin.val heq))
    (fun heq => h2 (congrArg Fin.val heq))

/-- `adjT_of_ne` at `adjLo l`, phrased on the index so `omega` can see the hypotheses. -/
theorem adjT_adjLo_of_ne {k l : Fin (n - 1)} (h1 : (l : ℕ) ≠ (k : ℕ))
    (h2 : (l : ℕ) ≠ (k : ℕ) + 1) : adjT k (adjLo l) = adjLo l :=
  adjT_of_ne k h1 h2

/-- …and at `adjHi l`. -/
theorem adjT_adjHi_of_ne {k l : Fin (n - 1)} (h1 : (l : ℕ) + 1 ≠ (k : ℕ))
    (h2 : (l : ℕ) + 1 ≠ (k : ℕ) + 1) : adjT k (adjHi l) = adjHi l :=
  adjT_of_ne k h1 h2

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
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [adjLo_val, adjHi_val] <;> grind

/-! ## The group the transpositions generate -/

theorem adjT_mul_self (k : Fin (n - 1)) : adjT k * adjT k = 1 := swap_mul_self _ _

theorem mul_adjT_adjT (σ : Perm (Fin n)) (k : Fin (n - 1)) : σ * adjT k * adjT k = σ := by
  rw [mul_assoc, adjT_mul_self, mul_one]

/-- Appending a simple swap swaps the two ranks it names. -/
theorem symm_mul_adjT (σ : Perm (Fin n)) (k : Fin (n - 1)) (p : Fin n) :
    (σ * adjT k).symm p = adjT k (σ.symm p) := by
  rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply,
    show adjT k (adjT k (σ.symm p)) = σ.symm p from Equiv.swap_apply_self _ _ _]
  exact (σ.apply_symm_apply p).symm

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
  have hmid : adjLo j = adjHi i := adjLo_eq_adjHi h
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

/-- Commutation, appended to an arbitrary permutation — the square at a commutation stratum. -/
theorem mul_adjT_comm (σ : Perm (Fin n)) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 < (j : ℕ)) :
    σ * adjT i * adjT j = σ * adjT j * adjT i := by
  simpa only [mul_assoc] using congrArg (σ * ·) (adjT_comm i j h)

/-- The braid relation, appended to an arbitrary permutation — the hexagon at a braid stratum. -/
theorem mul_adjT_braid (σ : Perm (Fin n)) {i j : Fin (n - 1)} (h : (j : ℕ) = (i : ℕ) + 1) :
    σ * adjT i * adjT j * adjT i = σ * adjT j * adjT i * adjT j := by
  simpa only [mul_assoc] using congrArg (σ * ·) (adjT_braid i j h)

/-! ## Length-additivity for adjacent transpositions -/

/-- An adjacent transposition crosses exactly one pair. -/
theorem permLen_adjT (k : Fin (n - 1)) : permLen (adjT k) = 1 := by
  rw [permLen, Finset.card_eq_one]
  refine ⟨(adjLo k, adjHi k), ?_⟩
  ext ⟨p, q⟩
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hpq, hinv⟩
    exact adjT_inverts k hpq hinv
  · rintro ⟨rfl, rfl⟩
    have hlt : adjLo k < adjHi k := by rw [Fin.lt_def, adjLo_val, adjHi_val]; omega
    exact ⟨hlt, by rw [adjT_hi, adjT_lo]; exact hlt⟩

/-- **Only the swapped pair can double-cross a simple swap** (`adjT_inverts`), so an ascent of `A`
there is the whole no-double-cross criterion for `A * adjT k`. -/
theorem noDoubleCross_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    ∀ i j : Fin n, i < j → adjT k j < adjT k i → A (adjT k j) < A (adjT k i) := by
  intro p q hpq hinv
  obtain ⟨rfl, rfl⟩ := adjT_inverts k hpq hinv
  rw [adjT_hi, adjT_lo]
  exact h

/-- Appending a simple swap across an ascent is length-additive in the germ. -/
theorem ofPerm_mul_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    ofPerm A * ofPerm (adjT k) = ofPerm (A * adjT k) :=
  ofPerm_mul_of_noDoubleCross (noDoubleCross_adjT h)

/-- Appending a simple swap across an ascent adds the one new crossing. -/
theorem permLen_mul_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    permLen (A * adjT k) = permLen A + 1 := by
  rw [permLen_mul_of_noDoubleCross (σ := adjT k) (ρ := A) (noDoubleCross_adjT h), permLen_adjT,
    Nat.add_comm]

/-- …read as a length-additive product, which is the shape a germ relation asks for. -/
theorem permLen_mul_adjT_add {A : Perm (Fin n)} {k : Fin (n - 1)}
    (h : A (adjLo k) < A (adjHi k)) :
    permLen (A * adjT k) = permLen A + permLen (adjT k) := by
  rw [permLen_mul_adjT h, permLen_adjT]

/-! ## The two Artin relations

The relations are a property of a *family* `g : Fin (n-1) → M`, and every germ has one. -/

/-- A family satisfying the two Artin relations: far-apart generators commute, consecutive ones
braid. -/
structure IsArtinFamily {M : Type*} [Monoid M] (g : Fin (n - 1) → M) : Prop where
  /-- Far-apart generators commute. -/
  comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ)) : g i * g j = g j * g i
  /-- Consecutive generators braid. -/
  braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
    g i * g j * g i = g j * g i * g j

/-- **Every germ carries an Artin family.**  Multiplicativity across an ascent is the only input;
the two sides are then the same permutation (`adjT_comm`, `adjT_braid`). -/
theorem isArtinFamily_of_atom {M : Type*} [Monoid M] {g : Perm (Fin n) → M}
    (hatom : ∀ (A : Perm (Fin n)) (k : Fin (n - 1)), A (adjLo k) < A (adjHi k) →
      g A * g (adjT k) = g (A * adjT k)) :
    IsArtinFamily fun i : Fin (n - 1) => g (adjT i) where
  comm i j h := by
    rw [hatom (adjT i) j ?_, hatom (adjT j) i ?_, adjT_comm i j h]
    all_goals simp only [Fin.lt_def, adjT_val, adjLo_val, adjHi_val]
    all_goals grind
  braid i j h := by
    rw [hatom (adjT i) j ?_, hatom (adjT i * adjT j) i ?_, hatom (adjT j) i ?_,
        hatom (adjT j * adjT i) j ?_, adjT_braid i j h]
    all_goals simp only [Fin.lt_def, Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
    all_goals grind

/-- **The simples of the adjacent transpositions are an Artin family.** -/
theorem isArtinFamily_ofPerm_adjT :
    IsArtinFamily fun i : Fin (n - 1) => ofPerm (adjT i) :=
  isArtinFamily_of_atom fun _ _ ha => ofPerm_mul_adjT ha

/-! ## The Artin presentations

One relation family, two presented objects: `ArtinBraid` here, and the monoid `ArtinPosBraid` in
`Braid/Matsumoto`. -/

/-- The two Artin relation families, as pairs of words on the `n-1` generators. -/
inductive ArtinRel (n : ℕ) : FreeMonoid (Fin (n - 1)) → FreeMonoid (Fin (n - 1)) → Prop
  | comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ)) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j) (FreeMonoid.of j * FreeMonoid.of i)
  | braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i)
        (FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j)

/-- **An Artin family satisfies the relations word by word** — the shape both universal properties
ask for. -/
theorem IsArtinFamily.lift_eq {M : Type*} [Monoid M] {g : Fin (n - 1) → M} (hg : IsArtinFamily g)
    {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    FreeMonoid.lift g x = FreeMonoid.lift g y := by
  cases h with
  | comm i j h => simpa only [map_mul, FreeMonoid.lift_eval_of] using hg.comm i j h
  | braid i j h => simpa only [map_mul, FreeMonoid.lift_eval_of] using hg.braid i j h

/-- A relation word, read in the free group. -/
def artinWord (n : ℕ) : FreeMonoid (Fin (n - 1)) →* FreeGroup (Fin (n - 1)) :=
  FreeMonoid.lift FreeGroup.of

/-- A group-valued hom reads an Artin word as the `FreeMonoid` lift of its values on generators. -/
theorem artinWord_lift {M : Type*} [Monoid M] {φ : FreeGroup (Fin (n - 1)) →* M}
    {f : Fin (n - 1) → M} (hf : ∀ i, φ (FreeGroup.of i) = f i) (z : FreeMonoid (Fin (n - 1))) :
    φ (artinWord n z) = FreeMonoid.lift f z :=
  DFunLike.congr_fun (FreeMonoid.hom_eq (f := φ.comp (artinWord n)) (g := FreeMonoid.lift f) hf) z

/-- The Artin relations, as free-group relators. -/
def artinRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ x y, ArtinRel n x y ∧ r = artinWord n x * (artinWord n y)⁻¹}

/-- **The Artin braid group** on `n` strands. -/
abbrev ArtinBraid (n : ℕ) : Type := PresentedGroup (artinRels n)

/-- The `i`-th Artin generator. -/
def artinGen (i : Fin (n - 1)) : ArtinBraid n := PresentedGroup.of i

/-- An Artin family kills every relator, so it extends to the group. -/
theorem IsArtinFamily.lift_artinRels {G : Type*} [Group G] {g : Fin (n - 1) → G}
    (hg : IsArtinFamily g) {r : FreeGroup (Fin (n - 1))} (hr : r ∈ artinRels n) :
    FreeGroup.lift g r = 1 := by
  obtain ⟨x, y, h, rfl⟩ := hr
  have key := artinWord_lift (φ := FreeGroup.lift g) fun _ => FreeGroup.lift_apply_of
  rw [map_mul, map_inv, key x, key y, hg.lift_eq h, mul_inv_cancel]

/-- **The universal property of the Artin braid group.** -/
def ArtinBraid.lift {G : Type*} [Group G] (g : Fin (n - 1) → G) (hg : IsArtinFamily g) :
    ArtinBraid n →* G :=
  PresentedGroup.toGroup (f := g) fun _ hr => hg.lift_artinRels hr

@[simp] theorem ArtinBraid.lift_gen {G : Type*} [Group G] {g : Fin (n - 1) → G}
    {hg : IsArtinFamily g} (i : Fin (n - 1)) : ArtinBraid.lift g hg (artinGen i) = g i :=
  PresentedGroup.toGroup.of _

/-- The relations hold between the generators themselves. -/
theorem artinGen_rel {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    FreeMonoid.lift artinGen x = FreeMonoid.lift artinGen y := by
  have key := artinWord_lift (φ := PresentedGroup.mk (artinRels n))
    (f := artinGen (n := n)) fun _ => rfl
  rw [← key x, ← key y]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨x, y, h, rfl⟩

/-- **The Artin generators are an Artin family** — the presentation imposes its own relations. -/
theorem isArtinFamily_artinGen : IsArtinFamily (artinGen (n := n)) where
  comm i j h := by
    simpa only [map_mul, FreeMonoid.lift_eval_of] using artinGen_rel (ArtinRel.comm i j h)
  braid i j h := by
    simpa only [map_mul, FreeMonoid.lift_eval_of] using artinGen_rel (ArtinRel.braid i j h)

/-- **The easy direction**: the Artin group maps to the germ, sending each generator to its simple
braid.  The Artin relations hold in the germ because they are length-additive. -/
def garsideOfArtin (n : ℕ) : ArtinBraid n →* GarsideBraid n :=
  ArtinBraid.lift _ isArtinFamily_ofPerm_adjT

@[simp] theorem garsideOfArtin_gen (i : Fin (n - 1)) :
    garsideOfArtin n (artinGen i) = ofPerm (adjT i) :=
  ArtinBraid.lift_gen i

end CubeChains
