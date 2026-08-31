import CubeChains.Machinery.Braid.Generated
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Ring.Int.Defs

/-!
# Machinery/Braid/PosGerm — the positive braid monoid, and the atom relations

`PosBraid n` is the germ presentation of `Machinery/Braid/Germ` read as a **monoid**: the same
generators and the same length-additive relations, with no inverses.

`germ_of_atom` cuts those relations down to the ones whose right factor is an adjacent
transposition.  That is the only shape geometry produces — a length-additive pair need not be
parabolic (at `n = 3`, `s₁s₂` against `s₂` is length-additive but lies in no proper Young
subgroup) — so the reduction is what lets a cocycle of shuffles name a positive braid.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-! ### The atom relations generate

Peeling one adjacent descent off the right factor keeps both halves length-additive, so the
induction never leaves the germ. -/

/-- **Every length-additive product is a consequence of the atom relations.** -/
theorem germ_of_atom {M : Type*} [Monoid M] {g : Perm (Fin n) → M} (hone : g 1 = 1)
    (hatom : ∀ (β : Perm (Fin n)) (i : Fin (n - 1)),
      permLen (β * adjT i) = permLen β + 1 → g β * g (adjT i) = g (β * adjT i))
    (σ : Perm (Fin n)) :
    ∀ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ → g σ * g τ = g (σ * τ) := by
  intro τ
  induction τ using permLen_strongRec with
  | _ τ ih =>
    intro h
    rcases Nat.eq_zero_or_pos (permLen τ) with h0 | hpos
    · rw [eq_one_of_permLen_eq_zero τ h0, hone, mul_one, mul_one]
    obtain ⟨i, hdesc⟩ := exists_adjacent_descent τ hpos
    have hlen : permLen τ = permLen (τ * adjT i) + 1 := permLen_mul_adjT_of_descent hdesc
    have hback : τ * adjT i * adjT i = τ := mul_adjT_adjT τ i
    -- the descent, peeled off the right factor
    have hgτ : g (τ * adjT i) * g (adjT i) = g τ := by
      have hβ := hatom (τ * adjT i) i (by rw [hback]; omega)
      rwa [hback] at hβ
    -- the same product, regrouped
    have hsplit : σ * (τ * adjT i) * adjT i = σ * τ := by
      rw [mul_assoc, hback]
    -- both halves stay length-additive
    have hmul : permLen (σ * (τ * adjT i)) = permLen σ + permLen (τ * adjT i) := by
      have hle := permLen_mul_le σ (τ * adjT i)
      have hge := permLen_mul_le (σ * (τ * adjT i)) (adjT i)
      rw [hsplit, permLen_adjT] at hge
      omega
    have hih := ih (τ * adjT i) (by omega) hmul
    have htop := hatom (σ * (τ * adjT i)) i (by rw [hsplit]; omega)
    rw [hsplit] at htop
    rw [← hgτ, ← mul_assoc, hih, htop]

/-! ### The monoid -/

/-- The germ relations, as a monoid presentation.  `one` must be imposed: without it every
generator may go to a single idempotent, which satisfies every `germ` relation. -/
inductive PosGermRel (n : ℕ) : FreeMonoid (Perm (Fin n)) → FreeMonoid (Perm (Fin n)) → Prop
  | germ (σ τ : Perm (Fin n)) (h : permLen (σ * τ) = permLen σ + permLen τ) :
      PosGermRel n (FreeMonoid.of σ * FreeMonoid.of τ) (FreeMonoid.of (σ * τ))
  | one : PosGermRel n (FreeMonoid.of 1) 1

/-- **The positive braid monoid on `n` strands.** -/
def PosBraid (n : ℕ) : Type := PresentedMonoid (PosGermRel n)

instance : Monoid (PosBraid n) := inferInstanceAs (Monoid (PresentedMonoid (PosGermRel n)))

/-- The simple positive braid of a permutation — a generator. -/
def posPerm (σ : Perm (Fin n)) : PosBraid n := PresentedMonoid.of _ σ

/-- **The germ relation**, in `PosBraid n`. -/
theorem posPerm_mul {σ τ : Perm (Fin n)} (h : permLen (σ * τ) = permLen σ + permLen τ) :
    posPerm σ * posPerm τ = posPerm (σ * τ) :=
  PresentedMonoid.mk_eq_mk_of_rel (PosGermRel.germ σ τ h)

@[simp] theorem posPerm_one : posPerm (1 : Perm (Fin n)) = 1 :=
  PresentedMonoid.mk_eq_mk_of_rel PosGermRel.one

/-- Appending a simple swap across an ascent is length-additive in the positive monoid. -/
theorem posPerm_mul_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    posPerm A * posPerm (adjT k) = posPerm (A * adjT k) :=
  posPerm_mul (permLen_mul_adjT_add h)

/-- **The simples of the adjacent transpositions are an Artin family in the positive germ.** -/
theorem isArtinFamily_posPerm_adjT :
    IsArtinFamily fun i : Fin (n - 1) => posPerm (adjT i) :=
  isArtinFamily_of_atom fun _ _ ha => posPerm_mul_adjT ha

theorem posPerm_surjective_closure :
    Submonoid.closure (Set.range (posPerm : Perm (Fin n) → PosBraid n)) = ⊤ :=
  PresentedMonoid.closure_range_of _

/-- **Induction on positive braids**: the simples generate, so a property holding at `1` and stable
under right multiplication by a simple holds everywhere. -/
@[elab_as_elim]
theorem PosBraid.induction {motive : PosBraid n → Prop} (b : PosBraid n) (one : motive 1)
    (mul : ∀ (a : PosBraid n) (σ : Perm (Fin n)), motive a → motive (a * posPerm σ)) :
    motive b :=
  Submonoid.induction_of_closure_eq_top_right posPerm_surjective_closure b one
    (by rintro a _ ⟨σ, rfl⟩ ha; exact mul a σ ha)

/-- **The universal property**: a map on simples that is unital and multiplicative at every
length-additive product extends to `PosBraid n`. -/
def PosBraid.lift {M : Type*} [Monoid M] (g : Perm (Fin n) → M) (hone : g 1 = 1)
    (hmul : ∀ σ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ →
      g σ * g τ = g (σ * τ)) : PosBraid n →* M :=
  PresentedMonoid.lift g (by
    rintro x y (⟨σ, τ, h⟩ | _)
    · simpa using hmul σ τ h
    · simpa using hone)

@[simp] theorem PosBraid.lift_posPerm {M : Type*} [Monoid M] {g : Perm (Fin n) → M} {hone} {hmul}
    (σ : Perm (Fin n)) : PosBraid.lift g hone hmul (posPerm σ) = g σ := rfl

/-- **The universal property from the atom relations alone** — `germ_of_atom` packaged. -/
def PosBraid.liftAtom {M : Type*} [Monoid M] (g : Perm (Fin n) → M) (hone : g 1 = 1)
    (hatom : ∀ (β : Perm (Fin n)) (i : Fin (n - 1)),
      permLen (β * adjT i) = permLen β + 1 → g β * g (adjT i) = g (β * adjT i)) :
    PosBraid n →* M :=
  PosBraid.lift g hone fun σ => germ_of_atom hone hatom σ

@[simp] theorem PosBraid.liftAtom_posPerm {M : Type*} [Monoid M] {g : Perm (Fin n) → M} {hone}
    {hatom} (σ : Perm (Fin n)) : PosBraid.liftAtom g hone hatom (posPerm σ) = g σ := rfl

theorem posPerm_ext {M : Type*} [Monoid M] {φ ψ : PosBraid n →* M}
    (h : ∀ σ : Perm (Fin n), φ (posPerm σ) = ψ (posPerm σ)) : φ = ψ :=
  PresentedMonoid.ext _ h

/-! ### The underlying permutation -/

/-- The underlying permutation of a positive braid — `Machinery/Braid/Germ`'s `permHom`, on the
monoid. -/ def posPermHom (n : ℕ) : PosBraid n →* Perm (Fin n) :=
  PosBraid.lift id rfl fun _ _ _ => rfl

@[simp] theorem posPermHom_posPerm (σ : Perm (Fin n)) : posPermHom n (posPerm σ) = σ := rfl

/-- **The positive pure braids**: the positive braids whose permutation is trivial. -/
def PosPureBraid (n : ℕ) : Submonoid (PosBraid n) := MonoidHom.mker (posPermHom n)

theorem mem_posPureBraid {β : PosBraid n} : β ∈ PosPureBraid n ↔ posPermHom n β = 1 :=
  MonoidHom.mem_mker

/-! ### The length

The germ relation *is* additivity of `permLen`, so the Coxeter length extends to the monoid with
nothing to check.  Being additive and vanishing only at `1`, it is an atomicity function in
Garside's sense. -/

/-- **The length of a positive braid**: the crossings it makes. -/
def posLen (n : ℕ) : PosBraid n →* Multiplicative ℕ :=
  PosBraid.lift (fun σ => Multiplicative.ofAdd (permLen σ)) (by simp)
    fun _ _ h => by simp only [h, ofAdd_add]

@[simp] theorem posLen_posPerm (σ : Perm (Fin n)) :
    posLen n (posPerm σ) = Multiplicative.ofAdd (permLen σ) := rfl

/-- **The Coxeter length never exceeds the crossing count** — `permLen` is subadditive, so a
factorisation can only lose inversions. -/
theorem permLen_posPermHom_le (b : PosBraid n) :
    permLen (posPermHom n b) ≤ Multiplicative.toAdd (posLen n b) := by
  induction b using PosBraid.induction with
  | one => simp
  | mul a σ ha =>
      rw [map_mul, map_mul, toAdd_mul, posPermHom_posPerm, posLen_posPerm, toAdd_ofAdd]
      exact le_trans (permLen_mul_le _ _) (by omega)

/-- **A positive braid that loses no inversion is a simple** — the reduced case of the germ
relation, read all the way down a factorisation. -/
theorem eq_posPerm_of_posLen {b : PosBraid n}
    (h : Multiplicative.toAdd (posLen n b) = permLen (posPermHom n b)) :
    b = posPerm (posPermHom n b) := by
  induction b using PosBraid.induction with
  | one => rw [map_one, posPerm_one]
  | mul a σ ha =>
      rw [map_mul, toAdd_mul, posLen_posPerm, toAdd_ofAdd, map_mul, posPermHom_posPerm] at h
      have hsub := permLen_mul_le (posPermHom n a) σ
      have hle := permLen_posPermHom_le a
      have hred : Multiplicative.toAdd (posLen n a) = permLen (posPermHom n a) := by omega
      have hadd : permLen (posPermHom n a * σ) = permLen (posPermHom n a) + permLen σ := by omega
      rw [map_mul, posPermHom_posPerm, ← posPerm_mul hadd, ← ha hred]

/-- **The length detects the identity.** -/
theorem eq_one_of_posLen_eq_zero {b : PosBraid n}
    (h : Multiplicative.toAdd (posLen n b) = 0) : b = 1 := by
  revert h
  induction b using PosBraid.induction with
  | one => exact fun _ => rfl
  | mul a σ ha =>
    intro h
    rw [map_mul, toAdd_mul, posLen_posPerm, toAdd_ofAdd] at h
    rw [ha (by omega), eq_one_of_permLen_eq_zero σ (by omega), posPerm_one, one_mul]

theorem posLen_eq_zero_iff {b : PosBraid n} :
    Multiplicative.toAdd (posLen n b) = 0 ↔ b = 1 :=
  ⟨eq_one_of_posLen_eq_zero, fun h => by rw [h, map_one]; rfl⟩

/-- **A proper right factor shortens** — the Noetherian half of Garside's axioms. -/
theorem posLen_lt_of_mul {a b : PosBraid n} (hb : b ≠ 1) :
    Multiplicative.toAdd (posLen n a) < Multiplicative.toAdd (posLen n (a * b)) := by
  have hadd : Multiplicative.toAdd (posLen n (a * b))
      = Multiplicative.toAdd (posLen n a) + Multiplicative.toAdd (posLen n b) := by
    rw [map_mul, toAdd_mul]
  have hb' : Multiplicative.toAdd (posLen n b) ≠ 0 := fun h0 => hb (posLen_eq_zero_iff.mp h0)
  omega

/-- **`PosBraid n` has no non-trivial units**: lengths add, and only `1` has length zero. -/
theorem eq_one_of_mul_eq_one {a b : PosBraid n} (h : a * b = 1) : a = 1 := by
  have hsum := congrArg (fun c => Multiplicative.toAdd (posLen n c)) h
  simp only [map_mul, toAdd_mul, map_one, toAdd_one] at hsum
  exact eq_one_of_posLen_eq_zero (by omega)

/-! ### Comparison with the group -/

/-- **The positive braids, inside `Braid n`.**  Injectivity is Garside's theorem and is not proved
here. -/
def posToBraid (n : ℕ) : PosBraid n →* Braid n :=
  PosBraid.lift ofPerm ofPerm_one fun _ _ h => ofPerm_mul h

@[simp] theorem posToBraid_posPerm (σ : Perm (Fin n)) :
    posToBraid n (posPerm σ) = ofPerm σ := rfl

/-- The germ presentation's two forgetful maps agree: reading the permutation through `Braid n`
is reading it directly. -/
theorem permHom_comp_posToBraid (n : ℕ) : (permHom n).comp (posToBraid n) = posPermHom n :=
  posPerm_ext fun _ => rfl

theorem posToBraid_mem_pureBraid {β : PosBraid n} (h : β ∈ PosPureBraid n) :
    posToBraid n β ∈ PureBraid n := by
  have := congrArg (fun φ => (φ : PosBraid n →* Perm (Fin n)) β) (permHom_comp_posToBraid n)
  simpa [mem_posPureBraid.mp h] using this

/-- The comparison `PosPureBraid n → PureBraid n`. -/
def posPureToPure (n : ℕ) : PosPureBraid n →* PureBraid n where
  toFun β := ⟨posToBraid n β.1, posToBraid_mem_pureBraid β.2⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- **The comparison is injective exactly as far as Garside's theorem reaches**: `posToBraid`
injective is the only input, and there is no weaker one — the two monoids differ only by it. -/
theorem posPureToPure_injective (hg : Function.Injective (posToBraid n)) :
    Function.Injective (posPureToPure n) := fun _ _ h =>
  Subtype.ext (hg (congrArg Subtype.val h))

/-! ### The writhe

The writhe of a positive braid is `posLen` cast to `ℤ`, so it never goes negative — which is what
`posToBraid` misses. -/

/-- The writhe of a positive braid: its crossing count, read in the group. -/
def posWrithe (n : ℕ) : PosBraid n →* Multiplicative ℤ := (writheHom n).comp (posToBraid n)

theorem posWrithe_apply (b : PosBraid n) : posWrithe n b = writheHom n (posToBraid n b) := rfl

@[simp] theorem posWrithe_posPerm (σ : Perm (Fin n)) :
    posWrithe n (posPerm σ) = Multiplicative.ofAdd ((permLen σ : ℤ)) := writheHom_ofPerm σ

/-- **The writhe is the length**, cast to `ℤ`. -/
theorem posWrithe_comp (n : ℕ) :
    posWrithe n = (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ)).comp (posLen n) :=
  posPerm_ext fun σ => by rw [posWrithe_posPerm]; rfl

theorem toAdd_posWrithe (b : PosBraid n) :
    Multiplicative.toAdd (posWrithe n b) = ((Multiplicative.toAdd (posLen n b) : ℕ) : ℤ) :=
  congrArg Multiplicative.toAdd (DFunLike.congr_fun (posWrithe_comp n) b)

/-- **A positive braid has non-negative writhe.** -/
theorem writhe_nonneg (b : PosBraid n) : 0 ≤ Multiplicative.toAdd (posWrithe n b) := by
  rw [toAdd_posWrithe]
  exact Int.natCast_nonneg _

/-- **`posToBraid` is not surjective once there are two strands**: the inverse of a generator has
writhe `-1`, and nothing positive does. -/
theorem not_surjective_posToBraid (i : Fin (n - 1)) :
    ¬ Function.Surjective (posToBraid n) := by
  intro hsurj
  obtain ⟨b, hb⟩ := hsurj (ofPerm (adjT i))⁻¹
  have hw := writhe_nonneg b
  rw [posWrithe_apply, hb, map_inv, writheHom_ofPerm, permLen_adjT] at hw
  exact absurd hw (by decide)

end CubeChains
