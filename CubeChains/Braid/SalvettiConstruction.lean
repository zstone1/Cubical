import CubeChains.Arrangements.Braid
import CubeChains.Arrangements.BraidPreorder
import CubeChains.Arrangements.Sal
import CubeChains.Braid.Germ
import Mathlib.Data.Fintype.Inv
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Braid/SalvettiConstruction — the computable braid-word map read off the Salvetti complex

A tope `T` of `braidCOM n` assigns each ordered pair `{i<j}` the sign of `σᵢ − σⱼ`, so it *is* a
linear order on `Fin n`.  `topeRank` reads that order off the sign vector by counting predecessors,
`topePerm` packages it as a permutation, and `crossPerm a b` is the order change of a Salvetti edge
— all computable, no `evPerm'`, no `FreeGroupoid.lift`.
-/

open SignType

namespace CubeChains

variable {n : ℕ}

/-- `i` precedes `j` in the order of tope `T`: read the sign of the `{i,j}` entry directly. -/
def topeBefore (T : SignVec (BraidGround n)) (i j : Fin n) : Bool :=
  if h : i < j then decide (T ⟨(i, j), h⟩ = -1)
  else if h : j < i then decide (T ⟨(j, i), h⟩ = 1) else false

/-- No coordinate precedes itself. -/
@[simp] theorem topeBefore_self (T : SignVec (BraidGround n)) (i : Fin n) :
    topeBefore T i i = false := by
  simp only [topeBefore, lt_irrefl, dif_neg, not_false_iff]

/-- The predecessor set of `i` never contains `i`, so its cardinality is `< n`. -/
theorem topeRank_lt (T : SignVec (BraidGround n)) (i : Fin n) :
    (Finset.univ.filter (fun j => topeBefore T j i = true)).card < n := by
  have hi : i ∉ Finset.univ.filter (fun j => topeBefore T j i = true) := by
    simp [topeBefore_self]
  calc (Finset.univ.filter (fun j => topeBefore T j i = true)).card
      ≤ (Finset.univ.erase i).card :=
        Finset.card_le_card (fun j hj => Finset.mem_erase.mpr
          ⟨fun h => hi (h ▸ hj), Finset.mem_univ j⟩)
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    _ < n := Nat.sub_lt (Fin.pos i) one_pos

/-- The **rank** of `i` in the order of tope `T`: its number of predecessors, as `Fin n`. -/
def topeRank (T : SignVec (BraidGround n)) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter (fun j => topeBefore T j i = true)).card, topeRank_lt T i⟩

/-- **`topeBefore` reads the height order.**  On a tope `braidSign σ`, `i` precedes `j` exactly when
`σ i < σ j` — both branches of the sign lookup reduce to it. -/
theorem topeBefore_braidSign {σ : Fin n → ℤ} (i j : Fin n) :
    topeBefore (braidSign σ) i j = decide (σ i < σ j) := by
  unfold topeBefore
  split_ifs with h1 h2
  · rw [braidSign_apply, decide_eq_decide, sign_eq_neg_one_iff, sub_neg]
  · rw [braidSign_apply, decide_eq_decide, sign_eq_one_iff, sub_pos]
  · have : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    subst this
    simp

/-- The rank counts the `σ`-predecessors, once the tope is realised as `braidSign σ`. -/
theorem topeRank_eq_card {a : Sal (braidCOM n)} {σ : Fin n → ℤ} (hT : a.tope = braidSign σ)
    (i : Fin n) :
    (topeRank a.tope i : ℕ) = (Finset.univ.filter (fun j => σ j < σ i)).card := by
  simp only [topeRank]
  refine congrArg Finset.card (Finset.filter_congr (fun j _ => ?_))
  rw [hT, topeBefore_braidSign]
  simp

/-- **The rank is injective on a tope.**  Realising the tope as `braidSign σ` (`σ` injective), the
rank is the number of `σ`-predecessors, which strictly increases with the `σ`-value. -/
theorem topeRank_injective (a : Sal (braidCOM n)) : Function.Injective (topeRank a.tope) := by
  obtain ⟨σ, hσ, hT⟩ := (braidCOM_isTope_iff_injective a.tope).mp a.2.2.1
  intro i k hik
  have hcard : (Finset.univ.filter (fun j => σ j < σ i)).card
             = (Finset.univ.filter (fun j => σ j < σ k)).card := by
    have h := congrArg Fin.val hik
    rw [topeRank_eq_card hT i, topeRank_eq_card hT k] at h
    exact h
  rcases lt_trichotomy (σ i) (σ k) with h | h | h
  · exfalso
    have hsub : Finset.univ.filter (fun j => σ j < σ i) ⊆ Finset.univ.filter (fun j => σ j < σ k) :=
      fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_trans (Finset.mem_filter.mp hj).2 h⟩
    have hss : Finset.univ.filter (fun j => σ j < σ i) ⊂ Finset.univ.filter (fun j => σ j < σ k) :=
      (Finset.ssubset_iff_of_subset hsub).mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩,
          fun hc => lt_irrefl (σ i) (Finset.mem_filter.mp hc).2⟩
    exact absurd hcard (ne_of_lt (Finset.card_lt_card hss))
  · exact hσ h
  · exfalso
    have hsub : Finset.univ.filter (fun j => σ j < σ k) ⊆ Finset.univ.filter (fun j => σ j < σ i) :=
      fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_trans (Finset.mem_filter.mp hj).2 h⟩
    have hss : Finset.univ.filter (fun j => σ j < σ k) ⊂ Finset.univ.filter (fun j => σ j < σ i) :=
      (Finset.ssubset_iff_of_subset hsub).mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩,
          fun hc => lt_irrefl (σ k) (Finset.mem_filter.mp hc).2⟩
    exact absurd hcard.symm (ne_of_lt (Finset.card_lt_card hss))

theorem topeRank_bijective (a : Sal (braidCOM n)) : Function.Bijective (topeRank a.tope) :=
  Finite.injective_iff_bijective.mp (topeRank_injective a)

/-- **The permutation of a Salvetti cell**: the linear order its tope encodes, read directly off
the sign vector.  Computable (`Fintype.bijInv` for the inverse). -/
def topePerm (a : Sal (braidCOM n)) : Equiv.Perm (Fin n) where
  toFun := topeRank a.tope
  invFun := Fintype.bijInv (topeRank_bijective a)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

/-- **The crossing permutation of a Salvetti edge** `a ⟶ b`: the reordering from `a`'s tope to
`b`'s. -/
def crossPerm (a b : Sal (braidCOM n)) : Equiv.Perm (Fin n) := topePerm b * (topePerm a)⁻¹

@[simp] theorem crossPerm_self (a : Sal (braidCOM n)) : crossPerm a a = 1 := mul_inv_cancel _

/-- The crossing cocycle telescopes: `a ⟶ c` is `b ⟶ c` after `a ⟶ b`. -/
theorem crossPerm_comp (a b c : Sal (braidCOM n)) :
    crossPerm a c = crossPerm b c * crossPerm a b := by
  simp only [crossPerm, mul_assoc, inv_mul_cancel_left]

@[simp] theorem topePerm_apply (a : Sal (braidCOM n)) (p : Fin n) :
    topePerm a p = topeRank a.tope p := rfl

open CategoryTheory

/-- **Shared builder.**  A length-additive permutation cocycle `p` on a category `C` lifts, via
`ofPerm`, to a braid-valued functor.  The germ engine `ofPerm_mul` / `permLen_mul_of_noDoubleCross`
(`Braid/Germ`) is the shared math — `braidGrading` is the graded (`Braids`) client, `salFunctor` the
fixed-`n` one. -/
def permBraidFunctor {C : Type*} [Category C] (n : ℕ)
    (p : ∀ {a b : C}, (a ⟶ b) → Equiv.Perm (Fin n))
    (hp1 : ∀ a : C, p (𝟙 a) = 1)
    (hpc : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c), p (f ≫ g) = p g * p f)
    (hlen : ∀ {a b c : C} (f : a ⟶ b) (g : b ⟶ c),
      permLen (p (f ≫ g)) = permLen (p f) + permLen (p g)) :
    C ⥤ SingleObj (Braid n) where
  obj _ := SingleObj.star (Braid n)
  map f := ofPerm (p f)
  map_id a := by
    change ofPerm (p (𝟙 a)) = (1 : Braid n)
    rw [hp1, ofPerm_one]
  map_comp {a b c} f g := by
    show ofPerm (p (f ≫ g)) = ofPerm (p g) * ofPerm (p f)
    rw [hpc f g]
    exact (ofPerm_mul (by rw [← hpc f g, hlen f g]; omega)).symm

end CubeChains
