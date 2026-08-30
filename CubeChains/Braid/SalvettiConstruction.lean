import CubeChains.Arrangements.BraidCovector
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
`topePerm` packages it as a permutation, and `topeCross a b` is the order change of a Salvetti edge
— all computable, no `FreeGroupoid.lift`.

`topeCross` is the *arrangement's* crossing permutation; `ChainCat.crossPerm` is the wedge map's,
read through the lexicographic flattening `pos`.  `Salvetti/CrossCompare` identifies them.
-/

open SignType

namespace CubeChains

variable {n : ℕ}

/-- The predecessor set of `i` never contains `i`, so its cardinality is `< n`. -/
theorem topeRank_lt (T : SignVec (BraidGround n)) (i : Fin n) :
    (Finset.univ.filter (fun j => covectorBelow T j i = true)).card < n := by
  have hi : i ∉ Finset.univ.filter (fun j => covectorBelow T j i = true) := by
    simp [covectorBelow_self]
  calc (Finset.univ.filter (fun j => covectorBelow T j i = true)).card
      ≤ (Finset.univ.erase i).card :=
        Finset.card_le_card (fun j hj => Finset.mem_erase.mpr
          ⟨fun h => hi (h ▸ hj), Finset.mem_univ j⟩)
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    _ < n := Nat.sub_lt (Fin.pos i) one_pos

/-- The **rank** of `i` in the order of tope `T`: `covectorHeight`, bounded into `Fin n` by the
tope's own strictness. -/
def topeRank (T : SignVec (BraidGround n)) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter (fun j => covectorBelow T j i = true)).card, topeRank_lt T i⟩

/-- The rank is the canonical height, read in `ℕ`. -/
theorem topeRank_val (T : SignVec (BraidGround n)) (i : Fin n) :
    ((topeRank T i : ℕ) : ℤ) = covectorHeight T i := rfl

/-- The rank counts the `σ`-predecessors, once the tope is realised as `braidSign σ`. -/
theorem topeRank_eq_card {a : Sal (braidCOM n)} {σ : Fin n → ℤ} (hT : a.tope = braidSign σ)
    (i : Fin n) :
    (topeRank a.tope i : ℕ) = (Finset.univ.filter (fun j => σ j < σ i)).card := by
  simp only [topeRank]
  refine congrArg Finset.card (Finset.filter_congr (fun j _ => ?_))
  rw [hT, covectorBelow_braidSign]
  simp

/-- **The rank is injective on a tope.**  Realising the tope as `braidSign σ` (`σ` injective), the
rank is the canonical height, which strictly increases with the `σ`-value. -/
theorem topeRank_injective (a : Sal (braidCOM n)) : Function.Injective (topeRank a.tope) := by
  obtain ⟨σ, hσ, hT⟩ := (braidCOM_isTope_iff_injective a.tope).mp a.2.2.1
  intro i k hik
  have hcard : covectorHeight (braidSign σ) i = covectorHeight (braidSign σ) k := by
    rw [← hT, ← topeRank_val, ← topeRank_val, hik]
  rcases lt_trichotomy (σ i) (σ k) with h | h | h
  · exact absurd hcard (ne_of_lt (covectorHeight_strictMono σ h))
  · exact hσ h
  · exact absurd hcard.symm (ne_of_lt (covectorHeight_strictMono σ h))

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
def topeCross (a b : Sal (braidCOM n)) : Equiv.Perm (Fin n) := topePerm b * (topePerm a)⁻¹

@[simp] theorem topeCross_self (a : Sal (braidCOM n)) : topeCross a a = 1 := mul_inv_cancel _

/-- The crossing cocycle telescopes: `a ⟶ c` is `b ⟶ c` after `a ⟶ b`. -/
theorem topeCross_comp (a b c : Sal (braidCOM n)) :
    topeCross a c = topeCross b c * topeCross a b := by
  simp only [topeCross, mul_assoc, inv_mul_cancel_left]

@[simp] theorem topePerm_apply (a : Sal (braidCOM n)) (p : Fin n) :
    topePerm a p = topeRank a.tope p := rfl

open CategoryTheory

/-- **Shared builder.**  A length-additive permutation cocycle `p` on a category `C` lifts, via
`ofPerm`, to a braid-valued functor; the germ relation `ofPerm_eq_mul` is the whole content. -/
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
  map_comp _ _ := ofPerm_eq_mul (hpc _ _) (hlen _ _)

end CubeChains
