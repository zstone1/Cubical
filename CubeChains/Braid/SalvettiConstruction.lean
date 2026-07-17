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

/-- Strict monotonicity of the `σ`-predecessor count. -/
theorem card_sigma_lt {σ : Fin n → ℤ} {p q : Fin n} (h : σ p < σ q) :
    (Finset.univ.filter (fun j => σ j < σ p)).card
      < (Finset.univ.filter (fun j => σ j < σ q)).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset
    (fun j hj => Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, lt_trans (Finset.mem_filter.mp hj).2 h⟩)).mpr
    ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩,
      fun hc => lt_irrefl (σ p) (Finset.mem_filter.mp hc).2⟩)

@[simp] theorem topePerm_apply (a : Sal (braidCOM n)) (p : Fin n) :
    topePerm a p = topeRank a.tope p := rfl

/-- **The tope permutation's order is the tope's order.**  `p` precedes `q` under `topePerm a`
exactly when `topeBefore a.tope p q`. -/
theorem topePerm_lt_iff (a : Sal (braidCOM n)) (p q : Fin n) :
    topePerm a p < topePerm a q ↔ topeBefore a.tope p q = true := by
  obtain ⟨σ, hσ, hT⟩ := (braidCOM_isTope_iff_injective a.tope).mp a.2.2.1
  rw [topePerm_apply, topePerm_apply, Fin.lt_def, topeRank_eq_card hT p,
    topeRank_eq_card hT q, hT, topeBefore_braidSign, decide_eq_true_eq]
  refine ⟨fun hcard => ?_, card_sigma_lt⟩
  rcases lt_trichotomy (σ p) (σ q) with h | h | h
  · exact h
  · exact absurd (h ▸ hcard) (lt_irrefl _)
  · exact absurd (card_sigma_lt h) (by omega)

/-! ## No-double-cross: the Salvetti order never un-crosses a pair -/

/-- `topeBefore T p q` at a `q < p` pair reads the entry as `+1`. -/
theorem topeBefore_of_gt {T : SignVec (BraidGround n)} {p q : Fin n} (h : q < p)
    (hb : topeBefore T p q = true) : T ⟨(q, p), h⟩ = 1 := by
  unfold topeBefore at hb
  rw [dif_neg (not_lt.mpr h.le), dif_pos h, decide_eq_true_eq] at hb
  exact hb

/-- `topeBefore T p q` at a `p < q` pair reads the entry as `-1`. -/
theorem topeBefore_of_lt {T : SignVec (BraidGround n)} {p q : Fin n} (h : p < q)
    (hb : topeBefore T p q = true) : T ⟨(p, q), h⟩ = -1 := by
  unfold topeBefore at hb
  rw [dif_pos h, decide_eq_true_eq] at hb
  exact hb

/-- `topeBefore` reads only the `{p,q}` entry, so topes agreeing there give the same order. -/
theorem topeBefore_congr {T T' : SignVec (BraidGround n)} {p q : Fin n}
    (hpq : ∀ h : p < q, T ⟨(p, q), h⟩ = T' ⟨(p, q), h⟩)
    (hqp : ∀ h : q < p, T ⟨(q, p), h⟩ = T' ⟨(q, p), h⟩) :
    topeBefore T p q = topeBefore T' p q := by
  unfold topeBefore
  split_ifs with h1 h2
  · rw [hpq h1]
  · rw [hqp h2]
  · rfl

/-- **The tope of a flipped pair is frozen once resolved.**  If `a.tope` and `b.tope` disagree at
`e`, the finer face `b.face` is nonzero there, so (`b.face ⊑ c.face`) `c.tope = b.tope` at `e` — the
pair cannot flip back going `b → c`. -/
theorem tope_eq_of_flip {a b c : Sal (braidCOM n)} (hab : a ≤ b) (hbc : b ≤ c)
    (e : BraidGround n) (hflip : a.tope e ≠ b.tope e) : c.tope e = b.tope e := by
  have hbe : b.tope e = if b.face e = 0 then a.tope e else b.face e := by rw [hab.2]; rfl
  have hbface : b.face e ≠ 0 := fun h0 => hflip (by rw [hbe, if_pos h0])
  have hbeq : b.tope e = b.face e := by rw [hbe, if_neg hbface]
  have hcface : c.face e = b.face e := by
    rcases hbc.1 e with h | h
    · exact absurd h hbface
    · exact h.symm
  have hce : c.tope e = if c.face e = 0 then b.tope e else c.face e := by rw [hbc.2]; rfl
  rw [hce, hcface, if_neg hbface, hbeq]

/-- **The no-double-cross condition** (`permLen_mul_of_noDoubleCross`'s hypothesis) for the crossing
cocycle: a pair flipped `a → b` stays flipped `b → c`. -/
theorem crossPerm_H {a b c : Sal (braidCOM n)} (hab : a ≤ b) (hbc : b ≤ c)
    (i j : Fin n) (hij : i < j) (hfl : crossPerm a b j < crossPerm a b i) :
    crossPerm b c (crossPerm a b j) < crossPerm b c (crossPerm a b i) := by
  obtain ⟨p, rfl⟩ := (topePerm a).surjective i
  obtain ⟨q, rfl⟩ := (topePerm a).surjective j
  have hb : ∀ x, crossPerm a b (topePerm a x) = topePerm b x := fun x => by
    have h : crossPerm a b * topePerm a = topePerm b := by
      simp only [crossPerm, mul_assoc, inv_mul_cancel, mul_one]
    rw [← Equiv.Perm.mul_apply, h]
  have hc : ∀ x, crossPerm b c (topePerm b x) = topePerm c x := fun x => by
    have h : crossPerm b c * topePerm b = topePerm c := by
      simp only [crossPerm, mul_assoc, inv_mul_cancel, mul_one]
    rw [← Equiv.Perm.mul_apply, h]
  rw [hb q, hb p] at hfl ⊢
  rw [hc q, hc p]
  rw [topePerm_lt_iff] at hij hfl ⊢
  have hbc_eq : topeBefore c.tope q p = topeBefore b.tope q p := by
    refine topeBefore_congr ?_ ?_
    · intro h
      refine tope_eq_of_flip hab hbc ⟨(q, p), h⟩ ?_
      rw [topeBefore_of_gt h hij, topeBefore_of_lt h hfl]; decide
    · intro h
      refine tope_eq_of_flip hab hbc ⟨(p, q), h⟩ ?_
      rw [topeBefore_of_lt h hij, topeBefore_of_gt h hfl]; decide
  rw [hbc_eq]; exact hfl

/-- **Length additivity of the crossing cocycle** — the germ relation, from the Salvetti order. -/
theorem crossPerm_noDoubleCross {a b c : Sal (braidCOM n)} (hab : a ≤ b) (hbc : b ≤ c) :
    permLen (crossPerm a c) = permLen (crossPerm a b) + permLen (crossPerm b c) := by
  rw [crossPerm_comp a b c]
  exact permLen_mul_of_noDoubleCross (fun i j hij hfl => crossPerm_H hab hbc i j hij hfl)

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

/-- **The Salvetti braid grading** — computable: a Salvetti edge `a ⟶ b` goes to the positive braid
of its crossing permutation `crossPerm a b`, read straight off the sign vectors. -/
def salvettiGrading (n : ℕ) : Sal (braidCOM n) ⥤ SingleObj (Braid n) :=
  permBraidFunctor n
    (p := fun {a b} (_ : a ⟶ b) => crossPerm a b)
    (hp1 := crossPerm_self)
    (hpc := fun {a b c} (_ : a ⟶ b) (_ : b ⟶ c) => crossPerm_comp a b c)
    (hlen := fun {a b c} f g => crossPerm_noDoubleCross (leOfHom f) (leOfHom g))

/-- **The Salvetti construction** on the concurrency braid groupoid of the braid arrangement: the
free-groupoid lift of `salvettiGrading`.  (Noncomputable only through mathlib's `FreeGroupoid.lift`,
exactly as `braidGrpd`; braid words are computed by `salvettiGrading`.) -/
def salvettiConstruction (n : ℕ) :
    FreeGroupoid (Sal (braidCOM n)) ⥤ SingleObj (Braid n) :=
  FreeGroupoid.lift (salvettiGrading n)

/-- **Salvetti's theorem** (asphericity of the braid arrangement), as an axiom: the Salvetti
construction is an injection — faithful, hence injective on every concurrency-braid vertex group. -/
axiom salvettiConstruction_faithful (n : ℕ) : (salvettiConstruction n).Faithful

end CubeChains
