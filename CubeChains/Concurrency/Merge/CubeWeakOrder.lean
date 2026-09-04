import CubeChains.Concurrency.Merge.CubeCrossing
import CubeChains.Concurrency.Presentation.LocPresentation
import Mathlib.Tactic.Group

/-!
# Concurrency/Merge/CubeWeakOrder — the localized cube slice is the weak order

`crossLen_eq_add` says a refinement drops the Coxeter length by exactly the length of its own
crossing permutation.  That *is* the right weak (Bruhat) order: `cross c = cross c' * crossPerm f`
with the lengths adding, so `cross c'` sits below `cross c`.  So `cross` is a functor to the weak
order read backwards, it inverts `W`, and it descends to the localization.

`WeakOrder n` is `Perm (Fin n)` under that order, as a type synonym — the order is not an instance
on `Perm` itself.  Transitivity and antisymmetry need only subadditivity of `permLen` and the fact
that only the identity has length zero.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace CubeChains

variable {n : ℕ}

/-! ## The right weak order on `Perm (Fin n)` -/

/-- `Perm (Fin n)` under the **right weak (Bruhat) order**: `x ≤ y` when `y` factors as `x`
followed by something, with the crossing counts adding. -/
def WeakOrder (n : ℕ) : Type := Equiv.Perm (Fin n)

namespace WeakOrder

/-- A permutation, read in the weak order. -/
def of (σ : Equiv.Perm (Fin n)) : WeakOrder n := σ

/-- An element of the weak order, read as a permutation. -/
def perm (x : WeakOrder n) : Equiv.Perm (Fin n) := x

@[simp] theorem perm_of (σ : Equiv.Perm (Fin n)) : perm (of σ) = σ := rfl

@[simp] theorem of_perm (x : WeakOrder n) : of (perm x) = x := rfl

theorem of_injective : Function.Injective (of (n := n)) := fun _ _ h => h

instance : PartialOrder (WeakOrder n) where
  le x y := permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y)
  le_refl x := by simp
  le_trans x y z hxy hyz := by
    have hsplit : (perm x)⁻¹ * perm z = ((perm x)⁻¹ * perm y) * ((perm y)⁻¹ * perm z) := by
      group
    have hfac : perm z = perm x * ((perm x)⁻¹ * perm z) := by group
    have h₁ := permLen_mul_le ((perm x)⁻¹ * perm y) ((perm y)⁻¹ * perm z)
    have h₂ := permLen_mul_le (perm x) ((perm x)⁻¹ * perm z)
    rw [← hsplit] at h₁
    rw [← hfac] at h₂
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) at hxy
    change permLen (perm y) + permLen ((perm y)⁻¹ * perm z) = permLen (perm z) at hyz
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm z) = permLen (perm z)
    omega
  le_antisymm x y hxy hyx := by
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) at hxy
    change permLen (perm y) + permLen ((perm y)⁻¹ * perm x) = permLen (perm x) at hyx
    have hz : permLen ((perm x)⁻¹ * perm y) = 0 := by omega
    have := eq_one_of_permLen_eq_zero _ hz
    have hxy' : perm x = perm y := by
      rw [← mul_one (perm x), ← this, mul_inv_cancel_left]
    exact hxy'

theorem le_def {x y : WeakOrder n} :
    x ≤ y ↔ permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) := Iff.rfl

/-- Below in the weak order means no longer. -/
theorem permLen_le_of_le {x y : WeakOrder n} (h : x ≤ y) : permLen (perm x) ≤ permLen (perm y) := by
  rw [le_def] at h; omega

/-- The witnessing factorisation. -/
theorem le_of_mul {σ β : Equiv.Perm (Fin n)}
    (h : permLen σ + permLen β = permLen (σ * β)) : of σ ≤ of (σ * β) := by
  rw [le_def]
  simpa [inv_mul_cancel_left] using h

/-! ### Self-duality

The reversal is the top (`permLen_add_inv_mul_revPerm`), and `σ ↦ w₀σ` is an involution reversing
the order: `w₀` cancels out of the difference `x⁻¹y`, while each length is complemented.  This is
the **orientation bridge** — it is what turns a presentation of `Ch(□n)[W⁻¹]ᵒᵖ` into one of
`Ch(□n)[W⁻¹]`. -/

instance : OrderTop (WeakOrder n) where
  top := of Fin.revPerm
  le_top x := permLen_add_inv_mul_revPerm (perm x)

/-- The order-reversing involution `σ ↦ w₀σ`, `w₀` the reversal. -/
def rev (x : WeakOrder n) : WeakOrder n := of (Fin.revPerm * perm x)

@[simp] theorem perm_rev (x : WeakOrder n) : perm (rev x) = Fin.revPerm * perm x := rfl

@[simp] theorem rev_rev (x : WeakOrder n) : rev (rev x) = x := by
  change of (Fin.revPerm * (Fin.revPerm * perm x)) = x
  rw [← mul_assoc, revPerm_mul_self, one_mul, of_perm]

theorem rev_le_rev {x y : WeakOrder n} (h : x ≤ y) : rev y ≤ rev x := by
  have hcancel : (Fin.revPerm * perm y)⁻¹ * (Fin.revPerm * perm x) = (perm y)⁻¹ * perm x := by
    rw [mul_inv_rev, revPerm_inv, mul_assoc, ← mul_assoc (Fin.revPerm : Equiv.Perm (Fin n)),
      revPerm_mul_self, one_mul]
  have h3 : permLen ((perm y)⁻¹ * perm x) = permLen ((perm x)⁻¹ * perm y) := by
    rw [← permLen_inv ((perm x)⁻¹ * perm y), mul_inv_rev, inv_inv]
  have h1 := permLen_revPerm_mul_add (perm x)
  have h2 := permLen_revPerm_mul_add (perm y)
  rw [le_def] at h ⊢
  simp only [perm_rev, hcancel]
  omega

theorem rev_le_rev_iff {x y : WeakOrder n} : rev y ≤ rev x ↔ x ≤ y :=
  ⟨fun h => by simpa using rev_le_rev h, rev_le_rev⟩

/-- **The right weak order is self-dual**, by `σ ↦ w₀σ`. -/
def revOrderIso (n : ℕ) : WeakOrder n ≃o (WeakOrder n)ᵒᵈ where
  toFun x := OrderDual.toDual (rev x)
  invFun x := rev (OrderDual.ofDual x)
  left_inv := rev_rev
  right_inv := rev_rev
  map_rel_iff' := rev_le_rev_iff

/-- …read as an equivalence of categories, which is the form the presentations consume. -/
def revEquivalence (n : ℕ) : WeakOrder n ≌ (WeakOrder n)ᵒᵖ :=
  (revOrderIso n).equivalence.trans (orderDualEquivalence (WeakOrder n))

/-! ### Two lower covers, and what lies below both

Confluence needs one fact about the order and nothing more: anything below two lower covers of `σ`
is below the permutation that sorts their merged window.  That is a count of descents, not the
lattice structure of the weak order — the join of the two faces supplies the window, and the three
descent steps supply the length. -/

/-- A descent gives a lower cover. -/
theorem of_mul_adjT_le {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjHi i) < σ (adjLo i)) : of (σ * adjT i) ≤ of σ := by
  have hinv : (σ * adjT i)⁻¹ * σ = adjT i := by
    have hs : (adjT i)⁻¹ = adjT i := by rw [adjT, Equiv.swap_inv]
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, hs]
  rw [le_def]
  simp only [perm_of, hinv, permLen_adjT]
  exact (permLen_mul_adjT_of_descent h).symm

/-- The two endpoints of an adjacent swap are distinct. -/
theorem adjLo_ne_adjHi (i : Fin (n - 1)) : adjLo i ≠ adjHi i := by
  intro h
  have := congrArg Fin.val h
  simp only [adjLo_val, adjHi_val] at this
  omega

/-- Length dropping across an adjacent swap *is* a descent. -/
theorem descent_of_permLen_drop {w : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : permLen (w * adjT i) + 1 = permLen w) : w (adjHi i) < w (adjLo i) := by
  rcases lt_trichotomy (w (adjLo i)) (w (adjHi i)) with hlt | heq | hgt
  · have := permLen_mul_adjT hlt
    omega
  · exact absurd (w.injective heq) (adjLo_ne_adjHi i)
  · exact hgt

/-- Below a lower cover, the drop shows up in the residue `x⁻¹σ` as well. -/
theorem permLen_residue_drop {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {x : WeakOrder n}
    (hd : σ (adjHi i) < σ (adjLo i)) (hx : x ≤ of (σ * adjT i)) :
    permLen ((perm x)⁻¹ * σ * adjT i) + 1 = permLen ((perm x)⁻¹ * σ) := by
  have hxσ := hx.trans (of_mul_adjT_le hd)
  rw [le_def] at hx hxσ
  simp only [perm_of, ← mul_assoc] at hx hxσ
  have hstep := permLen_mul_adjT_of_descent hd
  omega
/-- An adjacent swap fixes everything outside its two endpoints. -/
theorem adjT_apply_of_ne {i : Fin (n - 1)} {a : Fin n}
    (h1 : (a : ℕ) ≠ (i : ℕ)) (h2 : (a : ℕ) ≠ (i : ℕ) + 1) : adjT i a = a := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;>
    · intro h
      have := congrArg Fin.val h
      simp only [adjLo_val, adjHi_val] at this
      omega

/-- Far-apart swaps leave each other's descents alone. -/
theorem descent_mul_adjT_far {u : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hij : (i : ℕ) + 1 < (j : ℕ)) (hj : u (adjHi j) < u (adjLo j)) :
    (u * adjT i) (adjHi j) < (u * adjT i) (adjLo j) := by
  have h1 : adjT i (adjLo j) = adjLo j :=
    adjT_apply_of_ne (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega)
  have h2 : adjT i (adjHi j) = adjHi j :=
    adjT_apply_of_ne (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, h2]
  exact hj

/-- Consecutive swaps share their middle point. -/
theorem adjLo_eq_adjHi {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1) : adjLo j = adjHi i := by
  apply Fin.ext
  simp only [adjLo_val, adjHi_val]
  omega

/-- Undoing the first of two consecutive descents leaves the second one a descent. -/
theorem descent_mul_adjT_braid₁ {u : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hi : u (adjHi i) < u (adjLo i)) (hj : u (adjHi j) < u (adjLo j)) :
    (u * adjT i) (adjHi j) < (u * adjT i) (adjLo j) := by
  have hm := adjLo_eq_adjHi hij
  have h1 : adjT i (adjLo j) = adjLo i := by rw [hm]; exact adjT_hi i
  have h2 : adjT i (adjHi j) = adjHi j :=
    adjT_apply_of_ne (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, h2]
  rw [hm] at hj
  exact hj.trans hi

/-- …and undoing that one leaves the first a descent again: three steps sort the window. -/
theorem descent_mul_adjT_braid₂ {u : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1) (hj : u (adjHi j) < u (adjLo j)) :
    (u * adjT i * adjT j) (adjHi i) < (u * adjT i * adjT j) (adjLo i) := by
  have hm := adjLo_eq_adjHi hij
  have h1 : adjT j (adjLo i) = adjLo i :=
    adjT_apply_of_ne (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega)
  have h2 : adjT j (adjHi i) = adjHi j := by rw [← hm]; exact adjT_lo j
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    h1, h2, adjT_lo i,
    adjT_apply_of_ne (i := i) (a := adjHi j) (by simp only [adjHi_val]; omega)
      (by simp only [adjHi_val]; omega)]
  rw [hm] at hj
  exact hj

/-- **Two far-apart lower covers**: whatever lies below both lies below the doubly sorted
permutation. -/
theorem le_mul_adjT_mul_adjT {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)} {x : WeakOrder n}
    (hij : (i : ℕ) + 1 < (j : ℕ))
    (hi : σ (adjHi i) < σ (adjLo i)) (hj : σ (adjHi j) < σ (adjLo j))
    (hxi : x ≤ of (σ * adjT i)) (hxj : x ≤ of (σ * adjT j)) :
    x ≤ of (σ * adjT i * adjT j) := by
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent (descent_mul_adjT_far hij hj)
  have h3 := permLen_residue_drop hi hxi
  have h4 := permLen_mul_adjT_of_descent
    (descent_mul_adjT_far hij (descent_of_permLen_drop (permLen_residue_drop hj hxj)))
  have hxσ : x ≤ of σ := hxi.trans (of_mul_adjT_le hi)
  rw [le_def] at hxσ ⊢
  simp only [perm_of, ← mul_assoc] at hxσ ⊢
  omega

/-- **Two consecutive lower covers**: whatever lies below both lies below the sorted
three-window. -/
theorem le_mul_adjT_braid {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)} {x : WeakOrder n}
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hi : σ (adjHi i) < σ (adjLo i)) (hj : σ (adjHi j) < σ (adjLo j))
    (hxi : x ≤ of (σ * adjT i)) (hxj : x ≤ of (σ * adjT j)) :
    x ≤ of (σ * adjT i * adjT j * adjT i) := by
  have hdwi := descent_of_permLen_drop (permLen_residue_drop hi hxi)
  have hdwj := descent_of_permLen_drop (permLen_residue_drop hj hxj)
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₁ hij hi hj)
  have h3 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₂ hij hj)
  have h4 := permLen_mul_adjT_of_descent hdwi
  have h5 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₁ hij hdwi hdwj)
  have h6 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₂ hij hdwj)
  have hxσ : x ≤ of σ := hxi.trans (of_mul_adjT_le hi)
  rw [le_def] at hxσ ⊢
  simp only [perm_of, ← mul_assoc] at hxσ ⊢
  omega

/-- **Below and not equal means below a lower cover.**  Peel an adjacent descent off the residue
`x⁻¹σ`; length-additivity survives it, so the cut it names is a descent of `σ` too. -/
theorem exists_cover_of_lt {σ : Equiv.Perm (Fin n)} {x : WeakOrder n}
    (hle : x ≤ of σ) (hne : perm x ≠ σ) :
    ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) ∧ x ≤ of (σ * adjT i) := by
  rw [le_def] at hle
  simp only [perm_of] at hle
  set β : Equiv.Perm (Fin n) := (perm x)⁻¹ * σ with hβ
  have hσβ : perm x * β = σ := by rw [hβ, mul_inv_cancel_left]
  have hβ1 : β ≠ 1 := fun hc => hne (by rw [← hσβ, hc, mul_one])
  have hpos : 0 < permLen β := Nat.pos_of_ne_zero fun hc => hβ1 (eq_one_of_permLen_eq_zero β hc)
  obtain ⟨i, hdi⟩ := exists_adjacent_descent β hpos
  have hstep := permLen_mul_adjT_of_descent hdi
  have hup : permLen (perm x * (β * adjT i)) ≤ permLen (perm x) + permLen (β * adjT i) :=
    permLen_mul_le _ _
  have hassoc : perm x * (β * adjT i) = σ * adjT i := by rw [← mul_assoc, hσβ]
  rw [hassoc] at hup
  have hdown : permLen σ ≤ permLen (σ * adjT i) + 1 := by
    have h := permLen_mul_le (σ * adjT i) (adjT i)
    rw [mul_adjT_adjT, permLen_adjT] at h
    exact h
  have hkey : permLen (σ * adjT i) + 1 = permLen σ := by omega
  refine ⟨i, descent_of_permLen_drop hkey, ?_⟩
  rw [le_def]
  simp only [perm_of]
  rw [show (perm x)⁻¹ * (σ * adjT i) = β * adjT i by rw [hβ, mul_assoc]]
  omega


end WeakOrder

end CubeChains

namespace ChainCat

variable {n : ℕ}

/-! ## `cross`, as a functor to the weak order -/

/-- **A refinement factors the crossing permutation on the right.** -/
theorem cross_eq_mul {c c' : Ch (□n)} (f : c ⟶ c') :
    cross c = cross c' * crossPerm (dimSum_dims_cube c) f := by
  rw [cross, ← comp_toCubeTop f, crossPerm_comp]
  rfl

/-- The weak-order class of a chain of `□n` — its crossing permutation. -/
noncomputable def weakClass (c : Ch (□n)) : WeakOrder n := WeakOrder.of (cross c)

@[simp] theorem perm_weakClass (c : Ch (□n)) : WeakOrder.perm (weakClass c) = cross c := rfl

/-- **A refinement descends the weak order**, by length-additivity of the crossings. -/
theorem weakClass_le {c c' : Ch (□n)} (f : c ⟶ c') : weakClass c' ≤ weakClass c := by
  have hmul : cross c' * crossPerm (dimSum_dims_cube c) f = cross c := (cross_eq_mul f).symm
  have h : permLen (cross c') + permLen (crossPerm (dimSum_dims_cube c) f)
      = permLen (cross c' * crossPerm (dimSum_dims_cube c) f) := by
    rw [hmul]
    have hadd := crossLen_eq_add f
    rw [crossLen, crossLen] at hadd
    omega
  have hle := WeakOrder.le_of_mul h
  rw [hmul] at hle
  exact hle

/-- The crossing permutation, as a functor to the weak order read backwards. -/
noncomputable def weakFunctor (n : ℕ) : Ch (□n) ⥤ (WeakOrder n)ᵒᵖ where
  obj c := Opposite.op (weakClass c)
  map f := (homOfLE (weakClass_le f)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem weakClass_eq_of_W {c c' : Ch (□n)} {f : c ⟶ c'} (hf : W (□n) f) :
    weakClass c = weakClass c' := by
  rw [weakClass, weakClass, cross_eq_mul f, crossPerm_eq_one_of_W _ hf, mul_one]

theorem weakFunctor_inverts : (W (□n)).IsInvertedBy (weakFunctor n) := by
  intro c c' f hf
  exact ⟨(homOfLE (le_of_eq (weakClass_eq_of_W hf))).op,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The crossing permutation, on the localized cube slice. -/
noncomputable def weakLoc (n : ℕ) : (W (□n)).Localization ⥤ (WeakOrder n)ᵒᵖ :=
  Localization.Construction.lift (weakFunctor n) weakFunctor_inverts

/-- **A morphism of the localized cube slice descends the weak order.**  This is the necessary
half of the identification. -/
theorem weakClass_le_of_loc_hom {c c' : Ch (□n)}
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') : weakClass c' ≤ weakClass c :=
  leOfHom ((weakLoc n).map g).unop


/-! ## The collapse: off `W`, the crossing permutation strictly descends -/

/-- **A refinement that preserves the crossing permutation is a merge.**  With `crossLen_eq_add`
this is immediate, and it is what makes the weak order the whole story: a non-`W` arrow strictly
descends `cross`, so the `W`-arrows are exactly the fibres of `cross`. -/
theorem W_of_cross_eq {c c' : Ch (□n)} (f : c ⟶ c') (h : cross c = cross c') : W (□n) f := by
  rw [W_iff_crossPerm_eq_one (dimSum_dims_cube c) f]
  refine eq_one_of_permLen_eq_zero _ ?_
  have hadd := crossLen_eq_add f
  rw [crossLen, crossLen, h] at hadd
  omega

/-- `W` is exactly the class of refinements fixing the weak-order class. -/
theorem W_iff_weakClass_eq {c c' : Ch (□n)} (f : c ⟶ c') :
    W (□n) f ↔ weakClass c = weakClass c' :=
  ⟨weakClass_eq_of_W, fun h => W_of_cross_eq f (WeakOrder.of_injective h)⟩


/-! ## Every object is a run

A chain of a cube *is* a chart (`chartHomEquiv`), so the base's crossing-free merge out of the run
lifts to one here by composing charts — the fibre description of `Ch (□n) ⥤ Ch Zbp`. -/

/-- **Every chain of a cube is entered from a run by a merge.** -/
theorem exists_W_run (c : Ch (□n)) :
    ∃ (r : Ch (□n)) (f : r ⟶ c), r.dims = 𝟙^n ∧ W (□n) f :=
  exists_W_run_gen c (dimSum_dims_cube c)

/-- **…and it carries the same weak-order class**, the merge crossing nothing. -/
theorem exists_W_run_weakClass (c : Ch (□n)) :
    ∃ (r : Ch (□n)) (f : r ⟶ c), r.dims = 𝟙^n ∧ W (□n) f ∧ weakClass r = weakClass c := by
  obtain ⟨r, f, hr, hf⟩ := exists_W_run c
  exact ⟨r, f, hr, hf, weakClass_eq_of_W hf⟩


/-- **A run is pinned by its crossing permutation.**  A chain of a cube is a chart, `crossPerm` sees
only the wedge map, and a wedge map is pinned by its crossing permutation
(`hom_ext_of_crossPerm`) — so `cross` is injective on runs, with no coordinates in sight. -/
theorem run_eq_of_cross_eq {r r' : Ch (□n)} (hr : r.dims = 𝟙^n) (hr' : r'.dims = 𝟙^n)
    (h : cross r = cross r') : r = r' := by
  obtain ⟨d, x⟩ := r
  obtain ⟨d', x'⟩ := r'
  subst hr
  subst hr'
  have key : zHom (Hom.φ (toCubeTop (⟨𝟙^n, x⟩ : Ch (□n))))
      = zHom (Hom.φ (toCubeTop (⟨𝟙^n, x'⟩ : Ch (□n)))) :=
    hom_ext_of_crossPerm (h := dimSum_replicate n) h
  have hφ : x ≫ (topWedgeIso n).inv = x' ≫ (topWedgeIso n).inv := by
    have hk := congrArg Hom.φ key
    rwa [zHom_φ, zHom_φ] at hk
  rw [(cancel_mono (topWedgeIso n).inv).mp hφ]


/-! ## The runs of a cube are its weak-order classes

`cross` is injective on runs and there are `n!` of each, so it is a bijection — the permutation a
run realises never has to be computed. -/

theorem run_dims (r : Run (□n)) : r.chain.dims = 𝟙^n :=
  cubeChain_dims_ones r.chain r.ones

/-- The weak-order class of a run. -/
noncomputable def crossRun (r : Run (□n)) : Equiv.Perm (Fin n) := cross r.chain

theorem crossRun_injective : Function.Injective (crossRun (n := n)) := fun r r' h =>
  Run.ext (run_eq_of_cross_eq (run_dims r) (run_dims r') h)

/-- **A run of a cube *is* a permutation, read by `cross`** — injective between two copies of
`n!`. -/
theorem crossRun_bijective : Function.Bijective (crossRun (n := n)) :=
  (Function.Bijective.of_comp_iff _ (runPermEquiv n).symm.bijective).mp
    (Finite.injective_iff_bijective.mp
      (crossRun_injective.comp (runPermEquiv n).symm.injective))

/-- The run realising a given permutation. -/
noncomputable def runAt (σ : Equiv.Perm (Fin n)) : Run (□n) :=
  (crossRun_bijective.surjective σ).choose

@[simp] theorem cross_runAt (σ : Equiv.Perm (Fin n)) : cross (runAt σ).chain = σ :=
  (crossRun_bijective.surjective σ).choose_spec

@[simp] theorem weakClass_runAt (σ : Equiv.Perm (Fin n)) :
    weakClass (runAt σ).chain = WeakOrder.of σ := by
  rw [weakClass, cross_runAt]


/-! ## The objects of the localized cube slice -/

/-- **Every object of the localized cube slice is a chain** — `Q` is the identity on objects. -/
theorem exists_loc_obj (X : (W (□n)).Localization) : ∃ c : Ch (□n), (W (□n)).Q.obj c = X :=
  ⟨(Localization.Construction.objEquiv (W := W (□n))).symm X,
    (Localization.Construction.objEquiv (W := W (□n))).apply_symm_apply X⟩

/-- **Every object of the localized cube slice is a run** — the merge out of its run is inverted. -/
theorem exists_run_iso (c : Ch (□n)) :
    ∃ r : Run (□n), Nonempty ((W (□n)).Q.obj r.chain ≅ (W (□n)).Q.obj c) := by
  obtain ⟨r, f, hr, hf⟩ := exists_W_run c
  haveI : IsIso ((W (□n)).Q.map f) := Localization.inverts (W (□n)).Q (W (□n)) f hf
  exact ⟨⟨r, fun d hd => List.eq_of_mem_replicate (hr ▸ hd)⟩,
    ⟨asIso ((W (□n)).Q.map f)⟩⟩

/-- **…and distinct runs stay distinct**: `cross` is a two-sided bound on an isomorphism, so
antisymmetry of the weak order pins the run. -/
theorem run_eq_of_iso {r r' : Run (□n)}
    (e : (W (□n)).Q.obj r.chain ≅ (W (□n)).Q.obj r'.chain) : r = r' :=
  crossRun_injective (WeakOrder.of_injective
    ((weakClass_le_of_loc_hom e.inv).antisymm (weakClass_le_of_loc_hom e.hom)))

end ChainCat
