import CubeChains.Events.EventMapBij
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Hom.Set

/-!
# Events/OrdSign — comparing two orders of a chain's events

`ordSign Lα Lβ u` is the sign of a bijection `u : α ≃ β` of *finite linear orders*: read `u` through
the two order isomorphisms with `Fin k` and take the sign of the resulting permutation.  It is the
tool for comparing two frames on one finite set — the cocycle identity `ordSign_trans` factors
through **any** middle order.

Applied to the events of a cube chain with their lex order (bead, then coordinate inside the bead),
the sign of the event bijection of a refinement is the **orientation character**

    orSign : (a ⟶ b) → ℤˣ ,      orSign (𝟙 a) = 1 ,   orSign (f ≫ g) = orSign f * orSign g

a ℤ/2 local system on `Ch K`; `Orientable K` says this cocycle is a coboundary.

Gotcha: the linear orders are explicit arguments, not instances — the whole point is to compare
*two* orders on `EventObj a`.  The common cardinality `k` is passed explicitly (with proofs
`Fintype.card α = k`, `Fintype.card β = k`) so that composites stay in **one** permutation group,
instead of dragging a `Fin`-cast per composition.
-/

open CategoryTheory CubeChain

namespace CubeChains

/-! ## The sign of a bijection of finite linear orders -/

section OrdSign

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- `u : α ≃ β` read through the order isomorphisms `Fin k ≃o α`, `Fin k ≃o β`. -/
noncomputable def ordPerm (Lα : LinearOrder α) (Lβ : LinearOrder β) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (u : α ≃ β) : Equiv.Perm (Fin k) :=
  (@monoEquivOfFin α _ Lα k ha).toEquiv.trans
    (u.trans (@monoEquivOfFin β _ Lβ k hb).symm.toEquiv)

/-- The **sign** of a bijection of finite linear orders: `+1` iff it is an even permutation of the
two orderings. -/
noncomputable def ordSign (Lα : LinearOrder α) (Lβ : LinearOrder β) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (u : α ≃ β) : ℤˣ :=
  Equiv.Perm.sign (ordPerm Lα Lβ ha hb u)

/-- The value does not depend on the chosen `k` (nor on the cardinality proofs). -/
theorem ordSign_cast (Lα : LinearOrder α) (Lβ : LinearOrder β) {k k' : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k)
    (ha' : Fintype.card α = k') (hb' : Fintype.card β = k') (u : α ≃ β) :
    ordSign Lα Lβ ha hb u = ordSign Lα Lβ ha' hb' u := by
  subst ha; subst ha'; rfl

/-- An order isomorphism is read as the identity permutation. -/
theorem ordPerm_eq_one (Lα : LinearOrder α) (Lβ : LinearOrder β) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (u : α ≃ β)
    (hu : ∀ x y : α, Lα.le x y ↔ Lβ.le (u x) (u y)) :
    ordPerm Lα Lβ ha hb u = 1 := by
  letI := Lα
  letI := Lβ
  let U : α ≃o β := ⟨u, fun {x y} => (hu x y).symm⟩
  have hO : (monoEquivOfFin α ha).trans (U.trans (monoEquivOfFin β hb).symm)
      = OrderIso.refl (Fin k) := Subsingleton.elim _ _
  apply Equiv.ext
  intro x
  exact congrArg (fun e : Fin k ≃o Fin k => e x) hO

/-- The sign of an order isomorphism is `1`. -/
theorem ordSign_eq_one (Lα : LinearOrder α) (Lβ : LinearOrder β) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (u : α ≃ β)
    (hu : ∀ x y : α, Lα.le x y ↔ Lβ.le (u x) (u y)) :
    ordSign Lα Lβ ha hb u = 1 := by
  rw [ordSign, ordPerm_eq_one Lα Lβ ha hb u hu, map_one]

theorem ordSign_refl (Lα : LinearOrder α) {k : ℕ}
    (ha ha' : Fintype.card α = k) : ordSign Lα Lα ha ha' (Equiv.refl α) = 1 :=
  ordSign_eq_one Lα Lα ha ha' (Equiv.refl α) fun _ _ => Iff.rfl

theorem ordPerm_trans (Lα : LinearOrder α) (Lβ : LinearOrder β) (Lγ : LinearOrder γ) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (hc : Fintype.card γ = k)
    (u : α ≃ β) (v : β ≃ γ) :
    ordPerm Lα Lγ ha hc (u.trans v)
      = ordPerm Lβ Lγ hb hc v * ordPerm Lα Lβ ha hb u := by
  apply Equiv.ext
  intro x
  simp [ordPerm, Equiv.Perm.mul_apply]

/-- The cocycle identity: the sign is multiplicative in the middle order `Lβ`, whichever `Lβ` is. -/
theorem ordSign_trans (Lα : LinearOrder α) (Lβ : LinearOrder β) (Lγ : LinearOrder γ) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (hc : Fintype.card γ = k)
    (u : α ≃ β) (v : β ≃ γ) :
    ordSign Lα Lγ ha hc (u.trans v)
      = ordSign Lα Lβ ha hb u * ordSign Lβ Lγ hb hc v := by
  rw [ordSign, ordSign, ordSign, ordPerm_trans Lα Lβ Lγ ha hb hc u v, map_mul, mul_comm]

end OrdSign

/-- `ℤˣ` has exponent 2. -/
theorem intUnits_inv_self (u : ℤˣ) : u⁻¹ = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

/-! ## The lex order on the events of a chain -/

variable {K : BPSet}

/-- The **lex order** on `EventObj a = Σ (bead), Fin (bead dimension)`: bead first, then coordinate
inside the bead. -/
noncomputable instance eventObjLinearOrder (a : Ch K) : LinearOrder (EventObj a) :=
  LinearOrder.lift' (fun e : EventObj a => (toLex ((e.1 : ℕ), (e.2 : ℕ)) : ℕ ×ₗ ℕ)) <| by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have h1 : (i : ℕ) = (j : ℕ) := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) h
    obtain rfl : i = j := Fin.ext h1
    have h2 : (x : ℕ) = (y : ℕ) := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h
    exact congrArg (Sigma.mk i) (Fin.ext h2)

/-- The order isomorphism `Fin (card (EventObj a)) ≃o EventObj a` of the lex order. -/
noncomputable def evFin (a : Ch K) :
    Fin (Fintype.card (EventObj a)) ≃o EventObj a :=
  monoEquivOfFin (EventObj a) rfl

/-! ## The orientation character -/

/-- The **orientation sign** of a refinement `f : a ⟶ b`: the sign of the coordinate permutation
`eventEquiv f` relates the lex orders of the two charts.  This is the transition sign of the atlas
of `Sched K`. -/
noncomputable def orSign {a b : Ch K} (f : a ⟶ b) : ℤˣ :=
  ordSign (eventObjLinearOrder a) (eventObjLinearOrder b) rfl
    (card_eventObj_eq_of_hom f).symm (eventEquiv f)

@[simp] theorem orSign_id (a : Ch K) : orSign (𝟙 a) = 1 := by
  rw [orSign, eventEquiv_id]
  exact ordSign_refl _ _ _

theorem orSign_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    orSign (f ≫ g) = orSign f * orSign g := by
  have hb : Fintype.card (EventObj b) = Fintype.card (EventObj a) :=
    (card_eventObj_eq_of_hom f).symm
  have hc : Fintype.card (EventObj c) = Fintype.card (EventObj a) :=
    (card_eventObj_eq_of_hom (f ≫ g)).symm
  rw [orSign, eventEquiv_comp,
    ordSign_trans (eventObjLinearOrder a) (eventObjLinearOrder b) (eventObjLinearOrder c)
      rfl hb hc (eventEquiv f) (eventEquiv g)]
  congr 1
  exact ordSign_cast _ _ hb hc rfl _ (eventEquiv g)

/-- **Orientability of the schedule space.**  The orientation cocycle is a coboundary: chart signs
`ε` can be chosen chain-by-chain so that every transition sign is `ε a * ε b` (`ℤˣ` has exponent 2,
so `ε a * ε b` is its own inverse — no direction convention is needed). -/
def Orientable (K : BPSet) : Prop :=
  ∃ ε : Ch K → ℤˣ, ∀ {a b : Ch K} (f : a ⟶ b), orSign f = ε a * ε b

end CubeChains
