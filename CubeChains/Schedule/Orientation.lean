import CubeChains.Schedule.Cover
import CubeChains.Schedule.HDA
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.CategoryTheory.SingleObj

/-!
# Schedule/Orientation — the orientation character of `Sched K`

The chart of a chain `a` is an open cone in `ℝ^(EventObj a)` (`Schedule/Space.lean`), and the
transition between two charts is the event bijection `eventEquiv f` — a permutation of the
coordinates.  Its sign is the **orientation character**

    orSign : (a ⟶ b) → ℤˣ ,      orSign (𝟙 a) = 1 ,   orSign (f ≫ g) = orSign f * orSign g

i.e. a ℤ/2 local system on `Ch K` — the first Stiefel–Whitney class of the schedule space.  `K` is
`Orientable` when this cocycle is a coboundary.

A global event naming orders all events of all chains coherently; comparing the lex order of a
chain's events with that naming's order gives the coboundary
(`orientable_of_hasGlobalEventNaming`).

The sign of a bijection `u : α ≃ β` of *finite linear orders* is measured by reading `u` through the
two order isomorphisms with `Fin k` (`ordPerm`).  The common `k` is passed explicitly (with proofs
`Fintype.card α = k`, `Fintype.card β = k`) so that composites of bijections stay in **one**
permutation group — otherwise every composition drags a `Fin`-cast.  Gotcha: the linear orders are
explicit arguments, not instances, because the whole point is to compare *two* orders on
`EventObj a` (the canonical lex one and the one pulled back from a naming).
-/

open CategoryTheory CubeChain

namespace CubeChains

open HDA

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

theorem eventEquiv_id (a : Ch K) : eventEquiv (𝟙 a) = Equiv.refl (EventObj a) :=
  Equiv.ext eventMap_id

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

/-- The orientation character as a functor to the one-object category `ℤˣ`. -/
noncomputable def orChar (K : BPSet) : Ch K ⥤ SingleObj ℤˣ where
  obj _ := SingleObj.star ℤˣ
  map f := orSign f
  map_id a := orSign_id a
  map_comp f g := by
    change orSign (f ≫ g) = orSign g * orSign f
    rw [orSign_comp, mul_comm]

/-- **Orientability of the schedule space.**  The orientation cocycle is a coboundary: chart signs
`ε` can be chosen chain-by-chain so that every transition sign is `ε a * ε b` (`ℤˣ` has exponent 2,
so `ε a * ε b` is its own inverse — no direction convention is needed). -/
def Orientable (K : BPSet) : Prop :=
  ∃ ε : Ch K → ℤˣ, ∀ {a b : Ch K} (f : a ⟶ b), orSign f = ε a * ε b

/-! ## A global event naming orients the schedule space

Well-order the names.  Each chain then carries a second linear order on its events — pulled back
from the names — and the transition `eventEquiv f` is an *order isomorphism* for those, by
coherence.  So the naming order is a "constant" reference frame, and the sign comparing it with the
lex order of each chain is the coboundary. -/

/-- **Orientability from a global event naming.**  `ε a` = the sign comparing `a`'s lex order of
events with the order pulled back from the (well-ordered) naming; coherence makes `eventEquiv f` an
order isomorphism for the pulled-back orders, so its lex sign splits as `ε a * ε b`. -/
theorem orientable_of_hasGlobalEventNaming (K : BPSet) (h : HasGlobalEventNaming K) :
    Orientable K := by
  obtain ⟨σ, name, hcoh, hinj⟩ := h
  obtain ⟨Lσ, -⟩ := exists_wellFoundedLT σ
  letI := Lσ
  -- the naming order on the events of a chain
  let P : ∀ a : Ch K, LinearOrder (EventObj a) := fun a =>
    LinearOrder.lift' (fun e : EventObj a => name ⟨a, e⟩) (hinj a)
  refine ⟨fun a => ordSign (eventObjLinearOrder a) (P a) rfl rfl (Equiv.refl (EventObj a)), ?_⟩
  intro a b f
  have hb : Fintype.card (EventObj b) = Fintype.card (EventObj a) :=
    (card_eventObj_eq_of_hom f).symm
  -- `eventEquiv f` is an order isomorphism for the naming orders
  have hord : ∀ x y : EventObj a, (P a).le x y ↔ (P b).le (eventEquiv f x) (eventEquiv f y) := by
    intro x y
    have hx : name (⟨b, eventEquiv f x⟩ : Σ a : Ch K, EventObj a) = name ⟨a, x⟩ := hcoh f x
    have hy : name (⟨b, eventEquiv f y⟩ : Σ a : Ch K, EventObj a) = name ⟨a, y⟩ := hcoh f y
    change name (⟨a, x⟩ : Σ a : Ch K, EventObj a) ≤ name ⟨a, y⟩
      ↔ name (⟨b, eventEquiv f x⟩ : Σ a : Ch K, EventObj a) ≤ name ⟨b, eventEquiv f y⟩
    rw [hx, hy]
  -- the `b`-side sign, read at `a`'s cardinality, is `ε b` (inverse = itself in `ℤˣ`)
  have hbside : ordSign (P b) (eventObjLinearOrder b) hb hb (Equiv.refl (EventObj b))
      = ordSign (eventObjLinearOrder b) (P b) rfl rfl (Equiv.refl (EventObj b)) := by
    have hone : ordSign (eventObjLinearOrder b) (P b) hb hb (Equiv.refl (EventObj b))
          * ordSign (P b) (eventObjLinearOrder b) hb hb (Equiv.refl (EventObj b)) = 1 := by
      rw [← ordSign_trans (eventObjLinearOrder b) (P b) (eventObjLinearOrder b) hb hb hb
        (Equiv.refl (EventObj b)) (Equiv.refl (EventObj b))]
      rw [Equiv.refl_trans]
      exact ordSign_refl _ hb hb
    have hcast : ordSign (eventObjLinearOrder b) (P b) hb hb (Equiv.refl (EventObj b))
        = ordSign (eventObjLinearOrder b) (P b) rfl rfl (Equiv.refl (EventObj b)) :=
      ordSign_cast _ _ hb hb rfl rfl _
    rw [hcast] at hone
    rw [eq_comm, ← inv_eq_of_mul_eq_one_right hone, intUnits_inv_self]
  -- split the lex sign through the two naming orders
  calc orSign f
      = ordSign (eventObjLinearOrder a) (eventObjLinearOrder b) rfl hb
          ((Equiv.refl (EventObj a)).trans (eventEquiv f)) := by
        rw [Equiv.refl_trans]; rfl
    _ = ordSign (eventObjLinearOrder a) (P a) rfl rfl (Equiv.refl (EventObj a))
          * ordSign (P a) (eventObjLinearOrder b) rfl hb (eventEquiv f) :=
        ordSign_trans _ _ _ rfl rfl hb _ _
    _ = ordSign (eventObjLinearOrder a) (P a) rfl rfl (Equiv.refl (EventObj a))
          * (ordSign (P a) (P b) rfl hb (eventEquiv f)
              * ordSign (P b) (eventObjLinearOrder b) hb hb (Equiv.refl (EventObj b))) := by
        congr 1
        rw [← ordSign_trans (P a) (P b) (eventObjLinearOrder b) rfl hb hb
          (eventEquiv f) (Equiv.refl (EventObj b)), Equiv.trans_refl]
    _ = ordSign (eventObjLinearOrder a) (P a) rfl rfl (Equiv.refl (EventObj a))
          * ordSign (eventObjLinearOrder b) (P b) rfl rfl (Equiv.refl (EventObj b)) := by
        rw [ordSign_eq_one (P a) (P b) rfl hb (eventEquiv f) hord, one_mul, hbside]

/-- A run-injective HDA labelling orients the schedule space (via
`hasGlobalEventNaming_of_labelling`). -/
theorem orientable_of_labelling {A : Type} (ℓ : EdgeLabelling K A) (h : RunInjective ℓ) :
    Orientable K :=
  orientable_of_hasGlobalEventNaming K (hasGlobalEventNaming_of_labelling ℓ h)

end CubeChains
