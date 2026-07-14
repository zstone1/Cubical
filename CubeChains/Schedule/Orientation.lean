import CubeChains.Events.OrdSign
import CubeChains.Schedule.HDA
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.CategoryTheory.SingleObj

/-!
# Schedule/Orientation — the orientation character of `Sched K`

The chart of a chain `a` is an open cone in `ℝ^(EventObj a)` (`Schedule/Space.lean`), and the
transition between two charts is the event bijection `eventEquiv f` — a permutation of the
coordinates.  Its sign `orSign` (`Events/OrdSign.lean`) is a ℤ/2 local system on `Ch K`: the first
Stiefel–Whitney class of the schedule space, trivial exactly when `K` is `Orientable`.

A global event naming orders all events of all chains coherently, so it is a *constant* reference
frame; comparing it with the lex order of each chain's events gives the coboundary.
-/

open CategoryTheory CubeChain

namespace CubeChains

open HDA

variable {K : BPSet}

/-- The orientation character as a functor to the one-object category `ℤˣ`. -/
noncomputable def orChar (K : BPSet) : Ch K ⥤ SingleObj ℤˣ where
  obj _ := SingleObj.star ℤˣ
  map f := orSign f
  map_id a := orSign_id a
  map_comp f g := by
    change orSign (f ≫ g) = orSign g * orSign f
    rw [orSign_comp, mul_comm]

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
