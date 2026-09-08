import CubeChains.Machinery.Braid.PosGerm
import CubeChains.Machinery.Presentation.Partial

/-!
# Machinery/Braid/WeakAction — a downward-closed set of permutations is a partial braid action

`weakAction X` is the action of `PosBraid N` on a set `X` of permutations by **length-additive
right multiplication**: `β` is defined at `σ` when `σ·β` is still in `X` and crosses every pair
`β` names.  Downward-closure of `X` for the right weak order is the only hypothesis — it supplies
the intermediate of a two-step composite, which is exactly what multiplicativity asks for.

`weakActionOn` carries the action across a bijection, so a geometric set of runs can carry it
without ever being replaced by its permutations.
-/

namespace CubeChains

open CategoryTheory Equiv

variable {N : ℕ}

/-- The permutations `X` names. -/
abbrev WeakSet (X : Perm (Fin N) → Prop) : Type := {σ : Perm (Fin N) // X σ}

/-- **`X` is closed downwards** in the right weak order. -/
def WeakDown (X : Perm (Fin N) → Prop) : Prop :=
  ∀ {u v : Perm (Fin N)}, X v → permLen u + permLen (u⁻¹ * v) = permLen v → X u

/-- The whole symmetric group is closed downwards. -/
theorem weakDown_univ : WeakDown fun _ : Perm (Fin N) => True := fun _ _ => trivial

/-- **A set with no condition is the permutations themselves.** -/
def weakSetUniv (N : ℕ) : WeakSet (fun _ : Perm (Fin N) => True) ≃ Perm (Fin N) :=
  Equiv.subtypeUnivEquiv fun _ => trivial

variable (X : Perm (Fin N) → Prop)

open scoped Classical in
/-- Right multiplication by `A`, where it stays in `X` and adds every crossing. -/
noncomputable def weakStep (A : Perm (Fin N)) : Option (WeakSet X) → Option (WeakSet X) :=
  fun o => o.bind fun x =>
    if h : X (x.1 * A) ∧ permLen x.1 + permLen A = permLen (x.1 * A)
      then some ⟨x.1 * A, h.1⟩ else none

@[simp] theorem weakStep_none (A : Perm (Fin N)) : weakStep X A none = none := rfl

/-- **The step in closed form**: it lands on `x·A`, where the lengths add. -/
theorem weakStep_eq_some_iff {A : Perm (Fin N)} {x y : WeakSet X} :
    weakStep X A (some x) = some y ↔
      y.1 = x.1 * A ∧ permLen x.1 + permLen A = permLen (x.1 * A) := by
  classical
  change (if h : X (x.1 * A) ∧ permLen x.1 + permLen A = permLen (x.1 * A)
      then some (⟨x.1 * A, h.1⟩ : WeakSet X) else none) = some y ↔ _
  by_cases h : X (x.1 * A) ∧ permLen x.1 + permLen A = permLen (x.1 * A)
  · rw [dif_pos h]
    exact ⟨fun hh => ⟨(congrArg Subtype.val (Option.some_inj.mp hh)).symm, h.2⟩,
      fun hy => congrArg some (Subtype.ext hy.1.symm)⟩
  · rw [dif_neg h]
    exact ⟨fun hh => absurd hh (by simp), fun hy => absurd ⟨hy.1 ▸ y.2, hy.2⟩ h⟩

/-- The step, as a partial endomorphism in the base's composition order. -/
noncomputable def weakEnd (A : Perm (Fin N)) : (strictEnd (WeakSet X))ᵐᵒᵖ :=
  MulOpposite.op ⟨weakStep X A, rfl⟩

@[simp] theorem weakEnd_unop_val (A : Perm (Fin N)) :
    (weakEnd X A).unop.val = weakStep X A := rfl

theorem weakEnd_one : weakEnd X 1 = 1 :=
  congrArg MulOpposite.op (Subtype.ext (funext fun o => by
    cases o with
    | none => rfl
    | some x =>
        exact (weakStep_eq_some_iff X).mpr ⟨(mul_one x.1).symm, by simp⟩))

/-- **The steps multiply where the lengths add** — the intermediate is squeezed out by
subadditivity, and `hX` puts it back in `X`. -/
theorem weakEnd_mul (hX : WeakDown X) {A B : Perm (Fin N)}
    (h : permLen (A * B) = permLen A + permLen B) :
    weakEnd X A * weakEnd X B = weakEnd X (A * B) := by
  refine congrArg MulOpposite.op (Subtype.ext (funext fun o => ?_))
  cases o with
  | none => rfl
  | some x =>
      change weakStep X B (weakStep X A (some x)) = weakStep X (A * B) (some x)
      refine Option.ext fun y => ?_
      change weakStep X B (weakStep X A (some x)) = some y ↔ weakStep X (A * B) (some x) = some y
      rw [weakStep_eq_some_iff]
      constructor
      · intro hh
        rcases hc : weakStep X A (some x) with _ | x'
        · rw [hc] at hh; exact absurd hh (by simp)
        rw [hc] at hh
        obtain ⟨hx', hlx'⟩ := (weakStep_eq_some_iff X).mp hc
        obtain ⟨hy, hly⟩ := (weakStep_eq_some_iff X).mp hh
        have hxab : x.1 * (A * B) = x'.1 * B := by rw [hx', mul_assoc]
        refine ⟨by rw [hy, hx', mul_assoc], ?_⟩
        rw [hxab, ← hly, hx', ← hlx', h]
        omega
      · rintro ⟨hy, hly⟩
        rw [← mul_assoc] at hy
        rw [← mul_assoc, h] at hly
        have hsub1 := permLen_mul_le x.1 A
        have hsub2 := permLen_mul_le (x.1 * A) B
        have hmid : permLen x.1 + permLen A = permLen (x.1 * A) := by omega
        have hlast : permLen (x.1 * A) + permLen B = permLen (x.1 * A * B) := by omega
        have hmem : X (x.1 * A) := hX (v := y.1) y.2 (by
          rw [hy, inv_mul_cancel_left]; omega)
        rw [(weakStep_eq_some_iff X (y := (⟨x.1 * A, hmem⟩ : WeakSet X))).mpr ⟨rfl, hmid⟩]
        exact (weakStep_eq_some_iff X).mpr ⟨hy, hlast⟩

/-- **A downward-closed set of permutations carries a partial action of the braid monoid.** -/
noncomputable def weakAction (hX : WeakDown X) : PosBraid N →* (strictEnd (WeakSet X))ᵐᵒᵖ :=
  PosBraid.lift (weakEnd X) (weakEnd_one X) fun _ _ h => weakEnd_mul X hX h

@[simp] theorem weakAction_posPerm (hX : WeakDown X) (σ : Perm (Fin N)) :
    weakAction X hX (posPerm σ) = weakEnd X σ := rfl

/-- **The action in closed form**: `β` is defined at `x` exactly where every crossing it names is
new there — so a defined `β` is reduced, hence a simple. -/
theorem weakAction_eq_some_iff (hX : WeakDown X) (β : PosBraid N) (x y : WeakSet X) :
    (weakAction X hX β).unop.val (some x) = some y ↔
      y.1 = x.1 * posPermHom N β ∧
        permLen x.1 + Multiplicative.toAdd (posLen N β) = permLen y.1 := by
  induction β using PosBraid.induction generalizing x y with
  | one =>
      simp only [map_one, MulOpposite.unop_one, OneMemClass.coe_one, toAdd_one, mul_one,
        Nat.add_zero]
      change some x = some y ↔ _
      exact ⟨fun hp => ⟨congrArg Subtype.val (Option.some_inj.mp hp).symm,
          congrArg (fun z : WeakSet X => permLen z.1) (Option.some_inj.mp hp)⟩,
        fun hy => congrArg some (Subtype.ext hy.1.symm)⟩
  | mul a σ ih =>
      have hsplit : ∀ o, (weakAction X hX (a * posPerm σ)).unop.val o
          = weakStep X σ ((weakAction X hX a).unop.val o) := fun o => by
        rw [map_mul]; rfl
      rw [hsplit, map_mul, map_mul, posPermHom_posPerm, posLen_posPerm, toAdd_mul, toAdd_ofAdd]
      constructor
      · intro hp
        rcases hc : (weakAction X hX a).unop.val (some x) with _ | x'
        · rw [hc] at hp; exact absurd hp (by simp)
        rw [hc] at hp
        obtain ⟨hx', hlx'⟩ := (ih x x').mp hc
        obtain ⟨hy, hly⟩ := (weakStep_eq_some_iff X).mp hp
        refine ⟨by rw [hy, hx', mul_assoc], ?_⟩
        rw [hy, ← hly, ← hlx']
        omega
      · rintro ⟨hy, hly⟩
        rw [← mul_assoc] at hy
        have h1 := permLen_mul_le (x.1 * posPermHom N a) σ
        have h2 := permLen_mul_le x.1 (posPermHom N a)
        have h3 := permLen_posPermHom_le a
        rw [← hy] at h1
        have hmid : permLen x.1 + Multiplicative.toAdd (posLen N a)
            = permLen (x.1 * posPermHom N a) := by omega
        have hmem : X (x.1 * posPermHom N a) := hX (v := y.1) y.2 (by
          rw [hy, inv_mul_cancel_left, ← hy]; omega)
        rw [(ih x ⟨x.1 * posPermHom N a, hmem⟩).mpr ⟨rfl, hmid⟩]
        refine (weakStep_eq_some_iff X).mpr ⟨hy, ?_⟩
        change permLen (x.1 * posPermHom N a) + permLen σ
          = permLen (x.1 * posPermHom N a * σ)
        rw [← hy]
        omega

/-! ## Carrying the action across a bijection -/

theorem optionMap_symm_map {Y Z : Type} (e : Y ≃ Z) (o : Option Y) :
    Option.map e.symm (Option.map e o) = o := by cases o <;> simp

theorem optionMap_map_symm {Y Z : Type} (e : Y ≃ Z) (o : Option Z) :
    Option.map e (Option.map e.symm o) = o := by cases o <;> simp

/-- **A bijection of sets is one of their partial endomorphism monoids.** -/
def strictEndCongr {Y Z : Type} (e : Y ≃ Z) : strictEnd Y ≃* strictEnd Z where
  toFun f := ⟨fun o => Option.map e (f.1 (Option.map e.symm o)), by
    change Option.map e (f.1 (Option.map e.symm none)) = none
    rw [show Option.map e.symm (none : Option Z) = none from rfl,
      show f.1 none = none from f.2]
    rfl⟩
  invFun g := ⟨fun o => Option.map e.symm (g.1 (Option.map e o)), by
    change Option.map e.symm (g.1 (Option.map e none)) = none
    rw [show Option.map e (none : Option Y) = none from rfl,
      show g.1 none = none from g.2]
    rfl⟩
  left_inv f := Subtype.ext (funext fun o => by
    change Option.map e.symm (Option.map e (f.1 (Option.map e.symm (Option.map e o)))) = f.1 o
    rw [optionMap_symm_map, optionMap_symm_map])
  right_inv g := Subtype.ext (funext fun o => by
    change Option.map e (Option.map e.symm (g.1 (Option.map e (Option.map e.symm o)))) = g.1 o
    rw [optionMap_map_symm, optionMap_map_symm])
  map_mul' f g := Subtype.ext (funext fun o => by
    change Option.map e (f.1 (g.1 (Option.map e.symm o)))
      = Option.map e (f.1 (Option.map e.symm (Option.map e (g.1 (Option.map e.symm o)))))
    rw [optionMap_symm_map])

@[simp] theorem strictEndCongr_apply_val {Y Z : Type} (e : Y ≃ Z) (f : strictEnd Y) (o : Option Z) :
    (strictEndCongr e f).val o = Option.map e (f.1 (Option.map e.symm o)) := rfl

/-- **The action, read on any set in bijection with `X`.** -/
noncomputable def weakActionOn {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X) :
    PosBraid N →* (strictEnd Y)ᵐᵒᵖ where
  toFun β := MulOpposite.op (strictEndCongr e.symm (weakAction X hX β).unop)
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, MulOpposite.unop_mul, map_mul]
    rfl

/-- **A defined braid is a germ step**: it is reduced, hence a simple, and it multiplies by its own
permutation. -/
theorem weakAction_reduced (hX : WeakDown X) {β : PosBraid N} {x y : WeakSet X}
    (h : (weakAction X hX β).unop.val (some x) = some y) : GermStep β x.1 y.1 := by
  obtain ⟨hy, hly⟩ := (weakAction_eq_some_iff X hX β x y).mp h
  have h1 := permLen_mul_le x.1 (posPermHom N β)
  have h2 := permLen_posPermHom_le β
  rw [← hy] at h1
  exact ⟨eq_posPerm_of_posLen (by omega), hy, by omega⟩

/-- **The acting braid is pinned by the two elements** — a defined braid is a simple, and a simple
is its permutation. -/
theorem weakAction_injective (hX : WeakDown X) {β γ : PosBraid N} {x y : WeakSet X}
    (hβ : (weakAction X hX β).unop.val (some x) = some y)
    (hγ : (weakAction X hX γ).unop.val (some x) = some y) : β = γ :=
  (weakAction_reduced X hX hβ).eq_of_eq (weakAction_reduced X hX hγ)

/-- **…in the same closed form**, read through the bijection. -/
theorem weakActionOn_eq_some_iff {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X)
    (β : PosBraid N) (u v : Y) :
    (weakActionOn X e hX β).unop.val (some u) = some v ↔
      (e v).1 = (e u).1 * posPermHom N β ∧
        permLen (e u).1 + Multiplicative.toAdd (posLen N β) = permLen (e v).1 := by
  rw [← weakAction_eq_some_iff X hX β (e u) (e v)]
  change Option.map e.symm ((weakAction X hX β).unop.val (some (e u))) = some v ↔ _
  constructor
  · intro h
    have h' := congrArg (Option.map e) h
    rwa [optionMap_map_symm, show Option.map e (some v) = some (e v) from rfl] at h'
  · intro h
    rw [h, show Option.map e.symm (some (e v)) = some (e.symm (e v)) from rfl,
      Equiv.symm_apply_apply]

/-- **The acting braid is pinned by the two elements**, read through the bijection. -/
theorem weakActionOn_injective {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X)
    {β γ : PosBraid N} {u v : Y}
    (hβ : (weakActionOn X e hX β).unop.val (some u) = some v)
    (hγ : (weakActionOn X e hX γ).unop.val (some u) = some v) : β = γ :=
  weakAction_injective X hX
    ((weakAction_eq_some_iff X hX β (e u) (e v)).mpr
      ((weakActionOn_eq_some_iff X e hX β u v).mp hβ))
    ((weakAction_eq_some_iff X hX γ (e u) (e v)).mpr
      ((weakActionOn_eq_some_iff X e hX γ u v).mp hγ))

/-- **A defined braid is a germ step**, read through the bijection. -/
theorem weakActionOn_germStep {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X)
    {β : PosBraid N} {u v : Y} (h : (weakActionOn X e hX β).unop.val (some u) = some v) :
    GermStep β (e u).1 (e v).1 :=
  weakAction_reduced X hX ((weakAction_eq_some_iff X hX β (e u) (e v)).mpr
    ((weakActionOn_eq_some_iff X e hX β u v).mp h))

/-- **Definedness *is* the germ condition** — `Option` is only its encoding, so every statement
about the action can be read without one. -/
theorem weakActionOn_eq_some_iff_germStep {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X)
    (β : PosBraid N) (u v : Y) :
    (weakActionOn X e hX β).unop.val (some u) = some v ↔ GermStep β (e u).1 (e v).1 := by
  refine ⟨weakActionOn_germStep X e hX, fun hg => ?_⟩
  refine (weakActionOn_eq_some_iff X e hX β u v).mpr ⟨hg.mul_eq, ?_⟩
  have hlen : Multiplicative.toAdd (posLen N β) = permLen (posPermHom N β) := by
    conv_lhs => rw [hg.simple]
    rw [posLen_posPerm, toAdd_ofAdd]
  rw [hlen]
  exact hg.permLen_add

/-- **The atom of the action**: right multiplication by `adjT k`, defined exactly at an ascent.
This is the closed form a geometric atom family is compared against. -/
theorem weakActionOn_adjT_eq_some_iff {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X)
    (k : Fin (N - 1)) (u v : Y) :
    (weakActionOn X e hX (posPerm (adjT k))).unop.val (some u) = some v ↔
      (e u).1 (adjLo k) < (e u).1 (adjHi k) ∧ (e v).1 = (e u).1 * adjT k := by
  rw [weakActionOn_eq_some_iff, posPermHom_posPerm, posLen_posPerm, permLen_adjT, toAdd_ofAdd]
  exact ⟨fun ⟨hv, hl⟩ => ⟨ascent_of_permLen_mul_adjT (by rw [← hv]; omega), hv⟩,
    fun ⟨ha, hv⟩ => ⟨hv, by rw [hv, permLen_mul_adjT ha]⟩⟩

/-- **…and every rise is realised**, read through the bijection. -/
theorem weakActionOn_of_le {Y : Type} (e : Y ≃ WeakSet X) (hX : WeakDown X) {u v : Y}
    (h : permLen (e u).1 + permLen ((e u).1⁻¹ * (e v).1) = permLen (e v).1) :
    (weakActionOn X e hX (posPerm ((e u).1⁻¹ * (e v).1))).unop.val (some u) = some v :=
  (weakActionOn_eq_some_iff X e hX _ u v).mpr
    ⟨(mul_inv_cancel_left (e u).1 (e v).1).symm, by rw [posLen_posPerm, toAdd_ofAdd]; exact h⟩

end CubeChains
