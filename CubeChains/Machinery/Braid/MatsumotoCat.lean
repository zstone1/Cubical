import CubeChains.Machinery.Braid.WeakOrder
import Mathlib.CategoryTheory.Category.Basic

/-!
# Machinery/Braid/MatsumotoCat — Matsumoto between distinct objects

`Machinery/Braid/Matsumoto` lifts an Artin family into a *monoid*, where every generator is a loop.
Here one object carries each permutation of a set closed under peeling descents, and an adjacent
ascent is an arrow between two of them, so a reduced word is a **climb** and there is nothing to
multiply.  `Web.IsArtin` — two descents of an element are closed below it, as far below as their
Coxeter exponent — then makes any two climbs with the same ends name one arrow.

    w ──▸ c ──▸ b ──e──▸ v        the two words of the Coxeter exponent,
          └────▸ b' ─e'─▸ v       reached by `ih` through any climb `w ⟶ c`

The two descents are apart or consecutive, and the foot is reached by iterating `exists_step` —
peel a descent of the residue `w⁻¹v`, which is exactly what keeps the peel above `w`.
-/

namespace CubeChains

open CategoryTheory Equiv

universe u

variable {n : ℕ} {V : Type u} {p : V → Perm (Fin n)}

/-! ## Ascents and climbs -/

/-- An adjacent ascent inside `V`: `p v` crosses the `idx`-th pair, which `p w` has not. -/
structure Ascent (p : V → Perm (Fin n)) (w v : V) where
  /-- Which pair the ascent crosses. -/
  idx : Fin (n - 1)
  /-- `p w` has not crossed it. -/
  asc : p w (adjLo idx) < p w (adjHi idx)
  /-- …and `p v` is `p w` with it crossed. -/
  perm_eq : p v = p w * adjT idx

/-- An ascent is pinned by the pair it crosses. -/
theorem Ascent.eq_of_idx {w v : V} {e e' : Ascent p w v} (h : e.idx = e'.idx) : e = e' := by
  obtain ⟨i, hi, hi'⟩ := e
  obtain ⟨j, hj, hj'⟩ := e'
  simp only at h
  subst h
  rfl

/-- …and read at the top, the pair is a descent. -/
theorem Ascent.descent {w v : V} (e : Ascent p w v) : p v (adjHi e.idx) < p v (adjLo e.idx) := by
  rw [e.perm_eq, Perm.mul_apply, Perm.mul_apply, adjT_lo, adjT_hi]
  exact e.asc

/-- …so the ascent reads backwards as a peel. -/
theorem Ascent.perm_eq' {w v : V} (e : Ascent p w v) : p w = p v * adjT e.idx := by
  rw [e.perm_eq, mul_adjT_adjT]

theorem Ascent.permLen_eq {w v : V} (e : Ascent p w v) : permLen (p v) = permLen (p w) + 1 := by
  rw [e.perm_eq, permLen_mul_adjT e.asc]

/-- **Two ascents into one element differ by the pair they span** — whose order is the Coxeter
exponent, so the pair is what the relation between them is indexed by. -/
theorem Ascent.inv_mul {v b b' : V} (e : Ascent p b v) (e' : Ascent p b' v) :
    (p b)⁻¹ * p b' = adjT e.idx * adjT e'.idx := by
  rw [e.perm_eq', e'.perm_eq', mul_inv_rev, adjT_inv, mul_assoc, inv_mul_cancel_left]

/-- **…so they come from different elements exactly when they cross different pairs.** -/
theorem Ascent.idx_ne_iff (hp : Function.Injective p) {v b b' : V} (e : Ascent p b v)
    (e' : Ascent p b' v) : (e.idx : ℕ) ≠ (e'.idx : ℕ) ↔ b ≠ b' := by
  refine ⟨fun h hc => ?_, fun h hc => h (hp ?_)⟩
  · subst hc
    exact h (congrArg Fin.val (adjT_injective
      (mul_left_cancel (a := p v) (e.perm_eq'.symm.trans e'.perm_eq'))))
  · rw [e.perm_eq', e'.perm_eq', Fin.ext hc]

theorem Ascent.le {w v : V} (e : Ascent p w v) : WeakOrder.of (p w) ≤ WeakOrder.of (p v) := by
  rw [e.perm_eq']
  exact WeakOrder.of_mul_adjT_le e.descent

/-- An ascending chain of adjacent transpositions — a reduced word, climbing from `w` to `v`. -/
inductive Climb (p : V → Perm (Fin n)) : V → V → Type u
  | nil {v : V} : Climb p v v
  | cons {w b v : V} (R : Climb p w b) (e : Ascent p b v) : Climb p w v

namespace Climb

theorem le {w v : V} (R : Climb p w v) : WeakOrder.of (p w) ≤ WeakOrder.of (p v) := by
  induction R with
  | nil => exact le_refl _
  | cons R e ih => exact ih.trans e.le

/-- A climb never shortens — which is what rules out a climb against an ascent. -/
theorem permLen_le {w v : V} (R : Climb p w v) : permLen (p w) ≤ permLen (p v) := by
  simpa only [WeakOrder.perm_of] using WeakOrder.permLen_le_of_le R.le

/-- **A climb that returns to its start is trivial** — every ascent raises the length, and a climb
never shortens. -/
theorem eq_nil {w : V} : ∀ R : Climb p w w, R = Climb.nil
  | .nil => rfl
  | .cons R e => absurd R.permLen_le (by rw [e.permLen_eq]; omega)

/-- **A climb that raises the length by one is a single ascent** — so it is pinned by its two ends,
even when the climb itself was chosen.  This is what makes a length-one word canonical. -/
theorem eq_start_of_permLen_eq (hp : Function.Injective p) {w b : V} (R : Climb p w b)
    (h : permLen (p b) = permLen (p w)) : w = b :=
  hp (WeakOrder.eq_of_le_of_permLen_eq R.le h.symm)

theorem eq_cons_nil (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 1) : ∃ e : Ascent p w v, R = Climb.nil.cons e := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain rfl := eq_start_of_permLen_eq hp R (by have := e.permLen_eq; omega)
      exact ⟨e, congrArg (fun S => Climb.cons S e) (eq_nil R)⟩

/-- **A climb of length two is two ascents** — through the middle the climb itself names, which is
not forced by the two ends. -/
theorem eq_cons_cons (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 2) :
    ∃ (b : V) (f₁ : Ascent p w b) (f₂ : Ascent p b v), R = (Climb.nil.cons f₁).cons f₂ := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain ⟨f₁, rfl⟩ := eq_cons_nil hp R (by have := e.permLen_eq; omega)
      exact ⟨_, f₁, e, rfl⟩

/-- Climbs concatenate. -/
def comp {w b : V} (R : Climb p w b) : ∀ {v : V}, Climb p b v → Climb p w v
  | _, .nil => R
  | _, .cons R' e => (R.comp R').cons e

@[simp] theorem comp_nil {w b : V} (R : Climb p w b) : R.comp (.nil : Climb p b b) = R := rfl

@[simp] theorem comp_cons {w b c v : V} (R : Climb p w b) (R' : Climb p b c)
    (e : Ascent p c v) : R.comp (R'.cons e) = (R.comp R').cons e := rfl

end Climb

/-! ## A web of ascents

The data a climb can be evaluated on: an object per element of `V`, an arrow per ascent.
`perm_inj` and `exists_desc` are what make the index set a down-closed set of permutations — the
hypothesis Matsumoto is stated under, and they are already enough for every climb to exist
(`Descents.exists_climb_of_le`).
-/

/-- A down-closed family of permutations: pinned by the permutation it carries, and closed under
peeling an adjacent descent. -/
structure Descents (n : ℕ) (V : Type u) where
  /-- The permutation an element performs. -/
  perm : V → Perm (Fin n)
  /-- An element is pinned by its permutation. -/
  perm_inj : Function.Injective perm
  /-- Peeling an adjacent descent stays inside. -/
  exists_desc (v : V) (k : Fin (n - 1)) : perm v (adjHi k) < perm v (adjLo k) →
    ∃ w : V, perm w = perm v * adjT k

namespace Descents

variable (W : Descents n V)

/-- The ascent a descent of `perm v` names, once its peel is realised. -/
def descAsc {v w : V} {k : Fin (n - 1)} (hd : W.perm v (adjHi k) < W.perm v (adjLo k))
    (hw : W.perm w = W.perm v * adjT k) : Ascent W.perm w v where
  idx := k
  asc := by rw [hw]; exact adjT_ascent_of_descent hd
  perm_eq := by rw [hw, mul_adjT_adjT]

/-- **One peel, staying above a foot**: at a descent of the residue `w⁻¹v` the peel of `v` is
realised, still above `w` and one crossing below `v`.  The square and the hexagon are this, twice
and three times over. -/
theorem exists_step {w v : V} {k : Fin (n - 1)}
    (hwv : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v))
    (hd : ((W.perm w)⁻¹ * W.perm v) (adjHi k) < ((W.perm w)⁻¹ * W.perm v) (adjLo k)) :
    ∃ u : V, W.perm u = W.perm v * adjT k ∧
      WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm u) ∧
      WeakOrder.of (W.perm u) ≤ WeakOrder.of (W.perm v) ∧
      permLen (W.perm u) + 1 = permLen (W.perm v) := by
  have hlen := WeakOrder.permLen_mul_adjT_of_residue hwv hd
  obtain ⟨u, hu⟩ := W.exists_desc v k (descent_of_permLen_drop hlen)
  exact ⟨u, hu, by rw [hu]; exact WeakOrder.le_mul_adjT_of_residue hwv hd,
    by rw [hu]; exact WeakOrder.of_mul_adjT_le (descent_of_permLen_drop hlen),
    by rw [hu]; omega⟩

/-- **Everything below an object is realised, and climbed to it**: `exists_cover_of_lt` picks a
descent that stays above the foot and `exists_desc` realises it, so peeling covers until the length
runs out both finds the foot and spells the word up from it. -/
theorem exists_climb_of_le : ∀ (N : ℕ) {v : V}, permLen (W.perm v) ≤ N → ∀ {x : WeakOrder n},
    x ≤ WeakOrder.of (W.perm v) →
      ∃ u : V, W.perm u = WeakOrder.perm x ∧ Nonempty (Climb W.perm u v) := by
  intro N
  induction N with
  | zero =>
      intro v hN x h
      refine ⟨v, ?_, ⟨Climb.nil⟩⟩
      have h1 := WeakOrder.permLen_le_of_le h
      simp only [WeakOrder.perm_of] at h1
      rw [eq_one_of_permLen_eq_zero _ (by omega : permLen (W.perm v) = 0),
        eq_one_of_permLen_eq_zero _ (by omega : permLen (WeakOrder.perm x) = 0)]
  | succ N ih =>
      intro v hN x h
      by_cases hne : WeakOrder.perm x = W.perm v
      · exact ⟨v, hne.symm, ⟨Climb.nil⟩⟩
      · obtain ⟨k, hd, hcov⟩ := WeakOrder.exists_cover_of_lt h hne
        obtain ⟨b, hb⟩ := W.exists_desc v k hd
        have hlen := permLen_mul_adjT_of_descent hd
        obtain ⟨u, hu, ⟨R⟩⟩ := ih (v := b) (by rw [hb]; omega) (x := x) (by rw [hb]; exact hcov)
        exact ⟨u, hu, ⟨R.cons (W.descAsc hd hb)⟩⟩

/-- **The family is down-closed**: a permutation below one that is realised is realised. -/
theorem exists_of_le (N : ℕ) {v : V} (hN : permLen (W.perm v) ≤ N) {x : WeakOrder n}
    (h : x ≤ WeakOrder.of (W.perm v)) : ∃ u : V, W.perm u = WeakOrder.perm x :=
  (W.exists_climb_of_le N hN h).imp fun _ hu => hu.1

/-- **Everything below an object is climbed to it.** -/
theorem nonempty_climb' {w v : V} (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) :
    Nonempty (Climb W.perm w v) := by
  obtain ⟨u, hu, hR⟩ := W.exists_climb_of_le _ le_rfl h
  exact W.perm_inj (hu.trans (WeakOrder.perm_of _)) ▸ hR

end Descents

/-- Arrows along the adjacent ascents of a down-closed family of permutations. -/
structure Web (n : ℕ) (V : Type u) (C : Type*) [Category C] extends Descents n V where
  /-- The object an element carries. -/
  obj : V → C
  /-- The arrow an ascent names. -/
  arr {w v : V} : Ascent perm w v → (obj w ⟶ obj v)

namespace Web

variable {C : Type*} [Category C] (W : Web n V C)

/-- The arrow a climb composes to. -/
def ev (W : Web n V C) {w : V} : ∀ {v : V}, Climb W.perm w v → (W.obj w ⟶ W.obj v)
  | _, .nil => 𝟙 _
  | _, .cons R e => ev W R ≫ W.arr e

@[simp] theorem ev_nil {v : V} : W.ev (Climb.nil : Climb W.perm v v) = 𝟙 (W.obj v) := rfl

@[simp] theorem ev_cons {w b v : V} (R : Climb W.perm w b) (e : Ascent W.perm b v) :
    W.ev (R.cons e) = W.ev R ≫ W.arr e := rfl

/-- **Concatenating climbs composes their arrows.** -/
theorem ev_comp {w b : V} (R : Climb W.perm w b) : ∀ {v : V} (R' : Climb W.perm b v),
    W.ev (R.comp R') = W.ev R ≫ W.ev R'
  | _, .nil => (Category.comp_id _).symm
  | _, .cons R' e => by
      rw [Climb.comp_cons, W.ev_cons, W.ev_cons, ev_comp R R', Category.assoc]

/-- **Artin's relation, in one clause**: two ascents into an element out of *different* elements,
with a foot below both as far down as the **order of the pair they span**, are joined by two climbs
over that foot, and those name one arrow — the order being `2` for a commuting pair and `3` for a
braiding one, so the species never enters the statement. -/
def IsArtin : Prop :=
  ∀ {v b b' c : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v), b ≠ b' →
    WeakOrder.of (W.perm c) ≤ WeakOrder.of (W.perm b) →
    WeakOrder.of (W.perm c) ≤ WeakOrder.of (W.perm b') →
    permLen (W.perm v)
        = permLen (W.perm c) + orderOf ((W.perm b)⁻¹ * W.perm b') →
    ∃ (R : Climb W.perm c b) (R' : Climb W.perm c b'), W.ev (R.cons e) = W.ev (R'.cons e')

variable {W}

/-- **Matsumoto's theorem between distinct objects**, by induction on the top's crossing count: a
shared top ascent reduces, and two distinct ones are closed by `IsArtin`'s foot — which the weak
order puts above the climbs' own start, hence within reach of a climb. -/
theorem ev_eq_of_le (hW : W.IsArtin) : ∀ (N : ℕ) {w v : V}, permLen (W.perm v) ≤ N →
    ∀ (R R' : Climb W.perm w v), W.ev R = W.ev R' := by
  intro N
  induction N with
  | zero =>
      intro w v hN R R'
      cases R with
      | nil =>
          cases R' with
          | nil => rfl
          | cons R₀' e' => exact absurd e'.permLen_eq (by omega)
      | cons R₀ e => exact absurd e.permLen_eq (by omega)
  | succ N ih =>
      -- the ordered two-descent step; the symmetric one follows by swapping the two climbs
      have main : ∀ {w v b b' : V} (R₀ : Climb W.perm w b) (e : Ascent W.perm b v)
          (R₀' : Climb W.perm w b') (e' : Ascent W.perm b' v), permLen (W.perm v) ≤ N + 1 →
          (e.idx : ℕ) < (e'.idx : ℕ) → W.ev (R₀.cons e) = W.ev (R₀'.cons e') := by
        intro w v b b' R₀ e R₀' e' hN hlt
        have hdi := e.descent
        have hdj := e'.descent
        have hb := e.perm_eq'
        have hb' := e'.perm_eq'
        have hwb := R₀.le
        have hwb' := R₀'.le
        have hlb := e.permLen_eq
        have hlb' := e'.permLen_eq
        -- the residue `w⁻¹v` descends at both cuts, which is what makes the peels below `w`
        have dwi : ((W.perm w)⁻¹ * W.perm v) (adjHi e.idx)
            < ((W.perm w)⁻¹ * W.perm v) (adjLo e.idx) :=
          WeakOrder.residue_descent hdi (by rw [← hb]; exact hwb)
        have dwj : ((W.perm w)⁻¹ * W.perm v) (adjHi e'.idx)
            < ((W.perm w)⁻¹ * W.perm v) (adjLo e'.idx) :=
          WeakOrder.residue_descent hdj (by rw [← hb']; exact hwb')
        have hord : orderOf ((W.perm b)⁻¹ * W.perm b')
            = orderOf (adjT e.idx * adjT e'.idx) := congrArg orderOf (e.inv_mul e')
        obtain ⟨c, hcb, hcb', hwc, hlen⟩ : ∃ c : V,
            WeakOrder.of (W.perm c) ≤ WeakOrder.of (W.perm b) ∧
            WeakOrder.of (W.perm c) ≤ WeakOrder.of (W.perm b') ∧
            WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm c) ∧
            permLen (W.perm v)
              = permLen (W.perm c) + orderOf ((W.perm b)⁻¹ * W.perm b') := by
          rcases Nat.lt_or_ge ((e.idx : ℕ) + 1) ((e'.idx : ℕ)) with hfar | hnear
          · -- far apart: the square, one step below `b`
            obtain ⟨c, hc, hwc, hcb, hlc⟩ := W.exists_step (v := b) (k := e'.idx) hwb (by
              rw [hb]; simp only [← mul_assoc]
              exact descent_mul_adjT_of_far (by omega) (by omega) (by omega) dwj)
            refine ⟨c, hcb, ?_, hwc, ?_⟩
            · rw [show W.perm c = W.perm b' * adjT e.idx from by
                rw [hc, hb, hb', mul_adjT_comm _ hfar]]
              exact WeakOrder.of_mul_adjT_le (by
                rw [hb']; exact descent_mul_adjT_of_far (by omega) (by omega) (by omega) hdi)
            · rw [hord, orderOf_adjT_mul_adjT_of_apart (by omega) (Or.inl hfar)]; omega
          · -- consecutive: the hexagon, two steps below `b` — and two below `b'` to the same foot
            have hadj : (e'.idx : ℕ) = (e.idx : ℕ) + 1 := by omega
            obtain ⟨c₁, hc₁, hwc₁, hc₁b, hl₁⟩ := W.exists_step (v := b) (k := e'.idx) hwb (by
              rw [hb]; simp only [← mul_assoc]; exact descent_mul_adjT_braid₁ hadj dwi dwj)
            obtain ⟨c, hc, hwc, hcc₁, hlc⟩ := W.exists_step (v := c₁) (k := e.idx) hwc₁ (by
              rw [hc₁, hb]; simp only [← mul_assoc]; exact descent_mul_adjT_braid₂ hadj dwj)
            obtain ⟨c₂, hc₂, hwc₂, hc₂b', -⟩ := W.exists_step (v := b') (k := e.idx) hwb' (by
              rw [hb']; simp only [← mul_assoc]; exact descent_mul_adjT_braid₃ hadj dwi dwj)
            obtain ⟨c₃, hc₃, -, hc₃c₂, -⟩ := W.exists_step (v := c₂) (k := e'.idx) hwc₂ (by
              rw [hc₂, hb']; simp only [← mul_assoc]; exact descent_mul_adjT_braid₄ hadj dwi)
            obtain rfl : c₃ = c := W.perm_inj (by
              rw [hc₃, hc₂, hb', hc, hc₁, hb]; exact (mul_adjT_braid _ hadj).symm)
            refine ⟨c₃, hcc₁.trans hc₁b, hc₃c₂.trans hc₂b', hwc, ?_⟩
            rw [hord, orderOf_adjT_mul_adjT_of_adj (by omega) (Or.inl hadj)]; omega
        obtain ⟨R, R', heq⟩ :=
          hW e e' ((e.idx_ne_iff W.perm_inj e').mp (by omega)) hcb hcb' hlen
        obtain ⟨P⟩ := W.nonempty_climb' hwc
        rw [W.ev_cons, W.ev_cons, ih (by omega) R₀ (P.comp R), ih (by omega) R₀' (P.comp R'),
          W.ev_comp, W.ev_comp, Category.assoc, Category.assoc]
        exact congrArg (fun t => W.ev P ≫ t) heq
      intro w v hN R R'
      cases R with
      | nil =>
          cases R' with
          | nil => rfl
          | cons R₀' e' => exact absurd R₀'.permLen_le (by have := e'.permLen_eq; omega)
      | cons R₀ e =>
          cases R' with
          | nil => exact absurd R₀.permLen_le (by have := e.permLen_eq; omega)
          | cons R₀' e' =>
              rcases lt_trichotomy (e.idx : ℕ) (e'.idx : ℕ) with hlt | heq | hgt
              · exact main R₀ e R₀' e' hN hlt
              · have hidx : e.idx = e'.idx := Fin.ext heq
                obtain rfl : _ = _ :=
                  W.perm_inj (e.perm_eq'.trans (by rw [hidx]; exact e'.perm_eq'.symm))
                obtain rfl : e = e' := Ascent.eq_of_idx hidx
                have := e.permLen_eq
                rw [W.ev_cons, W.ev_cons, ih (by omega) R₀ R₀']
              · exact (main R₀' e' R₀ e hN hgt).symm

/-- **Matsumoto's theorem between distinct objects**: two climbs with the same ends name one
arrow. -/
theorem ev_eq (hW : W.IsArtin) {w v : V} (R R' : Climb W.perm w v) : W.ev R = W.ev R' :=
  ev_eq_of_le hW _ le_rfl R R'

/-! ## The arrow of a comparison

With uniqueness in hand a climb need not be named: the weak order alone gives the arrow, and it
composes with an ascent on the right.
-/

/-- The arrow from `w` up to `v` that any climb spells — well defined only under `IsArtin`, which
every theorem about it carries. -/
noncomputable def arrow (W : Web n V C) {w v : V}
    (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) : W.obj w ⟶ W.obj v :=
  W.ev (W.nonempty_climb' h).some

theorem ev_eq_arrow (hW : W.IsArtin) {w v : V} (R : Climb W.perm w v) :
    W.ev R = W.arrow R.le := ev_eq hW _ _

@[simp] theorem arrow_refl (hW : W.IsArtin) {v : V}
    (h : WeakOrder.of (W.perm v) ≤ WeakOrder.of (W.perm v)) : W.arrow h = 𝟙 (W.obj v) :=
  (ev_eq_arrow hW (Climb.nil : Climb W.perm v v)).symm

/-- **The arrows compose** — concatenating two climbs. -/
theorem arrow_comp (hW : W.IsArtin) {w b v : V}
    (h₁ : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b))
    (h₂ : WeakOrder.of (W.perm b) ≤ WeakOrder.of (W.perm v)) :
    W.arrow h₁ ≫ W.arrow h₂ = W.arrow (h₁.trans h₂) := by
  obtain ⟨R₁⟩ := W.nonempty_climb' h₁
  obtain ⟨R₂⟩ := W.nonempty_climb' h₂
  rw [← ev_eq_arrow hW R₁, ← ev_eq_arrow hW R₂, ← W.ev_comp R₁ R₂]
  exact ev_eq_arrow hW (R₁.comp R₂)

end Web

end CubeChains
