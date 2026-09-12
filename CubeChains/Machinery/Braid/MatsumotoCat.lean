import CubeChains.Machinery.Braid.WeakOrder
import Mathlib.CategoryTheory.Category.Basic

/-!
# Machinery/Braid/MatsumotoCat — Matsumoto between distinct objects

`Machinery/Braid/Matsumoto` lifts an Artin family into a *monoid*, where every generator is a loop.
Here one object carries each permutation of a set closed under peeling descents, and an adjacent
ascent is an arrow between two of them, so a reduced word is a **climb** and there is nothing to
multiply.  Artin's two relations — the square at far-apart indices, the hexagon at consecutive ones
— then make any two climbs with the same ends name one arrow.

Local confluence is the two-descent dichotomy, as in the monoid.  What replaces the monoid's base
point is the weak order: the square's, resp. the hexagon's, far end stays above the climb's foot, so
it is climbed to (`le_mul_adjT_mul_adjT`, `le_mul_adjT_braid`, `exists_cover_of_lt`).
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

/-- Climbs concatenate. -/
def comp {w b : V} (R : Climb p w b) : ∀ {v : V}, Climb p b v → Climb p w v
  | _, .nil => R
  | _, .cons R' e => (R.comp R').cons e

@[simp] theorem comp_nil {w b : V} (R : Climb p w b) : R.comp (.nil : Climb p b b) = R := rfl

@[simp] theorem comp_cons {w b c v : V} (R : Climb p w b) (R' : Climb p b c)
    (e : Ascent p c v) : R.comp (R'.cons e) = (R.comp R').cons e := rfl

end Climb

/-! ## An Artin web

The data a climb can be evaluated on: an object per element of `V`, an arrow per ascent, and
Artin's two relations among them.  `perm_inj` and `exists_desc` are what make the index set a
down-closed set of permutations — the hypothesis Matsumoto is stated under, and they are already
enough for every climb to exist (`Descents.nonempty_climb`).
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

/-- Arrows along the adjacent ascents of a down-closed family of permutations, satisfying Artin's
two relations. -/
structure ArtinWeb (n : ℕ) (V : Type u) (C : Type*) [Category C] extends Descents n V where
  /-- The object an element carries. -/
  obj : V → C
  /-- The arrow an ascent names. -/
  arr {w v : V} : Ascent perm w v → (obj w ⟶ obj v)
  /-- **The square at far-apart indices.** -/
  comm {v vi vj c : V} (a : Ascent perm vi v) (b : Ascent perm c vi) (a' : Ascent perm vj v)
    (b' : Ascent perm c vj) (hij : (a.idx : ℕ) + 1 < (a'.idx : ℕ))
    (hb : (b.idx : ℕ) = (a'.idx : ℕ)) (hb' : (b'.idx : ℕ) = (a.idx : ℕ)) :
    arr b ≫ arr a = arr b' ≫ arr a'
  /-- **The hexagon at consecutive indices.** -/
  braid {v vi vj vij vji c : V} (a₁ : Ascent perm vi v) (a₂ : Ascent perm vij vi)
    (a₃ : Ascent perm c vij) (b₁ : Ascent perm vj v) (b₂ : Ascent perm vji vj)
    (b₃ : Ascent perm c vji) (hij : (b₁.idx : ℕ) = (a₁.idx : ℕ) + 1)
    (h₂ : (a₂.idx : ℕ) = (b₁.idx : ℕ)) (h₃ : (a₃.idx : ℕ) = (a₁.idx : ℕ))
    (h₂' : (b₂.idx : ℕ) = (a₁.idx : ℕ)) (h₃' : (b₃.idx : ℕ) = (b₁.idx : ℕ)) :
    arr a₃ ≫ arr a₂ ≫ arr a₁ = arr b₃ ≫ arr b₂ ≫ arr b₁

namespace Descents

variable (W : Descents n V)

/-- The ascent a descent of `perm v` names, once its peel is realised. -/
def descAsc {v w : V} {k : Fin (n - 1)} (hd : W.perm v (adjHi k) < W.perm v (adjLo k))
    (hw : W.perm w = W.perm v * adjT k) : Ascent W.perm w v where
  idx := k
  asc := by rw [hw]; exact adjT_ascent_of_descent hd
  perm_eq := by rw [hw, mul_adjT_adjT]

@[simp] theorem descAsc_idx {v w : V} {k : Fin (n - 1)}
    (hd : W.perm v (adjHi k) < W.perm v (adjLo k)) (hw : W.perm w = W.perm v * adjT k) :
    (W.descAsc hd hw).idx = k := rfl

/-- **Everything below an object is climbed to it**: `exists_cover_of_lt` picks a descent that stays
above the foot and `exists_desc` realises it. -/
theorem nonempty_climb : ∀ (N : ℕ) {w v : V}, permLen (W.perm v) ≤ N →
    WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v) → Nonempty (Climb W.perm w v) := by
  intro N
  induction N with
  | zero =>
      intro w v hN h
      obtain rfl : w = v := W.perm_inj (by
        have h1 := WeakOrder.permLen_le_of_le h
        simp only [WeakOrder.perm_of] at h1
        rw [eq_one_of_permLen_eq_zero _ (by omega : permLen (W.perm w) = 0),
          eq_one_of_permLen_eq_zero _ (by omega : permLen (W.perm v) = 0)])
      exact ⟨Climb.nil⟩
  | succ N ih =>
      intro w v hN h
      by_cases hne : W.perm w = W.perm v
      · obtain rfl : w = v := W.perm_inj hne
        exact ⟨Climb.nil⟩
      · obtain ⟨k, hd, hcov⟩ := WeakOrder.exists_cover_of_lt h hne
        obtain ⟨b, hb⟩ := W.exists_desc v k hd
        have hlen := permLen_mul_adjT_of_descent hd
        obtain ⟨R⟩ := ih (w := w) (v := b) (by rw [hb]; omega) (by rw [hb]; exact hcov)
        exact ⟨R.cons (W.descAsc hd hb)⟩

/-- **Everything below an object is climbed to it.** -/
theorem nonempty_climb' {w v : V} (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) :
    Nonempty (Climb W.perm w v) := W.nonempty_climb _ le_rfl h

/-- **A climb of one step is a single ascent** — the intermediate object is the foot, by gradedness
of the weak order. -/
theorem eq_cons_nil {w v : V} (R : Climb W.perm w v)
    (hlen : permLen (W.perm v) = permLen (W.perm w) + 1) :
    ∃ e : Ascent W.perm w v, R = Climb.nil.cons e := by
  cases R with
  | nil => exact absurd hlen (by omega)
  | cons R₀ e =>
      rename_i b
      have he := e.permLen_eq
      have hb : permLen (WeakOrder.perm (WeakOrder.of (W.perm w)))
          = permLen (WeakOrder.perm (WeakOrder.of (W.perm b))) := by
        simp only [WeakOrder.perm_of]; omega
      obtain rfl := W.perm_inj (WeakOrder.eq_of_le_of_permLen_eq R₀.le hb)
      cases R₀ with
      | nil => exact ⟨e, rfl⟩
      | cons R₁ e' => exact absurd R₁.permLen_le (by have := e'.permLen_eq; omega)

end Descents

namespace ArtinWeb

variable {C : Type*} [Category C] (W : ArtinWeb n V C)

/-- The arrow a climb composes to. -/
def ev (W : ArtinWeb n V C) {w : V} : ∀ {v : V}, Climb W.perm w v → (W.obj w ⟶ W.obj v)
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

/-- **A one-step climb is the ascent it crosses.** -/
theorem ev_eq_arr {w v : V} (R : Climb W.perm w v) (e : Ascent W.perm w v)
    (hlen : permLen (W.perm v) = permLen (W.perm w) + 1) : W.ev R = W.arr e := by
  obtain ⟨e', rfl⟩ := W.toDescents.eq_cons_nil R hlen
  obtain rfl : e' = e := Ascent.eq_of_idx
    (adjT_injective (mul_left_cancel (a := W.perm w) (e'.perm_eq.symm.trans e.perm_eq)))
  exact Category.id_comp _

/-- **Matsumoto's theorem between distinct objects**, by induction on the top's crossing count: a
shared top ascent reduces, and two distinct ones are closed by the square or the hexagon — whose far
end the weak order puts above the foot, hence within reach of a climb. -/
theorem ev_eq_of_le : ∀ (N : ℕ) {w v : V}, permLen (W.perm v) ≤ N →
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
        have hlb : permLen (W.perm b) + 1 = permLen (W.perm v) := by
          rw [hb]; exact (permLen_mul_adjT_of_descent hdi).symm
        have hlb' : permLen (W.perm b') + 1 = permLen (W.perm v) := by
          rw [hb']; exact (permLen_mul_adjT_of_descent hdj).symm
        rcases Nat.lt_or_ge ((e.idx : ℕ) + 1) ((e'.idx : ℕ)) with hfar | hnear
        · -- far apart: the square
          have dj : W.perm b (adjHi e'.idx) < W.perm b (adjLo e'.idx) := by
            rw [hb]; exact descent_mul_adjT_of_far (by omega) (by omega) (by omega) hdj
          have di : W.perm b' (adjHi e.idx) < W.perm b' (adjLo e.idx) := by
            rw [hb']; exact descent_mul_adjT_of_far (by omega) (by omega) (by omega) hdi
          obtain ⟨c, hc⟩ := W.exists_desc b e'.idx dj
          have hcv : W.perm c = W.perm v * adjT e.idx * adjT e'.idx := by rw [hc, hb]
          have hc' : W.perm c = W.perm b' * adjT e.idx := by
            rw [hcv, hb', mul_adjT_comm _ hfar]
          have hwc : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm c) := by
            rw [hcv]
            exact WeakOrder.le_mul_adjT_mul_adjT hfar hdi hdj (by rw [← hb]; exact hwb)
              (by rw [← hb']; exact hwb')
          obtain ⟨P⟩ := W.nonempty_climb' hwc
          rw [W.ev_cons, W.ev_cons, ih (by omega) R₀ (P.cons (W.descAsc dj hc)),
            ih (by omega) R₀' (P.cons (W.descAsc di hc')), W.ev_cons, W.ev_cons,
            Category.assoc, Category.assoc]
          exact congrArg (fun t => W.ev P ≫ t)
            (W.comm e (W.descAsc dj hc) e' (W.descAsc di hc') hfar rfl rfl)
        · -- consecutive: the hexagon
          have hadj : (e'.idx : ℕ) = (e.idx : ℕ) + 1 := by omega
          have dj : W.perm b (adjHi e'.idx) < W.perm b (adjLo e'.idx) := by
            rw [hb]; exact descent_mul_adjT_braid₁ hadj hdi hdj
          obtain ⟨c₁, hc₁⟩ := W.exists_desc b e'.idx dj
          have hc₁v : W.perm c₁ = W.perm v * adjT e.idx * adjT e'.idx := by rw [hc₁, hb]
          have di₁ : W.perm c₁ (adjHi e.idx) < W.perm c₁ (adjLo e.idx) := by
            rw [hc₁v]; exact descent_mul_adjT_braid₂ hadj hdj
          obtain ⟨c, hc⟩ := W.exists_desc c₁ e.idx di₁
          have hcv : W.perm c = W.perm v * adjT e.idx * adjT e'.idx * adjT e.idx := by
            rw [hc, hc₁v]
          have di' : W.perm b' (adjHi e.idx) < W.perm b' (adjLo e.idx) := by
            rw [hb']; exact descent_mul_adjT_braid₃ hadj hdi hdj
          obtain ⟨c₂, hc₂⟩ := W.exists_desc b' e.idx di'
          have hc₂v : W.perm c₂ = W.perm v * adjT e'.idx * adjT e.idx := by rw [hc₂, hb']
          have dj₂ : W.perm c₂ (adjHi e'.idx) < W.perm c₂ (adjLo e'.idx) := by
            rw [hc₂v]; exact descent_mul_adjT_braid₄ hadj hdi
          have hcc₂ : W.perm c = W.perm c₂ * adjT e'.idx := by
            rw [hcv, hc₂v, mul_adjT_braid _ hadj]
          have hwc : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm c) := by
            rw [hcv]
            exact WeakOrder.le_mul_adjT_braid hadj hdi hdj (by rw [← hb]; exact hwb)
              (by rw [← hb']; exact hwb')
          obtain ⟨P⟩ := W.nonempty_climb' hwc
          rw [W.ev_cons, W.ev_cons,
            ih (by omega) R₀ ((P.cons (W.descAsc di₁ hc)).cons (W.descAsc dj hc₁)),
            ih (by omega) R₀' ((P.cons (W.descAsc dj₂ hcc₂)).cons (W.descAsc di' hc₂))]
          simp only [W.ev_cons, Category.assoc]
          exact congrArg (fun t => W.ev P ≫ t)
            (W.braid e (W.descAsc dj hc₁) (W.descAsc di₁ hc) e' (W.descAsc di' hc₂)
              (W.descAsc dj₂ hcc₂) hadj rfl rfl rfl rfl)
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
theorem ev_eq {w v : V} (R R' : Climb W.perm w v) : W.ev R = W.ev R' :=
  W.ev_eq_of_le _ le_rfl R R'

/-! ## The arrow of a comparison

With uniqueness in hand a climb need not be named: the weak order alone gives the arrow, and it
composes with an ascent on the right.
-/

/-- The arrow from `w` up to `v` that any climb spells. -/
noncomputable def arrow {w v : V} (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) :
    W.obj w ⟶ W.obj v := W.ev (W.nonempty_climb' h).some

theorem ev_eq_arrow {w v : V} (R : Climb W.perm w v) : W.ev R = W.arrow R.le := W.ev_eq _ _

@[simp] theorem arrow_refl {v : V} (h : WeakOrder.of (W.perm v) ≤ WeakOrder.of (W.perm v)) :
    W.arrow h = 𝟙 (W.obj v) :=
  (W.ev_eq_arrow (Climb.nil : Climb W.perm v v)).symm

/-- **The arrows compose** — concatenating two climbs. -/
theorem arrow_comp {w b v : V} (h₁ : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b))
    (h₂ : WeakOrder.of (W.perm b) ≤ WeakOrder.of (W.perm v)) :
    W.arrow h₁ ≫ W.arrow h₂ = W.arrow (h₁.trans h₂) := by
  obtain ⟨R₁⟩ := W.toDescents.nonempty_climb' h₁
  obtain ⟨R₂⟩ := W.toDescents.nonempty_climb' h₂
  rw [← W.ev_eq_arrow R₁, ← W.ev_eq_arrow R₂, ← W.ev_comp R₁ R₂]
  exact W.ev_eq_arrow (R₁.comp R₂)

/-- **An ascent appends to the arrow below it.** -/
theorem arrow_ascent {w b v : V} (e : Ascent W.perm b v)
    (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b)) :
    W.arrow (h.trans e.le) = W.arrow h ≫ W.arr e := by
  obtain ⟨R⟩ := W.nonempty_climb' h
  rw [← W.ev_eq_arrow (R.cons e), ← W.ev_eq_arrow R, W.ev_cons]

end ArtinWeb

end CubeChains
