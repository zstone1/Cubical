import CubeChains.Machinery.Braid.RankTwo
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Machinery/Braid/MatsumotoCat — Matsumoto between distinct objects

The index set is a **lower set of the right weak order on `Sₙ`** (`WeakOrder.Lower`), one object per
element, and the covers quiver it (`Ascents`), so a reduced word is a **path** and a web is a
prefunctor out of it.  `Web.IsArtin` — the two covers below an element are joined over the foot of
the polygon they span — then extends that labelling to a functor on the poset, uniquely.

    w ──▸ foot ──▸ b ──e──▸ v     `Machinery/Braid/RankTwo` supplies the foot and the two
             └────▸ b' ─e'─▸ v     walks down to it; nothing here sees the pair's species.
-/

namespace CubeChains

open CategoryTheory Equiv

universe u

variable {n : ℕ} {V : Type u} {p : V → Perm (Fin n)}

/-! ## Covers and climbs -/

/-- A cover of the right weak order, pulled back along `p` and labelled by the pair it crosses:
`p v` crosses `idx`, which `p w` has not. -/
structure Ascent (p : V → Perm (Fin n)) (w v : V) where
  /-- Which pair the ascent crosses. -/
  idx : Fin (n - 1)
  /-- `p w` has not crossed it. -/
  asc : p w (adjLo idx) < p w (adjHi idx)
  /-- …and `p v` is `p w` with it crossed. -/
  perm_eq : p v = p w * adjT idx

/-- **An ascent is pinned by its two ends** — cancelling `p w` in `perm_eq` leaves the crossing,
which names the index (`adjT_injective`).  No hypothesis on `p`. -/
instance Ascent.instSubsingleton {w v : V} : Subsingleton (Ascent p w v) :=
  ⟨fun ⟨_, _, hi⟩ ⟨_, _, hj⟩ => by
    obtain rfl := adjT_injective (mul_left_cancel (hi.symm.trans hj))
    rfl⟩

/-- …and read at the top, the pair is a descent. -/
theorem Ascent.descent {w v : V} (e : Ascent p w v) : p v (adjHi e.idx) < p v (adjLo e.idx) := by
  rw [e.perm_eq, Perm.mul_apply, Perm.mul_apply, adjT_lo, adjT_hi]
  exact e.asc

/-- …so the ascent reads backwards as a peel. -/
theorem Ascent.perm_eq' {w v : V} (e : Ascent p w v) : p w = p v * adjT e.idx := by
  rw [e.perm_eq, mul_adjT_adjT]

/-- The ascent a peeled descent names. -/
def Ascent.ofPeel {w v : V} {k : Fin (n - 1)} (hd : p v (adjHi k) < p v (adjLo k))
    (hw : p w = p v * adjT k) : Ascent p w v where
  idx := k
  asc := by rw [hw]; exact adjT_ascent_of_descent hd
  perm_eq := by rw [hw, mul_adjT_adjT]

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
    exact h (congrArg (fun f : Ascent p b v => (f.idx : ℕ)) (Subsingleton.elim e e'))
  · rw [e.perm_eq', e'.perm_eq', Fin.ext hc]

theorem Ascent.le {w v : V} (e : Ascent p w v) : WeakOrder.of (p w) ≤ WeakOrder.of (p v) := by
  rw [e.perm_eq']
  exact WeakOrder.of_mul_adjT_le e.descent

/-- `V`, quivered by the adjacent ascents of `p`. -/
def Ascents (_p : V → Perm (Fin n)) : Type u := V

instance : Quiver.{0} (Ascents p) := ⟨Ascent p⟩

/-- **The label is no data**, so the quiver is thin and a climb is the sequence of elements it
passes through. -/
instance : Quiver.IsThin (Ascents p) := fun _ _ => Ascent.instSubsingleton

/-- **`Ascents p` is the Hasse diagram of the right weak order, pulled back along `p`.** -/
theorem nonempty_ascent_iff {w v : V} :
    Nonempty (Ascent p w v) ↔ WeakOrder.of (p w) ⋖ WeakOrder.of (p v) :=
  ⟨fun ⟨e⟩ => WeakOrder.covBy_iff.mpr ⟨e.idx, e.descent, e.perm_eq'⟩,
    fun h => match WeakOrder.covBy_iff.mp h with
      | ⟨_, hd, hw⟩ => ⟨Ascent.ofPeel hd hw⟩⟩

/-- A saturated chain of the weak order — a reduced word, climbing from `w` to `v`. -/
abbrev Climb (p : V → Perm (Fin n)) (w v : V) : Type u := Quiver.Path (V := Ascents p) w v

namespace Climb

theorem le {w v : V} (R : Climb p w v) : WeakOrder.of (p w) ≤ WeakOrder.of (p v) := by
  induction R with
  | nil => exact le_refl _
  | cons R e ih => exact ih.trans (Ascent.le e)

/-- **A climb crosses once per letter** — so its length is a function of its two ends, and any
count of its letters is this. -/
theorem permLen_eq {w : V} : ∀ {v : V} (R : Climb p w v),
    permLen (p v) = permLen (p w) + R.length
  | _, .nil => rfl
  | _, .cons R e => e.permLen_eq.trans (congrArg (· + 1) (permLen_eq R))

/-- A climb never shortens — which is what rules out a climb against an ascent. -/
theorem permLen_le {w v : V} (R : Climb p w v) : permLen (p w) ≤ permLen (p v) := by
  have := permLen_eq R; omega

/-- **A climb that returns to its start is trivial** — every ascent raises the length, and a climb
never shortens. -/
theorem eq_nil {w : V} (R : Climb p w w) : R = Quiver.Path.nil :=
  Quiver.Path.eq_nil_of_length_zero R (by have := permLen_eq R; omega)

/-- **A climb that raises the length by one is a single ascent** — so it is pinned by its two ends,
even when the climb itself was chosen.  This is what makes a length-one word canonical. -/
theorem eq_start_of_permLen_eq (hp : Function.Injective p) {w b : V} (R : Climb p w b)
    (h : permLen (p b) = permLen (p w)) : w = b :=
  hp (WeakOrder.eq_of_le_of_permLen_eq (le R) h.symm)

theorem eq_cons_nil (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 1) :
    ∃ e : Ascent p w v, R = Quiver.Path.nil.cons e := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain rfl := eq_start_of_permLen_eq hp R (by have := e.permLen_eq; omega)
      exact ⟨e, congrArg (fun S : Climb p w w => S.cons e) (eq_nil R)⟩

/-- **A climb of length two is two ascents** — through the middle the climb itself names, which is
not forced by the two ends. -/
theorem eq_cons_cons (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 2) :
    ∃ (b : V) (f₁ : Ascent p w b) (f₂ : Ascent p b v),
      R = (Quiver.Path.nil.cons f₁).cons f₂ := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain ⟨f₁, rfl⟩ := eq_cons_nil hp R (by have := e.permLen_eq; omega)
      exact ⟨_, f₁, e, rfl⟩

end Climb

/-! ## A lower set in the right weak order

The index set Matsumoto is stated over.  `V` is not literally a set of permutations — the runs over
a chain are a subtype of one — so it comes with the injection naming which permutation each element
performs, and the hypothesis is on that injection's range.
-/

namespace WeakOrder

/-- **A lower set in the right weak order on `Sₙ`**, indexed faithfully by `V`. -/
structure Lower (n : ℕ) (V : Type u) where
  /-- The permutation an element performs. -/
  perm : V → Perm (Fin n)
  /-- An element is pinned by its permutation. -/
  perm_inj : Function.Injective perm
  /-- …and the permutations performed are closed downwards. -/
  isLowerSet : IsLowerSet (Set.range fun v => of (perm v))

namespace Lower

variable (W : Lower n V)

/-- **Everything below something performed is performed** — the lower set, read at its elements. -/
theorem exists_of_le {v : V} {x : WeakOrder n} (h : x ≤ WeakOrder.of (W.perm v)) :
    ∃ u : V, WeakOrder.of (W.perm u) = x :=
  W.isLowerSet h ⟨v, rfl⟩

/-- …read as an element rather than as a range condition. -/
theorem exists_perm_eq {v : V} {x : Equiv.Perm (Fin n)}
    (h : WeakOrder.of x ≤ WeakOrder.of (W.perm v)) : ∃ u : V, W.perm u = x :=
  W.exists_of_le h

/-- **The element performing a permutation the lower set reaches** — pinned by `perm_inj`, so
naming it is no choice: two calls at the same permutation are the same element. -/
noncomputable def elemOf {x : Equiv.Perm (Fin n)} (h : ∃ u : V, W.perm u = x) : V := h.choose

@[simp] theorem perm_elemOf {x : Equiv.Perm (Fin n)} (h : ∃ u : V, W.perm u = x) :
    W.perm (W.elemOf h) = x := h.choose_spec

/-- **Everything below an element is climbed to it**: `exists_cover_of_lt` picks a cover that stays
above the foot, and the lower set performs it, so peeling until the length runs out spells the word
up from the foot. -/
theorem nonempty_climb {w v : V} (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) :
    Nonempty (Climb W.perm w v) := by
  have key : ∀ (N : ℕ) {w v : V}, permLen (W.perm v) ≤ N →
      WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v) → Nonempty (Climb W.perm w v) := by
    intro N
    induction N with
    | zero =>
        intro w v hN h
        have hle := WeakOrder.permLen_le_of_le h
        simp only [WeakOrder.perm_of] at hle
        have hlen : permLen (W.perm w) = permLen (W.perm v) := by omega
        obtain rfl := W.perm_inj (WeakOrder.eq_of_le_of_permLen_eq h hlen)
        exact ⟨Quiver.Path.nil⟩
    | succ N ih =>
        intro w v hN h
        by_cases hne : W.perm w = W.perm v
        · obtain rfl := W.perm_inj hne
          exact ⟨Quiver.Path.nil⟩
        · obtain ⟨k, hd, hcov⟩ := WeakOrder.exists_cover_of_lt h hne
          obtain ⟨b, hb⟩ := W.exists_of_le (WeakOrder.of_mul_adjT_le hd)
          have hb' : W.perm b = W.perm v * adjT k := hb
          have hlen : permLen (W.perm v) = permLen (W.perm v * adjT k) + 1 :=
            permLen_mul_adjT_of_descent hd
          obtain ⟨R⟩ := ih (w := w) (v := b) (by rw [hb']; omega) (by rw [hb']; exact hcov)
          exact ⟨R.cons (Ascent.ofPeel hd hb')⟩
  exact key _ le_rfl h

/-- `V`, ordered by the weak order it indexes — the poset a web is a functor out of. -/
def Poset (_W : Lower n V) : Type u := V

instance : PartialOrder W.Poset :=
  PartialOrder.lift (β := WeakOrder n) (fun v => WeakOrder.of (W.perm v)) W.perm_inj

variable {W}

theorem Poset.le_iff {w v : W.Poset} :
    w ≤ v ↔ WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v) := Iff.rfl

end Lower

end WeakOrder

/-! ## A web of covers

The data a climb is evaluated on: a prefunctor out of the Hasse quiver of a lower set. -/

/-- A labelling of the Hasse diagram of a lower set of the right weak order: an object per element
and an arrow per cover. -/
structure Web (n : ℕ) (V : Type u) (C : Type*) [Category C] extends WeakOrder.Lower n V where
  /-- The object an element carries, and the arrow a cover names. -/
  pre : Ascents perm ⥤q C

namespace Web

variable {C : Type*} [Category C] (W : Web n V C)

/-- The arrow a climb composes to — the free category on the covers, evaluated. -/
abbrev eval (W : Web n V C) : Paths (Ascents W.perm) ⥤ C := Paths.lift W.pre

/-! ### The polygon two covers span

`Machinery/Braid/RankTwo` names the foot as a permutation; the lower set performs it, and
`perm_inj` makes the element it performs it at no choice at all. -/

variable {v b b' : V}

theorem idx_ne (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    ((e.idx : ℕ) ≠ (e'.idx : ℕ)) := (e.idx_ne_iff W.perm_inj e').mpr h

/-- **The foot of the polygon two covers span** — both crossings undone, and everything they
force. -/
noncomputable def foot (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') : V :=
  W.elemOf (W.exists_perm_eq (polyFoot_le (idx_ne W e e' h) e.descent e'.descent))

@[simp] theorem perm_foot (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    W.perm (W.foot e e' h) = polyFoot (W.perm v) e.idx e'.idx := W.perm_elemOf _

theorem foot_le_left (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    WeakOrder.of (W.perm (W.foot e e' h)) ≤ WeakOrder.of (W.perm b) := by
  rw [perm_foot, e.perm_eq']
  exact polyFoot_le_mul_adjT (idx_ne W e e' h) e.descent e'.descent

theorem foot_le_right (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    WeakOrder.of (W.perm (W.foot e e' h)) ≤ WeakOrder.of (W.perm b') := by
  rw [perm_foot, polyFoot_comm (idx_ne W e e' h), e'.perm_eq']
  exact polyFoot_le_mul_adjT (Ne.symm (idx_ne W e e' h)) e'.descent e.descent

/-- **The foot is reached from below**: anything under both covers is under it, which is what makes
the induction on the crossing count close. -/
theorem le_foot {w : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b')
    (hb : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b))
    (hb' : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b')) :
    WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm (W.foot e e' h)) := by
  rw [perm_foot]
  refine le_polyFoot (idx_ne W e e' h) (hb.trans e.le) ?_ ?_
  · exact WeakOrder.residue_descent e.descent (by rw [← e.perm_eq']; exact hb)
  · exact WeakOrder.residue_descent e'.descent (by rw [← e'.perm_eq']; exact hb')

/-- **Artin's relation, in one clause**: two covers below an element with *different* elements
underneath are joined over the foot of the polygon they span, and the two climbs up from it name one
arrow.  No species, no length equation: `RankTwo` has already absorbed the Coxeter exponent. -/
def IsArtin : Prop :=
  ∀ {v b b' : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b'),
    ∃ (R : Climb W.perm (W.foot e e' h) b) (R' : Climb W.perm (W.foot e e' h) b'),
      W.eval.map (R.cons e) = W.eval.map (R'.cons e')

/-- **…supplied at a named foot**: the foot is pinned by the permutation it performs, so a supplier
may work with any element performing it. -/
theorem isArtin_of_climbs
    (H : ∀ {v b b' : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v), b ≠ b' →
      ∀ c : V, W.perm c = polyFoot (W.perm v) e.idx e'.idx →
        ∃ (R : Climb W.perm c b) (R' : Climb W.perm c b'),
          W.eval.map (R.cons e) = W.eval.map (R'.cons e')) : W.IsArtin :=
  fun e e' h => H e e' h _ (W.perm_foot e e' h)

variable {W}

/-- **Matsumoto's theorem between distinct objects**, by induction on the top's crossing count: a
shared top cover strips off, and two distinct ones are closed at the polygon's foot — which
`le_foot` puts above the climbs' own start, hence within reach of a climb. -/
theorem eval_eq_of_le (hW : W.IsArtin) : ∀ (N : ℕ) {w v : V}, permLen (W.perm v) ≤ N →
    ∀ (R R' : Climb W.perm w v), W.eval.map R = W.eval.map R' := by
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
      intro w v hN R R'
      cases R with
      | nil =>
          cases R' with
          | nil => rfl
          | cons R₀' e' =>
              exact absurd (Climb.permLen_le R₀') (by have := e'.permLen_eq; omega)
      | cons R₀ e =>
          cases R' with
          | nil => exact absurd (Climb.permLen_le R₀) (by have := e.permLen_eq; omega)
          | cons R₀' e' =>
              have hlb := e.permLen_eq
              have hlb' := e'.permLen_eq
              by_cases hbb : (e.idx : ℕ) = (e'.idx : ℕ)
              · obtain rfl : _ = _ :=
                  W.perm_inj (e.perm_eq'.trans (by rw [Fin.ext hbb]; exact e'.perm_eq'.symm))
                obtain rfl : e = e' := Ascent.instSubsingleton.allEq e e'
                exact congrArg (fun t => t ≫ W.pre.map e) (ih (by omega) R₀ R₀')
              · have hne := (e.idx_ne_iff W.perm_inj e').mp hbb
                obtain ⟨S, S', heq⟩ := hW e e' hne
                obtain ⟨P⟩ := W.nonempty_climb (le_foot W e e' hne (Climb.le R₀) (Climb.le R₀'))
                change W.eval.map R₀ ≫ W.pre.map e = W.eval.map R₀' ≫ W.pre.map e'
                rw [ih (by omega) R₀ (P.comp S), ih (by omega) R₀' (P.comp S'),
                  show W.eval.map (P.comp S) = W.eval.map P ≫ W.eval.map S from
                    W.eval.map_comp P S,
                  show W.eval.map (P.comp S') = W.eval.map P ≫ W.eval.map S' from
                    W.eval.map_comp P S',
                  Category.assoc, Category.assoc]
                exact congrArg (fun t => W.eval.map P ≫ t) heq

/-- **Matsumoto's theorem between distinct objects**: two climbs with the same ends name one
arrow. -/
theorem eval_eq (hW : W.IsArtin) {w v : V} (R R' : Climb W.perm w v) :
    W.eval.map R = W.eval.map R' :=
  eval_eq_of_le hW _ le_rfl R R'

/-! ## The functor the labelling extends to

With uniqueness in hand a climb need not be named: the order alone gives the arrow, so the web is a
functor out of the poset, and the only one restricting to the labelling.
-/

/-- The arrow from `w` up to `v` that any climb spells — well defined only under `IsArtin`, which
every theorem about it carries. -/
noncomputable def arrow (W : Web n V C) {w v : V}
    (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) : W.pre.obj w ⟶ W.pre.obj v :=
  W.eval.map (W.nonempty_climb h).some

theorem eval_eq_arrow (hW : W.IsArtin) {w v : V} (R : Climb W.perm w v) :
    W.eval.map R = W.arrow (Climb.le R) := eval_eq hW _ _

/-- **A climb that returns to its start spells nothing**, so this one needs no hypothesis. -/
@[simp] theorem arrow_refl {v : V}
    (h : WeakOrder.of (W.perm v) ≤ WeakOrder.of (W.perm v)) : W.arrow h = 𝟙 (W.pre.obj v) := by
  rw [arrow, Climb.eq_nil (W.nonempty_climb h).some]
  exact W.eval.map_id v

/-- **The arrows compose** — concatenating two climbs. -/
theorem arrow_comp (hW : W.IsArtin) {w b v : V}
    (h₁ : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b))
    (h₂ : WeakOrder.of (W.perm b) ≤ WeakOrder.of (W.perm v)) :
    W.arrow h₁ ≫ W.arrow h₂ = W.arrow (h₁.trans h₂) := by
  obtain ⟨R₁⟩ := W.nonempty_climb h₁
  obtain ⟨R₂⟩ := W.nonempty_climb h₂
  rw [← eval_eq_arrow hW R₁, ← eval_eq_arrow hW R₂]
  exact (W.eval.map_comp R₁ R₂).symm.trans (eval_eq_arrow hW (R₁.comp R₂))

/-- **Matsumoto's theorem, as the universal property it is**: a labelling of the covers satisfying
Artin's relation extends to a functor on the poset — `functor_unique` says it is the only one. -/
noncomputable def functor (hW : W.IsArtin) : W.Poset ⥤ C where
  obj v := W.pre.obj v
  map h := W.arrow (leOfHom (X := W.Poset) h)
  map_id _ := arrow_refl _
  map_comp _ _ := (arrow_comp hW _ _).symm

/-- **…and it extends the labelling**: a cover's arrow is the one it names. -/
@[simp] theorem functor_map_ascent (hW : W.IsArtin) {w v : V} (e : Ascent W.perm w v) :
    (W.functor hW).map (homOfLE (X := W.Poset) e.le) = W.pre.map e :=
  (eval_eq_arrow hW (Quiver.Path.nil.cons e)).symm.trans (Category.id_comp _)

/-- …and a climb spells nothing but its two ends. -/
theorem functor_map_climb (hW : W.IsArtin) {w v : V} (R : Climb W.perm w v) :
    (W.functor hW).map (homOfLE (X := W.Poset) (Climb.le R)) = W.eval.map R :=
  (eval_eq_arrow hW R).symm

/-- Two renamed arrows, composed at a shared renaming. -/
private theorem sandwich_comp {A A' B B' D D' : C} (p : A = A') (q : B = B') (r : D = D')
    (f : A' ⟶ B') (g : B' ⟶ D') :
    (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm)
      = eqToHom p ≫ (f ≫ g) ≫ eqToHom r.symm := by
  subst p; subst q; subst r; simp

/-- **…uniquely**: the covers generate the poset, so a functor restricting to the labelling on them
is this one. -/
theorem functor_unique (hW : W.IsArtin) (F : W.Poset ⥤ C) (hobj : ∀ v : V, F.obj v = W.pre.obj v)
    (hmap : ∀ {w v : V} (e : Ascent W.perm w v),
      F.map (homOfLE (X := W.Poset) e.le)
        = eqToHom (hobj w) ≫ W.pre.map e ≫ eqToHom (hobj v).symm) :
    F = W.functor hW := by
  have key : ∀ {w v : V} (R : Climb W.perm w v)
      (hle : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)),
      F.map (homOfLE (X := W.Poset) hle)
        = eqToHom (hobj w) ≫ W.eval.map R ≫ eqToHom (hobj v).symm := by
    intro w v R
    induction R with
    | nil =>
        intro hle
        have h1 : F.map (homOfLE (X := W.Poset) hle)
            = eqToHom (hobj w) ≫ eqToHom (hobj w).symm := by
          rw [eqToHom_trans, eqToHom_refl]
          exact F.map_id _
        rw [h1]
        change eqToHom (hobj w) ≫ eqToHom (hobj w).symm
          = eqToHom (hobj w) ≫ 𝟙 (W.pre.obj w) ≫ eqToHom (hobj w).symm
        simp
    | @cons b c R e ih =>
        intro hle
        rw [show homOfLE (X := W.Poset) hle
              = homOfLE (X := W.Poset) (Climb.le R) ≫ homOfLE (X := W.Poset) (Ascent.le e)
              from rfl, F.map_comp, ih _, hmap e]
        exact sandwich_comp (hobj w) (hobj b) (hobj c) (W.eval.map R) (W.pre.map e)
  refine CategoryTheory.Functor.ext hobj fun w v h => ?_
  obtain ⟨R⟩ := W.nonempty_climb (leOfHom (X := W.Poset) h)
  rw [Subsingleton.elim h (homOfLE (X := W.Poset) (leOfHom (X := W.Poset) h)), key R _,
    functor_map_climb hW R]
  rfl

end Web

end CubeChains
