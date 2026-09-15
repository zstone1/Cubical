import CubeChains.Machinery.Braid.RankTwo
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Machinery/Braid/MatsumotoCat — Matsumoto between distinct objects

The index set is a **lower set of the right weak order on `Sₙ`** (`WeakOrder.Lower`), one object per
element, and the covers quiver it (`Ascents`), so a reduced word is a **path** and a web is a
prefunctor out of it.  `Web.IsArtin` — the two covers below an element are joined over the foot of
the polygon they span — extends that labelling to a functor on the poset, uniquely.

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

/-- **An ascent is pinned by its two ends** — the crossing names the index (`adjT_injective`). -/
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

/-- **Two ascents into one element come from different elements exactly when they cross different
pairs.** -/
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

/-- **A climb crosses once per letter** — so its length is a function of its two ends. -/
theorem permLen_eq {w : V} : ∀ {v : V} (R : Climb p w v),
    permLen (p v) = permLen (p w) + R.length
  | _, .nil => rfl
  | _, .cons R e => e.permLen_eq.trans (congrArg (· + 1) (permLen_eq R))

/-- **A climb that returns to its start is trivial.** -/
theorem eq_nil {w : V} (R : Climb p w w) : R = Quiver.Path.nil :=
  Quiver.Path.eq_nil_of_length_zero R (by have := permLen_eq R; omega)

/-- **A climb that keeps the length is trivial**, even when the climb itself was chosen. -/
theorem eq_start_of_permLen_eq (hp : Function.Injective p) {w b : V} (R : Climb p w b)
    (h : permLen (p b) = permLen (p w)) : w = b :=
  hp (WeakOrder.eq_of_le_of_permLen_eq (le R) h.symm)

/-- **A climb that raises the length by one is a single ascent.** -/
theorem eq_cons_nil (hp : Function.Injective p) {w v : V} (R : Climb p w v)
    (h : permLen (p v) = permLen (p w) + 1) :
    ∃ e : Ascent p w v, R = Quiver.Path.nil.cons e := by
  cases R with
  | nil => exact absurd h (by omega)
  | cons R e =>
      obtain rfl := eq_start_of_permLen_eq hp R (by have := e.permLen_eq; omega)
      exact ⟨e, congrArg (fun S : Climb p w w => S.cons e) (eq_nil R)⟩

/-- **A climb of length two is two ascents** — through a middle the two ends do not force. -/
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

`V` is not literally a set of permutations — the runs over a chain are a subtype of one — so it
comes with the injection naming which permutation each element performs. -/

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

/-- **Everything below something performed is performed.** -/
theorem exists_of_le {v : V} {x : WeakOrder n} (h : x ≤ WeakOrder.of (W.perm v)) :
    ∃ u : V, WeakOrder.of (W.perm u) = x :=
  W.isLowerSet h ⟨v, rfl⟩

/-- **Everything below an element is climbed to it** — reachability in the Hasse diagram, which
the lower set performs step by step. -/
theorem nonempty_climb {w v : V} (h : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm v)) :
    Nonempty (Climb W.perm w v) := by
  suffices ∀ x, Relation.ReflTransGen (· ⋖ ·) x (WeakOrder.of (W.perm v)) →
      ∀ u : V, WeakOrder.of (W.perm u) = x → Nonempty (Climb W.perm u v) from
    this _ (le_iff_reflTransGen.mp h) w rfl
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun u hu => by obtain rfl := W.perm_inj hu; exact ⟨.nil⟩
  | head hxy hyv ih =>
      intro u hu
      obtain ⟨b, rfl⟩ := W.exists_of_le (le_iff_reflTransGen.mpr hyv)
      obtain ⟨R⟩ := ih b rfl
      obtain ⟨e⟩ := nonempty_ascent_iff.mpr (hu ▸ hxy)
      exact ⟨(Quiver.Path.nil.cons e).comp R⟩

/-- `V`, ordered by the weak order it indexes — the poset a web is a functor out of. -/
def Poset (_W : Lower n V) : Type u := V

instance : PartialOrder W.Poset :=
  PartialOrder.lift (β := WeakOrder n) (fun v => WeakOrder.of (W.perm v)) W.perm_inj

end Lower

end WeakOrder

/-! ## A web of covers -/

/-- A labelling of the Hasse diagram of a lower set of the right weak order: an object per element
and an arrow per cover. -/
structure Web (n : ℕ) (V : Type u) (C : Type*) [Category C] extends WeakOrder.Lower n V where
  /-- The object an element carries, and the arrow a cover names. -/
  pre : Ascents perm ⥤q C

namespace Web

variable {C : Type*} [Category C] (W : Web n V C)

/-- The arrow a climb composes to — the free category on the covers, evaluated. -/
abbrev eval (W : Web n V C) : Paths (Ascents W.perm) ⥤ C := Paths.lift W.pre

/-! ### The polygon two covers span -/

variable {v b b' : V}

theorem idx_ne (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    ((e.idx : ℕ) ≠ (e'.idx : ℕ)) := (e.idx_ne_iff W.perm_inj e').mpr h

/-- **The foot of the polygon two covers span**, performed by the lower set. -/
noncomputable def foot (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') : V :=
  (W.exists_of_le (polyFoot_le (idx_ne W e e' h) e.descent e'.descent)).choose

@[simp] theorem perm_foot (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    W.perm (W.foot e e' h) = polyFoot (W.perm v) e.idx e'.idx :=
  (W.exists_of_le (polyFoot_le (idx_ne W e e' h) e.descent e'.descent)).choose_spec

theorem foot_le_left (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    WeakOrder.of (W.perm (W.foot e e' h)) ≤ WeakOrder.of (W.perm b) := by
  rw [perm_foot, e.perm_eq']
  exact polyFoot_le_mul_adjT (idx_ne W e e' h) e.descent e'.descent

theorem foot_le_right (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b') :
    WeakOrder.of (W.perm (W.foot e e' h)) ≤ WeakOrder.of (W.perm b') := by
  rw [perm_foot, polyFoot_comm (idx_ne W e e' h), e'.perm_eq']
  exact polyFoot_le_mul_adjT (Ne.symm (idx_ne W e e' h)) e'.descent e.descent

/-- **The foot is reached from below**: anything under both covers is under it. -/
theorem le_foot {w : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b')
    (hb : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b))
    (hb' : WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm b')) :
    WeakOrder.of (W.perm w) ≤ WeakOrder.of (W.perm (W.foot e e' h)) := by
  rw [perm_foot]
  refine le_polyFoot (idx_ne W e e' h) (hb.trans e.le) ?_ ?_
  · exact WeakOrder.residue_descent e.descent (by rw [← e.perm_eq']; exact hb)
  · exact WeakOrder.residue_descent e'.descent (by rw [← e'.perm_eq']; exact hb')

/-- **Artin's relation, in one clause**: two covers below an element with *different* elements
underneath are joined over the foot of the polygon they span, by two climbs naming one arrow. -/
def IsArtin : Prop :=
  ∀ {v b b' : V} (e : Ascent W.perm b v) (e' : Ascent W.perm b' v) (h : b ≠ b'),
    ∃ (R : Climb W.perm (W.foot e e' h) b) (R' : Climb W.perm (W.foot e e' h) b'),
      W.eval.map (R.cons e) = W.eval.map (R'.cons e')

variable {W}

/-- **Matsumoto's theorem between distinct objects**: two climbs with the same ends name one arrow.
A shared top cover strips off; distinct ones close at the foot, above both starts (`le_foot`). -/
theorem eval_eq (hW : W.IsArtin) {w v : V} (R R' : Climb W.perm w v) :
    W.eval.map R = W.eval.map R' := by
  cases R with
  | nil => exact congrArg W.eval.map (Climb.eq_nil R').symm
  | @cons b _ R₀ e =>
    cases R' with
    | nil => exact absurd (Climb.eq_nil (p := W.perm) (.cons R₀ e)) nofun
    | @cons b' _ R₀' e' =>
      change W.eval.map R₀ ≫ W.pre.map e = W.eval.map R₀' ≫ W.pre.map e'
      by_cases hbb : b = b'
      · subst hbb
        rw [Ascent.instSubsingleton.allEq e e', eval_eq hW R₀ R₀']
      · obtain ⟨S, S', heq⟩ := hW e e' hbb
        obtain ⟨P⟩ := W.nonempty_climb (le_foot W e e' hbb (Climb.le R₀) (Climb.le R₀'))
        rw [eval_eq hW R₀ (P.comp S), eval_eq hW R₀' (P.comp S'),
          show W.eval.map (P.comp S) = W.eval.map P ≫ W.eval.map S from W.eval.map_comp P S,
          show W.eval.map (P.comp S') = W.eval.map P ≫ W.eval.map S' from W.eval.map_comp P S',
          Category.assoc, Category.assoc]
        exact congrArg (W.eval.map P ≫ ·) heq
termination_by permLen (W.perm v)
decreasing_by
  all_goals first
    | (have := e.permLen_eq; omega)
    | (have := e'.permLen_eq; omega)

/-! ## The functor the labelling extends to -/

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

/-- **…uniquely**: the climbs reach every comparison, so a functor agreeing with the labelling on
the covers agrees with it after `Paths.lift`, hence everywhere. -/
theorem functor_unique (hW : W.IsArtin) (F : W.Poset ⥤ C) (hobj : ∀ v : V, F.obj v = W.pre.obj v)
    (hmap : ∀ {w v : V} (e : Ascent W.perm w v),
      F.map (homOfLE (X := W.Poset) e.le)
        = eqToHom (hobj w) ≫ W.pre.map e ≫ eqToHom (hobj v).symm) :
    F = W.functor hW := by
  let Φ : Paths (Ascents W.perm) ⥤ W.Poset :=
    Paths.lift { obj := id, map := fun e => homOfLE (X := W.Poset) (Ascent.le e) }
  have hΦ : Φ ⋙ F = Φ ⋙ W.functor hW := Paths.ext_functor (funext hobj) fun _ _ e => by
    simp only [Functor.comp_map, Φ, Paths.lift_toPath]
    exact (hmap e).trans (congrArg (eqToHom _ ≫ · ≫ eqToHom _) (functor_map_ascent hW e).symm)
  refine CategoryTheory.Functor.ext hobj fun w v h => ?_
  obtain ⟨R⟩ := W.nonempty_climb (leOfHom (X := W.Poset) h)
  rw [Subsingleton.elim h (Φ.map R)]
  exact Functor.congr_hom hΦ R

end Web

end CubeChains
