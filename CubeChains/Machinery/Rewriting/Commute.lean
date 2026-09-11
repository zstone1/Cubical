import CubeChains.Machinery.Rewriting.Presentation
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Machinery/Rewriting/Commute — ⟨a, b | ba = ab⟩, worked

The free commutative monoid on two letters, presented through `Presents.ofOrientation`.  The rule
`ba → ab` is **length-preserving**, so the termination measure is the inversion count and not a
length: the Coxeter situation in miniature, and the check that the bridge takes a measure it was not
built around.

A one-0-cell polygraph's words are lists by structure eta on `Unit` — every 0-cell is `pt`
definitionally, so nothing transports.  `Quiver.Path` snocs, so `snoc p e` reads "`p`, then `e`";
`Word.rec'` exists because `Quiver.Path.rec` generalises the target, which a word with both
endpoints pinned cannot spare.
-/

namespace CategoryTheory

namespace CommuteTwo

/-! ## Words -/

/-- The two letters on one 0-cell: `false` is `a`, `true` is `b`. -/
abbrev Letter : Unit → Unit → Type := fun _ _ => Bool

/-- The only 0-cell. -/
abbrev pt : GenObj Letter := ⟨()⟩

/-- A word. -/
abbrev Word := Quiver.Path pt pt

/-- Append a letter.  `Quiver.Path.cons` leaves the middle 0-cell to be inferred with nothing to
infer it from, so pin it here once. -/
abbrev snoc (p : Word) (e : Bool) : Word := p.cons e

/-- **Induction on words.**  `Quiver.Path.rec` generalises the target 0-cell; a word has both
endpoints pinned, so the generalisation is re-absorbed by eta. -/
@[elab_as_elim] def Word.rec' {motive : Word → Sort*} (hnil : motive Quiver.Path.nil)
    (hsnoc : ∀ (p : Word) (e : Bool), motive p → motive (snoc p e)) (p : Word) : motive p :=
  @Quiver.Path.rec (GenObj Letter) _ pt (fun _ t => motive t) hnil
    (fun q e ih => hsnoc q e ih) pt p

/-- `b` then `a`. -/
def ba : Word := snoc (snoc Quiver.Path.nil true) false

/-- `a` then `b`. -/
def ab : Word := snoc (snoc Quiver.Path.nil false) true

/-- **⟨a, b | ba = ab⟩.** -/
def poly : Polygraph where
  V := Unit
  Gen := Letter
  Rel := fun _ _ => Unit
  src := fun _ => ba
  tgt := fun _ => ab

/-! ## The oriented rule, read as a swap of adjacent letters -/

/-- One `ba → ab`: `tail` swaps the last two letters, `cons` moves the window left. -/
inductive Swap : Word → Word → Prop
  | tail (p : Word) : Swap (snoc (snoc p true) false) (snoc (snoc p false) true)
  | cons {p q : Word} (e : Bool) : Swap p q → Swap (snoc p e) (snoc q e)

/-- **A rule fired inside a context is a swap** — induction on the right-hand context, whose target
0-cell is free, which is what makes the induction legal. -/
theorem Swap.of_ctx {b : GenObj Letter} (f : Word) (g : Quiver.Path pt b) :
    Swap (f.comp (ba.comp g)) (f.comp (ab.comp g)) := by
  induction g with
  | nil => simpa [ba, ab] using Swap.tail f
  | cons g e ih => simpa using Swap.cons e ih

/-- **A rule fired anywhere survives one more letter on the right.** -/
theorem step_snoc {p q : Word} (e : Bool) (h : HomRel.CompClosure poly.homRel p q) :
    HomRel.CompClosure poly.homRel (snoc p e) (snoc q e) := by
  obtain ⟨a, b, f, m₁, m₂, g, hm⟩ := h
  exact HomRel.CompClosure.intro a b f m₁ m₂ (snoc g e) hm

/-- **The contextual closure of the 2-cell is exactly `Swap`.** -/
theorem step_iff {u v : Word} : Polygraph.step poly.homRel pt pt u v ↔ Swap u v := by
  have hr : poly.homRel ba ab := ⟨(), rfl, rfl⟩
  constructor
  · rintro ⟨_, _, f, _, _, g, ⟨⟩, rfl, rfl⟩
    exact Swap.of_ctx f g
  · intro h
    induction h with
    | tail p =>
      exact HomRel.CompClosure.intro (C := poly.Word) pt pt p ba ab Quiver.Path.nil hr
    | cons e _ ih => exact step_snoc e ih

theorem step_eq_swap (x y : GenObj Letter) : Polygraph.step poly.homRel x y = Swap := by
  funext u v; exact propext step_iff

/-! ## Termination: the inversion count -/

/-- Letters counted with a weight; both letter counts read off this. -/
def weigh (f : Bool → ℕ) : ∀ {b : GenObj Letter}, Quiver.Path pt b → ℕ
  | _, .nil => 0
  | _, .cons p e => weigh f p + f e

theorem weigh_nil (f : Bool → ℕ) : weigh f (Quiver.Path.nil : Word) = 0 := by simp [weigh]

theorem weigh_cons (f : Bool → ℕ) {b c : GenObj Letter} (p : Quiver.Path pt b)
    (e : b ⟶ c) : weigh f (p.cons e) = weigh f p + f e := by simp [weigh]

theorem weigh_comp (f : Bool → ℕ) {b : GenObj Letter} (p : Word) (q : Quiver.Path pt b) :
    weigh f (p.comp q) = weigh f p + weigh f q := by
  induction q with
  | nil => simp [weigh_nil]
  | cons q e ih => simp only [Quiver.Path.comp_cons, weigh_cons, ih, Nat.add_assoc]

/-- The number of `a`s. -/
def countA : ∀ {b : GenObj Letter}, Quiver.Path pt b → ℕ := weigh fun e => if e then 0 else 1

/-- The number of `b`s. -/
def countB : ∀ {b : GenObj Letter}, Quiver.Path pt b → ℕ := weigh fun e => if e then 1 else 0

@[simp] theorem countA_nil : countA (Quiver.Path.nil : Word) = 0 := weigh_nil _
@[simp] theorem countB_nil : countB (Quiver.Path.nil : Word) = 0 := weigh_nil _
@[simp] theorem countA_true (p : Word) : countA (snoc p true) = countA p := by
  simpa [countA] using weigh_cons _ p (true : pt ⟶ pt)
@[simp] theorem countA_false (p : Word) : countA (snoc p false) = countA p + 1 := by
  simpa [countA] using weigh_cons _ p (false : pt ⟶ pt)
@[simp] theorem countB_true (p : Word) : countB (snoc p true) = countB p + 1 := by
  simpa [countB] using weigh_cons _ p (true : pt ⟶ pt)
@[simp] theorem countB_false (p : Word) : countB (snoc p false) = countB p := by
  simpa [countB] using weigh_cons _ p (false : pt ⟶ pt)

theorem countA_comp {b : GenObj Letter} (p : Word) (q : Quiver.Path pt b) :
    countA (p.comp q) = countA p + countA q := weigh_comp _ p q

theorem countB_comp {b : GenObj Letter} (p : Word) (q : Quiver.Path pt b) :
    countB (p.comp q) = countB p + countB q := weigh_comp _ p q

/-- Inversions: each `a` inverts with every `b` before it. -/
def inversions : ∀ {b : GenObj Letter}, Quiver.Path pt b → ℕ
  | _, .nil => 0
  | _, .cons p e => inversions p + (if e then 0 else countB p)

@[simp] theorem inversions_true (p : Word) : inversions (snoc p true) = inversions p := by
  simp [inversions]

@[simp] theorem inversions_false (p : Word) :
    inversions (snoc p false) = inversions p + countB p := by simp [inversions]

/-- **A swap keeps the letter counts** — it permutes the word. -/
theorem Swap.countB_eq {u v : Word} (h : Swap u v) : countB u = countB v := by
  induction h with
  | tail p => simp
  | cons e _ ih => cases e <;> simp [ih]

/-- **…and spends exactly one inversion.** -/
theorem Swap.inversions_lt {u v : Word} (h : Swap u v) : inversions v < inversions u := by
  induction h with
  | tail p => simp only [inversions_true, inversions_false, countB_true]; omega
  | cons e h ih =>
    cases e
    · simp only [inversions_false, h.countB_eq]; omega
    · simp only [inversions_true]; omega

theorem swap_terminating : Relation.Terminating Swap :=
  Relation.terminating_of_measure Nat.lt_wfRel.wf inversions fun {_ _} h => h.inversions_lt

/-! ## Local confluence: there are no critical pairs

Two swaps out of one word are either at the same window, or at windows one apart — impossible, since
the shared letter would be both `a` and `b` — or disjoint, and disjoint swaps commute. -/

theorem Swap.cons_reflTransGen {p q : Word} (e : Bool) (h : Relation.ReflTransGen Swap p q) :
    Relation.ReflTransGen Swap (snoc p e) (snoc q e) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (Swap.cons e hbc)

theorem swap_locallyConfluent : Relation.LocallyConfluent Swap := by
  intro u v₁ v₂ h₁ h₂
  induction h₁ generalizing v₂ with
  | tail p =>
    cases h₂ with
    | tail => exact ⟨_, .refl, .refl⟩
    | cons _ h =>
      cases h with
      | cons _ h' =>
        exact ⟨snoc (snoc _ false) true,
          Swap.cons_reflTransGen _ (Swap.cons_reflTransGen _ (.single h')),
          .single (Swap.tail _)⟩
  | cons e h₁ ih =>
    cases h₂ with
    | tail p =>
      cases h₁ with
      | cons _ h' =>
        exact ⟨snoc (snoc _ false) true, .single (Swap.tail _),
          Swap.cons_reflTransGen _ (Swap.cons_reflTransGen _ (.single h'))⟩
    | cons _ h₂ =>
      obtain ⟨d, hd₁, hd₂⟩ := ih h₂
      exact ⟨snoc d e, Swap.cons_reflTransGen e hd₁, Swap.cons_reflTransGen e hd₂⟩

/-! ## Normal words are sorted, hence pinned by their letter counts -/

theorem normal_of_snoc {p : Word} {e : Bool} (h : Relation.Normal Swap (snoc p e)) :
    Relation.Normal Swap p := fun _ hq => h _ (Swap.cons e hq)

/-- **A normal word ending in `a` has no `b`**: the last `b` would swap with that `a`. -/
theorem countB_eq_zero_of_normal :
    ∀ {p : Word}, Relation.Normal Swap (snoc p false) → countB p = 0 := by
  intro p
  induction p using Word.rec' with
  | hnil => exact fun _ => countB_nil
  | hsnoc q g ih =>
    intro h
    match g with
    | true => exact absurd (Swap.tail q) (h _)
    | false => simpa using ih (normal_of_snoc h)

/-- **Normal words are separated by their letter counts.** -/
theorem eq_of_normal : ∀ (u v : Word), Relation.Normal Swap u → Relation.Normal Swap v →
    countA u = countA v → countB u = countB v → u = v := by
  intro u
  induction u using Word.rec' with
  | hnil =>
    intro v _ _ ha hb
    induction v using Word.rec' with
    | hnil => rfl
    | hsnoc q g _ =>
      exfalso
      match g with
      | true => simp only [countB_nil, countB_true] at hb; omega
      | false => simp only [countA_nil, countA_false] at ha; omega
  | hsnoc p e ih =>
    intro v hu hv ha hb
    induction v using Word.rec' with
    | hnil =>
      exfalso
      match e with
      | true => simp only [countB_nil, countB_true] at hb; omega
      | false => simp only [countA_nil, countA_false] at ha; omega
    | hsnoc q f _ =>
      match e, f with
      | false, false =>
        simp only [countA_false, countB_false] at ha hb
        rw [ih q (normal_of_snoc hu) (normal_of_snoc hv) (by omega) hb]
      | true, true =>
        simp only [countA_true, countB_true] at ha hb
        rw [ih q (normal_of_snoc hu) (normal_of_snoc hv) ha (by omega)]
      | true, false =>
        simp only [countB_true, countB_false, countB_eq_zero_of_normal hv] at hb
        omega
      | false, true =>
        simp only [countB_false, countB_true, countB_eq_zero_of_normal hu] at hb
        omega

/-! ## The orientation -/

/-- **The 2-cell, oriented `ba → ab`.** -/
def orient : poly.Orientation :=
  Polygraph.Orientation.ofCells poly fun x y => by
    rw [step_eq_swap x y]; exact ⟨swap_terminating, swap_locallyConfluent⟩

@[simp] theorem orient_rule : orient.rule = poly.homRel := rfl

/-! ## What it presents -/

/-- The free commutative monoid on the two letters. -/
abbrev M := Multiplicative (ℕ × ℕ)

/-- Each letter counted in its own coordinate.  The quiver is the one `SingleObj`'s *category*
induces — `Quiver.SingleObj.inst` is a second, equal-but-distinct instance that `Paths.lift` will
not accept. -/
def val : @Prefunctor (GenObj Letter) (genObjQuiver Letter) (SingleObj M)
    (CategoryStruct.toQuiver (self := Category.toCategoryStruct)) where
  obj _ := SingleObj.star M
  map e := (Multiplicative.ofAdd (if e then (0, 1) else (1, 0)) : M)

@[simp] theorem val_map (e : Bool) : val.map (X := pt) (Y := pt) e
    = (Multiplicative.ofAdd (if e then (0, 1) else (1, 0)) : M) := rfl

/-- **A word evaluates to its letter counts.** -/
theorem lift_val (u : Word) :
    (Paths.lift val).map u = (Multiplicative.ofAdd (countA u, countB u) : M) := by
  induction u using Word.rec' with
  | hnil => rfl
  | hsnoc p e ih =>
    rw [Paths.lift_cons, ih, SingleObj.comp_as_mul, val_map, ← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (Prod.ext_iff.mpr ⟨?_, ?_⟩)
    all_goals cases e
    all_goals simp
    all_goals omega

/-- `aⁱ` or `bʲ`. -/
def rep (e : Bool) : ℕ → Word
  | 0 => Quiver.Path.nil
  | n + 1 => snoc (rep e n) e

/-- The normal word `aⁱbʲ`. -/
def canon (i j : ℕ) : Word := (rep false i).comp (rep true j)

@[simp] theorem countA_rep_false (n : ℕ) : countA (rep false n) = n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih]

@[simp] theorem countA_rep_true (n : ℕ) : countA (rep true n) = 0 := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih]

@[simp] theorem countB_rep_false (n : ℕ) : countB (rep false n) = 0 := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih]

@[simp] theorem countB_rep_true (n : ℕ) : countB (rep true n) = n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, ih]

@[simp] theorem countA_canon (i j : ℕ) : countA (canon i j) = i := by simp [canon, countA_comp]

@[simp] theorem countB_canon (i j : ℕ) : countB (canon i j) = j := by simp [canon, countB_comp]

/-- **⟨a, b | ba = ab⟩ presents the free commutative monoid on two generators.** -/
def presents : Presents poly (SingleObj M) :=
  Presents.ofOrientation (C := SingleObj M) orient val
    (fun _ => by
      change (Paths.lift val).map ba = (Paths.lift val).map ab
      rw [lift_val, lift_val]; simp [ba, ab])
    (fun {x y _ _} hu hv h => by
      rw [orient_rule, step_eq_swap x y] at hu hv
      have h' := Multiplicative.ofAdd.injective
        ((lift_val _).symm.trans (h.trans (lift_val _)))
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h'
      exact eq_of_normal _ _ hu hv h1 h2)
    ⟨fun {_ _} f => ⟨canon (Multiplicative.toAdd f).1 (Multiplicative.toAdd f).2, by
      refine (lift_val _).trans ?_
      rw [countA_canon, countB_canon]
      rfl⟩⟩
    ⟨fun _ => ⟨pt, ⟨Iso.refl _⟩⟩⟩

end CommuteTwo

end CategoryTheory
