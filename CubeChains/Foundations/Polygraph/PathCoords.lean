import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Order.Basic

/-!
# Foundations/Polygraph/PathCoords — a path is its length and its letters

The concrete content of Carboni–Johnstone's first step: the free-category monad on quivers is
*familially representable*, the family being the length.  `ofCoords` lays `m` letters end to end,
`vtx`/`edgeAt` read them back, and `ext_of_coords` says nothing else is left.

Vertices are indexed by `ℕ` and clamped past the end, and letters carry their bound as a
propositional argument, so a path's coordinates never transport: `length_castPath` and friends are
`rfl` after `subst`, which is what lets a path equation be checked coordinatewise across a change
of endpoints.
-/

universe v₁ v₂ u₁ u₂

namespace Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- An arrow pushed forward along a map of quivers. -/
@[simps] def Total.map (π : V ⥤q W) (t : Total V) : Total W :=
  ⟨π.obj t.left, π.obj t.right, π.map t.hom⟩

namespace Path

/-! ## Coordinates -/

/-- The `i`-th vertex of a path, clamped to its target past its length. -/
def vtx {a : V} : ∀ {b : V}, Path a b → ℕ → V
  | _, nil => fun _ => a
  | b, cons q _ => fun i => if i ≤ q.length then q.vtx i else b

@[simp] theorem vtx_nil (a : V) (i : ℕ) : (nil : Path a a).vtx i = a := rfl

@[simp] theorem vtx_cons {a b c : V} (q : Path a b) (e : b ⟶ c) (i : ℕ) :
    (q.cons e).vtx i = if i ≤ q.length then q.vtx i else c := rfl

@[simp] theorem vtx_zero {a b : V} (p : Path a b) : p.vtx 0 = a := by
  induction p with
  | nil => rfl
  | cons q e ih => simp [ih]

theorem vtx_of_le {a b : V} (p : Path a b) {i : ℕ} (h : p.length ≤ i) : p.vtx i = b := by
  cases p with
  | nil => rfl
  | cons q e => rw [vtx_cons, if_neg (by simp only [length_cons] at h; omega)]

@[simp] theorem vtx_length {a b : V} (p : Path a b) : p.vtx p.length = b :=
  p.vtx_of_le (Nat.le_refl _)

/-- The `i`-th letter of a path. -/
def edgeAt {a : V} : ∀ {b : V} (p : Path a b), ∀ i : ℕ, i < p.length → Total V
  | _, nil => fun i h => absurd h (Nat.not_lt_zero i)
  | b, cons q e => fun i _ => if hi : i < q.length then q.edgeAt i hi else ⟨_, b, e⟩

theorem edgeAt_cons_of_lt {a b c : V} (q : Path a b) (e : b ⟶ c) (i : ℕ)
    (h : i < (q.cons e).length) (hi : i < q.length) : (q.cons e).edgeAt i h = q.edgeAt i hi :=
  dif_pos hi

theorem edgeAt_cons_of_ge {a b c : V} (q : Path a b) (e : b ⟶ c) (i : ℕ)
    (h : i < (q.cons e).length) (hi : q.length ≤ i) : (q.cons e).edgeAt i h = ⟨b, c, e⟩ :=
  dif_neg (by omega)

theorem edgeAt_congr {a b : V} {p q : Path a b} (h : p = q) (i : ℕ) (hp : i < p.length)
    (hq : i < q.length) : p.edgeAt i hp = q.edgeAt i hq := by subst h; rfl

theorem left_edgeAt {a b : V} (p : Path a b) (i : ℕ) (h : i < p.length) :
    (p.edgeAt i h).left = p.vtx i := by
  induction p with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons q e ih =>
      rcases Nat.lt_or_ge i q.length with hi | hi
      · rw [edgeAt_cons_of_lt q e i h hi, ih hi, vtx_cons, if_pos (by omega)]
      · rw [edgeAt_cons_of_ge q e i h hi, vtx_cons, if_pos (by simp only [length_cons] at h; omega)]
        exact (vtx_of_le q (by omega)).symm

theorem right_edgeAt {a b : V} (p : Path a b) (i : ℕ) (h : i < p.length) :
    (p.edgeAt i h).right = p.vtx (i + 1) := by
  induction p with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons q e ih =>
      rcases Nat.lt_or_ge i q.length with hi | hi
      · rw [edgeAt_cons_of_lt q e i h hi, ih hi, vtx_cons, if_pos (by omega)]
      · rw [edgeAt_cons_of_ge q e i h hi, vtx_cons,
          if_neg (by simp only [length_cons] at h; omega)]

/-! ## A path is its coordinates -/

/-- The path with prescribed vertices and letters. -/
def ofCoords (v : ℕ → V) : ∀ m : ℕ, (∀ i, i < m → (v i ⟶ v (i + 1))) → Path (v 0) (v m)
  | 0, _ => nil
  | m + 1, hom => (ofCoords v m fun i h => hom i (by omega)).cons (hom m (by omega))

@[simp] theorem ofCoords_zero (v : ℕ → V) (hom) : ofCoords v 0 hom = nil := rfl

@[simp] theorem ofCoords_succ (v : ℕ → V) (m : ℕ) (hom) :
    ofCoords v (m + 1) hom =
      (ofCoords v m fun i h => hom i (Nat.lt_succ_of_lt h)).cons (hom m (Nat.lt_succ_self m)) :=
  rfl

@[simp] theorem length_ofCoords (v : ℕ → V) (m : ℕ) (hom) : (ofCoords v m hom).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (· + 1) (ih _)

theorem vtx_ofCoords (v : ℕ → V) (m : ℕ) (hom) {i : ℕ} (h : i ≤ m) :
    (ofCoords v m hom).vtx i = v i := by
  induction m with
  | zero => obtain rfl : i = 0 := Nat.le_zero.1 h; rfl
  | succ m ih =>
      rw [ofCoords_succ, vtx_cons, length_ofCoords]
      rcases Nat.lt_or_ge i (m + 1) with hi | hi
      · rw [if_pos (by omega)]; exact ih _ (by omega)
      · rw [if_neg (by omega)]; exact congrArg v (by omega)

theorem edgeAt_ofCoords (v : ℕ → V) (m : ℕ) (hom) {i : ℕ} (h : i < m) (h') :
    (ofCoords v m hom).edgeAt i h' = ⟨v i, v (i + 1), hom i h⟩ := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero i)
  | succ m ih =>
      rcases Nat.lt_or_ge i m with hi | hi
      · refine (edgeAt_cons_of_lt _ _ _ h' ?_).trans (ih _ hi _)
        rw [length_ofCoords]; exact hi
      · obtain rfl : i = m := by omega
        exact edgeAt_cons_of_ge _ _ _ h' (by simp)

/-- **A path is pinned by its length and its letters.** -/
theorem ext_of_coords {a : V} : ∀ (m : ℕ) {b : V} {p q : Path a b}, p.length = m → q.length = m →
    (∀ i (h : i < p.length) (h' : i < q.length), p.edgeAt i h = q.edgeAt i h') → p = q := by
  intro m
  induction m with
  | zero =>
      rintro b p q hp hq -
      obtain rfl : a = b := eq_of_length_zero p hp
      rw [eq_nil_of_length_zero p hp, eq_nil_of_length_zero q hq]
  | succ m ih =>
      rintro b (_ | ⟨p, e⟩) (_ | ⟨q, f⟩) hp hq he
      · exact absurd hp (by simp)
      · exact absurd hp (by simp)
      · exact absurd hq (by simp)
      · have hpl : p.length = m := by simpa using hp
        have hql : q.length = m := by simpa using hq
        have hlast := he p.length (by simp) (by simp; omega)
        rw [edgeAt_cons_of_ge p e _ _ (Nat.le_refl _),
          edgeAt_cons_of_ge q f _ _ (by omega)] at hlast
        injection hlast with h₁ _ h₂
        subst h₁
        obtain rfl : e = f := eq_of_heq h₂
        refine congrArg (Path.cons · e) (ih hpl hql fun i h h' => ?_)
        have := he i (by simp; omega) (by simp; omega)
        rwa [edgeAt_cons_of_lt p e i _ h, edgeAt_cons_of_lt q e i _ h'] at this

/-! ## Transport, and functoriality

Coordinates are stable under a change of endpoints and under a map of quivers, so a path equation
can always be checked one letter at a time. -/

/-- A path transported along equalities of its endpoints. -/
def castPath {a b a' b' : V} (p : Path a b) (ha : a = a') (hb : b = b') : Path a' b' := by
  subst ha; subst hb; exact p

@[simp] theorem castPath_rfl {a b : V} (p : Path a b) : p.castPath rfl rfl = p := rfl

@[simp] theorem length_castPath {a b a' b' : V} (p : Path a b) (ha : a = a') (hb : b = b') :
    (p.castPath ha hb).length = p.length := by subst ha; subst hb; rfl

@[simp] theorem vtx_castPath {a b a' b' : V} (p : Path a b) (ha : a = a') (hb : b = b') (i : ℕ) :
    (p.castPath ha hb).vtx i = p.vtx i := by subst ha; subst hb; rfl

theorem edgeAt_castPath {a b a' b' : V} (p : Path a b) (ha : a = a') (hb : b = b') (i : ℕ)
    (h : i < (p.castPath ha hb).length) (h' : i < p.length) :
    (p.castPath ha hb).edgeAt i h = p.edgeAt i h' := by subst ha; subst hb; rfl

theorem _root_.Prefunctor.length_mapPath (π : V ⥤q W) {a b : V} (p : Path a b) :
    (π.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih

@[simp] theorem vtx_mapPath (π : V ⥤q W) {a b : V} (p : Path a b) (i : ℕ) :
    (π.mapPath p).vtx i = π.obj (p.vtx i) := by
  induction p with
  | nil => rfl
  | cons q e ih =>
      rw [show π.mapPath (q.cons e) = (π.mapPath q).cons (π.map e) from rfl, vtx_cons, vtx_cons,
        π.length_mapPath q, ih]
      split <;> rfl

theorem edgeAt_mapPath (π : V ⥤q W) {a b : V} (p : Path a b) (i : ℕ) (h : i < p.length)
    (h' : i < (π.mapPath p).length) :
    (π.mapPath p).edgeAt i h' = Total.map π (p.edgeAt i h) := by
  induction p with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons q e ih =>
      rcases Nat.lt_or_ge i q.length with hi | hi
      · refine (edgeAt_cons_of_lt (π.mapPath q) (π.map e) i h' ?_).trans ?_
        · rw [π.length_mapPath]; exact hi
        · rw [ih hi, edgeAt_cons_of_lt q e i h hi]
      · refine (edgeAt_cons_of_ge (π.mapPath q) (π.map e) i h' ?_).trans ?_
        · rw [π.length_mapPath]; exact hi
        · rw [edgeAt_cons_of_ge q e i h hi]; rfl

end Path

end Quiver
