import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Order.Basic

/-!
# Foundations/Polygraph/PathCoords — a path is its length and its letters

The concrete content of Carboni–Johnstone's first step: the free-category monad on quivers is
*familially representable*, the family being the length.  `ofCoords` lays `m` letters end to end,
`vtx`/`edgeAt` read them back, and `ext_of_coords` says nothing else is left.

Vertices are indexed by `ℕ` and clamped past the end, and letters carry their bound as a
propositional argument, so a path's coordinates never transport across a change of endpoints:
`length_cellCongr` and friends are `rfl` after `subst`.  That change is `cellCongr` — one spelling
for every cell fibred over a boundary, words and 2-cells alike.
-/

universe v₁ v₂ u₁ u₂

/-! ## Cells read at other names for their boundary

A cell is fibred over the two indices its boundary spans, so a proof that renames those indices
must carry the cell across.  `cellCongr` is that transport — `Quiver.homOfEq` is the 1-cell case;
words and 2-cells have no mathlib version — and it is the *only* one a cell ever carries. -/

/-- A cell of a family fibred over a boundary, read at indices its boundary is equal to. -/
def cellCongr {ι : Sort*} (F : ι → ι → Sort*) :
    ∀ {a b A B : ι}, a = A → b = B → F a b → F A B
  | _, _, _, _, rfl, rfl, c => c

/-- **A cell read at its own indices is itself** — proof irrelevance, so neither equation need be
`rfl` on the nose.  This is what makes `rintro … rfl rfl` leave no transport behind. -/
theorem cellCongr_self {ι : Sort*} (F : ι → ι → Sort*) {a b : ι} (ha : a = a)
    (hb : b = b) (c : F a b) : cellCongr F ha hb c = c := rfl

/-- Which proofs name the indices is irrelevant, so `cellCongr` descends to a quotient. -/
theorem cellCongr_heq {ι : Sort*} (F : ι → ι → Sort*) {a b A B : ι} (ha : a = A) (hb : b = B)
    (c : F a b) : cellCongr F ha hb c ≍ c := by subst ha; subst hb; rfl

theorem cellCongr_trans {ι : Sort*} (F : ι → ι → Sort*) {a b A B A' B' : ι} (ha : a = A)
    (hb : b = B) (ha' : A = A') (hb' : B = B') (c : F a b) :
    cellCongr F ha' hb' (cellCongr F ha hb c) = cellCongr F (ha.trans ha') (hb.trans hb') c := by
  subst ha; subst hb; subst ha'; subst hb'; rfl

/-! `cellCongr` on words is blind to which proof names an index, so it commutes with the way a word
is built: an empty word is pinned by its endpoints, and concatenation passes through. -/

section CellCongrPath

variable {V : Type*} [Quiver V]

/-- **A transported empty word is pinned by its endpoints.** -/
theorem cellCongr_nil_eq {x x' A B : V} (h₁ : x = A) (h₂ : x = B) (h₁' : x' = A) (h₂' : x' = B) :
    cellCongr Quiver.Path h₁ h₂ (Quiver.Path.nil : Quiver.Path x x)
      = cellCongr Quiver.Path h₁' h₂' (Quiver.Path.nil : Quiver.Path x' x') := by
  subst h₁; subst h₂; subst h₁'; rfl

/-- **Transport distributes over concatenation.** -/
theorem cellCongr_comp {x y z A B C : V} (h₁ : x = A) (h₂ : y = B) (h₃ : z = C)
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    (cellCongr Quiver.Path h₁ h₂ p).comp (cellCongr Quiver.Path h₂ h₃ q)
      = cellCongr Quiver.Path h₁ h₃ (p.comp q) := by
  subst h₁; subst h₂; subst h₃; rfl

/-- **…and a transported one-letter word is the transported letter.** -/
theorem cellCongr_toPath {x y A B : V} (h₁ : x = A) (h₂ : y = B) (e : x ⟶ y) :
    cellCongr Quiver.Path h₁ h₂ e.toPath = (Quiver.homOfEq e h₁ h₂).toPath := by
  subst h₁; subst h₂; rfl

end CellCongrPath

/-! ## Words along a prefunctor -/

/-- **A prefunctor carries a transported word to the transported word.** -/
theorem Prefunctor.mapPath_cellCongr {V : Type*} [Quiver V] {W : Type*} [Quiver W] (π : V ⥤q W)
    {x y x' y' : V} (hx : x = x') (hy : y = y') (p : Quiver.Path x y) :
    π.mapPath (cellCongr Quiver.Path hx hy p)
      = cellCongr Quiver.Path (congrArg π.obj hx) (congrArg π.obj hy) (π.mapPath p) := by
  subst hx; subst hy; rfl

/-- A route of three prefunctors moves a word the way its composite does; name them, or the
unifier solves them off the right-hand side and loses the composition defeq. -/
theorem Prefunctor.mapPath_comp₃_apply {V W X Y : Type*} [Quiver V] [Quiver W] [Quiver X]
    [Quiver Y] (F : V ⥤q W) (G : W ⥤q X) (H : X ⥤q Y) {a b : V} (p : Quiver.Path a b) :
    (F ⋙q G ⋙q H).mapPath p = H.mapPath (G.mapPath (F.mapPath p)) :=
  (Prefunctor.mapPath_comp_apply F (G ⋙q H) p).trans
    (Prefunctor.mapPath_comp_apply G H (F.mapPath p))

/-- **Equal prefunctors agree on words.** -/
theorem Prefunctor.mapPath_heq_of_eq {V : Type*} [Quiver V] {W : Type*} [Quiver W] {π σ : V ⥤q W}
    (h : π = σ) {x y : V} (u : Quiver.Path x y) : π.mapPath u ≍ σ.mapPath u := by subst h; rfl

namespace Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- An arrow pushed forward along a map of quivers. -/
@[simps] def Total.map (π : V ⥤q W) (t : Total V) : Total W :=
  ⟨π.obj t.left, π.obj t.right, π.map t.hom⟩

/-- The `b`-endpoint (`false` = source) of an arrow. -/
def Total.endpt (b : Bool) (t : Total V) : V := if b then t.right else t.left

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

/-- **The `β`-endpoint of the `i`-th letter is the `i`-th vertex** — one further along at the
target end. -/
theorem endpt_edgeAt {a b : V} (p : Path a b) (β : Bool) (i : ℕ) (h : i < p.length) :
    (p.edgeAt i h).endpt β = p.vtx (bif β then i + 1 else i) := by
  induction p with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons q e ih =>
      simp only [length_cons] at h
      rcases Nat.lt_or_ge i q.length with hi | hi
      · rw [edgeAt_cons_of_lt q e i _ hi, ih hi, vtx_cons,
          if_pos (by cases β <;> [exact Nat.le_of_lt hi; exact hi])]
      · rw [edgeAt_cons_of_ge q e i _ hi]
        cases β
        · change _ = (q.cons e).vtx i
          rw [vtx_cons, if_pos (show i ≤ q.length by omega)]
          exact (vtx_of_le q hi).symm
        · change _ = (q.cons e).vtx (i + 1)
          rw [vtx_cons, if_neg (show ¬ i + 1 ≤ q.length by omega)]
          rfl

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

@[simp] theorem length_cellCongr {a b a' b' : V} (ha : a = a') (hb : b = b') (p : Path a b) :
    (cellCongr Path ha hb p).length = p.length := by subst ha; subst hb; rfl

@[simp] theorem vtx_cellCongr {a b a' b' : V} (ha : a = a') (hb : b = b') (p : Path a b) (i : ℕ) :
    (cellCongr Path ha hb p).vtx i = p.vtx i := by subst ha; subst hb; rfl

theorem edgeAt_cellCongr {a b a' b' : V} (ha : a = a') (hb : b = b') (p : Path a b) (i : ℕ)
    (h : i < (cellCongr Path ha hb p).length) (h' : i < p.length) :
    (cellCongr Path ha hb p).edgeAt i h = p.edgeAt i h' := by subst ha; subst hb; rfl

/-! ### A prescribed word, re-endpointed

`ofCoords` followed by `cellCongr` is how a word with prescribed coordinates is read at names for
its ends, so its own coordinates come back unchanged. -/

theorem vtx_cellCongr_ofCoords (v : ℕ → V) (m : ℕ) (hom) {a b : V} (ha : v 0 = a) (hb : v m = b)
    {i : ℕ} (h : i ≤ m) : (cellCongr Path ha hb (ofCoords v m hom)).vtx i = v i :=
  (vtx_cellCongr ..).trans (vtx_ofCoords v m hom h)

theorem edgeAt_cellCongr_ofCoords (v : ℕ → V) (m : ℕ) (hom) {a b : V} (ha : v 0 = a) (hb : v m = b)
    {i : ℕ} (h : i < m) (h') :
    (cellCongr Path ha hb (ofCoords v m hom)).edgeAt i h' = ⟨v i, v (i + 1), hom i h⟩ :=
  (edgeAt_cellCongr _ _ _ i h' (by rw [length_ofCoords]; exact h)).trans
    (edgeAt_ofCoords v m hom h _)

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

/-- **A re-endpointed word is a pushed-forward word** when the two agree letter by letter. -/
theorem cellCongr_eq_mapPath {A B : W} {a b : V} (p : Path A B) (π : V ⥤q W) (q : Path a b)
    (hA : A = π.obj a) (hB : B = π.obj b) (hlen : p.length = q.length)
    (h : ∀ i (hp : i < p.length) (hq : i < q.length),
      p.edgeAt i hp = Total.map π (q.edgeAt i hq)) :
    cellCongr Path hA hB p = π.mapPath q := by
  refine ext_of_coords q.length ((length_cellCongr ..).trans hlen) (π.length_mapPath q)
    fun i hi hi' => ?_
  have hq : i < q.length := by rwa [length_cellCongr, hlen] at hi
  exact (edgeAt_cellCongr hA hB p i hi (by rw [hlen]; exact hq)).trans
    ((h i _ hq).trans (edgeAt_mapPath π q i hq hi').symm)

end Path

end Quiver
