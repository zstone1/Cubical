import CubeChains.Foundations.Shift
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Foundations/CubeConcat

The **geometric concatenation** (juxtaposition) of cubes, giving the box category
`Box` a `MonoidalCategory` structure.  On objects `⟨m⟩ ⊗ ⟨n⟩ = ⟨m + n⟩`; the unit
is `𝟙_ = ⟨0⟩ = □⁰`; on morphisms it juxtaposes two precubical cube maps.

**Layer:** Foundations.  **Imports:** `Shift`, mathlib `Monoidal.Category`.

This is the *n-fold / two-block generalization* of `Box.shift`'s `snocFree`:
instead of appending one free coordinate we juxtapose two whole sign-vectors with
`Fin.append`.  As in `Shift.lean`, everything routes through the concrete cube
Yoneda lemma (`Representable.lean`): a precubical map `□^m ⟶ □^n` is the same data
as an `m`-cell of `□^n` (its value `ev f` on the top cell), and `□^m ⟶ K` is rebuilt
from an `m`-cell by `canonicalMap`.

The combinatorial crux (the analogue of `StdCube.app_snocFree`) is
`StdCube.app_append`: the iterated-face map `sapp` commutes with the juxtaposition
`append` of cells.  It is proved by the same strong-induction-on-codimension,
peeling the smallest fixed coordinate — which, because left-block (`castAdd`)
indices precede right-block (`natAdd`) indices, lies in the left block unless the
left block is already a top cell.  From it, functoriality (`tensor_id`,
`tensor_comp`) follows exactly as in `Box.shift.map_comp`.

The associator/unitors come from `Fin.append` associativity (`Fin.append_assoc`)
and the empty-vector laws (`Fin.append_left_nil`/`Fin.append_right_nil`); since
`⟨a+b⟩+c` and `⟨a+(b+c)⟩` differ by `Nat.add_assoc` (not defeq), the associator is a
genuine `eqToHom` iso (`Box.reHom`).  All coherences are reduced to cell-level
identities through the cube-Yoneda map `ev`, which is injective on box morphisms;
pentagon/triangle then collapse because every associator/unitor is a reindexing iso
`reHom` and these compose and depend only on their endpoints.
-/

open CategoryTheory Opposite

namespace StdCube

/-! ### `noneSet` cardinality and `none`-positions under `Fin.append` -/

/-- The `none`-count of an appended raw cell splits as the sum of the two blocks'
`none`-counts. -/
theorem card_noneSet_append {M N : ℕ} (u : Fin M → Option Bool) (w : Fin N → Option Bool) :
    (noneSet (Fin.append u w)).card = (noneSet u).card + (noneSet w).card := by
  rw [card_noneSet_eq_sum, card_noneSet_eq_sum u, card_noneSet_eq_sum w,
    Fin.sum_univ_add]
  congr 1 <;> · apply Finset.sum_congr rfl; intro j _
                first
                  | rw [Fin.append_left] | rw [Fin.append_right]

/-! ### Appending two cells -/

/-- Juxtapose a `p`-cell of `□^M` and a `q`-cell of `□^N` into a `(p+q)`-cell of
`□^(M+N)`: the underlying sign-vector is `Fin.append`. -/
def append {M N p q : ℕ} (u : cells M p) (w : cells N q) : cells (M + N) (p + q) :=
  ⟨Fin.append u.val w.val, by rw [card_noneSet_append, u.prop, w.prop]⟩

@[simp] theorem append_val {M N p q : ℕ} (u : cells M p) (w : cells N q) :
    (append u w).val = Fin.append u.val w.val := rfl

/-- The function underlying the order embedding of `noneSet (append u w)`:
left-block `none`s via `castAdd ∘ nones u`, right-block via `natAdd ∘ nones w`. -/
private def nonesAppendFun {M N p q : ℕ} (u : cells M p) (w : cells N q) :
    Fin (p + q) → Fin (M + N) :=
  Fin.addCases (fun x => Fin.castAdd N (nones u x)) (fun y => Fin.natAdd M (nones w y))

@[simp] theorem nonesAppendFun_castAdd {M N p q : ℕ} (u : cells M p) (w : cells N q)
    (x : Fin p) : nonesAppendFun u w (Fin.castAdd q x) = Fin.castAdd N (nones u x) := by
  rw [nonesAppendFun, Fin.addCases_left]

@[simp] theorem nonesAppendFun_natAdd {M N p q : ℕ} (u : cells M p) (w : cells N q)
    (y : Fin q) : nonesAppendFun u w (Fin.natAdd p y) = Fin.natAdd M (nones w y) := by
  rw [nonesAppendFun, Fin.addCases_right]

private theorem nonesAppendFun_strictMono {M N p q : ℕ} (u : cells M p) (w : cells N q) :
    StrictMono (nonesAppendFun u w) := by
  intro a b hab
  induction a using Fin.addCases with
  | left a => induction b using Fin.addCases with
    | left b =>
        simp only [nonesAppendFun_castAdd, Fin.lt_def, Fin.val_castAdd] at hab ⊢
        have := (nones u).strictMono (a := a) (b := b); simp only [Fin.lt_def] at this
        exact this hab
    | right b => simp only [nonesAppendFun_castAdd, nonesAppendFun_natAdd, Fin.lt_def,
        Fin.val_castAdd, Fin.val_natAdd]; have := (nones u a).isLt; omega
  | right a => induction b using Fin.addCases with
    | left b =>
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hab
        have := (nones u b).isLt; omega
    | right b =>
        simp only [nonesAppendFun_natAdd, Fin.lt_def, Fin.val_natAdd] at hab ⊢
        have := (nones w).strictMono (a := a) (b := b); simp only [Fin.lt_def] at this
        omega

/-- The `none`-positions of `append u w`: the left-block ones via `castAdd ∘ nones u`,
the right-block ones via `natAdd ∘ nones w`. -/
theorem nones_append {M N p q : ℕ} (u : cells M p) (w : cells N q) :
    (nones (append u w) : Fin (p + q) → Fin (M + N)) = nonesAppendFun u w := by
  refine (Finset.orderEmbOfFin_unique (append u w).prop (fun y => ?_)
    (nonesAppendFun_strictMono u w)).symm
  rw [mem_noneSet]
  refine Fin.addCases (fun x => ?_) (fun x => ?_) y
  · rw [nonesAppendFun_castAdd, append_val, Fin.append_left, ← mem_noneSet]
    exact Finset.orderEmbOfFin_mem _ u.prop x
  · rw [nonesAppendFun_natAdd, append_val, Fin.append_right, ← mem_noneSet]
    exact Finset.orderEmbOfFin_mem _ w.prop x

theorem nones_append_castAdd {M N p q : ℕ} (u : cells M p) (w : cells N q) (x : Fin p) :
    nones (append u w) (Fin.castAdd q x) = Fin.castAdd N (nones u x) := by
  rw [show (nones (append u w)) (Fin.castAdd q x)
    = (nones (append u w) : Fin (p + q) → Fin (M + N)) (Fin.castAdd q x) from rfl,
    nones_append, nonesAppendFun_castAdd]

theorem nones_append_natAdd {M N p q : ℕ} (u : cells M p) (w : cells N q) (y : Fin q) :
    nones (append u w) (Fin.natAdd p y) = Fin.natAdd M (nones w y) := by
  rw [show (nones (append u w)) (Fin.natAdd p y)
    = (nones (append u w) : Fin (p + q) → Fin (M + N)) (Fin.natAdd p y) from rfl,
    nones_append, nonesAppendFun_natAdd]

/-! ### `Function.update` commuting with `Fin.append` -/

/-- Updating the left block of an `append` commutes through `Fin.append`. -/
theorem update_append_castAdd {M N : ℕ} (u : Fin M → Option Bool) (w : Fin N → Option Bool)
    (p : Fin M) (e : Option Bool) :
    Fin.append (Function.update u p e) w
      = Function.update (Fin.append u w) (Fin.castAdd N p) e := by
  funext j
  induction j using Fin.addCases with
  | left j =>
      rw [Fin.append_left]
      by_cases hj : j = p
      · subst hj; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne (by
          simpa [Fin.castAdd_injective M N |>.eq_iff] using hj), Fin.append_left]
  | right j =>
      rw [Fin.append_right, Function.update_of_ne (by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        have := p.isLt; omega), Fin.append_right]

/-- Updating the right block of an `append` commutes through `Fin.append`. -/
theorem update_append_natAdd {M N : ℕ} (u : Fin M → Option Bool) (w : Fin N → Option Bool)
    (p : Fin N) (e : Option Bool) :
    Fin.append u (Function.update w p e) = Function.update (Fin.append u w) (Fin.natAdd M p) e := by
  funext j
  induction j using Fin.addCases with
  | left j =>
      rw [Fin.append_left, Function.update_of_ne (by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        intro h; have := j.isLt; omega), Fin.append_left]
  | right j =>
      rw [Fin.append_right]
      by_cases hj : j = p
      · subst hj; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne (by
          simpa [Fin.natAdd_injective M N |>.eq_iff] using hj), Fin.append_right]

/-! ### A grade cast for cells

Appending shifts grades by sums whose associativity is not definitional
(`(p+1)+q` vs `(p+q)+1`).  `gradeCast` relabels a cell's grade along a numeric
equality, leaving the underlying vector untouched; `sapp` and `append` are then
shown to commute with it. -/

/-- Relabel the grade of a cell along `h : j = k` (the underlying vector is
unchanged). -/
def gradeCast {n j k : ℕ} (h : j = k) (a : cells n j) : cells n k :=
  ⟨a.val, h ▸ a.prop⟩

@[simp] theorem gradeCast_val {n j k : ℕ} (h : j = k) (a : cells n j) :
    (gradeCast h a).val = a.val := rfl

@[simp] theorem gradeCast_rfl {n j : ℕ} (a : cells n j) : gradeCast rfl a = a := rfl

/-- `sapp` only depends on a cell through its underlying vector, so it commutes
with `gradeCast`. -/
theorem sapp_gradeCast {P n j k : ℕ} (c : cells P n) (h : j = k) (a : cells n j) :
    sapp c (gradeCast h a) = gradeCast h (sapp c a) := by
  subst h; rfl

/-! ### Faces commute with `append` (one block at a time)

The append-of-cells shifts grades by sums whose associativity is not
definitional; the elaborator also mis-decomposes a face index `Fin.natAdd p j :
Fin (p + (q+1))` against the expected `Fin (?k + 1)` by syntactic `HAdd`-matching
(splitting `q + 1` rather than reducing `p + (q + 1)` to `(p + q) + 1`).  The two
index helpers below pin the grade by carrying the reduced type as their return
type. -/

/-- A right-block face index, with its grade presented as the reduced `(p+q)+1`. -/
def faceIdxR (p : ℕ) {q : ℕ} (j : Fin (q + 1)) : Fin ((p + q) + 1) := (Fin.natAdd p j).cast rfl

/-- A left-block face index, with its grade presented as the reduced `(p+q)+1`. -/
def faceIdxL {p : ℕ} (i : Fin (p + 1)) (q : ℕ) : Fin ((p + q) + 1) :=
  (Fin.castAdd q i).cast (Nat.add_right_comm p 1 q)

@[simp] theorem faceIdxR_val (p : ℕ) {q : ℕ} (j : Fin (q + 1)) :
    (faceIdxR p j).val = p + j.val := rfl

@[simp] theorem faceIdxL_val {p : ℕ} (i : Fin (p + 1)) (q : ℕ) :
    (faceIdxL i q).val = i.val := rfl

/-- Facing a right-block coordinate commutes with `append` (grade-definitional:
`p + (q+1) = (p+q) + 1`). -/
theorem face_append_right {M N p q : ℕ} (ε : Bool) (j : Fin (q + 1)) (a₁ : cells M p)
    (a₂ : cells N (q + 1)) :
    append a₁ (face ε j a₂)
      = face ε (faceIdxR p j) (gradeCast (Nat.add_succ p q) (append a₁ a₂)) := by
  apply Subtype.ext
  rw [append_val, face_val, face_val, gradeCast_val, append_val]
  have hn : nones (gradeCast (Nat.add_succ p q) (append a₁ a₂)) (faceIdxR p j)
      = nones (append a₁ a₂) (Fin.natAdd p j) := by
    simp only [nones, gradeCast_val, Finset.orderEmbOfFin_eq_orderEmbOfFin_iff, faceIdxR_val,
      Fin.val_natAdd]
  rw [hn, nones_append_natAdd, update_append_natAdd]

/-- Facing a left-block coordinate commutes with `append`: the left-block face of
`append a₁ a₂` is computed after relabelling the grade `(p+1)+q` to `(p+q)+1`. -/
theorem face_append_left {M N p q : ℕ} (ε : Bool) (i : Fin (p + 1)) (a₁ : cells M (p + 1))
    (a₂ : cells N q) :
    append (face ε i a₁) a₂
      = face ε (faceIdxL i q)
          (gradeCast (Nat.add_right_comm p 1 q) (append a₁ a₂)) := by
  apply Subtype.ext
  rw [append_val, face_val, face_val, gradeCast_val, append_val]
  have hn : nones (gradeCast (Nat.add_right_comm p 1 q) (append a₁ a₂)) (faceIdxL i q)
      = nones (append a₁ a₂) (Fin.castAdd q i) := by
    simp only [nones, gradeCast_val, Finset.orderEmbOfFin_eq_orderEmbOfFin_iff, faceIdxL_val,
      Fin.val_castAdd]
  rw [hn, nones_append_castAdd, update_append_castAdd]

/-! ### The combinatorial crux: `sapp` commutes with `append`

The iterated-face map commutes with the juxtaposition of cells.  Proved in two
stages by peeling one block at a time, using naturality of `sapp` (`sapp_face`)
and the one-block face/append commutation lemmas.  The right block peels
grade-definitionally; the left block peels through the grade cast. -/

/-- Crux, right-block-trivial stage: `sapp` commutes with appending when the right
argument is a top cell.  Proved by peeling the left block (strong induction on the
left codimension `M - p`). -/
theorem app_append_topRight {P Q M N : ℕ} (c₁ : cells P M) (c₂ : cells Q N) {p : ℕ}
    (a₁ : cells M p) :
    sapp (append c₁ c₂) (append a₁ (topCell N)) = append (sapp c₁ a₁) c₂ := by
  induction hd : M - p using Nat.strong_induction_on generalizing p a₁ with
  | _ d ih =>
    rcases Nat.lt_or_ge p M with hlt | hge
    · -- peel the smallest fixed coordinate of `a₁` (left block)
      set εV := minFixedVal a₁ hlt
      set iI := minFixedIdx a₁ hlt
      have hstep : sapp (append c₁ c₂) (append (freeMin a₁ hlt) (topCell N))
          = append (sapp c₁ (freeMin a₁ hlt)) c₂ := ih (M - (p + 1)) (by omega) (freeMin a₁ hlt) rfl
      calc sapp (append c₁ c₂) (append a₁ (topCell N))
          = sapp (append c₁ c₂) (append (face εV iI (freeMin a₁ hlt)) (topCell N)) := by
            rw [face_freeMin]
        _ = sapp (append c₁ c₂)
              (face εV (faceIdxL iI N)
                (gradeCast (Nat.add_right_comm p 1 N)
                  (append (freeMin a₁ hlt) (topCell N)))) := by rw [face_append_left]
        _ = face εV (faceIdxL iI N)
              (sapp (append c₁ c₂)
                (gradeCast (Nat.add_right_comm p 1 N)
                  (append (freeMin a₁ hlt) (topCell N)))) := by rw [sapp_face]
        _ = face εV (faceIdxL iI N)
              (gradeCast (Nat.add_right_comm p 1 N)
                (sapp (append c₁ c₂) (append (freeMin a₁ hlt) (topCell N)))) := by
            rw [sapp_gradeCast]
        _ = face εV (faceIdxL iI N)
              (gradeCast (Nat.add_right_comm p 1 N)
                (append (sapp c₁ (freeMin a₁ hlt)) c₂)) := by rw [hstep]
        _ = append (face εV iI (sapp c₁ (freeMin a₁ hlt))) c₂ := by
            rw [face_append_left]
        _ = append (sapp c₁ (face εV iI (freeMin a₁ hlt))) c₂ := by rw [sapp_face]
        _ = append (sapp c₁ a₁) c₂ := by rw [face_freeMin]
    · -- top cell on the left too: `p = M`, `a₁ = topCell M`
      have hpm : p = M := le_antisymm (cells_card_le a₁) hge
      subst hpm
      rw [eq_topCell a₁]
      have htop : append (topCell p) (topCell N) = topCell (p + N) := by
        apply Subtype.ext
        rw [append_val]
        funext j
        induction j using Fin.addCases with
        | left j => rw [Fin.append_left]; rfl
        | right j => rw [Fin.append_right]; rfl
      rw [htop, sapp_topCell, sapp_topCell]

/-- **The combinatorial crux** (analogue of `StdCube.app_snocFree`): the
iterated-face map `sapp` commutes with the juxtaposition `append` of cells.
Proved by peeling the right block (strong induction on the right codimension
`N - q`), reducing to `app_append_topRight`. -/
theorem app_append {P Q M N : ℕ} (c₁ : cells P M) (c₂ : cells Q N) {p q : ℕ}
    (a₁ : cells M p) (a₂ : cells N q) :
    sapp (append c₁ c₂) (append a₁ a₂) = append (sapp c₁ a₁) (sapp c₂ a₂) := by
  induction hd : N - q using Nat.strong_induction_on generalizing q a₂ with
  | _ d ih =>
    rcases Nat.lt_or_ge q N with hlt | hge
    · -- peel the smallest fixed coordinate of `a₂` (right block)
      set εV := minFixedVal a₂ hlt
      set iI := minFixedIdx a₂ hlt
      have hstep : sapp (append c₁ c₂) (append a₁ (freeMin a₂ hlt))
          = append (sapp c₁ a₁) (sapp c₂ (freeMin a₂ hlt)) :=
        ih (N - (q + 1)) (by omega) (freeMin a₂ hlt) rfl
      calc sapp (append c₁ c₂) (append a₁ a₂)
          = sapp (append c₁ c₂) (append a₁ (face εV iI (freeMin a₂ hlt))) := by
            rw [face_freeMin]
        _ = sapp (append c₁ c₂)
              (face εV (faceIdxR p iI) (gradeCast (Nat.add_succ p q)
                (append a₁ (freeMin a₂ hlt)))) := by rw [face_append_right]
        _ = face εV (faceIdxR p iI)
              (sapp (append c₁ c₂)
                (gradeCast (Nat.add_succ p q) (append a₁ (freeMin a₂ hlt)))) := by rw [sapp_face]
        _ = face εV (faceIdxR p iI)
              (gradeCast (Nat.add_succ p q)
                (sapp (append c₁ c₂) (append a₁ (freeMin a₂ hlt)))) := by rw [sapp_gradeCast]
        _ = face εV (faceIdxR p iI)
              (gradeCast (Nat.add_succ p q)
                (append (sapp c₁ a₁) (sapp c₂ (freeMin a₂ hlt)))) := by rw [hstep]
        _ = append (sapp c₁ a₁) (face εV iI (sapp c₂ (freeMin a₂ hlt))) := by
            rw [face_append_right]
        _ = append (sapp c₁ a₁) (sapp c₂ (face εV iI (freeMin a₂ hlt))) := by rw [sapp_face]
        _ = append (sapp c₁ a₁) (sapp c₂ a₂) := by rw [face_freeMin]
    · -- top cell on the right: `q = N`, reduce to `app_append_topRight`
      have hqn : q = N := le_antisymm (cells_card_le a₂) hge
      subst hqn
      rw [eq_topCell a₂, app_append_topRight, sapp_topCell]

/-! ### `append` of top cells, identities, and reindexing -/

/-- The juxtaposition of two top cells is the top cell. -/
theorem append_topCell (M N : ℕ) : append (topCell M) (topCell N) = topCell (M + N) := by
  apply Subtype.ext
  rw [append_val]
  funext j
  induction j using Fin.addCases with
  | left j => rw [Fin.append_left]; rfl
  | right j => rw [Fin.append_right]; rfl

/-- `append` of two cells, reassociated, equals the reassociation of the appended
cells: the underlying-vector content of the associator coherence. -/
theorem append_assoc {P₁ P₂ P₃ k₁ k₂ k₃ : ℕ} (a : cells P₁ k₁) (b : cells P₂ k₂)
    (c : cells P₃ k₃) :
    (append (append a b) c).val
      = (append a (append b c)).val ∘ Fin.cast (Nat.add_assoc P₁ P₂ P₃) := by
  rw [append_val, append_val, append_val, append_val, Fin.append_assoc]

end StdCube

/-! ## The concatenation monoidal structure on `Box`

`⟨m⟩ ⊗ ⟨n⟩ = ⟨m + n⟩`, unit `⟨0⟩ = □⁰`, and on morphisms the juxtaposition of
precubical cube maps via `StdCube.append` and the cube Yoneda lemma.  All
coherences are checked through `ev` (the cube Yoneda forward map is injective), so
they reduce to `StdCube.append`/`Fin.append` identities. -/

namespace Box

open StdCube
open scoped MonoidalCategory

/-! ### `ev`-extensionality and the building blocks -/

/-- Two box morphisms are equal iff they agree on the top cell (cube Yoneda). -/
theorem ev_injective {a b : Box} {f g : a ⟶ b} (h : ev f = ev g) : f = g :=
  (StdCube.cubeRepr (stdPre b.dim) a.dim).injective h

/-- `ev` of a composite peels the first factor. -/
theorem ev_comp {a b c : Box} (f : a ⟶ b) (g : b ⟶ c) : ev (f ≫ g) = sapp (ev g) (ev f) :=
  app_unique g rfl (ev f)

/-- `ev` of the identity is the top cell. -/
theorem ev_id (a : Box) : ev (𝟙 a) = topCell a.dim := rfl

/-- The reindexing box morphism `⟨m⟩ ⟶ ⟨n⟩` for a dimension equality `m = n`:
the `eqToHom` of the underlying object equality. -/
def reHom {m n : ℕ} (hd : m = n) : Box.ob m ⟶ Box.ob n := eqToHom (congrArg Box.ob hd)

@[simp] theorem reHom_rfl (n : ℕ) : reHom (rfl : n = n) = 𝟙 (Box.ob n) := by
  rw [reHom]; simp

/-- `ev (reHom hd)` is the all-`none` cell relabelled along `hd`. -/
theorem ev_reHom {m n : ℕ} (hd : m = n) : ev (reHom hd) = hd ▸ topCell m := by
  subst hd; rw [reHom_rfl, ev_id]

/-- The underlying map of a reindexing iso transports cells along `hd`. -/
theorem app_reHom {m n : ℕ} (hd : m = n) {k : ℕ} (x : cells m k) :
    PrecubicalConstructions.Hom.app (reHom hd) k x = hd ▸ x := by
  subst hd; rw [reHom_rfl]; rfl

/-- Postcomposing with a reindexing iso relabels the value of `ev` by `Fin.cast`
along the ambient equality `hd`. -/
theorem ev_comp_reHom_val {a : Box} {m n : ℕ} (f : a ⟶ Box.ob m) (hd : m = n) :
    (ev (f ≫ reHom hd)).val = (ev f).val ∘ Fin.cast hd.symm := by
  subst hd
  rw [reHom_rfl]
  have : f ≫ 𝟙 (Box.ob m) = f := Category.comp_id f
  rw [show ev (f ≫ 𝟙 (Box.ob m)) = ev f from congrArg ev this]
  rfl

/-- Precomposing with a reindexing iso relabels the value of `ev` by `Fin.cast`
along the grade equality `hd.symm`. -/
theorem ev_reHom_comp_val {b : Box} {m n : ℕ} (hd : m = n) (g : Box.ob n ⟶ b) :
    (ev (reHom hd ≫ g)).val = (ev g).val := by
  subst hd
  rw [reHom_rfl]
  rw [show ev (𝟙 (Box.ob m) ≫ g) = ev g from congrArg ev (Category.id_comp g)]

/-! ### The monoidal-category data -/

/-- Tensor of box morphisms: juxtapose the cube maps via `append` of their values
on the top cell (cube Yoneda). -/
def tensorHom {a b c d : Box} (f : a ⟶ b) (g : c ⟶ d) :
    Box.ob (a.dim + c.dim) ⟶ Box.ob (b.dim + d.dim) :=
  canonicalMap (append (ev f) (ev g))

@[simp] theorem ev_tensorHom {a b c d : Box} (f : a ⟶ b) (g : c ⟶ d) :
    ev (tensorHom f g) = append (ev f) (ev g) := ev_canonicalMap _

instance monoidalStruct : MonoidalCategoryStruct Box where
  tensorObj a b := Box.ob (a.dim + b.dim)
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorHom f g := tensorHom f g
  tensorUnit := Box.ob 0
  associator a b c := eqToIso (congrArg Box.ob (Nat.add_assoc a.dim b.dim c.dim))
  leftUnitor a := eqToIso (congrArg Box.ob (Nat.zero_add a.dim))
  rightUnitor a := eqToIso (congrArg Box.ob (Nat.add_zero a.dim))

@[simp] theorem tensorObj_dim (a b : Box) : (a ⊗ b).dim = a.dim + b.dim := rfl

theorem tensorHom_eq {a b c d : Box} (f : a ⟶ b) (g : c ⟶ d) : f ⊗ₘ g = tensorHom f g := rfl

theorem whiskerLeft_eq (X : Box) {b c : Box} (g : b ⟶ c) : X ◁ g = tensorHom (𝟙 X) g := rfl

theorem whiskerRight_eq {a b : Box} (f : a ⟶ b) (Y : Box) : f ▷ Y = tensorHom f (𝟙 Y) := rfl

theorem associator_hom_eq (a b c : Box) :
    (α_ a b c).hom = reHom (Nat.add_assoc a.dim b.dim c.dim) := rfl

theorem leftUnitor_hom_eq (a : Box) : (λ_ a).hom = reHom (Nat.zero_add a.dim) := rfl

theorem rightUnitor_hom_eq (a : Box) : (ρ_ a).hom = reHom (Nat.add_zero a.dim) := rfl

/-! ### Functoriality of the tensor -/

/-- `id ⊗ id = id`. -/
theorem id_tensorHom_id (a b : Box) : tensorHom (𝟙 a) (𝟙 b) = 𝟙 (Box.ob (a.dim + b.dim)) := by
  apply ev_injective
  rw [ev_tensorHom, ev_id, ev_id, ev_id, append_topCell]

/-- Interchange: `(f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) = (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)`. -/
theorem tensorHom_comp_tensorHom {a₁ b₁ c₁ a₂ b₂ c₂ : Box}
    (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) (g₁ : b₁ ⟶ c₁) (g₂ : b₂ ⟶ c₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply PrecubicalConstructions.hom_ext
  intro k x
  change sapp (append (ev g₁) (ev g₂)) (sapp (append (ev f₁) (ev f₂)) x)
    = sapp (append (ev (f₁ ≫ g₁)) (ev (f₂ ≫ g₂))) x
  rw [sapp_comp, app_append, ev_comp f₁ g₁, ev_comp f₂ g₂]

/-! ### Naturality of the associator and unitors -/

/-- Naturality of the associator. -/
theorem associator_naturality {a₁ b₁ a₂ b₂ a₃ b₃ : Box}
    (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) (f₃ : a₃ ⟶ b₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (α_ b₁ b₂ b₃).hom
      = (α_ a₁ a₂ a₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply ev_injective
  rw [associator_hom_eq, associator_hom_eq]
  apply Subtype.ext
  erw [ev_comp_reHom_val, ev_reHom_comp_val]
  rw [ev_tensorHom, ev_tensorHom, ev_tensorHom, ev_tensorHom, append_assoc]
  funext j
  simp

/-- Naturality of the left unitor. -/
theorem leftUnitor_naturality {a b : Box} (f : a ⟶ b) :
    tensorHom (𝟙 (Box.ob 0)) f ≫ (λ_ b).hom = (λ_ a).hom ≫ f := by
  apply ev_injective
  rw [leftUnitor_hom_eq, leftUnitor_hom_eq]
  apply Subtype.ext
  erw [ev_comp_reHom_val, ev_reHom_comp_val]
  rw [ev_tensorHom, ev_id, append_val, Fin.append_left_nil _ _ (rfl : (Box.ob 0).dim = 0)]
  funext j
  simp

/-- Naturality of the right unitor. -/
theorem rightUnitor_naturality {a b : Box} (f : a ⟶ b) :
    tensorHom f (𝟙 (Box.ob 0)) ≫ (ρ_ b).hom = (ρ_ a).hom ≫ f := by
  apply ev_injective
  rw [rightUnitor_hom_eq, rightUnitor_hom_eq]
  apply Subtype.ext
  erw [ev_comp_reHom_val, ev_reHom_comp_val]
  rw [ev_tensorHom, ev_id, append_val, Fin.append_right_nil _ _ (rfl : (Box.ob 0).dim = 0)]
  funext j
  simp

/-! ### Whiskered reindexing isos are reindexing isos -/

/-- Left-whiskering a reindexing iso is a reindexing iso. -/
theorem whiskerLeft_reHom (X : Box) {m n : ℕ} (hd : m = n) :
    tensorHom (𝟙 X) (reHom hd) = reHom (congrArg (X.dim + ·) hd) := by
  subst hd
  apply ev_injective
  rw [reHom_rfl]
  rw [show (congrArg (X.dim + ·) (rfl : m = m)) = rfl from rfl, reHom_rfl]
  rw [ev_id, ev_tensorHom, ev_id, ev_id, append_topCell]

/-- Right-whiskering a reindexing iso is a reindexing iso. -/
theorem whiskerRight_reHom {m n : ℕ} (hd : m = n) (Y : Box) :
    tensorHom (reHom hd) (𝟙 Y) = reHom (congrArg (· + Y.dim) hd) := by
  subst hd
  apply ev_injective
  rw [reHom_rfl]
  rw [show (congrArg (· + Y.dim) (rfl : m = m)) = rfl from rfl, reHom_rfl]
  rw [ev_id, ev_tensorHom, ev_id, ev_id, append_topCell]

/-- Composition of reindexing isos. -/
theorem reHom_comp_reHom {m n p : ℕ} (h₁ : m = n) (h₂ : n = p) :
    reHom h₁ ≫ reHom h₂ = reHom (h₁.trans h₂) := by
  rw [reHom, reHom, reHom, eqToHom_trans]

/-- Any two reindexing isos with the same endpoints agree. -/
theorem reHom_eq {m n : ℕ} (h₁ h₂ : m = n) : reHom h₁ = reHom h₂ := rfl

/-! ### Pentagon and triangle

Every associator/unitor is a reindexing iso `reHom`; whiskering preserves this
(`whisker*_reHom`), and reindexing isos compose (`reHom_comp_reHom`) and only
depend on their endpoints (`reHom_eq`).  So both sides of each coherence collapse
to the *same* reindexing iso. -/

/-- The pentagon identity. -/
theorem pentagon (W X Y Z : Box) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom
      = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
  simp only [associator_hom_eq, whiskerLeft_eq, whiskerRight_eq, whiskerLeft_reHom,
    whiskerRight_reHom, tensorObj_dim, reHom_comp_reHom]

/-- The triangle identity. -/
theorem triangle (a b : Box) :
    (α_ a (Box.ob 0) b).hom ≫ a ◁ (λ_ b).hom = (ρ_ a).hom ▷ b := by
  simp only [associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq, whiskerLeft_eq,
    whiskerRight_eq, whiskerLeft_reHom, whiskerRight_reHom, reHom_comp_reHom]

/-! ### The monoidal category instance -/

/-- **The cube-concatenation monoidal structure on `Box`**: `⟨m⟩ ⊗ ⟨n⟩ = ⟨m + n⟩`,
unit `⟨0⟩ = □⁰`, tensor of morphisms = juxtaposition of precubical cube maps. -/
instance instMonoidalCategory : MonoidalCategory Box :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun a b => id_tensorHom_id a b)
    -- `id_tensorHom`/`tensorHom_id` hold definitionally (whiskerings *are* the
    -- corresponding tensorHoms), discharged by `ofTensorHom`'s default `cat_disch`.
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => tensorHom_comp_tensorHom f₁ f₂ g₁ g₂)
    (associator_naturality := fun f₁ f₂ f₃ => associator_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => leftUnitor_naturality f)
    (rightUnitor_naturality := fun f => rightUnitor_naturality f)
    (pentagon := fun W X Y Z => pentagon W X Y Z)
    (triangle := fun a b => triangle a b)

end Box
