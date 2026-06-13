import CubeChains.Box

/-!
# Representability of the standard cube (Yoneda for cubes)

The bridge `PrecubicalSet ≌ PrecubicalConstructions` rests on a single lemma:
the standard cube `□ⁿ` is *representable*, i.e. a precubical map `□ⁿ ⟶ K` is the
same data as an `n`-cell of `K`,

  `(□ⁿ ⟶ K) ≃ K.cells n`,

naturally in `n` (along `Box`) and `K`.  The forward map `ev` sends `f` to its
value `f.app n ⊤` on the top cell `⊤` (all coordinates free).  The inverse is the
*canonical map* `c ↦ canonicalMap c`, the unique precubical map sending `⊤` to
`c`, built from iterated faces of `c` at the fixed coordinates.

This file fixes the statement (`cubeRepr`).  The construction of the inverse is
the iterated-face computation flagged in `DESIGN.md`; it is the cube's Yoneda
lemma and is the remaining proof obligation of the topos bridge.
-/

open CategoryTheory

namespace StdCube

/-- The top cell of `□ⁿ`: every coordinate free (`none`), the unique `n`-cell. -/
def topCell (n : ℕ) : cells n n :=
  ⟨fun _ => none, by simp [noneSet]⟩

/-- The cube inclusion `Box ⥤ PrecubicalConstructions`, `[n] ↦ □ⁿ`.  Fully
faithful by construction, since `Box`'s homs *are* precubical maps of cubes. -/
def cubeι : Box ⥤ PrecubicalConstructions where
  obj b := stdPre b.dim
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `cubeι` is fully faithful: this holds definitionally, as `Box (m ⟶ n)` is by
definition `□^m ⟶ □^n`. -/
def cubeιFullyFaithful : cubeι.FullyFaithful where
  preimage f := f

/-- Evaluation of a precubical map out of `□ⁿ` at the top cell: an `n`-cell of `K`. -/
def ev {K : PrecubicalConstructions} {n : ℕ} (f : stdPre n ⟶ K) : K.cells n :=
  PrecubicalConstructions.Hom.app f n (topCell n)

/-! ### Cube combinatorics for the canonical map

To build `□ⁿ ⟶ K` from `c : K.cells n` we send a `k`-cell `a` of `□ⁿ` to the
iterated face of `c` obtained by facing out the *fixed* coordinates of `a`.  We
peel them one at a time, always taking the *smallest* fixed coordinate; the
facts below package that single peeling step. -/

/-- A `k`-cell of `□ⁿ` has at most `n` free coordinates. -/
theorem cells_card_le {n k : ℕ} (a : cells n k) : k ≤ n := by
  rw [← a.prop]
  calc (noneSet a.val).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := Finset.card_fin n

/-- A `k`-cell of `□ⁿ` with `k = n` is the top cell. -/
theorem eq_topCell {n : ℕ} (a : cells n n) : a = topCell n := by
  apply Subtype.ext
  funext j
  have huniv : noneSet a.val = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [a.prop, Fintype.card_fin])
  have : a.val j = none := by
    have : j ∈ noneSet a.val := huniv ▸ Finset.mem_univ j
    rwa [mem_noneSet] at this
  rw [this]; rfl

/-- The set of *fixed* (non-`none`) coordinates of a cell: the complement of the
`none`-set. -/
def fixedSet {n k : ℕ} (a : cells n k) : Finset (Fin n) := (noneSet a.val)ᶜ

theorem fixedSet_card {n k : ℕ} (a : cells n k) : (fixedSet a).card = n - k := by
  rw [fixedSet, Finset.card_compl, Fintype.card_fin, a.prop]

theorem fixedSet_nonempty {n k : ℕ} (a : cells n k) (h : k < n) : (fixedSet a).Nonempty := by
  rw [← Finset.card_pos, fixedSet_card]; omega

/-- Facing out coordinate `i` adds `nones a i` to the fixed set. -/
theorem fixedSet_face {n k : ℕ} (a : cells n (k + 1)) (ε : Bool) (i : Fin (k + 1)) :
    fixedSet (face ε i a) = insert (nones a i) (fixedSet a) := by
  rw [fixedSet, fixedSet, face_val, noneSet_update, Finset.compl_erase]

/-- The smallest fixed coordinate of a non-top cell. -/
def minFixed {n k : ℕ} (a : cells n k) (h : k < n) : Fin n :=
  (fixedSet a).min' (fixedSet_nonempty a h)

theorem minFixed_mem {n k : ℕ} (a : cells n k) (h : k < n) : minFixed a h ∈ fixedSet a :=
  Finset.min'_mem _ _

theorem minFixed_notMem {n k : ℕ} (a : cells n k) (h : k < n) : minFixed a h ∉ noneSet a.val := by
  have := minFixed_mem a h; rwa [fixedSet, Finset.mem_compl] at this

theorem minFixed_val_ne_none {n k : ℕ} (a : cells n k) (h : k < n) :
    a.val (minFixed a h) ≠ none := fun hc => minFixed_notMem a h (by rwa [mem_noneSet])

/-- The (boolean) value `c` takes at its smallest fixed coordinate. -/
def minFixedVal {n k : ℕ} (a : cells n k) (h : k < n) : Bool :=
  (a.val (minFixed a h)).get (Option.isSome_iff_ne_none.mpr (minFixed_val_ne_none a h))

theorem minFixed_val_eq {n k : ℕ} (a : cells n k) (h : k < n) :
    a.val (minFixed a h) = some (minFixedVal a h) := (Option.some_get _).symm

/-- Freeing the smallest fixed coordinate (setting it back to `none`): a
`(k+1)`-cell. -/
def freeMin {n k : ℕ} (a : cells n k) (h : k < n) : cells n (k + 1) :=
  ⟨Function.update a.val (minFixed a h) none, by
    have hp : minFixed a h ∉ noneSet a.val := minFixed_notMem a h
    have hset : noneSet (Function.update a.val (minFixed a h) none)
        = insert (minFixed a h) (noneSet a.val) := by
      ext j
      rw [mem_noneSet]
      by_cases hj : j = minFixed a h
      · subst hj; simp [Function.update_self]
      · rw [Function.update_of_ne hj, Finset.mem_insert, mem_noneSet]; simp [hj]
    rw [hset, Finset.card_insert_of_notMem hp, a.prop]⟩

@[simp] theorem freeMin_val {n k : ℕ} (a : cells n k) (h : k < n) :
    (freeMin a h).val = Function.update a.val (minFixed a h) none := rfl

theorem noneSet_freeMin {n k : ℕ} (a : cells n k) (h : k < n) :
    noneSet (freeMin a h).val = insert (minFixed a h) (noneSet a.val) := by
  rw [freeMin_val]
  ext j
  rw [mem_noneSet]
  by_cases hj : j = minFixed a h
  · subst hj; simp [Function.update_self]
  · rw [Function.update_of_ne hj, Finset.mem_insert, mem_noneSet]; simp [hj]

theorem minFixed_mem_free {n k : ℕ} (a : cells n k) (h : k < n) :
    minFixed a h ∈ noneSet (freeMin a h).val := by
  rw [mem_noneSet, freeMin_val, Function.update_self]

/-- The index of a `none`-coordinate `x` of `a` among the `k` free positions. -/
def nonesIdx {n k : ℕ} (a : cells n k) (x : Fin n) (hx : x ∈ noneSet a.val) : Fin k :=
  (Finset.orderIsoOfFin (noneSet a.val) a.prop).symm ⟨x, hx⟩

theorem nones_nonesIdx {n k : ℕ} (a : cells n k) (x : Fin n) (hx : x ∈ noneSet a.val) :
    nones a (nonesIdx a x hx) = x := by
  change (noneSet a.val).orderEmbOfFin a.prop (nonesIdx a x hx) = x
  rw [← Finset.coe_orderIsoOfFin_apply, nonesIdx, OrderIso.apply_symm_apply]

/-- The index, among the free positions of `freeMin a h`, of the coordinate we just
freed. -/
def minFixedIdx {n k : ℕ} (a : cells n k) (h : k < n) : Fin (k + 1) :=
  nonesIdx (freeMin a h) (minFixed a h) (minFixed_mem_free a h)

theorem nones_minFixedIdx {n k : ℕ} (a : cells n k) (h : k < n) :
    nones (freeMin a h) (minFixedIdx a h) = minFixed a h :=
  nones_nonesIdx _ _ _

/-- Refacing the freed coordinate recovers `a`: `a` is the `minFixedIdx`-face of
`freeMin a`. -/
theorem face_freeMin {n k : ℕ} (a : cells n k) (h : k < n) :
    face (minFixedVal a h) (minFixedIdx a h) (freeMin a h) = a := by
  apply Subtype.ext
  rw [face_val, nones_minFixedIdx, freeMin_val, Function.update_idem,
    ← minFixed_val_eq a h, Function.update_eq_self]

/-! ### The iterated-face map

`appAux c d a` faces `c` out at the `d = n - k` fixed coordinates of the
`k`-cell `a`, peeling the smallest one each step.  We recurse structurally on the
*number of fixed coordinates* `d`, carrying the equation `k + d = n`. -/

/-- The iterated-face value of `c : K.cells n` along a `k`-cell `a` of `□ⁿ` with
`k + d = n`: peel the `d` fixed coordinates of `a`, smallest first. -/
def appAux {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    (d : ℕ) → {k : ℕ} → (a : cells n k) → k + d = n → K.cells k
  | 0,     _, _, h => cast (congrArg K.cells h.symm) c
  | d + 1, _, a, h =>
      K.face (minFixedVal a (by omega)) (minFixedIdx a (by omega))
        (appAux c d (freeMin a (by omega)) (by omega))

/-- The peeling step of `appAux`: defining equation at `d + 1`. -/
theorem appAux_succ {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) (d : ℕ) {k : ℕ}
    (a : cells n k) (h : k + (d + 1) = n) :
    appAux c (d + 1) a h
      = K.face (minFixedVal a (by omega)) (minFixedIdx a (by omega))
          (appAux c d (freeMin a (by omega)) (by omega)) := rfl

/-- The iterated-face map underlying the canonical precubical map: send a
`k`-cell `a` to the face of `c` at the fixed coordinates of `a`. -/
def app {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) {k : ℕ} (a : cells n k) :
    K.cells k :=
  appAux c (n - k) a (by have := cells_card_le a; omega)

/-- `appAux` does not depend on the choice of `d` (it is forced to `n - k`). -/
theorem appAux_eq_app {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) (d : ℕ) {k : ℕ}
    (a : cells n k) (h : k + d = n) : appAux c d a h = app c a := by
  have hd : d = n - k := by omega
  subst hd; rfl

/-- The canonical map sends the top cell to `c`. -/
theorem app_topCell {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    app c (topCell n) = c := by
  rw [← appAux_eq_app c 0 (topCell n) (by omega)]
  exact cast_eq _ c

/-- Unfolding `app` at a non-top cell: peel the smallest fixed coordinate. -/
theorem app_unfold {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n) (a : cells n k)
    (h : k < n) :
    app c a = K.face (minFixedVal a h) (minFixedIdx a h) (app c (freeMin a h)) := by
  rw [← appAux_eq_app c ((n - (k + 1)) + 1) a (by omega), appAux_succ,
    appAux_eq_app c (n - (k + 1)) (freeMin a h) (by omega)]

/-! ### Naturality of the iterated-face map

The crux: `app c` commutes with all faces.  The "easy" case is when the
coordinate being faced is already the smallest fixed coordinate of `face ε i a`;
otherwise we commute past the smaller fixed coordinate using the precubical
identity `face_face` and induct. -/

/-- Naturality when the faced coordinate `i` is the smallest fixed coordinate. -/
theorem app_face_caseA {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n)
    (a : cells n (k + 1)) (ε : Bool) (i : Fin (k + 1)) (hlt : k < n)
    (hA : minFixed (face ε i a) hlt = nones a i) :
    app c (face ε i a) = K.face ε i (app c a) := by
  rw [app_unfold c (face ε i a) hlt]
  have hq : a.val (nones a i) = none := by
    rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a.prop i
  have hfree : freeMin (face ε i a) hlt = a := by
    apply Subtype.ext
    rw [freeMin_val, hA, face_val, Function.update_idem, ← hq, Function.update_eq_self]
  have hval : minFixedVal (face ε i a) hlt = ε := by
    have hv := minFixed_val_eq (face ε i a) hlt
    rw [hA, face_val, Function.update_self] at hv
    exact (Option.some.inj hv).symm
  have hidx : minFixedIdx (face ε i a) hlt = i := by
    have hni := nones_minFixedIdx (face ε i a) hlt
    rw [hA, hfree] at hni
    exact (nones a).injective hni
  rw [hfree, hval, hidx]

/-- `app c` commutes with all faces (induction on the number of fixed
coordinates). -/
theorem app_face_aux {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    ∀ (d : ℕ) {k : ℕ} (a : cells n (k + 1)), n - (k + 1) = d →
      ∀ (ε : Bool) (i : Fin (k + 1)), app c (face ε i a) = K.face ε i (app c a) := by
  intro d
  induction d with
  | zero =>
      intro k a hd ε i
      have hlt : k < n := by have := cells_card_le a; omega
      refine app_face_caseA c a ε i hlt ?_
      have hempty : fixedSet a = ∅ := by rw [← Finset.card_eq_zero, fixedSet_card]; omega
      have hmem : minFixed (face ε i a) hlt ∈ fixedSet (face ε i a) := minFixed_mem _ _
      rw [fixedSet_face, hempty, Finset.insert_empty, Finset.mem_singleton] at hmem
      exact hmem
  | succ d ih =>
      intro k a hd ε i
      have hlt : k < n := by have := cells_card_le a; omega
      by_cases hpq : minFixed (face ε i a) hlt = nones a i
      · exact app_face_caseA c a ε i hlt hpq
      · -- Case B: smallest fixed coordinate `p` of `face ε i a` is below `q = nones a i`.
        have hlt1 : k + 1 < n := by omega
        have hfs : fixedSet (face ε i a) = insert (nones a i) (fixedSet a) := fixedSet_face a ε i
        have hp_in_a : minFixed (face ε i a) hlt ∈ fixedSet a := by
          have hp_mem : minFixed (face ε i a) hlt ∈ insert (nones a i) (fixedSet a) := by
            rw [← hfs]; exact minFixed_mem _ _
          rcases Finset.mem_insert.mp hp_mem with h | h
          · exact absurd h hpq
          · exact h
        have h1 : minFixed a hlt1 ≤ minFixed (face ε i a) hlt := Finset.min'_le _ _ hp_in_a
        have h2 : minFixed (face ε i a) hlt ≤ minFixed a hlt1 := by
          refine Finset.min'_le _ _ ?_
          rw [hfs, Finset.mem_insert]; right; exact minFixed_mem _ _
        have hp_eq : minFixed a hlt1 = minFixed (face ε i a) hlt := le_antisymm h1 h2
        have hplt : minFixed a hlt1 < nones a i := by
          rw [hp_eq]
          refine lt_of_le_of_ne (Finset.min'_le _ _ ?_) hpq
          rw [hfs]; exact Finset.mem_insert_self _ _
        have hpa_ne_q : minFixed a hlt1 ≠ nones a i := ne_of_lt hplt
        -- The freed cell `freeMin a hlt1` and the index `i'` of `q = nones a i` in it.
        have hface_a : face (minFixedVal a hlt1) (minFixedIdx a hlt1) (freeMin a hlt1) = a :=
          face_freeMin a hlt1
        have hnι'p : nones (freeMin a hlt1) (minFixedIdx a hlt1) = minFixed a hlt1 :=
          nones_minFixedIdx a hlt1
        have hq_free_a : a.val (nones a i) = none := by
          rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a.prop i
        have hq_in_a0 : nones a i ∈ noneSet (freeMin a hlt1).val := by
          rw [noneSet_freeMin, Finset.mem_insert]
          right; rw [mem_noneSet]; exact hq_free_a
        have hni' : nones (freeMin a hlt1) (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0)
            = nones a i := nones_nonesIdx _ _ _
        -- C2: the freed cell of `face ε i a` is `face ε i' (freeMin a hlt1)`.
        have hC2 : freeMin (face ε i a) hlt
            = face ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0) (freeMin a hlt1) := by
          apply Subtype.ext
          rw [freeMin_val, face_val, ← hp_eq, face_val, hni', freeMin_val,
            Function.update_comm hpa_ne_q.symm]
        -- C3: the freed value matches.
        have hC3 : minFixedVal (face ε i a) hlt = minFixedVal a hlt1 := by
          have hb := minFixed_val_eq (face ε i a) hlt
          have ha2 := minFixed_val_eq a hlt1
          rw [← hp_eq, face_val, Function.update_of_ne hpa_ne_q] at hb
          rw [hb] at ha2
          exact Option.some.inj ha2
        -- index relations
        have hnιp : nones (face ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0) (freeMin a hlt1))
            (minFixedIdx (face ε i a) hlt) = minFixed a hlt1 := by
          rw [← hC2, nones_minFixedIdx]; exact hp_eq.symm
        have hR1 : (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0).succAbove
            (minFixedIdx (face ε i a) hlt) = minFixedIdx a hlt1 := by
          have hh := hnιp
          rw [face_nones, ← hnι'p] at hh
          exact (nones (freeMin a hlt1)).injective hh
        have hR2 : (minFixedIdx a hlt1).succAbove i
            = nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
          have hh : nones a i = nones (freeMin a hlt1) ((minFixedIdx a hlt1).succAbove i) := by
            rw [← face_nones (minFixedVal a hlt1), hface_a]
          rw [← hni'] at hh
          exact ((nones (freeMin a hlt1)).injective hh).symm
        have hR3 : minFixedIdx a hlt1 < nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
          rw [← (nones (freeMin a hlt1)).lt_iff_lt, hnι'p, hni']; exact hplt
        have hcast : minFixedIdx a hlt1 = (minFixedIdx (face ε i a) hlt).castSucc := by
          have hlt' : (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0).succAbove
              (minFixedIdx (face ε i a) hlt) < nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
            rw [hR1]; exact hR3
          have hc := (Fin.succAbove_lt_iff_castSucc_lt _ _).mp hlt'
          rw [← hR1, Fin.succAbove_of_castSucc_lt _ _ hc]
        have hsucc : nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 = i.succ := by
          have hlt' : minFixedIdx a hlt1 < (minFixedIdx a hlt1).succAbove i := by
            rw [hR2]; exact hR3
          have hc := (Fin.lt_succAbove_iff_le_castSucc _ _).mp hlt'
          rw [← hR2, Fin.succAbove_of_le_castSucc _ _ hc]
        have hle : minFixedIdx (face ε i a) hlt ≤ i := by
          have hlt' : (minFixedIdx (face ε i a) hlt).castSucc < i.succ := by
            rw [← hcast, ← hsucc]; exact hR3
          exact Fin.castSucc_lt_succ_iff.mp hlt'
        -- assemble
        rw [app_unfold c (face ε i a) hlt, hC3, hC2,
          ih (freeMin a hlt1) (by omega) ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0),
          app_unfold c a hlt1, hsucc, hcast]
        exact K.face_face (minFixedVal a hlt1) ε hle (app c (freeMin a hlt1))

/-- Naturality of `app`: it commutes with every face. -/
theorem app_face {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n) (a : cells n (k + 1))
    (ε : Bool) (i : Fin (k + 1)) : app c (face ε i a) = K.face ε i (app c a) :=
  app_face_aux c (n - (k + 1)) a rfl ε i

/-! ### Uniqueness and the canonical map -/

/-- Any precubical map agreeing with `c` on the top cell is `app c`: built from
faces, peeling the smallest fixed coordinate. -/
theorem app_unique {K : PrecubicalConstructions} {n : ℕ} {c : K.cells n} (g : stdPre n ⟶ K)
    (hg : PrecubicalConstructions.Hom.app g n (topCell n) = c) :
    ∀ {k : ℕ} (a : cells n k), PrecubicalConstructions.Hom.app g k a = app c a := by
  intro k a
  induction hk : n - k using Nat.strong_induction_on generalizing k a with
  | _ d ih =>
    rcases Nat.lt_or_ge k n with hlt | hge
    · -- non-top: peel the smallest fixed coordinate and use the induction hypothesis
      have hstep : PrecubicalConstructions.Hom.app g (k + 1) (freeMin a hlt)
          = app c (freeMin a hlt) := ih (n - (k + 1)) (by omega) (freeMin a hlt) rfl
      calc PrecubicalConstructions.Hom.app g k a
          = PrecubicalConstructions.Hom.app g k
              (face (minFixedVal a hlt) (minFixedIdx a hlt) (freeMin a hlt)) := by
            rw [face_freeMin]
        _ = K.face (minFixedVal a hlt) (minFixedIdx a hlt)
              (PrecubicalConstructions.Hom.app g (k + 1) (freeMin a hlt)) :=
            g.app_face (minFixedVal a hlt) (minFixedIdx a hlt) (freeMin a hlt)
        _ = K.face (minFixedVal a hlt) (minFixedIdx a hlt) (app c (freeMin a hlt)) := by
            rw [hstep]
        _ = app c a := (app_unfold c a hlt).symm
    · -- top cell: `k = n`, so `a = topCell n`
      have hkn : k = n := le_antisymm (cells_card_le a) hge
      subst hkn
      rw [eq_topCell a, hg, app_topCell]

/-- The canonical precubical map `□ⁿ ⟶ K` determined by an `n`-cell `c`: the
unique map sending the top cell to `c`, built from iterated faces of `c` at the
fixed coordinates (the inverse half of the cube's Yoneda lemma `cubeRepr`). -/
def canonicalMap {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) : stdPre n ⟶ K where
  app _k a := app c a
  app_face ε i a := app_face c a ε i

@[simp] theorem canonicalMap_app {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n)
    (a : cells n k) : PrecubicalConstructions.Hom.app (canonicalMap c) k a = app c a := rfl

/-- **Representability of the standard cube** (cube Yoneda): a precubical map out
of `□ⁿ` is the same data as an `n`-cell of `K`.  Forward map is `ev`; inverse is
`canonicalMap`. -/
def cubeRepr (K : PrecubicalConstructions) (n : ℕ) :
    (stdPre n ⟶ K) ≃ K.cells n where
  toFun := ev
  invFun := canonicalMap
  left_inv f := by
    apply PrecubicalConstructions.hom_ext
    intro k a
    exact (app_unique f rfl a).symm
  right_inv c := app_topCell c

end StdCube
