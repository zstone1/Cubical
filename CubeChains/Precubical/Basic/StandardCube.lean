import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# Precubical/Basic/StandardCube

Sign-vector algebra: a `k`-cell of `□ᴺ` is `c : Fin N → Option Bool` with exactly `k` free
(`none`) coordinates (`none = ∗`, `some false = 0`, `some true = 1`).  Three operations, in
dependency order: `faceCell ε i` substitutes `some ε` for the `i`-th `none` (`nones` enumerates
those positions, `nonesIdx` inverts it, and `face_nones` is the `succAbove` crux behind the
precubical identity); `freeMin` peels the *smallest fixed* coordinate, giving `Cell.peelRec`;
`subst c a` plugs `a` into the free coordinates of `c` — associative, unital and face-natural,
hence composition in `Box`.
-/

open CategoryTheory

namespace StdCube

variable {N : ℕ}

/-! ### Cells and their free coordinates -/

/-- The set of `none`-coordinates (the "∗" positions, the free directions) of a
raw cell `c : Fin N → Option Bool`. -/
def noneSet (c : Fin N → Option Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun j => c j = none)

@[simp] theorem mem_noneSet {c : Fin N → Option Bool} {j : Fin N} :
    j ∈ noneSet c ↔ c j = none := by simp [noneSet]

/-- Substituting a non-`none` value at `p` removes `p` from the `none`-set. -/
theorem noneSet_update (c : Fin N → Option Bool) (p : Fin N) (ε : Bool) :
    noneSet (Function.update c p (some ε)) = (noneSet c).erase p := by
  ext j
  rw [mem_noneSet, Finset.mem_erase, mem_noneSet]
  by_cases hj : j = p
  · subst hj; simp
  · rw [Function.update_of_ne hj]; simp [hj]

/-- Freeing a coordinate adds it to the `none`-set — the `none` sibling of `noneSet_update`. -/
theorem noneSet_update_none (c : Fin N → Option Bool) (p : Fin N) :
    noneSet (Function.update c p none) = insert p (noneSet c) := by
  ext j
  rw [mem_noneSet]
  by_cases hj : j = p
  · subst hj; simp [Function.update_self]
  · rw [Function.update_of_ne hj, Finset.mem_insert, mem_noneSet]; simp [hj]

/-- The `k`-cells of the standard `N`-cube: functions `Fin N → Option Bool` with
exactly `k` free (`none`) coordinates. -/
def Cell (N k : ℕ) : Type :=
  { c : Fin N → Option Bool // (noneSet c).card = k }

instance instDecidableEqCell (N k : ℕ) : DecidableEq (Cell N k) :=
  inferInstanceAs (DecidableEq {c : Fin N → Option Bool // (noneSet c).card = k})

/-- The point has at most one cell in each dimension: a sign vector on `Fin 0` is the empty
function. -/
instance instSubsingletonCell0 (k : ℕ) : Subsingleton (Cell 0 k) :=
  ⟨fun _ _ => Subtype.ext (funext fun i => i.elim0)⟩

/-- A cube has no `k`-cell above its dimension: `Cell N k` is empty for `k > N`. -/
instance instIsEmptyCell {N k : ℕ} (h : N < k) : IsEmpty (Cell N k) :=
  ⟨fun c => absurd (c.prop ▸ (Finset.card_le_univ _).trans_eq (Finset.card_fin N)) (by omega)⟩

/-- A `k`-cell of `□ⁿ` has at most `n` free coordinates. -/
theorem cells_card_le {n k : ℕ} (a : Cell n k) : k ≤ n := by
  rw [← a.prop]
  calc (noneSet a.val).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := Finset.card_fin n

/-- The order embedding of the `k` `none`-positions of a `k`-cell. -/
def nones {k : ℕ} (c : Cell N k) : Fin k ↪o Fin N :=
  (noneSet c.val).orderEmbOfFin c.prop

theorem nones_mem {k : ℕ} (c : Cell N k) (i : Fin k) : nones c i ∈ noneSet c.val :=
  Finset.orderEmbOfFin_mem _ c.prop i

theorem val_nones {k : ℕ} (c : Cell N k) (i : Fin k) : c.val (nones c i) = none :=
  mem_noneSet.mp (nones_mem c i)

/-- The index of a `none`-coordinate `x` of `a` among the `k` free positions. -/
def nonesIdx {k : ℕ} (a : Cell N k) (x : Fin N) (hx : x ∈ noneSet a.val) : Fin k :=
  (Finset.orderIsoOfFin (noneSet a.val) a.prop).symm ⟨x, hx⟩

theorem nones_nonesIdx {k : ℕ} (a : Cell N k) (x : Fin N) (hx : x ∈ noneSet a.val) :
    nones a (nonesIdx a x hx) = x := by
  change (noneSet a.val).orderEmbOfFin a.prop (nonesIdx a x hx) = x
  rw [← Finset.coe_orderIsoOfFin_apply, nonesIdx, OrderIso.apply_symm_apply]

theorem nonesIdx_nones {k : ℕ} (c : Cell N k) (i : Fin k) (h : nones c i ∈ noneSet c.val) :
    nonesIdx c (nones c i) h = i :=
  (nones c).injective (nones_nonesIdx c (nones c i) h)

/-! ### Faces and the precubical identity -/

/-- The `ε`-face at coordinate `i`: substitute `some ε` for the `i`-th `none`. -/
def faceCell (ε : Bool) {k : ℕ} (i : Fin (k + 1)) (c : Cell N (k + 1)) : Cell N k :=
  ⟨Function.update c.val (nones c i) (some ε), by
    rw [noneSet_update, Finset.card_erase_of_mem (nones_mem c i), c.prop, Nat.add_sub_cancel]⟩

@[simp] theorem face_val (ε : Bool) {k : ℕ} (i : Fin (k + 1)) (c : Cell N (k + 1)) :
    (faceCell ε i c).val = Function.update c.val (nones c i) (some ε) := rfl

/-- The crux computation: the order embedding of the `none`-set after a face is
the original embedding precomposed with `succAbove`.  Evaluated, the `x`-th
`none` of `faceCell η a c` is the `(a.succAbove x)`-th `none` of `c`. -/
theorem face_nones (η : Bool) {k : ℕ} (c : Cell N (k + 2)) (a : Fin (k + 2))
    (x : Fin (k + 1)) : nones (faceCell η a c) x = nones c (a.succAbove x) := by
  have hmem : ∀ y, ((Fin.succAboveOrderEmb a).trans (nones c)) y
      ∈ noneSet (faceCell η a c).val := by
    intro y
    change ((Fin.succAboveOrderEmb a).trans (nones c)) y
        ∈ noneSet (Function.update c.val (nones c a) (some η))
    rw [noneSet_update, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · simp only [RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
      exact fun h => (Fin.succAbove_ne a y) ((nones c).injective h)
    · simp only [RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
      exact Finset.orderEmbOfFin_mem _ c.prop _
  have key : nones (faceCell η a c) = (Fin.succAboveOrderEmb a).trans (nones c) :=
    (Finset.orderEmbOfFin_unique' (faceCell η a c).prop hmem).symm
  rw [key]
  simp [Fin.succAboveOrderEmb_apply]

/-- The precubical identity for the standard cube. -/
theorem face_face (ε η : Bool) {k : ℕ} {i j : Fin (k + 1)} (hij : i ≤ j) (c : Cell N (k + 2)) :
    faceCell ε i (faceCell η j.succ c) = faceCell η j (faceCell ε i.castSucc c) := by
  apply Subtype.ext
  change Function.update (Function.update c.val (nones c j.succ) (some η))
        (nones (faceCell η j.succ c) i) (some ε)
      = Function.update (Function.update c.val (nones c i.castSucc) (some ε))
        (nones (faceCell ε i.castSucc c) j) (some η)
  rw [face_nones η c j.succ i, face_nones ε c i.castSucc j,
    Fin.succAbove_succ_of_le j i hij, Fin.succAbove_castSucc_of_le i j hij]
  have hne : nones c j.succ ≠ nones c i.castSucc := by
    refine (nones c).injective.ne ?_
    intro h
    rw [Fin.ext_iff] at h
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    have : i.val ≤ j.val := hij
    omega
  exact Function.update_comm hne (some η) (some ε) c.val

/-! ### The extremal cells -/

/-- The top cell of `□ⁿ`: every coordinate free (`none`), the unique `n`-cell. -/
def topCell (n : ℕ) : Cell n n :=
  ⟨fun _ => none, by simp [noneSet]⟩

/-- `nones` of the top cell is the identity embedding. -/
theorem nones_topCell (k : ℕ) (x : Fin k) : nones (topCell k) x = x := by
  have h : (id : Fin k → Fin k) = nones (topCell k) :=
    Finset.orderEmbOfFin_unique (topCell k).prop
      (fun y => by simp [mem_noneSet, topCell]) strictMono_id
  exact (congrFun h x).symm

/-- A `k`-cell of `□ⁿ` with `k = n` is the top cell. -/
theorem eq_topCell {n : ℕ} (a : Cell n n) : a = topCell n := by
  apply Subtype.ext
  funext j
  have huniv : noneSet a.val = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [a.prop, Fintype.card_fin])
  have : a.val j = none := by
    have : j ∈ noneSet a.val := huniv ▸ Finset.mem_univ j
    rwa [mem_noneSet] at this
  rw [this]; rfl

/-- The constant-`some ε` `0`-cell (a vertex). -/
def constVertex (N : ℕ) (ε : Bool) : Cell N 0 :=
  ⟨fun _ => some ε, by simp [noneSet]⟩

/-- A vertex of `□ᴺ` *is* a sign assignment `Fin N → Bool`: a `0`-cell fixes every coordinate. -/
def vtxEquiv (N : ℕ) : Cell N 0 ≃ (Fin N → Bool) where
  toFun c q := (c.val q).getD false
  invFun v := ⟨fun q => some (v q), by simp [noneSet]⟩
  left_inv c := Subtype.ext (funext fun q => by
    have hq : c.val q ≠ none := fun h =>
      absurd (Finset.card_eq_zero.mp c.prop ▸ mem_noneSet.mpr h) (Finset.notMem_empty q)
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hq
    change some ((c.val q).getD false) = c.val q
    rw [hb]; rfl)
  right_inv _ := rfl

/-! ### Peeling the smallest fixed coordinate

A non-top cell is the face of a cell with one more free direction; peeling always the
*smallest* fixed coordinate makes that choice canonical and gives `Cell.peelRec`. -/

/-- The set of *fixed* (non-`none`) coordinates of a cell: the complement of the
`none`-set. -/
def fixedSet {n k : ℕ} (a : Cell n k) : Finset (Fin n) := (noneSet a.val)ᶜ

theorem fixedSet_card {n k : ℕ} (a : Cell n k) : (fixedSet a).card = n - k := by
  rw [fixedSet, Finset.card_compl, Fintype.card_fin, a.prop]

theorem fixedSet_nonempty {n k : ℕ} (a : Cell n k) (h : k < n) : (fixedSet a).Nonempty := by
  rw [← Finset.card_pos, fixedSet_card]; omega

/-- Facing out coordinate `i` adds `nones a i` to the fixed set. -/
theorem fixedSet_face {n k : ℕ} (a : Cell n (k + 1)) (ε : Bool) (i : Fin (k + 1)) :
    fixedSet (faceCell ε i a) = insert (nones a i) (fixedSet a) := by
  rw [fixedSet, fixedSet, face_val, noneSet_update, Finset.compl_erase]

/-- The smallest fixed coordinate of a non-top cell. -/
def minFixed {n k : ℕ} (a : Cell n k) (h : k < n) : Fin n :=
  (fixedSet a).min' (fixedSet_nonempty a h)

theorem minFixed_mem {n k : ℕ} (a : Cell n k) (h : k < n) : minFixed a h ∈ fixedSet a :=
  Finset.min'_mem _ _

theorem minFixed_notMem {n k : ℕ} (a : Cell n k) (h : k < n) : minFixed a h ∉ noneSet a.val := by
  have := minFixed_mem a h; rwa [fixedSet, Finset.mem_compl] at this

theorem minFixed_val_ne_none {n k : ℕ} (a : Cell n k) (h : k < n) :
    a.val (minFixed a h) ≠ none := fun hc => minFixed_notMem a h (by rwa [mem_noneSet])

/-- The (boolean) value `c` takes at its smallest fixed coordinate. -/
def minFixedVal {n k : ℕ} (a : Cell n k) (h : k < n) : Bool :=
  (a.val (minFixed a h)).get (Option.isSome_iff_ne_none.mpr (minFixed_val_ne_none a h))

theorem minFixed_val_eq {n k : ℕ} (a : Cell n k) (h : k < n) :
    a.val (minFixed a h) = some (minFixedVal a h) := (Option.some_get _).symm

/-- Freeing the smallest fixed coordinate (setting it back to `none`): a
`(k+1)`-cell. -/
def freeMin {n k : ℕ} (a : Cell n k) (h : k < n) : Cell n (k + 1) :=
  ⟨Function.update a.val (minFixed a h) none, by
    rw [noneSet_update_none, Finset.card_insert_of_notMem (minFixed_notMem a h), a.prop]⟩

@[simp] theorem freeMin_val {n k : ℕ} (a : Cell n k) (h : k < n) :
    (freeMin a h).val = Function.update a.val (minFixed a h) none := rfl

theorem noneSet_freeMin {n k : ℕ} (a : Cell n k) (h : k < n) :
    noneSet (freeMin a h).val = insert (minFixed a h) (noneSet a.val) := by
  rw [freeMin_val, noneSet_update_none]

theorem minFixed_mem_free {n k : ℕ} (a : Cell n k) (h : k < n) :
    minFixed a h ∈ noneSet (freeMin a h).val := by
  rw [mem_noneSet, freeMin_val, Function.update_self]

/-- The index, among the free positions of `freeMin a h`, of the coordinate we just
freed. -/
def minFixedIdx {n k : ℕ} (a : Cell n k) (h : k < n) : Fin (k + 1) :=
  nonesIdx (freeMin a h) (minFixed a h) (minFixed_mem_free a h)

theorem nones_minFixedIdx {n k : ℕ} (a : Cell n k) (h : k < n) :
    nones (freeMin a h) (minFixedIdx a h) = minFixed a h :=
  nones_nonesIdx _ _ _

/-- Refacing the freed coordinate recovers `a`: `a` is the `minFixedIdx`-face of
`freeMin a`. -/
theorem face_freeMin {n k : ℕ} (a : Cell n k) (h : k < n) :
    faceCell (minFixedVal a h) (minFixedIdx a h) (freeMin a h) = a := by
  apply Subtype.ext
  rw [face_val, nones_minFixedIdx, freeMin_val, Function.update_idem,
    ← minFixed_val_eq a h, Function.update_eq_self]

/-- Peeling recursion: every cell of `□ᴺ` is reached from the top cell by repeatedly
freeing its smallest fixed coordinate. -/
theorem Cell.peelRec {N : ℕ} {P : ∀ k, Cell N k → Prop} (top : ∀ c : Cell N N, P N c)
    (step : ∀ k (c : Cell N k) (h : k < N), P (k + 1) (freeMin c h) → P k c) :
    ∀ k (c : Cell N k), P k c := by
  have aux : ∀ d k (c : Cell N k), N - k = d → P k c := by
    intro d
    induction d with
    | zero =>
        intro k c hd
        obtain rfl : k = N := le_antisymm (cells_card_le c) (by omega)
        exact top c
    | succ d ih =>
        intro k c hd
        have h : k < N := by omega
        exact step k c h (ih (k + 1) (freeMin c h) (by omega))
  exact fun k c => aux (N - k) k c rfl

/-! ### Substitution

`subst c a` plugs the cell `a` of `□ⁿ` into the free coordinates of `c : Cell N n`.  It is
associative and unital on `topCell`, hence composition in `Box`; every `subst c` is
injective, so every cube map is monic. -/

variable {n k : ℕ}

/-- The raw substituted sign vector: keep the fixed coordinates of `c`, and fill its `i`-th
free coordinate with the `i`-th entry of `a`. -/
def substFun (c : Cell N n) (a : Cell n k) : Fin N → Option Bool := fun j =>
  if h : c.val j = none then a.val (nonesIdx c j (mem_noneSet.mpr h)) else c.val j

theorem substFun_of_none (c : Cell N n) (a : Cell n k) {j : Fin N} (h : c.val j = none) :
    substFun c a j = a.val (nonesIdx c j (mem_noneSet.mpr h)) := dif_pos h

theorem substFun_of_some (c : Cell N n) (a : Cell n k) {j : Fin N} (h : c.val j ≠ none) :
    substFun c a j = c.val j := dif_neg h

theorem noneSet_substFun (c : Cell N n) (a : Cell n k) :
    noneSet (substFun c a) = (noneSet a.val).map (nones c).toEmbedding := by
  ext j
  rw [mem_noneSet, Finset.mem_map]
  constructor
  · intro hj
    by_cases hc : c.val j = none
    · refine ⟨nonesIdx c j (mem_noneSet.mpr hc), ?_, nones_nonesIdx c j _⟩
      rw [substFun_of_none c a hc] at hj
      rwa [mem_noneSet]
    · rw [substFun_of_some c a hc] at hj
      exact absurd hj hc
  · rintro ⟨i, hi, rfl⟩
    change substFun c a (nones c i) = none
    rw [substFun_of_none c a (val_nones c i), nonesIdx_nones]
    rwa [mem_noneSet] at hi

/-- Substitution: plug `a` into the free coordinates of `c`. -/
def subst (c : Cell N n) (a : Cell n k) : Cell N k :=
  ⟨substFun c a, by rw [noneSet_substFun, Finset.card_map, a.prop]⟩

@[simp] theorem subst_val (c : Cell N n) (a : Cell n k) : (subst c a).val = substFun c a := rfl

/-- The defining property of substitution: at `c`'s `i`-th free coordinate it reads `a` at `i`. -/
theorem subst_val_nones (c : Cell N n) (a : Cell n k) (i : Fin n) :
    (subst c a).val (nones c i) = a.val i := by
  rw [subst_val, substFun_of_none c a (val_nones c i), nonesIdx_nones]

/-- **Every cube map is monic**: the substituted cell remembers what was substituted. -/
theorem subst_injective (c : Cell N n) : Function.Injective (subst c : Cell n k → Cell N k) :=
  fun a b h => Subtype.ext (funext fun i => by
    rw [← subst_val_nones c a i, ← subst_val_nones c b i, h])

theorem nones_subst (c : Cell N n) (a : Cell n k) (i : Fin k) :
    nones (subst c a) i = nones c (nones a i) := by
  have key : (nones a).trans (nones c) = nones (subst c a) := by
    refine Finset.orderEmbOfFin_unique' (subst c a).prop (fun x => ?_)
    rw [mem_noneSet]
    exact (subst_val_nones c a (nones a x)).trans (val_nones a x)
  exact (congrArg (fun e : Fin k ↪o Fin N => e i) key).symm

@[simp] theorem subst_topCell (c : Cell N n) : subst c (topCell n) = c := by
  apply Subtype.ext
  funext j
  rw [subst_val]
  by_cases h : c.val j = none
  · rw [substFun_of_none c _ h]; exact h.symm
  · rw [substFun_of_some c _ h]

@[simp] theorem topCell_subst (a : Cell n k) : subst (topCell n) a = a := by
  apply Subtype.ext
  funext j
  rw [subst_val, substFun_of_none _ a rfl]
  exact congrArg a.val ((nones_topCell n _).symm.trans (nones_nonesIdx (topCell n) j _))

/-- Substitution is associative — composition in `Box`, with no peeling induction. -/
theorem subst_assoc (c : Cell N n) {m : ℕ} (b : Cell n m) (a : Cell m k) :
    subst (subst c b) a = subst c (subst b a) := by
  apply Subtype.ext
  funext j
  rw [subst_val, subst_val]
  by_cases hc : c.val j = none
  · set i := nonesIdx c j (mem_noneSet.mpr hc) with hi
    have hval : (subst c b).val j = b.val i := substFun_of_none c b hc
    rw [substFun_of_none c (subst b a) hc, ← hi, subst_val]
    by_cases hb : b.val i = none
    · have hj : (subst c b).val j = none := hval.trans hb
      rw [substFun_of_none _ a hj, substFun_of_none b a hb]
      refine congrArg a.val ((nones (subst c b)).injective ?_)
      rw [nones_nonesIdx, nones_subst, nones_nonesIdx, hi, nones_nonesIdx]
    · have hj : (subst c b).val j ≠ none := fun h => hb (hval.symm.trans h)
      rw [substFun_of_some _ a hj, substFun_of_some b a hb, hval]
  · have hj : (subst c b).val j ≠ none := fun h =>
      hc ((substFun_of_some c b hc).symm.trans h)
    rw [substFun_of_some _ a hj, substFun_of_some c (subst b a) hc, subst_val,
      substFun_of_some c b hc]

/-- Substitution is face-natural: a face of the plug is the same face of the result. -/
theorem subst_faceCell (c : Cell N n) {k : ℕ} (ε : Bool) (i : Fin (k + 1))
    (a : Cell n (k + 1)) :
    subst c (faceCell ε i a) = faceCell ε i (subst c a) := by
  apply Subtype.ext
  rw [face_val, subst_val, subst_val, nones_subst]
  funext j
  by_cases hj : j = nones c (nones a i)
  · subst hj
    rw [Function.update_self, substFun_of_none c _ (val_nones c _), nonesIdx_nones, face_val,
      Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hc : c.val j = none
    · have hne : nonesIdx c j (mem_noneSet.mpr hc) ≠ nones a i := by
        intro hcontra
        exact hj (by rw [← nones_nonesIdx c j (mem_noneSet.mpr hc), hcontra])
      rw [substFun_of_none c _ hc, substFun_of_none c a hc, face_val,
        Function.update_of_ne hne]
    · rw [substFun_of_some c _ hc, substFun_of_some c a hc]

/-! ### The `trueCount` grading

`trueCount` counts the coordinates a cell fixes to `1`.  It is additive along `subst`, which
is what makes it an altitude on the cube. -/

/-- The number of coordinates a cell of `□ⁿ` fixes to `true`. -/
def trueCount {N k : ℕ} (a : Cell N k) : ℕ :=
  (Finset.univ.filter (fun j => a.val j = some true)).card

/-- A cell that fixes no coordinate to `1` is at altitude zero. -/
theorem trueCount_eq_zero {N k : ℕ} {a : Cell N k} (h : ∀ j, a.val j ≠ some true) :
    trueCount a = 0 := by
  rw [trueCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun j _ => h j

theorem trueCount_topCell (N : ℕ) : trueCount (topCell N) = 0 :=
  trueCount_eq_zero fun _ => by simp [topCell]

theorem trueCount_constVertex_false (N : ℕ) : trueCount (constVertex N false) = 0 :=
  trueCount_eq_zero fun _ => by simp [constVertex]

theorem trueCount_constVertex_true (N : ℕ) : trueCount (constVertex N true) = N := by
  have h : (Finset.univ.filter (fun j => (constVertex N true).val j = some true))
      = Finset.univ := Finset.filter_true_of_mem (fun j _ => rfl)
  rw [trueCount, h, Finset.card_univ, Fintype.card_fin]

/-- A vertex (`0`-cell) all of whose coordinates are `true` is the all-`true` vertex. -/
theorem trueCount_eq_top {n : ℕ} (c : Cell n 0) (hc : trueCount c = n) :
    c = constVertex n true := by
  apply Subtype.ext
  funext j
  have hfilter : Finset.univ.filter (fun j => c.val j = some true) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]; exact hc
  have hj : j ∈ Finset.univ.filter (fun j => c.val j = some true) := by
    rw [hfilter]; exact Finset.mem_univ j
  rw [Finset.mem_filter] at hj
  exact hj.2

/-- `trueCount` is bounded by the number of fixed coordinates `N - k`. -/
theorem trueCount_le {N k : ℕ} (a : Cell N k) : trueCount a ≤ N - k := by
  rw [← fixedSet_card a]
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [fixedSet, Finset.mem_compl, mem_noneSet, hj.2]
  simp

/-- Facing a free coordinate to `ε` raises `trueCount` by `ε`. -/
theorem trueCount_face {N k : ℕ} (ε : Bool) (i : Fin (k + 1)) (b : Cell N (k + 1)) :
    trueCount (faceCell ε i b) = trueCount b + (if ε then 1 else 0) := by
  have hq : b.val (nones b i) = none := val_nones b i
  cases ε with
  | false =>
      rw [if_neg (by simp), Nat.add_zero, trueCount, trueCount]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro j _
      by_cases hj : j = nones b i
      · subst hj; rw [face_val, Function.update_self]; simp [hq]
      · rw [face_val, Function.update_of_ne hj]
  | true =>
      rw [if_pos rfl, trueCount, trueCount]
      have hqnot : nones b i ∉ Finset.univ.filter (fun j => b.val j = some true) := by
        rw [Finset.mem_filter, hq]; simp
      have hins : Finset.univ.filter (fun j => (faceCell true i b).val j = some true)
          = insert (nones b i) (Finset.univ.filter (fun j => b.val j = some true)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hj : j = nones b i
        · subst hj; rw [face_val, Function.update_self]; simp
        · rw [face_val, Function.update_of_ne hj]; simp [hj]
      rw [hins, Finset.card_insert_of_notMem hqnot]

/-- Freeing the smallest fixed coordinate drops `trueCount` by its (boolean) value. -/
theorem trueCount_freeMin {N k : ℕ} (a : Cell N k) (h : k < N) :
    trueCount a = trueCount (freeMin a h) + (if minFixedVal a h then 1 else 0) := by
  conv_lhs => rw [← face_freeMin a h]
  rw [trueCount_face]

end StdCube
