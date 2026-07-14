import CubeChains.Foundations.Nerve
import CubeChains.Cobordisms.DirectedBoundary
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Foundations/Cylinder — the geometric cylinder of a precubical set

The **geometric cylinder** `Cyl X` (morally `X ⊗ □¹`) built *concretely* and then
pushed to the topos via the nerve, using only **face maps** — no Day coend, no cube
combinatorics (`app`/`sapp`/`snocFree`).

* `cylC : PrecubicalConstructions ⥤ PrecubicalConstructions` — the **concrete**
  cylinder endofunctor.  Its `n`-cells are
  `K.cells n ⊕ K.cells n ⊕ tube K n` (bottom copy / top copy / "tube over an
  `(n-1)`-cell", empty at dimension `0`); the interval is the *last* coordinate.
* `Cyl : PrecubicalSet ⥤ PrecubicalSet := realize ⋙ cylC ⋙ Nerve` — the
  **topos-level** cylinder, the operative cylinder for cobordism identities and
  collars, with cell decomposition `cylCellEquiv`, the two ends `cylEnd ε X`
  (`false` = bottom `δ⁰`, `true` = top `δ¹`; `Mono`, disjoint images), and the
  directed-boundary facts `cylEnd_false_isSieve` / `cylEnd_true_isCosieve`.
-/

set_option relaxedAutoImplicit false

open CategoryTheory Opposite StdCube

namespace PrecubicalSet

namespace Cylinder

/-! ### The tube type -/

/-- The **tube** cells of the concrete cylinder over `K`: a tube cell in dimension
`n` is a cell of `K` one dimension lower (the cell swept across the interval), and
there are no tube cells in dimension `0`.  `tube K 0 = PEmpty`,
`tube K (m+1) = K.cells m`. -/
def tube (K : PrecubicalConstructions) : ℕ → Type
  | 0 => PEmpty
  | m + 1 => K.cells m

@[simp] theorem tube_zero (K : PrecubicalConstructions) : tube K 0 = PEmpty := rfl
@[simp] theorem tube_succ (K : PrecubicalConstructions) (m : ℕ) :
    tube K (m + 1) = K.cells m := rfl

/-! ### The concrete cylinder cells and face maps -/

/-- The `n`-cells of the concrete cylinder `cylC.obj K`: a bottom copy of `K`, a
top copy of `K`, and the tube over an `(n-1)`-cell. -/
def cell (K : PrecubicalConstructions) (n : ℕ) : Type :=
  K.cells n ⊕ K.cells n ⊕ tube K n

/-- The bottom-copy inclusion of an `n`-cell into the cylinder cells. -/
abbrev cellBot {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) : cell K n :=
  Sum.inl c

/-- The top-copy inclusion of an `n`-cell into the cylinder cells. -/
abbrev cellTop {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) : cell K n :=
  Sum.inr (Sum.inl c)

/-- The tube inclusion of an `m`-cell `t : K.cells m` as the tube cell in dimension
`m+1`. -/
abbrev cellTube {K : PrecubicalConstructions} {m : ℕ} (t : K.cells m) : cell K (m + 1) :=
  Sum.inr (Sum.inr (t : tube K (m + 1)))

/-- The face of a tube cell `tube t` (`t : K.cells m`) at index `i : Fin (m+1)`:
the *last* coordinate (interval) caps the tube to `bot t`/`top t`; a `K`-coordinate
`Fin.castSucc i'` faces the swept cell.  Defined directly on the dimension `m` so
the `K.face` in the `castSucc` branch is well-typed (`m` must be a successor for a
`K`-coordinate to exist; `Fin 0` is empty when `m = 0`). -/
def tubeFace (K : PrecubicalConstructions) (ε : Bool) :
    ∀ {m : ℕ}, Fin (m + 1) → K.cells m → cell K m
  | 0, _, t => cond ε (cellTop t) (cellBot t)
  | _ + 1, i, t =>
      Fin.lastCases
        (motive := fun _ => cell K _)
        (cond ε (cellTop t) (cellBot t))
        (fun i' => cellTube (K.face ε i' t))
        i

/-- **The cylinder face map.**  On the two copies it is `K`'s face; on a tube cell
it is `tubeFace`. -/
def cylFace (K : PrecubicalConstructions) (ε : Bool) :
    ∀ {n : ℕ}, Fin (n + 1) → cell K (n + 1) → cell K n
  | _, i, Sum.inl c => cellBot (K.face ε i c)
  | _, i, Sum.inr (Sum.inl c) => cellTop (K.face ε i c)
  | _, i, Sum.inr (Sum.inr t) => tubeFace K ε i t

@[simp] theorem cylFace_bot (K : PrecubicalConstructions) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : K.cells (n + 1)) :
    cylFace K ε i (cellBot c) = cellBot (K.face ε i c) := rfl

@[simp] theorem cylFace_top (K : PrecubicalConstructions) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : K.cells (n + 1)) :
    cylFace K ε i (cellTop c) = cellTop (K.face ε i c) := rfl

@[simp] theorem cylFace_tube (K : PrecubicalConstructions) (ε : Bool) {m : ℕ}
    (i : Fin (m + 1)) (t : K.cells m) :
    cylFace K ε i (cellTube t) = tubeFace K ε i t := rfl

@[simp] theorem tubeFace_zero (K : PrecubicalConstructions) (ε : Bool)
    (i : Fin 1) (t : K.cells 0) :
    tubeFace K ε i t = cond ε (cellTop t) (cellBot t) := rfl

@[simp] theorem tubeFace_last (K : PrecubicalConstructions) (ε : Bool) {m : ℕ}
    (t : K.cells (m + 1)) :
    tubeFace K ε (Fin.last (m + 1)) t = cond ε (cellTop t) (cellBot t) := by
  change Fin.lastCases (motive := fun _ => cell K (m + 1))
      (cond ε (cellTop t) (cellBot t)) (fun i' => cellTube (K.face ε i' t))
      (Fin.last (m + 1)) = _
  rw [Fin.lastCases_last]

@[simp] theorem tubeFace_castSucc (K : PrecubicalConstructions) (ε : Bool) {m : ℕ}
    (i' : Fin (m + 1)) (t : K.cells (m + 1)) :
    tubeFace K ε (Fin.castSucc i') t = cellTube (K.face ε i' t) := by
  change Fin.lastCases (motive := fun _ => cell K (m + 1))
      (cond ε (cellTop t) (cellBot t)) (fun i' => cellTube (K.face ε i' t))
      (Fin.castSucc i') = _
  rw [Fin.lastCases_castSucc]

/-- The interval-coordinate (`Fin.last`) face of a tube cell caps it, in every
dimension (unifying `tubeFace_zero` and `tubeFace_last`). -/
theorem tubeFace_last_gen (K : PrecubicalConstructions) (ε : Bool) {m : ℕ}
    (t : K.cells m) :
    tubeFace K ε (Fin.last m) t = cond ε (cellTop t) (cellBot t) := by
  cases m with
  | zero => rfl
  | succ m => exact tubeFace_last K ε t

/-! ### The precubical identity for the concrete cylinder -/

/-- The precubical identity `face_face` for the cylinder face maps.  The `bot`/`top`
cases are immediate from `K.face_face`; the tube case is bookkeeping over the
interval-vs-`K` split (`Fin.lastCases` on both indices). -/
theorem cylFace_face (K : PrecubicalConstructions) (ε η : Bool) {n : ℕ}
    {i j : Fin (n + 1)} (hij : i ≤ j) (c : cell K (n + 2)) :
    cylFace K ε i (cylFace K η j.succ c) = cylFace K η j (cylFace K ε i.castSucc c) := by
  match c with
  | Sum.inl c => exact congrArg cellBot (K.face_face ε η hij c)
  | Sum.inr (Sum.inl c) => exact congrArg cellTop (K.face_face ε η hij c)
  | Sum.inr (Sum.inr t) =>
      -- `t : tube K (n+2) = K.cells (n+1)`; the inner cylinder faces are `tubeFace`.
      rw [cylFace_tube, cylFace_tube]
      -- carry `hij` through the `Fin.lastCases` splits by reverting it, which
      -- generalizes `j` (resp. `i`) everywhere in the goal.
      revert hij
      induction j using Fin.lastCases with
      | last =>
        -- `j = Fin.last n`, so `j.succ = Fin.last (n+1)`.
        intro _
        rw [show (Fin.last n).succ = Fin.last (n + 1) from Fin.succ_last n,
          tubeFace_last, show i.castSucc = Fin.castSucc i from rfl, tubeFace_castSucc,
          cylFace_tube, tubeFace_last_gen]
        -- LHS: `cylFace ε i (cond η …)`; RHS: `cond η …` of the faced cell.
        cases η with
        | false => simp only [cond_false, cylFace_bot]
        | true => simp only [cond_true, cylFace_top]
      | cast j' =>
        -- `j = Fin.castSucc j'`, `j' : Fin n`; so `j.succ = Fin.castSucc j'.succ`.
        intro hle
        rw [show (Fin.castSucc j').succ = Fin.castSucc j'.succ from Fin.succ_castSucc j',
          tubeFace_castSucc]
        revert hle
        induction i using Fin.lastCases with
        | last =>
          -- `i = Fin.last n`; but `i ≤ j = castSucc j' < last n`, contradiction.
          intro hle
          exact absurd (lt_of_lt_of_le (Fin.castSucc_lt_last j') hle) (lt_irrefl _)
        | cast i' =>
          -- `i = Fin.castSucc i'`, `i' : Fin n`.  A `K`-coordinate on both indices
          -- forces `n` to be a successor (else `i' : Fin 0` is empty).
          intro hle
          rcases n with _ | p
          · exact i'.elim0
          · -- `n = p + 1`: now `K.face` faces compose; reduce to `K.face_face`.
            rw [cylFace_tube, tubeFace_castSucc,
              show (Fin.castSucc i').castSucc = Fin.castSucc i'.castSucc from rfl,
              tubeFace_castSucc, cylFace_tube, tubeFace_castSucc]
            have hij' : i' ≤ j' := by rwa [← Fin.castSucc_le_castSucc_iff] at hle
            exact congrArg cellTube (K.face_face ε η hij' t)

/-! ### The concrete cylinder object and endofunctor -/

/-- The concrete cylinder of a precubical set `K`: cells
`K.cells n ⊕ K.cells n ⊕ tube K n`, faces `cylFace`, precubical identity
`cylFace_face`. -/
def cylCObj (K : PrecubicalConstructions) : PrecubicalConstructions where
  cells := cell K
  face := fun {_n} ε i c => cylFace K ε i c
  face_face := fun {_n} ε η {_i _j} hij c => cylFace_face K ε η hij c

@[simp] theorem cylCObj_cells (K : PrecubicalConstructions) (n : ℕ) :
    (cylCObj K).cells n = cell K n := rfl

@[simp] theorem cylCObj_face (K : PrecubicalConstructions) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : cell K (n + 1)) :
    (cylCObj K).face ε i c = cylFace K ε i c := rfl

/-- The action of a tube cell under a precubical map: face down one dimension is
just the underlying map on `K.cells`. -/
def tubeMap {K L : PrecubicalConstructions} (φ : K ⟶ L) :
    ∀ {n : ℕ}, tube K n → tube L n
  | 0, t => t.elim
  | _ + 1, t => φ.app _ t

/-- The action of a precubical map on cylinder cells: the underlying map on the two
copies and on the tube. -/
def cylCellMap {K L : PrecubicalConstructions} (φ : K ⟶ L) {n : ℕ} :
    cell K n → cell L n :=
  Sum.map (φ.app n) (Sum.map (φ.app n) (tubeMap φ))

@[simp] theorem cylCellMap_bot {K L : PrecubicalConstructions} (φ : K ⟶ L) {n : ℕ}
    (c : K.cells n) : cylCellMap φ (cellBot c) = cellBot (φ.app n c) := rfl

@[simp] theorem cylCellMap_top {K L : PrecubicalConstructions} (φ : K ⟶ L) {n : ℕ}
    (c : K.cells n) : cylCellMap φ (cellTop c) = cellTop (φ.app n c) := rfl

@[simp] theorem cylCellMap_tube {K L : PrecubicalConstructions} (φ : K ⟶ L) {m : ℕ}
    (t : K.cells m) : cylCellMap φ (cellTube t) = cellTube (φ.app m t) := rfl

/-- A precubical map commutes with the cylinder faces (the `app_face` for the
cylinder).  Cases on the cell; the tube case uses `φ.app_face` and the explicit
`tubeFace` formulas. -/
theorem cylCellMap_face {K L : PrecubicalConstructions} (φ : K ⟶ L) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : cell K (n + 1)) :
    cylCellMap φ (cylFace K ε i c) = cylFace L ε i (cylCellMap φ c) := by
  match c with
  | Sum.inl c => exact congrArg cellBot (φ.app_face ε i c)
  | Sum.inr (Sum.inl c) => exact congrArg cellTop (φ.app_face ε i c)
  | Sum.inr (Sum.inr t) =>
      -- `t : tube K (n+1) = K.cells n`.
      rw [cylFace_tube, cylCellMap_tube, cylFace_tube]
      induction i using Fin.lastCases with
      | last =>
        rw [tubeFace_last_gen, tubeFace_last_gen]
        cases ε with
        | false => rfl
        | true => rfl
      | cast i' =>
        rcases n with _ | p
        · exact i'.elim0
        · rw [tubeFace_castSucc, tubeFace_castSucc, cylCellMap_tube,
            φ.app_face ε i' t]

/-- The cylinder action on a precubical morphism. -/
def cylCMap {K L : PrecubicalConstructions} (φ : K ⟶ L) : cylCObj K ⟶ cylCObj L where
  app _n c := cylCellMap φ c
  app_face ε i c := cylCellMap_face φ ε i c

@[simp] theorem cylCMap_app {K L : PrecubicalConstructions} (φ : K ⟶ L) (n : ℕ)
    (c : cell K n) : PrecubicalConstructions.Hom.app (cylCMap φ) n c = cylCellMap φ c := rfl

theorem tubeMap_id (K : PrecubicalConstructions) {n : ℕ} (t : tube K n) :
    tubeMap (𝟙 K) t = t := by
  rcases n with _ | p
  · exact t.elim
  · rfl

theorem cylCellMap_id (K : PrecubicalConstructions) {n : ℕ} (c : cell K n) :
    cylCellMap (𝟙 K) c = c := by
  match c with
  | Sum.inl c => rfl
  | Sum.inr (Sum.inl c) => rfl
  | Sum.inr (Sum.inr t) =>
      change (Sum.inr (Sum.inr (tubeMap (𝟙 K) t)) : cell K n) = Sum.inr (Sum.inr t)
      rw [tubeMap_id]

theorem tubeMap_comp {K L M : PrecubicalConstructions} (φ : K ⟶ L) (ψ : L ⟶ M) {n : ℕ}
    (t : tube K n) : tubeMap (φ ≫ ψ) t = tubeMap ψ (tubeMap φ t) := by
  rcases n with _ | p
  · exact t.elim
  · rfl

theorem cylCellMap_comp {K L M : PrecubicalConstructions} (φ : K ⟶ L) (ψ : L ⟶ M)
    {n : ℕ} (c : cell K n) :
    cylCellMap (φ ≫ ψ) c = cylCellMap ψ (cylCellMap φ c) := by
  match c with
  | Sum.inl c => rfl
  | Sum.inr (Sum.inl c) => rfl
  | Sum.inr (Sum.inr t) =>
      change (Sum.inr (Sum.inr (tubeMap (φ ≫ ψ) t)) : cell M n)
        = Sum.inr (Sum.inr (tubeMap ψ (tubeMap φ t)))
      rw [tubeMap_comp]

/-- **The concrete cylinder endofunctor** `cylC : PrecubicalConstructions ⥤
PrecubicalConstructions`. -/
def cylC : PrecubicalConstructions ⥤ PrecubicalConstructions where
  obj := cylCObj
  map := cylCMap
  map_id K := by
    apply PrecubicalConstructions.hom_ext
    intro n c; exact cylCellMap_id K c
  map_comp φ ψ := by
    apply PrecubicalConstructions.hom_ext
    intro n c; exact cylCellMap_comp φ ψ c

@[simp] theorem cylC_obj (K : PrecubicalConstructions) : cylC.obj K = cylCObj K := rfl

@[simp] theorem cylC_map {K L : PrecubicalConstructions} (φ : K ⟶ L) :
    cylC.map φ = cylCMap φ := rfl

/-! ### The topos-level cylinder `Cyl`

`Cyl X` is the geometric cylinder of `X` (morally `X ⊗ □¹`), built by realizing to
the concrete model, applying the concrete cylinder, and taking the nerve back to the
topos. -/

/-- **The geometric cylinder functor** `Cyl : PrecubicalSet ⥤ PrecubicalSet`, via the
concrete-model + nerve presentation: `realize ⋙ cylC ⋙ Nerve`. -/
noncomputable def Cyl : PrecubicalSet ⥤ PrecubicalSet :=
  realize ⋙ cylC ⋙ Nerve

theorem Cyl_obj (X : PrecubicalSet) :
    Cyl.obj X = Nerve.obj (cylC.obj (realize.obj X)) := rfl

theorem Cyl_map {X Y : PrecubicalSet} (f : X ⟶ Y) :
    Cyl.map f = Nerve.map (cylC.map (realize.map f)) := rfl

/-! ### Cell decomposition of `Cyl X` -/

/-- **The cell decomposition of the cylinder.**  `(Cyl.obj X).cells n` is the
bottom copy, top copy, and tube: `X.cells n ⊕ X.cells n ⊕ tube (realize.obj X) n`.
Immediate from `nerveCellEquiv` on `cylC.obj (realize.obj X)` (whose cells are by
definition that sum, since `(realize.obj X).cells m = X.cells m`). -/
noncomputable def cylCellEquiv (X : PrecubicalSet) (n : ℕ) :
    (Cyl.obj X).cells n ≃ X.cells n ⊕ X.cells n ⊕ tube (realize.obj X) n :=
  nerveCellEquiv (cylC.obj (realize.obj X)) n

@[simp] theorem cylCellEquiv_apply (X : PrecubicalSet) {n : ℕ}
    (f : (Cyl.obj X).cells n) :
    cylCellEquiv X n f = ev f := rfl

@[simp] theorem cylCellEquiv_symm_apply (X : PrecubicalSet) {n : ℕ}
    (c : cell (realize.obj X) n) :
    (cylCellEquiv X n).symm c = canonicalMap c := rfl

/-! ### The two ends -/

/-- The concrete end-inclusion `K ⟶ cylC.obj K`: the bottom copy (`ε = false`) or
the top copy (`ε = true`).  Faces commute since the copies are sub-precubical-sets. -/
def cylCEnd (K : PrecubicalConstructions) (ε : Bool) : K ⟶ cylCObj K where
  app _n c := cond ε (cellTop c) (cellBot c)
  app_face ε' i c := by cases ε <;> rfl

@[simp] theorem cylCEnd_app_false (K : PrecubicalConstructions) {n : ℕ} (c : K.cells n) :
    PrecubicalConstructions.Hom.app (cylCEnd K false) n c = cellBot c := rfl

@[simp] theorem cylCEnd_app_true (K : PrecubicalConstructions) {n : ℕ} (c : K.cells n) :
    PrecubicalConstructions.Hom.app (cylCEnd K true) n c = cellTop c := rfl

/-- **The two ends** `cylEnd ε X : X ⟶ Cyl.obj X`.  `cylEnd false` is the bottom
(`δ⁰`) and `cylEnd true` the top (`δ¹`).  Built from the concrete end through the
nerve, fixed up by the round-trip iso. -/
noncomputable def cylEnd (ε : Bool) (X : PrecubicalSet) : X ⟶ Cyl.obj X :=
  (nerveRealizeIso X).inv ≫ Nerve.map (cylCEnd (realize.obj X) ε)

/-- **End characterization.**  Under `cylCellEquiv`, the end `cylEnd ε X` at
dimension `n` sends an `n`-cell `c` to the bottom (`ε = false`) / top (`ε = true`)
copy of `c`. -/
theorem cylCellEquiv_cylEnd (ε : Bool) (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    cylCellEquiv X n ((cylEnd ε X)⟪n⟫ c)
      = (cond ε (cellTop c) (cellBot c) : cell (realize.obj X) n) := by
  -- Abbreviate the realized cell `f := (nerveRealizeIso X).inv.app _ c`.
  set f : (Nerve.obj (realize.obj X)).cells n :=
    (nerveRealizeIso X).inv⟪n⟫ c with hf
  -- `(cylEnd ε X).app c = (Nerve.map (cylCEnd …)).app f`; read through naturality.
  have hstep : cylCellEquiv X n ((cylEnd ε X)⟪n⟫ c)
      = PrecubicalConstructions.Hom.app (cylCEnd (realize.obj X) ε) n
          (nerveCellEquiv (realize.obj X) n f) :=
    nerveCellEquiv_naturality (cylCEnd (realize.obj X) ε) f
  rw [hstep]
  -- `nerveCellEquiv (realize.obj X) n f = c` since `nerveCellEquiv = hom.app` and
  -- `f = inv.app c`, so `hom.app (inv.app c) = c`.
  have hinv : nerveCellEquiv (realize.obj X) n f = c := by
    rw [nerveCellEquiv_apply, hf, ← nerveRealizeIso_hom_app X (op ▫n)]
    exact congrFun (congrArg (fun t => t.app (op ▫n))
      (nerveRealizeIso X).inv_hom_id) c
  rw [hinv]
  cases ε <;> rfl

/-! ### The ends are mono with disjoint images -/

/-- The cell-level inclusion `cond ε (top c) (bot c)` is injective. -/
theorem cylEnd_summand_injective (ε : Bool) {K : PrecubicalConstructions} {n : ℕ}
    {a b : K.cells n}
    (hab : (cond ε (cellTop a) (cellBot a) : cell K n) = cond ε (cellTop b) (cellBot b)) :
    a = b := by
  cases ε with
  | false => simp only [cond_false] at hab; exact Sum.inl_injective hab
  | true => simp only [cond_true] at hab; exact Sum.inl_injective (Sum.inr_injective hab)

/-- **Each end is injective in every dimension.**  Composing the characterization
`cylCellEquiv_cylEnd` (an `Equiv`, hence injective) with the injective summand
inclusion. -/
theorem cylEnd_app_injective (ε : Bool) (X : PrecubicalSet) {n : ℕ} :
    Function.Injective ((cylEnd ε X)⟪n⟫) := by
  intro a b hab
  refine cylEnd_summand_injective ε (K := realize.obj X) (n := n) ?_
  rw [← cylCellEquiv_cylEnd ε X a, ← cylCellEquiv_cylEnd ε X b]
  exact congrArg (cylCellEquiv X n) hab

/-- **Each end is a monomorphism.** -/
instance cylEnd_mono (ε : Bool) (X : PrecubicalSet) : Mono (cylEnd ε X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro b
  rw [mono_iff_injective]
  -- every `b : Boxᵒᵖ` is `op ▫b.unop.dim` (single-field structure, eta).
  intro a a' hab
  exact cylEnd_app_injective ε X (n := b.unop.dim) hab

/-- **The two ends have disjoint images.**  Under `cylCellEquiv`, the bottom end
lands in the `bot` summand and the top end in the `top` summand; these are different
`⊕`-injections, so no cell is in both images. -/
theorem cylEnd_disjoint (X : PrecubicalSet) {n : ℕ} (a b : X.cells n)
    (h : (cylEnd false X)⟪n⟫ a = (cylEnd true X)⟪n⟫ b) :
    False := by
  have he : (cellBot a : cell (realize.obj X) n) = cellTop b := by
    have h1 := cylCellEquiv_cylEnd false X a
    have h2 := cylCellEquiv_cylEnd true X b
    rw [cond_false] at h1
    rw [cond_true] at h2
    rw [← h1, ← h2]
    exact congrArg (cylCellEquiv X n) h
  exact Sum.inl_ne_inr he

/-! ### The ends as a sieve / cosieve

The bottom end is *past-closed* (`IsSieve`) and the top end *future-closed*
(`IsCosieve`) for the directed reachability of `Cyl.obj X`.  The proofs run through
`cylCellEquiv`: the bottom image is exactly the `bot` summand, and a directed step
out of a `bot`/`top` cell stays in that summand (the only faces producing a `bot`
cell from a non-`bot` cell are the `false`-interval face of a tube — which is a
*source* step, consistent with `bot` being a sieve). -/

/-- Abbreviation: the realized concrete cylinder `cylC.obj (realize.obj X)`. -/
noncomputable abbrev cylCReal (X : PrecubicalSet) : PrecubicalConstructions :=
  cylC.obj (realize.obj X)

/-- **Face translation.**  The topos face map of `Cyl.obj X`, read through
`cylCellEquiv`, is the concrete cylinder face `cylFace` of `cylCReal X`. -/
theorem cylCellEquiv_faceMap (X : PrecubicalSet) (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (z : (Cyl.obj X).cells (n + 1)) :
    cylCellEquiv X n ((Cyl.obj X).faceMap ε i z)
      = cylFace (realize.obj X) ε i (cylCellEquiv X (n + 1) z) :=
  nerveCellEquiv_faceMap (K := cylCReal X) ε i z

/-- A cell of `Cyl.obj X` is **in the bottom copy** when its `cylCellEquiv` image is
a `bot` cell. -/
def InBot (X : PrecubicalSet) (z : (Cyl.obj X).TotalCell) : Prop :=
  ∃ c : (realize.obj X).cells z.1, cylCellEquiv X z.1 z.2 = cellBot c

/-- A cell of `Cyl.obj X` is **in the top copy** when its `cylCellEquiv` image is a
`top` cell. -/
def InTop (X : PrecubicalSet) (z : (Cyl.obj X).TotalCell) : Prop :=
  ∃ c : (realize.obj X).cells z.1, cylCellEquiv X z.1 z.2 = cellTop c

/-- **The bottom image is the `bot` summand.**  The predicate "`z` is in the image
of `cylEnd false X`" equals `InBot`. -/
theorem inBot_iff_image (X : PrecubicalSet) (z : (Cyl.obj X).TotalCell) :
    InBot X z ↔ ∃ c, mapCell (cylEnd false X) c = z := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨z.1, c⟩, ?_⟩
    -- `mapCell (cylEnd false X) ⟨z.1, c⟩ = ⟨z.1, (cylEnd false X).app … c⟩`; its
    -- `cylCellEquiv` is `cellBot c`, matching `z`'s.
    have hz : (cylEnd false X)⟪z.1⟫ c = z.2 := by
      apply (cylCellEquiv X z.1).injective
      rw [hc, cylCellEquiv_cylEnd false X c, cond_false]
    exact Sigma.ext rfl (heq_of_eq hz)
  · rintro ⟨⟨m, c⟩, rfl⟩
    -- `z = mapCell (cylEnd false X) ⟨m,c⟩ = ⟨m, (cylEnd false X).app … c⟩`.
    refine ⟨c, ?_⟩
    change cylCellEquiv X m ((cylEnd false X)⟪m⟫ c)
      = (cellBot c : cell (realize.obj X) m)
    rw [cylCellEquiv_cylEnd false X c, cond_false]

/-- **The top image is the `top` summand.** -/
theorem inTop_iff_image (X : PrecubicalSet) (z : (Cyl.obj X).TotalCell) :
    InTop X z ↔ ∃ c, mapCell (cylEnd true X) c = z := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨z.1, c⟩, ?_⟩
    have hz : (cylEnd true X)⟪z.1⟫ c = z.2 := by
      apply (cylCellEquiv X z.1).injective
      rw [hc, cylCellEquiv_cylEnd true X c, cond_true]
    exact Sigma.ext rfl (heq_of_eq hz)
  · rintro ⟨⟨m, c⟩, rfl⟩
    refine ⟨c, ?_⟩
    change cylCellEquiv X m ((cylEnd true X)⟪m⟫ c)
      = (cellTop c : cell (realize.obj X) m)
    rw [cylCellEquiv_cylEnd true X c, cond_true]

/-! ### Face propagation for the bot / top summands -/

/-- A `true`-face landing in the `bot` summand comes from a `bot` cell: the only
faces producing a `bot` cell are `false`-faces of `bot`/tube cells, never a
`true`-face of a non-`bot` cell. -/
theorem face_true_eq_bot {K : PrecubicalConstructions} {n : ℕ} (i : Fin (n + 1))
    {z : cell K (n + 1)} {w : K.cells n} (h : cylFace K true i z = cellBot w) :
    ∃ c, z = cellBot c := by
  match z with
  | Sum.inl c => exact ⟨c, rfl⟩
  | Sum.inr (Sum.inl c) => rw [cylFace_top] at h; simp at h
  | Sum.inr (Sum.inr t) =>
      exfalso
      rw [cylFace_tube] at h
      induction i using Fin.lastCases with
      | last => rw [tubeFace_last_gen, cond_true] at h; simp at h
      | cast i' =>
        rcases n with _ | p
        · exact i'.elim0
        · rw [tubeFace_castSucc] at h; simp at h

/-- A `false`-face landing in the `top` summand comes from a `top` cell. -/
theorem face_false_eq_top {K : PrecubicalConstructions} {n : ℕ} (i : Fin (n + 1))
    {z : cell K (n + 1)} {w : K.cells n} (h : cylFace K false i z = cellTop w) :
    ∃ c, z = cellTop c := by
  match z with
  | Sum.inl c => rw [cylFace_bot] at h; simp at h
  | Sum.inr (Sum.inl c) => exact ⟨c, rfl⟩
  | Sum.inr (Sum.inr t) =>
      exfalso
      rw [cylFace_tube] at h
      induction i using Fin.lastCases with
      | last => rw [tubeFace_last_gen, cond_false] at h; simp at h
      | cast i' =>
        rcases n with _ | p
        · exact i'.elim0
        · rw [tubeFace_castSucc] at h
          exact Sum.inr_ne_inl (Sum.inr_injective h)

/-! ### The sieve / cosieve theorems -/

/-- **The bottom end is a sieve** (past-closed).  A directed step into a `bot` cell,
read backward, stays in the `bot` summand. -/
theorem cylEnd_false_isSieve (X : PrecubicalSet) :
    Precubical.Cobordism.IsSieve (Cyl.obj X)
      (fun z => ∃ c, mapCell (cylEnd false X) c = z) := by
  -- Translate the predicate to `InBot`, then induct on `Reaches`.
  intro x y hxy hy
  rw [← inBot_iff_image] at hy ⊢
  induction hxy with
  | refl x => exact hy
  | source i c =>
      -- `x = ⟨faceMap false i c⟩`, `y = ⟨c⟩`, `c` in bot ⟹ its false-face in bot.
      obtain ⟨w, hw⟩ := hy
      refine ⟨(realize.obj X).face false i w, ?_⟩
      rw [cylCellEquiv_faceMap, hw, cylFace_bot]
  | target i c =>
      -- `x = ⟨c⟩`, `y = ⟨faceMap true i c⟩` in bot ⟹ `c` in bot.
      obtain ⟨w, hw⟩ := hy
      rw [cylCellEquiv_faceMap] at hw
      obtain ⟨c', hc'⟩ := face_true_eq_bot i hw
      exact ⟨c', hc'⟩
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hy)

/-- **The top end is a cosieve** (future-closed).  A directed step out of a `top`
cell stays in the `top` summand. -/
theorem cylEnd_true_isCosieve (X : PrecubicalSet) :
    Precubical.Cobordism.IsCosieve (Cyl.obj X)
      (fun z => ∃ c, mapCell (cylEnd true X) c = z) := by
  intro x y hxy hx
  rw [← inTop_iff_image] at hx ⊢
  induction hxy with
  | refl x => exact hx
  | source i c =>
      -- `x = ⟨faceMap false i c⟩` in top ⟹ `c` in top.
      obtain ⟨w, hw⟩ := hx
      rw [cylCellEquiv_faceMap] at hw
      obtain ⟨c', hc'⟩ := face_false_eq_top i hw
      exact ⟨c', hc'⟩
  | target i c =>
      -- `x = ⟨c⟩` in top ⟹ its true-face `y` in top.
      obtain ⟨w, hw⟩ := hx
      refine ⟨(realize.obj X).face true i w, ?_⟩
      rw [cylCellEquiv_faceMap, hw, cylFace_top]
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)

end Cylinder

end PrecubicalSet
