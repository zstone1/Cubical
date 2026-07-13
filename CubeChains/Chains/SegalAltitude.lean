import CubeChains.Foundations.Altitude
import CubeChains.Chains.WedgeMap

/-!
# Chains/SegalAltitude

Discharges, sorry-free, the `AdmitsAltitude` hypotheses the Segal splitting needs:
`cube_admitsAltitude` (`□ⁿ`, via `trueCount ∘ ev`), `wedge2_admitsAltitude` (glue
two altitudes), and `serialWedge_admitsAltitude` (by recursion).

**Layer:** Chains.  **Imports:** `Foundations.Altitude`, `WedgeMap`.
These make the n-ary Segal decomposition `chSegalProd` (in `Chains/SegalProd.lean`)
hypothesis-free.

This file discharges, sorry-free, the `AdmitsAltitude` hypotheses needed by the
Segal splitting (`Chains/Segal.lean` / `Chains/SegalProd.lean`):

* `BPSet.cube_admitsAltitude`  — every standard cube `□ⁿ` admits an altitude,
  namely `trueCount ∘ ev` (the number of `1`-fixed coordinates of the pulled-back
  cell rises by `1` across a `target` face and is unchanged across a `source` face).
* `BPSet.wedge2_admitsAltitude` — `X ∨ Y` admits an altitude whenever both `X` and
  `Y` do, by gluing the two altitude functions (shifting `Y`'s up by `X.final`'s
  altitude so it strictly increases across the junction).
* `BPSet.serialWedge_admitsAltitude` — hence so does every serial wedge, by
  recursion.

These make the n-ary Segal decomposition `chSegalProd` **hypothesis-free**: each
`chSegal (□n) (⋁rest)` invocation gets its `AdmitsAltitude` argument
from `wedge2_admitsAltitude (cube_admitsAltitude n) (serialWedge_admitsAltitude rest)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace StdCube

/-- **`trueCount` is additive along the iterated-face map `act`.**  Facing a cell
`x : Cell N m` out at the fixed coordinates of `a : Cell m k` adds, to the
`true`-count, exactly the `true`-count of `a` (each `1`-fixed coordinate of `a`
contributes one extra `1` to the result).  Proved by peeling the smallest fixed
coordinate of `a` (`app_unfold`), exactly mirroring the recursion of `act`. -/
theorem trueCount_app {N m : ℕ} (x : Cell N m) :
    ∀ {k : ℕ} (a : Cell m k),
      trueCount (act (K := stdPre N) x a) = trueCount x + trueCount a := by
  intro k a
  induction hd : m - k using Nat.strong_induction_on generalizing k a with
  | _ d ih =>
    rcases Nat.lt_or_ge k m with h | h
    · -- peel the smallest fixed coordinate of `a`
      rw [app_unfold (K := stdPre N) x a h]
      change trueCount (faceCell (minFixedVal a h) (minFixedIdx a h)
          (act (K := stdPre N) x (freeMin a h))) = trueCount x + trueCount a
      rw [trueCount_face, ih (m - (k + 1)) (by omega) (freeMin a h) rfl,
        trueCount_freeMin a h]
      ring
    · -- `a` has no fixed coordinates: `a = topCell`, `app x (topCell) = x`
      have hkm : k = m := le_antisymm (cells_card_le a) h
      subst hkm
      rw [eq_topCell a, app_topCell, trueCount_topCell, Nat.add_zero]

end StdCube

namespace BPSet

open StdCube CategoryTheory Opposite

/-! ## The standard cube admits an altitude -/

/-- The altitude on `□ⁿ`'s cells: the `true`-count of the pulled-back cell.  An
`m`-cell of `cube N` is a box morphism `□ᵐ ⟶ □ᴺ`, i.e. (definitionally) a
`PrecubicalConstructions` map `stdPre m ⟶ stdPre N`; `ev` reads off its
top-cell value in `Cell N m`, and `trueCount` counts that cell's `1`-coordinates. -/
noncomputable def cubeAlt (N : ℕ) : ∀ m, (□N).cells m → ℤ :=
  fun _ x => (trueCount (ev x) : ℤ)

/-- The face map of `cube N` is precomposition by the coface (Yoneda). -/
theorem cube_faceMap (N : ℕ) {m : ℕ} (ε : Bool) (i : Fin (m + 1))
    (x : (□N).cells (m + 1)) :
    (□N).toPsh.faceMap ε i x = PrecubicalSet.coface ε i ≫ x := rfl

/-- `ev` of `coface ε i ≫ x` faces the top cell out at the freed coordinate, raising
`trueCount` by `ε` (the face axiom, computed via `ev_comp`/`trueCount_app`). -/
theorem cube_alt_axiom (N : ℕ) {m : ℕ} (ε : Bool) (i : Fin (m + 1))
    (x : (□N).cells (m + 1)) :
    cubeAlt N m ((□N).toPsh.faceMap ε i x)
      = cubeAlt N (m + 1) x + (if ε then 1 else 0) := by
  change (trueCount (ev ((□N).toPsh.faceMap ε i x)) : ℤ)
    = (trueCount (ev x) : ℤ) + (if ε then 1 else 0)
  -- `ev (coface ε i ≫ x) = app x (ev (coface ε i)) = app x (face ε i (topCell (m+1)))`
  have hev : ev ((□N).toPsh.faceMap ε i x)
      = act (ev x) (faceCell ε i (topCell (m + 1))) := by
    -- `ev (coface ≫ x) = Hom.app x (ev coface) = Hom.app x (face ε i ⊤)`;
    -- and `Hom.app x = Hom.app (canonicalMap (ev x)) = app (ev x)` (□Yoneda).
    have h1 : ev ((□N).toPsh.faceMap ε i x)
        = PrecubicalConstructions.Hom.app x m (ev (PrecubicalSet.coface ε i)) :=
      ev_comp (PrecubicalSet.coface ε i) x
    rw [h1, ev_coface]
    exact app_unique (c := ev x) x rfl (faceCell ε i (topCell (m + 1)))
  rw [hev, trueCount_app, trueCount_face, trueCount_topCell]
  push_cast
  ring

/-- **The standard cube admits an altitude.**  The altitude is `trueCount ∘ ev`; the
initial vertex `□⁰ ⟶ □ⁿ` is the constant-`false` vertex, whose pulled-back top cell
is the all-`0` vertex with `trueCount = 0`. -/
theorem cube_admitsAltitude (N : ℕ) : (□N).AdmitsAltitude := by
  refine ⟨cubeAlt N, fun ε i x => cube_alt_axiom N ε i x, ?_⟩
  -- `(□N).init = canonicalMap (constVertex N false)`, `ev` of which is that vertex.
  change (trueCount (ev ((□N).init)) : ℤ) = 0
  rw [show (□N).init = canonicalMap (constVertex N false) from rfl,
    ev_canonicalMap, trueCount_constVertex_false]
  rfl

/-! ## The binary wedge admits an altitude -/

section Wedge2

variable {X Y : BPSet}

/-- The cocone condition for the glued altitude: `altX` and the shifted `altY` agree
on the glued point `□⁰` (its only positive levels are empty; at level `0` the unique
vertex maps to `X.final` resp. `Y.init`, where the values match by `hY0`). -/
theorem wedge2Alt_cocone
    (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) (m : ℕ) :
    X.finalVertex⟪m⟫ ≫ TypeCat.ofHom (altX m)
      = Y.initVertex⟪m⟫
        ≫ TypeCat.ofHom (fun y => altY m y + altX 0 X.final) := by
  apply ConcreteCategory.hom_ext
  intro v
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hv : v = 𝟙 ▫0 :=
      Subsingleton.elim (α := (□0).cells 0) _ _
    have hxf : ConcreteCategory.hom (X.finalVertex⟪0⟫) v = X.final := by
      change (yonedaEquiv.symm X.final)⟪0⟫ v = X.final
      rw [yonedaEquiv_symm_app_apply, hv, op_id, X.toPsh.map_id]
      rfl
    have hyi : ConcreteCategory.hom (Y.initVertex⟪0⟫) v = Y.init := by
      change (yonedaEquiv.symm Y.init)⟪0⟫ v = Y.init
      rw [yonedaEquiv_symm_app_apply, hv, op_id, Y.toPsh.map_id]
      rfl
    rw [hxf, hyi]
    change altX 0 X.final = altY 0 Y.init + altX 0 X.final
    rw [hY0, zero_add]
  · exact ((CubeChain.cube0_cells_isEmpty hm).false v).elim

noncomputable def wedge2Alt
    (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) :
    ∀ m, (wedge2 X Y).cells m → ℤ :=
  fun m =>
    ConcreteCategory.hom
      ((CubeChain.wedge2_isPushout_app X Y m).desc (TypeCat.ofHom (altX m))
        (TypeCat.ofHom (fun y => altY m y + altX 0 X.final))
        (wedge2Alt_cocone altX altY hY0 m))

theorem wedge2Alt_inl (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) {m : ℕ} (x : X.cells m) :
    wedge2Alt altX altY hY0 m
        ((pushout.inl X.finalVertex Y.initVertex)⟪m⟫ x)
      = altX m x := by
  have h := (CubeChain.wedge2_isPushout_app X Y m).inl_desc (TypeCat.ofHom (altX m))
    (TypeCat.ofHom (fun y => altY m y + altX 0 X.final)) (wedge2Alt_cocone altX altY hY0 m)
  have h' := ConcreteCategory.congr_hom h x
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom] using h'

theorem wedge2Alt_inr (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) {m : ℕ} (y : Y.cells m) :
    wedge2Alt altX altY hY0 m
        ((pushout.inr X.finalVertex Y.initVertex)⟪m⟫ y)
      = altY m y + altX 0 X.final := by
  have h := (CubeChain.wedge2_isPushout_app X Y m).inr_desc (TypeCat.ofHom (altX m))
    (TypeCat.ofHom (fun y => altY m y + altX 0 X.final)) (wedge2Alt_cocone altX altY hY0 m)
  have h' := ConcreteCategory.congr_hom h y
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom] using h'

/-- Naturality of the left wedge inclusion against the face map: `faceMap` commutes
with `inl` (it is a natural transformation of presheaves). -/
theorem wedge2_inl_faceMap {m : ℕ} (ε : Bool) (i : Fin (m + 1)) (x : X.cells (m + 1)) :
    (wedge2 X Y).toPsh.faceMap ε i
        ((pushout.inl X.finalVertex Y.initVertex)⟪m + 1⟫ x)
      = (pushout.inl X.finalVertex Y.initVertex)⟪m⟫
          (X.toPsh.faceMap ε i x) := by
  exact ((pushout.inl X.finalVertex Y.initVertex).naturality_apply
    (PrecubicalSet.coface ε i).op x).symm

theorem wedge2_inr_faceMap {m : ℕ} (ε : Bool) (i : Fin (m + 1)) (y : Y.cells (m + 1)) :
    (wedge2 X Y).toPsh.faceMap ε i
        ((pushout.inr X.finalVertex Y.initVertex)⟪m + 1⟫ y)
      = (pushout.inr X.finalVertex Y.initVertex)⟪m⟫
          (Y.toPsh.faceMap ε i y) := by
  exact ((pushout.inr X.finalVertex Y.initVertex).naturality_apply
    (PrecubicalSet.coface ε i).op y).symm

/-- **The binary wedge admits an altitude.**  Glue the two altitude functions along
the pushout (`wedge2Alt`); the face axiom and basepoint condition follow case-by-case
on whether a cell comes from `X` (via `inl`) or `Y` (via `inr`). -/
theorem wedge2_admitsAltitude (hX : X.AdmitsAltitude) (hY : Y.AdmitsAltitude) :
    (wedge2 X Y).AdmitsAltitude := by
  obtain ⟨altX, haxX, hX0⟩ := hX
  obtain ⟨altY, haxY, hY0⟩ := hY
  refine ⟨wedge2Alt altX altY hY0, ?_, ?_⟩
  · -- face axiom: split the `(m+1)`-cell into an `inl` or `inr` cell.
    intro m ε i c
    rcases CubeChain.wedge2_cell_cases X Y (m + 1) c with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [wedge2_inl_faceMap, wedge2Alt_inl, wedge2Alt_inl, haxX ε i x]
    · rw [wedge2_inr_faceMap, wedge2Alt_inr, wedge2Alt_inr, haxY ε i y]
      ring
  · -- basepoint: `(wedge2 X Y).init = inl X.init`, altitude `altX X.init = 0`.
    rw [show (wedge2 X Y).init
        = (pushout.inl X.finalVertex Y.initVertex)⟪0⟫ X.init from rfl,
      wedge2Alt_inl]
    exact hX0

end Wedge2

/-! ## Serial wedges admit an altitude -/

/-- **Every serial wedge admits an altitude.**  By recursion on the dimension
sequence: `□⁰` is `cube 0`, and `⋁(n :: rest) = (□n) ∨ ⋁rest` admits an
altitude by `wedge2_admitsAltitude` from the head cube (`cube_admitsAltitude`) and the
tail (the recursive call). -/
theorem serialWedge_admitsAltitude : ∀ dims : List ℕ+, (⋁dims).AdmitsAltitude
  | [] => cube_admitsAltitude 0
  | n :: rest =>
      wedge2_admitsAltitude (cube_admitsAltitude (n : ℕ)) (serialWedge_admitsAltitude rest)

end BPSet
