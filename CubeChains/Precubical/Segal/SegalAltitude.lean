import CubeChains.Precubical.Basic.Altitude
import CubeChains.Precubical.Chains.WedgeMap

/-!
# Precubical/Segal/SegalAltitude

The `AdmitsAltitude` hypotheses the Segal splitting needs (`Precubical/Segal/Segal.lean` /
`Precubical/Segal/Split.lean`):

* `BPSet.cube_admitsAltitude`  — every standard cube `□ⁿ` admits an altitude,
  namely `trueCount ∘ ev` (the number of `1`-fixed coordinates of the pulled-back
  cell rises by `1` across a `target` face and is unchanged across a `source` face).
* `BPSet.wedge2_admitsAltitude` — `X ∨ Y` admits an altitude whenever both `X` and
  `Y` do, by gluing the two altitude functions (shifting `Y`'s up by `X.final`'s
  altitude so it strictly increases across the junction).
* `BPSet.serialWedge_admitsAltitude` — hence so does every serial wedge, by recursion.

These make the recursion over a serial wedge **hypothesis-free**: each `⋁(n :: rest)` step gets its
`AdmitsAltitude` argument from
`wedge2_admitsAltitude (cube_admitsAltitude n) (serialWedge_admitsAltitude rest)`.
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
  induction k, a using Cell.peelRec with
  | top a => rw [eq_topCell a, app_topCell, trueCount_topCell, Nat.add_zero]
  | step k a h ih =>
      rw [app_unfold (K := stdPre N) x a h]
      change trueCount (faceCell (minFixedVal a h) (minFixedIdx a h)
          (act (K := stdPre N) x (freeMin a h))) = trueCount x + trueCount a
      rw [trueCount_face, ih, trueCount_freeMin a h]
      ring

end StdCube

namespace BPSet

open StdCube CategoryTheory Opposite

/-! ## The standard cube admits an altitude -/

/-- The altitude on `□ⁿ`'s cells: the `true`-count of the pulled-back cell.  An
`m`-cell of `cube N` is a box morphism `□ᵐ ⟶ □ᴺ`, i.e. (definitionally) a
`PrecubicalConstructions` map `stdPre m ⟶ stdPre N`; `ev` reads off its
top-cell value in `Cell N m`, and `trueCount` counts that cell's `1`-coordinates. -/
def cubeAlt (N : ℕ) : ∀ m, (□N).cells m → ℤ :=
  fun _ x => (trueCount (ev x) : ℤ)

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

-- Descends through the *computable* `Glue.descCell` (a pointwise `Quot.lift`), not mathlib's
-- opaque `IsPushout.desc` — otherwise every consumer of an altitude becomes `noncomputable`.
def wedge2Alt
    (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) :
    ∀ m, (wedge2 X Y).cells m → ℤ :=
  fun m =>
    Glue.descCell (f := X.finalVertex) (g := Y.initVertex) (op ▫m)
      (altX m) (fun y => altY m y + altX 0 X.final)
      (fun s => by
        have h := ConcreteCategory.congr_hom (wedge2Alt_cocone altX altY hY0 m) s
        simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom] using h)

theorem wedge2Alt_inl (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) {m : ℕ} (x : X.cells m) :
    wedge2Alt altX altY hY0 m
        ((Glue.inl X.finalVertex Y.initVertex)⟪m⟫ x)
      = altX m x := Glue.descCell_inl _ x

theorem wedge2Alt_inr (altX : ∀ n, X.cells n → ℤ) (altY : ∀ n, Y.cells n → ℤ)
    (hY0 : altY 0 Y.init = 0) {m : ℕ} (y : Y.cells m) :
    wedge2Alt altX altY hY0 m
        ((Glue.inr X.finalVertex Y.initVertex)⟪m⟫ y)
      = altY m y + altX 0 X.final := Glue.descCell_inr _ y

/-- Naturality of a wedge inclusion against the face map: `faceMap` commutes with a presheaf map.
Stated at the two pushout legs, which is where `wedge2_admitsAltitude` needs it. -/
theorem wedge2_inl_faceMap {m : ℕ} (ε : Bool) (i : Fin (m + 1)) (x : X.cells (m + 1)) :
    (wedge2 X Y).toPsh.faceMap ε i
        ((Glue.inl X.finalVertex Y.initVertex)⟪m + 1⟫ x)
      = (Glue.inl X.finalVertex Y.initVertex)⟪m⟫ (X.toPsh.faceMap ε i x) :=
  ((Glue.inl X.finalVertex Y.initVertex).naturality_apply
    (PrecubicalSet.coface ε i).op x).symm

@[inherit_doc wedge2_inl_faceMap]
theorem wedge2_inr_faceMap {m : ℕ} (ε : Bool) (i : Fin (m + 1)) (y : Y.cells (m + 1)) :
    (wedge2 X Y).toPsh.faceMap ε i
        ((Glue.inr X.finalVertex Y.initVertex)⟪m + 1⟫ y)
      = (Glue.inr X.finalVertex Y.initVertex)⟪m⟫ (Y.toPsh.faceMap ε i y) :=
  ((Glue.inr X.finalVertex Y.initVertex).naturality_apply
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
    rcases CubeChain.glue0_cell_cases X.finalVertex Y.initVertex (m + 1) c with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rw [wedge2_inl_faceMap, wedge2Alt_inl, wedge2Alt_inl, haxX ε i x]
    · rw [wedge2_inr_faceMap, wedge2Alt_inr, wedge2Alt_inr, haxY ε i y]
      ring
  · -- basepoint: `(wedge2 X Y).init = inl X.init`, altitude `altX X.init = 0`.
    rw [show (wedge2 X Y).init
        = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.init from rfl,
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

/-! ## Chain-altitude arithmetic

How an altitude grows along a cube chain: each cube lifts the altitude by its own dimension, so
the `i`-th cube sits at the dimension prefix-sum `beadStart`. -/

namespace CubeChain

variable {K : BPSet}

/-- Where bead `i` of a dimension word starts: the total dimension of the earlier beads. -/
def beadStart (dims : List ℕ+) (i : ℕ) : ℕ := BPSet.dimSum (dims.take i)

@[simp] theorem beadStart_zero (dims : List ℕ+) : beadStart dims 0 = 0 := rfl

@[simp] theorem beadStart_length (dims : List ℕ+) :
    beadStart dims dims.length = BPSet.dimSum dims := by
  rw [beadStart, List.take_length]

/-- Peeling the head bead. -/
theorem beadStart_cons_succ (c : ℕ+) (rest : List ℕ+) (i : ℕ) :
    beadStart (c :: rest) (i + 1) = (c : ℕ) + beadStart rest i := by
  simp [beadStart, BPSet.dimSum]

/-- One-step increment: bead `i` occupies `[beadStart i, beadStart i + dims.get i)`. -/
theorem beadStart_succ (dims : List ℕ+) (i : Fin dims.length) :
    beadStart dims (i.val + 1) = beadStart dims i + (dims.get i : ℕ) := by
  simp only [beadStart, BPSet.dimSum, List.map_take]
  rw [List.sum_take_succ _ _ (by simp [i.isLt])]
  simp

theorem beadStart_mono (dims : List ℕ+) : Monotone (beadStart dims) := by
  intro i j hij
  obtain ⟨k, rfl⟩ := Nat.le.dest hij
  simp only [beadStart, BPSet.dimSum, List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- **Altitude gap of a chain = its total dimension.**  For any altitude, the final
vertex of a chain sits `∑ dims` above the initial one — each cube contributes its
dimension via `alt_vertex₀`/`alt_vertex₁` across the junction.  A vertex-level
companion to `isCubeChain_alt_get`. -/
theorem isCubeChain_alt_final (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q →
      alt 0 q = alt 0 p + ((BPSet.dimSum (cubes.map (·.1)) : ℕ) : ℤ)
  | [], p, q, h => by
      simp only [List.map_nil, BPSet.dimSum, List.sum_nil, Nat.cast_zero, add_zero]
      rw [h]
  | ⟨n, c⟩ :: rest, p, q, h => by
      obtain ⟨hsrc, hrest⟩ := h
      have ih := isCubeChain_alt_final alt hax rest (K.toPsh.vertexEnd true c) q hrest
      have h0 := PrecubicalSet.alt_vertex₀ alt hax c
      have h1 := PrecubicalSet.alt_vertex₁ alt hax c
      rw [hsrc] at h0
      simp only [List.map_cons, BPSet.dimSum, List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih, h1, ← h0]; simp only [BPSet.dimSum, List.map_map]; ring

/-- **Cube altitudes along a chain.**  The altitude of the `i`-th cube of a chain from
`p` to `q` is `alt p` plus the prefix-sum of the earlier cubes' dimensions.  (Each step
adds the previous cube's dimension, via `alt_vertex₀`/`alt_vertex₁` and the chain link.) -/
theorem isCubeChain_alt_get (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q → ∀ (i : ℕ) (h : i < cubes.length),
      alt _ (cubes.get ⟨i, h⟩).2 = alt 0 p + ((beadStart (cubes.map (·.1)) i : ℕ) : ℤ)
  | [], _, _, _, _, h => absurd h (by simp)
  | ⟨n, c⟩ :: rest, p, _, hchain, 0, _ => by
      obtain ⟨h1, _⟩ := hchain
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      simp only [beadStart_zero, Nat.cast_zero, add_zero]
      exact hc
  | ⟨n, c⟩ :: rest, p, q, hchain, k + 1, h => by
      obtain ⟨h1, h2⟩ := hchain
      have hk : k < rest.length := by simpa using h
      have ih := isCubeChain_alt_get alt hax rest (K.toPsh.vertexEnd true c) q h2 k hk
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      have hv1 : alt 0 (K.toPsh.vertexEnd true c) = alt 0 p + ((n : ℕ) : ℤ) := by
        rw [PrecubicalSet.alt_vertex₁ alt hax, hc]
      change alt ((rest.get ⟨k, hk⟩).1 : ℕ) (rest.get ⟨k, hk⟩).2
          = alt 0 p + ((beadStart ((⟨n, c⟩ :: rest).map (·.1)) (k + 1) : ℕ) : ℤ)
      rw [ih, hv1, List.map_cons, beadStart_cons_succ]
      push_cast
      ring

end CubeChain
