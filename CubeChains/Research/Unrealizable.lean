import CubeChains.Foundations.PrecubicalConstructions.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# Research/Unrealizable

The four-square loop: a chain-automorphism that no map of `K` realizes.
This file writes up, and verifies by brute force, the counter-example discussed in
`Unrealizable.md` at the root of the repository.  The claim it refutes is that
*bare functoriality forces coherent choices*: that every automorphism of the cube
chain category `Ch K` is induced by an automorphism of `K`.  It is **false**, and
the witness is finite — a loop of four squares.

## The set `K`

`K` is the precubical set with

* vertices (`0`-cells)  `o, w, w', z₁, z₂, t`;
* edges (`1`-cells)     `α : o→w`, `α' : o→w'`, `β₁ : w→z₁`, `β₂ : w→z₂`,
                        `γ₁ : w'→z₁`, `γ₂ : w'→z₂`, `δ₁ : z₁→t`, `δ₂ : z₂→t`;
* squares (`2`-cells)   `T₁₂, T₂₃, T₃₄, T₄₁`, the four "forks", and nothing in
  dimension `≥ 3`.

The four edge-paths `o ⤳ t` are

```
  m₁ = α β₁ δ₁,   m₂ = α β₂ δ₂,   m₃ = α' γ₂ δ₂,   m₄ = α' γ₁ δ₁,
```

and the four squares connect them in a cycle `m₁ — A — m₂ — B — m₃ — C — m₄ — D — m₁`,
where `A = (α, T₁₂)`, `B = (T₂₃, δ₂)`, `C = (α', T₃₄)`, `D = (T₄₁, δ₁)`.  The
relevant slice of `Ch K` (chains from `o` to `t`) is the **face poset of a
`4`-cycle**: four minimal elements `m₁,…,m₄` and four covering elements `A,…,D`,
each covering two consecutive `mᵢ`.

## What is verified here

* `K` is a genuine precubical set (`face_face` — the corner-coherence of all four
  squares, checked exhaustively).
* `ρ`, the rotation `mᵢ ↦ mᵢ₊₁`, `A↦B↦C↦D↦A`, **is a poset automorphism** of that
  slice (`arrow_ρ`/`arrow_ρ'`): a perfectly legitimate invertible functor.
* `ρ` **is not shape-preserving** (`ρ_not_dimSeq_preserving`): it sends shape
  `(1,2)` to `(2,1)`.  Equivalently, it moves a square off its altitude band
  (`ρ_moves_square_altitude`).  So it is **not** `OrientationPreserving` in the
  sense of the predicate of that name in `Chains/Category.lean`.
* `ρ` **is realized by no precubical map of `K`** (`ρ_not_realizable`): the
  incoherence `f α = α` and `f α = α'` forced at the very first edge.
* the honest swap `ρ² = (w↔w', z₁↔z₂)` **is** a precubical automorphism
  (`swapAut`), and it **does** realize `ρ²` on chains (`swap_realizes_ρ_sq`).

The upshot is exactly the resolution in `Unrealizable.md`: dropping shape /
orientation-preservation lets `Aut (Ch K)` strictly exceed the image of
`Aut K`; imposing it (the hypothesis `OrientationPreserving` in
`Conjectures.lower_orientationPreserving`) is what is needed to recover the
lifting.  This file is therefore a concrete witness for the **necessity** of that
hypothesis.

## What is missing (infrastructure gaps surfaced by this exercise)

The whole development lives at the **concrete** level `PrecubicalConstructions`,
because the chain/automorphism machinery (`BPSet`, `Ch`, `Aut (Ch.obj K)`) is
built over the **topos** `PrecubicalSet = Boxᵒᵖ ⥤ Type`, and there is currently

* **no nerve / restricted-Yoneda functor** `PrecubicalConstructions ⥤ PrecubicalSet`
  to turn a finite concrete set into a presheaf, and
* **no discharged equivalence** `PrecubicalSet ≌ PrecubicalConstructions`
  (it rests on the deferred cube-Yoneda lemma `StdCube.cubeRepr`).

So a finite example cannot yet be *fed to* `Ch`/`Aut (Ch.obj K)`.  The poset side
is therefore modelled here by an explicit `8`-element type (`ChObj`) with its
covering relation, rather than reusing `ChainCat.Obj`.  Closing the nerve +
equivalence is exactly what would let this counter-example be stated against the
real `Aut (Ch.obj K)` and `Aut.liftToCh`.

**Layer:** Research.  **Imports:** `Foundations/PrecubicalConstructions/Basic`,
mathlib `Endomorphism`/`FinCases`.
-/

open CategoryTheory

namespace Unrealizable

/-! ## The cells of `K` -/

/-- Vertices (`0`-cells) of `K`. -/
inductive UVtx | o | w | w' | z₁ | z₂ | t
  deriving DecidableEq

/-- Edges (`1`-cells) of `K`. -/
inductive UEdge | α | α' | β₁ | β₂ | γ₁ | γ₂ | δ₁ | δ₂
  deriving DecidableEq

/-- Squares (`2`-cells) of `K`. -/
inductive USq | T₁₂ | T₂₃ | T₃₄ | T₄₁
  deriving DecidableEq

/-- The source (`ε = false`, `d⁰`) and target (`ε = true`, `d¹`) vertex of each edge. -/
def edgeFace : Bool → UEdge → UVtx
  | false, .α  => .o  | true, .α  => .w
  | false, .α' => .o  | true, .α' => .w'
  | false, .β₁ => .w  | true, .β₁ => .z₁
  | false, .β₂ => .w  | true, .β₂ => .z₂
  | false, .γ₁ => .w' | true, .γ₁ => .z₁
  | false, .γ₂ => .w' | true, .γ₂ => .z₂
  | false, .δ₁ => .z₁ | true, .δ₁ => .t
  | false, .δ₂ => .z₂ | true, .δ₂ => .t

/-- The coordinate-`0` faces of a square (`false = left = d⁰₀`, `true = right = d¹₀`).

The orientations are chosen so that the honest swap `w↔w', z₁↔z₂` is a *plain*
precubical map (see `swapHom`); a different orientation of `T₃₄`/`T₄₁` would force a
coordinate transposition and only land in symmetric-precubical sets. -/
def sqFace0 : Bool → USq → UEdge
  | false, .T₁₂ => .β₂ | true, .T₁₂ => .δ₁
  | false, .T₂₃ => .α' | true, .T₂₃ => .β₂
  | false, .T₃₄ => .γ₁ | true, .T₃₄ => .δ₂
  | false, .T₄₁ => .α  | true, .T₄₁ => .γ₁

/-- The coordinate-`1` faces of a square (`false = bottom = d⁰₁`, `true = top = d¹₁`). -/
def sqFace1 : Bool → USq → UEdge
  | false, .T₁₂ => .β₁ | true, .T₁₂ => .δ₂
  | false, .T₂₃ => .α  | true, .T₂₃ => .γ₂
  | false, .T₃₄ => .γ₂ | true, .T₃₄ => .δ₁
  | false, .T₄₁ => .α' | true, .T₄₁ => .β₁

/-- The face of a square at coordinate `i : Fin 2`. -/
def sqFace (ε : Bool) (i : Fin 2) (s : USq) : UEdge :=
  if i = 0 then sqFace0 ε s else sqFace1 ε s

/-! ## `K` as a precubical set -/

/-- The graded family of cells: vertices, edges, squares, nothing above. -/
def Kcells : ℕ → Type
  | 0 => UVtx
  | 1 => UEdge
  | 2 => USq
  | _ + 3 => PEmpty

-- `DecidableEq` on each level, so `decide` can close the finite face computations
-- (the equands are typed `Kcells n`, which is only defeq — not syntactically — to the
-- underlying enum).
instance : DecidableEq (Kcells 0) := inferInstanceAs (DecidableEq UVtx)
instance : DecidableEq (Kcells 1) := inferInstanceAs (DecidableEq UEdge)
instance : DecidableEq (Kcells 2) := inferInstanceAs (DecidableEq USq)

/-- The face map of `K`: edge faces in dimension `0`, square faces in dimension `1`,
and vacuous above (there are no cells of dimension `≥ 3`). -/
def Kface : {n : ℕ} → Bool → Fin (n + 1) → Kcells (n + 1) → Kcells n
  | 0,     ε, _, e => edgeFace ε e
  | 1,     ε, i, s => sqFace ε i s
  | _ + 2, _, _, c => c.elim

/-- The four-square loop `K` as a (concrete) precubical set.  The only content is
the precubical identity, i.e. the corner-coherence of the four squares, checked
exhaustively. -/
def K : PrecubicalConstructions where
  cells := Kcells
  face := fun {_} ε i c => Kface ε i c
  face_face := by
    intro n ε η i j _ c
    cases n with
    | zero =>
        fin_cases i
        fin_cases j
        cases c <;> cases ε <;> cases η <;> decide
    | succ n => exact (c : PEmpty).elim

/-! ## Sanity: the edge-paths are genuine directed paths `o ⤳ t`

These `rfl`-checks exercise the concrete `vertex₀`/`vertex₁` API on `K` and confirm
the links of the chain `m₁ = α β₁ δ₁`. -/

example : K.vertex₀ (show K.cells 1 from UEdge.α) = (UVtx.o : K.cells 0) := rfl
example : K.vertex₁ (show K.cells 1 from UEdge.α) = (UVtx.w : K.cells 0) := rfl
/-- The first link of `m₁`: target of `α` = source of `β₁` = `w`. -/
example : K.vertex₁ (show K.cells 1 from UEdge.α) = K.vertex₀ (show K.cells 1 from UEdge.β₁) := rfl
/-- The second link of `m₁`: target of `β₁` = source of `δ₁` = `z₁`. -/
example : K.vertex₁ (show K.cells 1 from UEdge.β₁) = K.vertex₀ (show K.cells 1 from UEdge.δ₁) := rfl

/-! ## An altitude function on `K`

`K` *does* admit an altitude (height rising by `1` across target faces, unchanged
across source faces): this is the "directed monodromy gadget" of `Unrealizable.md`,
and the point is that altitude alone does **not** rule out the rotation `ρ`. -/

/-- Altitude of vertices: distance from `o`. -/
def altV : UVtx → ℤ
  | .o => 0 | .w => 1 | .w' => 1 | .z₁ => 2 | .z₂ => 2 | .t => 3

/-- Altitude of edges (= altitude of the source vertex). -/
def altE : UEdge → ℤ
  | .α => 0 | .α' => 0 | .β₁ => 1 | .β₂ => 1 | .γ₁ => 1 | .γ₂ => 1 | .δ₁ => 2 | .δ₂ => 2

/-- Altitude of squares (= altitude of the initial corner). -/
def altS : USq → ℤ
  | .T₁₂ => 1 | .T₂₃ => 0 | .T₃₄ => 1 | .T₄₁ => 0

/-- The altitude function on all cells of `K`. -/
def altK : (n : ℕ) → K.cells n → ℤ
  | 0 => altV
  | 1 => altE
  | 2 => altS
  | _ + 3 => fun _ => 0

/-- `K` admits an altitude function: it rises by `1` across a target face and is
unchanged across a source face. -/
theorem K_admits_altitude {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : K.cells (n + 1)) :
    altK n (K.face ε i c) = altK (n + 1) c + (if ε then 1 else 0) := by
  rcases n with _ | _ | m
  · fin_cases i
    cases c <;> cases ε <;> decide
  · fin_cases i <;> (cases c <;> cases ε <;> decide)
  · exact (c : PEmpty).elim

/-! ## The chain poset slice `Ch(K)₀¹` as the face poset of a 4-cycle

We model the eight objects directly (see the file header for why we cannot yet
reuse `ChainCat.Obj`). -/

/-- The eight objects of the chain slice: the four edge-paths and the four
square-chains. -/
inductive ChObj | m₁ | m₂ | m₃ | m₄ | A | B | C | D
  deriving DecidableEq

namespace ChObj

/-- The dimension sequence (shape) of each chain. `mᵢ` are `(1,1,1)`; `A,C` are
edge-then-square `(1,2)`; `B,D` are square-then-edge `(2,1)`. -/
def dimSeq : ChObj → List ℕ
  | m₁ | m₂ | m₃ | m₄ => [1, 1, 1]
  | A | C => [1, 2]
  | B | D => [2, 1]

/-- The single square sitting inside each square-chain (none for the edge-paths). -/
def chainSquare : ChObj → Option USq
  | A => some .T₁₂ | B => some .T₂₃ | C => some .T₃₄ | D => some .T₄₁
  | _ => none

/-- The ordered edges of each edge-path (none for the square-chains). -/
def edgePath : ChObj → Option (UEdge × UEdge × UEdge)
  | m₁ => some (.α, .β₁, .δ₁)
  | m₂ => some (.α, .β₂, .δ₂)
  | m₃ => some (.α', .γ₂, .δ₂)
  | m₄ => some (.α', .γ₁, .δ₁)
  | _ => none

/-- The covering ("subdivision") arrows of the poset: each square-chain covers the
two edge-paths it resolves to.  This is the face poset of the `4`-cycle
`m₁ — A — m₂ — B — m₃ — C — m₄ — D — m₁`.

It is `Prop`-valued, so the slice is automatically **thin** (at most one arrow per
pair, by proof irrelevance) — matching `Conjectures.hom_subsingleton`. -/
inductive Arrow : ChObj → ChObj → Prop
  | Am₁ : Arrow A m₁ | Am₂ : Arrow A m₂
  | Bm₂ : Arrow B m₂ | Bm₃ : Arrow B m₃
  | Cm₃ : Arrow C m₃ | Cm₄ : Arrow C m₄
  | Dm₄ : Arrow D m₄ | Dm₁ : Arrow D m₁

/-- The rotation `ρ` of `Unrealizable.md`: `mᵢ ↦ mᵢ₊₁` and `A↦B↦C↦D↦A`. -/
def ρ : ChObj → ChObj
  | m₁ => m₂ | m₂ => m₃ | m₃ => m₄ | m₄ => m₁
  | A => B | B => C | C => D | D => A

/-- The inverse rotation. -/
def ρ' : ChObj → ChObj
  | m₁ => m₄ | m₂ => m₁ | m₃ => m₂ | m₄ => m₃
  | A => D | B => A | C => B | D => C

@[simp] theorem ρ'_ρ (p : ChObj) : ρ' (ρ p) = p := by cases p <;> rfl
@[simp] theorem ρ_ρ' (p : ChObj) : ρ (ρ' p) = p := by cases p <;> rfl

/-- `ρ` is a bijection. -/
theorem ρ_bijective : Function.Bijective ρ :=
  ⟨Function.LeftInverse.injective ρ'_ρ, Function.RightInverse.surjective ρ_ρ'⟩

/-- **`ρ` preserves the covering relation**: it is a legitimate poset functor. -/
theorem arrow_ρ {x y : ChObj} (h : Arrow x y) : Arrow (ρ x) (ρ y) := by
  cases h with
  | Am₁ => exact .Bm₂ | Am₂ => exact .Bm₃
  | Bm₂ => exact .Cm₃ | Bm₃ => exact .Cm₄
  | Cm₃ => exact .Dm₄ | Cm₄ => exact .Dm₁
  | Dm₄ => exact .Am₁ | Dm₁ => exact .Am₂

/-- The inverse rotation preserves the covering relation too. -/
theorem arrow_ρ' {x y : ChObj} (h : Arrow x y) : Arrow (ρ' x) (ρ' y) := by
  cases h with
  | Am₁ => exact .Dm₄ | Am₂ => exact .Dm₁
  | Bm₂ => exact .Am₁ | Bm₃ => exact .Am₂
  | Cm₃ => exact .Bm₂ | Cm₄ => exact .Bm₃
  | Dm₄ => exact .Cm₃ | Dm₁ => exact .Cm₄

/-- **`ρ` is an order-automorphism** of the chain slice: `Arrow x y ↔ Arrow (ρx)(ρy)`. -/
theorem arrow_ρ_iff {x y : ChObj} : Arrow x y ↔ Arrow (ρ x) (ρ y) :=
  ⟨arrow_ρ, fun h => by simpa using arrow_ρ' h⟩

/-- **`ρ` is *not* shape-preserving**: it carries `A` (shape `(1,2)`) to `B`
(shape `(2,1)`).  Hence `ρ` is not `OrientationPreserving`. -/
theorem ρ_not_dimSeq_preserving : dimSeq (ρ A) ≠ dimSeq A := by decide

/-- **`ρ`'s altitude certificate**: it moves the square inside `A` (`T₁₂`, altitude
`1`) to the square inside `B` (`T₂₃`, altitude `0`).  A genuine automorphism of `K`
must fix each cell's altitude, so this already shows `ρ ∉ Aut K`. -/
theorem ρ_moves_square_altitude :
    (chainSquare (ρ A)).map altS ≠ (chainSquare A).map altS := by decide

/-- By contrast `ρ² = ρ ∘ ρ` **is** shape-preserving. -/
theorem ρ_sq_dimSeq_preserving (p : ChObj) : dimSeq (ρ (ρ p)) = dimSeq p := by
  cases p <;> rfl

end ChObj

/-! ## The realizability obstruction

A precubical map `f : K ⟶ K` acts cell-wise; in particular it acts position-wise on
each edge-path.  We say `f` *realizes* a permutation `g` of the chain slice when
applying `f` to the edges of every edge-path `p` produces the edges of `g p`. -/

open ChObj

/-- `f : K ⟶ K` realizes the chain permutation `g` (on the edge-paths). -/
def Realizes (g : ChObj → ChObj) (f : K ⟶ K) : Prop :=
  ∀ (p : ChObj) (e₁ e₂ e₃ : UEdge), edgePath p = some (e₁, e₂, e₃) →
    edgePath (g p) = some (f.app 1 e₁, f.app 1 e₂, f.app 1 e₃)

/-- **The rotation `ρ` is realized by no precubical map of `K`.**

This is the heart of the counter-example.  If some `f` realized `ρ`, then:

* from `m₁ ↦ m₂` (both start with `α`):   `f α = α`;
* from `m₂ ↦ m₃` (`m₂` starts `α`, `m₃` starts `α'`):  `f α = α'`.

So `α = α'`, which is false.  The shared first edge `α` is forced to two different
images — the within-altitude incoherence predicted in `Unrealizable.md`. -/
theorem ρ_not_realizable : ¬ ∃ f : K ⟶ K, Realizes ρ f := by
  rintro ⟨f, hf⟩
  -- `f α = α`, read off `ρ m₁ = m₂`.
  have e1 : (some (.α, .β₂, .δ₂) : Option (UEdge × UEdge × UEdge))
      = some (f.app 1 .α, f.app 1 .β₁, f.app 1 .δ₁) := hf .m₁ .α .β₁ .δ₁ rfl
  -- `f α = α'`, read off `ρ m₂ = m₃`.
  have e2 : (some (.α', .γ₂, .δ₂) : Option (UEdge × UEdge × UEdge))
      = some (f.app 1 .α, f.app 1 .β₂, f.app 1 .δ₂) := hf .m₂ .α .β₂ .δ₂ rfl
  have ha1 : f.app 1 UEdge.α = UEdge.α := (congrArg (·.1) (Option.some.inj e1)).symm
  have ha2 : f.app 1 UEdge.α = UEdge.α' := (congrArg (·.1) (Option.some.inj e2)).symm
  exact UEdge.noConfusion (ha1.symm.trans ha2)

/-! ## The realizable symmetry `ρ² = (w↔w', z₁↔z₂)`

The honest swap *is* a precubical automorphism, and it realizes `ρ²` — the
shape-preserving part of the picture survives. -/

/-- The swap on vertices. -/
def swapV : UVtx → UVtx
  | .o => .o | .w => .w' | .w' => .w | .z₁ => .z₂ | .z₂ => .z₁ | .t => .t

/-- The swap on edges (`e : u→v ↦ swapV u → swapV v`). -/
def swapE : UEdge → UEdge
  | .α => .α' | .α' => .α | .β₁ => .γ₂ | .β₂ => .γ₁
  | .γ₁ => .β₂ | .γ₂ => .β₁ | .δ₁ => .δ₂ | .δ₂ => .δ₁

/-- The swap on squares. -/
def swapS : USq → USq
  | .T₁₂ => .T₃₄ | .T₃₄ => .T₁₂ | .T₂₃ => .T₄₁ | .T₄₁ => .T₂₃

/-- The cell-wise swap map. -/
def swapApp : (n : ℕ) → Kcells n → Kcells n
  | 0 => swapV
  | 1 => swapE
  | 2 => swapS
  | _ + 3 => id

/-- The swap commutes with faces (the orientation choices in `sqFace0`/`sqFace1` are
exactly what make this hold).  Kept as a standalone lemma because `·`-bullets do not
parse inside a `def … where` field. -/
theorem swapApp_face {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : K.cells (n + 1)) :
    swapApp n (K.face ε i c) = K.face ε i (swapApp (n + 1) c) := by
  rcases n with _ | _ | m
  · fin_cases i
    cases c <;> cases ε <;> rfl
  · fin_cases i <;> (cases c <;> cases ε <;> rfl)
  · exact (c : PEmpty).elim

/-- The swap as a precubical endomorphism of `K`. -/
def swapHom : K ⟶ K where
  app := swapApp
  app_face := swapApp_face

/-- The swap is an involution. -/
theorem swapHom_involutive : swapHom ≫ swapHom = 𝟙 K := by
  apply PrecubicalConstructions.hom_ext
  intro n c
  rcases n with _ | _ | _ | m
  · cases c <;> rfl
  · cases c <;> rfl
  · cases c <;> rfl
  · exact (c : PEmpty).elim

/-- **The honest swap `ρ² = (w↔w', z₁↔z₂)` is a genuine automorphism of `K`.** -/
def swapAut : Aut K where
  hom := swapHom
  inv := swapHom
  hom_inv_id := swapHom_involutive
  inv_hom_id := swapHom_involutive

/-- The swap is *not* the identity (it moves `α`), so `Aut K` is non-trivial. -/
theorem swapHom_ne_id : swapHom ≠ 𝟙 K := by
  intro h
  have h2 : (UEdge.α' : K.cells 1) = (UEdge.α : K.cells 1) :=
    congrArg (fun f : K ⟶ K => f.app 1 UEdge.α) h
  exact UEdge.noConfusion h2

/-- **The swap realizes `ρ²` on chains.**  Contrast `ρ_not_realizable`: the
*shape-preserving* rotation `ρ²` is induced by an automorphism of `K`, while the
shape-changing `ρ` is not. -/
theorem swap_realizes_ρ_sq : Realizes (ρ ∘ ρ) swapHom := by
  rintro p e₁ e₂ e₃ h
  cases p
  · obtain ⟨rfl, rfl, rfl⟩ : UEdge.α = e₁ ∧ UEdge.β₁ = e₂ ∧ UEdge.δ₁ = e₃ := by
      simpa [edgePath] using h
    rfl
  · obtain ⟨rfl, rfl, rfl⟩ : UEdge.α = e₁ ∧ UEdge.β₂ = e₂ ∧ UEdge.δ₂ = e₃ := by
      simpa [edgePath] using h
    rfl
  · obtain ⟨rfl, rfl, rfl⟩ : UEdge.α' = e₁ ∧ UEdge.γ₂ = e₂ ∧ UEdge.δ₂ = e₃ := by
      simpa [edgePath] using h
    rfl
  · obtain ⟨rfl, rfl, rfl⟩ : UEdge.α' = e₁ ∧ UEdge.γ₁ = e₂ ∧ UEdge.δ₁ = e₃ := by
      simpa [edgePath] using h
    rfl
  all_goals simp [edgePath] at h

end Unrealizable
