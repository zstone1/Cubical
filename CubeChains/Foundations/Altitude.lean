import CubeChains.Foundations.Bipointed
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Defs

/-!
# Foundations/Altitude

The side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
all at the `PrecubicalSet` level, plus the altitude-of-pulled-back-cell theory
(`IsAltitude`, `alt_map_eq`, `alt_vertex₀/₁`, `alt_cubeMap`).

Face maps pull back along the *coface* box morphisms; `NonSelfLinked` is phrased
via the Yoneda canonical map.
-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-- **The altitude axiom** for a candidate height function `alt` on the cells of a
precubical set `X`: altitude rises by `1` across target faces (`ε = true`) and is
unchanged across source faces (`ε = false`). -/
def IsAltitude (X : PrecubicalSet) (alt : ∀ n, X.cells n → ℤ) : Prop :=
  ∀ {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : X.cells (n + 1)),
    alt n (X.faceMap ε i c) = alt (n + 1) c + (if ε then 1 else 0)

/-- `X` is *non-self-linked*: the canonical map `□ⁿ ⟶ X` of every cube is injective
in every dimension (via the Yoneda canonical map). -/
def NonSelfLinked (X : PrecubicalSet) : Prop :=
  ∀ (n : ℕ) (c : X.cells n) (m : ℕ),
    Function.Injective ((X.cubeMap c)⟪m⟫)

end PrecubicalSet

namespace BPSet

/-- `K` *admits an altitude function*: an integer height on cells rising by `1`
across target faces and unchanged across source faces, with `init` at height `0`. -/
def AdmitsAltitude (K : BPSet) : Prop :=
  ∃ alt : ∀ n, K.cells n → ℤ,
    K.toPsh.IsAltitude alt ∧ alt 0 K.init = 0

/-- The one-step reachability relation generating the accessibility preorder:
`face false i c ≼ c` and `c ≼ face true i c`, closed under reflexivity and
transitivity, on cells of all dimensions. -/
inductive Reach (K : BPSet) : (Σ n, K.cells n) → (Σ n, K.cells n) → Prop
  | refl (x) : Reach K x x
  | source {n} (i : Fin (n + 1)) (c : K.cells (n + 1)) :
      Reach K ⟨n, K.toPsh.faceMap false i c⟩ ⟨n + 1, c⟩
  | target {n} (i : Fin (n + 1)) (c : K.cells (n + 1)) :
      Reach K ⟨n + 1, c⟩ ⟨n, K.toPsh.faceMap true i c⟩
  | trans {x y z} : Reach K x y → Reach K y z → Reach K x z

/-- `K` is *accessible*: every cell lies between `init` and `final` for the
reachability preorder. -/
def Accessible (K : BPSet) : Prop :=
  ∀ c : Σ n, K.cells n, Reach K ⟨0, K.init⟩ c ∧ Reach K c ⟨0, K.final⟩

/-- `K` is *non-self-linked*: the canonical map `□ⁿ ⟶ K` of every cube is
injective in every dimension (via the Yoneda canonical map).
Thin wrapper around `PrecubicalSet.NonSelfLinked` on the underlying presheaf. -/
def NonSelfLinked (K : BPSet) : Prop := K.toPsh.NonSelfLinked

end BPSet

/-! ### Altitude of pulled-back cells

For the embedding theorem (`descent_mono`) we need that pulling a cell `c : K.cells n`
back along a box morphism (a cell `a` of `□ⁿ`) shifts altitude by the number of
coordinates that `a` fixes to `true`.  The `trueCount` invariant and the
canonical-map combinatorics it relies on live in `Representable.lean`. -/

namespace PrecubicalSet

open StdCube CategoryTheory Opposite

variable {X : PrecubicalSet}

/-- **Altitude of a pulled-back cell.**  Pulling `x : X.cells N` back along the box
morphism classified by a cell `c'` of `□ᴺ` shifts altitude by the number of
coordinates `c'` fixes to `true`.  Proved by peeling cofaces (`canonicalMap_peel`),
using the altitude axiom (`IsAltitude`) one face at a time. -/
theorem alt_map_eq (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : Cell N k),
      alt k (X.map (canonicalMap c').op x) = alt N x + trueCount c' := by
  intro k c'
  induction hd : N - k using Nat.strong_induction_on generalizing k c' with
  | _ d ih =>
    rcases Nat.lt_or_ge k N with h | h
    · have e1 : X.map (canonicalMap c').op x
          = X.map (PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
              ≫ canonicalMap (freeMin c' h)).op x :=
        congrArg (fun m => X.map (Quiver.Hom.op m) x) (canonicalMap_peel c' h)
      have hstep : X.map (canonicalMap c').op x
          = X.faceMap (minFixedVal c' h) (minFixedIdx c' h)
            (X.map (canonicalMap (freeMin c' h)).op x) := by
        rw [e1, op_comp, Functor.map_comp]; rfl
      rw [hstep, hax, ih (N - (k + 1)) (by omega) (freeMin c' h) rfl, trueCount_freeMin c' h]
      cases minFixedVal c' h <;> push_cast <;> ring
    · have hkN : k = N := le_antisymm (cells_card_le c') h
      subst hkN
      rw [eq_topCell c']
      -- `erw`: `Box`'s homs *are* cube maps, so `canonicalMap_topCell` (stated in
      -- `PrecubicalConstructions`) matches the `Box` composite only up to that defeq bridge.
      erw [canonicalMap_topCell, op_id, X.map_id]
      simp [trueCount_topCell]

/-- The altitude of the source vertex equals the altitude of the cell. -/
theorem alt_vertex₀ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertex₀ x) = alt N x := by
  have h := alt_map_eq alt hax x (constVertex N false)
  rwa [trueCount_constVertex_false, Nat.cast_zero, add_zero] at h

/-- The altitude of the target vertex is `N` above the cell's altitude. -/
theorem alt_vertex₁ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertex₁ x) = alt N x + N := by
  have h := alt_map_eq alt hax x (constVertex N true)
  rwa [trueCount_constVertex_true] at h

/-- The altitude of a face `(cubeMap c).app x` of an `n`-cube `c`, classified by a
box morphism `x : □ᵐ ⟶ □ⁿ`, exceeds `alt c` by `trueCount (ev x) ≤ n - m`. -/
theorem alt_cubeMap (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {n : ℕ} (c : X.cells n) {m : ℕ} (x : ▫m ⟶ ▫n) :
    alt m ((X.cubeMap c)⟪m⟫ x)
      = alt n c + trueCount (ev x) := by
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  conv_lhs => rw [show x = canonicalMap (ev x) from
    ((cubeRepr (stdPre n) m).left_inv x).symm]
  exact alt_map_eq alt hax c (ev x)

end PrecubicalSet
