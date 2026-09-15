import CubeChains.Precubical.Basic.Bipointed
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Defs

/-!
# Precubical/Basic/Altitude

The side conditions `NonSelfLinked` / `AdmitsAltitude`, and the altitude of a pulled-back cell:
pulling back along a `□ᴺ`-cell shifts altitude by the number of coordinates that cell fixes to
`true` (`alt_map_eq`), whence the two extremal vertices.

`NonSelfLinked` is phrased via the Yoneda canonical map, so it is a statement about cube maps,
not about faces.
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

def NonSelfLinked (K : BPSet) : Prop := K.toPsh.NonSelfLinked

end BPSet

/-- **An altitude pulls back along any map**: face maps are natural. -/
theorem PrecubicalSet.IsAltitude.comp {X Y : PrecubicalSet} {alt : ∀ n, Y.cells n → ℤ}
    (h : Y.IsAltitude alt) (φ : X ⟶ Y) : X.IsAltitude fun n x => alt n (φ⟪n⟫ x) :=
  fun ε i c => (congrArg (alt _) (NatTrans.naturality_apply φ (coface ε i).op c)).trans (h ε i _)

/-- …and along a bi-pointed map, which keeps the base point at height `0`. -/
theorem BPSet.AdmitsAltitude.of_hom {K L : BPSet} (f : K ⟶ L) (h : L.AdmitsAltitude) :
    K.AdmitsAltitude :=
  h.elim fun alt ⟨hax, h0⟩ =>
    ⟨fun n x => alt n (f.hom⟪n⟫ x), hax.comp f.hom, (congrArg (alt 0) f.app_init).trans h0⟩

namespace PrecubicalSet

open StdCube CategoryTheory Opposite

variable {X : PrecubicalSet}

/-- **Altitude of a pulled-back cell.**  Pulling `x : X.cells N` back along the box
morphism classified by a cell `c'` of `□ᴺ` shifts altitude by the number of
coordinates `c'` fixes to `true`. -/
theorem alt_map_eq (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : Cell N k),
      alt k (X.map (Box.ofSign c').op x) = alt N x + trueCount c' := by
  intro k c'
  induction k, c' using Cell.peelRec with
  | top c' =>
      rw [X.map_ofSign_top x c', eq_topCell c', trueCount_topCell]
      simp
  | step k c' h ih =>
      rw [X.map_ofSign_peel x c' h, hax, ih, trueCount_freeMin c' h]
      cases minFixedVal c' h <;> push_cast <;> ring

/-- The altitude of the source vertex equals the altitude of the cell. -/
theorem alt_vertex₀ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertexEnd false x) = alt N x := by
  have h := alt_map_eq alt hax x (constVertex N false)
  rwa [trueCount_constVertex_false, Nat.cast_zero, add_zero] at h

/-- The altitude of the target vertex is `N` above the cell's altitude. -/
theorem alt_vertex₁ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertexEnd true x) = alt N x + N := by
  have h := alt_map_eq alt hax x (constVertex N true)
  rwa [trueCount_constVertex_true] at h

/-- The altitude of a face `(cubeMap c).app x` of an `n`-cube `c`, classified by a
box morphism `x : □ᵐ ⟶ □ⁿ`, exceeds `alt c` by `trueCount (Box.sign x) ≤ n - m`. -/
theorem alt_cubeMap (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {n : ℕ} (c : X.cells n) {m : ℕ} (x : ▫m ⟶ ▫n) :
    alt m ((X.cubeMap c)⟪m⟫ x)
      = alt n c + trueCount (Box.sign x) := by
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  conv_lhs => rw [show x = Box.ofSign (Box.sign x) from (Box.ofSign_sign x).symm]
  exact alt_map_eq alt hax c (Box.sign x)

end PrecubicalSet
