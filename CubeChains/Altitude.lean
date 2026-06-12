import CubeChains.Bipointed
import Mathlib.CategoryTheory.Yoneda

/-!
# Side conditions: altitude, accessibility, non-self-linked (ClaudeSetup.md §6)

Working over the topos `PrecubicalSet`.  The face maps are pulled back along the
*coface* box morphisms `□ⁿ ⟶ □ⁿ⁺¹` (built from `StdCube.canonicalMap`, hence
depending on the deferred cube Yoneda lemma).  `NonSelfLinked` is phrased via the
Yoneda canonical map and needs no `sorry`.
-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-- The coface `□ⁿ ⟶ □ⁿ⁺¹` selecting the `(ε, i)`-face of the top cell. -/
noncomputable def coface (ε : Bool) {n : ℕ} (i : Fin (n + 1)) : Box.ob n ⟶ Box.ob (n + 1) :=
  StdCube.canonicalMap (StdCube.face ε i (StdCube.topCell (n + 1)))

/-- The face map `cells (n+1) → cells n` of a precubical set: pull back along the
coface. -/
noncomputable def faceMap (X : PrecubicalSet) (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (c : X.cells (n + 1)) : X.cells n :=
  X.map (coface ε i).op c

/-- The canonical map `□ⁿ ⟶ X` classifying an `n`-cell `c` (Yoneda). -/
noncomputable def cubeMap (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    yoneda.obj (Box.ob n) ⟶ X :=
  yonedaEquiv.symm c

end PrecubicalSet

namespace BPSet

/-- `K` *admits an altitude function*: an integer height on cells rising by `1`
across target faces and unchanged across source faces, with `init` at height `0`
(ClaudeSetup.md §6). -/
def AdmitsAltitude (K : BPSet) : Prop :=
  ∃ alt : ∀ n, K.toPsh.cells n → ℤ,
    (∀ {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)),
      alt n (K.toPsh.faceMap ε i c) = alt (n + 1) c + (if ε then 1 else 0)) ∧
    alt 0 K.init = 0

/-- The one-step reachability relation generating the accessibility preorder:
`face false i c ≼ c` and `c ≼ face true i c`, closed under reflexivity and
transitivity, on cells of all dimensions. -/
inductive Reach (K : BPSet) : (Σ n, K.toPsh.cells n) → (Σ n, K.toPsh.cells n) → Prop
  | refl (x) : Reach K x x
  | source {n} (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) :
      Reach K ⟨n, K.toPsh.faceMap false i c⟩ ⟨n + 1, c⟩
  | target {n} (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) :
      Reach K ⟨n + 1, c⟩ ⟨n, K.toPsh.faceMap true i c⟩
  | trans {x y z} : Reach K x y → Reach K y z → Reach K x z

/-- `K` is *accessible*: every cell lies between `init` and `final` for the
reachability preorder (ClaudeSetup.md §6). -/
def Accessible (K : BPSet) : Prop :=
  ∀ c : Σ n, K.toPsh.cells n, Reach K ⟨0, K.init⟩ c ∧ Reach K c ⟨0, K.final⟩

/-- `K` is *non-self-linked*: the canonical map `□ⁿ ⟶ K` of every cube is
injective in every dimension (ClaudeSetup.md §6, via the Yoneda canonical map). -/
def NonSelfLinked (K : BPSet) : Prop :=
  ∀ (n : ℕ) (c : K.toPsh.cells n) (m : ℕ),
    Function.Injective ((K.toPsh.cubeMap c).app (op (Box.ob m)))

end BPSet
