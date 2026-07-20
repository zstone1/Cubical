import CubeChains.Foundations.Bipointed
import CubeChains.Foundations.Representable
import CubeChains.Foundations.GluePushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.PNat.Basic

/-!
# Foundations/Wedge

The standard cube and wedges as `BPSet`s: `cube n` (the representable `よ[n]`,
bi-pointed at its extreme vertices), `vertexMap`/`initVertex`/`finalVertex`,
`wedge2 X Y` (the wedge `X ∨ Y` as a genuine pushout) and the `foldr` `serialWedge`.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube

namespace BPSet
open BPSet

/-- The standard cube `□ⁿ` as a bi-pointed precubical set: the representable
presheaf `よ[n]`, bi-pointed at the constant-`0`/`1` vertices.  The vertices use
the canonical maps `□⁰ ⟶ □ⁿ` (see `canonicalMap`). -/
def cube (n : ℕ) : BPSet where
  toPsh := yoneda.obj ▫n
  init := canonicalMap (constVertex n false)
  final := canonicalMap (constVertex n true)

/-- `□⁰` has only the identity endomorphism (it is the representable point). -/
instance stdPre0_subsingleton : Subsingleton (stdPre 0 ⟶ stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [noneSet])

instance : Subsingleton ((cube 0).cells 0) := stdPre0_subsingleton

/-- The map `□⁰ ⟶ X` selecting a vertex `v` of `X` (Yoneda).  Just `cubeMap` at
dimension `0`. -/
def vertexMap (X : PrecubicalSet) (v : X.cells 0) :
    yoneda.obj ▫0 ⟶ X :=
  X.cubeMap v

/-- The Yoneda inclusion `□⁰ ⟶ X` selecting `X`'s initial vertex. -/
def initVertex (X : BPSet) : yoneda.obj ▫0 ⟶ X.toPsh :=
  vertexMap X.toPsh X.init

/-- The Yoneda inclusion `□⁰ ⟶ X` selecting `X`'s final vertex. -/
def finalVertex (X : BPSet) : yoneda.obj ▫0 ⟶ X.toPsh :=
  vertexMap X.toPsh X.final

/-- The binary wedge `X ∨ Y`: glue `X.final` to `Y.init`, as the pushout of the
point `□⁰` in the topos `PrecubicalSet` (`X.finalVertex` against `Y.initVertex`).
Uses the *computable* `Glue.gluePsh` (a pointwise `Quot`) rather than the
`Classical.choice`-opaque `pushout`; `Glue.isPushout` recovers the universal property. -/
def wedge2 (X Y : BPSet) : BPSet where
  toPsh := Glue.gluePsh X.finalVertex Y.initVertex
  init := (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.init
  final := (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.final

/-- The serial wedge `□^∨(n₁,…,n_l)`: the end-to-end gluing of the standard cubes
`□^{nᵢ}` (the empty list gives the point `□⁰`). -/
def serialWedge : List ℕ+ → BPSet
  | [] => cube 0
  | n :: rest => wedge2 (cube (n : ℕ)) (serialWedge rest)

@[simp] theorem serialWedge_nil : serialWedge [] = cube 0 := rfl

theorem serialWedge_cons (n : ℕ+) (rest : List ℕ+) :
    serialWedge (n :: rest) = wedge2 (cube (n : ℕ)) (serialWedge rest) := rfl

def dimSum (a : List ℕ+) : ℕ := (a.map (fun d : ℕ+ => (d : ℕ))).sum

@[simp] theorem dimSum_sum (a : List ℕ+) : dimSum a = (a.map (fun d : ℕ+ => (d : ℕ))).sum := rfl

lemma dimSum0_nil (a : List ℕ+) : dimSum a = 0 → a = [] := by
  cases a <;> simp [dimSum]

/-! ### Notation

`□n` for the standard cube, `X ∨ Y` for the binary wedge, and `⋁d` for the serial wedge — all
print, so goals read as the maths does.  `□`/`⋁` bind at `max` (write `□(n+1)`, `⋁(a ++ b)`); `∨`
is `infixr:30`, overloading `Or` (disambiguated by type: `BPSet` vs `Prop`). -/

@[inherit_doc cube] notation:max "□" n:max => BPSet.cube n
@[inherit_doc wedge2] infixr:30 " ∨ " => BPSet.wedge2
@[inherit_doc serialWedge] notation:max "⋁" d:max => BPSet.serialWedge d

def serialWedge.ι : (dims : List ℕ+) → (i : Fin dims.length) →
    ((□(dims.get i)).toPsh ⟶ (⋁dims).toPsh)
  | [], i => i.elim0
  | _ :: rest, i =>
        Fin.cases (Glue.inl _ _) (fun j => serialWedge.ι rest j ≫ Glue.inr _ _) i

/-- `ιᵂ dims i` — the inclusion of bead `i` into the serial wedge, `□(dims.get i) ⟶ ⋁dims`. -/
notation:max "ιᵂ" => BPSet.serialWedge.ι

end BPSet
