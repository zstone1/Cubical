import CubeChains.Bipointed
import CubeChains.Representable
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.PNat.Basic

/-!
# The standard cube and serial wedges (over the topos `PrecubicalSet`)

Working in `PrecubicalSet = Boxᵒᵖ ⥤ Type`, the standard cube `□ⁿ` is the
*representable* presheaf `よ[n] = yoneda.obj [n]`, bi-pointed at its two extreme
vertices.  The wedge `X ∨ Y` is the genuine **pushout** of a point in the topos
— and since a functor category into `Type` is cocomplete, this needs **no
`sorry`** (it is the payoff of the topos definition).  The serial wedge is the
`foldr` of `∨` over the standard cubes.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace BPSet

/-- The standard cube `□ⁿ` as a bi-pointed precubical set: the representable
presheaf `よ[n]`, bi-pointed at the constant-`0`/`1` vertices.  The vertices use
the canonical maps `□⁰ ⟶ □ⁿ` (see `StdCube.canonicalMap`). -/
noncomputable def cube (n : ℕ) : BPSet where
  toPsh := yoneda.obj (Box.ob n)
  init := StdCube.canonicalMap (StdCube.constVertex n false)
  final := StdCube.canonicalMap (StdCube.constVertex n true)

/-- The map `□⁰ ⟶ X` selecting a vertex `v` of `X` (Yoneda). -/
noncomputable def vertexMap (X : PrecubicalSet) (v : X.cells 0) :
    yoneda.obj (Box.ob 0) ⟶ X :=
  yonedaEquiv.symm v

/-- The binary wedge `X ∨ Y`: glue `X.final` to `Y.init`, as the pushout of the
point `□⁰` in the topos `PrecubicalSet`. -/
noncomputable def wedge2 (X Y : BPSet) : BPSet where
  toPsh := pushout (vertexMap X.toPsh X.final) (vertexMap Y.toPsh Y.init)
  init := NatTrans.app (pushout.inl (vertexMap X.toPsh X.final) (vertexMap Y.toPsh Y.init))
    (op (Box.ob 0)) X.init
  final := NatTrans.app (pushout.inr (vertexMap X.toPsh X.final) (vertexMap Y.toPsh Y.init))
    (op (Box.ob 0)) Y.final

/-- The serial wedge `□^∨(n₁,…,n_l)`: the end-to-end gluing of the standard cubes
`□^{nᵢ}` (the empty list gives the point `□⁰`). -/
noncomputable def serialWedge : List ℕ+ → BPSet
  | [] => cube 0
  | n :: rest => wedge2 (cube (n : ℕ)) (serialWedge rest)

@[simp] theorem serialWedge_nil : serialWedge [] = cube 0 := rfl

theorem serialWedge_cons (n : ℕ+) (rest : List ℕ+) :
    serialWedge (n :: rest) = wedge2 (cube (n : ℕ)) (serialWedge rest) := rfl

noncomputable def serialWedge.ι : (dims : List ℕ+) → (i : Fin dims.length) →
    ((cube (dims.get i)).toPsh ⟶ (serialWedge dims).toPsh)
  | [], i => i.elim0
  | _ :: rest, i =>
        Fin.cases (pushout.inl _ _) (fun j => serialWedge.ι rest j ≫ pushout.inr _ _) i

/-
theorem serialWedge.ι_desc … -- computation rule
theorem serialWedge.hom_ext  (∀ i, ι i ≫ f = ι i ≫ g) → f = g  -- uniqueness
-/

end BPSet
