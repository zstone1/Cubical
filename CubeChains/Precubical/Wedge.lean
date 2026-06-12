import CubeChains.Precubical.StandardCube
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.PNat.Basic

/-!
# Serial wedges of standard cubes (ClaudeSetup.md §3, second half)

The serial wedge `□^∨(n₁,…,n_l)` is the end-to-end gluing of standard cubes,
identifying the final vertex of each block with the initial vertex of the next.
Following the project plan, we realize the gluing as a **pushout of a point**:
`X ∨ Y := pushout (pt ⟶ X at X.final) (pt ⟶ Y at Y.init)`, and the serial wedge
as a `foldr` of `∨` over the cubes.

Precubical sets form a presheaf topos and are therefore cocomplete, but mathlib
has no box category, so `HasColimits` is not available off the shelf.  We assume
the single placeholder instance `HasPushouts PrecubicalSet` (see `DESIGN.md`
§3b); it is the only `sorry` outside `Conjectures.lean`, an instance of a true
theorem to be discharged by representing `PrecubicalSet` as a functor category.
-/

open CategoryTheory CategoryTheory.Limits

namespace Precubical

/-- The single-vertex precubical set (terminal in dimension `0`, empty above):
the gluing object for wedges. -/
def pt : PrecubicalSet where
  cells
    | 0 => PUnit
    | _ + 1 => PEmpty
  face := fun {_} _ _ c => c.elim
  face_face := by intro n ε η i j h c; exact c.elim

/-- The precubical map `pt ⟶ X` selecting a `0`-cell `v` of `X`. -/
def vertexHom (X : PrecubicalSet) (v : X.cells 0) : pt ⟶ X where
  app
    | 0 => fun _ => v
    | _ + 1 => fun c => c.elim
  app_face := fun {_} _ _ c => c.elim

/-- Precubical sets form a presheaf topos, hence are cocomplete.  Pending the
functor-category representation, we assume this single instance (see DESIGN.md
§3b).  This is the only `sorry` outside `Conjectures.lean`. -/
instance : HasPushouts PrecubicalSet := sorry

end Precubical

namespace BPSet

open Precubical

/-- The single-vertex bi-pointed precubical set (`init = final`). -/
def pt : BPSet where
  toPrecubicalSet := Precubical.pt
  init := PUnit.unit
  final := PUnit.unit

/-- The binary wedge `X ∨ Y`: glue `X.final` to `Y.init`.  Realized as the
pushout of the point along the two chosen vertices. -/
noncomputable def wedge2 (X Y : BPSet) : BPSet where
  toPrecubicalSet :=
    pushout (vertexHom X.toPrecubicalSet X.final) (vertexHom Y.toPrecubicalSet Y.init)
  init := PrecubicalSet.Hom.app
    (pushout.inl (vertexHom X.toPrecubicalSet X.final) (vertexHom Y.toPrecubicalSet Y.init)) 0
    X.init
  final := PrecubicalSet.Hom.app
    (pushout.inr (vertexHom X.toPrecubicalSet X.final) (vertexHom Y.toPrecubicalSet Y.init)) 0
    Y.final

/-- The serial wedge `□^∨(n₁,…,n_l)` of a list of positive dimensions: the
end-to-end gluing of the standard cubes `□^{nᵢ}`. -/
noncomputable def serialWedge : List ℕ+ → BPSet
  | [] => BPSet.pt
  | n :: rest => wedge2 (StdCube.stdCube (n : ℕ)) (serialWedge rest)

@[simp] theorem serialWedge_nil : serialWedge [] = BPSet.pt := rfl

theorem serialWedge_cons (n : ℕ+) (rest : List ℕ+) :
    serialWedge (n :: rest) = wedge2 (StdCube.stdCube (n : ℕ)) (serialWedge rest) := rfl

end BPSet
