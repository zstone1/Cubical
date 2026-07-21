import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.WedgeExtend

/-!
# Chains/CoordFunctor — the coordinate copresheaf `▫n ↦ Fin n`

A cube face `g : ▫n ⟶ ▫m` acts on coordinates by its free-coordinate embedding `faceEmb g :
Fin n ↪ Fin m`.  It is **empty at `▫0`**, so its cubical coend `cotensorLift Coord`
(`Chains/WedgeExtend`) sends a serial wedge to the *coproduct* of its beads' coordinate sets — the
ordered partition of the coordinates a cube chain realises (`coordWedge`), and a cube to its own
coordinate set (`coordCube`).
-/

open CategoryTheory CubeChain ChainCat

namespace CubeChains

/-- The **coordinate copresheaf** `▫n ↦ Fin n`, a cube face acting by `faceEmb`. -/
def Coord : Box ⥤ Type where
  obj b := Fin b.dim
  map g := ↾fun i => faceEmb g i
  map_id b := by
    apply ConcreteCategory.hom_ext
    intro i
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact faceEmb_id b.dim i
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro i
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact faceEmb_comp g h i

@[simp] theorem Coord_obj (b : Box) : Coord.obj b = Fin b.dim := rfl

@[simp] theorem Coord_map_apply {b b' : Box} (g : b ⟶ b') (i : Fin b.dim) :
    Coord.map g i = faceEmb g i :=
  rfl

/-- `Coord` is **empty at the point** `▫0` — what turns its coend into a coproduct. -/
instance : IsEmpty (Coord.obj ▫0) := inferInstanceAs (IsEmpty (Fin 0))

/-! ## The coend of `Coord` -/

/-- **A cube's coend is its coordinate set** `Coord↓ □m ≃ Fin m` — co-Yoneda. -/
def coordCube (m : ℕ) : (cotensorLift Coord).obj (□m) ≃ Fin m :=
  Cotensor.cubeEquiv Coord m

/-- **A serial wedge's coend is the coproduct of its beads' coordinate sets**
`Coord↓ (⋁a) ≃ ⊕ᵢ Fin aᵢ` — the ordered coordinate partition. -/
def coordWedge (a : List ℕ+) :
    (cotensorLift Coord).obj (⋁a) ≃ wedgeCoprodType Coord a :=
  wedgeCoprodEquiv Coord inferInstance a

end CubeChains
