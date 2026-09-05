import CubeChains.Precubical.Wedge.GeoTensor.Monoidal
import CubeChains.Precubical.Wedge.GeoTensor.Cube
import CubeChains.Precubical.Wedge.Wedge

/-!
# Precubical/Wedge/GeoTensor/BP — the geometric monoidal structure on `BPSet`

Lifts the computable geometric tensor on `PrecubicalSet` (`GeoTensor.*`) to **bi-pointed**
precubical sets, written `K ⊗ᵍ L` (notation for `GeoTensor.tensorObjBP`, distinct from the wedge
`∨`), bi-pointed at the product cells

    init (K ⊗ᵍ L) = init K ⊗ init L,      final (K ⊗ᵍ L) = final K ⊗ final L.

A `BPSet` morphism is determined by its underlying presheaf map (`BPSet.hom_ext`), so every
monoidal axiom reduces to the corresponding one on `PrecubicalSet`.  `cubeTensorIsoBP : □m ⊗ᵍ □n ≅
□(m+n)`.  The tensor unit is `□0` on the nose (`tensorUnit = yoneda.obj ▫0`).
-/

open CategoryTheory Opposite StdCube

namespace StdCube

/-- Concatenating two constant vertices is the constant vertex of the summed dimension. -/
theorem appendCell_constVertex (m n : ℕ) (ε : Bool) :
    appendCell (constVertex m ε) (constVertex n ε) = constVertex (m + n) ε :=
  appendCell_const rfl rfl rfl

end StdCube

namespace Box

/-- The sign vector of a canonical map is the classifying cell. -/
theorem sign_canonicalMap {X Y : Box} (c : Cell Y.dim X.dim) :
    sign (canonicalMap (K := stdPre Y.dim) (n := X.dim) c : X ⟶ Y) = c :=
  ev_canonicalMap (K := stdPre Y.dim) (n := X.dim) c

end Box

namespace GeoTensor

open BPSet (isoOfPshIso)

/-- The geometric product of bi-pointed precubical sets. -/
def tensorObjBP (K L : BPSet) : BPSet where
  toPsh := tensorObj K.toPsh L.toPsh
  init := pair K.toPsh L.toPsh K.init L.init
  final := pair K.toPsh L.toPsh K.final L.final

/-- The endpoints of `K ⊗ᵍ L` are the paired endpoints of the factors. -/
theorem tensorObjBP_vtx (K L : BPSet) (ε : Bool) :
    (tensorObjBP K L).vtx ε = pair K.toPsh L.toPsh (K.vtx ε) (L.vtx ε) := by
  cases ε <;> rfl

/-- `f ⊗ g` preserves the paired `ε`-endpoint. -/
theorem tensorHom_vtxBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) (ε : Bool) :
    (tensorHom (f : BPSet.Hom K M).hom (g : BPSet.Hom L N).hom)⟪0⟫
        (pair K.toPsh L.toPsh (K.vtx ε) (L.vtx ε))
      = pair M.toPsh N.toPsh (M.vtx ε) (N.vtx ε) := by
  change pair M.toPsh N.toPsh ((f : BPSet.Hom K M).hom.app (op ▫0) (K.vtx ε))
      ((g : BPSet.Hom L N).hom.app (op ▫0) (L.vtx ε)) = _
  rw [(f : BPSet.Hom K M).app_vtx, (g : BPSet.Hom L N).app_vtx]

/-- The geometric product of bi-pointed maps. -/
def tensorHomBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    tensorObjBP K L ⟶ tensorObjBP M N where
  hom := tensorHom (f : BPSet.Hom K M).hom (g : BPSet.Hom L N).hom
  app_init := tensorHom_vtxBP f g false
  app_final := tensorHom_vtxBP f g true

/-- The tensor unit: the standard `0`-cube (`toPsh = yoneda.obj ▫0 = tensorUnit`). -/
def tensorUnitBP : BPSet := BPSet.cube 0

/-! ### The structural isomorphisms at the `BPSet` level -/

theorem assoc_vtx (K L M : BPSet) (ε : Bool) :
    (associator K.toPsh L.toPsh M.toPsh).hom⟪0⟫ ((tensorObjBP (tensorObjBP K L) M).vtx ε)
      = (tensorObjBP K (tensorObjBP L M)).vtx ε := by
  cases ε <;> rfl

/-- The `BPSet`-level associator. -/
def associatorBP (K L M : BPSet) :
    tensorObjBP (tensorObjBP K L) M ≅ tensorObjBP K (tensorObjBP L M) :=
  isoOfPshIso (associator K.toPsh L.toPsh M.toPsh) (assoc_vtx K L M false) (assoc_vtx K L M true)

theorem leftUnitor_vtxBP (K : BPSet) (ε : Bool) :
    (leftUnitor K.toPsh).hom⟪0⟫ ((tensorObjBP tensorUnitBP K).vtx ε) = K.vtx ε := by
  cases ε <;> exact eq_of_heq (map_eqToHom_heq _ _)

/-- The `BPSet`-level left unitor. -/
def leftUnitorBP (K : BPSet) : tensorObjBP tensorUnitBP K ≅ K :=
  isoOfPshIso (leftUnitor K.toPsh) (leftUnitor_vtxBP K false) (leftUnitor_vtxBP K true)

theorem rightUnitor_vtxBP (K : BPSet) (ε : Bool) :
    (rightUnitor K.toPsh).hom⟪0⟫ ((tensorObjBP K tensorUnitBP).vtx ε) = K.vtx ε := by
  cases ε <;> exact eq_of_heq (map_eqToHom_heq _ _)

/-- The `BPSet`-level right unitor. -/
def rightUnitorBP (K : BPSet) : tensorObjBP K tensorUnitBP ≅ K :=
  isoOfPshIso (rightUnitor K.toPsh) (rightUnitor_vtxBP K false) (rightUnitor_vtxBP K true)

/-- The geometric monoidal data on `BPSet` (plain `def`; `BPSet` carries no canonical product —
see `GeoBP`). -/
@[reducible] def geoStructBP : MonoidalCategoryStruct BPSet where
  tensorObj := tensorObjBP
  tensorHom := tensorHomBP
  whiskerLeft K _ _ f := tensorHomBP (𝟙 K) f
  whiskerRight f M := tensorHomBP f (𝟙 M)
  tensorUnit := tensorUnitBP
  associator := associatorBP
  leftUnitor := leftUnitorBP
  rightUnitor := rightUnitorBP

/-- The geometric `MonoidalCategory` data on `BPSet` (plain `def`; see `GeoBP`). -/
@[reducible] def geoMonoidalBP : MonoidalCategory BPSet :=
  letI := geoStructBP
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun K L => BPSet.hom_ext (tensorHom_id K.toPsh L.toPsh))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => BPSet.hom_ext
      (tensorHom_comp_tensorHom (f₁ : BPSet.Hom _ _).hom (g₁ : BPSet.Hom _ _).hom
        (f₂ : BPSet.Hom _ _).hom (g₂ : BPSet.Hom _ _).hom).symm)
    (associator_naturality := fun f₁ f₂ f₃ => BPSet.hom_ext
      (associator_naturality (f₁ : BPSet.Hom _ _).hom (f₂ : BPSet.Hom _ _).hom
        (f₃ : BPSet.Hom _ _).hom))
    (leftUnitor_naturality := fun f => BPSet.hom_ext
      (leftUnitor_naturality (f : BPSet.Hom _ _).hom))
    (rightUnitor_naturality := fun f => BPSet.hom_ext
      (rightUnitor_naturality (f : BPSet.Hom _ _).hom))
    (pentagon := fun W X Y Z => BPSet.hom_ext (pentagon W.toPsh X.toPsh Y.toPsh Z.toPsh))
    (triangle := fun X Y => BPSet.hom_ext (geoTriangle X.toPsh Y.toPsh))

/-! ### The cube tensor iso -/

theorem cube_sign (n : ℕ) (ε : Bool) :
    Box.sign ((BPSet.cube n).vtx ε : (▫0 : Box) ⟶ ▫n) = constVertex n ε := by
  cases ε <;> exact Box.sign_canonicalMap (X := ▫0) (Y := ▫n) _

/-- The tensor of the `ε`-vertices of `□m`, `□n` is the `ε`-vertex of `□(m+n)`. -/
theorem cube_vtx_tensor (m n : ℕ) (ε : Bool) :
    (cubeTensorIso m n).hom⟪0⟫ ((tensorObjBP (BPSet.cube m) (BPSet.cube n)).vtx ε)
      = (BPSet.cube (m + n)).vtx ε := by
  apply Box.hom_ext
  apply Subtype.ext
  rw [tensorObjBP_vtx, cube_sign (m + n)]
  refine (sign_tensorCubeFun (m := m) (n := n) ▫0 _).trans ?_
  change Fin.append (Box.sign ((BPSet.cube m).vtx ε : (▫0 : Box) ⟶ ▫m)).val
    (Box.sign ((BPSet.cube n).vtx ε : (▫0 : Box) ⟶ ▫n)).val = _
  rw [cube_sign m, cube_sign n]
  exact congrArg Subtype.val (appendCell_constVertex m n ε)

/-- **`□m ⊗ᵍ □n ≅ □(m+n)`** for the geometric product of standard cubes. -/
def cubeTensorIsoBP (m n : ℕ) :
    tensorObjBP (BPSet.cube m) (BPSet.cube n) ≅ BPSet.cube (m + n) :=
  isoOfPshIso (cubeTensorIso m n) (cube_vtx_tensor m n false) (cube_vtx_tensor m n true)

end GeoTensor

/-- `K ⊗ᵍ L` — the geometric (parallel) tensor of bi-pointed precubical sets, distinct from the
wedge `∨` (the default `⊗` on `BPSet`).  Lives on the alias `GeoBP` as a `MonoidalCategory`. -/
infixr:70 " ⊗ᵍ " => GeoTensor.tensorObjBP

/-- `BPSet` carrying the geometric tensor `⊗ᵍ` as its monoidal product. -/
def GeoBP := BPSet

instance : Category GeoBP := inferInstanceAs (Category BPSet)

instance : MonoidalCategory GeoBP := GeoTensor.geoMonoidalBP
