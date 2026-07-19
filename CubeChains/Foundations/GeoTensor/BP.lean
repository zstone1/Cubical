import CubeChains.Foundations.GeoTensor.Monoidal
import CubeChains.Foundations.GeoTensor.Cube
import CubeChains.Foundations.Wedge

/-!
# Foundations/GeoTensor/BP — the geometric monoidal structure on `BPSet`

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
    appendCell (constVertex m ε) (constVertex n ε) = constVertex (m + n) ε := by
  apply Subtype.ext
  funext j
  rw [appendCell_val]
  cases j using Fin.addCases with
  | left i => rw [Fin.append_left]; rfl
  | right i => rw [Fin.append_right]; rfl

end StdCube

namespace Box

/-- The sign vector of a canonical map is the classifying cell. -/
theorem sign_canonicalMap {X Y : Box} (c : Cell Y.dim X.dim) :
    sign (canonicalMap (K := stdPre Y.dim) (n := X.dim) c : X ⟶ Y) = c :=
  ev_canonicalMap (K := stdPre Y.dim) (n := X.dim) c

end Box

namespace GeoTensor

/-- Applying `Φ.inv` after `Φ.hom` is the identity, pointwise. -/
theorem psh_inv_hom {K L : PrecubicalSet} (Φ : K ≅ L) {n : ℕ} (c : K.cells n) :
    Φ.inv⟪n⟫ (Φ.hom⟪n⟫ c) = c := by
  rw [← CategoryTheory.comp_apply, ← NatTrans.comp_app, Φ.hom_inv_id, NatTrans.id_app,
    CategoryTheory.id_apply]

/-- Promote an iso of underlying presheaves preserving `init`/`final` to a `BPSet` iso. -/
def isoOfPshIso {K L : BPSet} (Φ : K.toPsh ≅ L.toPsh)
    (hinit : Φ.hom⟪0⟫ K.init = L.init) (hfinal : Φ.hom⟪0⟫ K.final = L.final) : K ≅ L where
  hom := ⟨Φ.hom, hinit, hfinal⟩
  inv := ⟨Φ.inv, by rw [← hinit, psh_inv_hom], by rw [← hfinal, psh_inv_hom]⟩
  hom_inv_id := BPSet.hom_ext Φ.hom_inv_id
  inv_hom_id := BPSet.hom_ext Φ.inv_hom_id

/-- The geometric product of bi-pointed precubical sets. -/
def tensorObjBP (K L : BPSet) : BPSet where
  toPsh := tensorObj K.toPsh L.toPsh
  init := pair K.toPsh L.toPsh K.init L.init
  final := pair K.toPsh L.toPsh K.final L.final

/-- `f ⊗ g` preserves the initial product cell. -/
theorem tensorHom_initBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    (tensorHom (f : BPSet.Hom K M).hom (g : BPSet.Hom L N).hom)⟪0⟫
        (pair K.toPsh L.toPsh K.init L.init) = pair M.toPsh N.toPsh M.init N.init := by
  change pair M.toPsh N.toPsh ((f : BPSet.Hom K M).hom.app (op ▫0) K.init)
      ((g : BPSet.Hom L N).hom.app (op ▫0) L.init) = _
  rw [(f : BPSet.Hom K M).app_init, (g : BPSet.Hom L N).app_init]

/-- `f ⊗ g` preserves the final product cell. -/
theorem tensorHom_finalBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    (tensorHom (f : BPSet.Hom K M).hom (g : BPSet.Hom L N).hom)⟪0⟫
        (pair K.toPsh L.toPsh K.final L.final) = pair M.toPsh N.toPsh M.final N.final := by
  change pair M.toPsh N.toPsh ((f : BPSet.Hom K M).hom.app (op ▫0) K.final)
      ((g : BPSet.Hom L N).hom.app (op ▫0) L.final) = _
  rw [(f : BPSet.Hom K M).app_final, (g : BPSet.Hom L N).app_final]

/-- The geometric product of bi-pointed maps. -/
def tensorHomBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    tensorObjBP K L ⟶ tensorObjBP M N where
  hom := tensorHom (f : BPSet.Hom K M).hom (g : BPSet.Hom L N).hom
  app_init := tensorHom_initBP f g
  app_final := tensorHom_finalBP f g

/-- The tensor unit: the standard `0`-cube (`toPsh = yoneda.obj ▫0 = tensorUnit`). -/
def tensorUnitBP : BPSet := BPSet.cube 0

/-! ### The structural isomorphisms at the `BPSet` level -/

theorem assoc_init (K L M : BPSet) :
    (associator K.toPsh L.toPsh M.toPsh).hom⟪0⟫ (tensorObjBP (tensorObjBP K L) M).init
      = (tensorObjBP K (tensorObjBP L M)).init := rfl

theorem assoc_final (K L M : BPSet) :
    (associator K.toPsh L.toPsh M.toPsh).hom⟪0⟫ (tensorObjBP (tensorObjBP K L) M).final
      = (tensorObjBP K (tensorObjBP L M)).final := rfl

/-- The `BPSet`-level associator. -/
def associatorBP (K L M : BPSet) :
    tensorObjBP (tensorObjBP K L) M ≅ tensorObjBP K (tensorObjBP L M) :=
  isoOfPshIso (associator K.toPsh L.toPsh M.toPsh) (assoc_init K L M) (assoc_final K L M)

theorem leftUnitor_initBP (K : BPSet) :
    (leftUnitor K.toPsh).hom⟪0⟫ (tensorObjBP tensorUnitBP K).init = K.init :=
  eq_of_heq (map_eqToHom_heq _ K.init)

theorem leftUnitor_finalBP (K : BPSet) :
    (leftUnitor K.toPsh).hom⟪0⟫ (tensorObjBP tensorUnitBP K).final = K.final :=
  eq_of_heq (map_eqToHom_heq _ K.final)

/-- The `BPSet`-level left unitor. -/
def leftUnitorBP (K : BPSet) : tensorObjBP tensorUnitBP K ≅ K :=
  isoOfPshIso (leftUnitor K.toPsh) (leftUnitor_initBP K) (leftUnitor_finalBP K)

theorem rightUnitor_initBP (K : BPSet) :
    (rightUnitor K.toPsh).hom⟪0⟫ (tensorObjBP K tensorUnitBP).init = K.init :=
  eq_of_heq (map_eqToHom_heq _ K.init)

theorem rightUnitor_finalBP (K : BPSet) :
    (rightUnitor K.toPsh).hom⟪0⟫ (tensorObjBP K tensorUnitBP).final = K.final :=
  eq_of_heq (map_eqToHom_heq _ K.final)

/-- The `BPSet`-level right unitor. -/
def rightUnitorBP (K : BPSet) : tensorObjBP K tensorUnitBP ≅ K :=
  isoOfPshIso (rightUnitor K.toPsh) (rightUnitor_initBP K) (rightUnitor_finalBP K)

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

theorem cube_init_sign (n : ℕ) :
    Box.sign ((BPSet.cube n).init : (▫0 : Box) ⟶ ▫n) = constVertex n false :=
  Box.sign_canonicalMap (X := ▫0) (Y := ▫n) (constVertex n false)

theorem cube_final_sign (n : ℕ) :
    Box.sign ((BPSet.cube n).final : (▫0 : Box) ⟶ ▫n) = constVertex n true :=
  Box.sign_canonicalMap (X := ▫0) (Y := ▫n) (constVertex n true)

/-- The tensor of the initial vertices of `□m`, `□n` is the initial vertex of `□(m+n)`. -/
theorem cube_init_tensor (m n : ℕ) :
    (cubeTensorIso m n).hom⟪0⟫ (tensorObjBP (BPSet.cube m) (BPSet.cube n)).init
      = (BPSet.cube (m + n)).init := by
  apply Box.hom_ext
  rw [cube_init_sign (m + n)]
  change Box.sign (tensorCubeFun m n ▫0 (pair (yoneda.obj ▫m) (yoneda.obj ▫n)
      (BPSet.cube m).init (BPSet.cube n).init)) = constVertex (m + n) false
  unfold tensorCubeFun
  rw [Box.sign_ofSign]
  apply Subtype.ext
  rw [castCellDim_val]
  change (appendCell (Box.sign ((BPSet.cube m).init : (▫0 : Box) ⟶ ▫m))
      (Box.sign ((BPSet.cube n).init : (▫0 : Box) ⟶ ▫n))).val = (constVertex (m + n) false).val
  rw [cube_init_sign m, cube_init_sign n, appendCell_constVertex]

theorem cube_final_tensor (m n : ℕ) :
    (cubeTensorIso m n).hom⟪0⟫ (tensorObjBP (BPSet.cube m) (BPSet.cube n)).final
      = (BPSet.cube (m + n)).final := by
  apply Box.hom_ext
  rw [cube_final_sign (m + n)]
  change Box.sign (tensorCubeFun m n ▫0 (pair (yoneda.obj ▫m) (yoneda.obj ▫n)
      (BPSet.cube m).final (BPSet.cube n).final)) = constVertex (m + n) true
  unfold tensorCubeFun
  rw [Box.sign_ofSign]
  apply Subtype.ext
  rw [castCellDim_val]
  change (appendCell (Box.sign ((BPSet.cube m).final : (▫0 : Box) ⟶ ▫m))
      (Box.sign ((BPSet.cube n).final : (▫0 : Box) ⟶ ▫n))).val = (constVertex (m + n) true).val
  rw [cube_final_sign m, cube_final_sign n, appendCell_constVertex]

/-- **`□m ⊗ᵍ □n ≅ □(m+n)`** for the geometric product of standard cubes. -/
def cubeTensorIsoBP (m n : ℕ) :
    tensorObjBP (BPSet.cube m) (BPSet.cube n) ≅ BPSet.cube (m + n) :=
  isoOfPshIso (cubeTensorIso m n) (cube_init_tensor m n) (cube_final_tensor m n)

end GeoTensor

/-- `K ⊗ᵍ L` — the geometric (parallel) tensor of bi-pointed precubical sets, distinct from the
wedge `∨` (the default `⊗` on `BPSet`).  Lives on the alias `GeoBP` as a `MonoidalCategory`. -/
infixr:70 " ⊗ᵍ " => GeoTensor.tensorObjBP

/-- `BPSet` carrying the geometric tensor `⊗ᵍ` as its monoidal product. -/
def GeoBP := BPSet

instance : Category GeoBP := inferInstanceAs (Category BPSet)

instance : MonoidalCategory GeoBP := GeoTensor.geoMonoidalBP
