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

/-- **A serial wedge's coend is its beads' coordinate sets, indexed by bead**
`Coord↓ (⋁a) ≃ Σ i : Fin a.length, Fin (a.get i)` — a coordinate's bead is the first component. -/
def coordWedge (a : List ℕ+) :
    (cotensorLift Coord).obj (⋁a) ≃ Σ i : Fin a.length, Fin ((a.get i : ℕ)) :=
  cotensorSigmaEquiv Coord inferInstance a

/-- The coordinate `k` of `□m`, as a coend class. -/
theorem coordCube_symm_apply (m : ℕ) (k : Fin m) :
    (coordCube m).symm k = Cotensor.mk Coord m (𝟙 ▫m) k := rfl

/-- **Reading a decorated cube cell**: the coend collapses to the free-coordinate embedding of the
cell.  `coordCube` sends `⟨x, k⟩` to the coordinate `x` sends `k`. -/
theorem coordCube_mk {b m : ℕ} (x : (□b).cells m) (k : Fin m) :
    coordCube b (Cotensor.mk Coord m x k) = faceEmb x k := rfl

/-- **A bead coordinate assembles from its bead inclusion.**  `coordWedge` reads bead `i`'s
inclusion, decorated by the `k`-th coordinate of `□(aᵢ)`, back to `⟨i, k⟩`. -/
theorem coordWedge_apply_map (a : List ℕ+) (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    coordWedge a (Cotensor.map Coord (ιᵂ a i) ((coordCube (a.get i : ℕ)).symm k)) = ⟨i, k⟩ :=
  cotensorSigmaEquiv_apply_map Coord inferInstance a i k

/-- **A bead coordinate is its bead inclusion decorated by the coordinate.**  `coordWedge.symm`
sends `⟨i, k⟩` to bead `i`'s inclusion pushed onto the `k`-th coordinate of `□(aᵢ)`. -/
theorem coordWedge_symm_apply (a : List ℕ+) (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    (coordWedge a).symm ⟨i, k⟩
      = Cotensor.map Coord (ιᵂ a i) ((coordCube (a.get i : ℕ)).symm k) :=
  cotensorSigmaEquiv_symm_apply Coord inferInstance a i k

/-- **Pushing a cube coordinate along a cube map** reads off `faceEmb` of the Yoneda cell. -/
theorem coordCube_map_symm {m b : ℕ} (g : (□m).toPsh ⟶ (□b).toPsh) (k : Fin m) :
    coordCube b (Cotensor.map Coord g ((coordCube m).symm k)) = faceEmb (yonedaEquiv g) k := rfl

end CubeChains
