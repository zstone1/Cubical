import CubeChains.Foundations.DayTensor
import CubeChains.Foundations.Wedge

/-!
# Foundations/BPTensor

The geometric product on **bi-pointed** precubical sets: `K ⊗ L` is the Day convolution of the
underlying presheaves (`Foundations/DayTensor`), bi-pointed at the product cells

    init (K ⊗ L) = init K ⊗ init L,      final (K ⊗ L) = final K ⊗ final L

(`dayCell` = the Day unit `η`, here in degree `0`).  Coherence is inherited: a `BPSet` morphism
is determined by its underlying presheaf map (`BPSet.hom_ext`), so every monoidal axiom reduces
to the corresponding one in `Boxᵒᵖ ⊛⥤ Type`.  The content is that the structure maps preserve
`init`/`final` — that is what the `LawfulDayConvolutionMonoidalCategoryStruct` unit lemmas give,
together with the fact that every `Box` map with `0`-dimensional target is unique
(`Box.hom_ext_target_zero`), which collapses the `Box`-side coherence maps in degree `0`.

`cubeTensorIso : □m ⊗ □n ≅ □(m+n)`.

The tensor unit is the Day unit bi-pointed at its canonical vertex, not `□0` on the nose
(mathlib's Day machinery chooses the unit).
-/

open CategoryTheory Opposite MonoidalCategory Limits StdCube
open scoped MonoidalCategory.DayFunctor MonoidalCategory.ExternalProduct

/-! ### Two small additions to the sign-vector / `Box` layer -/

namespace StdCube

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

/-- Any two `Box` maps into a `0`-dimensional box agree: their sign vectors live on `Fin 0`. -/
theorem hom_ext_target_zero {X Y : Box} (hY : Y.dim = 0) (f g : X ⟶ Y) : f = g :=
  hom_ext (Subtype.ext (funext fun j => (Fin.cast hY j).elim0))

theorem op_hom_ext_zero {X Y : Boxᵒᵖ} (hX : X.unop.dim = 0) (f g : X ⟶ Y) : f = g :=
  Quiver.Hom.unop_inj (hom_ext_target_zero hX f.unop g.unop)

theorem sign_canonicalMap {X Y : Box} (c : Cell Y.dim X.dim) :
    sign (canonicalMap (K := stdPre Y.dim) (n := X.dim) c : X ⟶ Y) = c :=
  ev_canonicalMap (K := stdPre Y.dim) (n := X.dim) c

end Box

/-! ### Product cells of a Day convolution -/

namespace DayCube

open LawfulDayConvolutionMonoidalCategoryStruct in
@[simp] theorem lawful_ι_obj (F : Boxᵒᵖ ⊛⥤ Type) :
    (ι Boxᵒᵖ Type (Boxᵒᵖ ⊛⥤ Type)).obj F = F.functor := rfl

open LawfulDayConvolutionMonoidalCategoryStruct in
@[simp] theorem lawful_ι_map {F G : Boxᵒᵖ ⊛⥤ Type} (f : F ⟶ G) :
    (ι Boxᵒᵖ Type (Boxᵒᵖ ⊛⥤ Type)).map f = f.natTrans := rfl

open LawfulDayConvolutionMonoidalCategoryStruct in
@[simp] theorem lawful_convolutionExtensionUnit (F G : Boxᵒᵖ ⊛⥤ Type) :
    convolutionExtensionUnit Boxᵒᵖ Type F G = DayFunctor.η F G := rfl

open LawfulDayConvolutionMonoidalCategoryStruct in
@[simp] theorem lawful_unitUnit :
    unitUnit Boxᵒᵖ Type (Boxᵒᵖ ⊛⥤ Type) = DayFunctor.ν Boxᵒᵖ Type := rfl

/-- The product cell: the Day unit sends a `p`-cell of `F` and a `q`-cell of `G` to a
`(p+q)`-cell of `F ⊗ G`. -/
noncomputable def dayCell (F G : Boxᵒᵖ ⊛⥤ Type) {p q : ℕ} (x : F.functor.obj (op ▫p))
    (y : G.functor.obj (op ▫q)) : (F ⊗ G).functor.obj (op ▫(p + q)) :=
  (DayFunctor.η F G).app (op ▫p, op ▫q) (x, y)

/-- `f ⊗ₘ g` carries product cells to product cells. -/
theorem tensorHom_dayCell {F G F' G' : Boxᵒᵖ ⊛⥤ Type} (f : F ⟶ F') (g : G ⟶ G')
    {p q : ℕ} (x : F.functor.obj (op ▫p)) (y : G.functor.obj (op ▫q)) :
    (f ⊗ₘ g).natTrans.app (op ▫(p + q)) (dayCell F G x y)
      = dayCell F' G' (f.natTrans.app (op ▫p) x) (g.natTrans.app (op ▫q) y) := by
  have h :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_tensorHom_app
      (C := Boxᵒᵖ) (V := Type) (D := Boxᵒᵖ ⊛⥤ Type) f g (op ▫p) (op ▫q)
  have h2 := ConcreteCategory.congr_hom h
    ((x, y) : F.functor.obj (op ▫p) × G.functor.obj (op ▫q))
  simp only [types_comp_apply, lawful_ι_map, lawful_convolutionExtensionUnit] at h2
  exact h2

/-- The Day associator carries iterated product cells to iterated product cells (degree `0`). -/
theorem associator_dayCell (F G H : Boxᵒᵖ ⊛⥤ Type) (x : F.functor.obj (op ▫0))
    (y : G.functor.obj (op ▫0)) (z : H.functor.obj (op ▫0)) :
    (α_ F G H).hom.natTrans.app (op ▫0) (dayCell (F ⊗ G) H (dayCell F G x y) z)
      = dayCell F (G ⊗ H) x (dayCell G H y z) := by
  have hass : (α_ (op ▫0 : Boxᵒᵖ) (op ▫0) (op ▫0)).inv = 𝟙 _ := Box.op_hom_ext_zero rfl _ _
  have hmap : ∀ P : Boxᵒᵖ ⥤ Type,
      P.map ((α_ (op ▫0 : Boxᵒᵖ) (op ▫0) (op ▫0)).inv) = 𝟙 (P.obj (op ▫0)) := fun P => by
    rw [hass]; exact P.map_id _
  have h := LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
    (C := Boxᵒᵖ) (V := Type) (D := Boxᵒᵖ ⊛⥤ Type) F G H (op ▫0) (op ▫0) (op ▫0)
  have h2 := ConcreteCategory.congr_hom h
    (((x, y), z) : (F.functor.obj (op ▫0) × G.functor.obj (op ▫0)) × H.functor.obj (op ▫0))
  -- mathlib spells the `C`-associator with `Prod` projections, so cancel the trailing
  -- `map (α_ …).inv` by `exact` (defeq) rather than by rewriting
  exact h2.trans (ConcreteCategory.congr_hom (hmap _) _)

/-- The Day left unitor kills the unit vertex of a degree-`0` product cell. -/
theorem leftUnitor_dayCell (F : Boxᵒᵖ ⊛⥤ Type) (x : F.functor.obj (op ▫0)) :
    (λ_ F).hom.natTrans.app (op ▫0)
        (dayCell (𝟙_ (Boxᵒᵖ ⊛⥤ Type)) F (DayFunctor.ν Boxᵒᵖ Type PUnit.unit) x) = x := by
  have hlu : (λ_ (op ▫0 : Boxᵒᵖ)).inv = 𝟙 _ := Box.op_hom_ext_zero rfl _ _
  have hmap : ∀ P : Boxᵒᵖ ⥤ Type,
      P.map ((λ_ (op ▫0 : Boxᵒᵖ)).inv) = 𝟙 (P.obj (op ▫0)) := fun P => by
    rw [hlu]; exact P.map_id _
  have h := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
    (C := Boxᵒᵖ) (V := Type) (D := Boxᵒᵖ ⊛⥤ Type) F (op ▫0)
  rw [hmap] at h
  exact ConcreteCategory.congr_hom h ((PUnit.unit, x) : PUnit × F.functor.obj (op ▫0))

/-- The Day right unitor kills the unit vertex of a degree-`0` product cell. -/
theorem rightUnitor_dayCell (F : Boxᵒᵖ ⊛⥤ Type) (x : F.functor.obj (op ▫0)) :
    (ρ_ F).hom.natTrans.app (op ▫0)
        (dayCell F (𝟙_ (Boxᵒᵖ ⊛⥤ Type)) x (DayFunctor.ν Boxᵒᵖ Type PUnit.unit)) = x := by
  have hru : (ρ_ (op ▫0 : Boxᵒᵖ)).inv = 𝟙 _ := Box.op_hom_ext_zero rfl _ _
  have hmap : ∀ P : Boxᵒᵖ ⥤ Type,
      P.map ((ρ_ (op ▫0 : Boxᵒᵖ)).inv) = 𝟙 (P.obj (op ▫0)) := fun P => by
    rw [hru]; exact P.map_id _
  have h := LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
    (C := Boxᵒᵖ) (V := Type) (D := Boxᵒᵖ ⊛⥤ Type) F (op ▫0)
  rw [hmap] at h
  exact ConcreteCategory.congr_hom h ((x, PUnit.unit) : F.functor.obj (op ▫0) × PUnit)

/-- An iso of Day functors is an iso of the underlying presheaves. -/
def pshIsoOfDayIso {F G : Boxᵒᵖ ⊛⥤ Type} (e : F ≅ G) : F.functor ≅ G.functor where
  hom := e.hom.natTrans
  inv := e.inv.natTrans
  hom_inv_id := congrArg DayFunctor.Hom.natTrans e.hom_inv_id
  inv_hom_id := congrArg DayFunctor.Hom.natTrans e.inv_hom_id

end DayCube

/-! ### The monoidal structure on `BPSet` -/

namespace BPSet

open DayCube

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

/-- The underlying presheaf of `K`, as an object of the Day-convolution monoidal category. -/
def day (K : BPSet) : Boxᵒᵖ ⊛⥤ Type := DayFunctor.mk K.toPsh

@[simp] theorem day_functor (K : BPSet) : K.day.functor = K.toPsh := rfl

/-- A bi-pointed map, as a morphism of Day functors. -/
def dayHom {K L : BPSet} (f : K ⟶ L) : K.day ⟶ L.day := ⟨(f : Hom K L).hom⟩

@[simp] theorem dayHom_natTrans {K L : BPSet} (f : K ⟶ L) :
    (dayHom f).natTrans = (f : Hom K L).hom := rfl

@[simp] theorem dayHom_id (K : BPSet) : dayHom (𝟙 K) = 𝟙 K.day := rfl

@[simp] theorem dayHom_comp {K L M : BPSet} (f : K ⟶ L) (g : L ⟶ M) :
    dayHom (f ≫ g) = dayHom f ≫ dayHom g := rfl

/-- The geometric product of bi-pointed precubical sets. -/
noncomputable def tensorObjBP (K L : BPSet) : BPSet where
  toPsh := (K.day ⊗ L.day).functor
  init := dayCell K.day L.day K.init L.init
  final := dayCell K.day L.day K.final L.final

/-- The tensor unit: the Day unit, bi-pointed at its canonical vertex. -/
noncomputable def tensorUnitBP : BPSet where
  toPsh := (𝟙_ (Boxᵒᵖ ⊛⥤ Type)).functor
  init := DayFunctor.ν Boxᵒᵖ Type PUnit.unit
  final := DayFunctor.ν Boxᵒᵖ Type PUnit.unit

theorem tensorHom_init {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    ((dayHom f ⊗ₘ dayHom g).natTrans)⟪0⟫ (dayCell K.day L.day K.init L.init)
      = dayCell M.day N.day M.init N.init := by
  rw [tensorHom_dayCell (dayHom f) (dayHom g) K.init L.init,
    show (dayHom f).natTrans.app (op ▫0) K.init = M.init from (f : Hom K M).app_init,
    show (dayHom g).natTrans.app (op ▫0) L.init = N.init from (g : Hom L N).app_init]

theorem tensorHom_final {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    ((dayHom f ⊗ₘ dayHom g).natTrans)⟪0⟫ (dayCell K.day L.day K.final L.final)
      = dayCell M.day N.day M.final N.final := by
  rw [tensorHom_dayCell (dayHom f) (dayHom g) K.final L.final,
    show (dayHom f).natTrans.app (op ▫0) K.final = M.final from (f : Hom K M).app_final,
    show (dayHom g).natTrans.app (op ▫0) L.final = N.final from (g : Hom L N).app_final]

/-- The geometric product of bi-pointed maps. -/
noncomputable def tensorHomBP {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    tensorObjBP K L ⟶ tensorObjBP M N where
  hom := (dayHom f ⊗ₘ dayHom g).natTrans
  app_init := tensorHom_init f g
  app_final := tensorHom_final f g

noncomputable instance monoidalStruct : MonoidalCategoryStruct BPSet where
  tensorObj := tensorObjBP
  tensorHom := tensorHomBP
  whiskerLeft K _ _ f := tensorHomBP (𝟙 K) f
  whiskerRight f M := tensorHomBP f (𝟙 M)
  tensorUnit := tensorUnitBP
  associator K L M :=
    isoOfPshIso (pshIsoOfDayIso (α_ K.day L.day M.day))
      (associator_dayCell K.day L.day M.day K.init L.init M.init)
      (associator_dayCell K.day L.day M.day K.final L.final M.final)
  leftUnitor K :=
    isoOfPshIso (pshIsoOfDayIso (λ_ K.day))
      (leftUnitor_dayCell K.day K.init) (leftUnitor_dayCell K.day K.final)
  rightUnitor K :=
    isoOfPshIso (pshIsoOfDayIso (ρ_ K.day))
      (rightUnitor_dayCell K.day K.init) (rightUnitor_dayCell K.day K.final)

@[simp] theorem tensorObj_toPsh (K L : BPSet) : (K ⊗ L).toPsh = (K.day ⊗ L.day).functor := rfl

@[simp] theorem tensorHom_hom {K L M N : BPSet} (f : K ⟶ M) (g : L ⟶ N) :
    ((f ⊗ₘ g : (K ⊗ L : BPSet) ⟶ M ⊗ N) : Hom _ _).hom = (dayHom f ⊗ₘ dayHom g).natTrans := rfl

noncomputable instance monoidal : MonoidalCategory BPSet :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun K L => hom_ext
      (congrArg DayFunctor.Hom.natTrans (MonoidalCategory.id_tensorHom_id K.day L.day)))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => hom_ext
      (congrArg DayFunctor.Hom.natTrans (MonoidalCategory.tensorHom_comp_tensorHom
        (dayHom f₁) (dayHom f₂) (dayHom g₁) (dayHom g₂))))
    (associator_naturality := fun f₁ f₂ f₃ => hom_ext
      (congrArg DayFunctor.Hom.natTrans (MonoidalCategory.associator_naturality
        (dayHom f₁) (dayHom f₂) (dayHom f₃))))
    (leftUnitor_naturality := fun {K L} f => hom_ext
      (congrArg DayFunctor.Hom.natTrans (show
          (𝟙 (𝟙_ (Boxᵒᵖ ⊛⥤ Type)) ⊗ₘ dayHom f) ≫ (λ_ L.day).hom
            = (λ_ K.day).hom ≫ dayHom f by
        rw [MonoidalCategory.id_tensorHom]
        exact MonoidalCategory.leftUnitor_naturality _)))
    (rightUnitor_naturality := fun {K L} f => hom_ext
      (congrArg DayFunctor.Hom.natTrans (show
          (dayHom f ⊗ₘ 𝟙 (𝟙_ (Boxᵒᵖ ⊛⥤ Type))) ≫ (ρ_ L.day).hom
            = (ρ_ K.day).hom ≫ dayHom f by
        rw [MonoidalCategory.tensorHom_id]
        exact MonoidalCategory.rightUnitor_naturality _)))
    (pentagon := fun W X Y Z => hom_ext
      (congrArg DayFunctor.Hom.natTrans (show
          ((α_ W.day X.day Y.day).hom ⊗ₘ 𝟙 Z.day) ≫ (α_ W.day (X.day ⊗ Y.day) Z.day).hom ≫
              (𝟙 W.day ⊗ₘ (α_ X.day Y.day Z.day).hom)
            = (α_ (W.day ⊗ X.day) Y.day Z.day).hom ≫ (α_ W.day X.day (Y.day ⊗ Z.day)).hom by
        rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
        exact MonoidalCategory.pentagon _ _ _ _)))
    (triangle := fun X Y => hom_ext
      (congrArg DayFunctor.Hom.natTrans (show
          (α_ X.day (𝟙_ (Boxᵒᵖ ⊛⥤ Type)) Y.day).hom ≫ (𝟙 X.day ⊗ₘ (λ_ Y.day).hom)
            = ((ρ_ X.day).hom ⊗ₘ 𝟙 Y.day) by
        rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
        exact MonoidalCategory.triangle _ _)))

/-! ### The cubes -/

theorem cube_init_sign (n : ℕ) :
    Box.sign ((cube n).init : (▫0 : Box) ⟶ ▫n) = constVertex n false :=
  Box.sign_canonicalMap (X := ▫0) (Y := ▫n) (constVertex n false)

theorem cube_final_sign (n : ℕ) :
    Box.sign ((cube n).final : (▫0 : Box) ⟶ ▫n) = constVertex n true :=
  Box.sign_canonicalMap (X := ▫0) (Y := ▫n) (constVertex n true)

/-- The tensor of the initial vertices of `□m` and `□n` is the initial vertex of `□(m+n)`. -/
theorem cube_init_tensorHom (m n : ℕ) :
    (((cube m).init : (▫0 : Box) ⟶ ▫m) ⊗ₘ ((cube n).init : (▫0 : Box) ⟶ ▫n))
      = ((cube (m + n)).init : (▫0 : Box) ⟶ ▫(m + n)) := by
  apply Box.hom_ext
  rw [Box.sign_tensorHom, cube_init_sign, cube_init_sign]
  exact (appendCell_constVertex m n false).trans (cube_init_sign (m + n)).symm

theorem cube_final_tensorHom (m n : ℕ) :
    (((cube m).final : (▫0 : Box) ⟶ ▫m) ⊗ₘ ((cube n).final : (▫0 : Box) ⟶ ▫n))
      = ((cube (m + n)).final : (▫0 : Box) ⟶ ▫(m + n)) := by
  apply Box.hom_ext
  rw [Box.sign_tensorHom, cube_final_sign, cube_final_sign]
  exact (appendCell_constVertex m n true).trans (cube_final_sign (m + n)).symm

/-- **`□m ⊗ □n ≅ □(m+n)`** in `BPSet`: the geometric product of standard cubes is the standard
cube of the summed dimension, bi-pointing included. -/
noncomputable def cubeTensorIso (m n : ℕ) : (cube m ⊗ cube n : BPSet) ≅ cube (m + n) :=
  isoOfPshIso (Box.cubeDayIso m n)
    ((Box.cubeDayIso_hom_app m n (op ▫0, op ▫0)
      ((cube m).init, (cube n).init)).trans (cube_init_tensorHom m n))
    ((Box.cubeDayIso_hom_app m n (op ▫0, op ▫0)
      ((cube m).final, (cube n).final)).trans (cube_final_tensorHom m n))

/-! ### Vertices of a product cell

The extremal vertices of `x ⊗ y` are the products of the extremal vertices; these are the
geometric inputs a cube chain of `K ⊗ L` needs. -/

theorem initVertexMap_tensorHom (m n : ℕ) :
    ((PrecubicalSet.initVertexMap m ⊗ₘ PrecubicalSet.initVertexMap n :
        (▫0 ⊗ ▫0 : Box) ⟶ ▫m ⊗ ▫n)) = PrecubicalSet.initVertexMap (m + n) :=
  cube_init_tensorHom m n

theorem finalVertexMap_tensorHom (m n : ℕ) :
    ((PrecubicalSet.finalVertexMap m ⊗ₘ PrecubicalSet.finalVertexMap n :
        (▫0 ⊗ ▫0 : Box) ⟶ ▫m ⊗ ▫n)) = PrecubicalSet.finalVertexMap (m + n) :=
  cube_final_tensorHom m n

theorem vertex₀_dayCell (K L : BPSet) {p q : ℕ} (x : K.cells p) (y : L.cells q) :
    PrecubicalSet.vertex₀ (K.day ⊗ L.day).functor (dayCell K.day L.day x y)
      = dayCell K.day L.day (PrecubicalSet.vertex₀ K.toPsh x)
          (PrecubicalSet.vertex₀ L.toPsh y) := by
  have hnat := NatTrans.naturality_apply (DayFunctor.η K.day L.day)
    (((PrecubicalSet.initVertexMap p).op, (PrecubicalSet.initVertexMap q).op) :
      ((op ▫p : Boxᵒᵖ), (op ▫q : Boxᵒᵖ)) ⟶ (op ▫0, op ▫0))
    ((x, y) : K.cells p × L.cells q)
  change (K.day ⊗ L.day).functor.map (PrecubicalSet.initVertexMap (p + q)).op _ = _
  rw [show ((PrecubicalSet.initVertexMap (p + q)).op : (op ▫(p + q) : Boxᵒᵖ) ⟶ op ▫0)
      = ((PrecubicalSet.initVertexMap p).op ⊗ₘ (PrecubicalSet.initVertexMap q).op) from
    congrArg Quiver.Hom.op (initVertexMap_tensorHom p q).symm]
  exact hnat.symm

theorem vertex₁_dayCell (K L : BPSet) {p q : ℕ} (x : K.cells p) (y : L.cells q) :
    PrecubicalSet.vertex₁ (K.day ⊗ L.day).functor (dayCell K.day L.day x y)
      = dayCell K.day L.day (PrecubicalSet.vertex₁ K.toPsh x)
          (PrecubicalSet.vertex₁ L.toPsh y) := by
  have hnat := NatTrans.naturality_apply (DayFunctor.η K.day L.day)
    (((PrecubicalSet.finalVertexMap p).op, (PrecubicalSet.finalVertexMap q).op) :
      ((op ▫p : Boxᵒᵖ), (op ▫q : Boxᵒᵖ)) ⟶ (op ▫0, op ▫0))
    ((x, y) : K.cells p × L.cells q)
  change (K.day ⊗ L.day).functor.map (PrecubicalSet.finalVertexMap (p + q)).op _ = _
  rw [show ((PrecubicalSet.finalVertexMap (p + q)).op : (op ▫(p + q) : Boxᵒᵖ) ⟶ op ▫0)
      = ((PrecubicalSet.finalVertexMap p).op ⊗ₘ (PrecubicalSet.finalVertexMap q).op) from
    congrArg Quiver.Hom.op (finalVertexMap_tensorHom p q).symm]
  exact hnat.symm

end BPSet
