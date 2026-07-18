import CubeChains.Foundations.GeoTensor

/-!
# Foundations/GeoTensor/Hom — the geometric tensor as a bifunctor on maps

The action of the computable geometric tensor (`Foundations/GeoTensor`) on precubical maps:
`tensorHom f g` runs `f` on the `X`-half and `g` on the `Y`-half of each product cell.  It is a
bifunctor (`tensorHom_id`, `tensorHom_comp_tensorHom`); naturality is componentwise naturality of
`f`, `g` against the split-restrict (`app_restr`).
-/

open CategoryTheory Opposite StdCube

namespace GeoTensor

/-- Naturality of a presheaf map against a sign-vector restriction: `f` commutes with `restr`. -/
theorem app_restr {X X' : PrecubicalSet} (f : X ⟶ X') {p a : ℕ} (x : X.obj (op ▫p))
    (c : Cell p a) : f.app (op ▫a) (restr X x c) = restr X' (f.app (op ▫p) x) c :=
  NatTrans.naturality_apply f (Box.ofSign c).op x

/-- The geometric tensor of two maps: run `f` on the `X`-half and `g` on the `Y`-half. -/
def tensorHom {X X' Y Y' : PrecubicalSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X' Y' where
  app B := TypeCat.ofHom fun c =>
    (⟨c.p, c.q, c.hpq, f.app (op ▫c.p) c.x, g.app (op ▫c.q) c.y⟩ : tensorCells X' Y' B.unop.dim)
  naturality := by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro c
    simp only [types_comp_apply, TypeCat.ofHom_apply, tensorObj_map]
    exact tensorCells_ext rfl rfl
      (heq_of_eq (app_restr f c.x (splitLeft (recast c.hpq (Box.sign φ.unop)))))
      (heq_of_eq (app_restr g c.y (splitRight (recast c.hpq (Box.sign φ.unop)))))

@[simp] theorem tensorHom_app {X X' Y Y' : PrecubicalSet} (f : X ⟶ X') (g : Y ⟶ Y')
    (B : Boxᵒᵖ) (c : tensorCells X Y B.unop.dim) :
    (tensorHom f g).app B c
      = ⟨c.p, c.q, c.hpq, f.app (op ▫c.p) c.x, g.app (op ▫c.q) c.y⟩ := rfl

/-- Restriction of a product cell of the tensor of maps. -/
theorem tensorHom_pair {X X' Y Y' : PrecubicalSet} (f : X ⟶ X') (g : Y ⟶ Y') {p q : ℕ}
    (x : X.obj (op ▫p)) (y : Y.obj (op ▫q)) :
    (tensorHom f g).app (op ▫(p + q)) (pair X Y x y)
      = pair X' Y' (f.app (op ▫p) x) (g.app (op ▫q) y) := rfl

/-- Left whiskering by `X`. -/
def whiskerLeft (X : PrecubicalSet) {Y Y' : PrecubicalSet} (g : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X Y' := tensorHom (𝟙 X) g

/-- Right whiskering by `Y`. -/
def whiskerRight {X X' : PrecubicalSet} (f : X ⟶ X') (Y : PrecubicalSet) :
    tensorObj X Y ⟶ tensorObj X' Y := tensorHom f (𝟙 Y)

theorem tensorHom_id (X Y : PrecubicalSet) : tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj X Y) := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  simp only [tensorHom_app, NatTrans.id_app, types_id_apply]
  rfl

theorem tensorHom_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : PrecubicalSet}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  simp only [tensorHom_app, NatTrans.comp_app, types_comp_apply]

end GeoTensor
