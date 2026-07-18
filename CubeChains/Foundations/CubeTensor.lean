import CubeChains.Foundations.DayTensor

/-!
# Foundations/CubeTensor — the computable geometric tensor of standard cubes

`□m ⊗ □n = □(m+n)` for representables: the pairing `η(f,g) = f ⊗ₘ g` (`cubeTensorPair`,
concatenation of sign vectors) together with its universal property (`cubeTensorDesc` /
`cubeTensorDesc_elem` / `cubeTensor_hom_ext`).  Every declaration here generates code — the
pairing reduces by `rfl` and `cubeTensorDesc` is usable in downstream `def`s.

Tensoring cubes needs no coend, so this bypasses the abstract Day-convolution wrapper
(`Box.cubeDayConv` / `Box.cubeDayIso`, both `noncomputable`: they extract a colimit descent
via `Nonempty.some`, so no code is generated).  The universal property is the computable
`CubeDay.corepExtProd`, reread through `tensor ⋙ H`.  (Proof-side `Classical.choice` from
mathlib's `Type`-category infrastructure remains in the axiom footprint; it does not affect
reduction.)
-/

open CategoryTheory Opposite MonoidalCategory
open StdCube CubeDay
open scoped MonoidalCategory.ExternalProduct

namespace Box

variable {H : Boxᵒᵖ ⥤ Type}

/-- The tensor pairing on cube cells: `(f, g) ↦ f ⊗ₘ g` (concatenation of sign vectors). -/
abbrev cubeTensorPair (m n : ℕ) :
    ((yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) ⊠ yoneda.obj ▫n) ⟶ tensor Boxᵒᵖ ⋙ yoneda.obj ▫(m + n) :=
  cubeDayUnit m n

/-- **Descent out of the cube tensor.**  An `(m+n)`-cell `t` of `H` extends to a map
`□m ⊠ □n ⟶ tensor ⋙ H` sending the universal pair `(𝟙, 𝟙)` to `t`. -/
def cubeTensorDesc (m n : ℕ) (t : H.obj (op ▫(m + n))) :
    ((yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) ⊠ yoneda.obj ▫n) ⟶ tensor Boxᵒᵖ ⋙ H :=
  (corepExtProd ▫m ▫n).desc (H := tensor Boxᵒᵖ ⋙ H) t

/-- `cubeTensorDesc` evaluates to `t` at the universal pair `(𝟙, 𝟙)`. -/
@[simp] theorem cubeTensorDesc_elem (m n : ℕ) (t : H.obj (op ▫(m + n))) :
    (cubeTensorDesc m n t).app (op ▫m, op ▫n) (corepExtProd ▫m ▫n).elem = t :=
  (corepExtProd ▫m ▫n).desc_elem (H := tensor Boxᵒᵖ ⋙ H) t

/-- A map out of the cube tensor is determined by its value at the universal pair `(𝟙, 𝟙)`. -/
theorem cubeTensor_hom_ext (m n : ℕ)
    (γ δ : ((yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) ⊠ yoneda.obj ▫n) ⟶ tensor Boxᵒᵖ ⋙ H)
    (h : γ.app (op ▫m, op ▫n) (corepExtProd ▫m ▫n).elem
       = δ.app (op ▫m, op ▫n) (corepExtProd ▫m ▫n).elem) :
    γ = δ :=
  (corepExtProd ▫m ▫n).hom_ext (H := tensor Boxᵒᵖ ⋙ H) γ δ h

end Box
