import CubeChains.Arrangements.COMSum
import CubeChains.Arrangements.ElementsProd

/-!
# Arrangements/SalSum — the Salvetti presheaf splits over a direct sum

The Salvetti presheaf of a direct sum is the external product of the two summand
presheaves, over the face-restriction equivalence:

      salFunctor (L₁ ⊕ L₂)  ≅  faceSum L₁ L₂ ⋙ (salFunctor L₁ ⊠ salFunctor L₂)

      Face (L₁ ⊕ L₂)  ≌  Face L₁ × Face L₂           (faceSum / faceSumEquiv)

On a face `X` the fibre of topes above `X` bijects with the product of the two summand
fibres (`salSumObjEquiv`), splitting a tope into its two restrictions and merging back by
`SignVec.elim`.  The covector-level analogue of the chamber-side `multIso`
(`Salvetti/LinesWedge.lean`).
-/

open CategoryTheory

namespace CubeChains

namespace COM

open SignVec

universe u

variable {E₁ E₂ : Type u}

/-! ## Restriction and gluing of faces of a direct sum -/

/-- A face of `L₁ ⊕ L₂` restricted to the left summand. -/
def Face.restrictL (L₁ : COM E₁) (L₂ : COM E₂) (X : Face (L₁.directSum L₂)) : Face L₁ :=
  ⟨SignVec.restrictL X.1, (mem_directSum_covectors.mp X.2).1⟩

/-- A face of `L₁ ⊕ L₂` restricted to the right summand. -/
def Face.restrictR (L₁ : COM E₁) (L₂ : COM E₂) (X : Face (L₁.directSum L₂)) : Face L₂ :=
  ⟨SignVec.restrictR X.1, (mem_directSum_covectors.mp X.2).2⟩

/-- Gluing a pair of faces into a face of the direct sum. -/
def Face.elim (L₁ : COM E₁) (L₂ : COM E₂) (u : Face L₁) (v : Face L₂) :
    Face (L₁.directSum L₂) :=
  ⟨Sum.elim u.1 v.1, u.2, v.2⟩

variable (L₁ : COM E₁) (L₂ : COM E₂)

/-- The product of two face posets is thin (a product of thin categories). -/
instance face_prod_isThin : Quiver.IsThin (Face L₁ × Face L₂) := fun _ _ =>
  ⟨fun _ _ => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- Restrict a face of `L₁ ⊕ L₂` to each summand; monotone by `faceLE_sum_iff`. -/
def faceSum : Face (L₁.directSum L₂) ⥤ Face L₁ × Face L₂ where
  obj X := (Face.restrictL L₁ L₂ X, Face.restrictR L₁ L₂ X)
  map {_ _} h := (homOfLE (faceLE_sum_iff.mp (leOfHom h)).1,
                  homOfLE (faceLE_sum_iff.mp (leOfHom h)).2)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- `Face` turns direct sums into products; the covector-level shadow of `salSumEquiv`. -/
noncomputable def faceSumEquiv : Face (L₁.directSum L₂) ≌ Face L₁ × Face L₂ :=
  haveI : (faceSum L₁ L₂).IsEquivalence :=
    { faithful := ⟨fun _ => Subsingleton.elim _ _⟩
      full := ⟨fun {_ _} k =>
        ⟨homOfLE (faceLE_sum_iff.mpr ⟨leOfHom k.1, leOfHom k.2⟩), Subsingleton.elim _ _⟩⟩
      essSurj := ⟨fun uv => ⟨Face.elim L₁ L₂ uv.1 uv.2, ⟨eqToIso rfl⟩⟩⟩ }
  (faceSum L₁ L₂).asEquivalence

/-! ## The object-level split of topes above a face -/

/-- The topes above a face `X` of `L₁ ⊕ L₂` biject with the product of the topes above
`restrictL X` and above `restrictR X`: split by `isTope_directSum_iff`/`faceLE_sum_iff`,
merge by `SignVec.elim`. -/
def salSumObjEquiv (X : Face (L₁.directSum L₂)) :
    {T : SignVec (E₁ ⊕ E₂) // (L₁.directSum L₂).IsTope T ∧ X.1 ⊑ T} ≃
      {T₁ : SignVec E₁ // L₁.IsTope T₁ ∧ SignVec.restrictL X.1 ⊑ T₁} ×
        {T₂ : SignVec E₂ // L₂.IsTope T₂ ∧ SignVec.restrictR X.1 ⊑ T₂} where
  toFun T :=
    (⟨SignVec.restrictL T.1, (isTope_directSum_iff.mp T.2.1).1, (faceLE_sum_iff.mp T.2.2).1⟩,
     ⟨SignVec.restrictR T.1, (isTope_directSum_iff.mp T.2.1).2, (faceLE_sum_iff.mp T.2.2).2⟩)
  invFun p :=
    ⟨Sum.elim p.1.1 p.2.1,
      isTope_directSum_iff.mpr ⟨p.1.2.1, p.2.2.1⟩,
      faceLE_sum_iff.mpr ⟨p.1.2.2, p.2.2.2⟩⟩
  left_inv T := Subtype.ext (SignVec.elim_restrict T.1)
  right_inv p := Prod.ext (Subtype.ext (SignVec.restrictL_elim p.1.1 p.2.1))
    (Subtype.ext (SignVec.restrictR_elim p.1.1 p.2.1))

/-! ## The multiplicativity natural isomorphism -/

/-- `salFunctor (L₁ ⊕ L₂) ≅ faceSum L₁ L₂ ⋙ (salFunctor L₁ ⊠ salFunctor L₂)`: on objects the
fibre split `salSumObjEquiv`, naturality the coordinatewise split of the wall-crossing
projection (`restrictL_comp`/`restrictR_comp`). -/
noncomputable def salFunctorSumIso :
    salFunctor (L₁.directSum L₂) ≅
      faceSum L₁ L₂ ⋙ CategoryOfElements.extProd (salFunctor L₁) (salFunctor L₂) :=
  NatIso.ofComponents
    (fun X => (salSumObjEquiv L₁ L₂ X).toIso)
    (by
      intro X Y h
      apply ConcreteCategory.hom_ext
      intro T
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (SignVec.restrictL_comp Y.1 T.1)
      · exact Subtype.ext (SignVec.restrictR_comp Y.1 T.1))

end COM

end CubeChains
