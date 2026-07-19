import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Foundations/MonoidalTransport

Transporting `⊗ₘ` along a family of comparison isos `μ : A ⊗ B ≅ P` (a *tensorator*): the
morphism `μ.inv ≫ (f ⊗ₘ g) ≫ μ'.hom`.  Such a transport is automatically functorial, and its
coherence squares are exactly the tensorator's own coherence squares conjugated by `⊗ₘ`'s
bifunctoriality — no `Glue.desc` chase.

Stated in an arbitrary `[MonoidalCategory M]`, which is the point: at `BPSet` a bare
`rw [Category.assoc]` can fail to match, while here `rw`/`simp`/`monoidal` all behave.
-/

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {M : Type*} [Category M] [MonoidalCategory M]

/-- Transporting a pair of identities gives the identity. -/
theorem tensorTransport_id {A B P : M} (μ : A ⊗ B ≅ P) :
    μ.inv ≫ (𝟙 A ⊗ₘ 𝟙 B) ≫ μ.hom = 𝟙 P := by
  rw [id_tensorHom_id, Category.id_comp, μ.inv_hom_id]

/-- Transport is functorial in the pair. -/
theorem tensorTransport_comp {A B A' B' A'' B'' P P' P'' : M}
    (μ : A ⊗ B ≅ P) (μ' : A' ⊗ B' ≅ P') (μ'' : A'' ⊗ B'' ≅ P'')
    (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : B ⟶ B') (g₂ : B' ⟶ B'') :
    μ.inv ≫ ((f₁ ≫ f₂) ⊗ₘ (g₁ ≫ g₂)) ≫ μ''.hom
      = (μ.inv ≫ (f₁ ⊗ₘ g₁) ≫ μ'.hom) ≫ μ'.inv ≫ (f₂ ⊗ₘ g₂) ≫ μ''.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc]

/-- A transport followed by an untransported tensor collapses into a single transport: the
commuting triangle over a common target. -/
theorem tensorTransport_comp_tensorHom {A B A' B' C D P P' : M}
    (μ : A ⊗ B ≅ P) (μ' : A' ⊗ B' ≅ P')
    (f : A ⟶ A') (g : B ⟶ B') (u : A' ⟶ C) (v : B' ⟶ D) :
    (μ.inv ≫ (f ⊗ₘ g) ≫ μ'.hom) ≫ μ'.inv ≫ (u ⊗ₘ v) = μ.inv ≫ ((f ≫ u) ⊗ₘ (g ≫ v)) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_comp_tensorHom]

/-- Post-composing a transport with a right whiskering. -/
theorem tensorTransport_comp_whiskerRight {A B A' B' C P : M} (μ : A ⊗ B ≅ P)
    (f : A ⟶ A') (g : B ⟶ B') (u : A' ⟶ C) :
    (μ.inv ≫ (f ⊗ₘ g)) ≫ (u ▷ B') = μ.inv ≫ ((f ≫ u) ⊗ₘ g) := by
  simp only [← tensorHom_id, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- Post-composing a transport with a left whiskering. -/
theorem tensorTransport_comp_whiskerLeft {A B A' B' D P : M} (μ : A ⊗ B ≅ P)
    (f : A ⟶ A') (g : B ⟶ B') (v : B' ⟶ D) :
    (μ.inv ≫ (f ⊗ₘ g)) ≫ (A' ◁ v) = μ.inv ≫ (f ⊗ₘ (g ≫ v)) := by
  simp only [← id_tensorHom, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- **Associativity of the transport**, across the comparison maps `Θ`/`Θ'`.  The hypotheses
`hc`/`hc'` are the tensorator's own associativity square; everything else is bifunctoriality of
`⊗ₘ` plus associator naturality. -/
theorem tensorTransport_assoc
    {A B C A' B' C' P P' Q Q' N N' R R' : M}
    (μ₁ : A ⊗ B ≅ P) (μ₂ : P ⊗ C ≅ Q) (μ₃ : B ⊗ C ≅ N) (μ₄ : A ⊗ N ≅ R)
    (μ₁' : A' ⊗ B' ≅ P') (μ₂' : P' ⊗ C' ≅ Q') (μ₃' : B' ⊗ C' ≅ N') (μ₄' : A' ⊗ N' ≅ R')
    {Θ : Q ⟶ R} {Θ' : Q' ⟶ R'}
    (hc : μ₁.hom ▷ C ≫ μ₂.hom ≫ Θ = (α_ A B C).hom ≫ A ◁ μ₃.hom ≫ μ₄.hom)
    (hc' : μ₁'.hom ▷ C' ≫ μ₂'.hom ≫ Θ' = (α_ A' B' C').hom ≫ A' ◁ μ₃'.hom ≫ μ₄'.hom)
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    (μ₂.inv ≫ ((μ₁.inv ≫ (f ⊗ₘ g) ≫ μ₁'.hom) ⊗ₘ h) ≫ μ₂'.hom) ≫ Θ'
      = Θ ≫ (μ₄.inv ≫ (f ⊗ₘ (μ₃.inv ≫ (g ⊗ₘ h) ≫ μ₃'.hom)) ≫ μ₄'.hom) := by
  haveI : IsIso (μ₁.hom ▷ C ≫ μ₂.hom) := by
    rw [show μ₁.hom ▷ C ≫ μ₂.hom = (whiskerRightIso μ₁ C ≪≫ μ₂).hom from rfl]; infer_instance
  rw [← cancel_epi (μ₁.hom ▷ C ≫ μ₂.hom)]
  have hL : (μ₁.hom ▷ C ≫ μ₂.hom)
        ≫ ((μ₂.inv ≫ ((μ₁.inv ≫ (f ⊗ₘ g) ≫ μ₁'.hom) ⊗ₘ h) ≫ μ₂'.hom) ≫ Θ')
      = ((f ⊗ₘ g) ⊗ₘ h) ≫ (μ₁'.hom ▷ C' ≫ μ₂'.hom ≫ Θ') := by
    simp only [← tensorHom_id, Category.assoc, tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id_assoc, Category.comp_id, Category.id_comp]
  have hR : (μ₁.hom ▷ C ≫ μ₂.hom)
        ≫ (Θ ≫ (μ₄.inv ≫ (f ⊗ₘ (μ₃.inv ≫ (g ⊗ₘ h) ≫ μ₃'.hom)) ≫ μ₄'.hom))
      = (α_ A B C).hom ≫ A ◁ μ₃.hom
        ≫ μ₄.hom ≫ μ₄.inv ≫ (f ⊗ₘ (μ₃.inv ≫ (g ⊗ₘ h) ≫ μ₃'.hom)) ≫ μ₄'.hom := by
    rw [Category.assoc, reassoc_of% hc]
  rw [hL, hR, hc']
  simp only [associator_naturality_assoc, ← id_tensorHom, Iso.hom_inv_id_assoc,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

/-- **Right unitality of the transport**, across the comparison maps `Θ`/`Θ'`. -/
theorem tensorTransport_rightUnit {A A' P P' : M}
    (μ : A ⊗ 𝟙_ M ≅ P) (μ' : A' ⊗ 𝟙_ M ≅ P') {Θ : P ⟶ A} {Θ' : P' ⟶ A'}
    (hc : μ.hom ≫ Θ = (ρ_ A).hom) (hc' : μ'.hom ≫ Θ' = (ρ_ A').hom) (f : A ⟶ A') :
    (μ.inv ≫ (f ⊗ₘ 𝟙 (𝟙_ M)) ≫ μ'.hom) ≫ Θ' = Θ ≫ f := by
  rw [← cancel_epi μ.hom, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Category.assoc, hc', ← Category.assoc, hc, tensorHom_id,
    rightUnitor_naturality]

/-- Associativity of the transport **into a plain tensor**: the case of `tensorTransport_assoc`
where the target tensorators are identities, so `Θ'` is the associator itself.  This is the shape
of the object part of a lax-monoidal comparison. -/
theorem tensorTransport_assoc_refl {A B C X Y Z P Q N R : M}
    (μ₁ : A ⊗ B ≅ P) (μ₂ : P ⊗ C ≅ Q) (μ₃ : B ⊗ C ≅ N) (μ₄ : A ⊗ N ≅ R)
    {Θ : Q ⟶ R}
    (hc : μ₁.hom ▷ C ≫ μ₂.hom ≫ Θ = (α_ A B C).hom ≫ A ◁ μ₃.hom ≫ μ₄.hom)
    (f : A ⟶ X) (g : B ⟶ Y) (h : C ⟶ Z) :
    (μ₂.inv ≫ ((μ₁.inv ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫ (α_ X Y Z).hom
      = Θ ≫ μ₄.inv ≫ (f ⊗ₘ (μ₃.inv ≫ (g ⊗ₘ h))) := by
  have h' := tensorTransport_assoc μ₁ μ₂ μ₃ μ₄ (Iso.refl (X ⊗ Y)) (Iso.refl ((X ⊗ Y) ⊗ Z))
    (Iso.refl (Y ⊗ Z)) (Iso.refl (X ⊗ (Y ⊗ Z))) (Θ' := (α_ X Y Z).hom) hc (by monoidal) f g h
  simpa using h'

/-! ### Cons steps for a tensorator built by iterated whiskering

A tensorator defined by recursion as `μ_{n :: x, y} = α_ ≫ n ◁ μ_{x, y}` satisfies its
coherence squares by induction, with these two steps at each cons. -/

/-- One inductive step of a tensorator's associativity square: pentagon plus associator
naturality. -/
theorem whiskerLeft_assoc_step {A B U D E P G : M}
    (f : B ⊗ U ⟶ E) (g : E ⊗ D ⟶ P) (h : U ⊗ D ⟶ G) (k : B ⊗ G ⟶ P)
    (ih : f ▷ D ≫ g = (α_ B U D).hom ≫ B ◁ h ≫ k) :
    ((α_ A B U).hom ≫ A ◁ f) ▷ D ≫ (α_ A E D).hom ≫ A ◁ g
      = (α_ (A ⊗ B) U D).hom ≫ (A ⊗ B) ◁ h ≫ (α_ A B G).hom ≫ A ◁ k := by
  rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp, ih]
  monoidal

/-- One inductive step of a tensorator's right-unitality square: the triangle, whiskered. -/
theorem whiskerLeft_rightUnit_step {A B P : M}
    (f : B ⊗ 𝟙_ M ⟶ P) (r : P ⟶ B) (ih : f ≫ r = (ρ_ B).hom) :
    ((α_ A B (𝟙_ M)).hom ≫ A ◁ f) ≫ A ◁ r = (ρ_ (A ⊗ B)).hom := by
  rw [Category.assoc, ← whiskerLeft_comp, ih]
  monoidal

/-- Right unitality of the transport **into a plain tensor**: the `Iso.refl` case of
`tensorTransport_rightUnit`. -/
theorem tensorTransport_rightUnit_refl {A X P : M} (μ : A ⊗ 𝟙_ M ≅ P) {Θ : P ⟶ A}
    (hc : μ.hom ≫ Θ = (ρ_ A).hom) (f : A ⟶ X) :
    (μ.inv ≫ (f ⊗ₘ 𝟙 (𝟙_ M))) ≫ (ρ_ X).hom = Θ ≫ f := by
  have h := tensorTransport_rightUnit μ (Iso.refl (X ⊗ 𝟙_ M)) hc (Category.id_comp _) f
  simpa using h

/-- **Left unitality of the transport** against the left unitor as tensorator. -/
theorem tensorTransport_leftUnitor {B B' : M} (g : B ⟶ B') :
    (λ_ B).inv ≫ (𝟙 (𝟙_ M) ⊗ₘ g) ≫ (λ_ B').hom = g := by
  rw [id_tensorHom, leftUnitor_naturality, Iso.inv_hom_id_assoc]

end CategoryTheory.MonoidalCategory
