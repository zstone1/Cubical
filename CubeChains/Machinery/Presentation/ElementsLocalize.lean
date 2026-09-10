import CubeChains.Machinery.Presentation.Elements
import CubeChains.Machinery.Presentation.Localize

/-!
# Machinery/Presentation/ElementsLocalize — the picked 1-cells, lifted along the fibration

A 1-cell of `∫F` is picked when the base 1-cell it acts by is (`elementsPicked`).  The projection is
a discrete covering, so a word of picked arrows lifts letter by letter from any element over its
source, and a word upstairs *is* its projection: the lifted picked 1-cells generate exactly the
inverse image of what the picked arrows generate.  That is `presentsLocalization`'s hypothesis,
transported.
-/

universe w₂ w' w v u' u v' u₂ u₁ v₁ v₂

namespace CategoryTheory

open CategoryOfElements

/-- **A class generated downstairs is generated upstairs, image by image** — a functor preserves
identities and composites, so nothing but the generators has to be checked. -/
theorem MorphismProperty.multiplicativeClosure_map {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] (G : MorphismProperty A) (H : MorphismProperty B) (Φ : A ⥤ B)
    (h : ∀ {X Y : A} (f : X ⟶ Y), G f → H (Φ.map f)) {X Y : A} {f : X ⟶ Y}
    (hf : G.multiplicativeClosure f) : H.multiplicativeClosure (Φ.map f) := by
  induction hf with
  | of f hf => exact .of _ (h f hf)
  | id X => rw [Φ.map_id]; exact .id _
  | comp_of f g _ hg ih =>
      rw [Φ.map_comp]
      exact H.multiplicativeClosure.comp_mem _ _ ih (.of _ (h g hg))

namespace Presents

open Polygraph

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (F : C ⥤ Type w') (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **A picked 1-cell of `∫F` lies over a picked arrow.** -/
theorem pickedArrows_elements_le :
    (p.elements F).pickedArrows (p.elementsPicked F S)
      ≤ (p.pickedArrows S).inverseImage (CategoryOfElements.π F) := by
  rintro X Y f ⟨e, he⟩
  exact Eq.mpr (congrArg (fun g => p.Picked S g) (p.elements_arrow_val F e))
    (Presents.Picked.mk e.1 he)

/-- **A picked arrow, lifted from an element over its source** — the target is forced. -/
theorem picked_lift {A B : C} {g : A ⟶ B} (hg : p.pickedArrows S g) (x : F.obj A) (y : F.obj B)
    (hxy : F.map g x = y) :
    (p.elements F).pickedArrows (p.elementsPicked F S)
      (homMk (F.elementsMk A x) (F.elementsMk B y) g hxy) := by
  obtain ⟨e, he⟩ := hg
  have h : homMk (F.elementsMk _ x) (F.elementsMk _ y) (p.arrow (Polygraph.cell e)) hxy
      = (p.elements F).arrow (⟨e, hxy⟩ : (p.elementsPoly F).Gen ⟨_, x⟩ ⟨_, y⟩) :=
    (p.elements_arrow F (⟨e, hxy⟩ : (p.elementsPoly F).Gen ⟨_, x⟩ ⟨_, y⟩)).symm
  rw [h]
  exact Presents.Picked.mk _ he

/-- **A word of picked arrows lifts**, from any element over its source. -/
theorem multiplicativeClosure_picked_lift :
    ∀ {A B : C} {g : A ⟶ B}, (p.pickedArrows S).multiplicativeClosure g →
      ∀ (x : F.obj A) (y : F.obj B) (hxy : F.map g x = y),
        ((p.elements F).pickedArrows (p.elementsPicked F S)).multiplicativeClosure
          (homMk (F.elementsMk A x) (F.elementsMk B y) g hxy) := by
  intro A B g hg
  induction hg with
  | of g hg => exact fun x y hxy => .of _ (p.picked_lift F S hg x y hxy)
  | id A =>
      intro x y hxy
      obtain rfl : x = y := (F.map_id_apply A x).symm.trans hxy
      rw [show homMk (F.elementsMk A x) (F.elementsMk A x) (𝟙 A) hxy = 𝟙 (F.elementsMk A x) from
        Subtype.ext rfl]
      exact .id _
  | @comp_of A B D g h _ hh ih =>
      intro x z hxz
      have hg : F.map g x = F.map g x := rfl
      have hh' : F.map h (F.map g x) = z := by rw [← Functor.map_comp_apply]; exact hxz
      have hcomp : homMk (F.elementsMk A x) (F.elementsMk B (F.map g x)) g hg
            ≫ homMk (F.elementsMk B (F.map g x)) (F.elementsMk D z) h hh'
          = homMk (F.elementsMk A x) (F.elementsMk D z) (g ≫ h) hxz := Subtype.ext rfl
      rw [← hcomp]
      exact .comp_of _ _ (ih x _ hg) (p.picked_lift F S hh _ _ hh')

/-- **The lifted picked 1-cells generate the inverse image of what the picked arrows generate.**
The fibration is discrete, so a factorization downstairs lifts, and a letter upstairs *is* its
projection, so nothing else is in the closure. -/
theorem multiplicativeClosure_pickedArrows_elements :
    ((p.elements F).pickedArrows (p.elementsPicked F S)).multiplicativeClosure
      = ((p.pickedArrows S).multiplicativeClosure).inverseImage (CategoryOfElements.π F) := by
  refine le_antisymm ((MorphismProperty.multiplicativeClosure_le_iff _ _).mpr
    ((p.pickedArrows_elements_le F S).trans (MorphismProperty.monotone_inverseImage _
      (MorphismProperty.le_multiplicativeClosure _)))) fun X Y f hf => ?_
  exact p.multiplicativeClosure_picked_lift F S hf X.2 Y.2 f.property

/-- **A transported presentation picks out the images of the picked arrows.** -/
theorem pickedArrows_transport {D : Type*} [Category D] (e : C ≌ D) {A B : C} (g : A ⟶ B)
    (hg : p.pickedArrows S g) : (p.transport e).pickedArrows S (e.functor.map g) := by
  obtain ⟨t, ht⟩ := hg
  exact Presents.Picked.mk t ht

end Presents

end CategoryTheory
