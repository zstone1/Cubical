import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-!
# Machinery/SigmaComponents — splitting a category along a hom-disjoint cover

A family of object properties that covers every object, with no morphism between different
members, exhibits the category as the disjoint union of the corresponding full subcategories.
Mathlib's `ConnectedComponents.decomposedEquiv` is the case where the index is the set of
components; here the index is supplied.
-/

universe w v u

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {ι : Type w} (P : ι → ObjectProperty C)

/-- The inclusions of a family of full subcategories, assembled on their disjoint union. -/
def sigmaι : (Σ i, (P i).FullSubcategory) ⥤ C :=
  Sigma.desc fun i => (P i).ι

instance : (sigmaι P).Faithful where
  map_injective := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨⟨_⟩⟩ ⟨⟨_⟩⟩ rfl
    rfl

/-- **An arrow cannot leave a member of a hom-disjoint cover, in either direction** — cover the end
that is not known, and `hdisj` names it. -/
theorem prop_iff_of_hom (hcover : ∀ X : C, ∃ i, P i X)
    (hdisj : ∀ {i j : ι} {X Y : C}, P i X → P j Y → (X ⟶ Y) → i = j)
    {i : ι} {X Y : C} (f : X ⟶ Y) : P i X ↔ P i Y :=
  ⟨fun hX => by obtain ⟨j, hj⟩ := hcover Y; obtain rfl := hdisj hX hj f; exact hj,
    fun hY => by obtain ⟨j, hj⟩ := hcover X; obtain rfl := hdisj hj hY f; exact hj⟩

theorem sigmaι_full (hdisj : ∀ {i j : ι} {X Y : C}, P i X → P j Y → (X ⟶ Y) → i = j) :
    (sigmaι P).Full where
  map_surjective := by
    rintro ⟨i, X, hX⟩ ⟨j, Y, hY⟩ f
    obtain rfl := hdisj hX hY f
    exact ⟨Sigma.SigmaHom.mk (homMk f), rfl⟩

theorem sigmaι_essSurj (hcover : ∀ X : C, ∃ i, P i X) : (sigmaι P).EssSurj where
  mem_essImage X := by
    obtain ⟨i, hi⟩ := hcover X
    exact ⟨⟨i, X, hi⟩, ⟨Iso.refl _⟩⟩

/-- **A hom-disjoint cover splits the category** into the disjoint union of its members. -/
noncomputable def sigmaEquiv (hcover : ∀ X : C, ∃ i, P i X)
    (hdisj : ∀ {i j : ι} {X Y : C}, P i X → P j Y → (X ⟶ Y) → i = j) :
    C ≌ Σ i, (P i).FullSubcategory := by
  haveI := sigmaι_full P hdisj
  haveI := sigmaι_essSurj P hcover
  haveI : (sigmaι P).IsEquivalence := { }
  exact (sigmaι P).asEquivalence.symm

end ObjectProperty

end CategoryTheory
