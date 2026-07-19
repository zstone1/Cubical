import CubeChains.Chains.WedgeLaxMonoidal
import CubeChains.Chains.Segal
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Chains/SerialWedgeFunctor — the serial wedge as a strong monoidal functor

`serialWedgeFunctor : DimList ⥤ BPSet` sends a word to its serial wedge, with tensorator
`serialWedgeAppend` and identity unit.  Naturality is free (the source is `Discrete`), and each
coherence field is the append iso's own square (`Chains/Segal`) after identifying what the functor
does to the discrete associator/unitors.
-/

open CategoryTheory MonoidalCategory ChainCat BPSet

/-- `DimList` — the index category of dimension sequences (words in `ℕ+`) for the serial wedge.
Discrete, so its only morphisms are identities; its monoidal product is list append
(`Discrete.monoidal` on `FreeMonoid ℕ+`), with unit the empty word.  An `abbrev` (a *type*), so it
stays reducible and the `Discrete` instances still fire through it. -/
abbrev DimList := Discrete (FreeMonoid ℕ+)

namespace ChainCat

/-- The serial wedge as a functor from the free monoid on `ℕ+`. -/
def serialWedgeFunctor : DimList ⥤ BPSet :=
  Discrete.functor (fun l => ⋁ (FreeMonoid.toList l))

@[simp] theorem serialWedgeFunctor_obj (l : FreeMonoid ℕ+) :
    serialWedgeFunctor.obj (Discrete.mk l) = ⋁ (FreeMonoid.toList l) := rfl

/-! ### What the functor does to the discrete structure maps

`DimList` is thin, so each structure map is the unique `eqToHom`; the functor sends it to the
corresponding `⋁`-reindexing.  Left unitors land on the identity (`[] ++ x` is `x` on the nose). -/

/-- `serialWedgeFunctor` sends the discrete associator to the `serialWedge` reindexing. -/
theorem serialWedgeFunctor_map_associator (X Y Z : DimList) :
    serialWedgeFunctor.map (α_ X Y Z).hom = serialWedgeAssocBP X.as Y.as Z.as := by
  have h : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) := Discrete.ext (Discrete.eq_of_hom (α_ X Y Z).hom)
  rw [Subsingleton.elim (α_ X Y Z).hom (eqToHom h), eqToHom_map]
  rfl

/-- `serialWedgeFunctor` sends the discrete left unitor to the identity (the empty word is a
strict left unit for `++`). -/
theorem serialWedgeFunctor_map_leftUnitor (X : DimList) :
    serialWedgeFunctor.map (λ_ X).hom = 𝟙 (⋁ (FreeMonoid.toList X.as)) := by
  have h : 𝟙_ (DimList) ⊗ X = X := Discrete.ext (Discrete.eq_of_hom (λ_ X).hom)
  rw [Subsingleton.elim (λ_ X).hom (eqToHom h), eqToHom_map]
  rfl

/-- `serialWedgeFunctor` sends the discrete right unitor to the `append_nil` reindexing. -/
theorem serialWedgeFunctor_map_rightUnitor (X : DimList) :
    serialWedgeFunctor.map (ρ_ X).hom = serialWedgeNilBP X.as := by
  have h : X ⊗ 𝟙_ (DimList) = X := Discrete.ext (Discrete.eq_of_hom (ρ_ X).hom)
  rw [Subsingleton.elim (ρ_ X).hom (eqToHom h), eqToHom_map]
  rfl

/-! ### The strong-monoidal structure -/

/-- Strong-monoidal core: tensorator `serialWedgeAppend`, identity unit. -/
def serialWedgeFunctorCore : serialWedgeFunctor.CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := serialWedgeAppend X.as Y.as
  μIso_hom_natural_left := by
    rintro ⟨x⟩ ⟨y⟩ f X'
    obtain rfl : x = y := Discrete.eq_of_hom f
    rw [Subsingleton.elim f (𝟙 _)]
    simp
  μIso_hom_natural_right := by
    rintro ⟨x⟩ ⟨y⟩ X' f
    obtain rfl : x = y := Discrete.eq_of_hom f
    rw [Subsingleton.elim f (𝟙 _)]
    simp
  associativity X Y Z := by
    rw [serialWedgeFunctor_map_associator]
    exact serialWedgeAppendIso_assoc X.as Y.as Z.as
  left_unitality X := by
    rw [serialWedgeFunctor_map_leftUnitor]
    change (λ_ (⋁X.as)).hom
      = 𝟙 (𝟙_ BPSet) ▷ (⋁X.as) ≫ (λ_ (⋁X.as)).hom ≫ 𝟙 (⋁X.as)
    monoidal
  right_unitality X := by
    rw [serialWedgeFunctor_map_rightUnitor]
    change (ρ_ (⋁X.as)).hom
      = (⋁X.as) ◁ 𝟙 (𝟙_ BPSet) ≫ serialWedgeAppendHom X.as [] ≫ serialWedgeNilBP X.as
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    exact (serialWedgeAppendIso_right_unitality X.as).symm

/-- The serial wedge is a strong monoidal functor `DimList ⥤ BPSet`. -/
instance : serialWedgeFunctor.Monoidal := serialWedgeFunctorCore.toMonoidal

@[simp] theorem serialWedgeFunctor_μ (X Y : DimList) :
    Functor.LaxMonoidal.μ serialWedgeFunctor X Y = serialWedgeAppendHom X.as Y.as := rfl

end ChainCat
