import CubeChains.Chains.WedgeLaxMonoidal
import CubeChains.Chains.Segal
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Chains/SerialWedgeFunctor — the serial wedge as a strong monoidal functor

`serialWedgeFunctor : DimList ⥤ BPSet` sends a word to its serial wedge, with
tensorator `serialWedgeAppend` and identity unit.  Naturality is free (the source is `Discrete`).
The tensorator is built only from `λ_`/`α_`/whiskering, so its coherence squares are induction
on the word with a structural step at each cons — `monoidal` closes them.
-/

open CategoryTheory MonoidalCategory ChainCat BPSet

/-- `DimList` — the index category of dimension sequences (words in `ℕ+`) for the serial wedge.
Discrete, so its only morphisms are identities; its monoidal product is list append
(`Discrete.monoidal` on `FreeMonoid ℕ+`), with unit the empty word.  An `abbrev` (a *type*), so it
stays reducible and the `Discrete` instances still fire through it. -/
abbrev DimList := Discrete (FreeMonoid ℕ+)

namespace ChainCat

/-! ### The append iso restricted to the empty left word is the left unitor -/

/-- With the empty left word the tensorator is definitionally the wedge left-unit. -/
theorem serialWedgeAppendHom_nil_left (x : List ℕ+) :
    (serialWedgeAppendHom [] x).hom = wedge2LeftUnitPsh (⋁x) := rfl

/-! ### The tensorator in monoidal notation

`serialWedgeAppend` is assembled only from `λ_`, `α_` and left whiskering, so both coherence
squares below are monoidal identities in disguise: associativity is *pentagon + associator
naturality*, right unitality is the *triangle* family.  Each inductive step closes with
mathlib's `monoidal`. -/

theorem serialWedgeAppendHom_nil' (y : List ℕ+) :
    serialWedgeAppendHom ([] : List ℕ+) y = (λ_ (⋁y)).hom := rfl

theorem serialWedgeAppendHom_cons' (n : ℕ+) (x y : List ℕ+) :
    serialWedgeAppendHom (n :: x) y
      = (α_ (□(n : ℕ)) (⋁x) (⋁y)).hom ≫ (□(n : ℕ)) ◁ serialWedgeAppendHom x y := rfl

/-- An `⋁`-reindexing of the tail of a cons is the head-cube whiskering of the reindexing. -/
private theorem serialWedge_eqToHom_cons (n : ℕ+) {l l' : List ℕ+} (h : l = l') :
    (eqToHom (congrArg BPSet.serialWedge (congrArg (fun m => n :: m) h)) :
        ⋁(n :: l) ⟶ ⋁(n :: l'))
      = (□(n : ℕ)) ◁ eqToHom (congrArg BPSet.serialWedge h) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, MonoidalCategory.whiskerLeft_id]
  rfl

/-- The `List.append_assoc` reindexing as a `BPSet` morphism. -/
def serialWedgeAssocBP (x y z : List ℕ+) : ⋁((x ++ y) ++ z) ⟶ ⋁(x ++ (y ++ z)) :=
  eqToHom (congrArg BPSet.serialWedge (List.append_assoc x y z))

@[simp] theorem serialWedgeAssocBP_hom (x y z : List ℕ+) :
    (serialWedgeAssocBP x y z).hom = serialWedgeAssoc x y z :=
  bpset_eqToHom_hom' _

theorem serialWedgeAssocBP_cons (n : ℕ+) (x y z : List ℕ+) :
    serialWedgeAssocBP (n :: x) y z = (□(n : ℕ)) ◁ serialWedgeAssocBP x y z :=
  serialWedge_eqToHom_cons n (List.append_assoc x y z)

/-- The `List.append_nil` reindexing as a `BPSet` morphism. -/
def serialWedgeNilBP (x : List ℕ+) : ⋁(x ++ ([] : List ℕ+)) ⟶ ⋁x :=
  eqToHom (congrArg BPSet.serialWedge (List.append_nil x))

@[simp] theorem serialWedgeNilBP_hom (x : List ℕ+) :
    (serialWedgeNilBP x).hom = eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_nil x)) :=
  bpset_eqToHom_hom' _

theorem serialWedgeNilBP_cons (n : ℕ+) (x : List ℕ+) :
    serialWedgeNilBP (n :: x) = (□(n : ℕ)) ◁ serialWedgeNilBP x :=
  serialWedge_eqToHom_cons n (List.append_nil x)

/-- One inductive step of the associativity square, in an arbitrary monoidal category: given the
recursive square `ih`, the consed square is pentagon plus associator naturality. -/
private theorem append_assoc_step {M : Type*} [Category M] [MonoidalCategory M]
    {A B U D E P G : M} (f : B ⊗ U ⟶ E) (g : E ⊗ D ⟶ P) (h : U ⊗ D ⟶ G) (k : B ⊗ G ⟶ P)
    (ih : f ▷ D ≫ g = (α_ B U D).hom ≫ B ◁ h ≫ k) :
    ((α_ A B U).hom ≫ A ◁ f) ▷ D ≫ (α_ A E D).hom ≫ A ◁ g
      = (α_ (A ⊗ B) U D).hom ≫ (A ⊗ B) ◁ h ≫ (α_ A B G).hom ≫ A ◁ k := by
  rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp, ih]
  monoidal

/-- One inductive step of the right-unitality square: the triangle, whiskered. -/
private theorem append_right_unit_step {M : Type*} [Category M] [MonoidalCategory M]
    {A B P : M} (f : B ⊗ 𝟙_ M ⟶ P) (r : P ⟶ B) (ih : f ≫ r = (ρ_ B).hom) :
    ((α_ A B (𝟙_ M)).hom ≫ A ◁ f) ≫ A ◁ r = (ρ_ (A ⊗ B)).hom := by
  rw [Category.assoc, ← whiskerLeft_comp, ih]
  monoidal

/-! ### The coherence squares of the tensorator -/

/-- **Associativity of the tensorator**, in monoidal notation.  Induction on `x`: the base case
is a unitor coherence, each step is `append_assoc_step`. -/
theorem serialWedgeAppendIso_assoc : ∀ (x y z : List ℕ+),
    serialWedgeAppendHom x y ▷ (⋁z) ≫ serialWedgeAppendHom (x ++ y) z ≫ serialWedgeAssocBP x y z
      = (α_ (⋁x) (⋁y) (⋁z)).hom
        ≫ (⋁x) ◁ serialWedgeAppendHom y z ≫ serialWedgeAppendHom x (y ++ z)
  | [], y, z => by
      change (λ_ (⋁y)).hom ▷ (⋁z) ≫ serialWedgeAppendHom y z ≫ 𝟙 (⋁(y ++ z))
          = (α_ (𝟙_ BPSet) (⋁y) (⋁z)).hom
            ≫ (𝟙_ BPSet) ◁ serialWedgeAppendHom y z ≫ (λ_ (⋁(y ++ z))).hom
      simp only [Category.comp_id]
      monoidal
  | n :: x', y, z => by
      have ih := serialWedgeAppendIso_assoc x' y z
      rw [serialWedgeAssocBP_cons]
      change ((α_ (□(n : ℕ)) (⋁x') (⋁y)).hom ≫ (□(n : ℕ)) ◁ serialWedgeAppendHom x' y) ▷ (⋁z)
            ≫ ((α_ (□(n : ℕ)) (⋁(x' ++ y)) (⋁z)).hom
                ≫ (□(n : ℕ)) ◁ serialWedgeAppendHom (x' ++ y) z)
            ≫ (□(n : ℕ)) ◁ serialWedgeAssocBP x' y z
          = (α_ ((□(n : ℕ)) ⊗ (⋁x')) (⋁y) (⋁z)).hom
            ≫ ((□(n : ℕ)) ⊗ (⋁x')) ◁ serialWedgeAppendHom y z
            ≫ ((α_ (□(n : ℕ)) (⋁x') (⋁(y ++ z))).hom
                ≫ (□(n : ℕ)) ◁ serialWedgeAppendHom x' (y ++ z))
      rw [Category.assoc, ← whiskerLeft_comp]
      exact append_assoc_step _ _ _ _ ih

/-- **Right unitality of the tensorator**, in monoidal notation. -/
theorem serialWedgeAppendIso_right_unitality : ∀ x : List ℕ+,
    serialWedgeAppendHom x ([] : List ℕ+) ≫ serialWedgeNilBP x = (ρ_ (⋁x)).hom
  | [] => by
      change (λ_ (𝟙_ BPSet)).hom ≫ 𝟙 (𝟙_ BPSet) = (ρ_ (𝟙_ BPSet)).hom
      monoidal
  | n :: x' => by
      have ih := serialWedgeAppendIso_right_unitality x'
      rw [serialWedgeAppendHom_cons', serialWedgeNilBP_cons]
      exact append_right_unit_step _ _ ih

/-! ### The coherence squares at the presheaf level

The forms consumed by `serialWedgeFunctorCore`: each is its monoidal twin above with `.hom`
applied. -/

/-- The bare associativity square for `serialWedgeAppend`. -/
theorem serialWedgeAppend_assoc (x y z : List ℕ+) :
    wedge2MapPsh (serialWedgeAppendHom x y) (𝟙 (⋁z))
        ≫ (serialWedgeAppendHom (x ++ y) z).hom ≫ serialWedgeAssoc x y z
      = wedge2AssocFwd (⋁x) (⋁y) (⋁z)
        ≫ wedge2MapPsh (𝟙 (⋁x)) (serialWedgeAppendHom y z)
        ≫ (serialWedgeAppendHom x (y ++ z)).hom := by
  have h := congrArg BPSet.Hom.hom (serialWedgeAppendIso_assoc x y z)
  simpa only [comp_hom, whiskerRight_hom, whiskerLeft_hom, associator_hom_hom,
    serialWedgeAssocBP_hom] using h

/-! ### The unit squares of the tensorator (presheaf level) -/

/-- Left unitality of the tensorator. -/
theorem serialWedgeAppend_left_unitality (x : List ℕ+) :
    wedge2MapPsh (𝟙 (□0)) (𝟙 (⋁x)) ≫ (serialWedgeAppendHom [] x).hom ≫ 𝟙 (⋁x).toPsh
      = wedge2LeftUnitPsh (⋁x) := by
  rw [serialWedgeAppendHom_nil_left]
  have hid : wedge2MapPsh (𝟙 (□0)) (𝟙 (⋁x)) = 𝟙 (wedge2 (□0) (⋁x)).toPsh := by
    rw [← wedge2Map_hom, wedge2Map_id, id_hom]
  rw [hid]
  simp

/-- Right unitality of the tensorator (with the `append_nil` reindexing). -/
theorem serialWedgeAppend_right_unitality (x : List ℕ+) :
    wedge2MapPsh (𝟙 (⋁x)) (𝟙 (□0)) ≫ (serialWedgeAppendHom x []).hom
        ≫ eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_nil x))
      = wedge2RightUnitPsh (⋁x) := by
  have hid : wedge2MapPsh (𝟙 (⋁x)) (𝟙 (□0)) = 𝟙 (wedge2 (⋁x) (□0)).toPsh := by
    rw [← wedge2Map_hom, wedge2Map_id, id_hom]
  rw [hid, Category.id_comp]
  have h := congrArg BPSet.Hom.hom (serialWedgeAppendIso_right_unitality x)
  simpa only [comp_hom, serialWedgeNilBP_hom] using h

/-! ### The functor and its strong-monoidal structure -/

/-- The serial wedge as a functor from the free monoid on `ℕ+`. -/
def serialWedgeFunctor : DimList ⥤ BPSet :=
  Discrete.functor (fun l => ⋁ (FreeMonoid.toList l))

@[simp] theorem serialWedgeFunctor_obj (l : FreeMonoid ℕ+) :
    serialWedgeFunctor.obj (Discrete.mk l) = ⋁ (FreeMonoid.toList l) := rfl

/-- `serialWedgeFunctor` sends the discrete associator to the `serialWedge` reindexing. -/
theorem serialWedgeFunctor_map_associator (X Y Z : DimList) :
    (serialWedgeFunctor.map (α_ X Y Z).hom).hom = serialWedgeAssoc X.as Y.as Z.as := by
  have h : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) := Discrete.ext (Discrete.eq_of_hom (α_ X Y Z).hom)
  rw [Subsingleton.elim (α_ X Y Z).hom (eqToHom h), eqToHom_map, bpset_eqToHom_hom']
  rfl

/-- `serialWedgeFunctor` sends the discrete left unitor to the identity (the empty word is a
strict left unit for `++`). -/
theorem serialWedgeFunctor_map_leftUnitor (X : DimList) :
    (serialWedgeFunctor.map (λ_ X).hom).hom = 𝟙 (⋁ (FreeMonoid.toList X.as)).toPsh := by
  have h : 𝟙_ (DimList) ⊗ X = X := Discrete.ext (Discrete.eq_of_hom (λ_ X).hom)
  rw [Subsingleton.elim (λ_ X).hom (eqToHom h), eqToHom_map, bpset_eqToHom_hom']
  rfl

/-- `serialWedgeFunctor` sends the discrete right unitor to the `append_nil` reindexing. -/
theorem serialWedgeFunctor_map_rightUnitor (X : DimList) :
    (serialWedgeFunctor.map (ρ_ X).hom).hom
      = eqToHom (congrArg (fun l => (⋁l).toPsh) (List.append_nil X.as)) := by
  have h : X ⊗ 𝟙_ (DimList) = X := Discrete.ext (Discrete.eq_of_hom (ρ_ X).hom)
  rw [Subsingleton.elim (ρ_ X).hom (eqToHom h), eqToHom_map, bpset_eqToHom_hom']
  rfl

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
  associativity := fun X Y Z => by
    apply BPSet.hom_ext
    simp only [comp_hom]
    rw [serialWedgeFunctor_map_associator]
    exact serialWedgeAppend_assoc X.as Y.as Z.as
  left_unitality := fun X => by
    apply BPSet.hom_ext
    simp only [comp_hom, serialWedgeFunctor_map_leftUnitor]
    exact (serialWedgeAppend_left_unitality X.as).symm
  right_unitality := fun X => by
    apply BPSet.hom_ext
    simp only [comp_hom, serialWedgeFunctor_map_rightUnitor]
    exact (serialWedgeAppend_right_unitality X.as).symm

/-- The serial wedge is a strong monoidal functor `DimList ⥤ BPSet`. -/
instance : serialWedgeFunctor.Monoidal := serialWedgeFunctorCore.toMonoidal

@[simp] theorem serialWedgeFunctor_μ (X Y : DimList) :
    Functor.LaxMonoidal.μ serialWedgeFunctor X Y = serialWedgeAppendHom X.as Y.as := rfl

end ChainCat
