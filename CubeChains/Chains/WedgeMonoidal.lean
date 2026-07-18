import CubeChains.Chains.Segal
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Chains/WedgeMonoidal — the wedge `∨` as a monoidal structure on the alias `WedgeBP`

`(BPSet, wedge2, □0)` is monoidal: tensor `= wedge2`, unit `= □0`, associator/unitors from
`wedge2Assoc` / `wedge2LeftUnit` / `wedge2RightUnit`.  It is **not** registered on `BPSet` (which
has no canonical product); it lives on `def WedgeBP := BPSet`, mirroring `GeoBP` for the geometric
tensor.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet MonoidalCategory

namespace ChainCat

/-! ### `wedge2` as a bifunctor -/

/-- A bi-pointed map's underlying presheaf map carries the final vertex to the final vertex
(selector form of `app_final`). -/
theorem finalVertex_comp_hom {X Y : BPSet} (f : X ⟶ Y) :
    X.finalVertex ≫ f.hom = Y.finalVertex := by
  rw [show X.finalVertex = yonedaEquiv.symm X.final from rfl, yonedaEquiv_symm_naturality_right]
  exact congrArg yonedaEquiv.symm f.app_final

theorem initVertex_comp_hom {X Y : BPSet} (f : X ⟶ Y) :
    X.initVertex ≫ f.hom = Y.initVertex := by
  rw [show X.initVertex = yonedaEquiv.symm X.init from rfl, yonedaEquiv_symm_naturality_right]
  exact congrArg yonedaEquiv.symm f.app_init

/-- Underlying presheaf map of the bifunctor action `wedge2 X₁ Y₁ ⟶ wedge2 X₂ Y₂`. -/
def wedge2MapPsh {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (wedge2 X₁ Y₁).toPsh ⟶ (wedge2 X₂ Y₂).toPsh :=
  Glue.desc (f.hom ≫ Glue.inl X₂.finalVertex Y₂.initVertex)
    (g.hom ≫ Glue.inr X₂.finalVertex Y₂.initVertex)
    (by
      erw [← Category.assoc, ← Category.assoc, finalVertex_comp_hom f, initVertex_comp_hom g]
      exact Glue.condition X₂.finalVertex Y₂.initVertex)

/-- The bifunctor action of `wedge2` on morphisms. -/
def wedge2Map {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    wedge2 X₁ Y₁ ⟶ wedge2 X₂ Y₂ where
  hom := wedge2MapPsh f g
  app_init := @app_init_eq_of_initVertex (wedge2 X₁ Y₁) (wedge2 X₂ Y₂) (wedge2MapPsh f g) (by
    unfold wedge2MapPsh
    erw [wedge2_initVertex X₁ Y₁, Category.assoc, Glue.inl_desc, ← Category.assoc,
      initVertex_comp_hom f, ← wedge2_initVertex X₂ Y₂])
  app_final := @app_final_eq_of_finalVertex (wedge2 X₁ Y₁) (wedge2 X₂ Y₂) (wedge2MapPsh f g) (by
    unfold wedge2MapPsh
    erw [wedge2_finalVertex X₁ Y₁, Category.assoc, Glue.inr_desc, ← Category.assoc,
      finalVertex_comp_hom g, ← wedge2_finalVertex X₂ Y₂])

@[simp] theorem wedge2Map_hom {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (wedge2Map f g).hom = wedge2MapPsh f g := rfl

/-- Functoriality (identity): `wedge2Map (𝟙 X) (𝟙 Y) = 𝟙`. -/
theorem wedge2Map_id (X Y : BPSet) : wedge2Map (𝟙 X) (𝟙 Y) = 𝟙 (wedge2 X Y) := by
  apply BPSet.hom_ext
  rw [wedge2Map_hom, id_hom]
  unfold wedge2MapPsh
  refine Glue.hom_ext ?_ ?_
  · erw [Glue.inl_desc, id_hom, Category.id_comp]
  · erw [Glue.inr_desc, id_hom, Category.id_comp]

/-- Functoriality (composition). -/
theorem wedge2Map_comp {X₁ X₂ X₃ Y₁ Y₂ Y₃ : BPSet}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    wedge2Map (f₁ ≫ f₂) (g₁ ≫ g₂) = wedge2Map f₁ g₁ ≫ wedge2Map f₂ g₂ := by
  apply BPSet.hom_ext
  rw [comp_hom, wedge2Map_hom, wedge2Map_hom, wedge2Map_hom]
  unfold wedge2MapPsh
  refine Glue.hom_ext ?_ ?_
  · erw [Glue.inl_desc, Glue.inl_desc_assoc, Category.assoc, Category.assoc, Glue.inl_desc]
  · erw [Glue.inr_desc, Glue.inr_desc_assoc, Category.assoc, Category.assoc, Glue.inr_desc]

/-! ### Restriction lemmas — action of each underlying map on the pushout leaf inclusions

Each lemma peels one `Glue.desc`; tagged `@[reassoc]` so they fire under a trailing composition.
The coherence proofs below are then `Glue.hom_ext` (iterated) + `rw` with these. -/

@[reassoc]
theorem wedge2MapPsh_inl {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    Glue.inl X₁.finalVertex Y₁.initVertex ≫ wedge2MapPsh f g
      = f.hom ≫ Glue.inl X₂.finalVertex Y₂.initVertex := by
  unfold wedge2MapPsh; exact Glue.inl_desc _ _ _

@[reassoc]
theorem wedge2MapPsh_inr {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    Glue.inr X₁.finalVertex Y₁.initVertex ≫ wedge2MapPsh f g
      = g.hom ≫ Glue.inr X₂.finalVertex Y₂.initVertex := by
  unfold wedge2MapPsh; exact Glue.inr_desc _ _ _

@[reassoc]
theorem wedge2AssocFwd_inl_inl (a b c : BPSet) :
    Glue.inl a.finalVertex b.initVertex
        ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex ≫ wedge2AssocFwd a b c
      = Glue.inl a.finalVertex (wedge2 b c).initVertex := by
  unfold wedge2AssocFwd; erw [Glue.inl_desc, Glue.inl_desc]

@[reassoc]
theorem wedge2AssocFwd_inr_inl (a b c : BPSet) :
    Glue.inr a.finalVertex b.initVertex
        ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex ≫ wedge2AssocFwd a b c
      = Glue.inl b.finalVertex c.initVertex ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex := by
  unfold wedge2AssocFwd; erw [Glue.inl_desc, Glue.inr_desc]; rfl

@[reassoc]
theorem wedge2AssocFwd_inr (a b c : BPSet) :
    Glue.inr (wedge2 a b).finalVertex c.initVertex ≫ wedge2AssocFwd a b c
      = Glue.inr b.finalVertex c.initVertex ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex := by
  unfold wedge2AssocFwd; exact Glue.inr_desc _ _ _

@[reassoc]
theorem wedge2AssocBwd_inl (a b c : BPSet) :
    Glue.inl a.finalVertex (wedge2 b c).initVertex ≫ wedge2AssocBwd a b c
      = Glue.inl a.finalVertex b.initVertex ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex := by
  unfold wedge2AssocBwd; exact Glue.inl_desc _ _ _

@[reassoc]
theorem wedge2AssocBwd_inl_inr (a b c : BPSet) :
    Glue.inl b.finalVertex c.initVertex
        ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex ≫ wedge2AssocBwd a b c
      = Glue.inr a.finalVertex b.initVertex ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex := by
  unfold wedge2AssocBwd; erw [Glue.inr_desc, Glue.inl_desc]; rfl

@[reassoc]
theorem wedge2AssocBwd_inr_inr (a b c : BPSet) :
    Glue.inr b.finalVertex c.initVertex
        ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex ≫ wedge2AssocBwd a b c
      = Glue.inr (wedge2 a b).finalVertex c.initVertex := by
  unfold wedge2AssocBwd; erw [Glue.inr_desc, Glue.inr_desc]

@[reassoc]
theorem wedge2LeftUnitPsh_inl (X : BPSet) :
    Glue.inl (□0).finalVertex X.initVertex ≫ wedge2LeftUnitPsh X = X.initVertex := by
  unfold wedge2LeftUnitPsh; exact Glue.inl_desc _ _ _

@[reassoc]
theorem wedge2LeftUnitPsh_inr (X : BPSet) :
    Glue.inr (□0).finalVertex X.initVertex ≫ wedge2LeftUnitPsh X = 𝟙 X.toPsh := by
  unfold wedge2LeftUnitPsh; exact Glue.inr_desc _ _ _

@[reassoc]
theorem wedge2RightUnitPsh_inl (X : BPSet) :
    Glue.inl X.finalVertex (□0).initVertex ≫ wedge2RightUnitPsh X = 𝟙 X.toPsh := by
  unfold wedge2RightUnitPsh; exact Glue.inl_desc _ _ _

@[reassoc]
theorem wedge2RightUnitPsh_inr (X : BPSet) :
    Glue.inr X.finalVertex (□0).initVertex ≫ wedge2RightUnitPsh X = X.finalVertex := by
  unfold wedge2RightUnitPsh; exact Glue.inr_desc _ _ _

/-- Expose `.hom` of the bi-pointed associator/unitor maps for `rw`. -/
@[simp] theorem wedge2AssocHom_hom (a b c : BPSet) :
    (wedge2AssocHom a b c).hom = wedge2AssocFwd a b c := rfl

@[simp] theorem wedge2AssocInv_hom (a b c : BPSet) :
    (wedge2AssocInv a b c).hom = wedge2AssocBwd a b c := rfl

@[simp] theorem wedge2LeftUnit_hom_hom (X : BPSet) :
    (wedge2LeftUnit X).hom.hom = wedge2LeftUnitPsh X := rfl

@[simp] theorem wedge2RightUnit_hom_hom (X : BPSet) :
    (wedge2RightUnit X).hom.hom = wedge2RightUnitPsh X := rfl

/-! ### Coherence lemmas for the wedge tensor

The underlying maps are sealed `irreducible` here so `erw` matches the restriction lemmas
syntactically (unfolding the nested `Glue.desc` towers during unification blows up). Reassoc
lemmas whose base RHS is itself a composition (`f.hom ≫ inl`, `inl ≫ inr`, …) leave a
left-associated `(a ≫ b) ≫ h`, repaired by a following `Category.assoc`. -/

attribute [local irreducible] wedge2MapPsh wedge2AssocFwd wedge2AssocBwd
  wedge2LeftUnitPsh wedge2RightUnitPsh

set_option maxHeartbeats 800000 in
-- Three leaves, each an `erw` chain over the sealed wedge maps; defeq matching is heavy.
/-- Associator naturality. -/
theorem wedge2Assoc_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : BPSet}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    wedge2Map (wedge2Map f₁ f₂) f₃ ≫ wedge2AssocHom Y₁ Y₂ Y₃
      = wedge2AssocHom X₁ X₂ X₃ ≫ wedge2Map f₁ (wedge2Map f₂ f₃) := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2Map_hom, wedge2AssocHom_hom, wedge2AssocHom_hom]
  refine Glue.hom_ext (Glue.hom_ext ?_ ?_) ?_
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [wedge2Map_hom]
    erw [wedge2MapPsh_inl_assoc, Category.assoc, wedge2AssocFwd_inl_inl,
      wedge2AssocFwd_inl_inl_assoc, wedge2MapPsh_inl]
    rfl
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [wedge2Map_hom]
    erw [wedge2MapPsh_inr_assoc, Category.assoc, wedge2AssocFwd_inr_inl,
      wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2MapPsh_inr]
    rw [wedge2Map_hom]
    erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rfl
  · erw [wedge2MapPsh_inr_assoc, Category.assoc, wedge2AssocFwd_inr, wedge2AssocFwd_inr_assoc,
      Category.assoc, wedge2MapPsh_inr]
    rw [wedge2Map_hom]
    erw [wedge2MapPsh_inr_assoc, Category.assoc]
    rfl

/-- Left-unitor naturality. -/
theorem wedge2LeftUnit_naturality {X Y : BPSet} (f : X ⟶ Y) :
    wedge2Map (𝟙 (□0)) f ≫ (wedge2LeftUnit Y).hom = (wedge2LeftUnit X).hom ≫ f := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2LeftUnit_hom_hom, wedge2LeftUnit_hom_hom]
  refine Glue.hom_ext ?_ ?_
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [id_hom]
    erw [wedge2LeftUnitPsh_inl, wedge2LeftUnitPsh_inl_assoc, initVertex_comp_hom]
  · erw [wedge2MapPsh_inr_assoc, Category.assoc, wedge2LeftUnitPsh_inr, wedge2LeftUnitPsh_inr_assoc,
      Category.comp_id]

/-- Right-unitor naturality. -/
theorem wedge2RightUnit_naturality {X Y : BPSet} (f : X ⟶ Y) :
    wedge2Map f (𝟙 (□0)) ≫ (wedge2RightUnit Y).hom = (wedge2RightUnit X).hom ≫ f := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2RightUnit_hom_hom, wedge2RightUnit_hom_hom]
  refine Glue.hom_ext ?_ ?_
  · erw [wedge2MapPsh_inl_assoc, Category.assoc, wedge2RightUnitPsh_inl,
      wedge2RightUnitPsh_inl_assoc, Category.comp_id]
  · erw [wedge2MapPsh_inr_assoc, Category.assoc]
    rw [id_hom]
    erw [wedge2RightUnitPsh_inr, wedge2RightUnitPsh_inr_assoc, finalVertex_comp_hom]

/-- Triangle identity. -/
theorem wedge2_triangle (X Y : BPSet) :
    wedge2AssocHom X (□0) Y ≫ wedge2Map (𝟙 X) (wedge2LeftUnit Y).hom
      = wedge2Map (wedge2RightUnit X).hom (𝟙 Y) := by
  apply BPSet.hom_ext
  rw [comp_hom, wedge2AssocHom_hom, wedge2Map_hom, wedge2Map_hom]
  refine Glue.hom_ext (Glue.hom_ext ?_ ?_) ?_
  · erw [wedge2AssocFwd_inl_inl_assoc, wedge2MapPsh_inl]
    rw [id_hom]
    erw [wedge2MapPsh_inl]
    rw [wedge2RightUnit_hom_hom]
    erw [wedge2RightUnitPsh_inl_assoc, Category.id_comp]
  · erw [wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2MapPsh_inr]
    rw [wedge2LeftUnit_hom_hom]
    erw [wedge2LeftUnitPsh_inl_assoc, wedge2MapPsh_inl]
    rw [wedge2RightUnit_hom_hom]
    erw [wedge2RightUnitPsh_inr_assoc]
    exact (Glue.condition X.finalVertex Y.initVertex).symm
  · erw [wedge2AssocFwd_inr_assoc, Category.assoc, wedge2MapPsh_inr]
    rw [wedge2LeftUnit_hom_hom]
    erw [wedge2LeftUnitPsh_inr_assoc, wedge2MapPsh_inr]
    rw [id_hom]
    erw [Category.id_comp]

-- Seal the vertex selectors too: `erw`'s defeq matching otherwise `whnf`s the `finalVertex`/
-- `initVertex` towers of the nested wedges, which dominates the (already heavy) pentagon chase.
attribute [local irreducible] BPSet.finalVertex BPSet.initVertex

set_option maxHeartbeats 1600000 in
-- Four leaves (W/X/Y/Z), each a long `erw` chain over the sealed wedge maps; defeq matching is
-- heavy, and all four share one declaration's heartbeat budget.
theorem wedge2_pentagon (W X Y Z : BPSet) :
    wedge2Map (wedge2AssocHom W X Y) (𝟙 Z) ≫ wedge2AssocHom W (wedge2 X Y) Z
        ≫ wedge2Map (𝟙 W) (wedge2AssocHom X Y Z)
      = wedge2AssocHom (wedge2 W X) Y Z ≫ wedge2AssocHom W X (wedge2 Y Z) := by
  apply BPSet.hom_ext
  simp only [comp_hom, wedge2Map_hom, wedge2AssocHom_hom]
  refine Glue.hom_ext (Glue.hom_ext (Glue.hom_ext ?_ ?_) ?_) ?_
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inl_inl_assoc, wedge2AssocFwd_inl_inl_assoc, wedge2MapPsh_inl,
      wedge2AssocFwd_inl_inl_assoc, wedge2AssocFwd_inl_inl]
    rfl
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2AssocFwd_inr_inl_assoc,
      Category.assoc, wedge2MapPsh_inr]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inl_inl_assoc, wedge2AssocFwd_inl_inl_assoc, wedge2AssocFwd_inr_inl]
    rfl
  · erw [wedge2MapPsh_inl_assoc, Category.assoc]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inr_assoc, Category.assoc, wedge2AssocFwd_inr_inl_assoc, Category.assoc,
      wedge2MapPsh_inr]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2AssocFwd_inr_inl_assoc,
      Category.assoc, wedge2AssocFwd_inr]
    rfl
  · erw [wedge2MapPsh_inr_assoc, Category.assoc, wedge2AssocFwd_inr_assoc, Category.assoc,
      wedge2MapPsh_inr]
    rw [wedge2AssocHom_hom]
    erw [wedge2AssocFwd_inr_assoc, Category.assoc, wedge2AssocFwd_inr_assoc, Category.assoc,
      wedge2AssocFwd_inr]
    rfl

/-! ### The monoidal structure, on the alias `WedgeBP` -/

/-- The wedge monoidal structure, as a plain `def` on `BPSet` (not an `instance`: `BPSet` carries
no canonical product — see `WedgeBP`). -/
@[reducible] noncomputable def wedgeMonoidalStruct : MonoidalCategoryStruct BPSet where
  tensorObj := wedge2
  tensorHom := wedge2Map
  whiskerLeft X _ _ g := wedge2Map (𝟙 X) g
  whiskerRight f Y := wedge2Map f (𝟙 Y)
  tensorUnit := □0
  associator := wedge2Assoc
  leftUnitor := wedge2LeftUnit
  rightUnitor := wedge2RightUnit

/-- The wedge `MonoidalCategory` data on `BPSet`, as a plain `def` (see `WedgeBP`). -/
@[reducible] noncomputable def wedgeMonoidal : MonoidalCategory BPSet :=
  letI := wedgeMonoidalStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := wedge2Map_id)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => (wedge2Map_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := fun f₁ f₂ f₃ => wedge2Assoc_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => wedge2LeftUnit_naturality f)
    (rightUnitor_naturality := fun f => wedge2RightUnit_naturality f)
    (pentagon := wedge2_pentagon)
    (triangle := wedge2_triangle)

end ChainCat

/-- `BPSet` carrying the wedge `∨` (serial gluing) as its monoidal product.  `BPSet` has no
canonical product (the geometric `⊛` and the topos cartesian product are equally natural), so
each lives on its own alias — this one, and `GeoBP` for the geometric tensor. -/
def WedgeBP := BPSet

instance : Category WedgeBP := inferInstanceAs (Category BPSet)

noncomputable instance : MonoidalCategory WedgeBP := ChainCat.wedgeMonoidal
