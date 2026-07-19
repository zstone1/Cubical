import CubeChains.Foundations.Wedge
import CubeChains.Foundations.GluePushout
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Foundations/WedgeMonoidal

The wedge `∨` as the **default** `MonoidalCategory BPSet`: tensor `= wedge2`, unit `= □0`,
associator/unitors from `wedge2Assoc` / `wedge2LeftUnit` / `wedge2RightUnit`, all built directly
from the pushout `Glue`.  The geometric tensor `⊗ᵍ` keeps its own alias `GeoBP`; `WedgeBP := BPSet`
survives only as a compat alias.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet MonoidalCategory

namespace ChainCat

/-- The initial-vertex *map* of `X ∨ Y` factors through the left inclusion. -/
theorem wedge2_initVertex (X Y : BPSet) :
    (wedge2 X Y).initVertex
      = X.initVertex ≫ Glue.inl X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (wedge2 X Y).initVertex
    = yonedaEquiv.symm ((wedge2 X Y).init) from rfl,
    show (wedge2 X Y).init = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.init from rfl]
  exact (yonedaEquiv_symm_naturality_right ▫0
    (Glue.inl X.finalVertex Y.initVertex) X.init).symm

/-- The final-vertex *map* of `X ∨ Y` factors through the right inclusion. -/
theorem wedge2_finalVertex (X Y : BPSet) :
    (wedge2 X Y).finalVertex
      = Y.finalVertex ≫ Glue.inr X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (wedge2 X Y).finalVertex
    = yonedaEquiv.symm ((wedge2 X Y).final) from rfl,
    show (wedge2 X Y).final = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.final from rfl]
  exact (yonedaEquiv_symm_naturality_right ▫0
    (Glue.inr X.finalVertex Y.initVertex) Y.final).symm

/-- The basepoint condition `e.app K.init = L.init` in vertex-map form: it is
equivalent to `K.initVertex ≫ e = L.initVertex` (Yoneda naturality). -/
theorem app_init_eq_of_initVertex {K L : BPSet} (e : K.toPsh ⟶ L.toPsh)
    (h : K.initVertex ≫ e = L.initVertex) : e⟪0⟫ K.init = L.init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (e⟪0⟫ K.init) = K.initVertex ≫ e from
    (yonedaEquiv_symm_naturality_right ▫0 e K.init).symm]
  exact h

theorem app_final_eq_of_finalVertex {K L : BPSet} (e : K.toPsh ⟶ L.toPsh)
    (h : K.finalVertex ≫ e = L.finalVertex) : e⟪0⟫ K.final = L.final := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (e⟪0⟫ K.final) = K.finalVertex ≫ e from
    (yonedaEquiv_symm_naturality_right ▫0 e K.final).symm]
  exact h

/-! ### Associativity of the wedge `(a ∨ b) ∨ c ≅ a ∨ (b ∨ c)`

Both sides are the triple wedge `a ∨ b ∨ c` (glue `a.final~b.init`, `b.final~c.init`) as an
iterated pushout; the associator is the canonical comparison.  Everything reduces to the pushout
`Glue.condition` and the vertex-selector lemmas `wedge2_initVertex`/`wedge2_finalVertex`. -/

/-- Underlying presheaf map of the forward associator. -/
def wedge2AssocFwd (a b c : BPSet) :
    (wedge2 (wedge2 a b) c).toPsh ⟶ (wedge2 a (wedge2 b c)).toPsh :=
  Glue.desc
    (Glue.desc (Glue.inl a.finalVertex (wedge2 b c).initVertex)
      (Glue.inl b.finalVertex c.initVertex ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex)
      (by erw [Glue.condition a.finalVertex (wedge2 b c).initVertex, ← Category.assoc,
        ← wedge2_initVertex b c]; rfl))
    (Glue.inr b.finalVertex c.initVertex ≫ Glue.inr a.finalVertex (wedge2 b c).initVertex)
    (by erw [wedge2_finalVertex a b, Category.assoc, Glue.inr_desc,
      reassoc_of% Glue.condition b.finalVertex c.initVertex])

theorem wedge2AssocFwd_initVertex (a b c : BPSet) :
    (wedge2 (wedge2 a b) c).initVertex ≫ wedge2AssocFwd a b c
      = (wedge2 a (wedge2 b c)).initVertex := by
  unfold wedge2AssocFwd
  erw [wedge2_initVertex (wedge2 a b) c, Category.assoc, Glue.inl_desc, wedge2_initVertex a b,
    Category.assoc, Glue.inl_desc, ← wedge2_initVertex a (wedge2 b c)]

theorem wedge2AssocFwd_finalVertex (a b c : BPSet) :
    (wedge2 (wedge2 a b) c).finalVertex ≫ wedge2AssocFwd a b c
      = (wedge2 a (wedge2 b c)).finalVertex := by
  unfold wedge2AssocFwd
  erw [wedge2_finalVertex (wedge2 a b) c, Category.assoc, Glue.inr_desc,
    wedge2_finalVertex a (wedge2 b c), wedge2_finalVertex b c, ← Category.assoc]

/-- Underlying presheaf map of the inverse associator. -/
def wedge2AssocBwd (a b c : BPSet) :
    (wedge2 a (wedge2 b c)).toPsh ⟶ (wedge2 (wedge2 a b) c).toPsh :=
  Glue.desc
    (Glue.inl a.finalVertex b.initVertex ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex)
    (Glue.desc
      (Glue.inr a.finalVertex b.initVertex ≫ Glue.inl (wedge2 a b).finalVertex c.initVertex)
      (Glue.inr (wedge2 a b).finalVertex c.initVertex)
      (by erw [← Category.assoc, ← wedge2_finalVertex a b,
        Glue.condition (wedge2 a b).finalVertex c.initVertex]; rfl))
    (by erw [← Category.assoc, Glue.condition a.finalVertex b.initVertex, Category.assoc,
      wedge2_initVertex b c, Category.assoc, Glue.inl_desc])

theorem wedge2AssocBwd_initVertex (a b c : BPSet) :
    (wedge2 a (wedge2 b c)).initVertex ≫ wedge2AssocBwd a b c
      = (wedge2 (wedge2 a b) c).initVertex := by
  unfold wedge2AssocBwd
  erw [wedge2_initVertex a (wedge2 b c), Category.assoc, Glue.inl_desc, ← Category.assoc,
    ← wedge2_initVertex a b, ← wedge2_initVertex (wedge2 a b) c]

theorem wedge2AssocBwd_finalVertex (a b c : BPSet) :
    (wedge2 a (wedge2 b c)).finalVertex ≫ wedge2AssocBwd a b c
      = (wedge2 (wedge2 a b) c).finalVertex := by
  unfold wedge2AssocBwd
  erw [wedge2_finalVertex a (wedge2 b c), Category.assoc, Glue.inr_desc, wedge2_finalVertex b c,
    Category.assoc, Glue.inr_desc, ← wedge2_finalVertex (wedge2 a b) c]

theorem wedge2AssocFwd_bwd (a b c : BPSet) :
    wedge2AssocFwd a b c ≫ wedge2AssocBwd a b c
      = 𝟙 (wedge2 (wedge2 a b) c).toPsh := by
  unfold wedge2AssocFwd wedge2AssocBwd
  refine Glue.hom_ext (Glue.hom_ext ?_ ?_) ?_
  · erw [Glue.inl_desc_assoc, Glue.inl_desc_assoc, Glue.inl_desc, Category.comp_id]
  · erw [Glue.inl_desc_assoc, Glue.inr_desc_assoc, Category.assoc, Glue.inr_desc, Glue.inl_desc,
      Category.comp_id]
  · erw [Glue.inr_desc_assoc, Category.assoc, Glue.inr_desc, Glue.inr_desc, Category.comp_id]

theorem wedge2AssocBwd_fwd (a b c : BPSet) :
    wedge2AssocBwd a b c ≫ wedge2AssocFwd a b c
      = 𝟙 (wedge2 a (wedge2 b c)).toPsh := by
  unfold wedge2AssocFwd wedge2AssocBwd
  refine Glue.hom_ext ?_ (Glue.hom_ext ?_ ?_)
  · erw [Glue.inl_desc_assoc, Category.assoc, Glue.inl_desc, Glue.inl_desc, Category.comp_id]
  · erw [Glue.inr_desc_assoc, Glue.inl_desc_assoc, Category.assoc, Glue.inl_desc, Glue.inr_desc,
      Category.comp_id]
  · erw [Glue.inr_desc_assoc, Glue.inr_desc_assoc, Glue.inr_desc, Category.comp_id]

/-- The forward associator as a bi-pointed morphism. -/
def wedge2AssocHom (a b c : BPSet) : wedge2 (wedge2 a b) c ⟶ wedge2 a (wedge2 b c) where
  hom := wedge2AssocFwd a b c
  app_init := app_init_eq_of_initVertex _ (wedge2AssocFwd_initVertex a b c)
  app_final := app_final_eq_of_finalVertex _ (wedge2AssocFwd_finalVertex a b c)

/-- The inverse associator as a bi-pointed morphism. -/
def wedge2AssocInv (a b c : BPSet) : wedge2 a (wedge2 b c) ⟶ wedge2 (wedge2 a b) c where
  hom := wedge2AssocBwd a b c
  app_init := app_init_eq_of_initVertex _ (wedge2AssocBwd_initVertex a b c)
  app_final := app_final_eq_of_finalVertex _ (wedge2AssocBwd_finalVertex a b c)

/-- **Associativity of the wedge.** `(a ∨ b) ∨ c ≅ a ∨ (b ∨ c)`. -/
def wedge2Assoc (a b c : BPSet) : wedge2 (wedge2 a b) c ≅ wedge2 a (wedge2 b c) where
  hom := wedge2AssocHom a b c
  inv := wedge2AssocInv a b c
  hom_inv_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    exact wedge2AssocFwd_bwd a b c
  inv_hom_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    exact wedge2AssocBwd_fwd a b c

/-! ### The collapse helpers for the point `cube 0`

These vertex-identity and `IsIso` facts about the point `□⁰` feed the concatenation
functor and the `cube 0` unit equivalence below. -/

/-- The point `□⁰` is rigid: `stdPre 0` has only the identity endomorphism. -/
instance stdPre0_subsingleton : Subsingleton (StdCube.stdPre 0 ⟶ StdCube.stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [StdCube.noneSet])

instance : Subsingleton ((□0).cells 0) := stdPre0_subsingleton

/-- The initial-vertex inclusion of the point `cube 0` is the identity. -/
@[simp] theorem cube0_initVertex_eq_id :
    (□0).initVertex = 𝟙 (yoneda.obj ▫0) := by
  rw [initVertex, vertexMap, PrecubicalSet.cubeMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((□0).initVertex) := by
  rw [cube0_initVertex_eq_id]; exact IsIso.id _

/-- The final-vertex inclusion of the point `cube 0` is the identity. -/
@[simp] theorem cube0_finalVertex_eq_id :
    (□0).finalVertex = 𝟙 (yoneda.obj ▫0) := by
  rw [finalVertex, vertexMap, PrecubicalSet.cubeMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((□0).finalVertex) := by
  rw [cube0_finalVertex_eq_id]; exact IsIso.id _

/-- Prepending the point `cube 0` to a wedge collapses: the right inclusion
`X ⟶ wedge2 (cube 0) X` is an iso. -/
instance wedge2_cube0_inr_isIso (X : BPSet) :
    IsIso (Glue.inr (□0).finalVertex X.initVertex) :=
  (Glue.isPushout _ _).isIso_inr_of_isIso

/-- Appending the point `cube 0` on the right collapses: the left inclusion
`X ⟶ wedge2 X (cube 0)` is an iso. -/
instance wedge2_cube0_inl_isIso (X : BPSet) :
    IsIso (Glue.inl X.finalVertex (□0).initVertex) :=
  (Glue.isPushout _ _).isIso_inl_of_isIso

/-! ### The point `cube 0` is the unit for the wedge

`cube 0 ∨ X ≅ X` and `X ∨ cube 0 ≅ X` — genuine isos (the wedge is a pushout, not a strict
unit).  The collapsing inclusion is the `IsIso` above; here we package the two-sided iso. -/

/-- `(□0).finalVertex` acts as an identity on the left (it *is* `𝟙`, but stated in `≫`-form so
it rewrites cleanly even when the cofactor's index mentions `(□0).finalVertex`). -/
theorem cube0_finalVertex_comp {A : PrecubicalSet} (f : (□0).toPsh ⟶ A) :
    (□0).finalVertex ≫ f = f := by rw [cube0_finalVertex_eq_id]; exact Category.id_comp f

theorem cube0_initVertex_comp {A : PrecubicalSet} (f : (□0).toPsh ⟶ A) :
    (□0).initVertex ≫ f = f := by rw [cube0_initVertex_eq_id]; exact Category.id_comp f

/-- At the collapsing junction of `cube 0 ∨ X`, the right inclusion of `X.init` is the left. -/
theorem wedge2_cube0_inr_eq_inl (X : BPSet) :
    X.initVertex ≫ Glue.inr (□0).finalVertex X.initVertex
      = Glue.inl (□0).finalVertex X.initVertex := by
  rw [← Glue.condition (□0).finalVertex X.initVertex, cube0_finalVertex_comp]

/-- At the collapsing junction of `X ∨ cube 0`, the left inclusion of `X.final` is the right. -/
theorem wedge2_cube0_inl_eq_inr (X : BPSet) :
    X.finalVertex ≫ Glue.inl X.finalVertex (□0).initVertex
      = Glue.inr X.finalVertex (□0).initVertex := by
  rw [Glue.condition X.finalVertex (□0).initVertex, cube0_initVertex_comp]

/-- Underlying map of the left-unit iso `cube 0 ∨ X ⟶ X`. -/
def wedge2LeftUnitPsh (X : BPSet) : (wedge2 (□0) X).toPsh ⟶ X.toPsh :=
  Glue.desc X.initVertex (𝟙 X.toPsh) (by rw [cube0_finalVertex_comp, Category.comp_id])

theorem wedge2LeftUnitPsh_initVertex (X : BPSet) :
    (wedge2 (□0) X).initVertex ≫ wedge2LeftUnitPsh X = X.initVertex := by
  unfold wedge2LeftUnitPsh
  erw [wedge2_initVertex (□0) X, Category.assoc, Glue.inl_desc, cube0_initVertex_comp]

theorem wedge2LeftUnitPsh_finalVertex (X : BPSet) :
    (wedge2 (□0) X).finalVertex ≫ wedge2LeftUnitPsh X = X.finalVertex := by
  unfold wedge2LeftUnitPsh
  erw [wedge2_finalVertex (□0) X, Category.assoc, Glue.inr_desc, Category.comp_id]

/-- **Left unit.** `cube 0 ∨ X ≅ X`. -/
def wedge2LeftUnit (X : BPSet) : wedge2 (□0) X ≅ X where
  hom :=
    { hom := wedge2LeftUnitPsh X
      app_init := app_init_eq_of_initVertex _ (wedge2LeftUnitPsh_initVertex X)
      app_final := app_final_eq_of_finalVertex _ (wedge2LeftUnitPsh_finalVertex X) }
  inv :=
    { hom := Glue.inr (□0).finalVertex X.initVertex
      app_init := @app_init_eq_of_initVertex X (wedge2 (□0) X)
        (Glue.inr (□0).finalVertex X.initVertex) (by
          rw [wedge2_initVertex (□0) X, cube0_initVertex_comp]; exact wedge2_cube0_inr_eq_inl X)
      app_final := @app_final_eq_of_finalVertex X (wedge2 (□0) X)
        (Glue.inr (□0).finalVertex X.initVertex) (wedge2_finalVertex (□0) X).symm }
  hom_inv_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    unfold wedge2LeftUnitPsh
    refine Glue.hom_ext ?_ ?_
    · erw [Glue.inl_desc_assoc, Category.comp_id]; exact wedge2_cube0_inr_eq_inl X
    · erw [Glue.inr_desc_assoc]; rfl
  inv_hom_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    unfold wedge2LeftUnitPsh
    exact Glue.inr_desc _ _ _

/-- Underlying map of the right-unit iso `X ∨ cube 0 ⟶ X`. -/
def wedge2RightUnitPsh (X : BPSet) : (wedge2 X (□0)).toPsh ⟶ X.toPsh :=
  Glue.desc (𝟙 X.toPsh) X.finalVertex (by rw [cube0_initVertex_comp, Category.comp_id])

theorem wedge2RightUnitPsh_initVertex (X : BPSet) :
    (wedge2 X (□0)).initVertex ≫ wedge2RightUnitPsh X = X.initVertex := by
  unfold wedge2RightUnitPsh
  erw [wedge2_initVertex X (□0), Category.assoc, Glue.inl_desc, Category.comp_id]

theorem wedge2RightUnitPsh_finalVertex (X : BPSet) :
    (wedge2 X (□0)).finalVertex ≫ wedge2RightUnitPsh X = X.finalVertex := by
  unfold wedge2RightUnitPsh
  erw [wedge2_finalVertex X (□0), Category.assoc, Glue.inr_desc, cube0_finalVertex_comp]

/-- **Right unit.** `X ∨ cube 0 ≅ X`. -/
def wedge2RightUnit (X : BPSet) : wedge2 X (□0) ≅ X where
  hom :=
    { hom := wedge2RightUnitPsh X
      app_init := app_init_eq_of_initVertex _ (wedge2RightUnitPsh_initVertex X)
      app_final := app_final_eq_of_finalVertex _ (wedge2RightUnitPsh_finalVertex X) }
  inv :=
    { hom := Glue.inl X.finalVertex (□0).initVertex
      app_init := @app_init_eq_of_initVertex X (wedge2 X (□0))
        (Glue.inl X.finalVertex (□0).initVertex) (wedge2_initVertex X (□0)).symm
      app_final := @app_final_eq_of_finalVertex X (wedge2 X (□0))
        (Glue.inl X.finalVertex (□0).initVertex) (by
          rw [wedge2_finalVertex X (□0), cube0_finalVertex_comp]; exact wedge2_cube0_inl_eq_inr X) }
  hom_inv_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    unfold wedge2RightUnitPsh
    refine Glue.hom_ext ?_ ?_
    · erw [Glue.inl_desc_assoc]; rfl
    · erw [Glue.inr_desc_assoc, Category.comp_id]; exact wedge2_cube0_inl_eq_inr X
  inv_hom_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    unfold wedge2RightUnitPsh
    exact Glue.inl_desc _ _ _

/-! ### The wedge on morphisms -/

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

/-! ### The wedge bifunctor -/

/-- The wedge as a bifunctor `BPSet × BPSet ⥤ BPSet` — the designated "wedge of morphisms".  Its
action is `wedge2Map`, which the `MonoidalCategoryStruct` below still refers to directly. -/
def wedgeFunctor : BPSet × BPSet ⥤ BPSet where
  obj p := wedge2 p.1 p.2
  map fg := wedge2Map fg.1 fg.2
  map_id p := wedge2Map_id p.1 p.2
  map_comp fg hk := wedge2Map_comp fg.1 hk.1 fg.2 hk.2

@[simp] theorem wedgeFunctor_obj (p : BPSet × BPSet) : wedgeFunctor.obj p = wedge2 p.1 p.2 := rfl

@[simp] theorem wedgeFunctor_map {p q : BPSet × BPSet} (fg : p ⟶ q) :
    wedgeFunctor.map fg = wedge2Map fg.1 fg.2 := rfl

/-- Whisker an iso through each side of `wedge2` (functoriality of `wedge2Map`). -/
def wedge2MapIso {X₁ X₂ Y₁ Y₂ : BPSet} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂) :
    wedge2 X₁ Y₁ ≅ wedge2 X₂ Y₂ where
  hom := wedge2Map e.hom e'.hom
  inv := wedge2Map e.inv e'.inv
  hom_inv_id :=
    calc wedge2Map e.hom e'.hom ≫ wedge2Map e.inv e'.inv
        = wedge2Map (e.hom ≫ e.inv) (e'.hom ≫ e'.inv) := (wedge2Map_comp _ _ _ _).symm
      _ = wedge2Map (𝟙 _) (𝟙 _)                       := by rw [e.hom_inv_id, e'.hom_inv_id]
      _ = 𝟙 (wedge2 _ _)                               := wedge2Map_id _ _
  inv_hom_id :=
    calc wedge2Map e.inv e'.inv ≫ wedge2Map e.hom e'.hom
        = wedge2Map (e.inv ≫ e.hom) (e'.inv ≫ e'.hom) := (wedge2Map_comp _ _ _ _).symm
      _ = wedge2Map (𝟙 _) (𝟙 _)                       := by rw [e.inv_hom_id, e'.inv_hom_id]
      _ = 𝟙 (wedge2 _ _)                               := wedge2Map_id _ _

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

/-! ### Components of the associator and unitors -/

/-- Expose `.hom` of the bi-pointed associator/unitor maps for `rw`. -/
@[simp] theorem wedge2AssocHom_hom (a b c : BPSet) :
    (wedge2AssocHom a b c).hom = wedge2AssocFwd a b c := rfl

@[simp] theorem wedge2AssocInv_hom (a b c : BPSet) :
    (wedge2AssocInv a b c).hom = wedge2AssocBwd a b c := rfl

@[simp] theorem wedge2LeftUnit_hom_hom (X : BPSet) :
    (wedge2LeftUnit X).hom.hom = wedge2LeftUnitPsh X := rfl

@[simp] theorem wedge2RightUnit_hom_hom (X : BPSet) :
    (wedge2RightUnit X).hom.hom = wedge2RightUnitPsh X := rfl

/-! ### Associativity and unit laws (naturality)

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

/-! ### Coherence: pentagon and triangle -/

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
@[reducible] def wedgeMonoidalStruct : MonoidalCategoryStruct BPSet where
  tensorObj := wedge2
  tensorHom := wedge2Map
  whiskerLeft X _ _ g := wedge2Map (𝟙 X) g
  whiskerRight f Y := wedge2Map f (𝟙 Y)
  tensorUnit := □0
  associator := wedge2Assoc
  leftUnitor := wedge2LeftUnit
  rightUnitor := wedge2RightUnit

/-- The wedge `MonoidalCategory` data on `BPSet`, as a plain `def` (see `WedgeBP`). -/
@[reducible] def wedgeMonoidal : MonoidalCategory BPSet :=
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

/-- The wedge `∨` (serial gluing) is the default monoidal product on `BPSet`.  The geometric tensor
`⊗ᵍ` lives on its own alias `GeoBP`, and the topos cartesian product on another. -/
instance : MonoidalCategory BPSet := ChainCat.wedgeMonoidal

/-- Alias for `BPSet` under its wedge tensor; the `MonoidalCategory BPSet` instance above is the
same structure, so prefer `BPSet` directly. -/
def WedgeBP := BPSet

instance : Category WedgeBP := inferInstanceAs (Category BPSet)

instance : MonoidalCategory WedgeBP := ChainCat.wedgeMonoidal
