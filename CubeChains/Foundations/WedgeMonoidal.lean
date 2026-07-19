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

/-! ### The wedge's pushout API, typed by the wedge

`Glue` spells the wedge's presheaf `Glue.gluePsh X.finalVertex Y.initVertex`; `wedge2` spells it
`(X ∨ Y).toPsh`.  The two are `rfl`, but `wedge2` is a plain `def`, and `rw` keyed-matches at
`.instances` transparency, which will not unfold it.  Since `CategoryStruct.comp` takes its object
arguments from the *factors*, one `Glue`-spelled inclusion poisons the whole composite: a goal
printing as `(f ≫ g) ≫ h` then refuses `Category.assoc`, because the inner composite's codomain is
`Glue.gluePsh …` where the outer expects `(X ∨ Y).toPsh`.  That, not any instance mismatch, is
what used to force `erw` here.

These wrappers pin the wedge's spelling for every map into and out of `X ∨ Y`, so `rw`/`simp`
match syntactically and never need to unfold anything. -/

/-- The left leaf `X ⟶ X ∨ Y`, typed by the wedge. -/
abbrev wedgeInl (X Y : BPSet) : X.toPsh ⟶ (X ∨ Y).toPsh := Glue.inl X.finalVertex Y.initVertex

/-- The right leaf `Y ⟶ X ∨ Y`, typed by the wedge. -/
abbrev wedgeInr (X Y : BPSet) : Y.toPsh ⟶ (X ∨ Y).toPsh := Glue.inr X.finalVertex Y.initVertex

/-- Maps out of the wedge: `X ∨ Y ⟶ W` from a pair agreeing at the glued vertex. -/
def wedge2Desc {X Y : BPSet} {W : PrecubicalSet} (h : X.toPsh ⟶ W) (k : Y.toPsh ⟶ W)
    (w : X.finalVertex ≫ h = Y.initVertex ≫ k) : (X ∨ Y).toPsh ⟶ W := Glue.desc h k w

/-- The gluing square of `X ∨ Y`. -/
theorem wedge2_condition (X Y : BPSet) :
    X.finalVertex ≫ wedgeInl X Y = Y.initVertex ≫ wedgeInr X Y := Glue.condition _ _

@[reassoc (attr := simp)]
theorem wedge2Desc_inl {X Y : BPSet} {W : PrecubicalSet} (h : X.toPsh ⟶ W) (k : Y.toPsh ⟶ W)
    (w : X.finalVertex ≫ h = Y.initVertex ≫ k) : wedgeInl X Y ≫ wedge2Desc h k w = h :=
  Glue.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem wedge2Desc_inr {X Y : BPSet} {W : PrecubicalSet} (h : X.toPsh ⟶ W) (k : Y.toPsh ⟶ W)
    (w : X.finalVertex ≫ h = Y.initVertex ≫ k) : wedgeInr X Y ≫ wedge2Desc h k w = k :=
  Glue.inr_desc _ _ _

/-- Maps out of the wedge are pinned by their two leaf restrictions. -/
theorem wedge2_hom_ext {X Y : BPSet} {W : PrecubicalSet} {a b : (X ∨ Y).toPsh ⟶ W}
    (hl : wedgeInl X Y ≫ a = wedgeInl X Y ≫ b)
    (hr : wedgeInr X Y ≫ a = wedgeInr X Y ≫ b) : a = b := Glue.hom_ext hl hr

/-- The initial-vertex *map* of `X ∨ Y` factors through the left inclusion. -/
theorem wedge2_initVertex (X Y : BPSet) :
    (wedge2 X Y).initVertex = X.initVertex ≫ wedgeInl X Y := by
  conv_lhs => rw [show (wedge2 X Y).initVertex
    = yonedaEquiv.symm ((wedge2 X Y).init) from rfl,
    show (wedge2 X Y).init = (wedgeInl X Y)⟪0⟫ X.init from rfl]
  exact (yonedaEquiv_symm_naturality_right ▫0 (wedgeInl X Y) X.init).symm

/-- The final-vertex *map* of `X ∨ Y` factors through the right inclusion. -/
theorem wedge2_finalVertex (X Y : BPSet) :
    (wedge2 X Y).finalVertex = Y.finalVertex ≫ wedgeInr X Y := by
  conv_lhs => rw [show (wedge2 X Y).finalVertex
    = yonedaEquiv.symm ((wedge2 X Y).final) from rfl,
    show (wedge2 X Y).final = (wedgeInr X Y)⟪0⟫ Y.final from rfl]
  exact (yonedaEquiv_symm_naturality_right ▫0 (wedgeInr X Y) Y.final).symm

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
def wedge2AssocFwd (a b c : BPSet) : ((a ∨ b) ∨ c).toPsh ⟶ (a ∨ b ∨ c).toPsh :=
  wedge2Desc
    (wedge2Desc (wedgeInl a (b ∨ c)) (wedgeInl b c ≫ wedgeInr a (b ∨ c))
      (by rw [wedge2_condition a (b ∨ c), wedge2_initVertex b c, Category.assoc]))
    (wedgeInr b c ≫ wedgeInr a (b ∨ c))
    (by rw [wedge2_finalVertex a b, Category.assoc, wedge2Desc_inr,
      reassoc_of% wedge2_condition b c])

theorem wedge2AssocFwd_initVertex (a b c : BPSet) :
    ((a ∨ b) ∨ c).initVertex ≫ wedge2AssocFwd a b c = (a ∨ b ∨ c).initVertex := by
  rw [wedge2AssocFwd, wedge2_initVertex (a ∨ b) c, Category.assoc, wedge2Desc_inl,
    wedge2_initVertex a b, Category.assoc, wedge2Desc_inl, ← wedge2_initVertex a (b ∨ c)]

theorem wedge2AssocFwd_finalVertex (a b c : BPSet) :
    ((a ∨ b) ∨ c).finalVertex ≫ wedge2AssocFwd a b c = (a ∨ b ∨ c).finalVertex := by
  rw [wedge2AssocFwd, wedge2_finalVertex (a ∨ b) c, Category.assoc, wedge2Desc_inr,
    wedge2_finalVertex a (b ∨ c), wedge2_finalVertex b c, ← Category.assoc]

/-- Underlying presheaf map of the inverse associator. -/
def wedge2AssocBwd (a b c : BPSet) : (a ∨ b ∨ c).toPsh ⟶ ((a ∨ b) ∨ c).toPsh :=
  wedge2Desc
    (wedgeInl a b ≫ wedgeInl (a ∨ b) c)
    (wedge2Desc (wedgeInr a b ≫ wedgeInl (a ∨ b) c) (wedgeInr (a ∨ b) c)
      (by rw [← Category.assoc, ← wedge2_finalVertex a b, wedge2_condition (a ∨ b) c]))
    (by rw [← Category.assoc, wedge2_condition a b, Category.assoc, wedge2_initVertex b c,
      Category.assoc, wedge2Desc_inl])

theorem wedge2AssocBwd_initVertex (a b c : BPSet) :
    (a ∨ b ∨ c).initVertex ≫ wedge2AssocBwd a b c = ((a ∨ b) ∨ c).initVertex := by
  rw [wedge2AssocBwd, wedge2_initVertex a (b ∨ c), Category.assoc, wedge2Desc_inl,
    ← Category.assoc, ← wedge2_initVertex a b, ← wedge2_initVertex (a ∨ b) c]

theorem wedge2AssocBwd_finalVertex (a b c : BPSet) :
    (a ∨ b ∨ c).finalVertex ≫ wedge2AssocBwd a b c = ((a ∨ b) ∨ c).finalVertex := by
  rw [wedge2AssocBwd, wedge2_finalVertex a (b ∨ c), Category.assoc, wedge2Desc_inr,
    wedge2_finalVertex b c, Category.assoc, wedge2Desc_inr, ← wedge2_finalVertex (a ∨ b) c]

theorem wedge2AssocFwd_bwd (a b c : BPSet) :
    wedge2AssocFwd a b c ≫ wedge2AssocBwd a b c = 𝟙 ((a ∨ b) ∨ c).toPsh := by
  rw [wedge2AssocFwd, wedge2AssocBwd]
  refine wedge2_hom_ext (wedge2_hom_ext ?_ ?_) ?_
  · rw [wedge2Desc_inl_assoc, wedge2Desc_inl_assoc, wedge2Desc_inl, Category.comp_id]
  · rw [wedge2Desc_inl_assoc, wedge2Desc_inr_assoc, Category.assoc, wedge2Desc_inr,
      wedge2Desc_inl, Category.comp_id]
  · rw [wedge2Desc_inr_assoc, Category.assoc, wedge2Desc_inr, wedge2Desc_inr, Category.comp_id]

theorem wedge2AssocBwd_fwd (a b c : BPSet) :
    wedge2AssocBwd a b c ≫ wedge2AssocFwd a b c = 𝟙 (a ∨ b ∨ c).toPsh := by
  rw [wedge2AssocFwd, wedge2AssocBwd]
  refine wedge2_hom_ext ?_ (wedge2_hom_ext ?_ ?_)
  · rw [wedge2Desc_inl_assoc, Category.assoc, wedge2Desc_inl, wedge2Desc_inl, Category.comp_id]
  · rw [wedge2Desc_inr_assoc, wedge2Desc_inl_assoc, Category.assoc, wedge2Desc_inl,
      wedge2Desc_inr, Category.comp_id]
  · rw [wedge2Desc_inr_assoc, wedge2Desc_inr_assoc, wedge2Desc_inr, Category.comp_id]

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
    X.initVertex ≫ wedgeInr (□0) X = wedgeInl (□0) X := by
  rw [← wedge2_condition (□0) X, cube0_finalVertex_comp]

/-- At the collapsing junction of `X ∨ cube 0`, the left inclusion of `X.final` is the right. -/
theorem wedge2_cube0_inl_eq_inr (X : BPSet) :
    X.finalVertex ≫ wedgeInl X (□0) = wedgeInr X (□0) := by
  rw [wedge2_condition X (□0), cube0_initVertex_comp]

/-- Underlying map of the left-unit iso `cube 0 ∨ X ⟶ X`. -/
def wedge2LeftUnitPsh (X : BPSet) : (□0 ∨ X).toPsh ⟶ X.toPsh :=
  wedge2Desc X.initVertex (𝟙 X.toPsh) (by rw [cube0_finalVertex_comp, Category.comp_id])

theorem wedge2LeftUnitPsh_initVertex (X : BPSet) :
    (□0 ∨ X).initVertex ≫ wedge2LeftUnitPsh X = X.initVertex := by
  rw [wedge2LeftUnitPsh, wedge2_initVertex (□0) X, Category.assoc, wedge2Desc_inl,
    cube0_initVertex_comp]

theorem wedge2LeftUnitPsh_finalVertex (X : BPSet) :
    (□0 ∨ X).finalVertex ≫ wedge2LeftUnitPsh X = X.finalVertex := by
  rw [wedge2LeftUnitPsh, wedge2_finalVertex (□0) X, Category.assoc, wedge2Desc_inr,
    Category.comp_id]

@[reassoc]
theorem wedge2LeftUnitPsh_inl (X : BPSet) :
    wedgeInl (□0) X ≫ wedge2LeftUnitPsh X = X.initVertex := by
  rw [wedge2LeftUnitPsh, wedge2Desc_inl]

@[reassoc]
theorem wedge2LeftUnitPsh_inr (X : BPSet) :
    wedgeInr (□0) X ≫ wedge2LeftUnitPsh X = 𝟙 X.toPsh := by
  rw [wedge2LeftUnitPsh, wedge2Desc_inr]

/-- **Left unit.** `cube 0 ∨ X ≅ X`. -/
def wedge2LeftUnit (X : BPSet) : (□0) ∨ X ≅ X where
  hom :=
    { hom := wedge2LeftUnitPsh X
      app_init := app_init_eq_of_initVertex _ (wedge2LeftUnitPsh_initVertex X)
      app_final := app_final_eq_of_finalVertex _ (wedge2LeftUnitPsh_finalVertex X) }
  inv :=
    { hom := wedgeInr (□0) X
      app_init := @app_init_eq_of_initVertex X ((□0) ∨ X) (wedgeInr (□0) X) (by
        rw [wedge2_initVertex (□0) X, cube0_initVertex_comp]; exact wedge2_cube0_inr_eq_inl X)
      app_final := @app_final_eq_of_finalVertex X ((□0) ∨ X) (wedgeInr (□0) X)
        (wedge2_finalVertex (□0) X).symm }
  hom_inv_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    refine wedge2_hom_ext ?_ ?_
    · rw [wedge2LeftUnitPsh_inl_assoc, Category.comp_id]; exact wedge2_cube0_inr_eq_inl X
    · rw [wedge2LeftUnitPsh_inr_assoc, Category.comp_id]
  inv_hom_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom, wedge2LeftUnitPsh_inr]

/-- Underlying map of the right-unit iso `X ∨ cube 0 ⟶ X`. -/
def wedge2RightUnitPsh (X : BPSet) : (X ∨ □0).toPsh ⟶ X.toPsh :=
  wedge2Desc (𝟙 X.toPsh) X.finalVertex (by rw [cube0_initVertex_comp, Category.comp_id])

theorem wedge2RightUnitPsh_initVertex (X : BPSet) :
    (X ∨ □0).initVertex ≫ wedge2RightUnitPsh X = X.initVertex := by
  rw [wedge2RightUnitPsh, wedge2_initVertex X (□0), Category.assoc, wedge2Desc_inl,
    Category.comp_id]

theorem wedge2RightUnitPsh_finalVertex (X : BPSet) :
    (X ∨ □0).finalVertex ≫ wedge2RightUnitPsh X = X.finalVertex := by
  rw [wedge2RightUnitPsh, wedge2_finalVertex X (□0), Category.assoc, wedge2Desc_inr,
    cube0_finalVertex_comp]

@[reassoc]
theorem wedge2RightUnitPsh_inl (X : BPSet) :
    wedgeInl X (□0) ≫ wedge2RightUnitPsh X = 𝟙 X.toPsh := by
  rw [wedge2RightUnitPsh, wedge2Desc_inl]

@[reassoc]
theorem wedge2RightUnitPsh_inr (X : BPSet) :
    wedgeInr X (□0) ≫ wedge2RightUnitPsh X = X.finalVertex := by
  rw [wedge2RightUnitPsh, wedge2Desc_inr]

/-- **Right unit.** `X ∨ cube 0 ≅ X`. -/
def wedge2RightUnit (X : BPSet) : X ∨ □0 ≅ X where
  hom :=
    { hom := wedge2RightUnitPsh X
      app_init := app_init_eq_of_initVertex _ (wedge2RightUnitPsh_initVertex X)
      app_final := app_final_eq_of_finalVertex _ (wedge2RightUnitPsh_finalVertex X) }
  inv :=
    { hom := wedgeInl X (□0)
      app_init := @app_init_eq_of_initVertex X (X ∨ □0) (wedgeInl X (□0))
        (wedge2_initVertex X (□0)).symm
      app_final := @app_final_eq_of_finalVertex X (X ∨ □0) (wedgeInl X (□0)) (by
        rw [wedge2_finalVertex X (□0), cube0_finalVertex_comp]; exact wedge2_cube0_inl_eq_inr X) }
  hom_inv_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom]
    refine wedge2_hom_ext ?_ ?_
    · rw [wedge2RightUnitPsh_inl_assoc, Category.comp_id]
    · rw [wedge2RightUnitPsh_inr_assoc, Category.comp_id]; exact wedge2_cube0_inl_eq_inr X
  inv_hom_id := by
    apply BPSet.hom_ext
    rw [comp_hom, id_hom, wedge2RightUnitPsh_inl]

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
    (X₁ ∨ Y₁).toPsh ⟶ (X₂ ∨ Y₂).toPsh :=
  wedge2Desc (f.hom ≫ wedgeInl X₂ Y₂) (g.hom ≫ wedgeInr X₂ Y₂)
    (by rw [← Category.assoc, ← Category.assoc, finalVertex_comp_hom f, initVertex_comp_hom g,
      wedge2_condition X₂ Y₂])

@[reassoc]
theorem wedge2MapPsh_inl {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    wedgeInl X₁ Y₁ ≫ wedge2MapPsh f g = f.hom ≫ wedgeInl X₂ Y₂ := by
  rw [wedge2MapPsh, wedge2Desc_inl]

@[reassoc]
theorem wedge2MapPsh_inr {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    wedgeInr X₁ Y₁ ≫ wedge2MapPsh f g = g.hom ≫ wedgeInr X₂ Y₂ := by
  rw [wedge2MapPsh, wedge2Desc_inr]

/-- The bifunctor action of `wedge2` on morphisms. -/
def wedge2Map {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : X₁ ∨ Y₁ ⟶ X₂ ∨ Y₂ where
  hom := wedge2MapPsh f g
  app_init := @app_init_eq_of_initVertex (X₁ ∨ Y₁) (X₂ ∨ Y₂) (wedge2MapPsh f g) (by
    rw [wedge2_initVertex X₁ Y₁, Category.assoc, wedge2MapPsh_inl, ← Category.assoc,
      initVertex_comp_hom f, ← wedge2_initVertex X₂ Y₂])
  app_final := @app_final_eq_of_finalVertex (X₁ ∨ Y₁) (X₂ ∨ Y₂) (wedge2MapPsh f g) (by
    rw [wedge2_finalVertex X₁ Y₁, Category.assoc, wedge2MapPsh_inr, ← Category.assoc,
      finalVertex_comp_hom g, ← wedge2_finalVertex X₂ Y₂])

@[simp] theorem wedge2Map_hom {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (wedge2Map f g).hom = wedge2MapPsh f g := rfl

/-- Functoriality (identity): `wedge2Map (𝟙 X) (𝟙 Y) = 𝟙`. -/
theorem wedge2Map_id (X Y : BPSet) : wedge2Map (𝟙 X) (𝟙 Y) = 𝟙 (wedge2 X Y) := by
  apply BPSet.hom_ext
  rw [wedge2Map_hom, id_hom]
  refine wedge2_hom_ext ?_ ?_
  · rw [wedge2MapPsh_inl, id_hom, Category.id_comp, Category.comp_id]
  · rw [wedge2MapPsh_inr, id_hom, Category.id_comp, Category.comp_id]

/-- Functoriality (composition). -/
theorem wedge2Map_comp {X₁ X₂ X₃ Y₁ Y₂ Y₃ : BPSet}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    wedge2Map (f₁ ≫ f₂) (g₁ ≫ g₂) = wedge2Map f₁ g₁ ≫ wedge2Map f₂ g₂ := by
  apply BPSet.hom_ext
  rw [comp_hom, wedge2Map_hom, wedge2Map_hom, wedge2Map_hom]
  refine wedge2_hom_ext ?_ ?_
  · rw [wedge2MapPsh_inl, wedge2MapPsh_inl_assoc, wedge2MapPsh_inl, comp_hom, Category.assoc]
  · rw [wedge2MapPsh_inr, wedge2MapPsh_inr_assoc, wedge2MapPsh_inr, comp_hom, Category.assoc]

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

Each lemma peels one `wedge2Desc`; tagged `@[reassoc]` so they fire under a trailing composition.
The coherence proofs below are then `wedge2_hom_ext` (iterated) + `simp` with these. -/

@[reassoc]
theorem wedge2AssocFwd_inl_inl (a b c : BPSet) :
    wedgeInl a b ≫ wedgeInl (a ∨ b) c ≫ wedge2AssocFwd a b c = wedgeInl a (b ∨ c) := by
  rw [wedge2AssocFwd, wedge2Desc_inl, wedge2Desc_inl]

@[reassoc]
theorem wedge2AssocFwd_inr_inl (a b c : BPSet) :
    wedgeInr a b ≫ wedgeInl (a ∨ b) c ≫ wedge2AssocFwd a b c
      = wedgeInl b c ≫ wedgeInr a (b ∨ c) := by
  rw [wedge2AssocFwd, wedge2Desc_inl, wedge2Desc_inr]

@[reassoc]
theorem wedge2AssocFwd_inr (a b c : BPSet) :
    wedgeInr (a ∨ b) c ≫ wedge2AssocFwd a b c = wedgeInr b c ≫ wedgeInr a (b ∨ c) := by
  rw [wedge2AssocFwd, wedge2Desc_inr]

@[reassoc]
theorem wedge2AssocBwd_inl (a b c : BPSet) :
    wedgeInl a (b ∨ c) ≫ wedge2AssocBwd a b c = wedgeInl a b ≫ wedgeInl (a ∨ b) c := by
  rw [wedge2AssocBwd, wedge2Desc_inl]

@[reassoc]
theorem wedge2AssocBwd_inl_inr (a b c : BPSet) :
    wedgeInl b c ≫ wedgeInr a (b ∨ c) ≫ wedge2AssocBwd a b c
      = wedgeInr a b ≫ wedgeInl (a ∨ b) c := by
  rw [wedge2AssocBwd, wedge2Desc_inr, wedge2Desc_inl]

@[reassoc]
theorem wedge2AssocBwd_inr_inr (a b c : BPSet) :
    wedgeInr b c ≫ wedgeInr a (b ∨ c) ≫ wedge2AssocBwd a b c = wedgeInr (a ∨ b) c := by
  rw [wedge2AssocBwd, wedge2Desc_inr, wedge2Desc_inr]

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

Every proof below is `wedge2_hom_ext` (iterated) down to the leaves, then `simp`: the restriction
lemmas peel one leaf inclusion per step and are confluent, so no hand-written chain is needed.
Sealing the underlying maps and the vertex selectors `irreducible` is load-bearing — it stops
unification descending into the nested `wedge2Desc` towers. -/

attribute [local irreducible] wedge2MapPsh wedge2AssocFwd wedge2AssocBwd
  wedge2LeftUnitPsh wedge2RightUnitPsh
attribute [local irreducible] BPSet.finalVertex BPSet.initVertex

attribute [local simp]
  wedge2MapPsh_inl wedge2MapPsh_inr wedge2MapPsh_inl_assoc wedge2MapPsh_inr_assoc
  wedge2AssocFwd_inl_inl wedge2AssocFwd_inr_inl wedge2AssocFwd_inr
  wedge2AssocFwd_inl_inl_assoc wedge2AssocFwd_inr_inl_assoc wedge2AssocFwd_inr_assoc
  wedge2LeftUnitPsh_inl wedge2LeftUnitPsh_inr
  wedge2LeftUnitPsh_inl_assoc wedge2LeftUnitPsh_inr_assoc
  wedge2RightUnitPsh_inl wedge2RightUnitPsh_inr
  wedge2RightUnitPsh_inl_assoc wedge2RightUnitPsh_inr_assoc

/-- Associator naturality. -/
theorem wedge2Assoc_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : BPSet}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    wedge2Map (wedge2Map f₁ f₂) f₃ ≫ wedge2AssocHom Y₁ Y₂ Y₃
      = wedge2AssocHom X₁ X₂ X₃ ≫ wedge2Map f₁ (wedge2Map f₂ f₃) := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2Map_hom, wedge2AssocHom_hom, wedge2AssocHom_hom]
  refine wedge2_hom_ext (wedge2_hom_ext ?_ ?_) ?_ <;> simp

/-- Left-unitor naturality. -/
theorem wedge2LeftUnit_naturality {X Y : BPSet} (f : X ⟶ Y) :
    wedge2Map (𝟙 (□0)) f ≫ (wedge2LeftUnit Y).hom = (wedge2LeftUnit X).hom ≫ f := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2LeftUnit_hom_hom, wedge2LeftUnit_hom_hom]
  refine wedge2_hom_ext ?_ ?_
  · simp only [wedge2MapPsh_inl_assoc, id_hom, wedge2LeftUnitPsh_inl,
      Category.id_comp, wedge2LeftUnitPsh_inl_assoc]
    -- `≫` here is the functor-category composition, which `simp`'s matcher does not see through.
    exact (initVertex_comp_hom f).symm
  · simp

/-- Right-unitor naturality. -/
theorem wedge2RightUnit_naturality {X Y : BPSet} (f : X ⟶ Y) :
    wedge2Map f (𝟙 (□0)) ≫ (wedge2RightUnit Y).hom = (wedge2RightUnit X).hom ≫ f := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2RightUnit_hom_hom, wedge2RightUnit_hom_hom]
  refine wedge2_hom_ext ?_ ?_
  · simp
  · simp only [wedge2MapPsh_inr_assoc, id_hom, wedge2RightUnitPsh_inr,
      Category.id_comp, wedge2RightUnitPsh_inr_assoc]
    exact (finalVertex_comp_hom f).symm

/-! ### Coherence: pentagon and triangle -/

/-- Triangle identity. -/
theorem wedge2_triangle (X Y : BPSet) :
    wedge2AssocHom X (□0) Y ≫ wedge2Map (𝟙 X) (wedge2LeftUnit Y).hom
      = wedge2Map (wedge2RightUnit X).hom (𝟙 Y) := by
  apply BPSet.hom_ext
  rw [comp_hom, wedge2AssocHom_hom, wedge2Map_hom, wedge2Map_hom]
  refine wedge2_hom_ext (wedge2_hom_ext ?_ ?_) ?_
  · simp
  · simp only [wedge2AssocFwd_inr_inl_assoc, wedge2MapPsh_inr,
      wedge2LeftUnit_hom_hom, wedge2LeftUnitPsh_inl_assoc, wedge2MapPsh_inl,
      wedge2RightUnit_hom_hom, wedge2RightUnitPsh_inr_assoc]
    -- the middle leaf lands on the gluing square itself
    exact (wedge2_condition X Y).symm
  · simp

/-- Pentagon identity. -/
theorem wedge2_pentagon (W X Y Z : BPSet) :
    wedge2Map (wedge2AssocHom W X Y) (𝟙 Z) ≫ wedge2AssocHom W (wedge2 X Y) Z
        ≫ wedge2Map (𝟙 W) (wedge2AssocHom X Y Z)
      = wedge2AssocHom (wedge2 W X) Y Z ≫ wedge2AssocHom W X (wedge2 Y Z) := by
  apply BPSet.hom_ext
  simp only [comp_hom, wedge2Map_hom, wedge2AssocHom_hom]
  refine wedge2_hom_ext (wedge2_hom_ext (wedge2_hom_ext ?_ ?_) ?_) ?_ <;> simp

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
