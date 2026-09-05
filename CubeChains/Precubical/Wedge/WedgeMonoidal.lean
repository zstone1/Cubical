import CubeChains.Precubical.Wedge.Wedge
import CubeChains.Precubical.Wedge.GluePushout
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Precubical/Wedge/WedgeMonoidal

The wedge `∨` as the **default** `MonoidalCategory BPSet`: tensor `= wedge2`, unit `= □0`,
associator/unitors from `wedge2Assoc` / `wedge2LeftUnit` / `wedge2RightUnit`, all built directly
from the pushout `Glue`.  The geometric tensor `⊗ᵍ` keeps its own alias `GeoBP`.
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
    (wedge2 X Y).initVertex = X.initVertex ≫ wedgeInl X Y :=
  (vertexMap_comp X.init (wedgeInl X Y)).symm

/-- The final-vertex *map* of `X ∨ Y` factors through the right inclusion. -/
theorem wedge2_finalVertex (X Y : BPSet) :
    (wedge2 X Y).finalVertex = Y.finalVertex ≫ wedgeInr X Y :=
  (vertexMap_comp Y.final (wedgeInr X Y)).symm

/-- `wedge2Desc` at the bi-pointed level: the endpoint conditions are supplied in vertex-map form,
so the descent of a pair of maps is a `BPSet` map and not merely a presheaf one. -/
def wedge2DescBP {X Y T : BPSet} (h : X.toPsh ⟶ T.toPsh) (k : Y.toPsh ⟶ T.toPsh)
    (w : X.finalVertex ≫ h = Y.initVertex ≫ k)
    (hi : X.initVertex ≫ h = T.initVertex) (hf : Y.finalVertex ≫ k = T.finalVertex) :
    X ∨ Y ⟶ T where
  hom := wedge2Desc h k w
  app_init := app_eq_of_vertexMap (by
    show (X ∨ Y).initVertex ≫ wedge2Desc h k w = T.initVertex
    rw [wedge2_initVertex, Category.assoc, wedge2Desc_inl, hi])
  app_final := app_eq_of_vertexMap (by
    show (X ∨ Y).finalVertex ≫ wedge2Desc h k w = T.finalVertex
    rw [wedge2_finalVertex, Category.assoc, wedge2Desc_inr, hf])

@[simp] theorem wedge2DescBP_hom {X Y T : BPSet} (h : X.toPsh ⟶ T.toPsh) (k : Y.toPsh ⟶ T.toPsh)
    (w : X.finalVertex ≫ h = Y.initVertex ≫ k)
    (hi : X.initVertex ≫ h = T.initVertex) (hf : Y.finalVertex ≫ k = T.finalVertex) :
    (wedge2DescBP h k w hi hf).hom = wedge2Desc h k w := rfl

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

/-- Underlying presheaf iso of the associator. -/
def wedge2AssocPshIso (a b c : BPSet) :
    ((a ∨ b) ∨ c).toPsh ≅ (a ∨ b ∨ c).toPsh where
  hom := wedge2AssocFwd a b c
  inv := wedge2AssocBwd a b c
  hom_inv_id := wedge2AssocFwd_bwd a b c
  inv_hom_id := wedge2AssocBwd_fwd a b c

/-- **Associativity of the wedge.** `(a ∨ b) ∨ c ≅ a ∨ (b ∨ c)`. -/
def wedge2Assoc (a b c : BPSet) : wedge2 (wedge2 a b) c ≅ wedge2 a (wedge2 b c) :=
  isoOfPshIso (wedge2AssocPshIso a b c)
    (app_eq_of_vertexMap (wedge2AssocFwd_initVertex a b c))
    (app_eq_of_vertexMap (wedge2AssocFwd_finalVertex a b c))

/-! ### The collapse helpers for the point `cube 0`

These vertex-identity and `IsIso` facts about the point `□⁰` feed the concatenation
functor and the `cube 0` unit equivalence below. -/

/-- Every vertex inclusion of the point `cube 0` is the identity — there is only one. -/
theorem cube0_vertexMap_eq_id (v : (□0).cells 0) :
    vertexMap (□0).toPsh v = 𝟙 (yoneda.obj ▫0) := by
  rw [vertexMap, PrecubicalSet.cubeMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

@[simp] theorem cube0_initVertex_eq_id : (□0).initVertex = 𝟙 (yoneda.obj ▫0) :=
  cube0_vertexMap_eq_id _

@[simp] theorem cube0_finalVertex_eq_id : (□0).finalVertex = 𝟙 (yoneda.obj ▫0) :=
  cube0_vertexMap_eq_id _

instance : IsIso ((□0).initVertex) := by
  rw [cube0_initVertex_eq_id]; exact IsIso.id _

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

/-- A vertex of `□0` acts as an identity on the left (it *is* `𝟙`, but stated in `≫`-form so
it rewrites cleanly even when the cofactor's index mentions the vertex). -/
theorem cube0_vertexMap_comp {A : PrecubicalSet} (v : (□0).cells 0) (f : (□0).toPsh ⟶ A) :
    vertexMap (□0).toPsh v ≫ f = f := by
  rw [cube0_vertexMap_eq_id]; exact Category.id_comp f

theorem cube0_finalVertex_comp {A : PrecubicalSet} (f : (□0).toPsh ⟶ A) :
    (□0).finalVertex ≫ f = f := cube0_vertexMap_comp _ f

theorem cube0_initVertex_comp {A : PrecubicalSet} (f : (□0).toPsh ⟶ A) :
    (□0).initVertex ≫ f = f := cube0_vertexMap_comp _ f

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

/-- Underlying presheaf iso of the left unit: the right leaf inclusion is its inverse. -/
def wedge2LeftUnitPshIso (X : BPSet) : ((□0) ∨ X).toPsh ≅ X.toPsh where
  hom := wedge2LeftUnitPsh X
  inv := wedgeInr (□0) X
  hom_inv_id := by
    refine wedge2_hom_ext ?_ ?_
    · rw [wedge2LeftUnitPsh_inl_assoc, Category.comp_id]; exact wedge2_cube0_inr_eq_inl X
    · rw [wedge2LeftUnitPsh_inr_assoc, Category.comp_id]
  inv_hom_id := wedge2LeftUnitPsh_inr X

/-- **Left unit.** `cube 0 ∨ X ≅ X`. -/
def wedge2LeftUnit (X : BPSet) : (□0) ∨ X ≅ X :=
  isoOfPshIso (wedge2LeftUnitPshIso X)
    (app_eq_of_vertexMap (wedge2LeftUnitPsh_initVertex X))
    (app_eq_of_vertexMap (wedge2LeftUnitPsh_finalVertex X))

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

/-- Underlying presheaf iso of the right unit: the left leaf inclusion is its inverse. -/
def wedge2RightUnitPshIso (X : BPSet) : (X ∨ □0).toPsh ≅ X.toPsh where
  hom := wedge2RightUnitPsh X
  inv := wedgeInl X (□0)
  hom_inv_id := by
    refine wedge2_hom_ext ?_ ?_
    · rw [wedge2RightUnitPsh_inl_assoc, Category.comp_id]
    · rw [wedge2RightUnitPsh_inr_assoc, Category.comp_id]; exact wedge2_cube0_inl_eq_inr X
  inv_hom_id := wedge2RightUnitPsh_inl X

/-- **Right unit.** `X ∨ cube 0 ≅ X`. -/
def wedge2RightUnit (X : BPSet) : X ∨ □0 ≅ X :=
  isoOfPshIso (wedge2RightUnitPshIso X)
    (app_eq_of_vertexMap (wedge2RightUnitPsh_initVertex X))
    (app_eq_of_vertexMap (wedge2RightUnitPsh_finalVertex X))

/-! ### The wedge on morphisms -/

/-- A bi-pointed map's underlying presheaf map carries the final vertex to the final vertex
(selector form of `app_final`). -/
theorem finalVertex_comp_hom {X Y : BPSet} (f : X ⟶ Y) :
    X.finalVertex ≫ f.hom = Y.finalVertex :=
  (vertexMap_comp X.final f.hom).trans (congrArg (vertexMap Y.toPsh) f.app_final)

theorem initVertex_comp_hom {X Y : BPSet} (f : X ⟶ Y) :
    X.initVertex ≫ f.hom = Y.initVertex :=
  (vertexMap_comp X.init f.hom).trans (congrArg (vertexMap Y.toPsh) f.app_init)

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
  app_init := app_eq_of_vertexMap (φ := wedge2MapPsh f g) (by
    show (X₁ ∨ Y₁).initVertex ≫ wedge2MapPsh f g = (X₂ ∨ Y₂).initVertex
    rw [wedge2_initVertex X₁ Y₁, Category.assoc, wedge2MapPsh_inl, ← Category.assoc,
      initVertex_comp_hom f, ← wedge2_initVertex X₂ Y₂])
  app_final := app_eq_of_vertexMap (φ := wedge2MapPsh f g) (by
    show (X₁ ∨ Y₁).finalVertex ≫ wedge2MapPsh f g = (X₂ ∨ Y₂).finalVertex
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

/-- **The interchange square of the wedge is a pushout** — maps re-shaping opposite halves of a
wedge are independent, so a cocone on them descends, uniquely.  Nothing is assumed of the four
sets, which is what makes `ChainCat.exists_join_of_split` hold for every `K`.

```
    X ∨ Y  --f∨1-->  X' ∨ Y
      |                 |
     1∨g               1∨g
      v                 v
    X ∨ Y' --f∨1-->  X' ∨ Y'
```
-/
theorem wedge2Map_isPushout {X X' Y Y' : BPSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    IsPushout (wedge2Map f (𝟙 Y)) (wedge2Map (𝟙 X) g)
      (wedge2Map (𝟙 X') g) (wedge2Map f (𝟙 Y')) := by
  have hIL : wedgeInl X Y ≫ wedge2MapPsh (𝟙 X) g = wedgeInl X Y' := by
    rw [wedge2MapPsh_inl, id_hom, Category.id_comp]
  have hIR : wedgeInr X Y ≫ wedge2MapPsh f (𝟙 Y) = wedgeInr X' Y := by
    rw [wedge2MapPsh_inr, id_hom, Category.id_comp]
  have hOL : wedgeInl X' Y ≫ wedge2MapPsh (𝟙 X') g = wedgeInl X' Y' := by
    rw [wedge2MapPsh_inl, id_hom, Category.id_comp]
  have hsq : wedge2Map f (𝟙 Y) ≫ wedge2Map (𝟙 X') g
      = wedge2Map (𝟙 X) g ≫ wedge2Map f (𝟙 Y') := by
    rw [← wedge2Map_comp, ← wedge2Map_comp, Category.comp_id, Category.id_comp,
      Category.id_comp, Category.comp_id]
  refine IsPushout.of_isColimit' ⟨hsq⟩ (PushoutCocone.isColimitAux' _ (fun s => ?_))
  have hcond : wedge2MapPsh f (𝟙 Y) ≫ (PushoutCocone.inl s).hom
      = wedge2MapPsh (𝟙 X) g ≫ (PushoutCocone.inr s).hom :=
    congrArg (fun t : (X ∨ Y) ⟶ s.pt => t.hom) s.condition
  have e1 : wedgeInr X' Y ≫ (PushoutCocone.inl s).hom
      = wedgeInr X Y ≫ wedge2MapPsh (𝟙 X) g ≫ (PushoutCocone.inr s).hom := by
    rw [← hcond, ← Category.assoc, hIR]
  have e2 : wedgeInl X Y' ≫ (PushoutCocone.inr s).hom
      = wedgeInl X Y ≫ wedge2MapPsh (𝟙 X) g ≫ (PushoutCocone.inr s).hom := by
    rw [← Category.assoc, hIL]
  have hcompat : X'.finalVertex ≫ (wedgeInl X' Y ≫ (PushoutCocone.inl s).hom)
      = Y'.initVertex ≫ (wedgeInr X Y' ≫ (PushoutCocone.inr s).hom) := by
    rw [← Category.assoc, wedge2_condition X' Y, Category.assoc, e1,
      ← Category.assoc, ← wedge2_condition X Y, Category.assoc, ← e2,
      ← Category.assoc, wedge2_condition X Y', Category.assoc]
  have hi : X'.initVertex ≫ (wedgeInl X' Y ≫ (PushoutCocone.inl s).hom) = s.pt.initVertex := by
    rw [← Category.assoc, ← wedge2_initVertex]
    exact initVertex_comp_hom (PushoutCocone.inl s)
  have hf : Y'.finalVertex ≫ (wedgeInr X Y' ≫ (PushoutCocone.inr s).hom) = s.pt.finalVertex := by
    rw [← Category.assoc, ← wedge2_finalVertex]
    exact finalVertex_comp_hom (PushoutCocone.inr s)
  -- `change` pins the wedge spelling of the cocone point, which `rw` cannot reach through
  -- `CommSq.cocone`.
  refine ⟨wedge2DescBP _ _ hcompat hi hf, ?_, ?_, ?_⟩
  · change wedge2Map (𝟙 X') g ≫ wedge2DescBP _ _ hcompat hi hf = PushoutCocone.inl s
    refine BPSet.hom_ext (wedge2_hom_ext ?_ ?_)
    · rw [comp_hom, wedge2Map_hom, ← Category.assoc, hOL, wedge2DescBP_hom, wedge2Desc_inl]
    · rw [comp_hom, wedge2Map_hom, wedge2MapPsh_inr_assoc, wedge2DescBP_hom, wedge2Desc_inr, e1,
        wedge2MapPsh_inr_assoc]
  · change wedge2Map f (𝟙 Y') ≫ wedge2DescBP _ _ hcompat hi hf = PushoutCocone.inr s
    refine BPSet.hom_ext (wedge2_hom_ext ?_ ?_)
    · rw [comp_hom, wedge2Map_hom, wedge2MapPsh_inl_assoc, wedge2DescBP_hom, wedge2Desc_inl,
        ← Category.assoc, ← wedge2MapPsh_inl f (𝟙 Y), Category.assoc, hcond, ← e2]
    · rw [comp_hom, wedge2Map_hom, wedge2MapPsh_inr_assoc, id_hom, Category.id_comp,
        wedge2DescBP_hom, wedge2Desc_inr]
  · intro m h₁ h₂
    replace h₁ : wedge2Map (𝟙 X') g ≫ m = PushoutCocone.inl s := h₁
    replace h₂ : wedge2Map f (𝟙 Y') ≫ m = PushoutCocone.inr s := h₂
    change m = wedge2DescBP _ _ hcompat hi hf
    refine BPSet.hom_ext (wedge2_hom_ext ?_ ?_)
    · have hm := congrArg (fun t : (X' ∨ Y) ⟶ s.pt => wedgeInl X' Y ≫ t.hom) h₁
      simp only [comp_hom, wedge2Map_hom, wedge2MapPsh_inl_assoc, id_hom, Category.id_comp] at hm
      rw [hm, wedge2DescBP_hom, wedge2Desc_inl]
    · have hm := congrArg (fun t : (X ∨ Y') ⟶ s.pt => wedgeInr X Y' ≫ t.hom) h₂
      simp only [comp_hom, wedge2Map_hom, wedge2MapPsh_inr_assoc, id_hom, Category.id_comp] at hm
      rw [hm, wedge2DescBP_hom, wedge2Desc_inr]

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
@[simp] theorem wedge2Assoc_hom_hom (a b c : BPSet) :
    (wedge2Assoc a b c).hom.hom = wedge2AssocFwd a b c := rfl

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
    wedge2Map (wedge2Map f₁ f₂) f₃ ≫ (wedge2Assoc Y₁ Y₂ Y₃).hom
      = (wedge2Assoc X₁ X₂ X₃).hom ≫ wedge2Map f₁ (wedge2Map f₂ f₃) := by
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, wedge2Map_hom, wedge2Map_hom, wedge2Assoc_hom_hom, wedge2Assoc_hom_hom]
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
    (wedge2Assoc X (□0) Y).hom ≫ wedge2Map (𝟙 X) (wedge2LeftUnit Y).hom
      = wedge2Map (wedge2RightUnit X).hom (𝟙 Y) := by
  apply BPSet.hom_ext
  rw [comp_hom, wedge2Assoc_hom_hom, wedge2Map_hom, wedge2Map_hom]
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
    wedge2Map (wedge2Assoc W X Y).hom (𝟙 Z) ≫ (wedge2Assoc W (wedge2 X Y) Z).hom
        ≫ wedge2Map (𝟙 W) (wedge2Assoc X Y Z).hom
      = (wedge2Assoc (wedge2 W X) Y Z).hom ≫ (wedge2Assoc W X (wedge2 Y Z)).hom := by
  apply BPSet.hom_ext
  simp only [comp_hom, wedge2Map_hom, wedge2Assoc_hom_hom]
  refine wedge2_hom_ext (wedge2_hom_ext (wedge2_hom_ext ?_ ?_) ?_) ?_ <;> simp

/-! ### The monoidal structure -/

/-- The wedge monoidal structure, as a plain `def` on `BPSet` (not an `instance`: `BPSet` carries
no canonical product; the instance below installs it). -/
@[reducible] def wedgeMonoidalStruct : MonoidalCategoryStruct BPSet where
  tensorObj := wedge2
  tensorHom := wedge2Map
  whiskerLeft X _ _ g := wedge2Map (𝟙 X) g
  whiskerRight f Y := wedge2Map f (𝟙 Y)
  tensorUnit := □0
  associator := wedge2Assoc
  leftUnitor := wedge2LeftUnit
  rightUnitor := wedge2RightUnit

/-- The wedge `MonoidalCategory` data on `BPSet`, as a plain `def`. -/
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
