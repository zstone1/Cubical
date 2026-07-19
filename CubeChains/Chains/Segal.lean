import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Foundations.WedgeMonoidal
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Chains/Segal

`Ch : BPSet ⥤ Cat` is strong monoidal from bi-pointed sets (wedge `∨`, unit `□⁰`) to
`Cat` (product `×`, unit `𝟙`):
```
Ch X × Ch Y  ≌  Ch (wedge2 X Y)
Ch (cube 0)            ≌  Discrete PUnit
Ch (serialWedge dims)  ≌  ∏ᵢ Ch (cube (dims.get i))   (n-ary)
```
Here: the **concatenation functor** `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)`, its
faithfulness (`wedgeInclL/R` monos + adhesive pushouts), and the unit
`chUnit : Ch(□⁰) ≌ Discrete PUnit`.  Full + EssSurj live in `Chains/SegalSplit.lean`,
the assembled `chSegal` in `Chains/SegalProd.lean`.

The crux is the **Segal property**: the glue point `□⁰` has no positive-dimensional
cells, so the positive cubes of a chain through `X ∨ Y` land in *exactly one* of `X`,
`Y` — the `X`-cubes a prefix, the `Y`-cubes a suffix — and the chain splits at the
junction vertex `v` as `(chain init → v in X) ++ (chain v → final in Y)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace ChainCat

universe u

/-! ## Wedge2 functoriality and the append isomorphism -/

def serialWedge1 (n : ℕ+) : serialWedge [n] ≅ (□n) := by
    rw [serialWedge_cons, serialWedge_nil]
    exact wedge2RightUnit _

/-! ## The append isomorphism `(⋁x) ∨ (⋁y) ≅ ⋁(x ++ y)`

Purely structural, from the wedge monoidal data: `[]` is the left unitor, `n :: x'` is the
associator followed by whiskering the recursive step.  No `eqToHom` appears — `⋁(n :: l)` is
`□n ∨ ⋁l` and `(n :: x) ++ y` is `n :: (x ++ y)`, both by `rfl`.

The half-inclusions are then the two pushout legs pushed through it, so every coherence fact
about them is a restriction lemma of the *monoidal* structure rather than a `Glue.desc` chase. -/

/-- **The append isomorphism.**  `(⋁x) ∨ (⋁y) ≅ ⋁(x ++ y)`. -/
def serialWedgeAppend : ∀ (x y : List ℕ+), wedge2 (⋁x) (⋁y) ≅ ⋁(x ++ y)
  | [],      y => wedge2LeftUnit (⋁y)
  | n :: x', y =>
      wedge2Assoc (□(n : ℕ)) (⋁x') (⋁y)
        ≪≫ wedge2MapIso (Iso.refl (□(n : ℕ))) (serialWedgeAppend x' y)

/-- Forward half of the append iso. -/
def serialWedgeAppendHom (x y : List ℕ+) : wedge2 (⋁x) (⋁y) ⟶ ⋁(x ++ y) :=
  (serialWedgeAppend x y).hom

/-- The cons step at the presheaf level: associator, then the recursive step whiskered. -/
theorem serialWedgeAppendHom_cons (n : ℕ+) (x' y : List ℕ+) :
    (serialWedgeAppendHom (n :: x') y).hom
      = wedge2AssocFwd (□(n : ℕ)) (⋁x') (⋁y)
        ≫ wedge2MapPsh (𝟙 (□(n : ℕ))) (serialWedgeAppendHom x' y) := rfl

/-! ### Canonical inclusions of the two halves of an appended serial wedge

`wedgeInclL da db : □^∨(da) ⟶ □^∨(da ++ db)` includes the first `da` blocks,
`wedgeInclR da db : □^∨(db) ⟶ □^∨(da ++ db)` the last `db` blocks.  They are the two pushout
legs of `(⋁da) ∨ (⋁db)` transported along `serialWedgeAppend`. -/

/-- The left half-inclusion `□^∨(da) ⟶ □^∨(da ++ db)`. -/
def wedgeInclL (da db : List ℕ+) : (⋁da).toPsh ⟶ (⋁(da ++ db)).toPsh :=
  Glue.inl (⋁da).finalVertex (⋁db).initVertex ≫ (serialWedgeAppendHom da db).hom

/-- The right half-inclusion `□^∨(db) ⟶ □^∨(da ++ db)`. -/
def wedgeInclR (da db : List ℕ+) : (⋁db).toPsh ⟶ (⋁(da ++ db)).toPsh :=
  Glue.inr (⋁da).finalVertex (⋁db).initVertex ≫ (serialWedgeAppendHom da db).hom

/-- The junction square for the two half-inclusions of `⋁(x ++ y)`, in selector form: the
pushout `Glue.condition` pushed through the append iso. -/
theorem serialWedge_junction (x y : List ℕ+) :
    (⋁x).finalVertex ≫ wedgeInclL x y = (⋁y).initVertex ≫ wedgeInclR x y := by
  rw [wedgeInclL, wedgeInclR, ← Category.assoc, ← Category.assoc,
    Glue.condition (⋁x).finalVertex (⋁y).initVertex]

/-- The append iso descends the two half-inclusions out of the wedge. -/
@[simp] theorem serialWedgeAppendHom_hom (x y : List ℕ+) :
    (serialWedgeAppendHom x y).hom
      = Glue.desc (wedgeInclL x y) (wedgeInclR x y) (serialWedge_junction x y) :=
  Glue.hom_ext ((Glue.inl_desc _ _ _).symm) ((Glue.inr_desc _ _ _).symm)

/-- The left inclusion preserves the initial vertex (selector form). -/
theorem wedgeInclL_initVertex (da db : List ℕ+) :
    (⋁da).initVertex ≫ wedgeInclL da db = (⋁(da ++ db)).initVertex := by
  rw [wedgeInclL, ← Category.assoc, ← wedge2_initVertex]
  exact initVertex_comp_hom (serialWedgeAppendHom da db)

/-- The right inclusion preserves the final vertex (selector form). -/
theorem wedgeInclR_finalVertex (da db : List ℕ+) :
    (⋁db).finalVertex ≫ wedgeInclR da db = (⋁(da ++ db)).finalVertex := by
  rw [wedgeInclR, ← Category.assoc, ← wedge2_finalVertex]
  exact finalVertex_comp_hom (serialWedgeAppendHom da db)

/-- With an empty left word the left inclusion is the initial-vertex map. -/
theorem wedgeInclL_nil_left (db : List ℕ+) :
    wedgeInclL ([] : List ℕ+) db = (⋁db).initVertex :=
  wedge2LeftUnitPsh_inl (⋁db)

/-- With an empty left word the right inclusion is the identity. -/
theorem wedgeInclR_nil_left (db : List ℕ+) :
    wedgeInclR ([] : List ℕ+) db = 𝟙 (⋁db).toPsh :=
  wedge2LeftUnitPsh_inr (⋁db)

/-- Head-cube leg of `wedgeInclL` on a cons. -/
@[reassoc]
theorem wedgeInclL_cons_inl (n : ℕ+) (da db : List ℕ+) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁da).initVertex ≫ wedgeInclL (n :: da) db
      = Glue.inl (□(n : ℕ)).finalVertex (⋁(da ++ db)).initVertex := by
  rw [wedgeInclL, serialWedgeAppendHom_cons]
  erw [wedge2AssocFwd_inl_inl_assoc, wedge2MapPsh_inl, id_hom, Category.id_comp]

/-- Tail leg of `wedgeInclL` on a cons: the right inclusion commutes into the tail. -/
@[reassoc]
theorem wedgeInclL_cons_inr (n : ℕ+) (da db : List ℕ+) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁da).initVertex ≫ wedgeInclL (n :: da) db
      = wedgeInclL da db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da ++ db)).initVertex := by
  rw [wedgeInclL, wedgeInclL, serialWedgeAppendHom_cons]
  erw [wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2MapPsh_inr, ← Category.assoc]

/-- `wedgeInclR` on a cons: the tail inclusion followed by the head-cube right inclusion. -/
theorem wedgeInclR_cons (n : ℕ+) (da db : List ℕ+) :
    wedgeInclR (n :: da) db
      = wedgeInclR da db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da ++ db)).initVertex := by
  rw [wedgeInclR, wedgeInclR, serialWedgeAppendHom_cons]
  erw [wedge2AssocFwd_inr_assoc, Category.assoc, wedge2MapPsh_inr, ← Category.assoc]

/-- Cell-level form of `wedgeInclR_nil_left`. -/
theorem wedgeInclR_nil_left_app (db : List ℕ+) (m : ℕ) (r : (⋁db).cells m) :
    (wedgeInclR ([] : List ℕ+) db)⟪m⟫ r = r := by
  rw [wedgeInclR_nil_left]; rfl

/-- Cell-level form of `wedgeInclR_cons`. -/
theorem wedgeInclR_cons_app (n : ℕ+) (da db : List ℕ+) (m : ℕ) (r : (⋁db).cells m) :
    (wedgeInclR (n :: da) db)⟪m⟫ r
      = (Glue.inr (□(n : ℕ)).finalVertex (⋁(da ++ db)).initVertex)⟪m⟫
          ((wedgeInclR da db)⟪m⟫ r) := by
  rw [wedgeInclR_cons]; rfl

/-- `wedgeInclL` on a cons unfolds to the `Glue.desc` with head leg `inl` and
tail leg `wedgeInclL da' db ≫ inr`. -/
theorem wedgeInclL_cons (n : ℕ+) (da' db : List ℕ+) :
    wedgeInclL (n :: da') db
      = Glue.desc
          (Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex)
          (wedgeInclL da' db ≫ Glue.inr (□(n : ℕ)).finalVertex
            (⋁(da' ++ db)).initVertex)
          (by
            have h : (⋁da').initVertex ≫ wedgeInclL da' db
                ≫ Glue.inr (□(n : ℕ)).finalVertex
                  (⋁(da' ++ db)).initVertex
              = (⋁(da' ++ db)).initVertex
                ≫ Glue.inr (□(n : ℕ)).finalVertex
                  (⋁(da' ++ db)).initVertex := by
              rw [← Category.assoc, wedgeInclL_initVertex]
            exact (Glue.condition _ _).trans h.symm) :=
  Glue.hom_ext ((wedgeInclL_cons_inl n da' db).trans (Glue.inl_desc _ _ _).symm)
    ((wedgeInclL_cons_inr n da' db).trans (Glue.inr_desc _ _ _).symm)

-- Sealed past this point: `erw`'s defeq matching otherwise unfolds the inclusions into
-- `Glue.inl/inr ≫ serialWedgeAppend`, which defeats the `_cons`/`_nil_left` rewrites.
attribute [irreducible] wedgeInclL wedgeInclR

/-! ## The concatenation functor `chConcat`

We build, by direct recursion on the left dimension sequence, a "concatenation"
of two wedge maps into a common target `Z`, glued at the junction (final vertex of
the left = initial vertex of the right).  This avoids the associator entirely. -/

/-- A wedge map `□^∨(da) ⟶ Z` bundled with the values it takes on the wedge's
`init`/`final` vertices.  Threading these invariants is what discharges the cocone
condition of the `cons` step (the junction matching). -/
structure ConcatDesc {Z : PrecubicalSet} (da : List ℕ+) (s t : Z.cells 0) where
  /-- The underlying wedge map. -/
  map : (⋁da).toPsh ⟶ Z
  /-- It sends the wedge's initial vertex to `s`. -/
  init_spec : map⟪0⟫ (⋁da).init = s
  /-- It sends the wedge's final vertex to `t`. -/
  final_spec : map⟪0⟫ (⋁da).final = t

/-- **Concatenation of two wedge maps** into a common target `Z`, glued at the
junction `t = s'` (the left map's final value = the right map's initial value).
Built by recursion on `da`:

* `da = []`: `[] ++ db = db` definitionally, and the empty wedge `□⁰` sends its
  single vertex to `s = t = s'`; just return the right descriptor.
* `da = n :: da'`: `(n :: da') ++ db = n :: (da' ++ db)` definitionally, so
  `serialWedge` unfolds to `wedge2 (cube n) (serialWedge (da' ++ db))`; use
  `Glue.desc` with the head leg `inl ≫ m1` and the recursive tail. -/
def concatWedgeMap {Z : PrecubicalSet} :
    ∀ (da : List ℕ+) {s t : Z.cells 0} (_ : ConcatDesc da s t)
      (db : List ℕ+) {t' : Z.cells 0} (_ : ConcatDesc db t t'),
      ConcatDesc (da ++ db) s t'
  | [], s, t, d1, db, t', d2 =>
      -- `[] ++ db = db` definitionally.  The empty left wedge `□⁰` forces `s = t`
      -- (its init = final), so `d2`'s init value `t` is `s`.
      { map := d2.map
        init_spec := d2.init_spec.trans
          ((d1.final_spec.symm.trans
            (congrArg (d1.map⟪0⟫)
              (Subsingleton.elim (α := (□0).cells 0)
                (⋁([] : List ℕ+)).final
                (⋁([] : List ℕ+)).init))).trans d1.init_spec)
        final_spec := d2.final_spec }
  | n :: da', s, t, d1, db, t', d2 =>
      -- `(n :: da') ++ db = n :: (da' ++ db)` and `serialWedge` unfolds to
      -- `wedge2 (cube n) (serialWedge (da' ++ db))`.
      -- The left map restricted to the tail blocks of `□^∨(n::da')`.
      let d1tail : ConcatDesc da'
          ((Glue.inr (□(n : ℕ)).finalVertex
              (⋁da').initVertex ≫ d1.map)⟪0⟫
            (⋁da').init) t :=
        { map := Glue.inr (□(n : ℕ)).finalVertex
            (⋁da').initVertex ≫ d1.map
          init_spec := rfl
          final_spec := d1.final_spec }
      let rec_ := concatWedgeMap da' d1tail db d2
      { map := Glue.desc
          (Glue.inl (□(n : ℕ)).finalVertex
            (⋁da').initVertex ≫ d1.map) rec_.map (by
            -- cocone condition: head-cube final vertex glues to tail init value
            apply yonedaEquiv.injective
            simp only [yonedaEquiv_comp, finalVertex, initVertex,
              vertexMap, PrecubicalSet.cubeMap, Equiv.apply_symm_apply]
            -- LHS = d1.map (inl (cube n).final); RHS = rec_.map (serialWedge (da'++db)).init.
            refine (congrArg (d1.map⟪0⟫)
              (CubeChain.wedge2_glue (□(n : ℕ)) (⋁da'))).trans
              rec_.init_spec.symm)
        init_spec :=
          (CubeChain.inl_desc_app (f := (□(n : ℕ)).finalVertex)
            (g := (⋁(da' ++ db)).initVertex)
            (h := Glue.inl (□(n : ℕ)).finalVertex
              (⋁da').initVertex ≫ d1.map)
            (k := rec_.map) (□(n : ℕ)).init).trans d1.init_spec
        final_spec :=
          (CubeChain.inr_desc_app (f := (□(n : ℕ)).finalVertex)
            (g := (⋁(da' ++ db)).initVertex)
            (h := Glue.inl (□(n : ℕ)).finalVertex
              (⋁da').initVertex ≫ d1.map)
            (k := rec_.map) (⋁(da' ++ db)).final).trans rec_.final_spec }

/-- **Left restriction of a concatenation**: restricting `concatWedgeMap` along the
left inclusion recovers the left descriptor's map. -/
theorem concatWedgeMap_inclL {Z : PrecubicalSet} :
    ∀ (da : List ℕ+) {s t : Z.cells 0} (d1 : ConcatDesc da s t)
      (db : List ℕ+) {t' : Z.cells 0} (d2 : ConcatDesc db t t'),
      wedgeInclL da db ≫ (concatWedgeMap da d1 db d2).map = d1.map
  | [], s, t, d1, db, t', d2 => by
      -- `serialWedge [] = cube 0`; both sides are maps out of `□⁰`, equal by Yoneda.
      -- `(concatWedgeMap [] …).map = d2.map`, `wedgeInclL [] db = (serialWedge db).initVertex`.
      have hL : wedgeInclL ([] : List ℕ+) db ≫ (concatWedgeMap [] d1 db d2).map
          = (⋁db).initVertex ≫ d2.map := by rw [wedgeInclL_nil_left]; rfl
      rw [hL, initVertex, vertexMap, PrecubicalSet.cubeMap,
        yonedaEquiv_symm_naturality_right, d2.init_spec]
      -- now: `yonedaEquiv.symm t = d1.map`; `d1.map` classifies `s = t`.
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_apply,
        show (𝟙 ▫0 : ▫0 ⟶ ▫0)
          = (⋁([] : List ℕ+)).init from
          Subsingleton.elim (α := (□0).cells 0) _ _]
      -- goal: `t = d1.map (serialWedge []).init`; `= s` and `s = t`.
      refine Eq.trans ?_ d1.init_spec.symm
      -- goal: `t = s`; the empty left wedge forces `s = t`.
      exact (d1.init_spec.symm.trans ((congrArg (d1.map⟪0⟫)
        (Subsingleton.elim (α := (□0).cells 0)
          (⋁([] : List ℕ+)).init
          (⋁([] : List ℕ+)).final)).trans d1.final_spec)).symm
  | n :: da', s, t, d1, db, t', d2 => by
      -- both sides are maps out of `wedge2 (cube n) (serialWedge da')`; check on inl/inr.
      refine Glue.hom_ext ?_ ?_
      · -- head: `inl ≫ wedgeInclL = inl'`, `inl' ≫ concatMap = inl ≫ d1.map`.
        erw [← Category.assoc, wedgeInclL_cons, Glue.inl_desc]
        -- now `inl' ≫ concatMap = inl ≫ d1.map`; the desc's head leg.
        exact Glue.inl_desc _ _ _
      · -- tail: `inr ≫ wedgeInclL = wedgeInclL da' db ≫ inr'`, recurse via IH.
        erw [← Category.assoc, wedgeInclL_cons, Glue.inr_desc, Category.assoc, Glue.inr_desc]
        exact concatWedgeMap_inclL da' _ db d2

/-- **Right restriction of a concatenation**: restricting `concatWedgeMap` along the
right inclusion recovers the right descriptor's map. -/
theorem concatWedgeMap_inclR {Z : PrecubicalSet} :
    ∀ (da : List ℕ+) {s t : Z.cells 0} (d1 : ConcatDesc da s t)
      (db : List ℕ+) {t' : Z.cells 0} (d2 : ConcatDesc db t t'),
      wedgeInclR da db ≫ (concatWedgeMap da d1 db d2).map = d2.map
  | [], s, t, d1, db, t', d2 => by
      rw [wedgeInclR_nil_left]
      erw [Category.id_comp]
      rfl
  | n :: da', s, t, d1, db, t', d2 => by
      -- `wedgeInclR (n::da') db = wedgeInclR da' db ≫ inr`; `inr ≫ concatMap = rec_.map`.
      rw [wedgeInclR_cons]
      erw [Category.assoc, Glue.inr_desc]
      exact concatWedgeMap_inclR da' _ db d2

/-! ### The concatenation descriptors for a pair of chains over `X` and `Y`

`leftDesc X Y a` packages a chain `a : Obj X` as a `ConcatDesc` into `wedge2 X Y`
(via the left inclusion), `rightDesc X Y b` a chain `b : Obj Y` via the right
inclusion; their junction values match by `wedge2_glue`. -/

/-- A chain over `X`, pushed into `wedge2 X Y` along the left inclusion, as a
`ConcatDesc` running from the wedge's init vertex to the junction `inl X.final`. -/
def leftDesc (X Y : BPSet) (a : Obj X) :
    ConcatDesc a.dims (wedge2 X Y).init
      ((Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final) where
  map := a.map.hom ≫ Glue.inl X.finalVertex Y.initVertex
  init_spec := by
    erw [NatTrans.comp_app, types_comp_apply, a.map.app_init]; rfl
  final_spec := by
    erw [NatTrans.comp_app, types_comp_apply, a.map.app_final]; rfl

/-- A chain over `Y`, pushed into `wedge2 X Y` along the right inclusion, as a
`ConcatDesc` running from the junction `inl X.final` to the wedge's final vertex. -/
def rightDesc (X Y : BPSet) (b : Obj Y) :
    ConcatDesc b.dims
      ((Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final)
      (wedge2 X Y).final where
  map := b.map.hom ≫ Glue.inr X.finalVertex Y.initVertex
  init_spec := by
    erw [NatTrans.comp_app, types_comp_apply, b.map.app_init]
    exact (CubeChain.wedge2_glue X Y).symm
  final_spec := by
    erw [NatTrans.comp_app, types_comp_apply, b.map.app_final]; rfl

/-- The concatenation map of two chains as a `BPSet` morphism `□^∨(a.dims ++ b.dims)
⟶ wedge2 X Y`. -/
def concatChainMap (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    ⋁(a.dims ++ b.dims) ⟶ wedge2 X Y where
  hom := (concatWedgeMap a.dims (leftDesc X Y a) b.dims (rightDesc X Y b)).map
  app_init := (concatWedgeMap a.dims (leftDesc X Y a) b.dims (rightDesc X Y b)).init_spec
  app_final := (concatWedgeMap a.dims (leftDesc X Y a) b.dims (rightDesc X Y b)).final_spec

/-! ### The junction lemma and the two-way extensionality for appended wedges

To build `chConcat.map` we need: (A) the left inclusion's value on the *final*
vertex equals the right inclusion's value on the *init* vertex (the descriptors
match at the junction), and (B) a map out of an appended wedge is determined by its
restrictions to the two halves. -/

/-- **The junction lemma.**  In `□^∨(da ++ db)`, the left inclusion applied to
`(serialWedge da).final` equals the right inclusion applied to
`(serialWedge db).init`.  Both are the shared junction vertex. -/
theorem wedgeInclL_final_eq_wedgeInclR_init (da db : List ℕ+) :
    (wedgeInclL da db)⟪0⟫ (⋁da).final
      = (wedgeInclR da db)⟪0⟫ (⋁db).init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm ((wedgeInclL da db)⟪0⟫ (⋁da).final)
      = (⋁da).finalVertex ≫ wedgeInclL da db from
        (yonedaEquiv_symm_naturality_right ▫0 (wedgeInclL da db) (⋁da).final).symm,
    show yonedaEquiv.symm ((wedgeInclR da db)⟪0⟫ (⋁db).init)
      = (⋁db).initVertex ≫ wedgeInclR da db from
        (yonedaEquiv_symm_naturality_right ▫0 (wedgeInclR da db) (⋁db).init).symm]
  exact serialWedge_junction da db

/-- **Two-way extensionality for maps out of an appended wedge.**  A map out of
`□^∨(da ++ db)` is determined by its restrictions along the two half-inclusions
`wedgeInclL`/`wedgeInclR`. -/
theorem concat_hom_ext {Z : PrecubicalSet} : ∀ (da db : List ℕ+)
    (u v : (⋁(da ++ db)).toPsh ⟶ Z)
    (_hL : wedgeInclL da db ≫ u = wedgeInclL da db ≫ v)
    (_hR : wedgeInclR da db ≫ u = wedgeInclR da db ≫ v), u = v
  | [], db, u, v, _, hR => by
      -- `wedgeInclR [] db = 𝟙`, so `hR : u = v` after id_comp.
      rw [wedgeInclR_nil_left] at hR
      erw [Category.id_comp, Category.id_comp] at hR
      exact hR
  | n :: da', db, u, v, hL, hR => by
      -- `serialWedge (n::da'++db) = wedge2 (cube n) (serialWedge (da'++db))` (defeq).
      -- Domain pushout injections (of `wedgeInclL (n::da') db`):
      set dinl := Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex
        with hdinl
      set dinr := Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex
        with hdinr
      -- Codomain pushout injections (of `serialWedge (n::da'++db)`):
      set cinl := Glue.inl (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex with hcinl
      set cinr := Glue.inr (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex with hcinr
      -- head/tail legs of the `wedgeInclL_cons` desc:
      have hhead : dinl ≫ wedgeInclL (n :: da') db = cinl := by
        rw [hdinl, hcinl, wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htail : dinr ≫ wedgeInclL (n :: da') db = wedgeInclL da' db ≫ cinr := by
        rw [hdinr, hcinr, wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      refine Glue.hom_ext ?_ ?_
      · -- head leg: precompose hL with `dinl`, use `hhead`.
        have hh : (dinl ≫ wedgeInclL (n :: da') db) ≫ u
            = (dinl ≫ wedgeInclL (n :: da') db) ≫ v := by
          rw [Category.assoc, Category.assoc]; exact congrArg (fun t => dinl ≫ t) hL
        rw [hhead] at hh
        exact hh
      · -- tail leg: IH on da' for `cinr ≫ u = cinr ≫ v`.
        refine concat_hom_ext da' db (cinr ≫ u) (cinr ≫ v) ?_ ?_
        · -- `wedgeInclL da' db ≫ (cinr ≫ u) = wedgeInclL da' db ≫ (cinr ≫ v)`.
          have ht : (dinr ≫ wedgeInclL (n :: da') db) ≫ u
              = (dinr ≫ wedgeInclL (n :: da') db) ≫ v := by
            rw [Category.assoc, Category.assoc]; exact congrArg (fun t => dinr ≫ t) hL
          rw [htail] at ht
          simpa only [Category.assoc] using ht
        · -- `wedgeInclR da' db ≫ (cinr ≫ u) = …`; `wedgeInclR (n::da') = wedgeInclR da' ≫ cinr`.
          have hRcons : wedgeInclR (n :: da') db = wedgeInclR da' db ≫ cinr := by
            rw [hcinr]; exact wedgeInclR_cons n da' db
          rw [hRcons] at hR
          rw [← Category.assoc, ← Category.assoc]
          exact hR

/-! ### The action of `chConcat` on morphisms

A morphism `(f, g) : (a, b) ⟶ (a', b')` in `Obj X × Obj Y` is concatenated into a
refinement `□^∨(a.dims ++ b.dims) ⟶ □^∨(a'.dims ++ b'.dims)` over `wedge2 X Y`.
The two halves `f.φ`, `g.φ` are pushed into the appended target along
`wedgeInclL`/`wedgeInclR`, and glued at the junction (this is where the junction
lemma and the BPSet basepoint conditions `app_init`/`app_final` of `f.φ`, `g.φ`
enter — `f.φ`/`g.φ` are *BPSet* morphisms, hence preserve endpoints by construction). -/

/-- The left descriptor of the concatenated morphism: `f.φ` pushed into the appended
target along the left inclusion.  Its final value is the junction `wedgeInclL .final`. -/
def concatMapDescL {X Y : BPSet} {a a' : Obj X} (f : a ⟶ a') (b' : Obj Y) :
    ConcatDesc a.dims (⋁(a'.dims ++ b'.dims)).init
      ((wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final) where
  map := fᵂ ≫ wedgeInclL a'.dims b'.dims
  init_spec := by
    rw [NatTrans.comp_app, types_comp_apply, f.φ.app_init]
    exact app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)
  final_spec := by
    rw [NatTrans.comp_app, types_comp_apply, f.φ.app_final]

/-- The right descriptor of the concatenated morphism: `g.φ` pushed into the appended
target along the right inclusion.  Its initial value matches the left descriptor's
final value at the junction (junction lemma + the basepoint conditions). -/
def concatMapDescR {X Y : BPSet} (a' : Obj X) {b b' : Obj Y} (g : b ⟶ b')
    (hjunc : (gᵂ ≫ wedgeInclR a'.dims b'.dims)⟪0⟫
        (⋁b.dims).init
      = (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final) :
    ConcatDesc b.dims
      ((wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final)
      (⋁(a'.dims ++ b'.dims)).final where
  map := gᵂ ≫ wedgeInclR a'.dims b'.dims
  init_spec := hjunc
  final_spec := by
    rw [NatTrans.comp_app, types_comp_apply, g.φ.app_final]
    exact app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)

/-- The junction condition for the concatenated morphism: `g.φ` pushed in along the
right inclusion sends `b`'s init vertex to the same junction as `f.φ` pushed in along
the left inclusion sends `a'`'s final vertex.  (Junction lemma + `g.φ.app_init`.) -/
theorem concatMap_junction {X Y : BPSet} (a' : Obj X) {b b' : Obj Y} (g : b ⟶ b') :
    (gᵂ ≫ wedgeInclR a'.dims b'.dims)⟪0⟫
        (⋁b.dims).init
      = (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final := by
  rw [NatTrans.comp_app, types_comp_apply, g.φ.app_init]
  exact (wedgeInclL_final_eq_wedgeInclR_init a'.dims b'.dims).symm

/-- The underlying wedge map of the concatenated morphism `(f, g)`, as a `BPSet`
morphism `□^∨(a.dims ++ b.dims) ⟶ □^∨(a'.dims ++ b'.dims)`. -/
def concatHomφ {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    ⋁(a.dims ++ b.dims) ⟶ ⋁(a'.dims ++ b'.dims) where
  hom := (concatWedgeMap a.dims (concatMapDescL f b') b.dims
    (concatMapDescR a' g (concatMap_junction a' g))).map
  app_init := (concatWedgeMap a.dims (concatMapDescL f b') b.dims
    (concatMapDescR a' g (concatMap_junction a' g))).init_spec
  app_final := (concatWedgeMap a.dims (concatMapDescL f b') b.dims
    (concatMapDescR a' g (concatMap_junction a' g))).final_spec

/-- Left restriction of the concatenated morphism recovers `f.φ` pushed in. -/
theorem concatHomφ_inclL {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    wedgeInclL a.dims b.dims ≫ (concatHomφ f g).hom
      = fᵂ ≫ wedgeInclL a'.dims b'.dims :=
  concatWedgeMap_inclL a.dims (concatMapDescL f b') b.dims
    (concatMapDescR a' g (concatMap_junction a' g))

/-- Right restriction of the concatenated morphism recovers `g.φ` pushed in. -/
theorem concatHomφ_inclR {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    wedgeInclR a.dims b.dims ≫ (concatHomφ f g).hom
      = gᵂ ≫ wedgeInclR a'.dims b'.dims :=
  concatWedgeMap_inclR a.dims (concatMapDescL f b') b.dims
    (concatMapDescR a' g (concatMap_junction a' g))

/-- Left restriction of `concatChainMap`: it equals `leftDesc.map` (a chain pushed in
along the left wedge inclusion). -/
theorem concatChainMap_inclL (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    wedgeInclL a.dims b.dims ≫ (concatChainMap X Y a b).hom = (leftDesc X Y a).map :=
  concatWedgeMap_inclL a.dims (leftDesc X Y a) b.dims (rightDesc X Y b)

/-- Right restriction of `concatChainMap`: it equals `rightDesc.map`. -/
theorem concatChainMap_inclR (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    wedgeInclR a.dims b.dims ≫ (concatChainMap X Y a b).hom = (rightDesc X Y b).map :=
  concatWedgeMap_inclR a.dims (leftDesc X Y a) b.dims (rightDesc X Y b)

/-- The commutation triangle of the concatenated morphism over `wedge2 X Y`. -/
theorem concatHomφ_w {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    concatHomφ f g ≫ concatChainMap X Y a' b' = concatChainMap X Y a b := by
  apply hom_ext
  rw [comp_hom]
  refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
  · -- left leg
    rw [← Category.assoc, concatHomφ_inclL, Category.assoc, concatChainMap_inclL,
      concatChainMap_inclL]
    -- `fᵂ ≫ (leftDesc X Y a').map = (leftDesc X Y a).map`
    change fᵂ ≫ a'.map.hom ≫ Glue.inl X.finalVertex Y.initVertex
      = a.map.hom ≫ Glue.inl X.finalVertex Y.initVertex
    rw [← Category.assoc]
    have hw : fᵂ ≫ a'.map.hom = a.map.hom :=
      congrArg (·.hom) f.w
    rw [hw]
  · -- right leg
    rw [← Category.assoc, concatHomφ_inclR, Category.assoc, concatChainMap_inclR,
      concatChainMap_inclR]
    change gᵂ ≫ b'.map.hom ≫ Glue.inr X.finalVertex Y.initVertex
      = b.map.hom ≫ Glue.inr X.finalVertex Y.initVertex
    rw [← Category.assoc]
    have hw : gᵂ ≫ b'.map.hom = b.map.hom :=
      congrArg (·.hom) g.w
    rw [hw]

/-- The concatenated morphism of identities is the identity. -/
theorem concatHomφ_id {X Y : BPSet} (a : Obj X) (b : Obj Y) :
    concatHomφ (𝟙 a) (𝟙 b) = 𝟙 (⋁(a.dims ++ b.dims)) := by
  apply hom_ext
  refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
  · rw [concatHomφ_inclL, show Hom.φ (𝟙 a) = 𝟙 _ from id_φ a, id_hom, Category.id_comp,
      id_hom, Category.comp_id]
  · rw [concatHomφ_inclR, show Hom.φ (𝟙 b) = 𝟙 _ from id_φ b, id_hom, Category.id_comp,
      id_hom, Category.comp_id]

/-- The concatenated morphism of composites is the composite of concatenations. -/
theorem concatHomφ_comp {X Y : BPSet} {a a' a'' : Obj X} {b b' b'' : Obj Y}
    (f₁ : a ⟶ a') (f₂ : a' ⟶ a'') (g₁ : b ⟶ b') (g₂ : b' ⟶ b'') :
    concatHomφ (f₁ ≫ f₂) (g₁ ≫ g₂) = concatHomφ f₁ g₁ ≫ concatHomφ f₂ g₂ := by
  apply hom_ext
  rw [comp_hom]
  refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
  · rw [concatHomφ_inclL, show Hom.φ (f₁ ≫ f₂) = f₁.φ ≫ f₂.φ from comp_φ f₁ f₂, comp_hom]
    -- RHS: `wedgeInclL a.dims ≫ ((concatHomφ f₁ g₁).hom ≫ (concatHomφ f₂ g₂).hom)`.
    rw [← Category.assoc (wedgeInclL a.dims b.dims), concatHomφ_inclL]
    simp only [Category.assoc]
    rw [concatHomφ_inclL]
  · rw [concatHomφ_inclR, show Hom.φ (g₁ ≫ g₂) = g₁.φ ≫ g₂.φ from comp_φ g₁ g₂, comp_hom]
    rw [← Category.assoc (wedgeInclR a.dims b.dims), concatHomφ_inclR]
    simp only [Category.assoc]
    rw [concatHomφ_inclR]

/-- **The concatenation functor** `Obj X × Obj Y ⥤ Obj (wedge2 X Y)`: it appends the
two dimension sequences and glues the two classifying maps along the junction. -/
def chConcat (X Y : BPSet) : Obj X × Obj Y ⥤ Obj (wedge2 X Y) where
  obj ab := ⟨ab.1.dims ++ ab.2.dims, concatChainMap X Y ab.1 ab.2⟩
  map {ab ab'} fg := ⟨concatHomφ fg.1 fg.2, concatHomφ_w fg.1 fg.2⟩
  map_id ab := by
    apply hom_ext'
    exact concatHomφ_id ab.1 ab.2
  map_comp {ab ab' ab''} fg fg' := by
    apply hom_ext'
    exact concatHomφ_comp fg.1 fg'.1 fg.2 fg'.2

@[simp] theorem chConcat_obj_dims (X Y : BPSet) (ab : Obj X × Obj Y) :
    ((chConcat X Y).obj ab).dims = ab.1.dims ++ ab.2.dims := rfl

@[simp] theorem chConcat_map_φ {X Y : BPSet} {ab ab' : Obj X × Obj Y} (fg : ab ⟶ ab') :
    Hom.φ ((chConcat X Y).map fg) = concatHomφ fg.1 fg.2 := rfl

/-! ### `chConcat` is faithful

The two wedge-half inclusions are monomorphisms (`PrecubicalSet` is adhesive, and
the vertex maps `□⁰ ⟶ ·` are monos because `□⁰` is pointwise a subsingleton), so
restricting `concatHomφ` along them via `concatHomφ_inclL`/`_inclR` recovers each
component map; faithfulness follows. -/

/-- The cons step of `wedgeInclL` sits in a pushout square: it is the right leg of the
square `[dinr, wedgeInclL da' db; wedgeInclL (n::da') db, cinr]`.  Obtained from the
defining (domain) pushout pasted under the target square, via `IsPushout.of_top`. -/
theorem wedgeInclL_cons_isPushout (n : ℕ+) (da' db : List ℕ+) :
    IsPushout (Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex)
      (wedgeInclL da' db) (wedgeInclL (n :: da') db)
      (Glue.inr (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex) := by
  set cinl := Glue.inl (□(n : ℕ)).finalVertex
    (⋁(da' ++ db)).initVertex
  set cinr := Glue.inr (□(n : ℕ)).finalVertex
    (⋁(da' ++ db)).initVertex
  set dinl := Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex
  set dinr := Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex
  -- the two desc legs of `wedgeInclL_cons`:
  have hhead : dinl ≫ wedgeInclL (n :: da') db = cinl := by
    rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _
  have htail : dinr ≫ wedgeInclL (n :: da') db = wedgeInclL da' db ≫ cinr := by
    rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _
  -- domain pushout (cons):
  have hdom : IsPushout (□(n : ℕ)).finalVertex (⋁da').initVertex
      dinl dinr := Glue.isPushout _ _
  -- codomain pushout, with left leg refactored through `wedgeInclL da' db`:
  have hcod : IsPushout (□(n : ℕ)).finalVertex
      ((⋁da').initVertex ≫ wedgeInclL da' db)
      (dinl ≫ wedgeInclL (n :: da') db) cinr := by
    rw [wedgeInclL_initVertex da' db, hhead]
    exact Glue.isPushout _ _
  exact hcod.of_top htail hdom

instance wedgeInclL_mono : ∀ (da db : List ℕ+), Mono (wedgeInclL da db)
  | [], db => by
      rw [wedgeInclL_nil_left]
      exact CubeChain.initVertex_mono _
  | n :: da', db => by
      have : Mono (wedgeInclL da' db) := wedgeInclL_mono da' db
      exact Adhesive.mono_of_isPushout_of_mono_right (wedgeInclL_cons_isPushout n da' db)

/-- The right half-inclusion `wedgeInclR` is a mono. -/
instance wedgeInclR_mono : ∀ (da db : List ℕ+), Mono (wedgeInclR da db)
  | [], db => by
      rw [wedgeInclR_nil_left]
      exact inferInstanceAs (Mono (𝟙 (⋁db).toPsh))
  | n :: da', db => by
      rw [wedgeInclR_cons]
      have hm1 : Mono (wedgeInclR da' db) := wedgeInclR_mono da' db
      have hm2 : Mono (Glue.inr (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex) :=
        CubeChain.wedge2_inr_mono (□(n : ℕ)) (⋁(da' ++ db))
      exact @mono_comp _ _ _ _ _ _ hm1 _ hm2

instance (X Y : BPSet) : (chConcat X Y).Faithful where
  map_injective {ab ab'} fg fg' h := by
    -- `concatHomφ fg.1 fg.2 = concatHomφ fg'.1 fg'.2`; restrict along the inclusions.
    have hφ : concatHomφ fg.1 fg.2 = concatHomφ fg'.1 fg'.2 := congrArg Hom.φ h
    have hφhom : (concatHomφ fg.1 fg.2).hom = (concatHomφ fg'.1 fg'.2).hom :=
      congrArg (·.hom) hφ
    -- left component: cancel the mono `wedgeInclL`.
    have hL : (fg.1)ᵂ ≫ wedgeInclL ab'.1.dims ab'.2.dims
        = (fg'.1)ᵂ ≫ wedgeInclL ab'.1.dims ab'.2.dims := by
      rw [← concatHomφ_inclL, ← concatHomφ_inclL, hφhom]
    have h1 : (fg.1)ᵂ = (fg'.1)ᵂ := (cancel_mono _).mp hL
    -- right component: cancel the mono `wedgeInclR`.
    have hR : (fg.2)ᵂ ≫ wedgeInclR ab'.1.dims ab'.2.dims
        = (fg'.2)ᵂ ≫ wedgeInclR ab'.1.dims ab'.2.dims := by
      rw [← concatHomφ_inclR, ← concatHomφ_inclR, hφhom]
    have h2 : (fg.2)ᵂ = (fg'.2)ᵂ := (cancel_mono _).mp hR
    -- assemble the product morphism.
    have e1 : fg.1 = fg'.1 := hom_ext' (hom_ext h1)
    have e2 : fg.2 = fg'.2 := hom_ext' (hom_ext h2)
    exact Prod.ext e1 e2

/-! ## The monoidal unit: `Ch(□⁰) ≌ 𝟙`

The point `□⁰` has no positive-dimensional cells, so the only chain in it is the
empty chain; and maps `□⁰ ⟶ □⁰` are rigid.  Hence `Ch(□⁰)` is the terminal
(one-object, one-morphism) category, equivalent to `Discrete PUnit`. -/

/-- A chain in the point `□⁰` has empty dimension sequence (a positive block would
contribute a positive cell to `□⁰`, of which there are none). -/
theorem obj_cube0_dims_nil (a : Obj (□0)) : a.dims = [] := by
  obtain ⟨dims, map⟩ := a
  cases dims with
  | nil => rfl
  | cons n rest =>
      -- block `0` is a cube of dimension `n ≥ 1` in `□⁰`, impossible.
      exfalso
      have hcell : (□0).cells (n : ℕ) :=
        yonedaEquiv (ιᵂ (n :: rest) 0 ≫ map.hom)
      exact (CubeChain.cube0_cells_isEmpty (m := (n : ℕ)) n.2).false hcell

/-- `BPSet` maps `□⁰ ⟶ □⁰` are unique (the underlying presheaf map is rigid; the
basepoint conditions are proof-irrelevant). -/
instance bpCube0_hom_subsingleton :
    Subsingleton (⋁([] : List ℕ+) ⟶ ⋁([] : List ℕ+)) := by
  constructor
  intro f g
  apply hom_ext
  apply yonedaEquiv.injective
  exact Subsingleton.elim (α := (□0).cells 0) _ _

/-- The canonical empty chain in `□⁰`. -/
instance : Inhabited (Obj (□0)) :=
  ⟨⟨[], ⟨𝟙 _, rfl, rfl⟩⟩⟩

/-- Two chains in `□⁰` are equal (both are the empty chain). -/
theorem obj_cube0_eq (a b : Obj (□0)) : a = b := by
  obtain ⟨da, ma⟩ := a
  obtain ⟨db, mb⟩ := b
  obtain rfl : da = [] := obj_cube0_dims_nil ⟨da, ma⟩
  obtain rfl : db = [] := obj_cube0_dims_nil ⟨db, mb⟩
  refine congrArg (Obj.mk []) (hom_ext ?_)
  apply yonedaEquiv.injective
  exact Subsingleton.elim (α := (□0).cells 0) _ _

/-- **`Ch(□⁰)` is a thin category**: with both dimension sequences forced to `[]`, the
underlying wedge map `□⁰ ⟶ □⁰` is rigid, so each hom-set is a subsingleton. -/
instance homCube0_subsingleton : Quiver.IsThin (Obj (□0)) := by
  rintro ⟨da, ma⟩ ⟨db, mb⟩
  obtain rfl : da = [] := obj_cube0_dims_nil ⟨da, ma⟩
  obtain rfl : db = [] := obj_cube0_dims_nil ⟨db, mb⟩
  constructor
  intro f g
  apply hom_ext'
  exact Subsingleton.elim f.φ g.φ

/-- Every hom-set of `Ch(□⁰)` is inhabited (both objects are the empty chain). -/
instance homCube0_inhabited (a b : Obj (□0)) : Inhabited (a ⟶ b) := by
  obtain rfl := obj_cube0_eq a b
  exact ⟨𝟙 a⟩

instance : (Functor.star (Obj (□0))).Faithful where
  map_injective {_ _} f g _ := Subsingleton.elim f g

instance : (Functor.star (Obj (□0))).Full where
  map_surjective {_ _} _ := ⟨default, Subsingleton.elim _ _⟩

instance : (Functor.star (Obj (□0))).EssSurj where
  mem_essImage Y := ⟨default, ⟨(Functor.star (Obj (□0))).punitExt
    ((Functor.const _).obj Y) |>.app default⟩⟩

instance : (Functor.star (Obj (□0))).IsEquivalence where

/-- **The monoidal unit.** `Ch(□⁰)` is equivalent to the terminal category
`Discrete PUnit`: it has one object (the empty chain) and one morphism.  The inverse is the
constant functor at the empty chain (no `Classical.choice`, unlike `Functor.star.asEquivalence`). -/
def chUnit : Obj (□0) ≌ Discrete PUnit.{u + 1} :=
  CategoryTheory.Equivalence.mk (Functor.star (Obj (□0)))
    ((Functor.const _).obj default)
    (NatIso.ofComponents (fun a => eqToIso (obj_cube0_eq a default))
      (fun _ => Subsingleton.elim _ _))
    (Functor.punitExt _ _)

/-! ## Concluding the Segal equivalence `chSegal`

`chConcat X Y` is faithful.  Its other two halves — **fullness** and **essential
surjectivity** (the *Segal splitting* of a chain through `X ∨ Y` into an `X`-prefix and a
`Y`-suffix) — reduce to `chain_split`/`chConcat_map_surjective` (`Chains/SegalSplit.lean`).
`Chains/SegalProd.lean` assembles those into `chSegal X Y : Ch X × Ch Y ≌ Ch(X ∨ Y)` and the
n-ary `chSegalProd`.

GOTCHA: the splitting is subtle because a chain may re-cross the junction; block
monotonicity is what rules that out. -/

end ChainCat
