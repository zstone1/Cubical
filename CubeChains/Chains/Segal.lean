import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Foundations.WedgeMonoidal
import CubeChains.Foundations.MonoidalTransport
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Chains/Segal

The monoidal side of the cube-chain category: the append isomorphism
`serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)` with its coherence, `⋁` as a **strong monoidal**
functor `DimList ⥤ BPSet` carrying that as tensorator, the **concatenation functor**
`chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` with its faithfulness (`wedgeInclL/R` monos +
adhesive pushouts), and the unit `chUnit : Ch(□⁰) ≌ Discrete PUnit`.

`serialWedgeAppend` is built only from `λ_`, `α_` and whiskering, so its coherence *is*
pentagon and triangle rather than a pushout chase — which is why the strong monoidal structure
at the end of the file is a transcription and not a proof.

That `chConcat` is an *equivalence* is the Segal property, and it belongs to the splitting:
`Chains/Split.lean`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite BPSet CubeChain

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

/-! ## Coherence of the append isomorphism

`serialWedgeAppend` is assembled only from `λ_`, `α_` and left whiskering, so its associativity
and unit squares are *pentagon + associator naturality* and the *triangle* family in disguise.
Each inductive step closes with mathlib's `monoidal`, in monoidal notation on `BPSet`. -/

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

theorem serialWedgeAssocBP_cons (n : ℕ+) (x y z : List ℕ+) :
    serialWedgeAssocBP (n :: x) y z = (□(n : ℕ)) ◁ serialWedgeAssocBP x y z :=
  serialWedge_eqToHom_cons n (List.append_assoc x y z)

/-- The `List.append_nil` reindexing as a `BPSet` morphism. -/
def serialWedgeNilBP (x : List ℕ+) : ⋁(x ++ ([] : List ℕ+)) ⟶ ⋁x :=
  eqToHom (congrArg BPSet.serialWedge (List.append_nil x))

theorem serialWedgeNilBP_cons (n : ℕ+) (x : List ℕ+) :
    serialWedgeNilBP (n :: x) = (□(n : ℕ)) ◁ serialWedgeNilBP x :=
  serialWedge_eqToHom_cons n (List.append_nil x)

/-- **Associativity of the append iso**, in monoidal notation.  Induction on `x`: the base case
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
      exact whiskerLeft_assoc_step _ _ _ _ ih

/-- **Right unitality of the append iso**, in monoidal notation. -/
theorem serialWedgeAppendIso_right_unitality : ∀ x : List ℕ+,
    serialWedgeAppendHom x ([] : List ℕ+) ≫ serialWedgeNilBP x = (ρ_ (⋁x)).hom
  | [] => by
      change (λ_ (𝟙_ BPSet)).hom ≫ 𝟙 (𝟙_ BPSet) = (ρ_ (𝟙_ BPSet)).hom
      monoidal
  | n :: x' => by
      have ih := serialWedgeAppendIso_right_unitality x'
      rw [serialWedgeAppendHom_cons', serialWedgeNilBP_cons]
      exact whiskerLeft_rightUnit_step _ _ ih

/-! ### Canonical inclusions of the two halves of an appended serial wedge

`wedgeInclL da db : □^∨(da) ⟶ □^∨(da ++ db)` includes the first `da` blocks,
`wedgeInclR da db : □^∨(db) ⟶ □^∨(da ++ db)` the last `db` blocks.  They are the two pushout
legs of `(⋁da) ∨ (⋁db)` transported along `serialWedgeAppend`. -/

/-- The left half-inclusion `□^∨(da) ⟶ □^∨(da ++ db)`. -/
def wedgeInclL (da db : List ℕ+) : (⋁da).toPsh ⟶ (⋁(da ++ db)).toPsh :=
  wedgeInl (⋁da) (⋁db) ≫ (serialWedgeAppendHom da db).hom

/-- The right half-inclusion `□^∨(db) ⟶ □^∨(da ++ db)`. -/
def wedgeInclR (da db : List ℕ+) : (⋁db).toPsh ⟶ (⋁(da ++ db)).toPsh :=
  wedgeInr (⋁da) (⋁db) ≫ (serialWedgeAppendHom da db).hom

/-- The left inclusion preserves the initial vertex (selector form). -/
theorem wedgeInclL_initVertex (da db : List ℕ+) :
    (⋁da).initVertex ≫ wedgeInclL da db = (⋁(da ++ db)).initVertex := by
  rw [wedgeInclL, ← Category.assoc, ← wedge2_initVertex]
  exact initVertex_comp_hom (serialWedgeAppendHom da db)

/-- With an empty left word the left inclusion is the initial-vertex map. -/
theorem wedgeInclL_nil_left (db : List ℕ+) :
    wedgeInclL ([] : List ℕ+) db = (⋁db).initVertex :=
  wedge2LeftUnitPsh_inl (⋁db)

/-- With an empty left word the right inclusion is the identity. -/
theorem wedgeInclR_nil_left (db : List ℕ+) :
    wedgeInclR ([] : List ℕ+) db = 𝟙 (⋁db).toPsh :=
  wedge2LeftUnitPsh_inr (⋁db)

/-- `wedgeInclL`/`wedgeInclR` on a cons, with the head wedge `⋁(n :: da)` folded to
`□n ∨ ⋁da`.  Both spellings are `rfl` (`serialWedge_cons`), but the gap sits in the *object*
argument of the ambient `≫`, which no rewrite can target — hence the `show`, which restates
the whole composite in one spelling and lets the associator restriction lemmas match. -/
@[reassoc]
theorem wedgeInclL_cons_inl (n : ℕ+) (da db : List ℕ+) :
    wedgeInl (□(n : ℕ)) (⋁da) ≫ wedgeInclL (n :: da) db
      = wedgeInl (□(n : ℕ)) (⋁(da ++ db)) := by
  rw [wedgeInclL, serialWedgeAppendHom_cons]
  change wedgeInl (□(n : ℕ)) (⋁da) ≫ wedgeInl ((□(n : ℕ)) ∨ ⋁da) (⋁db)
      ≫ wedge2AssocFwd (□(n : ℕ)) (⋁da) (⋁db)
      ≫ wedge2MapPsh (𝟙 (□(n : ℕ))) (serialWedgeAppendHom da db) = _
  rw [wedge2AssocFwd_inl_inl_assoc, wedge2MapPsh_inl, id_hom, Category.id_comp]

/-- Tail leg of `wedgeInclL` on a cons: the right inclusion commutes into the tail. -/
@[reassoc]
theorem wedgeInclL_cons_inr (n : ℕ+) (da db : List ℕ+) :
    wedgeInr (□(n : ℕ)) (⋁da) ≫ wedgeInclL (n :: da) db
      = wedgeInclL da db ≫ wedgeInr (□(n : ℕ)) (⋁(da ++ db)) := by
  rw [wedgeInclL, wedgeInclL, serialWedgeAppendHom_cons]
  change wedgeInr (□(n : ℕ)) (⋁da) ≫ wedgeInl ((□(n : ℕ)) ∨ ⋁da) (⋁db)
      ≫ wedge2AssocFwd (□(n : ℕ)) (⋁da) (⋁db)
      ≫ wedge2MapPsh (𝟙 (□(n : ℕ))) (serialWedgeAppendHom da db) = _
  rw [wedge2AssocFwd_inr_inl_assoc, Category.assoc, wedge2MapPsh_inr, ← Category.assoc]

/-- `wedgeInclR` on a cons: the tail inclusion followed by the head-cube right inclusion. -/
@[reassoc]
theorem wedgeInclR_cons (n : ℕ+) (da db : List ℕ+) :
    wedgeInclR (n :: da) db
      = wedgeInclR da db ≫ wedgeInr (□(n : ℕ)) (⋁(da ++ db)) := by
  rw [wedgeInclR, wedgeInclR, serialWedgeAppendHom_cons]
  change wedgeInr ((□(n : ℕ)) ∨ ⋁da) (⋁db)
      ≫ wedge2AssocFwd (□(n : ℕ)) (⋁da) (⋁db)
      ≫ wedge2MapPsh (𝟙 (□(n : ℕ))) (serialWedgeAppendHom da db) = _
  rw [wedge2AssocFwd_inr_assoc, Category.assoc, wedge2MapPsh_inr, ← Category.assoc]

/-- `wedgeInclL` on a cons unfolds to the `Glue.desc` with head leg `inl` and
tail leg `wedgeInclL da' db ≫ inr`. -/
theorem wedgeInclL_cons (n : ℕ+) (da' db : List ℕ+) :
    wedgeInclL (n :: da') db
      = Glue.desc
          (wedgeInl (□(n : ℕ)) (⋁(da' ++ db)))
          (wedgeInclL da' db ≫ wedgeInr (□(n : ℕ)) (⋁(da' ++ db)))
          (by
            have h : (⋁da').initVertex ≫ wedgeInclL da' db
                ≫ wedgeInr (□(n : ℕ)) (⋁(da' ++ db))
              = (⋁(da' ++ db)).initVertex
                ≫ wedgeInr (□(n : ℕ)) (⋁(da' ++ db)) := by
              rw [← Category.assoc, wedgeInclL_initVertex]
            exact (Glue.condition _ _).trans h.symm) :=
  Glue.hom_ext ((wedgeInclL_cons_inl n da' db).trans (Glue.inl_desc _ _ _).symm)
    ((wedgeInclL_cons_inr n da' db).trans (Glue.inr_desc _ _ _).symm)

/-! ### The half-inclusions against the append iso

The four lemmas that survive the `irreducible` seal below: each half-inclusion *is* a pushout leg
followed by `μ = serialWedgeAppendHom`, and cancels `μ⁻¹` back to that leg.  Everything about
`concatChainMap`/`concatHomφ` is these plus the tensor bifunctor. -/

/-- The append iso cancels, at the presheaf level (`BPSet` composition is componentwise, so this
is `Iso.hom_inv_id` with `.hom` applied — but stated so `rw` matches the presheaf `≫`). -/
theorem appendHom_comp_appendInv (da db : List ℕ+) :
    (serialWedgeAppendHom da db).hom ≫ (serialWedgeAppend da db).inv.hom
      = 𝟙 (wedge2 (⋁da) (⋁db)).toPsh :=
  congrArg BPSet.Hom.hom (serialWedgeAppend da db).hom_inv_id

@[reassoc]
theorem inl_comp_appendHom (da db : List ℕ+) :
    wedgeInl (⋁da) (⋁db) ≫ (serialWedgeAppendHom da db).hom
      = wedgeInclL da db := rfl

@[reassoc]
theorem inr_comp_appendHom (da db : List ℕ+) :
    wedgeInr (⋁da) (⋁db) ≫ (serialWedgeAppendHom da db).hom
      = wedgeInclR da db := rfl

@[reassoc]
theorem wedgeInclL_appendInv (da db : List ℕ+) :
    wedgeInclL da db ≫ (serialWedgeAppend da db).inv.hom
      = wedgeInl (⋁da) (⋁db) := by
  rw [wedgeInclL, Category.assoc]
  rw [appendHom_comp_appendInv, Category.comp_id]

@[reassoc]
theorem wedgeInclR_appendInv (da db : List ℕ+) :
    wedgeInclR da db ≫ (serialWedgeAppend da db).inv.hom
      = wedgeInr (⋁da) (⋁db) := by
  rw [wedgeInclR, Category.assoc]
  rw [appendHom_comp_appendInv, Category.comp_id]

-- Sealed past this point: `erw`'s defeq matching otherwise unfolds the inclusions into
-- `Glue.inl/inr ≫ serialWedgeAppend`, which defeats the `_cons`/`_nil_left` rewrites.
attribute [irreducible] wedgeInclL wedgeInclR

/-! ### The cocycle laws for the half-inclusions

`⋁(- ++ -)` with `wedgeInclL`/`wedgeInclR` is a system of coherent inclusions on lists: the three
laws below are `serialWedgeAppendIso_assoc` restricted along the three pushout legs
`inl≫inl`, `inr≫inl`, `inr` of `(⋁x ∨ ⋁y) ∨ ⋁z`, and the fourth is
`serialWedgeAppendIso_right_unitality` along `inl`.

```
          wedgeInclL x y        wedgeInclL (x++y) z
    ⋁x ───────────────→ ⋁(x++y) ──────────────────→ ⋁((x++y)++z)
      ╲                                                     │
        ╲  wedgeInclL x (y++z)                    assoc     │
          ╲                                                 ↓
            ────────────────────────────────────→  ⋁(x++(y++z))
``` -/

/-- The wedge associator at presheaf level — the spelling the restriction lemmas key on. -/
private theorem wedgeAssoc_hom_hom (a b c : BPSet) :
    (α_ a b c).hom.hom = wedge2AssocFwd a b c := rfl

/-- The associativity coherence of `serialWedgeAppend`, read at presheaf level. -/
private theorem appendIso_assoc_psh (x y z : List ℕ+) :
    wedge2MapPsh (serialWedgeAppendHom x y) (𝟙 (⋁z))
        ≫ (serialWedgeAppendHom (x ++ y) z).hom ≫ (serialWedgeAssocBP x y z).hom
      = wedge2AssocFwd (⋁x) (⋁y) (⋁z)
        ≫ wedge2MapPsh (𝟙 (⋁x)) (serialWedgeAppendHom y z)
          ≫ (serialWedgeAppendHom x (y ++ z)).hom := by
  have hE := congrArg BPSet.Hom.hom (serialWedgeAppendIso_assoc x y z)
  simpa only [comp_hom, whiskerRight, whiskerLeft, wedge2Map_hom, wedgeAssoc_hom_hom] using hE

/-! ## The concatenation functor `chConcat`

Concatenation is the **monoidal comma** construction over the append iso `μ = serialWedgeAppend`:
on objects `(a, b) ↦ (a.dims ++ b.dims, μ⁻¹ ≫ (a.map ⊗ₘ b.map))`, on morphisms
`(f, g) ↦ μ⁻¹ ≫ (f.φ ⊗ₘ g.φ) ≫ μ`.  Every law below is a `MonoidalTransport` fact plus the four
half-inclusion lemmas above. -/

/-- **The concatenation map of two chains** `⋁(a.dims ++ b.dims) ⟶ X ∨ Y`: untwist the append
iso, then tensor the two classifying maps. -/
def concatChainMap (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    ⋁(a.dims ++ b.dims) ⟶ wedge2 X Y :=
  (serialWedgeAppend a.dims b.dims).inv ≫ (a.map ⊗ₘ b.map)

theorem concatChainMap_hom (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    (concatChainMap X Y a b).hom
      = (serialWedgeAppend a.dims b.dims).inv.hom ≫ wedge2MapPsh a.map b.map := rfl

/-- Left restriction of `concatChainMap`: the chain `a`, pushed into `X ∨ Y` along `inl`. -/
theorem concatChainMap_inclL (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    wedgeInclL a.dims b.dims ≫ (concatChainMap X Y a b).hom
      = a.map.hom ≫ wedgeInl X Y := by
  rw [concatChainMap_hom, wedgeInclL_appendInv_assoc]
  exact wedge2MapPsh_inl a.map b.map

/-- Right restriction of `concatChainMap`: the chain `b`, pushed into `X ∨ Y` along `inr`. -/
theorem concatChainMap_inclR (X Y : BPSet) (a : Obj X) (b : Obj Y) :
    wedgeInclR a.dims b.dims ≫ (concatChainMap X Y a b).hom
      = b.map.hom ≫ wedgeInr X Y := by
  rw [concatChainMap_hom, wedgeInclR_appendInv_assoc]
  exact wedge2MapPsh_inr a.map b.map

/-! ### The junction lemma and two-way extensionality for appended wedges -/

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
      simpa using hR
  | n :: da', db, u, v, hL, hR => by
      -- `serialWedge (n::da'++db) = wedge2 (cube n) (serialWedge (da'++db))` (defeq).
      -- Domain pushout injections (of `wedgeInclL (n::da') db`):
      set dinl := wedgeInl (□(n : ℕ)) (⋁da')
        with hdinl
      set dinr := wedgeInr (□(n : ℕ)) (⋁da')
        with hdinr
      -- Codomain pushout injections (of `serialWedge (n::da'++db)`):
      set cinl := wedgeInl (□(n : ℕ)) (⋁(da' ++ db)) with hcinl
      set cinr := wedgeInr (□(n : ℕ)) (⋁(da' ++ db)) with hcinr
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

A morphism `(f, g) : (a, b) ⟶ (a', b')` in `Obj X × Obj Y` is concatenated by transporting
`f.φ ⊗ₘ g.φ` across the append iso.  The junction bookkeeping is carried by the tensor: `⊗ₘ` is
the *bi-pointed* wedge of morphisms, so the endpoint conditions come for free. -/

/-- The underlying wedge map of the concatenated morphism `(f, g)`: the tensor `f.φ ⊗ₘ g.φ`
transported across the append iso. -/
def concatHomφ {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    ⋁(a.dims ++ b.dims) ⟶ ⋁(a'.dims ++ b'.dims) :=
  (serialWedgeAppend a.dims b.dims).inv ≫ (f.φ ⊗ₘ g.φ)
    ≫ serialWedgeAppendHom a'.dims b'.dims

theorem concatHomφ_hom {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    (concatHomφ f g).hom
      = (serialWedgeAppend a.dims b.dims).inv.hom ≫ wedge2MapPsh f.φ g.φ
        ≫ (serialWedgeAppendHom a'.dims b'.dims).hom := rfl

/-- Left restriction of the concatenated morphism recovers `f.φ` pushed in. -/
theorem concatHomφ_inclL {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    wedgeInclL a.dims b.dims ≫ (concatHomφ f g).hom
      = fᵂ ≫ wedgeInclL a'.dims b'.dims := by
  rw [concatHomφ_hom, wedgeInclL_appendInv_assoc]
  rw [wedge2MapPsh_inl_assoc, inl_comp_appendHom]

/-- Right restriction of the concatenated morphism recovers `g.φ` pushed in. -/
theorem concatHomφ_inclR {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    wedgeInclR a.dims b.dims ≫ (concatHomφ f g).hom
      = gᵂ ≫ wedgeInclR a'.dims b'.dims := by
  rw [concatHomφ_hom, wedgeInclR_appendInv_assoc]
  rw [wedge2MapPsh_inr_assoc, inr_comp_appendHom]

/-- The commutation triangle of the concatenated morphism over `wedge2 X Y`. -/
theorem concatHomφ_w {X Y : BPSet} {a a' : Obj X} {b b' : Obj Y}
    (f : a ⟶ a') (g : b ⟶ b') :
    concatHomφ f g ≫ concatChainMap X Y a' b' = concatChainMap X Y a b := by
  have h : concatHomφ f g ≫ concatChainMap X Y a' b'
      = (serialWedgeAppend a.dims b.dims).inv ≫ ((f.φ ≫ a'.map) ⊗ₘ (g.φ ≫ b'.map)) :=
    tensorTransport_comp_tensorHom _ _ f.φ g.φ a'.map b'.map
  rw [h, f.w, g.w]
  rfl

/-- The concatenated morphism of identities is the identity. -/
theorem concatHomφ_id {X Y : BPSet} (a : Obj X) (b : Obj Y) :
    concatHomφ (𝟙 a) (𝟙 b) = 𝟙 (⋁(a.dims ++ b.dims)) :=
  tensorTransport_id (serialWedgeAppend a.dims b.dims)

/-- The concatenated morphism of composites is the composite of concatenations. -/
theorem concatHomφ_comp {X Y : BPSet} {a a' a'' : Obj X} {b b' b'' : Obj Y}
    (f₁ : a ⟶ a') (f₂ : a' ⟶ a'') (g₁ : b ⟶ b') (g₂ : b' ⟶ b'') :
    concatHomφ (f₁ ≫ f₂) (g₁ ≫ g₂) = concatHomφ f₁ g₁ ≫ concatHomφ f₂ g₂ :=
  tensorTransport_comp (serialWedgeAppend a.dims b.dims) (serialWedgeAppend a'.dims b'.dims)
    (serialWedgeAppend a''.dims b''.dims) f₁.φ f₂.φ g₁.φ g₂.φ

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
    IsPushout (wedgeInr (□(n : ℕ)) (⋁da'))
      (wedgeInclL da' db) (wedgeInclL (n :: da') db)
      (wedgeInr (□(n : ℕ)) (⋁(da' ++ db))) := by
  set cinl := wedgeInl (□(n : ℕ)) (⋁(da' ++ db))
  set cinr := wedgeInr (□(n : ℕ)) (⋁(da' ++ db))
  set dinl := wedgeInl (□(n : ℕ)) (⋁da')
  set dinr := wedgeInr (□(n : ℕ)) (⋁da')
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
      have hm2 : Mono (wedgeInr (□(n : ℕ)) (⋁(da' ++ db))) :=
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



/-- **`wedgeToCubes` of an appended serial wedge splits** as the append of the two
half-restrictions along `wedgeInclL`/`wedgeInclR`. -/
theorem wedgeToCubes_append {K : BPSet} :
    ∀ (da db : List ℕ+) (φ : (⋁(da ++ db)).toPsh ⟶ K.toPsh),
      wedgeToCubes ⟨da ++ db, φ⟩
        = wedgeToCubes ⟨da, wedgeInclL da db ≫ φ⟩ ++ wedgeToCubes ⟨db, wedgeInclR da db ≫ φ⟩
  | [], db, φ => by
      change wedgeToCubes ⟨db, φ⟩
          = wedgeToCubes ⟨([] : List ℕ+), wedgeInclL [] db ≫ φ⟩
            ++ wedgeToCubes ⟨db, wedgeInclR [] db ≫ φ⟩
      rw [wedgeInclR_nil_left]
      simp only [wedgeToCubes, List.nil_append, Category.id_comp]
  | n :: da', db, φ => by
      simp only [wedgeToCubes, List.cons_append]
      set cinr := Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex with hcinr
      have hhead : Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex ≫ wedgeInclL (n :: da') db
          = Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := by
        rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htail : Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex ≫ wedgeInclL (n :: da') db
          = wedgeInclL da' db ≫ cinr := by rw [hcinr, wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      refine congr_arg₂ List.cons ?_ ?_
      · exact congrArg (fun z => (⟨n, yonedaEquiv z⟩ : Σ m : ℕ+, K.cells (m : ℕ)))
          (((Category.assoc _ (wedgeInclL (n :: da') db) φ).symm.trans
            (congrArg (· ≫ φ) hhead)).symm)
      · refine (wedgeToCubes_append da' db (cinr ≫ φ)).trans (congr_arg₂ (· ++ ·)
          (congrArg (fun m => wedgeToCubes ⟨da', m⟩) ?_)
          (congrArg (fun m => wedgeToCubes ⟨db, m⟩) ?_))
        · exact ((Category.assoc _ cinr φ).symm.trans (congrArg (· ≫ φ) htail.symm)).trans
            (Category.assoc _ (wedgeInclL (n :: da') db) φ)
        · exact (Category.assoc _ cinr φ).symm.trans
            (congrArg (· ≫ φ) (wedgeInclR_cons n da' db).symm)



/-! ## `⋁` as a strong monoidal functor

Dimension sequences form the free monoid on `ℕ+`; as a discrete monoidal category its tensor is
`List.append` and its unit `[]`.  `⋁` carries that to `(BPSet, ∨, □0)` — strongly, with the append
iso as tensorator.  The three coherences are the lemmas already proved above, in exactly the shape
`CoreMonoidal` asks for, so the assembly below is a transcription. -/

/-- Dimension sequences as a discrete monoidal category: tensor is append, unit is `[]`. -/
abbrev DimList := Discrete (FreeMonoid ℕ+)

/-- `⋁` as a functor on dimension sequences.  The source is discrete, so there is nothing to say
about morphisms. -/
def serialWedgeFunctor : DimList ⥤ BPSet := Discrete.functor BPSet.serialWedge

@[simp] theorem serialWedgeFunctor_obj (X : DimList) :
    serialWedgeFunctor.obj X = ⋁X.as := rfl

/-- **`⋁` is strong monoidal.**  Tensorator `serialWedgeAppend`, unit `⋁[] = □0` on the nose. -/
def serialWedgeCoreMonoidal : serialWedgeFunctor.CoreMonoidal where
  εIso := Iso.refl (𝟙_ BPSet)
  μIso X Y := serialWedgeAppend X.as Y.as
  μIso_hom_natural_left {X Y} f X' := by
    obtain rfl : X = Y := Discrete.ext (Discrete.eq_of_hom f)
    rw [Subsingleton.elim f (𝟙 X)]; simp
  μIso_hom_natural_right {X Y} X' f := by
    obtain rfl : X = Y := Discrete.ext (Discrete.eq_of_hom f)
    rw [Subsingleton.elim f (𝟙 X)]; simp
  associativity X Y Z := serialWedgeAppendIso_assoc X.as Y.as Z.as
  left_unitality X := by
    have hmu : (serialWedgeAppend (𝟙_ DimList).as X.as).hom = (λ_ (⋁X.as)).hom := rfl
    have hmap : serialWedgeFunctor.map (λ_ X).hom = 𝟙 (⋁X.as) := rfl
    rw [hmu, hmap]; monoidal
  right_unitality X := by
    have hmu : (serialWedgeAppend X.as (𝟙_ DimList).as).hom = serialWedgeAppendHom X.as [] := rfl
    have hmap : serialWedgeFunctor.map (ρ_ X).hom = serialWedgeNilBP X.as := rfl
    change (ρ_ (⋁X.as)).hom = _
    rw [hmu, hmap, ← serialWedgeAppendIso_right_unitality X.as]
    monoidal

instance : serialWedgeFunctor.Monoidal := serialWedgeCoreMonoidal.toMonoidal

end ChainCat
