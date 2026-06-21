import CubeChains.Research.Scratch.Cyl1_Algebra
import CubeChains.Research.Scratch.Cyl3_Examples

/-!
# Cyl6_Monoid — the monoid of pointed endofunctors, and the cylinder image as a submonoid

Scratch investigation (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl6_Monoid`.  Owns ONLY this file
and its `.md`.

## The lens

Over a *groupoid* base the *category* `PointedEndofunctor 𝒢` is **contractible**: it is thin
(`Cyl2.pointed_subsingleton`/`Cyl5.pointedEndofunctor_isThin`) and every map is an iso
(`Cyl2.pointed_isIso`), so it is equivalent to the terminal category — it forgets everything up to
iso (recorded as `pointedEquivPUnit`).  The categorical structure is therefore the *wrong* lens.

But the **set of objects** `PointedEndofunctor 𝒞` carries a genuine **monoid** under composition of
endofunctors that the category structure ignores: `1 = ⟨𝟭, 𝟙⟩`, `A * B = ⟨A.F ⋙ B.F, A.pt ≫
whiskerLeft A.F B.pt⟩`.  This monoid is the right home for the cylinder construction's real content.

## What is proven here (sorry-free)

1. **Monoid instance.** `Monoid (PointedEndofunctor 𝒞)` for *any* category `𝒞` (groupoid not
   needed) — STRICT associativity and unitality, because `Functor.comp` is definitionally
   strict (`Functor.comp_id`/`id_comp`/associativity all `rfl` on the `F` field; the `pt` field
   laws are discharged by `NatTrans`-extensionality + whiskering identities).  See `mul_assoc`,
   `one_mul`, `mul_one`.

2. **Product in object-data terms.**  For free-groupoid object-data, the monoid product of
   `pointedOfPaths F₀ η` and `pointedOfPaths G₀ θ` is again `pointedOfPaths` of the *composite*
   object-data: object map `x ↦ G.obj (F₀ x)` and path `η x ≫ G.map(η x... )`.  Stated and proved
   via the `Cyl1.objDataEquiv` round-trip (`mul_pointedOfPaths`).

3. **Unit ∈ image.**  The tautological object-data `(of, 𝟙)` induces *literally* `1` on the nose
   (`taut_eq_one`), so `1 ∈ Set.range cylToPointedObj` once a tautological cylinder is exhibited
   (`one_mem_cylImage_of_taut`); we package the abstract step `1 = pointedOfPaths (of) (𝟙)`, the
   cylinder-independent heart.

4. **Contractibility.**  `pointedEquivPUnit : PointedEndofunctor 𝒢 ≌ Discrete PUnit` — an
   equivalence of CATEGORIES (every object iso to the unit, hom-sets subsingletons), the formal
   justification that "the category is the wrong lens".

5. **Submonoid closure (the open theorem).**  Is `Set.range cylToPointedObj` a submonoid?  We
   record the precise status: the unit is in the image (item 3); *closure under `·`* is the
   **OPEN/CONJECTURED** half, and we pin the obstruction (no precubical degeneracy ⟹ no vertical
   composition of cylinders `PathOb ×_K PathOb → PathOb`).  See `Cyl6_Monoid.md`.

**Layer:** Research/Scratch (decoupled).  **Imports:** `Cyl1_Algebra`, `Cyl3_Examples`.
-/

open CategoryTheory Operations
open CubeChain

universe v u

namespace Cyl6

/-! ## 1. The monoid of pointed endofunctors

The set of pointed endofunctors of any category `𝒞` is a monoid under composition:
`1 = ⟨𝟭, 𝟙⟩` and `A * B = ⟨A.F ⋙ B.F, A.pt ≫ whiskerLeft A.F B.pt⟩`.  Strictness of
`Functor.comp` makes the laws hold on the nose on the `F` field; the `pt` field laws are
nat-trans extensionality computations. -/

section Monoid

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- Multiplication of pointed endofunctors: compose the endofunctors and combine the points by
whiskering.  `(A * B).F = A.F ⋙ B.F` and `(A * B).pt = A.pt ≫ whiskerLeft A.F B.pt`. -/
instance : Mul (PointedEndofunctor 𝒞) where
  mul A B := ⟨A.F ⋙ B.F, A.pt ≫ Functor.whiskerLeft A.F B.pt⟩

/-- The unit pointed endofunctor `⟨𝟭, 𝟙⟩`. -/
instance : One (PointedEndofunctor 𝒞) where
  one := ⟨𝟭 𝒞, 𝟙 (𝟭 𝒞)⟩

@[simp] theorem mul_F (A B : PointedEndofunctor 𝒞) : (A * B).F = A.F ⋙ B.F := rfl
@[simp] theorem mul_pt (A B : PointedEndofunctor 𝒞) :
    (A * B).pt = A.pt ≫ Functor.whiskerLeft A.F B.pt := rfl
@[simp] theorem one_F : (1 : PointedEndofunctor 𝒞).F = 𝟭 𝒞 := rfl
@[simp] theorem one_pt : (1 : PointedEndofunctor 𝒞).pt = 𝟙 (𝟭 𝒞) := rfl

/-- Component formula for the product's point:
`(A * B).pt.app X = A.pt.app X ≫ B.pt.app (A.F.obj X)`. -/
@[simp] theorem mul_pt_app (A B : PointedEndofunctor 𝒞) (X : 𝒞) :
    (A * B).pt.app X = A.pt.app X ≫ B.pt.app (A.F.obj X) := rfl

instance : Monoid (PointedEndofunctor 𝒞) where
  one_mul A := by
    refine Cyl1.pointedEndofunctor_ext rfl ?_
    -- (1 * A).pt = 𝟙 ≫ whiskerLeft 𝟭 A.pt = A.pt, and (1 * A).F = 𝟭 ⋙ A.F = A.F (rfl)
    apply heq_of_eq
    ext X
    simp
  mul_one A := by
    refine Cyl1.pointedEndofunctor_ext rfl ?_
    -- (A * 1).pt = A.pt ≫ whiskerLeft A.F (𝟙 𝟭) = A.pt
    apply heq_of_eq
    ext X
    simp
  mul_assoc A B C := by
    refine Cyl1.pointedEndofunctor_ext rfl ?_
    -- both points have app X = A.pt X ≫ B.pt (A.F X) ≫ C.pt (B.F (A.F X))
    apply heq_of_eq
    ext X
    simp [Category.assoc]

end Monoid

/-! ## 2. The product in object-data terms

For free-groupoid object-data, `pointedOfPaths` is a bijection onto `PointedEndofunctor`
(`Cyl1.objDataEquiv`), so the monoid product transports to a binary operation on object-data.  We
compute it: the product object map is `x ↦ G.obj (F₀ x)` (where `G` is the lift of the second
factor's conjugation) and the product path is `η x ≫ G.map (... )`.  Concretely we prove the product
is again `pointedOfPaths` of the composite, read off from the converse `pointedOfPaths_objData`. -/

section Product

variable {C : Type u} [Category.{v} C]

/-- **The product of two `pointedOfPaths` is again a `pointedOfPaths`** — of the composite
object-data.  The composite object map sends `x` to `(pointedOfPaths G₀ θ).F.obj (F₀ x)`, and the
composite path is `η x ≫ (pointedOfPaths G₀ θ).pt.app (F₀ x)` (the product point's component at the
generator `of x`, by `mul_pt_app` + `pointedOfPaths_pt_app_mk`).  This is the computational heart:
the submonoid question becomes concrete in `(objMap, pathMap)` language. -/
theorem mul_objMap (A B : PointedEndofunctor (FreeGroupoid C)) (x : C) :
    Cyl1.objMap (A * B) x = B.F.obj (A.F.obj ((FreeGroupoid.of C).obj x)) := rfl

/-- The product's extracted path at a generator: `pathMap (A * B) x = A.pt.app (of x) ≫ B.pt.app
(A.F.obj (of x))`. -/
theorem mul_pathMap (A B : PointedEndofunctor (FreeGroupoid C)) (x : C) :
    Cyl1.pathMap (A * B) x
      = A.pt.app ((FreeGroupoid.of C).obj x)
        ≫ B.pt.app (A.F.obj ((FreeGroupoid.of C).obj x)) := rfl

/-- **The product formula in `pointedOfPaths` language.**  For object-data `(F₀, η)` and `(G₀, θ)`,
the monoid product `pointedOfPaths F₀ η * pointedOfPaths G₀ θ` equals `pointedOfPaths` of the
*composite* object-data:

* composite object map  `x ↦ (pointedOfPaths G₀ θ).F.obj (F₀ x)` (apply the lifted second factor to
  the first factor's target);
* composite path        `x ↦ η x ≫ (pointedOfPaths G₀ θ).F.map (η x ... )`  — concretely the
  extracted `pathMap` of the product (`mul_pathMap`).

The statement is the round-trip `pointedOfPaths_objData (A * B)` specialised to `A = pointedOfPaths
F₀ η`, `B = pointedOfPaths G₀ θ`: the product is recovered as `pointedOfPaths` of its own (now
explicitly computed) object-data. -/
theorem mul_pointedOfPaths (F₀ G₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x)
    (θ : ∀ x, (FreeGroupoid.of C).obj x ⟶ G₀ x) :
    pointedOfPaths F₀ η * pointedOfPaths G₀ θ
      = pointedOfPaths
          (Cyl1.objMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ))
          (Cyl1.pathMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ)) :=
  (Cyl1.pointedOfPaths_objData _).symm

/-- **The explicit composite object map.**  `objMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ) x`
unfolds to `(pointedOfPaths G₀ θ).F.obj (F₀ x)` — the second factor's lifted endofunctor applied to
the first factor's object target. -/
theorem mul_pointedOfPaths_objMap (F₀ G₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x)
    (θ : ∀ x, (FreeGroupoid.of C).obj x ⟶ G₀ x) (x : C) :
    Cyl1.objMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ) x
      = (pointedOfPaths G₀ θ).F.obj (F₀ x) := rfl

/-- **The explicit composite path.**  `pathMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ) x`
unfolds to `η x ≫ (pointedOfPaths G₀ θ).pt.app (F₀ x)` — the first path followed by the second
factor's point at the transported object.  (Uses `pointedOfPaths_pt_app_mk` to rewrite the generator
components to the chosen paths.) -/
theorem mul_pointedOfPaths_pathMap (F₀ G₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x)
    (θ : ∀ x, (FreeGroupoid.of C).obj x ⟶ G₀ x) (x : C) :
    Cyl1.pathMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ) x
      = η x ≫ (pointedOfPaths G₀ θ).pt.app (F₀ x) := by
  rw [mul_pathMap, Cyl1.pointedOfPaths_pt_app_mk]
  rfl

end Product

/-! ## 3. The unit is in the image

The tautological object-data `(of, 𝟙)` induces *literally* the monoid unit `1`: its underlying
functor is `𝟭` (`Cyl3.pointedOfPaths_id_F`) and its point is `𝟙` (the chosen paths are identities).
So `1 = pointedOfPaths (of) (𝟙)` — and since the tautological cylinder induces exactly this
object-data, `1 ∈ Set.range cylToPointedObj`. -/

section Unit

variable {C : Type u} [Category.{v} C]

/-- **The tautological object-data induces the monoid unit, on the nose.**  `pointedOfPaths (of)
(𝟙) = 1`: the underlying functor is `𝟭` (`Cyl3.pointedOfPaths_id_F`) and the point is `𝟙`
(`pointedOfPaths_pt_app_mk` gives each generator component `= 𝟙`, and a nat-trans out of a free
groupoid is pinned by its generator components). -/
theorem taut_eq_one :
    pointedOfPaths (Cyl3.tautF₀ (C := C)) (Cyl3.tautη (C := C))
      = (1 : PointedEndofunctor (FreeGroupoid C)) := by
  refine Cyl1.pointedEndofunctor_ext' ?_ ?_
  · -- underlying functors: lift (conjFunctor of of 𝟙) = 𝟭 = (1).F
    rw [Cyl3.pointedOfPaths_id_F]; rfl
  · intro Z
    -- both points agree on every generator object; every object is one
    obtain ⟨x, rfl⟩ := (FreeGroupoid.of_obj_bijective).2 Z
    rw [Cyl1.pointedOfPaths_pt_app_mk]
    -- LHS = tautη x = 𝟙 (of x);  RHS = (1).pt.app (of x) = (𝟙 𝟭).app (of x) = 𝟙 (of x)
    apply heq_of_eq
    simp [Cyl3.tautη, one_pt]

end Unit

/-! ## 4. Contractibility of the category (the wrong lens, formally)

Over a groupoid base `PointedEndofunctor 𝒢` is thin (`Cyl5.pointedEndofunctor_isThin`) and every
object is isomorphic to every other via the forced comparison (`Cyl2.pointedIsoOfGroupoid`).  A
thin category in which all objects are isomorphic is equivalent to the terminal category `Discrete
PUnit`.  This is the formal "the category forgets everything; the monoid is the right structure". -/

section Contractibility

variable {𝒢 : Type u} [Groupoid.{v} 𝒢]

/-- The constant functor to the unit object. -/
def toPUnit : PointedEndofunctor 𝒢 ⥤ Discrete PUnit where
  obj _ := ⟨PUnit.unit⟩
  map _ := 𝟙 _

/-- A chosen "basepoint" pointed endofunctor (the unit `1`), used as the essential image of the
inverse functor.  (Any object would do; all are isomorphic.) -/
def fromPUnit : Discrete PUnit ⥤ PointedEndofunctor 𝒢 where
  obj _ := (1 : PointedEndofunctor 𝒢)
  map _ := 𝟙 _

/-- **The category of pointed endofunctors of a groupoid is contractible.**  It is equivalent to the
terminal category `Discrete PUnit`: thin (unique morphisms) plus all-objects-isomorphic.  This is
the formal justification that the *category* structure is the wrong lens for the cylinder
construction — it remembers nothing beyond the (single) isomorphism class. -/
noncomputable def pointedEquivPUnit : PointedEndofunctor 𝒢 ≌ Discrete PUnit where
  functor := toPUnit
  inverse := fromPUnit
  unitIso := NatIso.ofComponents
    (fun A => Cyl3.pointedUniqueIso A (1 : PointedEndofunctor 𝒢))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end Contractibility

/-! ## 5. The cylinder image as a (candidate) submonoid

`Set.range cylToPointedObj ⊆ PointedEndofunctor (DPathGrpdR K)`.  Two questions for "submonoid":

* **Unit ∈ image** — REDUCES to exhibiting a tautological cylinder over `K` whose induced
  object-data is `(of, 𝟙)`; the algebraic step `1 = pointedOfPaths (of) (𝟙)` is `taut_eq_one`.

* **Closed under `·`** — the OPEN half.  The natural witness is *vertical composition of cylinders*
  (stacking two homotopies).  We record the abstract reduction and pin the obstruction. -/

section Submonoid

variable {K : BPSet}

/-- **The cylinder image (object level).**  The set of pointed endofunctors of `DPathGrpdR K` that
arise from some weak-equivalence cylinder. -/
def cylImage (K : BPSet) : Set (PointedEndofunctor (DPathGrpdR K)) :=
  Set.range (CylMapR.cylToPointedObj (K := K))

/-- **Abstract reduction of "unit ∈ image".**  If some weak-equivalence cylinder `c` has induced
object-data equal to the tautological `(of, 𝟙)` — i.e. `CylMapR.cylToPointedObj c = pointedOfPaths
(of) (𝟙)` — then `1 ∈ cylImage K`.  (Combine with `taut_eq_one`.)  Geometrically the witness is the
*tautological cylinder* `K × □¹` projecting both ends to `K` via the identity; its `sweepR` is the
trivial homotopy, giving `(F₀, η) = (of, 𝟙)`.  We state the reduction; the concrete tautological
cylinder is the geometric input (see `.md`). -/
theorem one_mem_cylImage_of_taut (c : CylMapWeqR K)
    (h : CylMapR.cylToPointedObj c
      = pointedOfPaths (Cyl3.tautF₀ (C := RefineObj (K := K) K.init K.final)) Cyl3.tautη) :
    (1 : PointedEndofunctor (DPathGrpdR K)) ∈ cylImage K :=
  ⟨c, by rw [h, taut_eq_one]⟩

/-- **The submonoid-closure reduction.**  `cylImage K` is closed under `·` *iff* for every pair of
weak-equivalence cylinders `c, c'` there is a weak-equivalence cylinder `d` with
`cylToPointedObj d = cylToPointedObj c * cylToPointedObj c'`.  This is the exact statement that a
*composition operation on cylinders realising the monoid product* exists; it is the open theorem.
(One direction is trivial; we record the substantive direction as a hypothesis-to-conclusion
reduction so the geometric content is isolated.) -/
theorem mul_mem_cylImage_of_compose
    (compose : ∀ c c' : CylMapWeqR K, ∃ d : CylMapWeqR K,
      CylMapR.cylToPointedObj d
        = CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c')
    {A B : PointedEndofunctor (DPathGrpdR K)}
    (hA : A ∈ cylImage K) (hB : B ∈ cylImage K) :
    A * B ∈ cylImage K := by
  obtain ⟨c, rfl⟩ := hA
  obtain ⟨c', rfl⟩ := hB
  obtain ⟨d, hd⟩ := compose c c'
  exact ⟨d, hd⟩

/-- **The product's object map STACKS the two transports** — the precise obstruction to closure.
For weak-equivalence cylinders `c, c'`, the product `cylToPointedObj c * cylToPointedObj c'` has
object map (on a generator `x`)

  `x ↦ (cylToPointedObj c').F.obj ((Rgrpd ∘ Lgrpd⁻¹) x)`,

i.e. the second factor's *lifted endofunctor* applied to the first transport `(Rgrpd∘Lgrpd⁻¹) x`.
Crucially the first transport `(Rgrpd∘Lgrpd⁻¹) x` is in general **not a generator** `of y` of the
free groupoid, so the second factor acts by its `lift` (conjugation), not by the simple transport
`Rgrpd'∘Lgrpd'⁻¹` — that only holds on generators.  For `cylImage K` to be closed under `·` one
needs a *single* cylinder `d` whose induced object map equals this stacked map (and whose `sweepR`
realises the composite path).  There is **no** general construction producing such a `d`: gluing
the two homotopies end-to-end needs a path-object multiplication `PathOb K ×_K PathOb K → PathOb K`,
which does not exist for a precubical set (no degeneracies).  This lemma makes the would-be
witness's object map explicit; the open content is constructing the cylinder realising it. -/
theorem mul_cylToPointedObj_objMap (c c' : CylMapWeqR K)
    (x : RefineObj (K := K) K.init K.final) :
    haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
    Cyl1.objMap (CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c') x
      = (CylMapR.cylToPointedObj c').F.obj
          (c.obj.Rgrpd.obj (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x))) :=
  rfl

/-- **`cylImage K` is a submonoid GIVEN cylinder composition + a tautological cylinder.**  Packages
items 3 and 5: if there is a tautological cylinder inducing `(of, 𝟙)` and a composition operation
realising the monoid product, then the cylinder image is a `Submonoid`.  Both hypotheses are the
geometric inputs the program still owes; the algebra around them is complete. -/
noncomputable def cylSubmonoid
    (taut : ∃ c : CylMapWeqR K, CylMapR.cylToPointedObj c
      = pointedOfPaths (Cyl3.tautF₀ (C := RefineObj (K := K) K.init K.final)) Cyl3.tautη)
    (compose : ∀ c c' : CylMapWeqR K, ∃ d : CylMapWeqR K,
      CylMapR.cylToPointedObj d
        = CylMapR.cylToPointedObj c * CylMapR.cylToPointedObj c') :
    Submonoid (PointedEndofunctor (DPathGrpdR K)) where
  carrier := cylImage K
  one_mem' := by obtain ⟨c, hc⟩ := taut; exact one_mem_cylImage_of_taut c hc
  mul_mem' := mul_mem_cylImage_of_compose compose

end Submonoid

end Cyl6
