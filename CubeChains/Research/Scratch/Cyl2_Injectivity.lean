import CubeChains.Cylinder.CylinderRefine

/-!
# Cyl2_Injectivity — fibers of `cylToPointedR`, its universal property, and the `η`-constraint

Scratch investigation (decoupled from the green build; build with
`lake build CubeChains.Research.Scratch.Cyl2_Injectivity`).  Owns ONLY this file and its `.md`.

Three questions (user items 0 and 3):

* **(A) What does the construction remember / forget?**  `cylToPointedObj c` is
  `pointedOfPaths F₀ η` with `F₀ x = Rgrpd (Lgrpd⁻¹ (of x))` and
  `η x = counit.inv (of x) ≫ sweepR (Lgrpd⁻¹ (of x)).as.as`.  We pin down that the *only*
  data of `c` seen by the construction is the pair `(F₀, η)` — everything else of the cylinder
  (its source, the higher cells of `cyl`, …) is forgotten.

* **(B) Fibers / collision condition.**  We prove a clean sufficient condition for two cylinders
  to induce the *same* pointed endofunctor (the kernel of `cylToPointedObj` on objects).

* **(C) Constraint on the points `η x` (item 3).**  Each `η x` is *not* an arbitrary
  free-groupoid word.  We isolate the structural class `OfClosure` (the wide subgroupoid generated
  by `FreeGroupoid.of` of genuine `ChainRefine` arrows, closed under `id`/`comp`/`inv`/`eqToHom`)
  and prove that every staircase ingredient — `sweepR`, hence every `η x` *up to the equivalence
  counit* — lies in it.  This is the precise "no formal inverse except the counit correction"
  statement.

See `Cyl2_Injectivity.md` for the prose writeup (asked / proven / conjectured / open).
-/

open CategoryTheory Opposite
open Operations
open CubeChain

namespace Cyl2

/-! ## (A)+(B) The kernel of `pointedOfPaths` and the collision condition

`pointedOfPaths` is a function of exactly its two arguments `(F₀, η)`.  So its fiber over a
pointed endofunctor is "equal object-data up to the dependent equality of `η`".  The next lemma is
that congruence: it is the rigorous form of "the construction remembers only `(F₀, η)`". -/

variable {C : Type*} [Category C]

/-- **Kernel of `pointedOfPaths` on object-data.**  `pointedOfPaths` depends on *nothing* but its
two arguments: if the object maps `F₀` agree and the chosen paths `η` agree (`HEq`, since their
type mentions `F₀`), the two pointed endofunctors are *literally equal*.  This is the precise sense
in which the cylinder ⟹ pointed-functor construction **forgets everything except `(F₀, η)`**. -/
theorem pointedOfPaths_congr
    {F₀ F₀' : C → FreeGroupoid C}
    {η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x}
    {η' : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀' x}
    (hF : F₀ = F₀') (hη : HEq η η') :
    pointedOfPaths F₀ η = pointedOfPaths F₀' η' := by
  subst hF
  obtain rfl : η = η' := eq_of_heq hη
  rfl

/-- A frequently-usable specialization: when the two object maps are *definitionally* the same, a
plain (non-`HEq`) equality of the path families forces a collision. -/
theorem pointedOfPaths_congr_of_eq
    {F₀ : C → FreeGroupoid C}
    {η η' : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x}
    (hη : η = η') :
    pointedOfPaths F₀ η = pointedOfPaths F₀ η' := by rw [hη]

end Cyl2

/-! ## The cylinder-level collision condition

`cylToPointedObj c = pointedOfPaths (F₀ c) (η c)` where

* `F₀ c x = c.Rgrpd.obj (c.Lgrpd.inv.obj (of x))`,
* `η c x  = (c.Lgrpd counit).inv (of x) ≫ sweepR c (Lgrpd.inv (of x)).as.as`.

So two weak-equivalence cylinders collide as soon as these two families agree.  We package the
object-data of a cylinder, then read off the collision lemma from `pointedOfPaths_congr`. -/

namespace CylMapR

open CubeChain

variable {K : BPSet}

/-- The object map `F₀` of the pointed endofunctor of a weak-equivalence cylinder. -/
noncomputable def ptObj (c : CylMapWeqR K) :
    RefineObj (K := K) K.init K.final → DPathGrpdR K :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  fun x => c.obj.Rgrpd.obj (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x))

/-- The chosen-path map `η` of the pointed endofunctor of a weak-equivalence cylinder. -/
noncomputable def ptHom (c : CylMapWeqR K) :
    ∀ x, (FreeGroupoid.of _).obj x ⟶ ptObj c x :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  fun x => c.obj.Lgrpd.asEquivalence.counitIso.inv.app ((FreeGroupoid.of _).obj x)
    ≫ c.obj.sweepR (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)).as.as

/-- `cylToPointedObj` is `pointedOfPaths` of exactly `(ptObj, ptHom)` (definitional unfolding). -/
theorem cylToPointedObj_eq_pointedOfPaths (c : CylMapWeqR K) :
    cylToPointedObj c = pointedOfPaths (ptObj c) (ptHom c) := rfl

/-- **Cylinder collision (sufficient condition).**  Two weak-equivalence cylinders induce the
SAME pointed endofunctor whenever their object maps `ptObj` agree and their chosen paths `ptHom`
agree (`HEq`).  This is the kernel of `cylToPointedObj` on objects, transported through
`pointedOfPaths_congr`.  Geometrically: *equal transported legs* (`F₀`) plus *homotopic
transported sweeps* (`η`) ⟹ identical endofunctor — so the cylinder's source and the higher
data of `cyl` beyond these are forgotten. -/
theorem cylToPointedObj_eq_of (c c' : CylMapWeqR K)
    (hF : ptObj c = ptObj c') (hη : HEq (ptHom c) (ptHom c')) :
    cylToPointedObj c = cylToPointedObj c' := by
  rw [cylToPointedObj_eq_pointedOfPaths, cylToPointedObj_eq_pointedOfPaths]
  exact Cyl2.pointedOfPaths_congr hF hη

end CylMapR

/-! ## (C) The constraint on the points `η x` (user item 3)

The induced points `η x = counit.inv ≫ sweepR …` are **not** arbitrary free-groupoid words.
`sweepR` is assembled entirely from:

* `FreeGroupoid.of.map` of genuine `ChainRefine` arrows (the bridge cofaces — *positive*, forward
  refinements);
* `Groupoid.inv` of such (the `Groupoid.inv top`/`Groupoid.inv topc` in the staircase);
* `eqToHom` of object (cube-list) identities;
* `FreeGroupoid.map` of the `appendLeft` whiskering functor; and
* composition.

We make "lies in the subgroupoid generated by genuine refinements" precise with the wide
inductive predicate `OfClosure`, and prove `sweepR` (hence `η` up to the counit) lies in it.  The
only *formal* inverse a point ever needs is the equivalence counit `Lgrpd⁻¹`'s `counit.inv`; the
geometry itself contributes only `of`-arrows, their inverses, and `eqToHom`. -/

namespace Cyl2

variable {C : Type*} [Category C]

/-- **The `of`-closure.**  The smallest wide subgroupoid-membership predicate on morphisms of a
free groupoid that contains every `(FreeGroupoid.of C).map f` (a genuine forward arrow), every
`eqToHom h` (object identity), and is closed under composition and `Groupoid.inv`.  A morphism in
`OfClosure` is, up to reassociation and the harmless `eqToHom` object bookkeeping, a *zigzag of
genuine `C`-arrows* — i.e. it uses **no formal inverse beyond inverting actual arrows**. -/
inductive OfClosure : {X Y : FreeGroupoid C} → (X ⟶ Y) → Prop
  | of_map {X Y : C} (f : X ⟶ Y) : OfClosure ((FreeGroupoid.of C).map f)
  | eqToHom {X Y : FreeGroupoid C} (h : X = Y) : OfClosure (eqToHom h)
  | comp {X Y Z : FreeGroupoid C} {f : X ⟶ Y} {g : Y ⟶ Z} :
      OfClosure f → OfClosure g → OfClosure (f ≫ g)
  | inv {X Y : FreeGroupoid C} {f : X ⟶ Y} : OfClosure f → OfClosure (Groupoid.inv f)

/-- Identities are in the closure (as `eqToHom rfl`). -/
theorem OfClosure.id (X : FreeGroupoid C) : OfClosure (𝟙 X) := by
  simp only [← eqToHom_refl]; exact OfClosure.eqToHom (rfl : X = X)

/-- **The closure is preserved by `FreeGroupoid.map`.**  A free-groupoid word built from genuine
`C`-arrows maps, under `FreeGroupoid.map φ`, to a word built from genuine `D`-arrows — the
whiskering `lifted` in the staircase therefore stays in the closure.  Base cases: `of.map f ↦
of.map (φ.map f)` (by `of_comp_map`); `eqToHom ↦ eqToHom` (`Functor.map_eqToHom`); inv/comp by
functoriality (`Functor.map_inv` via `Groupoid.inv_eq_inv`). -/
theorem OfClosure.map {D : Type*} [Category D] (φ : C ⥤ D)
    {X Y : FreeGroupoid C} {f : X ⟶ Y} (hf : OfClosure f) :
    OfClosure ((FreeGroupoid.map φ).map f) := by
  induction hf with
  | of_map g =>
      have : (FreeGroupoid.map φ).map ((FreeGroupoid.of C).map g)
          = (FreeGroupoid.of D).map (φ.map g) := by
        have h := Functor.congr_hom (FreeGroupoid.of_comp_map φ) g
        simp only [Functor.comp_map] at h
        exact h
      rw [this]; exact OfClosure.of_map _
  | eqToHom h => rw [eqToHom_map]; exact OfClosure.eqToHom _
  | comp _ _ ih₁ ih₂ => rw [Functor.map_comp]; exact OfClosure.comp ih₁ ih₂
  | inv _ ih =>
      rw [Groupoid.inv_eq_inv, Functor.map_inv, ← Groupoid.inv_eq_inv]
      exact OfClosure.inv ih

end Cyl2

namespace CylMapR

open CubeChain Cyl2

variable {K : BPSet}

/-- Every `FreeGroupoid.of.map` of a `ChainRefine` arrow is in the closure (a genuine forward
refinement). -/
theorem ofClosure_of_refine {a b : K.toPsh.cells 0} {x y : RefineObj (K := K) a b}
    (r : x ⟶ y) : OfClosure ((FreeGroupoid.of _).map r) := OfClosure.of_map r

/-- **The total sweep lies in the `of`-closure.**  `sweepFirst`, `sweepTail` and hence `sweepR`
are built only from `eqToHom`s, `FreeGroupoid.of.map` of genuine `ChainRefine` arrows (the bridge
cofaces `botArrow*`/`topArrow`/`topCofaceFirst`), their `Groupoid.inv`s, the whiskering
`FreeGroupoid.map (appendLeft …)` (`OfClosure.map`), and composition — all closure operations.  So
every staircase homotopy is a *zigzag of genuine refinements*: it never uses a formal inverse
except by inverting an actual refinement arrow. -/
theorem ofClosure_sweepTail (c : CylMapR K) :
    ∀ (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0) (h : BlockConsec bs mL mR),
      OfClosure (sweepTail bs mL mR h)
  | [], mL, mR, h => by
      unfold sweepTail; exact OfClosure.eqToHom _
  | B :: rest, mL, mR, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL; subst huR
      -- the recursive tail, lifted by the `lc`-prefix whiskering, is in the closure
      have htail : OfClosure
          ((FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
            (sweepTail rest B.vL B.vR hrec)) :=
        OfClosure.map _ (ofClosure_sweepTail c rest B.vL B.vR hrec)
      unfold sweepTail
      -- the `mid` arrow splits on `rest`; both branches are `eqToHom ≫ of.map (bridge coface)`
      cases rest with
      | nil =>
          exact OfClosure.comp (OfClosure.eqToHom _) (OfClosure.comp htail
            (OfClosure.comp (OfClosure.comp (OfClosure.eqToHom _) (OfClosure.of_map _))
              (OfClosure.comp (OfClosure.inv (OfClosure.of_map _)) (OfClosure.eqToHom _))))
      | cons B' tl =>
          exact OfClosure.comp (OfClosure.eqToHom _) (OfClosure.comp htail
            (OfClosure.comp (OfClosure.comp (OfClosure.eqToHom _) (OfClosure.of_map _))
              (OfClosure.comp (OfClosure.inv (OfClosure.of_map _)) (OfClosure.eqToHom _))))

/-- The top-level whole-chain sweep `sweepFirst` is in the `of`-closure (same staircase
ingredients, with the first block lifted by a single top coface instead of a bridge). -/
theorem ofClosure_sweepFirst (c : CylMapR K) :
    ∀ (bs : List (BlockRec c)) (mL : K.toPsh.cells 0) (h : BlockConsec bs mL mL),
      OfClosure (sweepFirst bs mL h)
  | [], mL, h => by unfold sweepFirst; exact OfClosure.eqToHom _
  | B :: rest, mL, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL
      have htail : OfClosure
          ((FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
            (sweepTail rest B.vL B.vR hrec)) :=
        OfClosure.map _ (ofClosure_sweepTail c rest B.vL B.vR hrec)
      unfold sweepFirst
      cases rest with
      | nil =>
          exact OfClosure.comp (OfClosure.eqToHom _) (OfClosure.comp htail
            (OfClosure.comp (OfClosure.comp (OfClosure.eqToHom _) (OfClosure.of_map _))
              (OfClosure.comp (OfClosure.inv (OfClosure.of_map _)) (OfClosure.eqToHom _))))
      | cons B' tl =>
          exact OfClosure.comp (OfClosure.eqToHom _) (OfClosure.comp htail
            (OfClosure.comp (OfClosure.comp (OfClosure.eqToHom _) (OfClosure.of_map _))
              (OfClosure.comp (OfClosure.inv (OfClosure.of_map _)) (OfClosure.eqToHom _))))

/-- **The constraint on `η`, geometric core.**  For every source chain `a`, the cylinder's
homotopy `sweepR c a` lies in the `of`-closure — it is a zigzag of genuine refinements, with no
formal inverse beyond inverting actual `ChainRefine` arrows. -/
theorem ofClosure_sweepR (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    OfClosure (sweepR c a) := by
  rw [sweepR]
  exact OfClosure.comp (OfClosure.eqToHom _)
    (OfClosure.comp (ofClosure_sweepFirst c _ _ _) (OfClosure.eqToHom _))

/-- **The points `η x` are genuine refinements prefixed by the equivalence counit (user item 3).**
Each induced point `ptHom c x` factors as `(equivalence counit).inv ≫ w` with `w` in the
`of`-closure: the geometry (`sweepR`) is a zigzag of *actual* refinement arrows
(`ofClosure_sweepR`), and the *only* formal inverse is the prefixed equivalence counit
`counit.inv` of `Lgrpd⁻¹`.  This is the precise analogue of "which `x → F₀ x` are realizable":
no *formal* inverse is ever needed except the counit correction. -/
theorem ptHom_eq_counit_comp_ofClosure (c : CylMapWeqR K) (x : RefineObj (K := K) K.init K.final) :
    haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
    ∃ w, OfClosure w ∧
      ptHom c x = c.obj.Lgrpd.asEquivalence.counitIso.inv.app ((FreeGroupoid.of _).obj x) ≫ w := by
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  exact ⟨c.obj.sweepR (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)).as.as,
    ofClosure_sweepR c.obj _, rfl⟩

end CylMapR

/-! ## (Universal property) The image is codiscrete: cylinders are uniquely isomorphic

The target `PointedEndofunctor (DPathGrpdR K)` over a *groupoid* base is **codiscrete**: between any
two objects there is *exactly one* morphism, and it is an isomorphism.  So:

* `cylToPointedR` sends **every** cylinder map to an *iso* of pointed endofunctors, and any two
  cylinders to *uniquely isomorphic* endofunctors.  There is therefore **no nontrivial fiber
  structure up to isomorphism** — the only genuine invariant is the *literal* pair `(F₀, η)`
  (section (A)/(B)).
* In particular there is **no** interesting initial/terminal object inside a fiber and **no**
  (co)reflection to detect: the naive "universal cylinder" question degenerates.  The honest
  universal content is the codiscreteness below; the *strict* injectivity question is the `(F₀, η)`
  kernel of (A)/(B). -/

namespace Cyl2

variable {𝒢 : Type*} [Groupoid 𝒢]

/-- **Morphisms of pointed endofunctors of a groupoid are unique** (the hom-sets are
subsingletons): the point axiom `A.pt ≫ τ = B.pt` forces `τ = inv A.pt ≫ B.pt`, so any two
morphisms agree.  Hence the category is *thin* on objects realised as pointed endofunctors of a
groupoid. -/
instance pointed_subsingleton (A B : PointedEndofunctor 𝒢) : Subsingleton (A ⟶ B) where
  allEq f g := PointedEndofunctor.Hom.ext (by
    have hf : inv A.pt ≫ A.pt ≫ f.τ = inv A.pt ≫ B.pt := by rw [f.w]
    have hg : inv A.pt ≫ A.pt ≫ g.τ = inv A.pt ≫ B.pt := by rw [g.w]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at hf hg
    rw [hf, hg])

/-- **The point-determined morphism is an isomorphism**, with inverse the point-determined morphism
the other way.  So any two pointed endofunctors of a groupoid are (uniquely) isomorphic. -/
noncomputable def pointedIsoOfGroupoid (A B : PointedEndofunctor 𝒢) : A ≅ B where
  hom := pointedHomOfGroupoid A B
  inv := pointedHomOfGroupoid B A
  hom_inv_id := by rw [pointedHomOfGroupoid_comp, pointedHomOfGroupoid_id]
  inv_hom_id := by rw [pointedHomOfGroupoid_comp, pointedHomOfGroupoid_id]

/-- Any morphism of pointed endofunctors of a groupoid is an iso (codiscreteness). -/
instance pointed_isIso {A B : PointedEndofunctor 𝒢} (f : A ⟶ B) : IsIso f := by
  obtain rfl : f = (pointedIsoOfGroupoid A B).hom :=
    Subsingleton.elim _ _
  exact (pointedIsoOfGroupoid A B).isIso_hom

end Cyl2

namespace CylMapR

open Cyl2

variable {K : BPSet}

/-- **`cylToPointedR` lands in a codiscrete category.**  Every cylinder-map is sent to an
isomorphism of pointed endofunctors — so all cylinders over `K` are *uniquely isomorphic* in the
target, and no fiber carries nontrivial categorical structure up to iso. -/
instance cylToPointedR_map_isIso {c c' : CylMapWeqR K} (f : c ⟶ c') :
    IsIso ((cylToPointedR K).map f) :=
  Cyl2.pointed_isIso _

/-- Any two cylinders over `K` induce *canonically isomorphic* pointed endofunctors (the unique
point-determined iso).  This is the "soft" injectivity statement; the *hard* (literal) one is the
`(ptObj, ptHom)` kernel `cylToPointedObj_eq_of`. -/
noncomputable def cylToPointedObj_iso (c c' : CylMapWeqR K) :
    cylToPointedObj c ≅ cylToPointedObj c' :=
  Cyl2.pointedIsoOfGroupoid _ _

end CylMapR
