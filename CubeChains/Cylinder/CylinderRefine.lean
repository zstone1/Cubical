import CubeChains.Cylinder.CylinderSweep

/-!
# Cylinder/CylinderRefine

The cylinder ⟹ pointed-functor functor `cylToPointedR` (the thin deliverable, RESULT 2).
The family of homotopies `sweepR` (`CylinderSweep`) assembles into a **pointed endofunctor** of
`DPathGrpdR K` via `pointedOfPaths`, and—since `DPathGrpdR K` is a groupoid—`pointedFunctorOfObj`
forces the morphism map uniquely.

**The construction is SECTION-PRIMARY.**  It runs on a `DPathSection` — a one-sided **section up
to iso** of the left leg-functor `Lgrpd` (a `Lstar : D ⥤ C` with `unit : 𝟭 ≅ Lstar ⋙ Lgrpd`),
strictly weaker than `IsEquivalence` (it never uses the second composite `Lgrpd ⋙ Lstar` nor the
triangle identities; `DPathSection` lives in `Cylinder/PointedFunctor.lean`).  There is **no
equivalence gate**: an equivalence is merely *one* supplier of a section, via
`DPathSection.ofEquivalence`/`SecCyl.ofEquiv`.

This file is the thin deliverable:
* `cylToPointedObjOfSection c s` — the **primary** section-based object map (from a `CylMapR K` + a
  `DPathSection` of its left leg);
* `SecCyl K` — the bundled **primary** user-facing "cylinder + section" entry point, a `CylMapR K`
  plus a section, carrying a `Category` instance (morphisms forget the section), with
  `SecCyl.toPointedObj` its induced pointed endofunctor and `SecCyl.ofEquiv` the
  equivalence-supplied section (one supplier, not a gate);
* `cylToPointedR` — the functor `SecCyl K ⥤ PointedEndofunctor (DPathGrpdR K)`, completing
  program step 2.

The geometry core is in `CylinderRefineCore.lean`; the staircase assembly `sweepR` is in
`CylinderSweep.lean`.

**Layer:** Cylinder.  **Imports:** `Cylinder/CylinderSweep`.
-/

open CategoryTheory Opposite
open Operations
open CubeChain

variable {K : BPSet}

namespace CylMapR

open CubeChain

/-! ## Piece 5 — the cylinder's pointed endofunctor on the d-path groupoid

For a cylinder `c : CylMapR K` equipped with a `DPathSection` `s` of its left leg-functor `Lgrpd`,
the homotopy `sweepR` assembles into a **pointed endofunctor** of `DPathGrpdR K` via
`pointedOfPaths`:

* object map `F₀ x := c.Rgrpd.obj (s.Lstar.obj x)` (the transport `Lstar ⋙ Rgrpd` of `Rgrpd`
  along the section `s`);
* per-object point `η x := s.unit.hom.app x ≫ sweepR c (s.Lstar.obj x)` — the cylinder's homotopy
  at the transported chain, prefixed by the section unit `x ⟶ Lgrpd(Lstar x)`.

`pointedOfPaths` turns this object-data into a genuine `PointedEndofunctor` with naturality *free*
(the conjugation trick), so no naturality chase is needed for the point.

The construction runs on a `DPathSection` — a **one-sided section up to iso** of the left leg,
strictly weaker than `IsEquivalence` (it never touches the second composite `Lgrpd ⋙ Lstar` nor the
triangle identities).  This is the **primary condition**: there is no equivalence gate.  An
equivalence is merely *one* supplier of a section, via `DPathSection.ofEquivalence` (packaged at the
cylinder level as `SecCyl.ofEquiv`).  The bundled entry point is `SecCyl K` (a `CylMapR K` plus a
section), with object map `SecCyl.toPointedObj` and deliverable functor `cylToPointedR`. -/

/-- **Piece 5 (object map, section form — PRIMARY): the pointed endofunctor of a cylinder +
section.**  From a cylinder `c : CylMapR K` and a `DPathSection` `s` of its left leg-functor
`c.Lgrpd`, build a `PointedEndofunctor (DPathGrpdR K)` via `pointedOfPaths`:

* object map `F₀ x := Rgrpd (Lstar x)` — the transport `Lstar ⋙ Rgrpd` of `Rgrpd`;
* per-object point `η x := s.unit.hom.app x ≫ sweepR (Lstar x)` — the section unit
  `x ⟶ Lgrpd(Lstar x)` followed by the cylinder homotopy `Lgrpd(Lstar x) ⟶ Rgrpd(Lstar x)`.

The section `s` is the **primary condition** of the construction: it consumes only the one-sided
section datum, never an equivalence (see `SecCyl.ofEquiv` for the canonical equivalence-supplied
instance). -/
noncomputable def cylToPointedObjOfSection (c : CylMapR K)
    (s : Operations.DPathSection c.Lgrpd) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedOfPaths
    (fun x => c.Rgrpd.obj (s.Lstar.obj ((FreeGroupoid.of _).obj x)))
    (fun x => s.unit.hom.app ((FreeGroupoid.of _).obj x)
      ≫ c.sweepR (s.Lstar.obj ((FreeGroupoid.of _).obj x)).as.as)

end CylMapR

/-- A **cylinder map with a chosen section** of its left leg-functor: a `CylMapR K` together with a
`DPathSection` of `c.Lgrpd`.  This is the **primary, user-facing entry point** of the cylinder ⟹
pointed-functor program: the construction runs on the one-sided section datum directly, with no
equivalence gate.  Its morphisms are the underlying cylinder-map morphisms (the section is
forgotten, see the `Category (SecCyl K)` instance); its induced pointed endofunctor is
`SecCyl.toPointedObj`.
A section can be supplied by an equivalence via `SecCyl.ofEquiv`, but that is just *one* supplier —
not a gate. -/
structure SecCyl (K : BPSet) where
  /-- The underlying cylinder map. -/
  obj : CylMapR K
  /-- A chosen section up to iso of the left leg-functor. -/
  sec : Operations.DPathSection obj.Lgrpd

/-- The pointed endofunctor of a `SecCyl K` object: the section-based construction at its chosen
section.  This is the object map of the deliverable functor `cylToPointedR`. -/
noncomputable def SecCyl.toPointedObj (c : SecCyl K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  CylMapR.cylToPointedObjOfSection c.obj c.sec

/-- **Morphisms of section-cylinders are morphisms of the underlying cylinder maps.**  A
`SecCyl K` is a `CylMapR K` plus a section; its morphisms forget the section, so
`Hom a b := a.obj ⟶ b.obj` with identity and composition inherited from `CylMapR K`.  (The section
plays no role in the morphism map: over the groupoid base `DPathGrpdR K` the comparison of induced
pointed endofunctors is *forced* by the points, see `cylToPointedR`.) -/
instance SecCyl.category (K : BPSet) : Category (SecCyl K) where
  Hom a b := a.obj ⟶ b.obj
  id a := 𝟙 a.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- **An equivalence supplies a section.**  When a cylinder map `c`'s left leg-functor `c.Lgrpd` is
an equivalence, the canonical section `DPathSection.ofEquivalence` makes it a `SecCyl K`.  This is
*one* supplier of the primary section datum — not a gate; the construction never depends on `c`
being an equivalence beyond producing this section. -/
noncomputable def SecCyl.ofEquiv (c : CylMapR K) [c.Lgrpd.IsEquivalence] : SecCyl K where
  obj := c
  sec := Operations.DPathSection.ofEquivalence c.Lgrpd

/-- **Piece 5 (morphism map): the cylinder ⟹ pointed-functor FUNCTOR.**  Assembles the
per-cylinder pointed endofunctors `SecCyl.toPointedObj` into a functor
`SecCyl K ⥤ PointedEndofunctor (DPathGrpdR K)`.

The morphism map is *forced*: the d-path groupoid `DPathGrpdR K` is a `Groupoid`, so each
point `(SecCyl.toPointedObj c).pt` is a natural isomorphism, and the morphism axiom
`pt_c ≫ τ = pt_{c'}` determines the comparison `τ = pt_c⁻¹ ≫ pt_{c'}` uniquely
(`Operations.pointedHomOfGroupoid`).  A section-cylinder morphism `f : c ⟶ c'` is therefore sent to
this unique point-determined comparison; `map_id`/`map_comp` and the point-compatibility `w` are all
automatic (`pointedFunctorOfObj`).  No naturality chase, no deferral — this COMPLETES the
cylinder ⟹ pointed-functor functor (program step 2). -/
noncomputable def cylToPointedR (K : BPSet) :
    SecCyl K ⥤ Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedFunctorOfObj SecCyl.toPointedObj

@[simp] theorem cylToPointedR_obj (c : SecCyl K) :
    (cylToPointedR K).obj c = c.toPointedObj := rfl

@[simp] theorem cylToPointedR_map {c c' : SecCyl K} (f : c ⟶ c') :
    (cylToPointedR K).map f
      = Operations.pointedHomOfGroupoid c.toPointedObj c'.toPointedObj := rfl

/-! ## 9. Module summary — the general sweep `sweepR` and Piece 5

The cylinder ⟹ pointed-functor **functor** (program step 2) is COMPLETE, green and sorry-free:
both its object map `cylToPointedObj` and its morphism map `cylToPointedR` are built.

The pipeline: for a `k`-block source chain the junction-bridge staircase lifts the blocks `k → 1`
through prism-cube cospans, sharing each junction edge `eᵢ` between the two bridges touching `sᵢ`
(making consecutive staircase objects definitionally equal so the zigzag composes).  It is run by
the list-indexed recursion `sweepTail`/`sweepFirst` over `BlockRec`/`BlockConsec` (each local arrow
whiskered by a fixed prefix via `RefineObj.appendLeft` and a fixed suffix via inline
`ChainRefine.append · (𝟙 _)`), assembled into the total homotopy `sweepR c a :
(pushforwardBP leftLeg).obj a ⟶ (pushforwardBP rightLeg).obj a`.  Piece 5 then turns the family
`sweepR` into `SecCyl.toPointedObj` (via the section-primary `cylToPointedObjOfSection`) using
`pointedOfPaths` (naturality free by conjugation), and—since `DPathGrpdR K` is a groupoid—
`pointedFunctorOfObj` forces the morphism map uniquely (`cylToPointedR`).  Connectivity for the
smallest multi-block cylinder is independently confirmed by `native_decide` in
`Testing/CylinderTwoBlock.lean`. -/
