import CubeChains.Cylinder.CylinderSweep

/-!
# Cylinder/CylinderRefine

The cylinder ⟹ pointed-functor functor `cylToPointedR` (the thin deliverable, RESULT 2).
The family of homotopies `sweepR` (`CylinderSweep`) assembles into a **pointed endofunctor** of
`DPathGrpdR K` via `pointedOfPaths`, and—since `DPathGrpdR K` is a groupoid—`pointedFunctorOfObj`
forces the morphism map uniquely.

**The construction runs on a `DPathSection`** — a one-sided **section up to iso** of the left
leg-functor `Lgrpd` (a `Lstar : D ⥤ C` with `unit : 𝟭 ≅ Lstar ⋙ Lgrpd`), strictly weaker than
`IsEquivalence` (it never uses the second composite `Lgrpd ⋙ Lstar` nor the triangle identities;
`DPathSection` lives in `Cylinder/PointedFunctor.lean`).  The **canonical instance** is
`DPathSection.ofEquivalence`: a weak-equivalence cylinder `c : CylMapWeqR K` carries the canonical
section `CylMapWeqR.section_`, and the original equivalence construction is recovered through it.

This file is the thin deliverable:
* `cylToPointedObjOfSection c s` — the section-based object map (from a `CylMapR K` + a
  `DPathSection` of its left leg);
* `cylToPointedObj` (object map for the equivalence case) — routed through
  `cylToPointedObjOfSection` at the canonical section, **definitionally equal** to the original
  term (`cylToPointedObjOfSection_section_`), so all downstream users (`cylToPointedR`,
  `MooreMonoid`) are undisturbed;
* `SecCyl K` — the bundled user-facing "cylinder + section" entry point, with `CylMapWeqR.toSecCyl`
  the canonical inclusion of the equivalence case;
* `cylToPointedR` — the functor `CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`, completing
  program step 2.

(`cylToPointedR` and `MooreMonoid`'s `mooreSubmonoid` deliberately remain on the equivalence case
`CylMapWeqR`; generalising them to bare `SecCyl` is a one-line follow-up once a section-level
morphism category is chosen.)

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
triangle identities).  The **canonical instance** is `DPathSection.ofEquivalence`, applied to a
weak-equivalence cylinder `c : CylMapWeqR K` via `CylMapWeqR.section_`; routing the equivalence case
through it reproduces the original construction **definitionally** (`cylToPointedObj` below is, by
unfolding, exactly `cylToPointedObjOfSection c.obj (CylMapWeqR.section_ c)`). -/

/-- **Piece 5 (object map, section form): the pointed endofunctor of a cylinder + section.**  From a
cylinder `c : CylMapR K` and a `DPathSection` `s` of its left leg-functor `c.Lgrpd`, build a
`PointedEndofunctor (DPathGrpdR K)` via `pointedOfPaths`:

* object map `F₀ x := Rgrpd (Lstar x)` — the transport `Lstar ⋙ Rgrpd` of `Rgrpd`;
* per-object point `η x := s.unit.hom.app x ≫ sweepR (Lstar x)` — the section unit
  `x ⟶ Lgrpd(Lstar x)` followed by the cylinder homotopy `Lgrpd(Lstar x) ⟶ Rgrpd(Lstar x)`.

For `s = DPathSection.ofEquivalence` (the equivalence case) this is definitionally the original
`cylToPointedObj`. -/
noncomputable def cylToPointedObjOfSection (c : CylMapR K)
    (s : Operations.DPathSection c.Lgrpd) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedOfPaths
    (fun x => c.Rgrpd.obj (s.Lstar.obj ((FreeGroupoid.of _).obj x)))
    (fun x => s.unit.hom.app ((FreeGroupoid.of _).obj x)
      ≫ c.sweepR (s.Lstar.obj ((FreeGroupoid.of _).obj x)).as.as)

/-- The **canonical section** of a weak-equivalence cylinder's left leg-functor, built from the
equivalence `CylMapWeqR.left_weq` via `DPathSection.ofEquivalence`. -/
noncomputable def CylMapWeqR.section_ (c : CylMapWeqR K) :
    Operations.DPathSection c.obj.Lgrpd :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  Operations.DPathSection.ofEquivalence c.obj.Lgrpd

/-- **Piece 5 (object map): the pointed endofunctor of a weak-equivalence cylinder.**  The
section-based construction `cylToPointedObjOfSection` fed the **canonical** section
`CylMapWeqR.section_` (built from the equivalence `Lgrpd`).  This is *definitionally* the original
term — object map `Rgrpd ∘ Lgrpd⁻¹` and per-chain point `counit.inv ≫ sweepR` — so every downstream
user (`cylToPointedR`, `MooreMonoid`) is undisturbed.  The general section form
`cylToPointedObjOfSection` admits the strictly weaker one-sided sections (see
`Cylinder/PointedFunctor.lean`'s `DPathSection`). -/
noncomputable def cylToPointedObj (c : CylMapWeqR K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  cylToPointedObjOfSection c.obj (CylMapWeqR.section_ c)

/-- **The equivalence-section reproduces the original construction (definitionally).**  For a
weak-equivalence cylinder `c`, feeding `cylToPointedObjOfSection` the canonical section
`CylMapWeqR.section_` (built from the equivalence) is *exactly* `cylToPointedObj c` — they are
**definitionally equal** (`rfl`).  This is what makes routing the equivalence case through the
section construction transparent to every downstream user. -/
theorem cylToPointedObjOfSection_section_ (c : CylMapWeqR K) :
    cylToPointedObjOfSection c.obj (CylMapWeqR.section_ c) = CylMapR.cylToPointedObj c := rfl

/-- A **cylinder map with a chosen section** of its left leg-functor: a `CylMapR K` together with a
`DPathSection` of `c.Lgrpd`.  This is the section-weakened, user-facing entry point — the strictly
weaker replacement for `CylMapWeqR K` (whose extra content was "`Lgrpd` is an equivalence").  Its
induced pointed endofunctor is `SecCyl.toPointedObj`; the equivalence case maps in via
`CylMapWeqR.toSecCyl`. -/
structure SecCyl (K : BPSet) where
  /-- The underlying cylinder map. -/
  obj : CylMapR K
  /-- A chosen section up to iso of the left leg-functor. -/
  sec : Operations.DPathSection obj.Lgrpd

/-- The pointed endofunctor of a `SecCyl K` object: the section-based construction at its chosen
section. -/
noncomputable def SecCyl.toPointedObj (c : SecCyl K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  cylToPointedObjOfSection c.obj c.sec

/-- **Every weak-equivalence cylinder is a section-cylinder**, via the canonical section
`CylMapWeqR.section_`.  This is the canonical inclusion of the equivalence case into the
section-weakened world; on pointed endofunctors it reproduces `cylToPointedObj` definitionally
(`toSecCyl_toPointedObj`). -/
noncomputable def CylMapWeqR.toSecCyl (c : CylMapWeqR K) : SecCyl K where
  obj := c.obj
  sec := CylMapWeqR.section_ c

/-- The section-cylinder of a weak-equivalence cylinder induces the *same* pointed endofunctor as
the original equivalence construction (definitionally). -/
theorem CylMapWeqR.toSecCyl_toPointedObj (c : CylMapWeqR K) :
    (CylMapWeqR.toSecCyl c).toPointedObj = CylMapR.cylToPointedObj c := rfl

/-- **Piece 5 (morphism map): the cylinder ⟹ pointed-functor FUNCTOR.**  Assembles the
per-cylinder pointed endofunctors `cylToPointedObj` into a functor
`CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`.

The morphism map is *forced*: the d-path groupoid `DPathGrpdR K` is a `Groupoid`, so each
point `(cylToPointedObj c).pt` is a natural isomorphism, and the morphism axiom
`pt_c ≫ τ = pt_{c'}` determines the comparison `τ = pt_c⁻¹ ≫ pt_{c'}` uniquely
(`Operations.pointedHomOfGroupoid`).  A cylinder map `f : c ⟶ c'` is therefore sent to this
unique point-determined comparison; `map_id`/`map_comp` and the point-compatibility `w` are all
automatic (`pointedFunctorOfObj`).  No naturality chase, no deferral — this COMPLETES the
cylinder ⟹ pointed-functor functor (program step 2). -/
noncomputable def cylToPointedR (K : BPSet) :
    CylMapWeqR K ⥤ Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedFunctorOfObj CylMapR.cylToPointedObj

@[simp] theorem cylToPointedR_obj (c : CylMapWeqR K) :
    (cylToPointedR K).obj c = CylMapR.cylToPointedObj c := rfl

@[simp] theorem cylToPointedR_map {c c' : CylMapWeqR K} (f : c ⟶ c') :
    (cylToPointedR K).map f
      = Operations.pointedHomOfGroupoid (CylMapR.cylToPointedObj c)
          (CylMapR.cylToPointedObj c') := rfl

end CylMapR

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
`sweepR` into `cylToPointedObj` via `pointedOfPaths` (naturality free by conjugation), and—since
`DPathGrpdR K` is a groupoid—`pointedFunctorOfObj` forces the morphism map uniquely
(`cylToPointedR`).  Connectivity for the smallest multi-block cylinder is independently confirmed by
`native_decide` in `Testing/CylinderTwoBlock.lean`. -/
