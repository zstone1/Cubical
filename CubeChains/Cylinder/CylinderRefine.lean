import CubeChains.Cylinder.CylinderSweep

/-!
# Cylinder/CylinderRefine

The cylinder ⟹ pointed-functor functor `cylToPointedR` (the thin deliverable, RESULT 2).
For a weak-equivalence cylinder `c : CylMapWeqR K`, the family of homotopies `sweepR`
(`CylinderSweep`) assembles into a **pointed endofunctor** of `DPathGrpdR K` via `pointedOfPaths`,
and—since `DPathGrpdR K` is a groupoid—`pointedFunctorOfObj` forces the morphism map uniquely.  This
file is the thin deliverable: `cylToPointedObj` (object map) and `cylToPointedR` (the functor
`CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`), the completion of program step 2.

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

For a weak-equivalence cylinder `c : CylMapWeqR K` (left leg a groupoid equivalence), the homotopy
`sweepR` assembles into a **pointed endofunctor** of `DPathGrpdR K` via `pointedOfPaths`:

* object map `F₀ x := c.Rgrpd.obj (c.Lgrpd.inv.obj x)` (the transport `Lgrpd⁻¹ ⋙ Rgrpd` of `Rgrpd`
  along the equivalence `Lgrpd`);
* per-object point `η x := counit.inv.app x ≫ sweepR c (Lgrpd.inv.obj x)` — the cylinder's homotopy
  at the transported chain, prefixed by the equivalence counit.

`pointedOfPaths` turns this object-data into a genuine `PointedEndofunctor` with naturality *free*
(the conjugation trick), so no naturality chase is needed for the point. -/

/-- **Piece 5 (object map): the pointed endofunctor of a weak-equivalence cylinder.**  Via
`pointedOfPaths`, from the object map `Rgrpd ∘ Lgrpd⁻¹` and the per-chain homotopy `sweepR`.  This
is the action of the cylinder `c` as a coherent family of d-path homotopies on `DPathGrpdR K`. -/
noncomputable def cylToPointedObj (c : CylMapWeqR K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  Operations.pointedOfPaths
    (fun x => c.obj.Rgrpd.obj (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)))
    (fun x => c.obj.Lgrpd.asEquivalence.counitIso.inv.app ((FreeGroupoid.of _).obj x)
      ≫ c.obj.sweepR (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)).as.as)

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
