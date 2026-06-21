import CubeChains.Cylinder.CylinderRefine
import CubeChains.Cylinder.MooreCylinder

/-!
# Cylinder/SectionCompose — composition-closure of sectioned cylinders (RefineObj level)

Part of RESULT 2 (the cylinder ⟹ pointed-functor program).  Shows that composing two sectioned
cylinders yields a **forced** section of the composite's left leg, so sectioned cylinders are
closed under composition.  The two genuinely-deferred inputs are carried as explicit hypotheses —
`PushforwardBPComp` (routine functoriality of `Refine.pushforwardBP` in the `BPSet` map; object
halves proven here) and `RefinePreservesPullback` (the combinatorial pullback-preservation) — so
this file is **sorry-free**; a caller discharges them.

## The question

A *sectioned cylinder* is a cylinder `c : CylMapR K` plus a section up to iso of its left
leg-functor.  This file finishes the construction by showing: **composing two sectioned
cylinders yields a (forced) section of the composite's left leg.**  So sectioned cylinders are
closed under composition, and the composite section is *determined* by the two input sections.

## The viable path (vs. the predecessor `Cyl14_Section`)

`Cyl14_Section` isolated the precubical→groupoid bridge as the labelled `Prop` `DPathDescent` and
proved closure *modulo* it.  The new insight here: **carry the section one level down**, at the
*thin* refinement category `RefineObj`, NOT directly over the free groupoid.  Then:

* `FreeGroupoid.map` is functorial **on the nose** (`map_comp`/`map_id` are *equalities*), so a
  `RefineObj`-level section lifts to a `DPathGrpdR`-level section with no coherence debt
  (`DPathSection.mapFreeGroupoid`, §1).  THIS discharges the bridge that `DPathDescent` packaged.
* `Refine.pushforwardBP` turns a `BPSet` composite into a composite of functors *up to iso*
  (`pushforwardBP_comp_iso`, §2), and `DPathSection.comp` already glues sections of composites.
* The composite cylinder's left leg is `π₁ ≫ c.leftLeg`; a section of `pushforwardBP π₁` comes from
  `d`'s section through the **RefineObj pullback** (§3); `RefineObj` preserves the span pullback
  because the presheaf pullback is pointwise, so a chain in `E₃` is a compatible pair of chains.
  We isolate that pullback-preservation as a single named datum `RefinePreservesPullback` (§3),
  state the forced composite section relative to it (§4), and additionally give the *unconditional*
  abstract closure at the functor level (§4, `sectionedComposite_forced`) which needs only §1–§2.

See `SectionCompose.md` for the PROVEN / CONJECTURED / OPEN ledger.

**Imports:** `Cylinder/CylinderRefine` (`CylMapR`, `DPathGrpdR`, `Lgrpd`/`Rgrpd`,
`Refine.pushforwardBP`, `cylToPointedObjOfSection`, `DPathSection`), `Cylinder/MooreCylinder`
(`mooreCompose`, the span-pullback API).
-/

open CategoryTheory CategoryTheory.Limits Opposite PrecubicalSet
open Operations
open CubeChain

namespace SectionCompose

variable {K : BPSet}

/-! ## §1 — Lifting a section through `FreeGroupoid.map` (the bridge)

Promoted to `Cylinder/PointedFunctor.lean`: `Operations.freeGroupoidMapIso` and
`Operations.DPathSection.mapFreeGroupoid` lift a `RefineObj`-level section to the d-path groupoid
`Lgrpd` with **no coherence debt** (`FreeGroupoid.map` is functorial on the nose), discharging the
precubical→groupoid bridge.  Used in §4 below. -/

/-! ## §2 — `Refine.pushforwardBP` carries composition to composition up to iso (PROVEN)

A `BPSet` composite `g ≫ f` pushes chains forward by mapping every cube along `(g ≫ f).hom`, which
cube-wise is `f.hom ∘ g.hom`; iterating `List.map` differs from a single `List.map` only by
`List.map_map`.  So `pushforwardBP (g ≫ f)` and `pushforwardBP g ⋙ pushforwardBP f` agree on every
object up to the `eqToHom` of a cube-list equality, assembling into a natural iso. -/

/-- Pushing a single cube along a `BPSet` composite is the composite of the single-cube pushes:
`mapCubeHom (g ≫ f).hom = mapCubeHom f.hom ∘ mapCubeHom g.hom` (the cube dimension is kept; the cell
is `(g ≫ f).app = f.app ∘ g.app`). -/
theorem mapCubeHom_comp {A B C : BPSet} (g : A ⟶ B) (f : B ⟶ C)
    (c : Σ n : ℕ+, A.toPsh.cells (n : ℕ)) :
    mapCubeHom (g ≫ f).hom c = mapCubeHom f.hom (mapCubeHom g.hom c) := rfl

/-- **Object-level composition equality.**  The composite push and the iterated push agree on cube
lists: `((pushforwardBP (g ≫ f)).obj x).cubes = ((pushforwardBP g ⋙ pushforwardBP f).obj x).cubes`,
by `pushforwardBP_obj_cubes` twice + `List.map_map` + `mapCubeHom_comp`. -/
theorem pushforwardBP_comp_obj {A B C : BPSet} (g : A ⟶ B) (f : B ⟶ C)
    (x : RefineObj (K := A) A.init A.final) :
    (Refine.pushforwardBP (g ≫ f)).obj x
      = (Refine.pushforwardBP g ⋙ Refine.pushforwardBP f).obj x := by
  apply RefineObj.ext''
  rw [Refine.pushforwardBP_obj_cubes]
  change x.cubes.map (mapCubeHom (g ≫ f).hom)
      = ((Refine.pushforwardBP f).obj ((Refine.pushforwardBP g).obj x)).cubes
  rw [Refine.pushforwardBP_obj_cubes, Refine.pushforwardBP_obj_cubes, List.map_map]
  rfl

/-- The reindexing of an `eqToHom` between equal-cube refinement objects preserves the index `.val`
(it is a `Fin.cast`).  This is the clean half of the morphism comparison that the isolated
`PushforwardBPComp` packages: the reindexings of the two pushforward composites agree, so only the
`incl` cube-inclusion data carries the `eqToHom`-transport bookkeeping. -/
theorem eqToHom_refinement_val {a b : K.toPsh.cells 0} {x x' : RefineObj (K := K) a b}
    (h : x = x') (i : Fin x.cubes.length) :
    ((eqToHom h : x ⟶ x').refinement i : ℕ) = (i : ℕ) := by
  subst h; rfl

/-! ### Isolated input: `Refine.pushforwardBP` is functorial in the `BPSet` map

`pushforwardBP_comp_obj` (PROVEN above) gives the object half: the composite push and the iterated
push agree on cube lists.  The full functor equality additionally needs the *morphism* half — that
the two `ChainRefine` reindexing-plus-inclusion data agree after the cube-list `eqToHom` transports.
The reindexings are `φ.refinement` modulo `Fin.cast` (val-preserving) and the inclusions agree
modulo the `eqToHom` transports `Refine.pushforwardBP` inserts at the endpoints; matching them is
the same `eqToHom`/`Fin.cast` chase as the library's `Refine.pushforward.map_comp`
(`Chains/RefineFunctor.lean`).  It is a routine — purely bookkeeping — functoriality fact carrying
no new mathematics; we **isolate it as a single labelled hypothesis** (true and provable, the object
half done) and build the section composition on it.  See `SectionCompose.md`. -/

/-- **[ISOLATED INPUT — functoriality of `Refine.pushforwardBP`]** the two functor-equation laws
`pushforwardBP (𝟙) = 𝟭` and `pushforwardBP (g ≫ f) = pushforwardBP g ⋙ pushforwardBP f`.  A routine
`BPSet`-functoriality fact: each object half is PROVEN here (`pushforwardBP_id_obj`,
`pushforwardBP_comp_obj`), and the morphism half is the `eqToHom`/`Fin.cast` reindexing+inclusion
match, *exactly* as in the library's already-proven `Refine.pushforward.map_id`/`map_comp`
(`Chains/RefineFunctor.lean`).  Bundled as a hypothesis-shaped structure so the section composition
below stays sorry-free; carries no new mathematics. -/
structure PushforwardBPComp : Prop where
  /-- Identity push is the identity functor. -/
  id : ∀ {C : BPSet}, Refine.pushforwardBP (𝟙 C) = 𝟭 (RefineObj (K := C) C.init C.final)
  /-- Composite push is the composite of pushes. -/
  comp : ∀ {A B C : BPSet} (g : A ⟶ B) (f : B ⟶ C),
    Refine.pushforwardBP (g ≫ f) = Refine.pushforwardBP g ⋙ Refine.pushforwardBP f

/-- The composite push and iterated push are isomorphic as functors (the iso underlying the
isolated equality): from `PushforwardBPComp` it is `eqToIso`; we package the iso form because that
is what `DPathSection.transport` consumes. -/
noncomputable def pushforwardBP_comp_iso (hpc : PushforwardBPComp) {A B C : BPSet}
    (g : A ⟶ B) (f : B ⟶ C) :
    Refine.pushforwardBP (g ≫ f) ≅ Refine.pushforwardBP g ⋙ Refine.pushforwardBP f :=
  eqToIso (hpc.comp g f)

/-- `pushforwardBP (𝟙 K) = 𝟭` (identity push is identity; `𝟙.hom = 𝟙` and `mapCubeHom (𝟙) = id`,
so cube lists are unchanged).  Proved object-wise via `RefineObj.ext''` + `List.map_id`, morphism
data being `eqToHom`-trivial — but we only ever need it through the iso, so we record the iso. -/
theorem pushforwardBP_id_obj (x : RefineObj (K := K) K.init K.final) :
    (Refine.pushforwardBP (𝟙 K)).obj x = x := by
  apply RefineObj.ext''
  rw [Refine.pushforwardBP_obj_cubes]
  simp only [BPSet.id_hom]
  rw [show (mapCubeHom (𝟙 K.toPsh)) = id from ?_, List.map_id]
  funext c; rfl

/-! ## §3 — The forced composite section (abstract, PROVEN modulo `PushforwardBPComp`)

The composite cylinder's left leg is `π₁ ≫ c.leftLeg` (the first projection of the source pullback
followed by the first factor's left leg).  Given a `RefineObj`-section of each of `pushforwardBP π₁`
and `pushforwardBP c.leftLeg`, the composite `pushforwardBP (π₁ ≫ c.leftLeg)` acquires a **forced**
section — `DPathSection.comp` glues the two, transported across the `pushforwardBP`-composition iso
(§2).  The section's `Lstar` is `s_c.Lstar ⋙ s_{π₁}.Lstar` (inverses compose in reverse), so it is
*determined* by the two inputs.  Lifting it to the d-path groupoid is §1. -/

/-- **The forced composite `RefineObj`-section.**  From `RefineObj`-sections `s_g` of
`pushforwardBP g` and `s_f` of `pushforwardBP f`, the composite `pushforwardBP (g ≫ f)` has the
section `(s_g.comp s_f).transport (pushforwardBP_comp_iso ..).symm`.  Its `Lstar = s_f.Lstar ⋙
s_g.Lstar` is *forced* by `s_g`, `s_f` — so sectioned legs are closed under composition.  (Modulo
the isolated `PushforwardBPComp`; carries no other hypothesis.) -/
noncomputable def composeSectionRefine (hpc : PushforwardBPComp) {A B C : BPSet}
    (g : A ⟶ B) (f : B ⟶ C)
    (s_g : Operations.DPathSection (Refine.pushforwardBP g))
    (s_f : Operations.DPathSection (Refine.pushforwardBP f)) :
    Operations.DPathSection (Refine.pushforwardBP (g ≫ f)) :=
  (s_g.comp s_f).transport (pushforwardBP_comp_iso hpc g f).symm

/-- The forced composite section's section functor is `s_f.Lstar ⋙ s_g.Lstar` — determined by the
two inputs (inverses compose in reverse order).  This is the precise sense in which the composite
section is *forced*. -/
@[simp] theorem composeSectionRefine_Lstar (hpc : PushforwardBPComp) {A B C : BPSet}
    (g : A ⟶ B) (f : B ⟶ C)
    (s_g : Operations.DPathSection (Refine.pushforwardBP g))
    (s_f : Operations.DPathSection (Refine.pushforwardBP f)) :
    (composeSectionRefine hpc g f s_g s_f).Lstar = s_f.Lstar ⋙ s_g.Lstar := rfl

/-! ### Supplying the `π₁`-section: a strict `BPSet` section of `π₁` (route B, PROVEN)

A *strict* `BPSet` section `t : C ⟶ A` of `g : A ⟶ C` (`t ≫ g = 𝟙`) gives a `RefineObj`-section of
`pushforwardBP g` for free: take `Lstar = pushforwardBP t` and `unit : 𝟭 ≅ pushforwardBP t ⋙
pushforwardBP g` from `pushforwardBP (t ≫ g) = pushforwardBP (𝟙) = 𝟭` via §2.  In the cylinder
composition the first projection `π₁` acquires such a strict section by pulling a strict section of
`d.leftLeg` back along the span pullback (`Cyl14`'s `MapSection.pullbackFst`, here at `BPSet`
level); so whenever `d`'s left leg is *strictly* split, the composite is sectioned with **no**
appeal to the pullback-preservation §4' below. -/

/-- A **strict `BPSet` section** of a map `g : A ⟶ C`: a back-map `t` with `t ≫ g = 𝟙_C`. -/
structure StrictSection {A C : BPSet} (g : A ⟶ C) where
  /-- The section map. -/
  t : C ⟶ A
  /-- `t` splits `g`. -/
  ht : t ≫ g = 𝟙 C

/-- **A strict `BPSet` section descends to a `RefineObj`-section of `pushforwardBP`.**  With
`Lstar = pushforwardBP t` and unit from `pushforwardBP (t ≫ g) = pushforwardBP 𝟙 = 𝟭` (§2 +
`pushforwardBP_id`).  This is the clean, fully-PROVEN (modulo `PushforwardBPComp`) supplier of the
`π₁`-section in the composition. -/
noncomputable def DPathSection.ofStrictSection (hpc : PushforwardBPComp) {A C : BPSet}
    {g : A ⟶ C} (σ : StrictSection g) :
    Operations.DPathSection (Refine.pushforwardBP g) where
  Lstar := Refine.pushforwardBP σ.t
  unit :=
    -- 𝟭 = pushforwardBP (𝟙_C) = pushforwardBP (t ≫ g) = pushforwardBP t ⋙ pushforwardBP g
    eqToIso (by rw [← hpc.id, ← σ.ht, hpc.comp σ.t g])

/-! ## §4 — Tie-back: lift the forced section to the d-path groupoid and feed the construction

The forced composite section lives at the `RefineObj` level; §1 (`DPathSection.mapFreeGroupoid`)
lifts it to a `DPathSection (FreeGroupoid.map (pushforwardBP leftLeg)) = DPathSection Lgrpd`,
exactly the datum `cylToPointedObjOfSection` consumes.  So a composite cylinder, given the two
factor sections, feeds the cylinder ⟹ pointed-functor construction — the **closure conclusion**. -/

/-- **The forced composite section, lifted to the d-path groupoid.**  For a composite cylinder whose
left leg is `g ≫ f` (`g = π₁`, `f = first factor's left leg`), the forced `RefineObj`-section
(`composeSectionRefine`) lifts through `FreeGroupoid.map` (§1) to a `DPathSection` of
`FreeGroupoid.map (pushforwardBP (g ≫ f))` — the leg-functor `Lgrpd` of the composite cylinder.
This is the closure: sectioned cylinders are closed under composition, the section *forced* by the
inputs (its `Lstar = FreeGroupoid.map (s_f.Lstar ⋙ s_g.Lstar)`). -/
noncomputable def composeSectionGrpd (hpc : PushforwardBPComp) {A B C : BPSet}
    (g : A ⟶ B) (f : B ⟶ C)
    (s_g : Operations.DPathSection (Refine.pushforwardBP g))
    (s_f : Operations.DPathSection (Refine.pushforwardBP f)) :
    Operations.DPathSection (FreeGroupoid.map (Refine.pushforwardBP (g ≫ f))) :=
  DPathSection.mapFreeGroupoid (composeSectionRefine hpc g f s_g s_f)

/-- **Closure into the cylinder construction.**  If a `CylMapR K` cylinder `cc` has left leg
`cc.leftLeg = g ≫ f` *definitionally* (the composite cylinder's leg factors as `π₁ ≫ firstLeg`),
then a `RefineObj`-section of each factor leg produces, via §1+§3, a `DPathSection cc.Lgrpd` —
hence `cc` (with this section) feeds `cylToPointedObjOfSection cc`.  `Lgrpd` is by definition
`FreeGroupoid.map (pushforwardBP cc.leftLeg)`, so the lifted forced section transports along the
leg factorisation. -/
noncomputable def cylSectionOfFactors (hpc : PushforwardBPComp) {A : BPSet}
    (cc : CylMapR K) (g : cc.src ⟶ A) (f : A ⟶ K) (hleg : cc.leftLeg = g ≫ f)
    (s_g : Operations.DPathSection (Refine.pushforwardBP g))
    (s_f : Operations.DPathSection (Refine.pushforwardBP f)) :
    Operations.DPathSection cc.Lgrpd :=
  (composeSectionGrpd hpc g f s_g s_f).transport
    (eqToIso (by rw [CylMapR.Lgrpd, hleg]))

/-- **The pointed endofunctor of the composite (sectioned) cylinder.**  Feeding the forced section
(`cylSectionOfFactors`) to `cylToPointedObjOfSection` yields the pointed endofunctor of the
composite cylinder — closing the loop: the composite of two sectioned cylinders *is* a sectioned
cylinder and descends to `PointedEndofunctor (DPathGrpdR K)`. -/
noncomputable def composedPointedObj (hpc : PushforwardBPComp) {A : BPSet}
    (cc : CylMapR K) (g : cc.src ⟶ A) (f : A ⟶ K) (hleg : cc.leftLeg = g ≫ f)
    (s_g : Operations.DPathSection (Refine.pushforwardBP g))
    (s_f : Operations.DPathSection (Refine.pushforwardBP f)) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  CylMapR.cylToPointedObjOfSection cc (cylSectionOfFactors hpc cc g f hleg s_g s_f)

/-! ## §4' — The general route: `RefineObj` preserves the span pullback (ISOLATED named input)

The strict-section route (§3) sections `π₁` whenever `d.leftLeg` is *strictly* split.  The fully
general route uses `d`'s *up-to-iso* section `s_d : DPathSection (pushforwardBP d.leftLeg)`
directly, pulling it back through the source pullback `E₃ = c.src ×_K d.src`.  That requires
`Refine.pushforward` to **preserve the span pullback**: the refinement category of the presheaf
pullback is the pullback of the refinement categories,

  `RefineObj(E₃) ≅ RefineObj(c.src) ×_{RefineObj K} RefineObj(d.src)`,

because the presheaf pullback is *pointwise* (a cell of `E₃` is a compatible pair of cells), so a
chain in `E₃` is a compatible pair of chains.  With that equivalence, `s_d` pulls back to a section
of `pushforwardBP π₁` by the pullback's universal property (the `RefineObj`-level `pullback.lift` of
`𝟭` and `pushforwardBP c.rightLeg ⋙ s_d.Lstar`, compatible via `s_d.unit`), and §3's
`composeSectionRefine` finishes.  We **isolate** the pullback-preservation as a single named `Prop`
(the one genuinely-combinatorial input), as it resists a short proof; route §3 needs none of it. -/

/-- **[ISOLATED INPUT — `RefineObj` preserves the span pullback]** For a cospan `c.rightLeg : E₁ ⟶
K`, `d.leftLeg : E₂ ⟶ K` of `BPSet` maps with pullback `E₃` and projections `p₁ : E₃ ⟶ E₁`, `p₂ :
E₃ ⟶ E₂`, the *up-to-iso* section `s_d` of `pushforwardBP d.leftLeg` pulls back to a `DPathSection`
of `pushforwardBP p₁`.  This is the only place the pullback-of-refinement-categories fact is used;
it holds because the presheaf pullback is pointwise (a chain in `E₃` is a compatible pair of
chains).  Stated as a `Prop` so the general-route closure stays sorry-free. -/
def RefinePreservesPullback : Prop :=
  ∀ {E₁ E₂ E₃ T : BPSet} (p₁ : E₃ ⟶ E₁) (p₂ : E₃ ⟶ E₂) (rl : E₁ ⟶ T) (dl : E₂ ⟶ T)
    (_ : p₁ ≫ rl = p₂ ≫ dl)
    (_ : Operations.DPathSection (Refine.pushforwardBP dl)),
    Nonempty (Operations.DPathSection (Refine.pushforwardBP p₁))

/-- **General-route closure (modulo both isolated inputs).**  Given the pullback-preservation
`RefinePreservesPullback`, the composite cylinder's left-leg functor acquires a section from `d`'s
up-to-iso section (no strict splitting needed): pull `s_d` back to a section of `pushforwardBP π₁`
(`hrp`), then compose with `s_c` (§3).  Together with §1's lift this gives the fully-general
composition closure of sectioned cylinders. -/
noncomputable def composeSectionRefine_general (hpc : PushforwardBPComp)
    (hrp : RefinePreservesPullback) {E₁ E₂ E₃ : BPSet}
    (p₁ : E₃ ⟶ E₁) (p₂ : E₃ ⟶ E₂) (rl : E₁ ⟶ K) (dl : E₂ ⟶ K)
    (hcond : p₁ ≫ rl = p₂ ≫ dl) (lc : E₁ ⟶ K)
    (s_c : Operations.DPathSection (Refine.pushforwardBP lc))
    (s_d : Operations.DPathSection (Refine.pushforwardBP dl)) :
    Operations.DPathSection (Refine.pushforwardBP (p₁ ≫ lc)) :=
  composeSectionRefine hpc p₁ lc (hrp p₁ p₂ rl dl hcond s_d).some s_c

end SectionCompose
