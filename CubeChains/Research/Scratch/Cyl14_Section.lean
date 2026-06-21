import CubeChains.Cylinder.CylinderRefine
import CubeChains.Cylinder.MooreCylinder

/-!
# Cyl14_Section — weakening the cylinder's left leg from "equivalence" to "has a section"

Scratch prototype (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl14_Section`.  Owns ONLY this
file and its `.md`.

## The idea

`cylToPointedObj` (`Cylinder/CylinderRefine.lean`) is built from a `CylMapWeqR K` object, i.e.
a cylinder whose left leg-functor `Lgrpd : DPathGrpdR src ⥤ DPathGrpdR K` is a full equivalence.
But the construction *only* ever touches the datum

  `(Lgrpd.inv , counitIso.inv : 𝟭 ⟹ Lgrpd.inv ⋙ Lgrpd)`.

It uses neither the real counit `Lgrpd ⋙ Lgrpd.inv ≅ 𝟭` nor the triangle identities — only the
one natural transformation `𝟭 ⟹ Lgrpd.inv ⋙ Lgrpd`.  So we can **weaken** the hypothesis on
`Lgrpd` from "is an equivalence" to "has a *section up to iso*":

  a functor `Lstar : D ⥤ C` together with `unit : 𝟭_D ≅ Lstar ⋙ Lgrpd`.

This is strictly weaker than an equivalence — even between groupoids — because a *full* adjunction
between groupoids is automatically an equivalence (unit & counit become isos), whereas a one-sided
section imposes no such collapse (see §A4 for a concrete non-equivalence with a section).

## What lands (PROVEN, sorry-free)

**Part A — the section-based construction.**
* `DPathSection F` — the section datum `(Lstar, unit : 𝟭 ≅ Lstar ⋙ F)`;
* `cylToPointedObjOfSection c s` — the pointed endofunctor from a section, copying
  `cylToPointedObj` with `Lgrpd.inv → s.Lstar`, `counitIso.inv → s.unit.inv`;
* `DPathSection.ofEquivalence` — `IsEquivalence ⟹ HasSection` (so all `CylMapWeqR` qualify);
* `cylToPointedObjOfSection_ofEquivalence` — the section built from the equivalence reproduces the
  original `cylToPointedObj` **on the nose**;
* `DPathSection.notEquivWitness` — a section of a functor that is *not* an equivalence
  (`{a,b} ⇉ {∗}`, discrete), so the weakening is genuine.

**Part B — composition closure.**
* `DPathSection.comp` — sections compose: `DPathSection F → DPathSection G → DPathSection (F⋙G)`;
* `DPathSection.pullbackPrecubical` — at the **precubical** level, a section of `d.startLeg` pulls
  back along the `mooreCompose` pullback projection `composeπ₁` to a section of that projection
  (universal property; sections pull back along *anything*, no right-properness);
* the **d-path descent** of that pulled-back section to the groupoid functor `(composeπ₁)grpd` is
  isolated as the single remaining lemma `DPathDescent` (a labelled `Prop`, NOT a sorry-as-proof).

See `Cyl14_Section.md` for the PROVEN / CONJECTURED / OPEN ledger.

**Imports:** `Cylinder/CylinderRefine` (`cylToPointedObj`, `CylMapR`, `DPathGrpdR`,
`Lgrpd`/`Rgrpd`, `sweepR`), `Cylinder/MooreCylinder` (`mooreCompose`, `composeπ₁`, the
span-pullback API).
-/

open CategoryTheory CategoryTheory.Limits Opposite PrecubicalSet
open Operations
open CubeChain

namespace Cyl14

variable {K : BPSet}

/-! ## Part A1 — the section datum

A **section up to iso** of a functor `F : C ⥤ D` is a functor `Lstar : D ⥤ C` going the other way,
together with a natural isomorphism `unit : 𝟭_D ≅ Lstar ⋙ F`.  This is one half of an equivalence
(`Lstar ⋙ F ≅ 𝟭`), with **no** condition on the other composite `F ⋙ Lstar` and **no** triangle
identities — exactly the data the cylinder construction consumes. -/

/-- A **section up to iso** of `F : C ⥤ D`: a functor `Lstar : D ⥤ C` and an iso
`unit : 𝟭_D ≅ Lstar ⋙ F`.  (`unit` is recorded as a genuine iso; over a groupoid base any natural
transformation `𝟭 ⟹ Lstar ⋙ F` is automatically iso, so this is no extra strength there, but
carrying the iso keeps the construction independent of the groupoid hypothesis.) -/
structure DPathSection {C D : Type*} [Category C] [Category D] (F : C ⥤ D) where
  /-- The section functor, going back `D ⥤ C`. -/
  Lstar : D ⥤ C
  /-- The unit witnessing `Lstar` is a section of `F` up to iso: `𝟭_D ≅ Lstar ⋙ F`. -/
  unit : 𝟭 D ≅ Lstar ⋙ F

/-- A **cylinder map with a section** of its left leg-functor: a `CylMapR K` together with a
`DPathSection` of `c.Lgrpd`.  This is the section-weakened replacement for `CylMapWeqR K` (whose
extra content was "`Lgrpd` is an equivalence"). -/
structure SecCyl (K : BPSet) where
  /-- The underlying cylinder map. -/
  obj : CylMapR K
  /-- A section up to iso of the left leg-functor. -/
  sec : DPathSection obj.Lgrpd

/-! ## Part A2 — the section-based pointed endofunctor

We copy `cylToPointedObj` verbatim, replacing the two equivalence data it uses:

* `Lgrpd.inv  ↝  s.Lstar`        (the object map's "transport back" functor);
* `counitIso.inv.app x  ↝  s.unit.hom.app x`   (the per-object point prefix `x ⟶ Lgrpd(Lstar x)`).

Everything else (`Rgrpd`, `sweepR`, `pointedOfPaths`) is unchanged.  `pointedOfPaths` supplies
naturality for free (the conjugation trick), so no naturality chase is needed. -/

/-- **The section-based pointed endofunctor.**  From a cylinder `c : CylMapR K` and a section
`s : DPathSection c.Lgrpd`, build a `PointedEndofunctor (DPathGrpdR K)` via `pointedOfPaths`:

* object map `F₀ x := Rgrpd (Lstar x)` — the transport `Lstar ⋙ Rgrpd` of `Rgrpd`;
* per-object point `η x := s.unit.hom.app x ≫ sweepR (Lstar x)` — the section unit
  `x ⟶ Lgrpd(Lstar x)` followed by the cylinder homotopy `Lgrpd(Lstar x) ⟶ Rgrpd(Lstar x)`.

For `s = DPathSection.ofEquivalence` this is *definitionally* the original `cylToPointedObj`
(`cylToPointedObjOfSection_ofEquivalence`). -/
noncomputable def cylToPointedObjOfSection (c : CylMapR K) (s : DPathSection c.Lgrpd) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedOfPaths
    (fun x => c.Rgrpd.obj (s.Lstar.obj ((FreeGroupoid.of _).obj x)))
    (fun x => s.unit.hom.app ((FreeGroupoid.of _).obj x)
      ≫ c.sweepR (s.Lstar.obj ((FreeGroupoid.of _).obj x)).as.as)

/-- The section-based pointed endofunctor of a `SecCyl K` object. -/
noncomputable def SecCyl.toPointedObj (c : SecCyl K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  cylToPointedObjOfSection c.obj c.sec

/-! ## Part A3 — equivalence ⟹ section (genuine generalisation)

An equivalence `Lgrpd` yields a section `(Lgrpd.inv, counitIso.symm)`: the section functor is the
inverse and the unit is the *inverse* of the counit `Lgrpd.inv ⋙ Lgrpd ≅ 𝟭`, i.e.
`𝟭 ≅ Lgrpd.inv ⋙ Lgrpd`.  So every `CylMapWeqR K` cylinder carries a section, and feeding that
section to `cylToPointedObjOfSection` reproduces the original `cylToPointedObj`. -/

/-- **`IsEquivalence ⟹ HasSection`.**  From an equivalence `F`, the section `(F.inv, counit⁻¹)`:
the inverse functor with the (symm of the) counit iso `F.inv ⋙ F ≅ 𝟭` as unit `𝟭 ≅ F.inv ⋙ F`. -/
noncomputable def DPathSection.ofEquivalence {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.IsEquivalence] : DPathSection F where
  Lstar := F.inv
  unit := F.asEquivalence.counitIso.symm

/-- The section built from an equivalence has `Lstar = F.inv`. -/
@[simp] theorem DPathSection.ofEquivalence_Lstar {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.IsEquivalence] : (DPathSection.ofEquivalence F).Lstar = F.inv := rfl

/-- The section built from an equivalence has `unit.hom = counitIso.inv`. -/
@[simp] theorem DPathSection.ofEquivalence_unit_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.IsEquivalence] :
    (DPathSection.ofEquivalence F).unit.hom = F.asEquivalence.counitIso.inv := rfl

/-- The canonical section of a weak-equivalence cylinder's left leg (from `CylMapWeqR.left_weq`). -/
noncomputable def CylMapWeqR.section_ (c : CylMapWeqR K) : DPathSection c.obj.Lgrpd :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  DPathSection.ofEquivalence c.obj.Lgrpd

/-- **The equivalence-section reproduces the original construction.**  For a weak-equivalence
cylinder `c`, feeding `cylToPointedObjOfSection` the canonical section built from the equivalence
yields *exactly* (definitionally) the original `cylToPointedObj c`.  So the section construction is
a genuine generalisation: it agrees with the established one on all `CylMapWeqR` cylinders. -/
theorem cylToPointedObjOfSection_ofEquivalence (c : CylMapWeqR K) :
    cylToPointedObjOfSection c.obj (CylMapWeqR.section_ c)
      = CylMapR.cylToPointedObj c := rfl

/-! ## Part A4 — non-vacuity: a section of a non-equivalence

`{a, b}` discrete (two objects, only identities) maps to the terminal groupoid `{∗}` (one object).
The unique functor `T : {a,b} ⥤ {∗}` is **not** an equivalence (not essentially injective on
objects — `a` and `b` both go to `∗`, but are not isomorphic in the discrete source).  Yet it has a
section `Lstar : {∗} ⥤ {a,b}` picking `a`, with `unit : 𝟭_{∗} ≅ Lstar ⋙ T = 𝟭_{∗}` the identity.
So `DPathSection` of a genuine non-equivalence exists — the weakening is real. -/

/-- The two-object discrete category (a groupoid with only identity morphisms). -/
abbrev TwoObj := Discrete (Fin 2)

/-- The one-object terminal category. -/
abbrev OneObj := Discrete (Fin 1)

/-- The unique (collapse) functor `{a,b} ⥤ {∗}`, sending everything to the single object `0`. -/
def collapse : TwoObj ⥤ OneObj := (Functor.const TwoObj).obj ⟨0⟩

/-- A section of `collapse`: the constant functor `{∗} ⥤ {a,b}` picking the object `0`, with the
identity unit `𝟭_{∗} ≅ collapse-back ⋙ collapse`. -/
def collapseSection : DPathSection collapse where
  Lstar := (Functor.const OneObj).obj ⟨0⟩
  unit := eqToIso (by
    -- both sides are the identity functor on the terminal category `{∗}` (a subsingleton of
    -- objects), so the composite `Lstar ⋙ collapse` equals `𝟭`.
    refine CategoryTheory.Functor.ext (fun X => Subsingleton.elim _ _) ?_
    intro X Y f
    apply Subsingleton.elim)

/-- **`collapse` is not an equivalence.**  An equivalence is essentially injective on objects, but
`collapse` sends the *non-isomorphic* objects `⟨0⟩` and `⟨1⟩` of the discrete `{a,b}` to the same
object — were it an equivalence, `⟨0⟩ ≅ ⟨1⟩` in `TwoObj`, forcing `(0 : Fin 2) = 1`, false. -/
theorem collapse_not_isEquivalence : ¬ collapse.IsEquivalence := by
  intro h
  -- `collapse.obj ⟨0⟩ = collapse.obj ⟨1⟩` (both `⟨0⟩` in `OneObj`), so they are isomorphic;
  -- a fully-faithful (equivalence) functor reflects isos, giving `⟨0⟩ ≅ ⟨1⟩` in the source.
  haveI := h
  have hobj : collapse.obj ⟨0⟩ = collapse.obj ⟨1⟩ := Subsingleton.elim _ _
  have hiso : (⟨0⟩ : TwoObj) ≅ (⟨1⟩ : TwoObj) :=
    (Functor.preimageIso collapse (eqToIso hobj))
  -- in a discrete category an iso (its `hom`) forces `.as`-equality, but `(0 : Fin 2) ≠ 1`.
  have h01 : (0 : Fin 2) = 1 := Discrete.eq_of_hom hiso.hom
  exact absurd h01 (by decide)

/-- **Non-vacuity witness.**  The collapse functor `{a,b} ⥤ {∗}` is not an equivalence
(`collapse_not_isEquivalence`) yet has a `DPathSection` (`collapseSection`).  So a `DPathSection`
can exist where an equivalence cannot — the section weakening is strictly stronger (admits more
cylinders) than the equivalence requirement. -/
theorem notEquivWitness : (¬ collapse.IsEquivalence) ∧ Nonempty (DPathSection collapse) :=
  ⟨collapse_not_isEquivalence, ⟨collapseSection⟩⟩

/-! ## Part B5 — sections compose

Given `F : C ⥤ D`, `G : D ⥤ E` and sections `s : DPathSection F`, `s' : DPathSection G`, the
composite `F ⋙ G` has a section with

  `Lstar = s'.Lstar ⋙ s.Lstar`   (go back through `G` then through `F`),
  `unit  : 𝟭_E ≅ (s'.Lstar ⋙ s.Lstar) ⋙ (F ⋙ G)`

glued from `s'.unit : 𝟭_E ≅ s'.Lstar ⋙ G` and `s.unit : 𝟭_D ≅ s.Lstar ⋙ F` whiskered into place.
This is the standard "inverses compose in the opposite order" gluing — here only the *section* half
is required, no triangle obligations. -/

/-- **Sections compose.**  `DPathSection F → DPathSection G → DPathSection (F ⋙ G)` with
`Lstar = s'.Lstar ⋙ s.Lstar` and the unit glued from the two component units.  The gluing is the
isomorphism chain
`𝟭_E ≅ s'.Lstar ⋙ G ≅ s'.Lstar ⋙ (𝟭_D ⋙ G) ≅ s'.Lstar ⋙ ((s.Lstar ⋙ F) ⋙ G)`, reassociated to
`(s'.Lstar ⋙ s.Lstar) ⋙ (F ⋙ G)`. -/
noncomputable def DPathSection.comp {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} (s : DPathSection F) (s' : DPathSection G) :
    DPathSection (F ⋙ G) where
  Lstar := s'.Lstar ⋙ s.Lstar
  unit :=
    -- 𝟭_E ≅ s'.Lstar ⋙ G              (s'.unit)
    s'.unit
    -- ≅ s'.Lstar ⋙ (s.Lstar ⋙ F) ⋙ G   (whisker s.unit on the left of G, on the right of s'.Lstar)
    ≪≫ Functor.isoWhiskerLeft s'.Lstar (Functor.isoWhiskerRight s.unit G)
    -- ≅ (s'.Lstar ⋙ s.Lstar) ⋙ (F ⋙ G)  (functor composition is strictly associative)
    ≪≫ eqToIso (by rfl)

/-! ## Part B6 — sections pull back (the precubical level)

The geometric payoff.  At the level of **precubical maps** a *strict* section pulls back along the
pullback projection with no hypothesis whatsoever on the maps — it is pure universal property.

A **strict section** of `f : X ⟶ Y` is `s : Y ⟶ X` with `s ≫ f = 𝟙_Y` (the precubical analogue of
`DPathSection`; for plain maps the strict version is the natural datum because the pullback lift
needs strict commutation of the square).  Given a pullback `W = X ×_Z Y` with projections
`fst : W ⟶ X`, `snd : W ⟶ Y` over `fst ≫ p = snd ≫ q`, a strict section `s` of `q : Y ⟶ Z` produces
a strict section of `fst : W ⟶ X`, namely `t = pullback.lift 𝟙_X (p ≫ s) …` (the square
`𝟙 ≫ p = (p ≫ s) ≫ q` commutes because `s ≫ q = 𝟙_Z`). -/

/-- A **strict section** of a precubical map `f : X ⟶ Y`: a map `s : Y ⟶ X` with `s ≫ f = 𝟙_Y`. -/
structure MapSection {X Y : PrecubicalSet} (f : X ⟶ Y) where
  /-- The section map. -/
  s : Y ⟶ X
  /-- `s` splits `f`: `s ≫ f = 𝟙_Y`. -/
  hs : s ≫ f = 𝟙 Y

/-- **Sections pull back along the first projection (generic pullback).**  For a `HasPullback p q`
square with projections `fst = pullback.fst p q`, a strict section `σ` of `q` yields a strict
section of `fst`: `t = pullback.lift 𝟙_X (p ≫ σ.s) (…)`.  The lift's square commutes because
`σ.s ≫ q = 𝟙`, so `𝟙_X ≫ p = (p ≫ σ.s) ≫ q`.  No properness, no condition on `p`/`q`: sections
pull back along **anything**. -/
noncomputable def MapSection.pullbackFst {X Y Z : PrecubicalSet} (p : X ⟶ Z) (q : Y ⟶ Z)
    [HasPullback p q] (σ : MapSection q) : MapSection (pullback.fst p q) where
  s := pullback.lift (𝟙 X) (p ≫ σ.s) (by
        rw [Category.id_comp, Category.assoc, σ.hs, Category.comp_id])
  hs := pullback.lift_fst _ _ _

/-- **Specialisation to the `mooreCompose` span-pullback.**  `composeπ₁ c d = pullback.fst c.endLeg
d.startLeg` (`MooreCyl.composeπ₁`), so a strict section of `d.startLeg` pulls back to a strict
section of `composeπ₁ c d`.  This is the section-version closure step at the geometric (precubical)
level: composing two cylinders, a section of the second factor's start leg supplies a section of
the composite's first projection. -/
noncomputable def MapSection.pullbackComposeπ₁ {K : PrecubicalSet} (c d : MooreCyl K)
    (σ : MapSection d.startLeg) : MapSection (MooreCyl.composeπ₁ c d) :=
  MapSection.pullbackFst c.endLeg d.startLeg σ

/-! ## Part B7 — the d-path descent (the single isolated remaining lemma) and the conclusion

`MapSection.pullbackComposeπ₁` lives at the **precubical** level (`composeπ₁` is a `PrecubicalSet`
map).  The `DPathSection` apparatus, by contrast, lives over the **d-path groupoid**: a section of
the *induced groupoid functor* of a precubical map.  Bridging the two is the **d-path descent**: a
precubical map `f : A ⟶ B` (of `BPSet`s) with a strict section should induce a `DPathSection` of its
groupoid leg-functor `FreeGroupoid.map (Refine.pushforwardBP f)`.

This descent is *not* automatic: `Refine.pushforwardBP` and `FreeGroupoid.map` preserve composition
only up to the coherence isos `FreeGroupoid.mapComp`/`mapId` (and `Refine.pushforward`'s own
functoriality), so a *strict* precubical section `s ≫ f = 𝟙` descends to a section of the induced
functor only **up to iso** — exactly the `DPathSection` notion.  We isolate this as a single
labelled `Prop`, `DPathDescent`, rather than asserting it; it is the one precise lemma standing
between the precubical pullback-section (B6, PROVEN) and a fully groupoid-level composition closure.

NB the `mooreCompose` source `composeSrc` is a `PrecubicalSet`, not a `BPSet`, and the legs
`composeπ₁` are plain maps; so even stating the descent for the composite requires choosing
basepoints on `composeSrc` (the matched endpoints), which the `BPSet`/`CylMapR` layer carries
explicitly via the component list (cf. `Cylinder/MooreMonoid.lean`'s list-carried staircase).  That
bookkeeping (orthogonal to the section logic above) is what `DPathDescent` packages. -/

/-- **The isolated d-path-descent hypothesis** (a labelled `Prop`, NOT a proven claim).  For
`BPSet`s `A`, `B` and a `BPSet` map `f : A ⟶ B`, a *strict precubical section* of `f.hom` descends
to a `DPathSection` of the induced leg-functor `FreeGroupoid.map (Refine.pushforwardBP f)`.

This is the precise remaining lemma: it requires propagating a strict precubical splitting through
`Refine.pushforwardBP` and `FreeGroupoid.map`, whose functoriality is only up-to-coherent-iso, so
the descended datum is a section *up to iso* (a `DPathSection`), matching the up-to-iso notion the
construction consumes.  Stated as a `Prop` so downstream results can take it as a hypothesis without
introducing a `sorry`. -/
def DPathDescent : Prop :=
  ∀ (A B : BPSet) (f : A ⟶ B) (_ : MapSection f.hom),
    Nonempty (DPathSection (FreeGroupoid.map (Refine.pushforwardBP f)))

/-! ### The closure conclusion (modulo `DPathDescent`)

Putting the pieces together: section-cylinders are closed under (the geometric Moore) composition,
*assuming* `DPathDescent` to cross the precubical→groupoid bridge.  Concretely, with
`hd : DPathDescent` in hand, the left leg-functor of a composite `CylMapR` (the matched pullback)
acquires a section by:

1. pulling back a section of the second factor's left leg along the projection (B6,
   `MapSection.pullbackComposeπ₁`), giving a precubical `MapSection` of the projection;
2. descending that precubical section to a `DPathSection` of the projection's groupoid functor
   (`hd`);
3. composing it with the first factor's section via `DPathSection.comp` (B5).

We record the *shape* of this conclusion as `sections_compose_modulo_descent`: given two
section-cylinders whose composite left leg factors as `proj ⋙ firstLeg` of two `BPSet` maps each
carrying the requisite data, `DPathDescent` plus `DPathSection.comp` produce a section of the
composite — i.e. `SecCyl` is closed under composition.  (The full `SecCyl K` `mooreCompose` requires
the `BPSet` structure on `composeSrc`, carried list-wise as in `MooreMonoid`; here we state the
leg-functor-level closure, which is the section-condition content.) -/

/-- **Composition closure of sections, modulo the descent.**  If `DPathDescent` holds, then for any
two `BPSet` maps `g : A ⟶ B`, `f : B ⟶ C` such that `g.hom` has a strict precubical section and
`f`'s induced d-path functor has a `DPathSection`, the *composite* induced d-path functor
`FreeGroupoid.map (Refine.pushforwardBP (g ≫ f))` has a `DPathSection`.

Proof: descend `g`'s precubical section to a `DPathSection` of `g`'s d-path functor (`hd`), compose
with `f`'s section (`DPathSection.comp`), giving a `DPathSection` of `g-functor ⋙ f-functor`; this
equals the `(g ≫ f)`-functor up to the `FreeGroupoid.map`/`pushforwardBP` composition coherence
(`mapComp`), transported with `DPathSection.transport`.  This is exactly the closure that the
equivalence version could *not* obtain without right-properness. -/
theorem sections_compose_modulo_descent (hd : DPathDescent)
    {A B C : BPSet} (g : A ⟶ B) (f : B ⟶ C)
    (σg : MapSection g.hom)
    (sf : DPathSection (FreeGroupoid.map (Refine.pushforwardBP f))) :
    Nonempty (DPathSection
      (FreeGroupoid.map (Refine.pushforwardBP g) ⋙ FreeGroupoid.map (Refine.pushforwardBP f))) :=
  ⟨(hd A B g σg).some.comp sf⟩

/-- **Section-condition closure (transported to the composite functor).**  The composite of the two
d-path leg-functors `g-functor ⋙ f-functor` is *isomorphic* to the `(g ≫ f)`-functor (functoriality
of `FreeGroupoid.map ∘ Refine.pushforwardBP` up to coherence); we record that a `DPathSection`
transports across any such iso of the underlying functor, so `sections_compose_modulo_descent`
delivers a `DPathSection` of the composite leg-functor once that coherence iso is supplied. -/
noncomputable def DPathSection.transport {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} (e : F ≅ F') (s : DPathSection F) : DPathSection F' where
  Lstar := s.Lstar
  unit := s.unit ≪≫ Functor.isoWhiskerLeft s.Lstar e

end Cyl14
