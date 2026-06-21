# Cyl1_Algebra — converse of `pointedOfPaths`, non-surjectivity, monad structure

Scratch investigation in the cylinder ⟹ pointed-functor program (RESULT 2).
Lean file: `CubeChains/Research/Scratch/Cyl1_Algebra.lean`.
Build: `lake build CubeChains.Research.Scratch.Cyl1_Algebra` — **green, sorry-free.**

This writeup is self-contained.  The Lean below is all PROVEN unless a line is explicitly
marked CONJECTURE / OPEN.

---

## 0. The question

`Cylinder/PointedFunctor.lean` defines, for a category `C`,

```
pointedOfPaths (F₀ : C → FreeGroupoid C) (η : ∀ x, (of C).obj x ⟶ F₀ x)
    : PointedEndofunctor (FreeGroupoid C)
```

— from *object-data* alone (an object-map and one chosen path per object), with naturality free
by the conjugation trick (`conjFunctor` + `conjNatIso` + `FreeGroupoid.liftNatIso`).  Its
docstring claims:

> "since every such transformation is a conjugation, **every** pointed endofunctor [of a free
> groupoid] arises this way."

The three tasks:

1. **Prove that converse** in Lean (ideally on the nose).
2. **Quantify non-surjectivity** of the cylinder construction using (1).
3. **Classical CT (monads):** does a cylinder `(F, η)` extend to a monad? is it *well-pointed*
   (`Fη = ηF`, Kelly)? is `F` idempotent / the point a reflective-localization unit?

---

## 1. The converse — PROVEN ON THE NOSE

**Headline:** the converse holds as a strict *equality* of pointed endofunctors, not merely up
to iso.

For `P : PointedEndofunctor (FreeGroupoid C)` define its object-data:

```
objMap  P : C → FreeGroupoid C        := fun x => P.F.obj (of x)
pathMap P : ∀ x, of x ⟶ objMap P x    := fun x => P.pt.app (of x)
```

### Lemmas (all proven)

- `pt_naturality_generator P f` :
  `P.F.map (of.map f) = (η x)⁻¹ ≫ of.map f ≫ η y`.
  The naturality square of `P.pt` at the *generator* `of.map f` is exactly the conjugation
  formula `conjFunctor` uses.  Proof: `P.pt.naturality (of.map f)` + invert the iso component
  `pt_x` (via `IsIso.inv_hom_id_assoc`).

- `objData_F P : P.F = (pointedOfPaths (objMap P) (pathMap P)).F`.
  `(pointedOfPaths …).F = lift (conjFunctor (of C) (objMap P) (pathMap P))`, and
  `FreeGroupoid.lift_unique` pins it to `P.F` because `of C ⋙ P.F` agrees with the conjugation
  on objects (definitionally) and on generators (`pt_naturality_generator`).  **On the nose.**

- `pointedOfPaths_pt_app_mk F₀ η x : (pointedOfPaths F₀ η).pt.app (of x) = η x`.
  The point is `liftNatIso (… conjNatIso …)`; `liftNatIso_hom_app` collapses its component at the
  generator `mk x` to the `conjNatIso` component, which is `η x`.

- **`pointedOfPaths_objData P : pointedOfPaths (objMap P) (pathMap P) = P`** — the deliverable.
  Uses the helper `pointedEndofunctor_ext'` (functor equality + `HEq`/component equality of the
  points).  The points agree on every generator `mk x` (both are `η x`), and *every* object of a
  free groupoid is `mk (Z.as.as)` via `FreeGroupoid.of_obj_bijective`, so they agree everywhere.

### Why on-the-nose works (it fought a little)

- The functor equality is forced by `lift_unique`, which is a *strict* universal property —
  no iso slack.  The only friction was `rw` failing on free-groupoid composites
  (instance mismatch `Functor.category…` vs `Category…`); fixed with `erw` and the
  `IsIso.inv_hom_id_assoc` cancellation, per the project's `erw`-not-`rw` convention.
- The point equality needed `HEq` only because the two functors are *propositionally* (not
  syntactically) equal; once `objData_F` substitutes them, the points are honest `NatTrans`es
  agreeing pointwise.

So: **the converse is an equality, and `pointedOfPaths` is a surjection onto
`PointedEndofunctor (FreeGroupoid C)`.**

---

## 2. Non-surjectivity of the cylinder construction — PROVEN (abstract half)

The clean statement is a **bijection**:

```
objDataEquiv : ObjData C ≃ PointedEndofunctor (FreeGroupoid C)
  where ObjData C := Σ F₀ : C → FreeGroupoid C, ∀ x, of x ⟶ F₀ x
```

- `toFun (F₀, η) = pointedOfPaths F₀ η`;
- `invFun P = (objMap P, pathMap P)`;
- `right_inv = pointedOfPaths_objData` (§1);
- `left_inv` from `objMap_pointedOfPaths` (object map is `F₀` on the nose) and
  `anyObjData_realized` (the path component is `η`, recovered unchanged).

Supporting proven lemmas: `objMap_pointedOfPaths`, `anyObjData_realized`, `objData_injective`
(distinct object-data ⟹ distinct pointed endofunctors).

**Interpretation.**  The codomain `PointedEndofunctor (DPathGrpdR K)` is parametrised by
**ARBITRARY object-data** `(F₀, η)`: an arbitrary object-map `C → FreeGroupoid C` *and* an
arbitrary path per object.  The cylinder construction `cylToPointedObj c`
(`Cylinder/CylinderRefine.lean`) factors through `pointedOfPaths` but feeds in object-data from a
**strict subclass**:

- `F₀ x = Rgrpd (Lgrpd⁻¹ x)` — the value is `Rgrpd` applied to a single *functorially*
  transported chain `Lgrpd⁻¹ x`, i.e. `F₀` is the object-action of the **functor**
  `Lgrpd⁻¹ ⋙ Rgrpd`.  An arbitrary `F₀ : C → FreeGroupoid C` need not even be functorial (need
  not respect any composition), so most object-maps are unreachable.
- `η x = counit.inv ≫ sweepR (Lgrpd⁻¹ x)` — one *canonical* homotopy determined by the cylinder
  geometry, not a free choice of path.

By `objData_injective`, two object-data give the same pointed endofunctor iff they are equal, so a
*fixed* cylinder `c` hits exactly **one** point of the codomain, while `objDataEquiv` shows the
codomain has a point for *every* element of the (vastly larger) space `ObjData (RefineObj K)`.

**What is Lean-backed:** the "arbitrary object-data" half — that `pointedOfPaths` realizes any
`(F₀, η)` and that the parametrisation is a bijection.  The complementary half — exhibiting a
*specific* `(F₀, η)` provably outside `{(Rgrpd∘Lgrpd⁻¹, counit≫sweepR) : c}` — is geometry-side
and not formalised here (it needs the full cylinder stack and a non-functorial / non-canonical
witness); it is argued structurally above.  This is the honest boundary.

---

## 3. Classical category theory: monads, well-pointedness, idempotency

### 3(b) Well-pointedness (Kelly) — characterisation PROVEN

A pointed endofunctor is well-pointed when `F ◫ pt = pt ◫ F`:

```
IsWellPointed P := ∀ Z, P.F.map (P.pt.app Z) = P.pt.app (P.F.obj Z)
```

**`isWellPointed_iff` (PROVEN):**
```
IsWellPointed (pointedOfPaths F₀ η) ↔ ∀ x, F.map (η x) = pt.app (F₀ x).
```
The reduction to generators is exact: every object is `mk x`, and `F.map (pt.app (mk x)) =
F.map (η x)` (`F_map_pt_app_mk`).  So well-pointedness is the **genuine, generally non-trivial**
equation `F.map (η x) = pt.app (F₀ x)` — `F.map (η x)` is the conjugate transport of `η x`,
while `pt.app (F₀ x)` is the chosen path at the *target* object `F₀ x`; these are independent
data unless `(F₀, η)` cohere.  In a groupoid base this is **not** free (contrast the codiscrete
*morphism* structure in 3-extra).

**`trivial_isWellPointed` (PROVEN):** the trivial object-data `F₀ x = mk x`, `η x = 𝟙` (the
identity-like pointed endofunctor) is well-pointed — a positive anchor.

> CONJECTURE (3b for cylinders).  The cylinder's `(F₀, η) = (Rgrpd∘Lgrpd⁻¹, counit≫sweepR)` is
> **not** well-pointed in general.  Reasoning: `pt.app (F₀ x)` is `counit≫sweepR` at the *already
> swept* chain `F₀ x = Rgrpd(Lgrpd⁻¹ x)`, i.e. a *second* sweep, whereas `F.map (η x)` is the
> conjugate of the *first* sweep; for a multi-block cylinder these traverse different prism
> staircases and there is no a-priori reason they coincide.  No Lean witness here (needs the
> geometry stack).

### 3(c) Idempotency — object-level characterisation PROVEN

`comp_F_obj_mk` (PROVEN): `(F ⋙ F).obj (mk x) = F.obj (F₀ x)`.  Hence `F` is idempotent **on
objects** (`F.obj (F.obj Z) = F.obj Z`) iff `F.obj (F₀ x) = F₀ x` for all generators `x`.

> CONJECTURE (3c).  For the cylinder `F = Lgrpd⁻¹⋙Rgrpd`, idempotency on objects is
> `Rgrpd(Lgrpd⁻¹(Rgrpd(Lgrpd⁻¹ x))) = Rgrpd(Lgrpd⁻¹ x)`, which holds when the right leg lands in
> the essential image stabilised by `Lgrpd⁻¹⋙Rgrpd`.  Full idempotency (`F⋙F ≅ F` as functors,
> with the point an idempotent-monad unit / reflective localisation) is OPEN; in a *connected*
> free groupoid `F` is an equivalence (point is iso), so a non-trivial idempotent would force
> `F ≃ 𝟭`, suggesting the only idempotent cylinders are essentially identities.

### 3(a) Monad extension — CONJECTURE with reasoning

A pointed endofunctor is "a monad without multiplication."  Does `(F, η)` extend (`μ : F⋙F ⟹ F`,
`η` the unit, satisfying the monad laws)?

- **Structural observation (PROVEN, `pointedOfPaths_pt_isIso`, also `pt_isIso` in the library):**
  in a groupoid base the point `pt` is *always* a natural **iso**.  So `(F, η)` is never a strict
  pointed endofunctor with a non-invertible unit.
- **Consequence (reasoning):** if `pt : 𝟭 ≅ F` is iso, then `F ≅ 𝟭`, so `F⋙F ≅ F ≅ 𝟭` and a
  multiplication `μ := pt⁻¹ ◫ ?` exists trivially — *every* such `(F, η)` extends to a monad, but
  the monad is (isomorphic to) the **identity monad**.  This matches the memory note
  `[[cubechains-cylinder-roadmap]]`: `PointedEndofunctor(Grpd)` is **codiscrete** on morphisms
  (`pointedHomOfGroupoid` is the unique map), so the algebra is degenerate and the naive
  "cylinders ⊣ pointed-endofunctors" adjunction is degenerate.  The *meaningful* monad/algebra
  content lives one level down (the geometric `⊗□¹ ⊣ PathOb`, or Tier-2 homotopical descent), not
  in this groupoid-pointed-endofunctor layer.
- **Status:** the "extends to a monad" answer is **YES but trivially** (identity-monad-up-to-iso),
  formalisation of the explicit `μ` not done (low value given degeneracy); marked CONJECTURE only
  in that the explicit monad object isn't built in Lean.

---

## Summary of Lean status

| Result | Lean name | Status |
|---|---|---|
| Converse of `pointedOfPaths`, on the nose | `pointedOfPaths_objData` | **PROVEN** |
| — functor half | `objData_F` | **PROVEN** |
| — generator naturality = conjugation | `pt_naturality_generator` | **PROVEN** |
| — point at generator | `pointedOfPaths_pt_app_mk` | **PROVEN** |
| Object-data bijection | `objDataEquiv` | **PROVEN** |
| `pointedOfPaths` realizes any data | `anyObjData_realized`, `objMap_pointedOfPaths` | **PROVEN** |
| Distinct data ⟹ distinct functors | `objData_injective` | **PROVEN** |
| Well-pointedness ⇔ generator condition | `isWellPointed_iff` | **PROVEN** |
| Trivial data is well-pointed | `trivial_isWellPointed` | **PROVEN** |
| Idempotency on objects | `comp_F_obj_mk` | **PROVEN** |
| Point always iso (groupoid) | `pointedOfPaths_pt_isIso` | **PROVEN** |
| Cylinder data not well-pointed (general) | — | CONJECTURE (reasoning) |
| Cylinder monad = identity-up-to-iso | — | CONJECTURE (reasoning; degenerate) |
| Specific data outside cylinder image | — | OPEN (geometry-side) |

## Headline conclusions

- The docstring claim is **true and provable on the nose**: `pointedOfPaths` is a *bijection*
  `ObjData C ≃ PointedEndofunctor (FreeGroupoid C)`.  Pointed endofunctors of a free groupoid
  ARE exactly object-data.
- The cylinder construction is therefore non-surjective for the sharp reason that its object-data
  is *functorial and canonical* (`Rgrpd∘Lgrpd⁻¹`, `counit≫sweepR`), a measure-zero slice of the
  arbitrary `ObjData (RefineObj K)`.
- **Most interesting discovery:** because the base is a groupoid, the point is *always* a natural
  iso, so `F ≅ 𝟭` and the whole `PointedEndofunctor(Grpd)` layer is degenerate (every object
  trivially extends to the identity monad; morphisms are forced/codiscrete).  Well-pointedness,
  though, is **not** free — `isWellPointed_iff` isolates the one genuine equation
  `F.map (η x) = pt.app (F₀ x)`, the only place real homotopical content can hide at this layer.
- **Sharpest open question:** is the cylinder's `(Rgrpd∘Lgrpd⁻¹, counit≫sweepR)` well-pointed
  (`F.map (η x) = pt.app (F₀ x)`)?  A NO would give the first genuinely non-degenerate invariant
  distinguishing cylinders at this layer; a YES would say cylinders are "double-sweep coherent"
  and collapse further toward the identity.
