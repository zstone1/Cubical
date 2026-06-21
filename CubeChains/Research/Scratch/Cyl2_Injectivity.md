# Cyl2_Injectivity — fibers of `cylToPointedR`, its universal property, and the `η`-constraint

**Status:** `Cyl2_Injectivity.lean` is **green and sorry-free** under
`lake build CubeChains.Research.Scratch.Cyl2_Injectivity`. Every lemma named below is backed by
Lean.

Topic (user items 0 and 3): *How injective is `cylToPointedR`, what universal/structural property
characterizes its fibers, and what constrains the induced `η x` maps?*

The construction recap (from `Cylinder/CylinderRefine.lean`):
`cylToPointedObj c = pointedOfPaths (F₀ c) (η c)` where, writing `Lgrpd`/`Rgrpd` for the two
leg-functors on `DPathGrpdR K = FreeGroupoid (RefineObj K.init K.final)`,

* `F₀ c x = c.Rgrpd.obj (c.Lgrpd.inv.obj (of x))`  (the transported right leg `Lgrpd⁻¹ ⋙ Rgrpd`);
* `η c x  = (Lgrpd counit).inv (of x) ≫ sweepR c (Lgrpd.inv (of x)).as.as`  (counit-corrected sweep).

---

## ASKED

0. **Injectivity / fibers.** Pin down precisely what data of `c` the endofunctor remembers vs
   forgets. Identify the kernel of `cylToPointedObj` on objects; prove a sufficient collision
   condition. Is there a universal property (initial/terminal cylinder per fiber; (co)reflection)?
3. **Constraint on the `x → F₀ x` maps.** The `η x` are not arbitrary free-groupoid words — they
   come from `sweepR` (a fence of genuine `ChainRefine` arrows) composed with the equivalence
   counit. Characterize the constraint; prove `η`'s geometry needs no *formal* inverse except the
   counit.

---

## PROVEN (sorry-free Lean)

### (A) What the construction remembers / forgets — the kernel of `pointedOfPaths`

* **`Cyl2.pointedOfPaths_congr`** — `pointedOfPaths F₀ η = pointedOfPaths F₀' η'` whenever
  `F₀ = F₀'` and `HEq η η'`. Proof: `subst` + `eq_of_heq` + `rfl`.
  This is the rigorous form of *"the construction remembers nothing but `(F₀, η)`"*: `pointedOfPaths`
  is literally a function of its two arguments. Everything else of the cylinder (its source `src`,
  the higher cells of `cyl`, the particular subdivision-words realising `sweepR`, …) is **forgotten**.
  Companion: `pointedOfPaths_congr_of_eq` (definitionally-equal `F₀`, plain equality of `η`).

* **`CylMapR.ptObj` / `CylMapR.ptHom`** — the named object-data of a weak-equivalence cylinder
  (`F₀ c`, `η c` above), and **`cylToPointedObj_eq_pointedOfPaths`** = the definitional identity
  `cylToPointedObj c = pointedOfPaths (ptObj c) (ptHom c)`.

### (B) Collision condition (the kernel on objects)

* **`CylMapR.cylToPointedObj_eq_of`** — *the sharpest sufficient condition proved:*
  if `ptObj c = ptObj c'` (equal transported legs) **and** `HEq (ptHom c) (ptHom c')` (equal
  counit-corrected sweeps), then `cylToPointedObj c = cylToPointedObj c'`.
  This is exactly the fiber relation: **two cylinders collide iff their `(F₀, η)` agree.** It is a
  clean, *complete* description of the kernel-on-objects (the converse is `rfl`-trivial from
  `cylToPointedObj_eq_pointedOfPaths`), so it is not merely sufficient — it characterizes the fiber.

  *Remember/forget summary.* Remembers: the transported right leg `Lgrpd⁻¹ ⋙ Rgrpd` on objects
  (`F₀`) and the one chosen homotopy `η x` per chain. Forgets: the source `src`, all higher cells
  of `cyl` not seen through these two, and the internal word-structure of `sweepR` (only its value
  as a groupoid arrow survives).

### (C) The constraint on `η` (item 3)

* **`Cyl2.OfClosure`** — wide inductive predicate on morphisms of a free groupoid: the smallest
  class containing every `(FreeGroupoid.of C).map f` (genuine forward `C`-arrow) and every
  `eqToHom h`, closed under composition and `Groupoid.inv`. Membership = *"a zigzag of genuine
  refinements, using no formal inverse beyond inverting actual arrows."*
  - `OfClosure.id`, `OfClosure.map` (the closure is preserved by `FreeGroupoid.map φ` — base cases
    via `FreeGroupoid.of_comp_map` and `eqToHom_map`; inv via `Functor.map_inv` + `Groupoid.inv_eq_inv`).

* **`CylMapR.ofClosure_sweepTail`, `ofClosure_sweepFirst`, `ofClosure_sweepR`** — the total sweep
  `sweepR c a` lies in `OfClosure` for every source chain `a`. Proved by structural recursion on the
  block list, `unfold`-ing the (tactic-defined, equation-lemma-less) `sweepTail`/`sweepFirst` and
  matching the staircase term shape: each step is `eqToHom ≫ (whiskered tail) ≫ (eqToHom ≫
  of.map bridge) ≫ (inv (of.map top)) ≫ eqToHom` — all closure operations; the tail recursion is
  re-whiskered by `OfClosure.map`.

* **`CylMapR.ptHom_eq_counit_comp_ofClosure`** — *the answer to item 3:* every induced point factors
  `ptHom c x = (Lgrpd counit).inv (of x) ≫ w` with `w ∈ OfClosure`. So the **geometry** contributes
  only a zigzag of *actual* `ChainRefine` arrows; **the only formal inverse a point ever uses is the
  equivalence counit** of `Lgrpd⁻¹`. This is the precise analogue of "which `x → F₀ x` are
  realizable": the realizable points are exactly `counit.inv ≫ (positive-and-inverse-refinement
  zigzag)`.

### (Universal property) The image is codiscrete — cylinders are uniquely isomorphic

* **`Cyl2.pointed_subsingleton`** — between any two pointed endofunctors of a *groupoid* base the
  hom-set is a `Subsingleton` (the point axiom `A.pt ≫ τ = B.pt` forces `τ = inv A.pt ≫ B.pt`).
* **`Cyl2.pointedIsoOfGroupoid`**, **`Cyl2.pointed_isIso`** — that unique morphism is an iso; so the
  full subcategory is **codiscrete** (indiscrete: a unique iso between any two objects).
* **`CylMapR.cylToPointedR_map_isIso`**, **`CylMapR.cylToPointedObj_iso`** — therefore
  `cylToPointedR` sends *every* cylinder-map to an iso, and **any two cylinders over `K` induce
  canonically (uniquely) isomorphic pointed endofunctors.**

  *Consequence for the universal-property question.* Up to isomorphism the target has **no fiber
  structure at all** (all objects in the image are uniquely isomorphic), so there is **no nontrivial
  initial/terminal cylinder per fiber and no (co)reflection to detect** — the naive "universal
  cylinder" / split-(co)reflection question **degenerates**. (This confirms, and now Lean-backs, the
  `[[cubechains-cylinder-roadmap]]` note that `PointedEndofunctor(Grpd)` is codiscrete.) The only
  *non-degenerate* injectivity content is the **literal** `(F₀, η)` kernel of (A)/(B).

---

## CONJECTURED (with reasoning; not yet Lean)

* **Strict-injectivity conjecture (the honest fiber question).** The literal fibers of
  `cylToPointedObj` are *large*: many genuinely different cylinders share one `(F₀, η)`. Reasoning:
  `F₀` only sees the transported legs on *objects*, and `η x` only the single composite
  `counit.inv ≫ sweepR(...)` as a groupoid *value*; two cylinders with the same legs but `cyl`s that
  differ only in cells invisible to `sweepR`'s value (e.g. an interior 2-cell of the homotopy that
  doesn't change any block's prism face) will collide via `cylToPointedObj_eq_of`. A concrete
  witness should be constructible in `Testing/` (a `FinBPSet` with two distinct cyl-fillers of the
  same boundary). *Status:* plausible, matches the user's intuition ("different top, same
  endofunctor"); needs a worked example (belongs partly to `Cyl3_Examples`).

* **Tautological cylinder.** `CylMap.tauto K = Over.mk (𝟙 (PathOb K))` is *terminal* in
  `CylMap K = Over (PathOb K)`. Conjecture: its `CylMapR` analogue (when it is a weak equivalence)
  induces the endofunctor whose `F₀`/`η` are the "identity-up-to-counit" data, i.e. it is a
  *neutral* element of the image. Because the image is codiscrete this is automatically iso to every
  other induced endofunctor, so the statement is only interesting at the *literal* `(F₀, η)` level.
  *Status:* not pursued — the codiscreteness result makes it categorically vacuous up to iso.

---

## OPEN

* **Exact size of the literal fiber.** Give a clean *iff* characterization of `(F₀, η)` collision
  directly in terms of cylinder data (legs + a finite list of per-block prism faces), eliminating
  the `HEq` and the transported-leg indirection. This would turn `cylToPointedObj_eq_of` from a
  sufficient (and `rfl`-converse) condition into a fully geometric criterion.

* **Is `OfClosure` *exactly* the constraint on `η`?** We proved `η = counit.inv ≫ w`, `w ∈
  OfClosure` (necessary side). Open: a *converse* realizability statement — which pairs
  `(counit.inv, w)` with `w ∈ OfClosure` actually arise from some cylinder `c`? (The analogue of the
  realizability program for `x → F₀ x` maps.) Likely needs the homotopy-generation results of
  `Cyl4_Generation`.

* **Beyond codiscreteness.** The degeneracy "all cylinders uniquely isomorphic" is an artifact of
  landing in `PointedEndofunctor(Grpd)`. A non-degenerate target (the geometric `⊗□¹ ⊣ PathOb`
  adjunction, or a Tier-2 homotopical/non-groupoid base) would give the fibers real structure; the
  `(F₀, η)` kernel computed here is the invariant that *should* survive that refinement.

---

## Files / lemma index

`CubeChains/Research/Scratch/Cyl2_Injectivity.lean`:
- `Cyl2.pointedOfPaths_congr`, `pointedOfPaths_congr_of_eq` — kernel of `pointedOfPaths`.
- `CylMapR.ptObj`, `ptHom`, `cylToPointedObj_eq_pointedOfPaths`, `cylToPointedObj_eq_of` — the
  cylinder fiber relation (A)/(B).
- `Cyl2.OfClosure` (+ `.id`, `.map`); `CylMapR.ofClosure_of_refine`, `ofClosure_sweepTail`,
  `ofClosure_sweepFirst`, `ofClosure_sweepR`, `ptHom_eq_counit_comp_ofClosure` — the `η`-constraint
  (C).
- `Cyl2.pointed_subsingleton`, `pointedIsoOfGroupoid`, `pointed_isIso`;
  `CylMapR.cylToPointedR_map_isIso`, `cylToPointedObj_iso` — codiscreteness / universal property.
