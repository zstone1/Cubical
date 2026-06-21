# Cyl6_Monoid — the monoid of pointed endofunctors, and the cylinder image as a submonoid

Scratch findings for the cylinder ⟹ pointed-functor program (RESULT 2). Companion to
`Cyl6_Monoid.lean` (decoupled from the green build; `lake build
CubeChains.Research.Scratch.Cyl6_Monoid`, **sorry-free and green**).

## The lens (why a monoid, not a category)

Earlier scratch work (Cyl2/Cyl3/Cyl5) established that, over a *groupoid* base, the **category**
`PointedEndofunctor 𝒢` is degenerate:

* it is **thin** (`Cyl2.pointed_subsingleton` / `Cyl5.pointedEndofunctor_isThin`): at most one
  morphism between any two objects, because the point axiom `A.pt ≫ τ = B.pt` with `A.pt` an iso
  forces `τ = A.pt⁻¹ ≫ B.pt`;
* every morphism is an **iso** (`Cyl2.pointed_isIso`), so all objects are *uniquely isomorphic*.

A thin category in which all objects are isomorphic is **contractible** — equivalent to the
terminal category. So the categorical structure forgets everything up to iso; it is the wrong lens.

But the **set of objects** carries a genuine **monoid** under composition of endofunctors, which the
category structure completely ignores. This file builds that monoid and asks whether the cylinder
construction's image is a *submonoid*.

---

## 1. Monoid structure — PROVEN (a full `Monoid` instance, strict)

`Monoid (PointedEndofunctor 𝒞)` for **any** category `𝒞` (groupoid not needed):

* `1 = ⟨𝟭 𝒞, 𝟙 (𝟭 𝒞)⟩`;
* `A * B = ⟨A.F ⋙ B.F, A.pt ≫ whiskerLeft A.F B.pt⟩`.

The point order/type checks out: `whiskerLeft A.F B.pt : A.F ⋙ 𝟭 ⟶ A.F ⋙ B.F`, and `A.F ⋙ 𝟭 =
A.F` is `rfl`, so `A.pt ≫ whiskerLeft A.F B.pt : 𝟭 ⟶ A.F ⋙ B.F`. The component formula is
`(A * B).pt.app X = A.pt.app X ≫ B.pt.app (A.F.obj X)` (`mul_pt_app`, `rfl`).

**Strictness.** Associativity and unitality hold **on the nose** (no coherence `eqToHom`):

* the `F` field laws (`𝟭 ⋙ A.F = A.F`, `A.F ⋙ 𝟭 = A.F`, `(A.F ⋙ B.F) ⋙ C.F = A.F ⋙ (B.F ⋙
  C.F)`) are `rfl`, because `Functor.comp` is definitionally strict (`Functor.id_comp`/`comp_id`
  are `rfl`; composition is definitionally associative);
* the `pt` field laws are then discharged by `NatTrans` extensionality + whiskering simp lemmas
  (`heq_of_eq; ext X; simp`). The associativity component on both sides is literally
  `A.pt.app X ≫ B.pt.app (A.F.obj X) ≫ C.pt.app (B.F.obj (A.F.obj X))`.

So the fallback to `Mul`+`One`+lemmas was **not** needed: it is a clean strict `Monoid`.

Lemmas: `mul_F`, `mul_pt`, `one_F`, `one_pt`, `mul_pt_app`, then the `Monoid` instance
(`one_mul`/`mul_one`/`mul_assoc`).

**Off-the-shelf note.** Mathlib has `Monad` (= `Mon_` in endofunctors, the unit+multiplication
algebra) and the whiskering API, but no "monoid of *pointed* endofunctors" — a pointed endofunctor
is "a monad without multiplication", so its objects do *not* assemble into a monoidal-internal
structure that mathlib already names. The whiskering lemmas (`whiskerLeft_comp`, `whiskerLeft_id`,
`whiskerLeft_app`, …) were reused; the monoid itself is hand-rolled (3 short proofs).

---

## 2. Product in object-data terms — PROVEN

Via `Cyl1.objDataEquiv` (the bijection `ObjData C ≃ PointedEndofunctor (FreeGroupoid C)`), the
monoid product transports to a binary operation on object-data. We compute it explicitly:

For object-data `(F₀, η)` and `(G₀, θ)`, writing `B = pointedOfPaths G₀ θ`:

* **product object map** (on a generator `x`):
  `objMap (pointedOfPaths F₀ η * pointedOfPaths G₀ θ) x = B.F.obj (F₀ x)`
  (`mul_pointedOfPaths_objMap`, `rfl`) — apply the second factor's *lifted* endofunctor `B.F` to
  the first factor's target `F₀ x`;
* **product path** (on a generator `x`):
  `pathMap (… * …) x = η x ≫ B.pt.app (F₀ x)`
  (`mul_pointedOfPaths_pathMap`) — first path, then the second factor's point at the transported
  object.

The packaged statement is `mul_pointedOfPaths`: the product is again `pointedOfPaths` of its own
(now explicitly computed) object-data, read off from the on-the-nose converse
`Cyl1.pointedOfPaths_objData`.

**Key subtlety (load-bearing for §5).** `B.F.obj (F₀ x)` is the **lift** `B.F` applied to `F₀ x`,
which is in general **not a generator** `of y`. So `B.F` acts by *conjugation* there, not by the
simple object map `G₀`. The product object map is therefore a genuine *stacking* of the two
endofunctors, not a pointwise composite of the two raw object maps `G₀ ∘ F₀`.

---

## 3. Unit ∈ image — PROVEN (algebraic core); reduces to one geometric input

* **Algebraic core (PROVEN, on the nose).** The tautological object-data `(of, 𝟙)` induces
  *literally* the monoid unit: `taut_eq_one : pointedOfPaths (of) (𝟙) = 1`. Proof: its underlying
  functor is `𝟭` (`Cyl3.pointedOfPaths_id_F` = `lift (conjFunctor of of 𝟙) = lift of = 𝟭`), and
  its point is `𝟙` on every generator (`pointedOfPaths_pt_app_mk` gives `tautη x = 𝟙`), hence
  everywhere.

* **Reduction (PROVEN).** `one_mem_cylImage_of_taut`: if some weak-equivalence cylinder `c` has
  `cylToPointedObj c = pointedOfPaths (of) (𝟙)`, then `1 ∈ cylImage K`.

* **Remaining geometric input (NOT formalised here).** Exhibiting that tautological cylinder over a
  given `K` — geometrically the cylinder `K × □¹` with both legs the identity, whose `sweepR` is the
  trivial homotopy. This is plausible but is genuine cylinder geometry (the `cyl : src → PathOb K`
  data with `src = K`), out of scope for this algebra-focused scratch. **Status of unit ∈ image:
  PROVEN modulo exhibiting the tautological cylinder** (a clearly-isolated geometric one-liner).

---

## 4. Contractibility — PROVEN

`pointedEquivPUnit : PointedEndofunctor 𝒢 ≌ Discrete PUnit` for any groupoid `𝒢` — an equivalence
of **categories** to the terminal category. Built from:

* `toPUnit` / `fromPUnit` (constant functors);
* `unitIso` via `Cyl3.pointedUniqueIso A 1` (the forced iso to the basepoint `1`), naturality free
  by thinness (`Subsingleton.elim`);
* `counitIso = Iso.refl`, all coherence by `Subsingleton.elim`.

This is the formal justification that "the category is the wrong lens; the monoid is the right one":
the category remembers exactly one isomorphism class.

---

## 5. Submonoid closure — UNIT half PROVEN(-modulo-geometry); CLOSURE half OPEN, obstruction PINNED

Question: is `cylImage K := Set.range cylToPointedObj` a **submonoid** of `PointedEndofunctor
(DPathGrpdR K)`?

### Unit ∈ `cylImage K`
See §3: PROVEN modulo the tautological cylinder.

### Closed under `·` — **OPEN. This is the open theorem.**

We **reduce** it cleanly and **pin the obstruction**, but do **not** prove it (and there is good
reason to expect it can FAIL — see below).

* **Reduction (PROVEN).** `mul_mem_cylImage_of_compose`: `cylImage K` is closed under `·` *iff* for
  every pair of weak-equivalence cylinders `c, c'` there is a single weak-equivalence cylinder `d`
  with `cylToPointedObj d = cylToPointedObj c * cylToPointedObj c'`. So the whole geometric content
  is "a cylinder composition realising the monoid product".

* **The would-be witness's object map (PROVEN explicit).** `mul_cylToPointedObj_objMap`: the
  product's object map on a generator `x` is
  `(cylToPointedObj c').F.obj ((Rgrpd ∘ Lgrpd⁻¹) x)` — the second factor's *lifted endofunctor*
  applied to the first transport. The needed cylinder `d` would have to have transport
  `Rgrpd_d ∘ Lgrpd_d⁻¹` equal to this *stacked* map.

* **The obstruction (CONJECTURED to be fatal; root cause identical to roadmap STEP 4).** The natural
  witness for `d` is the **vertical composition of cylinders** — stack the homotopy `cyl_c : src →
  PathOb K` of `c` on top of `cyl_{c'}`. This requires *gluing two homotopies end-to-end*, i.e. a
  **path-object multiplication** `PathOb K ×_K PathOb K → PathOb K` (a co-/concatenation on the
  cocylinder). For a precubical set **no such multiplication exists**: precubical sets have **no
  degeneracies**, so there is no `K → PathOb K` (constant/identity homotopy) and no composition
  `PathOb ×_K PathOb → PathOb` (concatenate two intervals). This is the *same wall* that blocks
  roadmap STEP 4 (`Hom(K,K) ↪ cylinders` needs the missing degeneracy `K → PathOb K`) and the same
  flavour as the lowering refutation.

  Concretely (codebase check): the repo has `RefineConcat` (refinement-level list-append) and the
  geometric `⊗□¹ ⊣ PathOb` adjunction (`Foundations/Shift.lean`), but **no** `PathOb`
  concatenation/co-multiplication anywhere. The `RefineObj`-level append composes *chains*, not
  *homotopies*; it does not give a cylinder whose `cyl` is the concatenation.

* **`cylSubmonoid` (PROVEN conditional).** `cylSubmonoid` assembles the `Submonoid` *given* the two
  geometric inputs (a tautological cylinder and a composition operation). The algebra around the two
  hypotheses is complete; only the hypotheses are owed.

### Bottom line on "image = submonoid"

**CONJECTURED, currently OBSTRUCTED.** The unit lies in the image (modulo a routine tautological
cylinder). Closure under `·` is OPEN; the obstruction is **pinned and sharp**: it is exactly the
non-existence of a path-object multiplication `PathOb K ×_K PathOb K → PathOb K` realising vertical
composition of cylinders, which fails because precubical sets lack degeneracies. We expect closure
can **fail** in general (the product object map is a stacked endofunctor that need not be of the
single-cylinder form `Rgrpd∘Lgrpd⁻¹`), so the honest conjecture is:

> **Conjecture (image submonoid).** `cylImage K` is **not** a submonoid for general `K`: it
> contains `1` but is not closed under the monoid product `·`, the obstruction being the absence of
> cylinder vertical-composition (= a `PathOb` multiplication), which precubical degeneracy-freeness
> forbids. A submonoid is recovered only after passing to a model **with** degeneracies (e.g. the
> homotopy/Tier-2 quotient, or a cubical-with-connections enrichment).

This is consistent with, and sharpens, the program-wide finding that the *meaningful* structure lives
one level down, in the geometric `⊗□¹ ⊣ PathOb` adjunction, not in this codiscrete target.

---

## Summary table

| Item | Statement | Status |
|---|---|---|
| Monoid instance | `Monoid (PointedEndofunctor 𝒞)`, strict | **PROVEN** |
| Product object map | `objMap (A*B) x = B.F.obj (F₀ x)` | **PROVEN** (`rfl`) |
| Product path | `pathMap (A*B) x = η x ≫ B.pt.app (F₀ x)` | **PROVEN** |
| Product = `pointedOfPaths` of composite | `mul_pointedOfPaths` | **PROVEN** |
| `pointedOfPaths (of) (𝟙) = 1` | `taut_eq_one` | **PROVEN** |
| `1 ∈ cylImage K` | `one_mem_cylImage_of_taut` | **PROVEN modulo taut. cylinder** |
| Contractibility | `PointedEndofunctor 𝒢 ≌ Discrete PUnit` | **PROVEN** |
| Product object map (cylinder level) | `mul_cylToPointedObj_objMap` | **PROVEN** (`rfl`) |
| Closure reduction | `mul_mem_cylImage_of_compose` | **PROVEN** |
| Conditional submonoid | `cylSubmonoid` | **PROVEN (conditional)** |
| **`cylImage K` is a submonoid** | unit yes; closure | **OPEN / obstructed** (no `PathOb` multiplication) |
