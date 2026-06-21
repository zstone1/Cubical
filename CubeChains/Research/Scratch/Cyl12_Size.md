# Cyl12_Size — how big is the cylinder monoid `mooreSubmonoid K`?

Scratch findings for the cylinder ⟹ pointed-functor program (RESULT 2). Companion to
`Cyl12_Size.lean` (decoupled from the green build; `lake build
CubeChains.Research.Scratch.Cyl12_Size`, **sorry-free and green, no warnings**; every named result
below depends only on `[propext, Classical.choice, Quot.sound]`). Built on top of Cyl1
(`objDataEquiv`), Cyl2 (`OfClosure`), Cyl3 (`tautF₀`/`tautη`, discreteness facts), Cyl6 (the
`Monoid` instance, `cylImage`), Cyl8 (`mooreSubmonoid`, `mooreToPointed`). No existing construction
was modified.

`M := PointedEndofunctor (DPathGrpdR K)`, the monoid under composition
(`A * B = ⟨A.F ⋙ B.F, …⟩`, unit `⟨𝟭, 𝟙⟩`). `DPathGrpdR K = FreeGroupoid (RefineObj K.init
K.final)`. `mooreSubmonoid K = Submonoid.closure (cylImage K)` (Cyl8).

---

## HEADLINE — is it the whole monoid?

> **NO in general, but the reason is subtle, and the gap is NOT where the brief expected.**
>
> * Over a **discrete** base (`fourPaths`) the *entire* monoid `M` is trivial (`= {1}`), so there
>   `mooreSubmonoid K = M = ⊤` and there is **no gap at all** (PROVEN,
>   `subsingleton_pointed_of_discrete`). The suggested "use `fourPaths`' `firstIncoherence`
>   π₀-permutation as the out-of-image witness" route is **degenerate**: such a permutation is **not
>   an element of `M`**, because every pointed endofunctor fixes π₀ (the π₀ upper bound below).
> * Over a base with a **non-identity loop** (e.g. `□²`'s staircase swap) `M` is genuinely
>   **nontrivial** / infinite (PROVEN, `nontrivial_pointed_of_loop`) — the only regime where a gap
>   can exist.
> * `mooreSubmonoid K ≠ ⊤` is PROVEN **conditionally** (`mooreSubmonoid_ne_top_of_isEmpty`): from
>   `Nontrivial M` together with `IsEmpty (CylMapWeqR K)`. An **unconditional** `≠ ⊤` is **OPEN** —
>   see the honest boundary below.

The sharpest quantitative statement: **π₀ measures *no* gap.**
`π0Action '' mooreSubmonoid K = {1} = π0Action '' M` (both fix π₀). The size difference between
`mooreSubmonoid K` and `M` lives entirely **one level down**, in the per-component *fiber/loop*
data — exactly the level the broader program already flags as the meaningful one.

---

## Task 1 — the π₀ constraint (the upper bound). PROVEN

Let `π₀ = Pi0 𝒢 := Quiver.WeaklyConnectedComponent 𝒢` (the underlying quiver's zigzag quotient; for
a groupoid this is the usual set of connected components / homotopy classes of objects).

| Lemma | Statement | Status |
|---|---|---|
| `wcc_eq_of_hom` | a morphism `f : x ⟶ y` forces `[x] = [y]` in `π₀` (length-1 zigzag in `Symmetrify`) | **PROVEN** |
| `pi0Map` | the object-map of an endofunctor descends to `π₀ → π₀` (`Quotient.lift`) | **PROVEN (def)** |
| `pi0Map_id` / `pi0Map_comp` | `pi0Map 𝟭 = id`, `pi0Map (F⋙G) = pi0Map G ∘ pi0Map F` | **PROVEN** |
| **`pi0Map_pointed_eq_id`** | **the π₀-object-map of ANY pointed endofunctor is the identity** | **PROVEN** |
| `π0End` | `pi0Map A.F` as an element of `Function.End π₀` | **PROVEN (def)** |
| `π0End_eq_one` | `π0End A = 1` (= `id`) | **PROVEN** |
| **`π0Action`** | the monoid hom `M →* (Function.End π₀)ᵐᵒᵖ`, `A ↦ op (π0End A)` | **PROVEN** |
| **`π0Action_eq_one`** | `π0Action A = 1` for every `A` | **PROVEN** |
| `π0Action_range_eq` | `Set.range π0Action = {1}` | **PROVEN** |

**The upper bound, in one line.** A point `pt.app x : x ⟶ F.obj x` is a *morphism*, so `x` and
`F.obj x` lie in the same component; hence the descended object-map is **literally the identity** on
π₀. This is *stronger* than "preserves π₀-components": a pointed endofunctor of a groupoid can never
even *permute* π₀ — it fixes every component pointwise. Restricting along
`cylImage K ⊆ mooreSubmonoid K ⊆ M` gives the constraint for all three (the hom `π0Action` is the
clean carrier).

**The monoidal bookkeeping.** Because the monoid product composes `A.F` *then* `B.F`
(`(A*B).F = A.F ⋙ B.F`), `π0End` is an *anti*-homomorphism, so `π0Action` lands in the **opposite**
monoid `(Function.End π₀)ᵐᵒᵖ` (this is the honest way to make `map_mul'` typecheck;
`Function.End` multiplies by `∘`). Since every value is `1`, the image is the trivial submonoid
regardless.

> **Consequence for the brief's Task 3 route.** The image of `π0Action` is `{1}`, not
> `⟨Aut K's π₀-action⟩`. The brief conjectured `π0Action '' mooreSubmonoid = ⟨Aut K⟩ ⊊ End π₀`; that
> is **false** — the image is `{1}`, because a π₀-*permuting* map carries no point and so is not an
> element of `M` at all. So π₀ cannot be the separating invariant. This is the key correction.

---

## Task 2 — is `OfClosure` a real constraint? VERDICT: **VACUOUS**. PROVEN

Cyl2 proved every induced point factors `η x = counit.inv ≫ w` with `w ∈ Cyl2.OfClosure` (the wide
inductive "zigzag of genuine refinements, no formal inverse beyond inverting actual arrows"), and
asked whether `OfClosure` is a genuine cut or vacuous.

| Lemma | Statement | Status |
|---|---|---|
| `OfClosureGrpd` (+ `Category`, `Groupoid` instances) | the wide subgroupoid of `OfClosure`-morphisms | **PROVEN** |
| `ι`, `fromC`, `fromC_comp_ι` | inclusion `OfClosureGrpd C ⥤ FreeGroupoid C`; `C` factors through it (`of.map ∈ OfClosure`) | **PROVEN** |
| `liftFromC_comp_ι` | `lift fromC ⋙ ι = 𝟭` (section, via `lift_unique`) | **PROVEN** |
| **`ofClosure_univ`** | **`OfClosure f` for EVERY morphism `f` of a free groupoid** | **PROVEN** |
| `ofClosure_eq_univ` | set form: `{f | OfClosure f} = univ` | **PROVEN** |

**Verdict.** `OfClosure` holds for *every* morphism. Proof idea: the `OfClosure`-morphisms form a
wide subgroupoid `OfClosureGrpd C` (identities, comp, inv all preserved); its inclusion `ι` has a
section `lift fromC ⋙ ι = 𝟭` because `of` factors through it (`OfClosure.of_map`). Hence every `f`
is `ι.map ((lift fromC).map f)` (up to `eqToHom` corrections, themselves in `OfClosure`), so
`OfClosure f`. **So `OfClosure` is NOT a constraint on `η`.**

**Therefore the real constraint on `cylImage`** is neither `η ∈ OfClosure` (vacuous) nor the π₀
object-map (vacuous — always `id`), but the `(F₀, η)` **correlation**: *which pairs* of a
functorial object-map `F₀` and a path family `η` actually arise from cylinder geometry. The only
formalised hard constraint on a *single* point is Cyl2's "the lone formal inverse is the equivalence
counit" — and that constrains the *shape* (`counit.inv ≫ (anything)`), not the value `w`.

---

## Task 3 — properness witness (the headline). PROVEN as far as honest

### 3a. Discrete base ⟹ `M` trivial (refutes the `fourPaths` route). PROVEN

| Def / theorem | Statement | Status |
|---|---|---|
| `IsDiscreteGrpd 𝒢` | hypotheses "hom-sets subsingleton" + "a hom forces equal endpoints" | def |
| **`subsingleton_pointed_of_discrete`** | over a discrete base, `Subsingleton (PointedEndofunctor 𝒢)` (i.e. `M = {1}`) | **PROVEN** |

Over a discrete groupoid (which `DPathGrpdR fourPaths` is — Cyl3 `native_decide`: `Ch(fourPaths)`
is the discrete 4-object category), the point `pt.app x : x ⟶ F x` forces `F.obj x = x`, and
thinness forces `F.map`/`pt` to be identities, so every pointed endofunctor *equals* the unit
`⟨𝟭, 𝟙⟩`. **`M` vanishes.** Hence `mooreSubmonoid (fourPaths) = M = ⊤ = {1}`: **no gap there.**
This formally refutes the suggested route (build the `firstIncoherence` π₀-permutation in `M`): that
object is not in `M`, and `M` itself is trivial.

### 3b. A non-identity loop ⟹ `M` nontrivial. PROVEN

| Theorem | Statement | Status |
|---|---|---|
| **`nontrivial_pointed_of_loop`** | a non-identity loop `g : of x ⟶ of x`, `g ≠ 𝟙` ⟹ `Nontrivial M` | **PROVEN** |

Given a non-identity loop in the free groupoid (e.g. `□²`'s staircase-swap loop, Cyl3
`native_decide`), the object-data `(of, 𝟙)` (which is the unit `1`) and `(of, g-at-x)` are distinct,
so by `Cyl1.objData_injective` they are distinct pointed endofunctors. So `M` is nontrivial — in
fact infinite, a free group's worth of loops per component. **This is the only regime where a gap
between `mooreSubmonoid` and `M` can exist.**

### 3c. The conditional `mooreSubmonoid K ≠ ⊤`. PROVEN (conditional); unconditional OPEN

| Theorem | Statement | Status |
|---|---|---|
| `mooreSubmonoid_eq_bot_of_isEmpty` | `IsEmpty (CylMapWeqR K) ⟹ mooreSubmonoid K = ⊥` (only the empty list survives ⟹ `{1}`) | **PROVEN** |
| **`mooreSubmonoid_ne_top_of_isEmpty`** | `Nontrivial M` ∧ `IsEmpty (CylMapWeqR K) ⟹ mooreSubmonoid K ≠ ⊤` | **PROVEN** |

Note `1 ∈ mooreSubmonoid K` *always* (empty Moore list), so an empty `CylMapWeqR` does **not** make
`mooreSubmonoid` empty — it makes it exactly `⊥ = {1}`. Combined with `Nontrivial M` (3b) that is a
genuine `≠ ⊤`.

> **The honest boundary (why no unconditional `≠ ⊤`).** Every invariant *formalised* in this program
> is satisfied by ALL of `M`:
> * the π₀-action is trivial for every pointed endofunctor (§1);
> * `OfClosure` membership is vacuous (§2);
> * over a connected base the whole *category* `PointedEndofunctor` is codiscrete (Cyl2/Cyl3), so no
>   **iso-invariant** can separate `mooreSubmonoid` from `M` either.
>
> So a genuine unconditional separator must be the **literal** `(F₀, η)` correlation: which
> object-map/path pairs are realised by *products of cylinder-induced* data. That object-map
> `F₀ = Rgrpd ∘ Lgrpd⁻¹` is noncomputable cylinder geometry, and Cyl6 (`mul_cylToPointedObj_objMap`)
> shows products *stack* with no closed form — it is **not characterised in Lean**. Hence the
> unconditional `≠ ⊤` is **OPEN** (and `IsEmpty (CylMapWeqR K)` is itself nontrivial to establish:
> the source cylinder is existentially quantified).

---

## Task 4 — characterise the image size. PROVEN

| Theorem | Statement | Status |
|---|---|---|
| `π0Action_mooreSubmonoid_eq_one` | every `A ∈ mooreSubmonoid K` has `π0Action A = 1` | **PROVEN** |
| **`π0Action_image_moore_eq_image_top`** | `π0Action '' mooreSubmonoid K = {1} = Set.range π0Action` | **PROVEN** |

**Sharpest size statement.** The π₀-image of `mooreSubmonoid K` equals that of the *whole* monoid
`M`: both are the trivial submonoid `{1}`. So:

* **π₀ measures no gap** — there are no π₀-permutations for cylinders to miss.
* `mooreSubmonoid K = M` (the whole monoid) **iff** `M` is trivial, i.e. iff the base groupoid is
  discrete (3a); then both are `{1}`.
* When `M` is nontrivial (a loop exists, 3b), the gap — if any — is **purely fiber/loop data**, the
  conjecturally-proper part (3c).

This sharpens the program-wide finding: the cylinder construction's content at this layer is a
**π₀-invariant that is identically trivial**, and the meaningful structure (the loops it can/can't
realise) sits in the fiber, which this codiscrete target cannot record — consistent with Cyl3's
"the meaningful adjunction is the geometric `⊗□¹ ⊣ PathOb`, not this codiscrete target".

---

## Status summary

| Item | Lean name | Status |
|---|---|---|
| π₀ morphism ⟹ same component | `wcc_eq_of_hom` | **PROVEN** |
| π₀-object-map of a pointed endofunctor = `id` | `pi0Map_pointed_eq_id` | **PROVEN** |
| π₀-action monoid hom | `π0Action` | **PROVEN** |
| π₀-action is trivial (upper bound) | `π0Action_eq_one`, `π0Action_range_eq` | **PROVEN** |
| `OfClosure` is vacuous | `ofClosure_univ`, `ofClosure_eq_univ` | **PROVEN** |
| discrete base ⟹ `M` trivial | `subsingleton_pointed_of_discrete` | **PROVEN** |
| loop ⟹ `M` nontrivial | `nontrivial_pointed_of_loop` | **PROVEN** |
| empty cylinders ⟹ `mooreSubmonoid = ⊥` | `mooreSubmonoid_eq_bot_of_isEmpty` | **PROVEN** |
| conditional `mooreSubmonoid ≠ ⊤` | `mooreSubmonoid_ne_top_of_isEmpty` | **PROVEN (conditional)** |
| π₀-image of moore = π₀-image of `M` = `{1}` | `π0Action_image_moore_eq_image_top` | **PROVEN** |
| **unconditional `mooreSubmonoid K ≠ ⊤`** | — | **OPEN** (separator = `(F₀,η)` correlation, noncomputable) |

## One-paragraph answer to "how big?"

`mooreSubmonoid K` is **not** detectably smaller than `M` by any *formalised* invariant: both fix
π₀ (the only computable invariant of this codiscrete target) trivially, so `π0Action`'s image is
`{1}` for both. The monoid `M` itself is `{1}` over a discrete base (and there `mooreSubmonoid = M =
⊤`) and infinite over a base with a loop; in the latter regime `mooreSubmonoid K ≠ ⊤` is provable
under `IsEmpty (CylMapWeqR K)` and conjecturally proper otherwise, with the only possible separator
being the literal `(F₀, η)` correlation — geometry the present formalisation does not pin down.
