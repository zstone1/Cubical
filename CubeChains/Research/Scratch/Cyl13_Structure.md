# Cyl13_Structure — special algebraic properties of the pointed-endofunctor monoid

Scratch findings for the cylinder ⟹ pointed-functor program (RESULT 2). Companion to
`Cyl13_Structure.lean` (decoupled from the green build; `lake build
CubeChains.Research.Scratch.Cyl13_Structure`, **sorry-free, green, no warnings**). Built on Cyl1
(`objDataEquiv`, `isWellPointed_iff`), Cyl5 (target thinness), Cyl6 (the `Monoid (PointedEndofunctor
𝒞)` instance, the product formula, `cylImage`) and Cyl8 (`mooreSubmonoid`).

We study `M := PointedEndofunctor (DPathGrpdR K)` under the Cyl6 monoid (composition `A * B = ⟨A.F ⋙
B.F, A.pt ≫ whiskerLeft A.F B.pt⟩`, `1 = ⟨𝟭, 𝟙⟩`) and its cylinder-induced submonoid `mooreSubmonoid
K = Submonoid.closure (cylImage K)`. **What special algebraic properties does it have?**

---

## HEADLINE — three sharp structural facts

1. **Units are detected by the underlying functor alone:** `A` is a unit of `M` **iff `A.F` is a
   strict isomorphism of categories** (invertible under `⋙` on the nose). On a groupoid base the
   point obstruction *vanishes* (every point is iso), so the unit data is "all in `A.F`". The group
   of units is the maximal subgroup `IsUnit.submonoid M` (mathlib `Group`). And `M` is **NOT a
   group** — any endofunctor with non-injective object map is a non-unit (concrete witness:
   `constObj`).

2. **Well-pointedness is FREE — Cyl1's flagged open question is settled YES.** *Every* pointed
   endofunctor of a groupoid (hence every `pointedOfPaths`, hence every cylinder-induced
   `cylToPointedObj`) is **well-pointed** (`F.map (η x) = pt.app (F₀ x)`, Kelly). It is automatic
   because the point is iso. So well-pointedness is **not** a discriminating invariant at this layer
   — the "one surviving non-degenerate invariant" Cyl1 hoped for collapses.

3. **Nontrivial idempotents EXIST** (besides `1`): the constant-object collapse `constObj x₀ η`
   (`η x₀ = 𝟙`) is idempotent yet `≠ 1` — an idempotent-monad-like retraction of the groupoid onto a
   point. But **every idempotent UNIT is `1`** (mathlib): the nontrivial idempotents are exactly the
   non-units.

The unifying mechanism behind all three: **`pt_app_F_obj`** — in a groupoid the point `A.pt` is iso,
so its naturality at the morphism `A.pt.app X` forces `A.pt.app (A.F.obj X) = A.F.map (A.pt.app X)`.
This single lemma gives well-pointedness for free (2), and underlies the inverse-point construction
for units (1).

---

## Task 1 — Units / maximal subgroup

### The characterisation (PROVEN, both directions)

`M` is a **strict** monoid (Cyl6): `(A * B).F = A.F ⋙ B.F` and `1.F = 𝟭` *on the nose*. Hence:

| Statement | Lean name | Status |
|---|---|---|
| Unit ⟹ `A.F` strict-iso (both `A.F ⋙ B.F = 𝟭` and `B.F ⋙ A.F = 𝟭`) | `strictInv_F_of_unit` | **PROVEN** |
| Unit ⟹ `A.F` `IsUnit` in the functor-composition monoid | `isUnit_F_of_isUnit` | **PROVEN** |
| **Strict-iso `A.F` ⟹ unit** (groupoid base) | `isUnit_of_strictInv` | **PROVEN** |

So on a groupoid base: **`A` is a unit of `M` ⟺ `A.F` is a strict isomorphism of categories.**

The hard direction (`isUnit_of_strictInv`) constructs the inverse explicitly: given a strict inverse
functor `G` (`A.F ⋙ G = 𝟭`, `G ⋙ A.F = 𝟭`), the inverse pointed endofunctor is `B = ⟨G, invPoint A G
hAG⟩` where `invPoint.app X = eqToHom .. ≫ G.map (inv (A.pt.app X))` transports the point's inverse.
The proof's spine:
* `isUnit_keyAB_app`: the component cancellation `A.pt.app X ≫ invPoint.app (A.F.obj X) =
  eqToHom (..)`, via `pt_app_F_obj` (rewriting `inv (A.pt.app (A.F X)) = A.F.map (inv (A.pt.app X))`)
  then collapsing `G.map (A.F.map ·)` by `Functor.congr_hom hAG`;
* `mul_invPointObj_eq_one`: packages `A * B = 1` from that, via `eq_one_of_F_pt` (a `PointedEndofunctor
  P = 1` recogniser: `P.F = 𝟭` plus `P.pt ≫ eqToHom = 𝟙`);
* the *other* product `B * A = 1` is obtained NOT by a second hand-computation but by the **monoid
  identity** `left_inv_eq_right_inv`: `A * B = 1` makes `A` a left inverse of `B`, and applying
  `mul_invPointObj_eq_one` to `B` (whose `B.F = G` strictly inverts `A.F` via `hGA`) gives `B` a
  right inverse `B'`; left-inverse = right-inverse ⟹ `A = B'` ⟹ `B * A = 1`.

### The "loop cylinder" reading

For the cylinder target `M = PointedEndofunctor (DPathGrpdR K)` (a *free groupoid* base), via Cyl1's
`objDataEquiv`, units correspond to object-data `(F₀, η)` whose `F₀ = A.F.obj` is a **bijection on
objects induced by a strict auto-equivalence** of `DPathGrpdR K`. These are the conjectured "loop
cylinders": `F₀ = id`-on-objects (up to the strict iso), `η` a self-homotopy. They form the maximal
subgroup. The tentative task conjecture "`F₀` bijective ⟹ unit" is *necessary* (`objMap_injective_of_isUnit`)
but the sharp sufficient condition is `A.F` a **strict iso of categories**, which is stronger than
mere object-bijectivity (a functor can be bijective on objects without being invertible).

### The maximal subgroup, and NOT a group

| Statement | Lean name | Status |
|---|---|---|
| The group of units `IsUnit.submonoid M` (mathlib `Group`) | `unitsSubgroup` | **PROVEN (def)** |
| `1` is a unit | `one_isUnit` | **PROVEN** |
| Unit ⟹ object map injective | `objMap_injective_of_isUnit` | **PROVEN** |
| Non-injective object map ⟹ NOT a unit | `not_isUnit_of_objMap_not_injective` | **PROVEN** |
| `constObj x₀ η` (constant object map) is NOT a unit | `constObj_not_isUnit` | **PROVEN** |

So `M` is a genuine **monoid, not a group**: the constant-object endofunctor `constObj` (object map
`_ ↦ of x₀`) is non-injective on objects, hence not a unit. (It needs two generators with distinct
free-groupoid images — true whenever `C` has ≥ 2 non-isomorphic objects.)

---

## Task 2 — Idempotents

| Statement | Lean name | Status |
|---|---|---|
| Idempotent ⟹ `A.F ⋙ A.F = A.F` | `comp_F_self_of_idempotent` | **PROVEN** |
| **Every idempotent UNIT is `1`** (mathlib `iff_eq_one_of_isUnit`) | `idempotent_unit_eq_one` | **PROVEN** |
| `constObj x₀ η` is idempotent when `η x₀ = 𝟙` | `constObj_isIdempotent` | **PROVEN** |
| **There IS a nontrivial idempotent `≠ 1`** | `exists_nontrivial_idempotent` | **PROVEN** |

**Verdict: nontrivial idempotents exist.** The constant-object endofunctor `constObj x₀ η` with `η
x₀ = 𝟙` satisfies `A * A = A` (its object map `_ ↦ of x₀` absorbs composition, and the product path
`η x ≫ pt.app (of x₀) = η x ≫ η x₀ = η x` once `η x₀ = 𝟙`), yet `A ≠ 1` (its `F` is the constant
functor at `of x₀`, not `𝟭`). This is an "idempotent-monad-like" collapse of the d-path groupoid
onto a point. `constObj_isIdempotent` is proved via Cyl1's `objDataEquiv` converse: the product's
object-data is `(F₀, η)` on the nose, so `A * A = objDataEquiv ⟨F₀, η⟩ = A`.

The caveat (geometric honesty): `constObj` needs a path `η x : of x ⟶ of x₀` for *every* generator
`x` — i.e. `x₀` reachable from all of `C` (connectivity). On a groupoid the point `A.pt.app (of x)`
is an iso `of x ≅ of x₀`, so the collapse is "up to iso the identity", but the *underlying
endofunctor* is strictly constant. So `exists_nontrivial_idempotent` is stated taking the connecting
path family `η` (with `η x₀ = 𝟙`) and a distinguished `x₁` with `of x₁ ≠ of x₀` as hypotheses — the
honest minimal data for the witness.

Combined with `idempotent_unit_eq_one`: **the only idempotent in the group of units is `1`; all
nontrivial idempotents are non-units** (collapses).

---

## Task 3 — Well-pointedness (Cyl1's open question, SETTLED)

| Statement | Lean name | Status |
|---|---|---|
| `pt_app_F_obj`: `A.pt.app (A.F.obj X) = A.F.map (A.pt.app X)` (groupoid) | `pt_app_F_obj` | **PROVEN** |
| **Every pointed endofunctor of a groupoid is well-pointed** | `isWellPointed_of_groupoid` | **PROVEN** |
| **The cylinder's `(Rgrpd∘Lgrpd⁻¹, counit≫sweepR)` IS well-pointed** | `pointedOfPaths_isWellPointed` | **PROVEN** |

**Verdict: YES, well-pointed — and trivially so.** Cyl1 isolated `isWellPointed_iff`:
`pointedOfPaths F₀ η` is well-pointed (Kelly, `F ◫ pt = pt ◫ F`) iff `∀ x, F.map (η x) = pt.app (F₀
x)`, and flagged the cylinder data as "the one surviving non-degenerate invariant — settle whether
cylinder-induced elements are well-pointed."

They are. `pt_app_F_obj` (naturality of the iso point `A.pt` at the morphism `A.pt.app X`) gives,
at a generator `X = of x`, exactly `pt.app (F₀ x) = F.map (η x)` — the Kelly equation. This holds for
**every** `pointedOfPaths`, hence for `cylToPointedObj c`. So well-pointedness is **automatic** in a
groupoid base and is **not** a discriminating invariant: the hoped-for "first genuinely
non-degenerate invariant" collapses with the rest. (This is consistent with the program finding that
the meaningful homotopical content lives one level down, in the geometric `⊗□¹ ⊣ PathOb`.)

Relation to "every well-pointed endofunctor generates a monad" (Kelly): since the point is iso,
`F ≅ 𝟭`, so the generated monad is the identity monad up to iso — degenerate, matching Cyl1.

---

## Task 4 — Commutativity and generation

| Statement | Lean name | Status |
|---|---|---|
| The monoid is **non-commutative** (`A * B ≠ B * A` witness) | `not_commutative_witness` | **PROVEN** |
| `mooreSubmonoid K` generated by ELEMENTARY (length-1) cylinders | `mooreSubmonoid_generated_by_elementary` | **PROVEN** |
| product = concatenation of elementary generators | `moore_product_is_concatenation` | **PROVEN** |

**Non-commutative.** The product object map STACKS (`Cyl6.mul_objMap`: `objMap (A*B) x = B.F.obj
(A.F.obj (of x))`), so `A * B` and `B * A` generally differ. `not_commutative_witness`: for two
constant collapses `constObj x₀ η`, `constObj x₁ θ` with `of x₀ ≠ of x₁`, `(constObj x₀ * constObj
x₁).objMap` is constant `of x₁` while `(constObj x₁ * constObj x₀).objMap` is constant `of x₀`, so
they differ. Hence `M` (and the cylinder submonoid, which contains such collapses when realisable) is
genuinely non-commutative.

**Generation.** `mooreSubmonoid K = Submonoid.closure (cylImage K)` (re-export of
`Cyl8.mooreSubmonoid_eq_closure`): the Moore submonoid is generated by the strict `□¹` (elementary,
length-1) cylinder image, and the monoid product is realised by **list concatenation** of those
elementary cylinders (`Cyl8.mooreToPointed_concat`). So every element of the cylinder-induced
submonoid is a product of single-block cylinders — connecting to Cyl4/Cyl8's generation findings: the
strict image is not itself `·`-closed (no fold `□¹ → I₂`, Cyl7/Cyl8), but its **closure** = the Moore
submonoid is exactly the elementary-generated submonoid.

---

## Status summary

| Item | Lean name | Status |
|---|---|---|
| Unit ⟹ `A.F` strict iso | `strictInv_F_of_unit`, `isUnit_F_of_isUnit` | **PROVEN** |
| Strict-iso `A.F` ⟹ unit (groupoid) | `isUnit_of_strictInv` | **PROVEN** |
| Group of units = `IsUnit.submonoid` | `unitsSubgroup`, `one_isUnit` | **PROVEN** |
| `M` is not a group (non-unit witness) | `constObj_not_isUnit` | **PROVEN** |
| Idempotent ⟹ `A.F ⋙ A.F = A.F` | `comp_F_self_of_idempotent` | **PROVEN** |
| Every idempotent unit is `1` | `idempotent_unit_eq_one` | **PROVEN** |
| Nontrivial idempotent exists | `exists_nontrivial_idempotent` | **PROVEN** |
| Every groupoid pointed endofunctor is well-pointed | `isWellPointed_of_groupoid` | **PROVEN** |
| Cylinder `(F₀,η)` well-pointed | `pointedOfPaths_isWellPointed` | **PROVEN** |
| Monoid non-commutative | `not_commutative_witness` | **PROVEN** |
| Moore submonoid generated by elementary cylinders | `mooreSubmonoid_generated_by_elementary` | **PROVEN** |

**The single most interesting structural property:** the monoid is *rigid in a surprising way* —
**well-pointedness is free** (every element is well-pointed, settling Cyl1's open question with a NO
for "discriminating invariant"), yet the monoid is **far from a group**: its units are exactly the
strict-iso endofunctors, it has genuine nontrivial idempotents (point-collapses), and it is
non-commutative. So the "interesting" structure is entirely in the *non-invertible* part — the
units/group-of-units is the rigid skeleton, and all the homotopical content that the cylinder
construction could carry has, at this groupoid-pointed-endofunctor layer, collapsed to the
automatic Kelly coherence. The discriminating invariants must be sought one level down (the
geometric `⊗□¹ ⊣ PathOb`), exactly as the broader program concluded.

**Off-the-shelf mathlib reused:** `IsUnit`, `Units`, `IsUnit.submonoid` (the `Group` of units),
`left_inv_eq_right_inv`, `IsIdempotentElem` + `IsIdempotentElem.iff_eq_one_of_isUnit`,
`Submonoid.closure`, `eqToHom`/`NatIso.isIso_inv_app`/`Functor.congr_hom` for the transport algebra.
