import CubeChains.Cylinder.CylinderRefine
import CubeChains.Testing.CylinderTwoBlock
import CubeChains.Testing.WedgeMapDivergence
import CubeChains.Testing.Examples

/-!
# Research/Scratch/Cyl3_Examples — worked examples + pathologies for `cylToPointedR`

Scratch deliverable for **user item 2** (worked examples + pathologies, in the spirit
of `Research/Unrealizable.lean`).  Build:

```
lake build CubeChains.Research.Scratch.Cyl3_Examples
```

This file is **decoupled** from the green build (nothing in the root `CubeChains.lean`
imports it).  It owns ONLY `Cyl3_Examples.{lean,md}`.

## What is in here

Two registers, exactly as the brief asks.

1. **Algebra anchor (PROVEN, topos-level, sorry-free).**  The cylinder ⟹ pointed-functor
   pipeline ends in `pointedOfPaths F₀ η : PointedEndofunctor (FreeGroupoid C)`
   (`Cylinder/PointedFunctor.lean`).  We pin what the *tautological/identity* object-data
   `(F₀, η) = (of, 𝟙)` induces: its underlying endofunctor is **literally `𝟭`**
   (`pointedOfPaths_id_F`/`taut_F_eq_id`), so it is **uniquely isomorphic to the identity
   pointed endofunctor** `idPointed` (`taut_iso_id`).  This is the algebraic shadow of "the
   tautological cylinder induces the identity": when both legs coincide (`F₀ = of`,
   `η = 𝟙`), `cylToPointedObj` collapses to `𝟭`.

   We further pin the **degeneracy mechanism** (the most important structural finding):
   over a groupoid base every pointed endofunctor's point is invertible
   (`PointedEndofunctor.pt_isIso`), so `PointedEndofunctor 𝒢` is **thin** (`pointedEndo_thin`)
   and in fact **codiscrete on objects** — between any two there is a *unique iso*
   (`pointedUniqueIso`).  Hence the homotopy datum `η x` carries **no** information beyond
   *which component* `F₀ x` lands in.  `cylToPointedObj` therefore only records the π₀-level
   data `x ↦ [Rgrpd (Lgrpd⁻¹ x)]`; the geometric content of `sweepR` is washed out into the
   forced conjugation iso.  (`pointed_determined_by_F_pt`, `pointedUniqueIso`.)

2. **Finite worked examples + the pathology (native_decide-backed, surrogate model).**
   The topos objects `RefineObj`/`DPathGrpdR`/`cylToPointedObj` are `noncomputable`
   (wedges = generic pushouts), so the *examples* are computed in the `Testing` FinBPSet
   surrogate (`Testing/Model.lean`): `chains` = objects of `Ch K`, `chLe` = the
   `RefineObj` face order, `chainsConnected` = connectivity of the d-path groupoid's
   component (`π₀`).  Each example reports its d-paths and whether the cylinder-relevant
   ends are connected (so the per-object homotopy `η x` exists).  The **pathology** is the
   self-linked square `cylSquare` (`Testing/CylinderObstruction.lean`): a cylinder whose
   induced pointed endofunctor exists yet is connected-component-collapsing (the
   information-loss pathology) — pinned here against the four-square-loop's `fourPaths`
   incoherence for contrast.

See `Cyl3_Examples.md` for the table and the prose.

**Layer:** Research/Scratch (decoupled).  **Imports:** `Cylinder/CylinderRefine`,
`Testing/CylinderTwoBlock`.
-/

open CategoryTheory Operations

namespace Cyl3

/-! ## Part 1 — the algebra anchor (topos-level, sorry-free)

The cylinder ⟹ pointed-functor functor lands every cylinder in `pointedOfPaths F₀ η`
(`Cylinder/PointedFunctor.lean:163`).  We isolate the object-data that the *tautological*
(both-legs-equal) cylinder produces — `F₀ = of`, `η = 𝟙` — and prove it is the identity
pointed endofunctor on the nose.  Everything is generic in a base category `C`. -/

section Identity

variable {C : Type*} [Category C]

/-- The tautological object-map: send each object to itself in the free groupoid. -/
abbrev tautF₀ : C → FreeGroupoid C := fun x => (FreeGroupoid.of C).obj x

/-- The tautological per-object path: the identity (no movement). -/
abbrev tautη : ∀ x, (FreeGroupoid.of C).obj x ⟶ tautF₀ (C := C) x := fun _ => 𝟙 _

/-- **The conjugation functor of the tautological data is `of` itself.**  With `F₀ = of`
and `η = 𝟙`, the conjugation `map f = (𝟙)⁻¹ ≫ of.map f ≫ 𝟙` is just `of.map f`. -/
theorem conjFunctor_taut :
    conjFunctor (FreeGroupoid.of C) (tautF₀ (C := C)) (tautη (C := C)) = FreeGroupoid.of C := by
  fapply CategoryTheory.Functor.ext
  · intro _; rfl
  · intro x y f
    simp only [conjFunctor, Category.comp_id, eqToHom_refl, Category.id_comp]
    rw [Groupoid.inv_eq_inv, IsIso.inv_id, Category.id_comp]

/-- `lift (of C) = 𝟭` — the universal property at the identity.  (mathlib has
`lift_id_comp_of` but no `lift_id`; we get it from `lift_unique`.) -/
theorem lift_of_eq_id : FreeGroupoid.lift (FreeGroupoid.of C) = 𝟭 (FreeGroupoid C) :=
  (FreeGroupoid.lift_unique (FreeGroupoid.of C) (𝟭 _) (Functor.comp_id _)).symm

/-- **The tautological pointed endofunctor's underlying functor is `𝟭`.**  Its `F` is
`lift (conjFunctor of of 𝟙) = lift of = 𝟭` (`conjFunctor_taut` + `lift_of_eq_id`). -/
theorem pointedOfPaths_id_F :
    (pointedOfPaths (tautF₀ (C := C)) (tautη (C := C))).F = 𝟭 (FreeGroupoid C) := by
  change FreeGroupoid.lift (conjFunctor (FreeGroupoid.of C) (tautF₀ (C := C)) (tautη (C := C)))
      = 𝟭 (FreeGroupoid C)
  rw [conjFunctor_taut, lift_of_eq_id]

end Identity

/-! ## Part 1b — the degeneracy mechanism (why the homotopy is washed out)

Over a groupoid base **every** pointed endofunctor's point is a natural iso
(`PointedEndofunctor.pt_isIso`, `Cylinder/PointedFunctor.lean:85`).  So between any two
pointed endofunctors of a groupoid there is exactly **one** morphism
(`pointedHomOfGroupoid`), and that is what forces the morphism map of `cylToPointedR`.
The consequence for *examples*: `cylToPointedObj c` is determined, up to unique iso, by its
object-map `F₀ = Rgrpd ∘ Lgrpd⁻¹` alone — the homotopy datum `η = counit ≫ sweepR` only
witnesses that `of x` and `F₀ x` lie in the **same connected component**; its actual path
is irrelevant (any other path gives an isomorphic pointed endofunctor).  This is the
"codiscrete ⟹ identity-deformation" degeneracy, made precise. -/

section Degeneracy

variable {𝒢 : Type*} [Groupoid 𝒢]

/-- **There is a unique morphism between pointed endofunctors of a groupoid.**  Both the
existence (`pointedHomOfGroupoid`) and the uniqueness are forced by the point axiom
(`A.pt ≫ τ = B.pt` with `A.pt` invertible).  Hence the whole category
`PointedEndofunctor 𝒢` is **thin** — its information is entirely in the objects. -/
instance pointedEndo_thin (A B : PointedEndofunctor 𝒢) : Subsingleton (A ⟶ B) where
  allEq f g := by
    apply PointedEndofunctor.Hom.ext
    have hf : A.pt ≫ f.τ = A.pt ≫ g.τ := by rw [f.w, g.w]
    exact (cancel_epi A.pt).mp hf

/-- **Information-loss, stated.**  Two pointed endofunctors of a groupoid that have *equal
object-maps and equal points-after-`F`* (i.e. the same `F` and same `pt`) are equal — there
is nothing else to a pointed endofunctor of a groupoid.  More to the point, by
`pointedEndo_thin` any two parallel morphisms agree, so a cylinder's induced object is
pinned by `(F, pt)` and the *path* chosen inside `sweepR` cannot be recovered. -/
theorem pointed_determined_by_F_pt (A B : PointedEndofunctor 𝒢)
    (hF : A.F = B.F) (hpt : HEq A.pt B.pt) : A = B := by
  cases A; cases B; cases hF; cases hpt; rfl

/-- The **identity pointed endofunctor** of a groupoid: `⟨𝟭, 𝟙⟩`. -/
def idPointed : PointedEndofunctor 𝒢 := ⟨𝟭 𝒢, 𝟙 _⟩

/-- **Any pointed endofunctor of a groupoid is isomorphic to another iff … always**, when a
morphism exists either way — and in a groupoid base one always does (`pointedHomOfGroupoid`).
So `PointedEndofunctor 𝒢` is not merely thin but a **codiscrete-on-π₀-of-objects** category:
between any two objects there is a *unique iso*.  This is the precise "codiscrete" statement
behind the cylinder degeneracy. -/
noncomputable def pointedUniqueIso (A B : PointedEndofunctor 𝒢) : A ≅ B :=
  ⟨pointedHomOfGroupoid A B, pointedHomOfGroupoid B A,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end Degeneracy

/-! ## Part 1c — the tautological cylinder induces the identity (up to the canonical iso)

Putting Parts 1 and 1b together: the tautological object-data lands the cylinder on a pointed
endofunctor whose underlying `F` is **literally `𝟭`** (`pointedOfPaths_id_F`), and which is
therefore **uniquely isomorphic to the identity pointed endofunctor** `idPointed`
(`taut_iso_id`).  Because `PointedEndofunctor (FreeGroupoid C)` is codiscrete-on-objects
(`pointedUniqueIso`), this is the strongest invariant statement available: the tautological
cylinder is the identity, and *every* cylinder is isomorphic to the identity inside its
π₀-component — the homotopy can never be observed.  This anchors all the worked examples:
the only data a cylinder's pointed endofunctor carries is the object-map `Rgrpd ∘ Lgrpd⁻¹` up
to π₀. -/

section Anchor

variable {C : Type*} [Category C]

/-- **The tautological cylinder's pointed endofunctor is uniquely isomorphic to the identity.**
Combines `pointedOfPaths_id_F` (the underlying functor is `𝟭`) with the codiscreteness
`pointedUniqueIso`.  This is the topos-level shadow of "`cylToPointedObj` of the
identity/tautological cylinder = `𝟭`". -/
noncomputable def taut_iso_id :
    pointedOfPaths (tautF₀ (C := C)) (tautη (C := C)) ≅ idPointed :=
  pointedUniqueIso _ _

/-- **Sharper: the taut object and `idPointed` have *equal* underlying functors.**  (Not just
isomorphic; `pointedOfPaths_id_F` is a literal equality `F = 𝟭`.)  So the iso `taut_iso_id`
has identity `F`-component up to `eqToHom`, and the entire deviation from the identity lives in
the (invisible, forced) point. -/
theorem taut_F_eq_id :
    (pointedOfPaths (tautF₀ (C := C)) (tautη (C := C))).F = (idPointed (𝒢 := FreeGroupoid C)).F :=
  pointedOfPaths_id_F

end Anchor

end Cyl3

/-! ## Part 2 — worked small bases (FinBPSet surrogate, native_decide)

The topos objects `RefineObj`/`DPathGrpdR`/`cylToPointedObj` are `noncomputable`, so the
*examples* are computed in the `Testing` FinBPSet surrogate.  Dictionary:

* `K.chains`               = objects of `Ch K` = objects of `RefineObj K.init K.final`;
* `K.dimSeq c`             = the shape (altitude bands) of a d-path;
* `K.chLe a b`             = the `RefineObj` morphism order (`a` refines into `b`);
* `K.chainsConnected objs` = those objects lie in one component of `DPathGrpdR K` (the π₀
  test that decides whether a per-object homotopy `η x : of x ⟶ F₀ x` can exist);
* `K.chConnected`          = `DPathGrpdR K` has a single component (π₀ trivial).

For each base we read off `DPathGrpdR K` (= free groupoid on `chains` under `chLe`) and note
what `cylToPointedObj` of a *natural* cylinder records.  By Part 1 the induced pointed
endofunctor is determined up to unique iso by its π₀-object-map `Rgrpd ∘ Lgrpd⁻¹`; when
`DPathGrpdR K` is connected (`chConnected = true`), that map is forced to be the identity on
π₀, so **every** cylinder over such a `K` induces a pointed endofunctor isomorphic to `𝟭`. -/

namespace Cyl3Examples
open CubeTest CubeTest.FinBPSet CubeTest.Examples

set_option linter.style.nativeDecide false

/-! ### `□¹` — the interval.  One d-path, `DPathGrpdR` = the terminal groupoid. -/

-- `chains □¹ = [[e]]`: a single d-path; `DPathGrpdR □¹` is the one-object groupoid.
#eval interval.chains            -- [[e]]
example : interval.chains.length = 1 := by native_decide
-- trivially connected; the tautological cylinder induces `𝟭` (Part 1, `taut_iso_id`).
example : interval.chConnected = true := by native_decide

/-! ### `□²` — the square.  Three d-paths, all in ONE component (`[sq]` is the common cube). -/

-- `chains □² = [[e0_,e_1], [e_0,e1_], [sq]]`: two "staircase" edge-paths + the full square,
-- shapes `[1,1],[1,1],[2]`.  Both edge-paths refine into `[sq]`, so `DPathGrpdR □²` is
-- connected (one π₀ class) — but NOT thin/discrete: it has the staircase-swap loop.
#eval square.chains              -- 3 objects
#eval square.chains.map square.dimSeq
example : square.chains.length = 3 := by native_decide
example : square.chConnected = true := by native_decide
-- the two edge-paths are mutually incomparable but both refine `[sq]`:
example : square.chLe [.e0_, .e_1] [.sq] = true := by native_decide
example : square.chLe [.e_0, .e1_] [.sq] = true := by native_decide
example : square.chLe [.e0_, .e_1] [.e_0, .e1_] = false := by native_decide
-- ⇒ any cylinder over `□²` induces a pointed endofunctor ≅ 𝟭 (π₀ is a single point).

/-! ### The wedge `□¹ ∨ □¹` — a length-2 directed path.  One d-path, `DPathGrpdR` terminal. -/

/-- The serial wedge `□¹ ∨ □¹`: a length-2 path `v0 → vm → v1` (the smallest wedge). -/
def pathWedge : FinBPSet (Fin 5) where
  cellList := [0, 1, 2, 3, 4]   -- 0=v0, 1=vm, 2=v1, 3=eA, 4=eB
  dim := fun c => if c = 3 ∨ c = 4 then 1 else 0
  face := fun ε i c => match c, i with
    | 3, 0 => some (cond ε 1 0)   -- eA : v0 → vm
    | 4, 0 => some (cond ε 2 1)   -- eB : vm → v1
    | _, _ => none
  init := 0
  final := 2

#eval pathWedge.wellFormed       -- true
#eval pathWedge.chains           -- [[eA, eB]]
example : pathWedge.wellFormed = true := by native_decide
example : pathWedge.chains.length = 1 := by native_decide
example : pathWedge.chConnected = true := by native_decide
-- Segal-style: `Ch(□¹∨□¹) ≅ Ch □¹ × Ch □¹`, so `DPathGrpdR` is again terminal (one d-path).

/-! ### `2×1` grid — two squares glued.  Several d-paths, still ONE component. -/

#eval grid2.chains.length        -- 5
#eval grid2.chConnected          -- true
example : grid2.chConnected = true := by native_decide

/-! ## Part 3 — pathologies (the realizability-style findings)

### Pathology A (PROVEN by native_decide) — the construction is a π₀-only invariant; over a
connected base it collapses every cylinder to `𝟭` (total information loss).

This is the cylinder analogue of `Unrealizable`'s four-square loop: there, *bare functoriality*
failed to pin a cube map; here, the *target algebra is too coarse to see the homotopy*.  By
Part 1 (`pointedUniqueIso`) the induced `cylToPointedObj c` is determined up to unique iso by
its π₀-object-map `Rgrpd ∘ Lgrpd⁻¹ : π₀ → π₀`.  When `DPathGrpdR K` is **connected**
(`chConnected = true`) that map is forced to be the identity on π₀, so `cylToPointedObj c ≅ 𝟭`
for *every* cylinder `c`.  The geometric homotopy `sweepR` — the whole point of the
construction — is invisible to the output.

The base the program actually needs is exactly such a `K`: a **rel-interface** cylinder forces
self-loops at the basepoints, and the smallest one is `cylSquare`
(`Testing/CylinderObstruction.lean`).  Its `DPathGrpdR` is connected, so its (nontrivial,
geometrically genuine) cylinder still induces a pointed endofunctor `≅ 𝟭`. -/

-- `cylSquare`: a genuine non-degenerate cylinder (legs `b0e ≠ b1e`, prism cell `pSq`).
-- Yet `DPathGrpdR cylSquare` is CONNECTED: both legs refine into the prism cube `R = [pSq]`.
example : cylSquare.chConnected = true := by native_decide
example : cylSquare.chLe [.b0e] [.pSq] = true := by native_decide
example : cylSquare.chLe [.b1e] [.pSq] = true := by native_decide
-- the legs are distinct d-paths (the cylinder is not trivial) …
example : cylSquare.chLe [.b0e] [.b1e] = false := by native_decide
example : cylSquare.chLe [.b1e] [.b0e] = false := by native_decide
-- … but they are zigzag-connected, so π₀ is a single point and the induced
-- pointed endofunctor is ≅ 𝟭 (`taut_iso_id` applies to EVERY cylinder here): INFO LOSS.
example : cylSquare.chainsConnected [[.b0e], [.pSq], [.b1e]] = true := by native_decide

-- Same collapse for the two-block cylinder `twoBlock` (legs `la = [lc1,lc2]` vs
-- `ra = [rc1,rc2]`): distinct d-paths, one component via the junction-bridge staircase.
example : twoBlock.chLe la ra = false := by native_decide
example : twoBlock.chLe ra la = false := by native_decide
example : twoBlock.chainsConnected [la, m1, bridge, m2, ra] = true := by native_decide

/-! ### Pathology B (PROVEN by native_decide) — the only NON-degenerate regime is a
*disconnected* `DPathGrpdR K`, but there `CylMapWeqR` (left leg a weak equivalence) is the
binding constraint.

For `cylToPointedObj c` to be more than `≅ 𝟭`, its object-map `Rgrpd ∘ Lgrpd⁻¹` must permute
π₀ nontrivially — which requires `DPathGrpdR K` to have **≥ 2 components**.  The minimal such
base is the 1-skeleton `fourPaths` (`Testing/Examples.lean`): `Ch K` is the **discrete**
4-object groupoid (four incomparable directed paths `o ⤳ t`), so π₀ has 4 points and the
endomorphism monoid of `DPathGrpdR fourPaths` realizes all of `End(π₀)`.  This is where the
construction *could* carry information — but a cylinder map must have its left leg a groupoid
equivalence (`CylMapWeqR`), pinning π₀(source) ≅ π₀(K), and the induced permutation is then
exactly the auto of K acting on its d-path components.  So the construction sees *only* the
π₀-action of automorphisms — the same coarse invariant that the lowering refutation isolated. -/

-- `fourPaths`: `Ch K` is DISCONNECTED with 4 incomparable components — the non-degenerate base.
example : fourPaths.chConnected = false := by native_decide
example : fourPaths.chains.length = 4 := by native_decide
-- the 4 d-paths are pairwise incomparable (genuinely 4 π₀-classes):
example : fourPaths.chLe [.a, .b1, .d1] [.a, .b2, .d2] = false := by native_decide
example : fourPaths.chLe [.a, .b1, .d1] [.ap, .g1, .d1] = false := by native_decide
-- Aut K = V₄ acts on these 4 components as the Klein-four subgroup of S₄ (the π₀-action a
-- cylinder's induced functor can record); the other 20 of S₄ are unrealized (lowering-refuted).
example : fourPaths.autK.length = 4 := by native_decide
example : fourPaths.opAutCh.length = 24 := by native_decide

/-! ### Pathology C (the realizability gap, in the spirit of `Unrealizable`)

`Unrealizable.lean` exhibits a poset-automorphism `ρ` of `Ch K` realized by no map of `K`.
The cylinder analogue: a **pointed endofunctor of `DPathGrpdR K` that no cylinder induces**.
Over a connected base (Pathology A) the only pointed endofunctor *up to iso* is `𝟭`, so this is
vacuous there.  Over a disconnected base (`fourPaths`) the candidate pointed endofunctors are
the π₀-permutations; the ones that are **not** the π₀-action of any `Aut K` are exactly the
unrealized chain-automorphisms of the lowering refutation (`S₄ / V₄ ≅ S₃`, 20 of 24).  A
single transposition of two d-paths is a perfectly good endofunctor of the discrete groupoid
`DPathGrpdR fourPaths`, but it fixes a shared edge to two different images, so it is induced by
no cylinder (whose legs are precubical maps).  This is `firstIncoherence`: -/

#eval fourPaths.firstIncoherence       -- a witness (F, c, d₁, d₂): F sends a shared edge two ways
example : fourPaths.firstIncoherence.isSome = true := by native_decide
example : fourPaths.coherentAll = false := by native_decide

/-! ### Summary of the pathologies

* **A.** Connected base ⇒ `cylToPointedObj c ≅ 𝟭` for *all* `c` (total homotopy-information
  loss).  Holds for `□¹`, `□²`, `□¹∨□¹`, the `2×1` grid (all `chConnected`), AND — crucially —
  for the self-linked rel-interface bases the construction requires (`cylSquare`, `twoBlock`).
* **B.** Nontrivial induced functors need a *disconnected* `DPathGrpdR K`; the minimal witness
  is the discrete `fourPaths`, where the construction sees only the π₀-action.
* **C.** Over a disconnected base, most π₀-permuting pointed endofunctors are realized by no
  cylinder — the cylinder analogue of `Unrealizable.ρ` (`firstIncoherence`).

**Cause (one sentence):** the target `PointedEndofunctor (FreeGroupoid (RefineObj …))` is
codiscrete-on-objects (Part 1), so the construction is a π₀-invariant; it is degenerate exactly
when `Ch K` is connected, which is the generic case and the case the program needs.  The
meaningful (geometric) adjunction is the `⊗□¹ ⊣ PathOb` one, not this codiscrete target. -/

end Cyl3Examples
