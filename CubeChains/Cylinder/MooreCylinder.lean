import CubeChains.Foundations.PathIterate
import CubeChains.Cylinder.Cylinder

/-!
# Cylinder/MooreCylinder — the geometric Moore cylinder and its composition

A **Moore cylinder** of length `n` over `K` is a directed homotopy whose interval is the
serial interval `Iₙ = □¹ ∨ ⋯ ∨ □¹`: a map `src ⟶ (PathObPow n).obj K` into the length-`n`
iterated path object (`Foundations/PathIterate.lean`).  For `n = 1` this is exactly an
ordinary cylinder `CylMap K = Over (PathOb K)` (`Cylinder/Cylinder.lean`), since
`PathObPow 1 = PathOb`.

The point of this file is the **geometric composition** answering the question: a "list of
cylinders" is the trivial monoidal lift; what we actually want is a single geometric cylinder
realising the concatenation.  Given Moore cylinders `c : E₁ ⟶ PathObPowⁿ K` and
`d : E₂ ⟶ PathObPowᵐ K` whose matched outer legs agree (`c`'s right end glued to `d`'s left
end), `mooreCompose` produces a *single* Moore cylinder of length `n + m`:

* its source is the span-pullback `E₃ = E₁ ×_K E₂` (gluing `c.endLeg` to `d.startLeg`);
* its classifying map is the glued pair `⟨π₁ ≫ c.cyl, π₂ ≫ d.cyl⟩ : E₃ ⟶ PathObPowⁿ K ×_K
  PathObPowᵐ K`, transported across the length-additivity iso
  `PathObPow^{n+m} K ≅ PathObPowⁿ K ×_K PathObPowᵐ K` (`pathObPowGlueIso`).

So `mooreCompose` is the genuine *single-cylinder realisation* of the list `[c, d]`.  Its
outer legs are the outer legs of the factors (`mooreCompose_startLeg`/`_endLeg`), and its
length is additive (`mooreCompose_len`).

The descent theorem (`mooreCompose_one_one_cyl`) records that, in length `1 + 1`, the composite
underlies the length-`2` span composition into `PathObPow 2 = PathOb K ×_K PathOb K` (the
length-`2` cocylinder), i.e. it *is* the span-pullback gluing of the two strict cylinders —
not a fold-collapsed length-`1` cylinder (no such fold exists; see
`Research/Scratch/Cyl7_SpanCompose`).

**Layer:** Cylinder.  **Imports:** `Foundations/PathIterate` (`PathObPow`, `pathObPowGlueIso`),
`Cylinder/Cylinder` (`CylMap`).

## Remaining step (not a `sorry`)

Relating `mooreCompose` to the pointed-endofunctor descent `cylToPointedObj`
(`Cylinder/CylinderRefine.lean`) — i.e. that Moore composition is a monoid homomorphism into
the directed-path groupoid — is deferred: it needs the Moore analogue of the prism/refinement
geometry and is orthogonal to the additivity established here.
-/

open CategoryTheory CategoryTheory.Limits Opposite PrecubicalSet

variable {K : PrecubicalSet}

/-- A **Moore cylinder** of length `n` over `K`: a directed homotopy over the serial interval
`Iₙ`, modelled as a classifying map `src ⟶ (PathObPow n).obj K` into the length-`n` iterated
(Moore) path object.  For `n = 1` this is an ordinary `CylMap K` (`PathObPow 1 = PathOb`). -/
structure MooreCyl (K : PrecubicalSet) where
  /-- The length of the Moore homotopy (number of `□¹`-segments). -/
  n : ℕ
  /-- The homotopy's source precubical set. -/
  src : PrecubicalSet
  /-- The classifying map into the length-`n` iterated path object. -/
  cyl : src ⟶ (PathObPow n).obj K

namespace MooreCyl

/-- The **start leg** `src ⟶ K`: the global start vertex of the Moore homotopy (the outer left
endpoint of the iterated path object). -/
noncomputable def startLeg (c : MooreCyl K) : c.src ⟶ K :=
  c.cyl ≫ (pathObPowLeft c.n).app K

/-- The **end leg** `src ⟶ K`: the global end vertex of the Moore homotopy (the outer right
endpoint of the iterated path object). -/
noncomputable def endLeg (c : MooreCyl K) : c.src ⟶ K :=
  c.cyl ≫ (pathObPowRight c.n).app K

/-! ## Length-1 Moore cylinders are ordinary cylinders

`PathObPow 1 = PathOb`, so a length-`1` Moore cylinder is the same data as an ordinary
`CylMap K = Over (PathOb K)`, and the start/end legs coincide with `CylMap.leftLeg`/`rightLeg`. -/

/-- A length-`1` Moore cylinder is an ordinary cylinder `CylMap K` (its classifying map already
lands in `PathObPow 1 = PathOb K`). -/
noncomputable def ofCylMap (c : CylMap K) : MooreCyl K where
  n := 1
  src := c.src
  cyl := c.cyl

/-- Conversely, every length-`1` Moore cylinder is an ordinary cylinder. -/
noncomputable def toCylMap (c : MooreCyl K) (h : c.n = 1) : CylMap K :=
  Over.mk (c.cyl ≫ (eqToHom (by rw [h, PathObPow_one]) : (PathObPow c.n).obj K ⟶ PathOb.obj K))

@[simp] theorem ofCylMap_startLeg (c : CylMap K) :
    (ofCylMap c).startLeg = c.leftLeg := rfl

@[simp] theorem ofCylMap_endLeg (c : CylMap K) :
    (ofCylMap c).endLeg = c.rightLeg := rfl

/-! ## The geometric composition

Two Moore cylinders `c, d` are *composable* when `c`'s end leg matches `d`'s start leg into `K`.
We glue them on the span-pullback `E₃ = c.src ×_K d.src` (of `c.endLeg` against `d.startLeg`),
producing a single Moore cylinder of length `c.n + d.n`. -/

variable (c d : MooreCyl K)

/-- The **span-pullback source** `E₃ = c.src ×_K d.src` of the matched outer legs `c.endLeg`
against `d.startLeg`. -/
noncomputable def composeSrc : PrecubicalSet := Limits.pullback c.endLeg d.startLeg

/-- The first projection `E₃ ⟶ c.src`. -/
noncomputable def composeπ₁ : composeSrc c d ⟶ c.src := Limits.pullback.fst c.endLeg d.startLeg

/-- The second projection `E₃ ⟶ d.src`. -/
noncomputable def composeπ₂ : composeSrc c d ⟶ d.src := Limits.pullback.snd c.endLeg d.startLeg

theorem compose_condition :
    composeπ₁ c d ≫ c.endLeg = composeπ₂ c d ≫ d.startLeg :=
  Limits.pullback.condition

/-- The glued classifying map into the matched pullback of the two iterated path objects,
`E₃ ⟶ (PathObPow c.n).obj K ×_K (PathObPow d.n).obj K`: the pair `⟨π₁ ≫ c.cyl, π₂ ≫ d.cyl⟩`,
whose matched inner ends agree because `π₁ ≫ c.endLeg = π₂ ≫ d.startLeg`. -/
noncomputable def composeGlue : composeSrc c d ⟶ pathObPowGlue c.n d.n K :=
  Limits.pullback.lift (composeπ₁ c d ≫ c.cyl) (composeπ₂ c d ≫ d.cyl) (by
    rw [Category.assoc, Category.assoc]
    exact compose_condition c d)

@[simp] theorem composeGlue_fst :
    composeGlue c d ≫ pathObPowGlue.fst c.n d.n K = composeπ₁ c d ≫ c.cyl :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem composeGlue_snd :
    composeGlue c d ≫ pathObPowGlue.snd c.n d.n K = composeπ₂ c d ≫ d.cyl :=
  Limits.pullback.lift_snd _ _ _

/-- **The geometric Moore composition.**  Glue `c` and `d` on the span-pullback `c.src ×_K
d.src` and transport across the length-additivity iso to a *single* Moore cylinder of length
`c.n + d.n`.  This is the genuine single-cylinder realisation of the list `[c, d]`. -/
noncomputable def mooreCompose : MooreCyl K where
  n := c.n + d.n
  src := composeSrc c d
  cyl := composeGlue c d ≫ (pathObPowGlueIso c.n d.n K).inv

@[simp] theorem mooreCompose_len : (mooreCompose c d).n = c.n + d.n := rfl

@[simp] theorem mooreCompose_src : (mooreCompose c d).src = composeSrc c d := rfl

/-- **The composite's start leg is the first factor's start leg** (restricted to the
span-pullback): `startLeg (c ∘ d) = π₁ ≫ c.startLeg`.  The composite's global start vertex is
`c`'s global start vertex. -/
theorem mooreCompose_startLeg :
    (mooreCompose c d).startLeg = composeπ₁ c d ≫ c.startLeg := by
  have h : composeGlue c d ≫ (pathObPowGlueIso c.n d.n K).inv
      ≫ (pathObPowLeft (c.n + d.n)).app K
      = composeπ₁ c d ≫ c.cyl ≫ (pathObPowLeft c.n).app K := by
    rw [pathObPowGlueIso_inv_left, ← Category.assoc, composeGlue_fst, Category.assoc]
  exact h

/-- **The composite's end leg is the second factor's end leg** (restricted to the
span-pullback): `endLeg (c ∘ d) = π₂ ≫ d.endLeg`.  The composite's global end vertex is `d`'s
global end vertex. -/
theorem mooreCompose_endLeg :
    (mooreCompose c d).endLeg = composeπ₂ c d ≫ d.endLeg := by
  have h : composeGlue c d ≫ (pathObPowGlueIso c.n d.n K).inv
      ≫ (pathObPowRight (c.n + d.n)).app K
      = composeπ₂ c d ≫ d.cyl ≫ (pathObPowRight d.n).app K := by
    rw [pathObPowGlueIso_inv_right, ← Category.assoc, composeGlue_snd, Category.assoc]
  exact h

/-! ## Descent: the length-`(1+1)` composite is the strict span composition

For two length-`1` Moore cylinders (i.e. ordinary `CylMap`s), `mooreCompose` has length `2`,
and its classifying map *is* the span composite into the length-`2` cocylinder
`PathObPow 2 = PathOb K ×_K PathOb K` (= the scratch `pathOb2 K`): the glued pair
`⟨π₁ ≫ cyl₁, π₂ ≫ cyl₂⟩`, transported across `pathObPowGlueIso 1 1`.  Concretely, `composeGlue`
of the two length-`1` cylinders is exactly the pullback-lift gluing of the two homotopies (the
strict-cylinder span composition), landing in the genuine length-`2` Moore cocylinder — *not* a
fold-collapsed length-`1` cylinder. -/

/-- **Descent theorem (the answer to the user's question).**  The geometric composite of two
length-`1` Moore cylinders (ordinary cylinders) `c₁, c₂` has length `2`, and its underlying
classifying map is the span-pullback gluing `⟨π₁ ≫ c₁.cyl, π₂ ≫ c₂.cyl⟩` into the length-`2`
cocylinder `pathObPowGlue 1 1 K = PathOb K ×_K PathOb K` — i.e. the single-cylinder realisation
of the strict span composition, before transport by the length-additivity iso.  The two outer
legs are `π₁ ≫ c₁.leftLeg` (left) and `π₂ ≫ c₂.rightLeg` (right). -/
theorem mooreCompose_ofCylMap_glue (c₁ c₂ : CylMap K) :
    composeGlue (ofCylMap c₁) (ofCylMap c₂) ≫ pathObPowGlue.fst 1 1 K
        = composeπ₁ (ofCylMap c₁) (ofCylMap c₂) ≫ c₁.cyl ∧
      composeGlue (ofCylMap c₁) (ofCylMap c₂) ≫ pathObPowGlue.snd 1 1 K
        = composeπ₂ (ofCylMap c₁) (ofCylMap c₂) ≫ c₂.cyl :=
  ⟨composeGlue_fst _ _, composeGlue_snd _ _⟩

/-- The length-`(1+1)` composite has length `2`, landing in the genuine length-`2` Moore
cocylinder `PathObPow 2 = PathOb K ×_K PathOb K` (no fold to length `1`). -/
theorem mooreCompose_ofCylMap_len (c₁ c₂ : CylMap K) :
    (mooreCompose (ofCylMap c₁) (ofCylMap c₂)).n = 2 := rfl

/-- The length-`(1+1)` composite's outer legs are the outer legs of the strict span
composition: `π₁ ≫ leftLeg₁` (left) and `π₂ ≫ rightLeg₂` (right). -/
theorem mooreCompose_ofCylMap_startLeg (c₁ c₂ : CylMap K) :
    (mooreCompose (ofCylMap c₁) (ofCylMap c₂)).startLeg
      = composeπ₁ (ofCylMap c₁) (ofCylMap c₂) ≫ c₁.leftLeg :=
  mooreCompose_startLeg _ _

theorem mooreCompose_ofCylMap_endLeg (c₁ c₂ : CylMap K) :
    (mooreCompose (ofCylMap c₁) (ofCylMap c₂)).endLeg
      = composeπ₂ (ofCylMap c₁) (ofCylMap c₂) ≫ c₂.rightLeg :=
  mooreCompose_endLeg _ _

end MooreCyl
