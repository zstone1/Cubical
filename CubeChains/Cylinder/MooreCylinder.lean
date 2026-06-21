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

## Length-`0` = constant cylinder = composition unit + the `End(K)` embedding

Since `PathObPow 0 = 𝟭`, a **length-`0`** Moore cylinder is just a bare map `cyl : E ⟶ K`: a
*degenerate/constant* directed homotopy (start leg = end leg = `cyl`).  Two payoffs:

* `mooreId K = ⟨0, K, 𝟙 K⟩` is the **composition unit** — `mooreComposeIdRight` proves the right
  unit law `mooreCompose c (mooreId K) ≅ c` (as a same-shape `MIso`); the left unit law holds the
  same way but is left as a TODO-comment (it carries a genuine `0 + c.n = c.n` length cast).
* `MooreCyl.ofEnd (φ : K ⟶ K) = ⟨0, K, φ⟩` (and `ofMap` for general `Hom(E,K)`) realises the
  embedding `End(K) ↪ MooreCyl K` (`ofEnd_injective`, `ofEnd_id`) with **no degeneracy**
  `K ⟶ PathOb K` — the construction the cylinder program's "STEP 4" wanted.

The descent theorem (`mooreCompose_one_one_cyl`) records that, in length `1 + 1`, the composite
underlies the length-`2` span composition into `PathObPow 2 = PathOb K ×_K PathOb K` (the
length-`2` cocylinder), i.e. it *is* the span-pullback gluing of the two strict cylinders —
not a fold-collapsed length-`1` cylinder (no such fold exists, as the `I₂ = □¹∨□¹`
interval has no edge running `init → final`).

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

/-! ## Length-`0` Moore cylinders: the composition unit and the `End(K)` embedding

`PathObPow 0 = 𝟭` (`Foundations/PathIterate.lean`), so a **length-`0`** Moore cylinder is just a
plain map `cyl : E ⟶ K` (no interval to sweep): a *constant/degenerate* directed homotopy whose
start and end legs both equal `cyl`.  Two facts make these the algebraic skeleton of the
composition monoid:

* `mooreId K = ⟨0, K, 𝟙 K⟩` is the **unit**: composing on the right (`mooreComposeIdRight`) gives
  a same-shape isomorphism `mooreCompose c (mooreId K) ≅ c` (`MIso`).  The composite source is the
  pullback `c.src ×_K K` along `(mooreId K).startLeg = 𝟙 K`, whose first projection is an iso
  (`pullback_fst_iso_of_right_iso`); the length cast `c.n + 0 = c.n` is definitional, so no
  `eqToHom` bookkeeping is needed.  (The **left** unit `mooreCompose (mooreId K) c ≅ c` is the
  mirror image but its length is `0 + c.n`, which is only *propositionally* `c.n` — `Nat.zero_add`
  is not defeq — forcing a genuine length cast through `PathObPow`; that cast reduces to
  characterising `(glueAt 0 m K).snd` as the cast `eqToHom`, an induction on `m` left as a TODO,
  see below.)

* `MooreCyl.ofEnd (φ : K ⟶ K) = ⟨0, K, φ⟩` realises **`End(K) ↪ MooreCyl K`** (more generally
  `ofMap (f : E ⟶ K) = ⟨0, E, f⟩` for `Hom(E,K)`).  It is injective in `φ` (`ofEnd_injective`)
  and sends `𝟙 K` to the unit (`ofEnd_id`).  Crucially this needs **no degeneracy** `K ⟶ PathOb K`
  (a length-`0` homotopy has no interval), which is precisely the embedding the cylinder program's
  "STEP 4" wanted but could not get through `PathOb` for want of a degeneracy. -/

/-- The **length-`0` (degenerate/constant) Moore cylinder on `E` with classifying map `f`**:
`⟨0, E, f⟩`.  Since `PathObPow 0 = 𝟭`, this is just the bare map `f : E ⟶ K` viewed as a constant
directed homotopy (start leg = end leg = `f`).  Realises `Hom(E,K) ↪ MooreCyl K` with **no
degeneracy** `K ⟶ PathOb K`. -/
def ofMap {E : PrecubicalSet} (f : E ⟶ K) : MooreCyl K where
  n := 0
  src := E
  cyl := f

/-- The **length-`0` Moore cylinder of an endomorphism** `φ : K ⟶ K`: `⟨0, K, φ⟩ = ofMap φ`.
Realises `End(K) ↪ MooreCyl K`, again with **no degeneracy** `K ⟶ PathOb K` (length `0` needs no
interval) — the embedding the cylinder program's STEP 4 was after. -/
def ofEnd (φ : K ⟶ K) : MooreCyl K := ofMap φ

@[simp] theorem ofMap_n {E : PrecubicalSet} (f : E ⟶ K) : (ofMap f).n = 0 := rfl
@[simp] theorem ofMap_src {E : PrecubicalSet} (f : E ⟶ K) : (ofMap f).src = E := rfl
@[simp] theorem ofMap_cyl {E : PrecubicalSet} (f : E ⟶ K) : (ofMap f).cyl = f := rfl

@[simp] theorem ofEnd_n (φ : K ⟶ K) : (ofEnd φ).n = 0 := rfl
@[simp] theorem ofEnd_src (φ : K ⟶ K) : (ofEnd φ).src = K := rfl
@[simp] theorem ofEnd_cyl (φ : K ⟶ K) : (ofEnd φ).cyl = φ := rfl

/-- **`ofMap` is injective** in the classifying map (over a fixed source `E`): the `cyl` field
recovers `f`. -/
theorem ofMap_injective {E : PrecubicalSet} {f g : E ⟶ K} (h : ofMap f = ofMap g) : f = g := by
  -- `ofMap f = ofMap g` is `mk 0 E f = mk 0 E g`; the `cyl` field equality is heterogeneous
  -- (its type depends on `n`, `src`) but at this fixed shape both sides share the type
  -- `E ⟶ (PathObPow 0).obj K = E ⟶ K`, so it homogenises.
  obtain ⟨_, _, hcyl⟩ := MooreCyl.mk.injEq .. ▸ h
  exact eq_of_heq hcyl

/-- **`ofEnd` is injective**: `ofEnd φ = ofEnd ψ → φ = ψ`, recovering the endomorphism from the
`cyl` field.  This is the injectivity of the embedding `End(K) ↪ MooreCyl K`. -/
theorem ofEnd_injective {φ ψ : K ⟶ K} (h : ofEnd φ = ofEnd ψ) : φ = ψ :=
  ofMap_injective h

/-- The **unit Moore cylinder** `⟨0, K, 𝟙 K⟩`: the length-`0` constant homotopy on `K`.  This is
the two-sided unit for `mooreCompose`; see `mooreComposeIdRight` for the right unit law. -/
def mooreId (K : PrecubicalSet) : MooreCyl K := ofMap (𝟙 K)

@[simp] theorem mooreId_n (K : PrecubicalSet) : (mooreId K).n = 0 := rfl
@[simp] theorem mooreId_src (K : PrecubicalSet) : (mooreId K).src = K := rfl
@[simp] theorem mooreId_cyl (K : PrecubicalSet) : (mooreId K).cyl = 𝟙 K := rfl

/-- **The unit is the endomorphism cylinder of the identity**: `ofEnd (𝟙 K) = mooreId K`. -/
@[simp] theorem ofEnd_id (K : PrecubicalSet) : ofEnd (𝟙 K) = mooreId K := rfl

/-- The unit's **start leg is `𝟙 K`** (a constant homotopy starts where it ends). -/
@[simp] theorem mooreId_startLeg (K : PrecubicalSet) : (mooreId K).startLeg = 𝟙 K := by
  change (𝟙 K) ≫ (pathObPowLeft 0).app K = 𝟙 K
  simp

/-- The unit's **end leg is `𝟙 K`**. -/
@[simp] theorem mooreId_endLeg (K : PrecubicalSet) : (mooreId K).endLeg = 𝟙 K := by
  change (𝟙 K) ≫ (pathObPowRight 0).app K = 𝟙 K
  simp

/-! ### The right unit law `mooreCompose c (mooreId K) ≅ c`

Composing on the right by the unit pulls `c.src` back along `(mooreId K).startLeg = 𝟙 K`, whose
first projection `composeπ₁` is therefore an iso (`pullback_fst_iso_of_right_iso`); the length cast
`c.n + 0 = c.n` is definitional.  We package the result as a `MIso` (a same-length source iso
intertwining the classifying maps). -/

/-- A **same-shape isomorphism of Moore cylinders**: a length equality `hn`, a source isomorphism
`srcIso`, and the compatibility of the classifying maps `cyl` transported across the length
equality (via `eqToHom` on `PathObPow`).  This is the minimal notion in which the unit and
(would-be) associativity laws are stated. -/
structure MIso (c d : MooreCyl K) where
  /-- The two cylinders have the same length. -/
  hn : c.n = d.n
  /-- An isomorphism of the underlying sources. -/
  srcIso : c.src ≅ d.src
  /-- The classifying maps agree after transporting `c.cyl` across the length equality and along
  the source isomorphism. -/
  cyl_compat :
    c.cyl ≫ eqToHom (by rw [hn]) = srcIso.hom ≫ d.cyl

/-- The unit's start leg `(mooreId K).startLeg = 𝟙 K` is an iso (used to make the right-unit
source pullback an isomorphism). -/
instance mooreId_startLeg_isIso (K : PrecubicalSet) : IsIso (mooreId K).startLeg := by
  rw [mooreId_startLeg]; exact IsIso.id K

/-- The unit's end leg `(mooreId K).endLeg = 𝟙 K` is an iso. -/
instance mooreId_endLeg_isIso (K : PrecubicalSet) : IsIso (mooreId K).endLeg := by
  rw [mooreId_endLeg]; exact IsIso.id K

/-- **The right-unit composite source projection is an iso.**  `composeSrc c (mooreId K) =
c.src ×_K K` is a pullback along the iso `(mooreId K).startLeg = 𝟙 K`, so its first projection is
invertible. -/
instance composeπ₁_mooreId_isIso (c : MooreCyl K) : IsIso (composeπ₁ c (mooreId K)) := by
  rw [composeπ₁]
  exact pullback_fst_iso_of_right_iso c.endLeg (mooreId K).startLeg

/-- In the right-unit glue (length `n + 0`), the first `glueAt` projection is the identity. -/
theorem glueAt_zero_fst (n : ℕ) (K : PrecubicalSet) :
    (glueAt n 0 K).fst = 𝟙 ((PathObPow n).obj K) := rfl

/-- **The length-`(n+0)` additivity inverse is the first glue projection.**  Since `glueAt n 0`
has `fst = 𝟙`, the additivity iso `pathObPowGlueIso n 0 K` has inverse exactly the pullback's
first projection `pathObPowGlue.fst n 0 K`. -/
theorem pathObPowGlueIso_zero_inv (n : ℕ) (K : PrecubicalSet) :
    (pathObPowGlueIso n 0 K).inv = pathObPowGlue.fst n 0 K := by
  have hfst : (pathObPowGlueIso n 0 K).hom ≫ pathObPowGlue.fst n 0 K
      = 𝟙 ((PathObPow n).obj K) := by
    rw [pathObPowGlueIso_hom_fst, glueAt_zero_fst]
  calc (pathObPowGlueIso n 0 K).inv
      = (pathObPowGlueIso n 0 K).inv
          ≫ ((pathObPowGlueIso n 0 K).hom ≫ pathObPowGlue.fst n 0 K) := by
            rw [hfst]; exact (Category.comp_id _).symm
    _ = pathObPowGlue.fst n 0 K := by
            rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The right-unit composite classifying map is the first factor's, restricted.**
`(mooreCompose c (mooreId K)).cyl = composeπ₁ c (mooreId K) ≫ c.cyl` (the codomains agree by the
defeq length cast `c.n + 0 = c.n`). -/
theorem mooreCompose_mooreId_cyl (c : MooreCyl K) :
    (mooreCompose c (mooreId K)).cyl = composeπ₁ c (mooreId K) ≫ c.cyl := by
  have h : composeGlue c (mooreId K) ≫ pathObPowGlue.fst c.n 0 K
      = composeπ₁ c (mooreId K) ≫ c.cyl := composeGlue_fst c (mooreId K)
  change composeGlue c (mooreId K) ≫ (pathObPowGlueIso c.n 0 K).inv = _
  rw [pathObPowGlueIso_zero_inv]
  exact h

/-- **RIGHT UNIT LAW.**  `mooreCompose c (mooreId K) ≅ c` as a Moore cylinder: same length
(`c.n + 0 = c.n`, definitional), source isomorphism `c.src ×_K K ≅ c.src` (the first projection,
an iso since `(mooreId K).startLeg = 𝟙 K`), and the classifying maps intertwine
(`mooreCompose_mooreId_cyl`). -/
noncomputable def mooreComposeIdRight (c : MooreCyl K) :
    MIso (mooreCompose c (mooreId K)) c where
  hn := rfl
  srcIso := @asIso _ _ _ _ _ (composeπ₁_mooreId_isIso c)
  cyl_compat := by
    rw [asIso_hom]
    -- the length cast is `eqToHom rfl = 𝟙` (`c.n + 0 ≡ c.n`), absorbed definitionally
    exact mooreCompose_mooreId_cyl c

/-! ### Left unit law (TODO, not a `sorry`)

The mirror statement `mooreCompose (mooreId K) c ≅ c` holds geometrically by the same pullback
argument: `composeSrc (mooreId K) c = K ×_K c.src` is a pullback along the iso
`(mooreId K).endLeg = 𝟙 K`, so its **second** projection `composeπ₂ (mooreId K) c` is an iso
(`composeπ₂_mooreId_isIso`).  The obstruction is purely the length: the composite has length
`0 + c.n`, which is only *propositionally* equal to `c.n` (`Nat.zero_add` is not definitional), so
the `MIso.cyl_compat` carries a genuine non-trivial length cast `eqToHom : (PathObPow (0+c.n)).obj K
= (PathObPow c.n).obj K`.  Discharging it reduces to characterising the additivity-iso inverse as
that cast,
  `(pathObPowGlueIso 0 c.n K).inv ≫ eqToHom = pathObPowGlue.snd 0 c.n K`,
equivalently `(glueAt 0 m K).snd = eqToHom (Nat.zero_add ▸ rfl)`, an induction on `m` whose step
unfolds `glueAt`'s `rseg.isPb.lift`.  This cast bookkeeping is deferred (the right unit suffices
for the unit-law content). -/

/-- **The left-unit composite source projection is an iso.**  `composeSrc (mooreId K) c =
K ×_K c.src` is a pullback along the iso `(mooreId K).endLeg = 𝟙 K`, so its second projection is
invertible.  (The source-isomorphism half of the left unit law; only the length cast is missing,
see the TODO above.) -/
instance composeπ₂_mooreId_isIso (c : MooreCyl K) : IsIso (composeπ₂ (mooreId K) c) := by
  rw [composeπ₂]
  exact pullback_snd_iso_of_left_iso (mooreId K).endLeg c.startLeg

end MooreCyl
