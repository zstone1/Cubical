import CubeChains.Foundations.Shift
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Foundations/PathIterate — the iterated (Moore) path object `PathObPow`

The path object `PathOb` (`Foundations/Shift.lean`) is the cocylinder of the *strict*
length-`1` interval `□¹`.  The **Moore** cocylinder `K^{Iₙ}` of the serial interval
`Iₙ = □¹ ∨ ⋯ ∨ □¹` (`n` segments glued end-to-end) is the `n`-fold *serial pullback* of
`PathOb`: a section is `n` homotopy-cubes whose successive ends match.  This file builds
that functor and its length-additivity.

* `PathObPow : ℕ → PrecubicalSet ⥤ PrecubicalSet` — the length-`n` iterated path object,
  `PathObPow 0 = 𝟭`, `PathObPow 1 = PathOb`, and `PathObPow (n+1)` glues a fresh `PathOb`
  segment onto the right end of `PathObPow n` (the functor-category pullback of the right
  endpoint of `PathObPow n` against the left `endpoint` of `PathOb`).
* `pathObPowLeft`/`pathObPowRight : PathObPow n ⟶ 𝟭` — the two *outer* endpoint
  evaluations (global start vertex / global end vertex of the Moore homotopy).
* `PathObPow.isPullback` — the pointwise pullback square realising the glue step at an
  object `K`.
* `pathObPowGlueIso n m K : (PathObPow (n+m)).obj K ≅ glue` — the **length-additivity**
  isomorphism, where `glue = pullback (Rₙ K) (Lₘ K)` glues the right end of the length-`n`
  cocylinder to the left end of the length-`m` one.  PROVEN for all `n, m` by iterated
  pullback associativity (`IsPullback.paste_vert`), together with its outer-endpoint
  compatibilities.

**Layer:** Foundations.  **Imports:** `Foundations/Shift` (`PathOb`, `endpoint`), mathlib
`FunctorCategory`/`Pullback`/`Types.Limits` (functor-category pullbacks come from
`Type` being complete).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace PrecubicalSet

/-! ## 1. A bundled interval cocylinder and the serial-glue step

We carry the cocylinder functor together with its two outer endpoints.  This is the data
that the serial gluing recursion consumes (the right end of one segment is matched against
the left end of the next). -/

/-- An **interval cocylinder**: a cocylinder functor `(Iₙ ⟹ -)` packaged with its two outer
endpoint evaluations `left`/`right : cocyl ⟶ 𝟭` (the global start/end vertices of the
homotopy). -/
structure IntervalCocyl where
  /-- The cocylinder functor `(Iₙ ⟹ -)`. -/
  cocyl : PrecubicalSet ⥤ PrecubicalSet
  /-- Outer left endpoint (global start vertex). -/
  left : cocyl ⟶ 𝟭 PrecubicalSet
  /-- Outer right endpoint (global end vertex). -/
  right : cocyl ⟶ 𝟭 PrecubicalSet

namespace IntervalCocyl

/-- The length-`0` cocylinder: the identity functor with trivial endpoints (the point's
cocylinder `K^{□⁰} = K`). -/
def unit : IntervalCocyl := ⟨𝟭 _, 𝟙 _, 𝟙 _⟩

/-- The length-`1` cocylinder: `PathOb` with its two `endpoint` evaluations. -/
def one : IntervalCocyl := ⟨PathOb, endpoint false, endpoint true⟩

/-- **Serial gluing.**  Glue the right end of `C` to the left end of `D` via the
functor-category pullback `C.cocyl ×_{𝟭} D.cocyl` (of `C.right` against `D.left`).  The
composite's outer endpoints are `C.left` (outer left) and `D.right` (outer right). -/
noncomputable def glue (C D : IntervalCocyl) : IntervalCocyl where
  cocyl := Limits.pullback C.right D.left
  left := Limits.pullback.fst C.right D.left ≫ C.left
  right := Limits.pullback.snd C.right D.left ≫ D.right

end IntervalCocyl

/-- The recursive interval cocylinder `iCocyl n = (Iₙ ⟹ -)`, built by snocing one `PathOb`
segment onto the right at each step: `iCocyl 0 = 𝟭`, `iCocyl 1 = PathOb`, and
`iCocyl (n+2) = glue (iCocyl (n+1)) PathOb`. -/
noncomputable def iCocyl : ℕ → IntervalCocyl
  | 0 => .unit
  | 1 => .one
  | n + 2 => .glue (iCocyl (n + 1)) .one

/-! ## 2. The iterated path object functor and its outer endpoints -/

/-- **The length-`n` iterated (Moore) path object** `PathObPow n = (Iₙ ⟹ -)`: the `n`-fold
serial pullback of `PathOb`.  `PathObPow 0 = 𝟭`, `PathObPow 1 = PathOb`, and
`PathObPow (n+1)` glues a fresh `PathOb` onto the right of `PathObPow n`. -/
noncomputable def PathObPow (n : ℕ) : PrecubicalSet ⥤ PrecubicalSet := (iCocyl n).cocyl

/-- The **outer left endpoint** `PathObPow n ⟶ 𝟭` — global start vertex. -/
noncomputable def pathObPowLeft (n : ℕ) : PathObPow n ⟶ 𝟭 PrecubicalSet := (iCocyl n).left

/-- The **outer right endpoint** `PathObPow n ⟶ 𝟭` — global end vertex. -/
noncomputable def pathObPowRight (n : ℕ) : PathObPow n ⟶ 𝟭 PrecubicalSet := (iCocyl n).right

@[simp] theorem PathObPow_zero : PathObPow 0 = 𝟭 PrecubicalSet := rfl
@[simp] theorem PathObPow_one : PathObPow 1 = PathOb := rfl

@[simp] theorem pathObPowLeft_one : pathObPowLeft 1 = endpoint false := rfl
@[simp] theorem pathObPowRight_one : pathObPowRight 1 = endpoint true := rfl

/-- `PathObPow (n+2)` is the serial glue of `PathObPow (n+1)` with one more `PathOb`. -/
theorem PathObPow_succ_succ (n : ℕ) :
    PathObPow (n + 2) = Limits.pullback (pathObPowRight (n + 1)) (endpoint false) := rfl

/-- `PathObPow 2` is the length-`2` cocylinder `pullback (endpoint true) (endpoint false)`. -/
theorem PathObPow_two :
    PathObPow 2 = Limits.pullback (endpoint true) (endpoint false) := rfl

/-! ## 3. The pointwise glue square

Evaluation at `K` preserves the functor-category pullback, so at each object `K` the glue
step `PathObPow (n+2)` is the honest pullback of the right endpoint of `PathObPow (n+1)`
against the left `endpoint` of `PathOb`. -/

/-- The first projection of the glue step `(PathObPow (n+2)).obj K ⟶ (PathObPow (n+1)).obj K`. -/
noncomputable def PathObPow.glueFst (n : ℕ) (K : PrecubicalSet) :
    (PathObPow (n + 2)).obj K ⟶ (PathObPow (n + 1)).obj K :=
  (Limits.pullback.fst (pathObPowRight (n + 1)) (endpoint false)).app K

/-- The second projection of the glue step `(PathObPow (n+2)).obj K ⟶ PathOb K`. -/
noncomputable def PathObPow.glueSnd (n : ℕ) (K : PrecubicalSet) :
    (PathObPow (n + 2)).obj K ⟶ PathOb.obj K :=
  (Limits.pullback.snd (pathObPowRight (n + 1)) (endpoint false)).app K

/-- **The pointwise glue square.**  At `K`, `(PathObPow (n+2)).obj K` is the pullback of the
right endpoint of `PathObPow (n+1)` against `endpoint false` — the matched-end gluing of one
more segment.  Obtained by evaluating the functor-category pullback at `K`. -/
noncomputable def PathObPow.isPullback (n : ℕ) (K : PrecubicalSet) :
    IsPullback (PathObPow.glueFst n K) (PathObPow.glueSnd n K)
      ((pathObPowRight (n + 1)).app K) ((endpoint false).app K) :=
  (IsPullback.of_hasPullback (pathObPowRight (n + 1)) (endpoint false)).map
    ((evaluation _ _).obj K)

/-! ### Endpoint recursion at an object

The outer endpoints are computed from the glue projections: the outer left endpoint of
`PathObPow (n+2)` is `glueFst ≫` the outer left of `PathObPow (n+1)`, and the outer right is
`glueSnd ≫ endpoint true` (the new segment's far end). -/

@[simp] theorem pathObPowLeft_zero_app (K : PrecubicalSet) :
    (pathObPowLeft 0).app K = 𝟙 K := rfl
@[simp] theorem pathObPowRight_zero_app (K : PrecubicalSet) :
    (pathObPowRight 0).app K = 𝟙 K := rfl

theorem pathObPowLeft_succ_succ_app (n : ℕ) (K : PrecubicalSet) :
    (pathObPowLeft (n + 2)).app K
      = PathObPow.glueFst n K ≫ (pathObPowLeft (n + 1)).app K := rfl

theorem pathObPowRight_succ_succ_app (n : ℕ) (K : PrecubicalSet) :
    (pathObPowRight (n + 2)).app K
      = PathObPow.glueSnd n K ≫ (endpoint true).app K := rfl

/-! ## 4. Length-additivity

The headline `pathObPowGlueIso` says `(PathObPow (n+m)).obj K` is the matched pullback of the
length-`n` and length-`m` cocylinders.  We package the data (the two projections, the
pullback witness, and the two outer-endpoint identities) as `GlueAt` and produce it by
induction on `m`, the inductive step being a single pullback paste (`IsPullback.paste_vert`)
of the previous glue square against one more segment's glue square (`succGlue`).  This is the
iterated pullback associativity, done sorry-free for all `n, m`. -/

/-- The data exhibiting `(PathObPow (n+m)).obj K` as the matched pullback gluing the
length-`n` cocylinder's right end to the length-`m` cocylinder's left end: the two
projections, the pullback square, and the compatibility of the *outer* endpoints. -/
structure GlueAt (n m : ℕ) (K : PrecubicalSet) where
  /-- Projection onto the length-`n` (left) factor. -/
  fst : (PathObPow (n + m)).obj K ⟶ (PathObPow n).obj K
  /-- Projection onto the length-`m` (right) factor. -/
  snd : (PathObPow (n + m)).obj K ⟶ (PathObPow m).obj K
  /-- The matched-end pullback square. -/
  isPb : IsPullback fst snd ((pathObPowRight n).app K) ((pathObPowLeft m).app K)
  /-- The composite's outer left endpoint is the left factor's outer left endpoint. -/
  leftEq : (pathObPowLeft (n + m)).app K = fst ≫ (pathObPowLeft n).app K
  /-- The composite's outer right endpoint is the right factor's outer right endpoint. -/
  rightEq : (pathObPowRight (n + m)).app K = snd ≫ (pathObPowRight m).app K

/-- **One-segment glue square (for any length).**  For every `j`, `(PathObPow (j+1)).obj K`
is the pullback gluing the length-`j` cocylinder's right end to a single `PathOb`'s left
`endpoint`.  Covers the base `j = 0` (`PathObPow 1 = PathOb`, glued onto the point) and the
recursive `j = i+1` step (the `PathObPow.isPullback` square) uniformly. -/
noncomputable def succGlue (j : ℕ) (K : PrecubicalSet) : GlueAt j 1 K := by
  cases j with
  | zero =>
    -- `PathObPow 1 = PathOb`, glued onto the point `PathObPow 0 = 𝟭`.
    refine
      { fst := (endpoint false).app K
        snd := 𝟙 _
        isPb := ?_
        leftEq := ?_
        rightEq := ?_ }
    · -- pullback of `R 0 = 𝟙 K` against `L 1 = endpoint false`: the iso square, flipped.
      refine IsPullback.of_horiz_isIso (g := 𝟙 K) ?_ |>.flip
      exact ⟨by simp⟩
    · simp
    · simp
  | succ i =>
    -- The genuine glue step: `PathObPow (i+2)` is the pullback square `PathObPow.isPullback`.
    refine
      { fst := PathObPow.glueFst i K
        snd := PathObPow.glueSnd i K
        isPb := ?_
        leftEq := ?_
        rightEq := ?_ }
    · -- `L 1 = endpoint false`, so the recursion square is exactly the glue square.
      exact PathObPow.isPullback i K
    · rw [pathObPowLeft_succ_succ_app]
    · rw [pathObPowRight_succ_succ_app]; rfl

/-- **The glue data for all `n, m`.**  By induction on `m`: `m = 0` is the identity (gluing
onto the point), and the step `m → m+1` pastes the previous glue square against the
`succGlue` square for one more segment (`IsPullback.paste_vert`), rewriting the outer
endpoints through `succGlue`'s `leftEq`/`rightEq`. -/
noncomputable def glueAt (n m : ℕ) (K : PrecubicalSet) : GlueAt n m K := by
  induction m with
  | zero =>
    -- `n + 0 = n`; glue onto the point `PathObPow 0 = 𝟭`.
    refine
      { fst := 𝟙 _
        snd := (pathObPowRight n).app K
        isPb := ?_
        leftEq := by simp
        rightEq := by simp }
    -- pullback of `R n` against `L 0 = 𝟙 K`: the iso square.
    exact IsPullback.of_horiz_isIso (g := 𝟙 K) ⟨by simp⟩
  | succ m ih =>
    -- `n + (m+1) = (n+m) + 1`.  Glue one more `PathOb` segment onto the right.
    -- `step` exhibits `PathObPow (n+m+1)` as `pullback (R (n+m)) (endpoint false)`;
    -- `rseg` exhibits `PathObPow (m+1)` as `pullback (R m) (endpoint false)`.
    have step := succGlue (n + m) K
    have rseg := succGlue m K
    -- The right factor's inner leg `R (n+m) = ih.snd ≫ R m`, matching the cospan.
    have hR : (pathObPowRight (n + m)).app K = ih.snd ≫ (pathObPowRight m).app K := ih.rightEq
    -- The new right projection `Snd : PathObPow (n+m+1) ⟶ PathObPow (m+1)`, into the
    -- `rseg` pullback (its legs are `step.fst ≫ ih.snd` and `step.snd`).
    refine
      { fst := step.fst ≫ ih.fst
        snd := rseg.isPb.lift (step.fst ≫ ih.snd) step.snd ?_
        isPb := ?_
        leftEq := ?_
        rightEq := ?_ }
    · -- inner-end match for the lift: (step.fst ≫ ih.snd) ≫ R m = step.snd ≫ endpoint false
      rw [Category.assoc, ← hR]; exact step.isPb.w
    · -- The middle square `M : IsPullback step.fst Snd ih.snd rseg.fst`, pasted horizontally
      -- against `ih.isPb`, gives the glue square over `R n` and `L (m+1) = rseg.fst ≫ L m`.
      have hM : IsPullback step.fst
          (rseg.isPb.lift (step.fst ≫ ih.snd) step.snd
            (by rw [Category.assoc, ← hR]; exact step.isPb.w))
          ih.snd rseg.fst :=
        -- the outer square `IsPullback step.fst step.snd (ih.snd ≫ R m) (endpoint false)`
        -- pasted with the right segment square `rseg.isPb` over `R m`.
        IsPullback.of_bot' (by rw [← hR]; exact step.isPb) rseg.isPb
      have hpaste := hM.paste_horiz ih.isPb
      -- rewrite the outer endpoints: bottom = rseg.fst ≫ L m = L (m+1)
      have hL : (pathObPowLeft (m + 1)).app K = rseg.fst ≫ (pathObPowLeft m).app K := rseg.leftEq
      rwa [← hL] at hpaste
    · -- leftEq: L (n+(m+1)) = (step.fst ≫ ih.fst) ≫ L n  (n+(m+1) ≡ (n+m)+1 definitionally)
      change (pathObPowLeft ((n + m) + 1)).app K = (step.fst ≫ ih.fst) ≫ (pathObPowLeft n).app K
      rw [step.leftEq, ih.leftEq, Category.assoc]
    · -- rightEq: R (n+(m+1)) = Snd ≫ R (m+1)
      change (pathObPowRight ((n + m) + 1)).app K = _ ≫ (pathObPowRight (m + 1)).app K
      rw [step.rightEq, rseg.rightEq, ← Category.assoc, rseg.isPb.lift_snd]
/-! ## 5. The public length-additivity API

We expose the additivity as an honest isomorphism `(PathObPow (n+m)).obj K ≅ glue`, where
`glue = Limits.pullback (Rₙ K) (Lₘ K)`, with the four projection/endpoint compatibilities
recorded as `simp` lemmas.  This is the data the geometric Moore composition consumes. -/

/-- The matched pullback **glue object** `(PathObPow n).obj K ×_K (PathObPow m).obj K`: glue
the right end of the length-`n` cocylinder to the left end of the length-`m` one. -/
noncomputable def pathObPowGlue (n m : ℕ) (K : PrecubicalSet) : PrecubicalSet :=
  Limits.pullback ((pathObPowRight n).app K) ((pathObPowLeft m).app K)

/-- **Length-additivity isomorphism.**  The length-`(n+m)` iterated path object is the matched
pullback gluing the length-`n` and length-`m` ones: `(PathObPow (n+m)).obj K ≅ glue`.  PROVEN
for all `n, m` (`glueAt`, by iterated pullback associativity). -/
noncomputable def pathObPowGlueIso (n m : ℕ) (K : PrecubicalSet) :
    (PathObPow (n + m)).obj K ≅ pathObPowGlue n m K :=
  (glueAt n m K).isPb.isoIsPullback _ _
    (IsPullback.of_hasPullback ((pathObPowRight n).app K) ((pathObPowLeft m).app K))

/-- The first glue projection `glue ⟶ (PathObPow n).obj K`. -/
noncomputable def pathObPowGlue.fst (n m : ℕ) (K : PrecubicalSet) :
    pathObPowGlue n m K ⟶ (PathObPow n).obj K :=
  Limits.pullback.fst ((pathObPowRight n).app K) ((pathObPowLeft m).app K)

/-- The second glue projection `glue ⟶ (PathObPow m).obj K`. -/
noncomputable def pathObPowGlue.snd (n m : ℕ) (K : PrecubicalSet) :
    pathObPowGlue n m K ⟶ (PathObPow m).obj K :=
  Limits.pullback.snd ((pathObPowRight n).app K) ((pathObPowLeft m).app K)

@[simp] theorem pathObPowGlueIso_hom_fst (n m : ℕ) (K : PrecubicalSet) :
    (pathObPowGlueIso n m K).hom ≫ pathObPowGlue.fst n m K = (glueAt n m K).fst :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[simp] theorem pathObPowGlueIso_hom_snd (n m : ℕ) (K : PrecubicalSet) :
    (pathObPowGlueIso n m K).hom ≫ pathObPowGlue.snd n m K = (glueAt n m K).snd :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **Outer-left compatibility.**  The glue's first projection, followed by the length-`n`
outer left endpoint, is the length-`(n+m)` outer left endpoint (transported by the iso).  The
global start vertex of the composite is the global start vertex of the left factor. -/
@[simp] theorem pathObPowGlueIso_inv_left (n m : ℕ) (K : PrecubicalSet) :
    (pathObPowGlueIso n m K).inv ≫ (pathObPowLeft (n + m)).app K
      = pathObPowGlue.fst n m K ≫ (pathObPowLeft n).app K := by
  rw [(glueAt n m K).leftEq, Iso.inv_comp_eq, ← Category.assoc, pathObPowGlueIso_hom_fst]

/-- **Outer-right compatibility.**  The glue's second projection, followed by the length-`m`
outer right endpoint, is the length-`(n+m)` outer right endpoint (transported by the iso).  The
global end vertex of the composite is the global end vertex of the right factor. -/
@[simp] theorem pathObPowGlueIso_inv_right (n m : ℕ) (K : PrecubicalSet) :
    (pathObPowGlueIso n m K).inv ≫ (pathObPowRight (n + m)).app K
      = pathObPowGlue.snd n m K ≫ (pathObPowRight m).app K := by
  rw [(glueAt n m K).rightEq, Iso.inv_comp_eq, ← Category.assoc, pathObPowGlueIso_hom_snd]

end PrecubicalSet
