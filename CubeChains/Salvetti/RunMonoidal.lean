import CubeChains.Foundations.BoxMonoidal
import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.Correspondence
import CubeChains.Chains.SerialWedgeFunctor
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Salvetti/RunMonoidal — the all-edges runs and `run` as a monoidal functor

`run n = ⋁(1ⁿ)` is the finest chain shape; `runPlus`/`runSl`/`runSr` are its wedge-splitting isos,
and `run` is packaged as a (strong) monoidal functor `(ℕ,+) ⥤ (WedgeBP, ∨)` with tensorator
`runPlus`.  The retraction machinery (`Run`, `runRetract`, `Chains/Salvetti/Lines`) builds on this.
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet MonoidalCategory

namespace CubeChains

/-- `n ↦ 1ⁿ`, the all-edges word; `Multiplicative` so that `⊗` on the source is `ℕ`'s `+`. -/
def onesObj (n : Multiplicative ℕ) : FreeMonoid ℕ+ :=
  FreeMonoid.ofList (List.replicate n.toAdd 1)

/-- The tensorator's content: concatenating all-edges words adds their lengths. -/
theorem onesObj_mul (m n : Multiplicative ℕ) :
    onesObj m * onesObj n = onesObj (m * n) :=
  congrArg FreeMonoid.ofList (List.replicate_append_replicate ..)

def Ones : Discrete (Multiplicative ℕ) ⥤ DimList :=
  Discrete.functor (fun n => (Discrete.mk (onesObj n)))

/-- Strong monoidal: the coherence squares are equations in the thin category `DimList`. -/
instance : Ones.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Discrete.eqToIso rfl
      μIso := fun X Y => Discrete.eqToIso (onesObj_mul X.as Y.as)
      μIso_hom_natural_left := fun _ _ => Subsingleton.elim _ _
      μIso_hom_natural_right := fun _ _ => Subsingleton.elim _ _
      associativity := fun _ _ _ => Subsingleton.elim _ _
      left_unitality := fun _ => Subsingleton.elim _ _
      right_unitality := fun _ => Subsingleton.elim _ _ }

def OneD : Discrete (Multiplicative ℕ) ⥤ BPSet := Ones ⋙ serialWedgeFunctor

instance : OneD.LaxMonoidal := inferInstanceAs ((Ones ⋙ serialWedgeFunctor).LaxMonoidal)

def Run (k : List ℕ+) : Type :=
  BPSet.Hom (OneD.obj (Discrete.mk (BPSet.dimSum k))) (⋁ k)

def runConsL (x : Run (a :: b)) : Run [a] := sorry
def runConsR (x : Run (a :: b)) : Run b := sorry

/-! ### Restricting a chain along a face

`restrictChain face C` projects every cube of `C` onto the directions `face` uses, dropping the
ones that collapse to a point.  Dimension-decreasing, endpoints to endpoints.

The projection itself is not a precubical map — `Box` has no degeneracies, and it drops the
dimension of any cube whose free coordinates `face` omits.  It becomes a chain map because a
collapsed cube has *equal endpoints* after projection, so its neighbours still compose.

Everything routes through `faceEmb`, and that is forced: the restriction depends on `face` only
through the directions it uses, never through its `ε`s, so nothing natural in `face` as a cube map
can be it.  Do not look for a universal property over `Box`; there isn't one. -/

/-- **The projection.**  Restrict a sign vector to the directions `face` uses. -/
def restrictCoord {n b : ℕ} (face : ▫n ⟶ ▫b) {k : ℕ} (c : Cell b k) : Fin n → Option Bool :=
  fun i => c.val (faceEmb face i)

/-- Vertices project to vertices: dimension `0` is total. -/
theorem card_restrictCoord_zero {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Cell b 0) :
    (noneSet (restrictCoord face c)).card = 0 := by
  have hc : ∀ j, c.val j ≠ none := fun j hj => by
    have hmem : j ∈ noneSet c.val := mem_noneSet.mpr hj
    rw [Finset.card_eq_zero.mp c.prop] at hmem
    exact Finset.notMem_empty _ hmem
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun i hi => ?_)
  have h1 : restrictCoord face c i = none := mem_noneSet.mp hi
  exact hc (faceEmb face i) h1

/-- **One cube at a time.**  The projected cell, with its dimension read off the sign vector. -/
def restrictCell {n b k : ℕ} (face : ▫n ⟶ ▫b) (s : Cell b k) :
    Cell n (noneSet (restrictCoord face s)).card :=
  ⟨restrictCoord face s, rfl⟩

/-- Project a vertex. -/
def restrictVertex {n b : ℕ} (face : ▫n ⟶ ▫b) (v : (cube b).cells 0) : (cube n).cells 0 :=
  Box.ofSign ⟨restrictCoord face (Box.sign v), card_restrictCoord_zero face (Box.sign v)⟩

/-- **Project a cube**: keep it when something survives, drop it when it collapses.  The kept
dimension is `≤` the original — that is the whole of "dimension-decreasing". -/
def restrictCube {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) :
    Option (Σ d : ℕ+, (cube n).cells (d : ℕ)) :=
  if h : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card then
    some ⟨⟨_, h⟩, Box.ofSign (restrictCell face (Box.sign c.2))⟩
  else none

theorem sign_restrictVertex {n b : ℕ} (face : ▫n ⟶ ▫b) (v : (cube b).cells 0) :
    (Box.sign (restrictVertex face v)).val = restrictCoord face (Box.sign v) :=
  congrArg Subtype.val (Box.sign_ofSign _)

/-! #### Endpoints, via composition

An extremal vertex is composition with a constant map (`sign_vertex₀/₁`), so a single
commutation — restriction commutes with `subst`ing a constant — gives *both* the kept case and
the collapsed case.  No case analysis on `restrictCube`. -/

theorem sign_vertex₀ {b k : ℕ} (c : (cube b).cells k) :
    Box.sign ((cube b).toPsh.vertex₀ c) = subst (Box.sign c) (constVertex k false) := by
  change Box.sign (PrecubicalSet.initVertexMap k ≫ c) = _
  rw [Box.sign_comp, show Box.sign (PrecubicalSet.initVertexMap k) = constVertex k false from
    ev_canonicalMap _]

theorem sign_vertex₁ {b k : ℕ} (c : (cube b).cells k) :
    Box.sign ((cube b).toPsh.vertex₁ c) = subst (Box.sign c) (constVertex k true) := by
  change Box.sign (PrecubicalSet.finalVertexMap k ≫ c) = _
  rw [Box.sign_comp, show Box.sign (PrecubicalSet.finalVertexMap k) = constVertex k true from
    ev_canonicalMap _]

/-- **The one commutation.**  Restriction commutes with composing a constant map — unconditionally,
whatever the projected dimension turns out to be. -/
theorem restrictCoord_subst_const {n b k : ℕ} (face : ▫n ⟶ ▫b) (s : Cell b k) (ε : Bool) :
    restrictCoord face (subst s (constVertex k ε))
      = (subst (restrictCell face s) (constVertex _ ε)).val := by
  funext i
  change (subst s (constVertex k ε)).val (faceEmb face i) = _
  rw [subst_val, subst_val]
  by_cases h : s.val (faceEmb face i) = none
  · rw [substFun_of_none s _ h, substFun_of_none (restrictCell face s) _ h]; rfl
  · rw [substFun_of_some s _ h, substFun_of_some (restrictCell face s) _ h]; rfl

/-- A cube with no surviving free coordinate is fixed by `subst`ing a constant — which is exactly
why a collapsed cube's two endpoints coincide. -/
theorem subst_const_of_no_free {n k : ℕ} (X : Cell n k) (ε : Bool) (h : ∀ j, X.val j ≠ none) :
    (subst X (constVertex k ε)).val = X.val := by
  funext j; rw [subst_val, substFun_of_some _ _ (h j)]

/-! #### Reading off the two cases -/

theorem restrictVertex_vertex₀ {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) :
    restrictVertex face ((cube b).toPsh.vertex₀ c.2) = (cube n).toPsh.vertex₀ d.2 := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    apply Box.hom_ext; apply Subtype.ext
    rw [sign_restrictVertex, sign_vertex₀ c.2, restrictCoord_subst_const, sign_vertex₀,
      Box.sign_ofSign]
    rfl
  · rw [restrictCube, dif_neg hpos] at h; cases h

theorem restrictVertex_vertex₁ {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) :
    restrictVertex face ((cube b).toPsh.vertex₁ c.2) = (cube n).toPsh.vertex₁ d.2 := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    apply Box.hom_ext; apply Subtype.ext
    rw [sign_restrictVertex, sign_vertex₁ c.2, restrictCoord_subst_const, sign_vertex₁,
      Box.sign_ofSign]
    rfl
  · rw [restrictCube, dif_neg hpos] at h; cases h

/-- **A dropped cube collapses**: nothing survives, so `subst`ing a constant does nothing and both
endpoints land on the same vertex.  This is the whole reason the projection lifts. -/
theorem restrictVertex_collapse {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (h : restrictCube face c = none) :
    restrictVertex face ((cube b).toPsh.vertex₀ c.2)
      = restrictVertex face ((cube b).toPsh.vertex₁ c.2) := by
  have hne : ∀ j, (restrictCell face (Box.sign c.2)).val j ≠ none := by
    have hcard : (noneSet (restrictCoord face (Box.sign c.2))).card = 0 := by
      by_contra hc
      rw [restrictCube, dif_pos (Nat.pos_of_ne_zero hc)] at h; cases h
    intro j hj
    have hmem : j ∈ noneSet (restrictCoord face (Box.sign c.2)) := mem_noneSet.mpr hj
    rw [Finset.card_eq_zero.mp hcard] at hmem
    exact Finset.notMem_empty _ hmem
  apply Box.hom_ext; apply Subtype.ext
  rw [sign_restrictVertex, sign_restrictVertex, sign_vertex₀, sign_vertex₁,
    restrictCoord_subst_const, restrictCoord_subst_const,
    subst_const_of_no_free _ _ hne, subst_const_of_no_free _ _ hne]

/-- The cube's own endpoints are constant sign vectors, so they project to the cube's own
endpoints — one proof for both, since `(cube n).init/final` *are* `canonicalMap (constVertex n ε)`. -/
theorem restrictVertex_cubeEnd {n b : ℕ} (face : ▫n ⟶ ▫b) (ε : Bool) :
    restrictVertex face (canonicalMap (constVertex b ε)) = canonicalMap (constVertex n ε) := by
  apply Box.hom_ext; apply Subtype.ext; funext i
  rw [sign_restrictVertex,
    show Box.sign (canonicalMap (constVertex b ε)) = constVertex b ε from ev_canonicalMap _,
    show Box.sign (canonicalMap (constVertex n ε)) = constVertex n ε from ev_canonicalMap _]
  rfl

theorem restrictVertex_init {n b : ℕ} (face : ▫n ⟶ ▫b) :
    restrictVertex face (cube b).init = (cube n).init := restrictVertex_cubeEnd face false

theorem restrictVertex_final {n b : ℕ} (face : ▫n ⟶ ▫b) :
    restrictVertex face (cube b).final = (cube n).final := restrictVertex_cubeEnd face true

/-! #### From one cube to a whole chain -/

/-- By induction on the cube list with moving endpoints — the shape `IsCubeChain` is defined in.
Kept cubes compose by `restrictVertex_vertex₀/₁`; dropped ones are absorbed by
`restrictVertex_collapse`. -/
theorem restrict_isCubeChain {n b : ℕ} (face : ▫n ⟶ ▫b) :
    ∀ (L : List (Σ d : ℕ+, (cube b).cells (d : ℕ))) (v w : (cube b).cells 0),
      IsCubeChain v L w →
      IsCubeChain (restrictVertex face v) (L.filterMap (restrictCube face))
        (restrictVertex face w)
  | [], v, w, h => by simpa [IsCubeChain] using congrArg (restrictVertex face) h
  | c :: rest, v, w, h => by
    obtain ⟨hsrc, htail⟩ := h
    rcases hc : restrictCube face c with _ | d
    · rw [List.filterMap_cons_none hc]
      have := restrict_isCubeChain face rest _ w htail
      rwa [← restrictVertex_collapse face c hc, hsrc] at this
    · rw [List.filterMap_cons_some hc]
      refine ⟨?_, ?_⟩
      · rw [← restrictVertex_vertex₀ face c d hc, hsrc]
      · have := restrict_isCubeChain face rest _ w htail
        rwa [restrictVertex_vertex₁ face c d hc] at this

/-- **Restrict a chain along a face.** -/
def restrictChain {n b : ℕ} (face : ▫n ⟶ ▫b) (C : CubeChain (cube b)) : CubeChain (cube n) :=
  CubeChain.ofIsCubeChain (C.cubes.filterMap (restrictCube face)) <| by
    have h := restrict_isCubeChain face C.cubes _ _ (isCubeChain C)
    rwa [restrictVertex_init, restrictVertex_final] at h

end CubeChains
