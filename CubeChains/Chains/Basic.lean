import CubeChains.Foundations.Bipointed
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Chains/Basic

Cube chains in the *junction-vertex* representation: `CubeChain K`, the folded
predicate `IsCubeChain`, the bridge `isCubeChain`/`ofIsCubeChain`, `dims`, `vtxCanon`.

**Layer:** Chains.  **Imports:** `Foundations.Bipointed`, mathlib `PNat`/`BigOperators.List`.
This file is *purely* about cube chains; the wedge-map side lives in `Chains/WedgeMap.lean`
and the equivalence between them in `Chains/Correspondence.lean`.

For a bi-pointed precubical set `K`, a *cube chain* is a sequence of cubes of
positive dimension running from `K.init` to `K.final`, each cube's target vertex
being the next cube's source vertex.

We use the *junction-vertex* representation: alongside the cubes we store the
`l + 1` junction vertices `vtx : Fin (dims.length + 1) → cells 0`, with
`vtx 0 = init`, `vtx last = final`, and `cube i` running from `vtx i.castSucc`
to `vtx i.succ`.  This handles the empty chain uniformly (it forces
`init = final`) and makes the link condition `vertex₁ (cube i) = vertex₀
(cube (i+1))` a theorem rather than a field.

This file is *purely about cube chains*: the structure, its folded predicate
`IsCubeChain`, and the bridge between the two (`isCubeChain`/`ofIsCubeChain`).
The wedge-map side lives in `Chains/WedgeMap.lean`, and the equivalence between
them in `Chains/Correspondence.lean`.
-/

open CategoryTheory Opposite

/-- A cube chain in a bi-pointed precubical set `K`: a list of cubes, each
carrying its own positive dimension as a dependent pair `⟨n, c⟩ : Σ n : ℕ+,
cells n`, together with the junction vertices tying them from `init` to `final`.
The dimension sequence is then the projection `cubes.map (·.1)`. -/
structure CubeChain (K : BPSet) where
  /-- The cubes of the chain, each with its (positive) dimension. -/
  cubes : List (Σ n : ℕ+, K.cells (n : ℕ))
  /-- The `l + 1` junction vertices. -/
  vtx : Fin (cubes.length + 1) → K.cells 0
  /-- The first junction vertex is the initial cell. -/
  vtx_zero : vtx 0 = K.init
  /-- The last junction vertex is the final cell. -/
  vtx_last : vtx (Fin.last cubes.length) = K.final
  /-- The source vertex of the `i`-th cube is junction `i`. -/
  cube_src : ∀ i : Fin cubes.length, K.toPsh.vertex₀ (cubes.get i).2 = vtx i.castSucc
  /-- The target vertex of the `i`-th cube is junction `i + 1`. -/
  cube_tgt : ∀ i : Fin cubes.length, K.toPsh.vertex₁ (cubes.get i).2 = vtx i.succ

/-- The *folded* chain predicate: `IsCubeChain a cubes b` says the cubes run from
`a` to `b`, each cube's target being the next cube's source.  This is the data
underlying a `CubeChain` (`isCubeChain`/`ofIsCubeChain`), with the junction
vertices recovered rather than stored. -/
def IsCubeChain {K : PrecubicalSet} (a : K.cells 0) :
    List (Σ n : ℕ+, K.cells (n : ℕ)) → K.cells 0 → Prop
  | [],            b => a = b
  | ⟨_, c⟩ :: rest, b => K.vertex₀ c = a ∧ IsCubeChain (K.vertex₁ c) rest b

/-- General-endpoints version: a list of cubes with junction vertices `vtx` and
the source/target conditions forms an `IsCubeChain` from `vtx 0` to `vtx last`.
Keeping the endpoints general (rather than fixing `K.init`/`K.final`) is exactly
what makes the induction hypothesis strong enough. -/
theorem isCubeChain_aux {K : BPSet}
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (vtx : Fin (cubes.length + 1) → K.cells 0)
    (hsrc : ∀ i : Fin cubes.length, K.toPsh.vertex₀ (cubes.get i).2 = vtx i.castSucc)
    (htgt : ∀ i : Fin cubes.length, K.toPsh.vertex₁ (cubes.get i).2 = vtx i.succ) :
    IsCubeChain (vtx 0) cubes (vtx (Fin.last cubes.length)) := by
  induction cubes with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, c⟩ := hd
      refine ⟨by simpa using hsrc 0, ?_⟩
      have hstart : K.toPsh.vertex₁ c = vtx (Fin.succ 0) := htgt 0
      rw [hstart]
      have key := ih (vtx ∘ Fin.succ)
        (fun i => by rw [Function.comp_apply, Fin.succ_castSucc]; exact hsrc i.succ)
        (fun i => by rw [Function.comp_apply]; exact htgt i.succ)
      simp only [Function.comp_apply, Fin.succ_last] at key
      exact key

/-- Every `CubeChain` gives a folded `IsCubeChain` from `K.init` to `K.final`. -/
theorem isCubeChain {K : BPSet} (C : CubeChain K) :
    IsCubeChain K.init C.cubes K.final := by
  have h := isCubeChain_aux C.cubes C.vtx C.cube_src C.cube_tgt
  rw [C.vtx_last, C.vtx_zero] at h
  exact h

namespace CubeChain

variable {K : BPSet}

/-- The dimension sequence of a chain: the dimensions of its cubes. -/
def dims (c : CubeChain K) : List ℕ+ := c.cubes.map (·.1)

/-! ### The canonical junction vertices, and `IsCubeChain → CubeChain`

A chain's `vtx` field is *determined* by its cubes: junction `i` is the source
vertex of cube `i`, and the final junction is `b` (`= K.final`).  We package this
as `vtxCanon`, defined by `Fin.cons` recursion so that the `0`/`succ` junctions
are definitional.  Reading the conditions off a folded `IsCubeChain` is then two
short mutually-recursive inductions (`isCubeChain_vtx_zero`/`isCubeChain_vtx_tgt`),
with no `Fin.lastCases` bookkeeping. -/

/-- The canonical junction-vertex function of a cube list ending at `b`: junction
`i` is the source vertex `vertex₀ (cubes[i])`, and the final junction is `b`. -/
noncomputable def vtxCanon : (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) →
    K.cells 0 → Fin (cubes.length + 1) → K.cells 0
  | [],           b => fun _ => b
  | ⟨_, c⟩ :: tl, b => Fin.cons (K.toPsh.vertex₀ c) (vtxCanon tl b)

@[simp] theorem vtxCanon_cons_succ (n : ℕ+) (c : K.cells (n : ℕ))
    (tl : List (Σ n : ℕ+, K.cells (n : ℕ))) (b : K.cells 0)
    (i : Fin (tl.length + 1)) :
    vtxCanon (⟨n, c⟩ :: tl) b i.succ = vtxCanon tl b i := by
  simp only [vtxCanon, Fin.cons_succ]

/-- The interior junctions of `vtxCanon` are the cubes' source vertices — this is
exactly the `cube_src` field. -/
@[simp] theorem vtxCanon_castSucc (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (b : K.cells 0) (i : Fin cubes.length) :
    vtxCanon cubes b i.castSucc = K.toPsh.vertex₀ (cubes.get i).2 := by
  induction cubes with
  | nil => exact i.elim0
  | cons hd tl ih =>
      obtain ⟨n, c⟩ := hd
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [vtxCanon]
      · rw [← Fin.succ_castSucc, vtxCanon_cons_succ]; exact ih k

/-- The final junction of `vtxCanon` is `b` — this is exactly the `vtx_last` field. -/
@[simp] theorem vtxCanon_last (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (b : K.cells 0) : vtxCanon cubes b (Fin.last cubes.length) = b := by
  induction cubes with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, c⟩ := hd
      exact (vtxCanon_cons_succ n c tl b (Fin.last tl.length)).trans ih

/-- `vtxCanon` reads the initial junction off the folded chain (the `vtx_zero`
field): for a chain `a → cubes → b`, the first junction is `a`. -/
theorem isCubeChain_vtx_zero (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a cubes b) :
    vtxCanon cubes b 0 = a := by
  cases cubes with
  | nil => exact h.symm
  | cons hd tl => obtain ⟨n, c⟩ := hd; simpa [vtxCanon] using h.1

/-- `vtxCanon` realises every cube's target as the next junction (the `cube_tgt`
field): the `0`-th cube lands on the start of the tail chain (`isCubeChain_vtx_zero`),
and later cubes recurse. -/
theorem isCubeChain_vtx_tgt : ∀ (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (_ : IsCubeChain a cubes b)
    (i : Fin cubes.length),
    K.toPsh.vertex₁ (cubes.get i).2 = vtxCanon cubes b i.succ
  | _, _, [], _, i => i.elim0
  | a, b, ⟨n, c⟩ :: tl, h, i => by
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [vtxCanon_cons_succ]
        exact (isCubeChain_vtx_zero (K.toPsh.vertex₁ c) b tl h.2).symm
      · rw [vtxCanon_cons_succ]
        exact isCubeChain_vtx_tgt (K.toPsh.vertex₁ c) b tl h.2 k

/-- **`IsCubeChain → CubeChain`**, the inverse of `isCubeChain`: bundle cubes
satisfying the folded chain condition into a `CubeChain`, with junctions
`vtxCanon`.  All four chain fields are the `vtxCanon` lemmas above. -/
noncomputable def ofIsCubeChain (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (h : IsCubeChain K.init cubes K.final) : CubeChain K where
  cubes := cubes
  vtx := vtxCanon cubes K.final
  vtx_zero := isCubeChain_vtx_zero K.init K.final cubes h
  vtx_last := vtxCanon_last cubes K.final
  cube_src := fun i => (vtxCanon_castSucc cubes K.final i).symm
  cube_tgt := isCubeChain_vtx_tgt K.init K.final cubes h

/-- A chain's junction function is forced by its cubes (`cube_src` pins the
interior junctions, `vtx_last` the final one), so it equals `vtxCanon`. -/
theorem vtx_eq_vtxCanon (C : CubeChain K) : C.vtx = vtxCanon C.cubes K.final := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [C.vtx_last, vtxCanon_last]
  | cast j => rw [← C.cube_src, vtxCanon_castSucc]

/-- A `CubeChain` is determined by its cubes (the junctions are forced, the rest
is `Prop`).  In particular `C = ofIsCubeChain C.cubes (isCubeChain C)`. -/
theorem eq_of_cubes {C₁ C₂ : CubeChain K} (hc : C₁.cubes = C₂.cubes) : C₁ = C₂ := by
  obtain ⟨c₁, v₁, z₁, l₁, s₁, t₁⟩ := C₁
  obtain ⟨c₂, v₂, z₂, l₂, s₂, t₂⟩ := C₂
  obtain rfl := hc
  obtain rfl : v₁ = v₂ :=
    (vtx_eq_vtxCanon ⟨c₁, v₁, z₁, l₁, s₁, t₁⟩).trans (vtx_eq_vtxCanon ⟨c₁, v₂, z₂, l₂, s₂, t₂⟩).symm
  rfl

end CubeChain
