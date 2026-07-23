import CubeChains.Foundations.Bipointed
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Chains/Basic

For a bi-pointed precubical set `K`, a *cube chain* is a sequence of cubes of
positive dimension running from `K.init` to `K.final`, each cube's target vertex
being the next cube's source vertex.

The junction vertices are *forced* by the cubes — junction `i` is the source vertex of cube `i`,
and the link condition `vertex₁ (cube i) = vertex₀ (cube (i+1))` is a theorem (`isCubeChain_junction`,
via the recovered `vtxCanon`), not stored data.  So a cube chain is exactly a list of cubes
satisfying the folded predicate `IsCubeChain`.

The wedge-map side lives in `Chains/WedgeMap.lean`, and the equivalence between them in
`Chains/Correspondence.lean`.
-/

open CategoryTheory Opposite

/-- The *folded* chain predicate: `IsCubeChain a cubes b` says the cubes run from `a` to `b`,
each cube's target being the next cube's source. -/
def IsCubeChain {K : PrecubicalSet} (a : K.cells 0) :
    List (Σ n : ℕ+, K.cells (n : ℕ)) → K.cells 0 → Prop
  | [],            b => a = b
  | ⟨_, c⟩ :: rest, b => K.vertex₀ c = a ∧ IsCubeChain (K.vertex₁ c) rest b

/-- A cube chain in a bi-pointed precubical set `K`: a list of cubes of positive dimension,
each `⟨n, c⟩ : Σ n : ℕ+, cells n`, composable from `init` to `final`.  The dimension sequence is
the projection `cubes.map (·.1)`; the junction vertices are recovered, not stored (`vtxCanon`). -/
def CubeChain (K : BPSet) : Type :=
  {cubes : List (Σ n : ℕ+, K.cells (n : ℕ)) // IsCubeChain K.init cubes K.final}

/-- The cubes of a chain. -/
def CubeChain.cubes {K : BPSet} (C : CubeChain K) : List (Σ n : ℕ+, K.cells (n : ℕ)) := C.1

/-- Every `CubeChain` is a folded `IsCubeChain` from `K.init` to `K.final`. -/
theorem isCubeChain {K : BPSet} (C : CubeChain K) : IsCubeChain K.init C.cubes K.final := C.2

/-- **From vertex data to a folded chain.**  A cube list with junction vertices `vtx` and the
source/target conditions forms an `IsCubeChain` from `vtx 0` to `vtx last`.  Keeping the endpoints
general is what makes the induction hypothesis strong enough. -/
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

/-- **Push a cube forward.**  The one operation every "map a cube list along a map" in the tree
is an instance of. -/
def cubePush {L W : PrecubicalSet} (φ : L ⟶ W) (c : Σ n : ℕ+, L.cells (n : ℕ)) :
    Σ n : ℕ+, W.cells (n : ℕ) := ⟨c.1, φ⟪(c.1 : ℕ)⟫ c.2⟩

@[simp] theorem cubePush_fst {L W : PrecubicalSet} (φ : L ⟶ W) (c : Σ n : ℕ+, L.cells (n : ℕ)) :
    (cubePush φ c).1 = c.1 := rfl

@[simp] theorem cubePush_snd {L W : PrecubicalSet} (φ : L ⟶ W) (c : Σ n : ℕ+, L.cells (n : ℕ)) :
    (cubePush φ c).2 = φ⟪(c.1 : ℕ)⟫ c.2 := rfl

@[simp] theorem cubePush_dims {L W : PrecubicalSet} (φ : L ⟶ W)
    (l : List (Σ n : ℕ+, L.cells (n : ℕ))) : (l.map (cubePush φ)).map (·.1) = l.map (·.1) := by
  rw [List.map_map]; rfl

/-- **A pointwise-injective map reflects `IsCubeChain`.**  If the `φ`-images of `cubes` form a
chain, so do `cubes` — `φ` preserves `vertex₀`/`vertex₁` and is injective on `0`-cells.  Only
injectivity at the levels actually occurring is needed, hence the `ℕ`-indexed hypothesis. -/
theorem isCubeChain_of_map_injective {L W : PrecubicalSet} (φ : L ⟶ W)
    (hinj : ∀ n : ℕ, Function.Injective (φ⟪n⟫)) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) (u v : L.cells 0),
    IsCubeChain (φ⟪0⟫ u) (cubes.map (cubePush φ)) (φ⟪0⟫ v) → IsCubeChain u cubes v
  | [], u, v, h => hinj 0 h
  | ⟨n, c⟩ :: rest, u, v, h => by
      rw [List.map_cons] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨hinj 0 ((PrecubicalSet.map_vertex₀ φ c).trans h1), ?_⟩
      refine isCubeChain_of_map_injective φ hinj rest (L.vertex₁ c) v ?_
      rw [PrecubicalSet.map_vertex₁]; exact h2

/-- **A map preserves `IsCubeChain`** — the converse direction, needing no injectivity. -/
theorem isCubeChain_map {L W : PrecubicalSet} (φ : L ⟶ W) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) {u v : L.cells 0},
    IsCubeChain u cubes v → IsCubeChain (φ⟪0⟫ u) (cubes.map (cubePush φ)) (φ⟪0⟫ v)
  | [], _, _, h => congrArg _ h
  | ⟨n, c⟩ :: rest, u, v, h => by
      obtain ⟨h1, h2⟩ := h
      refine ⟨(PrecubicalSet.map_vertex₀ φ c).symm.trans (congrArg _ h1), ?_⟩
      have := isCubeChain_map φ rest h2
      rwa [PrecubicalSet.map_vertex₁] at this

/-- Chains concatenate. -/
theorem IsCubeChain.append {L : PrecubicalSet} :
    ∀ {u v w : L.cells 0} {cs ds : List (Σ n : ℕ+, L.cells (n : ℕ))},
    IsCubeChain u cs v → IsCubeChain v ds w → IsCubeChain u (cs ++ ds) w
  | _, _, _, [], _, h1, h2 => h1 ▸ h2
  | _, _, _, _ :: _, _, ⟨h1, h1'⟩, h2 => ⟨h1, IsCubeChain.append h1' h2⟩

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
def vtxCanon : (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) →
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

/-- `vtxCanon` reads the initial junction off the folded chain: for a chain `a → cubes → b`, the
first junction is `a`. -/
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

/-- **Consecutive cubes glue** — the junction principle of a chain: cube `s`'s target vertex is
cube `t = s+1`'s source vertex, both being junction `vtxCanon … (s+1)`.  The single source for the
wedge spine's `junction_eq`. -/
theorem isCubeChain_junction (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (h : IsCubeChain a cubes b)
    {s t : Fin cubes.length} (hst : (t : ℕ) = (s : ℕ) + 1) :
    K.toPsh.vertex₁ (cubes.get s).2 = K.toPsh.vertex₀ (cubes.get t).2 := by
  rw [isCubeChain_vtx_tgt a b cubes h s, ← vtxCanon_castSucc cubes b t,
    show s.succ = t.castSucc from Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]

/-- **`IsCubeChain → CubeChain`**, the inverse of `isCubeChain`. -/
def ofIsCubeChain (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (h : IsCubeChain K.init cubes K.final) : CubeChain K := ⟨cubes, h⟩

/-- A `CubeChain` is determined by its cubes (the chain condition is a `Prop`). -/
theorem eq_of_cubes {C₁ C₂ : CubeChain K} (hc : C₁.cubes = C₂.cubes) : C₁ = C₂ :=
  Subtype.ext hc

end CubeChain
