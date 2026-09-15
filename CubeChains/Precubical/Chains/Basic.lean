import CubeChains.Precubical.Basic.Bipointed
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Precubical/Chains/Basic

For a bi-pointed precubical set `K`, a *cube chain* is a sequence of cubes of positive dimension
running from `K.init` to `K.final`, each cube's target vertex being the next cube's source vertex.

The junction vertices are *forced* by the cubes — junction `i` is the source vertex of cube `i` —
so a cube chain is exactly a list of cubes satisfying the folded predicate `IsCubeChain`, not a
list with stored junctions.
-/

open CategoryTheory Opposite

/-- The *folded* chain predicate: `IsCubeChain a cubes b` says the cubes run from `a` to `b`,
each cube's target being the next cube's source. -/
def IsCubeChain {K : PrecubicalSet} (a : K.cells 0) :
    List (Σ n : ℕ+, K.cells (n : ℕ)) → K.cells 0 → Prop
  | [],            b => a = b
  | ⟨_, c⟩ :: rest, b => K.vertexEnd false c = a ∧ IsCubeChain (K.vertexEnd true c) rest b

/-! ### Shape-indexed cube data

A cube list `List (Σ n : ℕ+, K.cells n)` *forgets* its shape, so the shape has to be recomputed as
`List.map (·.1)` — opaque to `.length`/`.get`, and a dimension transport at every use.  `Beads K d`
is the same data with the shape **given**; `toList`/`ofList` bridge the two, and that bridge is the
only place a transport is paid. -/

/-- Cube data of shape `d`: bead `i` is a cube of dimension `d.get i`. -/
abbrev Beads (K : PrecubicalSet) (d : List ℕ+) : Type := ∀ i : Fin d.length, K.cells (d.get i : ℕ)

namespace Beads

variable {K : PrecubicalSet}

/-- The beads after the first (`Fin.tail`, retyped so dot notation resolves). -/
def tail {n : ℕ+} {d : List ℕ+} (c : Beads K (n :: d)) : Beads K d := Fin.tail c

/-- The flat view: pair each bead with its dimension and forget the shape. -/
def toList {d : List ℕ+} (c : Beads K d) : List (Σ n : ℕ+, K.cells (n : ℕ)) :=
  match d, c with
  | [],     _ => []
  | _ :: _, c => ⟨_, c 0⟩ :: toList c.tail

@[simp] theorem toList_nil (c : Beads K []) : c.toList = [] := rfl

@[simp] theorem toList_cons {n : ℕ+} {d : List ℕ+} (c : Beads K (n :: d)) :
    c.toList = ⟨n, c 0⟩ :: c.tail.toList := rfl

@[simp] theorem map_fst_toList : ∀ {d : List ℕ+} (c : Beads K d), c.toList.map (·.1) = d
  | [],     _ => rfl
  | _ :: _, c => congrArg _ (map_fst_toList c.tail)

@[simp] theorem length_toList : ∀ {d : List ℕ+} (c : Beads K d), c.toList.length = d.length
  | [],     _ => rfl
  | _ :: _, c => congrArg _ (length_toList c.tail)

theorem toList_eq_ofFn : ∀ {d : List ℕ+} (c : Beads K d),
    c.toList = List.ofFn fun i => (⟨d.get i, c i⟩ : Σ n : ℕ+, K.cells (n : ℕ))
  | [],     _ => List.ofFn_zero.symm
  | n :: d, c => by
      rw [toList_cons, toList_eq_ofFn c.tail]
      exact (List.ofFn_succ (f := fun i : Fin (d.length + 1) =>
        (⟨(n :: d).get i, c i⟩ : Σ m : ℕ+, K.cells (m : ℕ)))).symm

/-- Reading the flat view back at an index, with the length transport threaded. -/
theorem toList_get {d : List ℕ+} (c : Beads K d) (i : Fin c.toList.length) :
    c.toList.get i = ⟨d.get (i.cast (length_toList c)), c (i.cast (length_toList c))⟩ := by
  rw [List.get_eq_getElem, List.getElem_of_eq (toList_eq_ofFn c), List.getElem_ofFn]; rfl

theorem toList_injective : ∀ {d : List ℕ+}, Function.Injective (toList (K := K) (d := d))
  | [],     _, _, _ => funext fun i => i.elim0
  | _ :: _, c, c', h => by
      rw [toList_cons, toList_cons, List.cons.injEq] at h
      exact funext (Fin.cases (by simpa using h.1) (congrFun (toList_injective h.2)))

/-- The shape-indexed view of a cube list, at its own shape. -/
def ofList : (l : List (Σ n : ℕ+, K.cells (n : ℕ))) → Beads K (l.map (·.1))
  | []     => fun i => i.elim0
  | c :: l => Fin.cons c.2 (ofList l)

@[simp] theorem toList_ofList : ∀ l : List (Σ n : ℕ+, K.cells (n : ℕ)), (ofList l).toList = l
  | []     => rfl
  | c :: l => congrArg (c :: ·) (toList_ofList l)

/-- The flat view determines both the shape and the beads. -/
theorem sigma_eq_of_toList_eq {d d' : List ℕ+} {c : Beads K d} {c' : Beads K d'}
    (h : c.toList = c'.toList) : (⟨d, c⟩ : Σ d : List ℕ+, Beads K d) = ⟨d', c'⟩ := by
  obtain rfl : d = d' := by rw [← map_fst_toList c, ← map_fst_toList c', h]
  exact congrArg _ (toList_injective h)

end Beads

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
    (hsrc : ∀ i : Fin cubes.length, K.toPsh.vertexEnd false (cubes.get i).2 = vtx i.castSucc)
    (htgt : ∀ i : Fin cubes.length, K.toPsh.vertexEnd true (cubes.get i).2 = vtx i.succ) :
    IsCubeChain (vtx 0) cubes (vtx (Fin.last cubes.length)) := by
  induction cubes with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨n, c⟩ := hd
      refine ⟨by simpa using hsrc 0, ?_⟩
      have hstart : K.toPsh.vertexEnd true c = vtx (Fin.succ 0) := htgt 0
      rw [hstart]
      have key := ih (vtx ∘ Fin.succ)
        (fun i => by rw [Function.comp_apply, Fin.succ_castSucc]; exact hsrc i.succ)
        (fun i => by rw [Function.comp_apply]; exact htgt i.succ)
      simp only [Function.comp_apply, Fin.succ_last] at key
      exact key

/-- **Push a cube forward** along a family of cell maps.  The one operation every "map a cube list
along a map" in the tree is an instance of; the family, not the presheaf morphism, is the right
argument, because the `IsCubeChain` transfer below uses naturality only at the vertices. -/
def cubePush {L W : PrecubicalSet} (u : ∀ n : ℕ, L.cells n → W.cells n)
    (c : Σ n : ℕ+, L.cells (n : ℕ)) : Σ n : ℕ+, W.cells (n : ℕ) := ⟨c.1, u _ c.2⟩

/-- A presheaf morphism, read as a family of cell maps. -/
abbrev cellsMap {L W : PrecubicalSet} (φ : L ⟶ W) (n : ℕ) : L.cells n → W.cells n := φ⟪n⟫

@[simp] theorem cubePush_fst {L W : PrecubicalSet} (u : ∀ n : ℕ, L.cells n → W.cells n)
    (c : Σ n : ℕ+, L.cells (n : ℕ)) : (cubePush u c).1 = c.1 := rfl

@[simp] theorem cubePush_snd {L W : PrecubicalSet} (u : ∀ n : ℕ, L.cells n → W.cells n)
    (c : Σ n : ℕ+, L.cells (n : ℕ)) : (cubePush u c).2 = u _ c.2 := rfl

/-- Push beads forward — `cubePush` at a fixed shape. -/
def Beads.push {L W : PrecubicalSet} (u : ∀ n : ℕ, L.cells n → W.cells n) {d : List ℕ+}
    (c : Beads L d) : Beads W d := fun i => u _ (c i)

@[simp] theorem Beads.toList_push {L W : PrecubicalSet} (u : ∀ n : ℕ, L.cells n → W.cells n) :
    ∀ {d : List ℕ+} (c : Beads L d), (c.push u).toList = c.toList.map (cubePush u)
  | [],     _ => rfl
  | _ :: _, c => congrArg _ (Beads.toList_push u c.tail)

/-- **A family of cell maps compatible with the extremal vertices preserves `IsCubeChain`.**
Naturality is used only at the two extremal vertices, so this covers families that are not maps of
presheaves — `Hbp`'s order-forgetting, say. -/
theorem isCubeChain_push {L W : PrecubicalSet} {u : ∀ n : ℕ, L.cells n → W.cells n}
    (hu : ∀ (ε : Bool) (n : ℕ) (c : L.cells n), u 0 (L.vertexEnd ε c) = W.vertexEnd ε (u n c)) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) {a b : L.cells 0},
    IsCubeChain a cubes b → IsCubeChain (u 0 a) (cubes.map (cubePush u)) (u 0 b)
  | [], _, _, h => congrArg _ h
  | ⟨n, c⟩ :: rest, _, _, h => by
      refine ⟨(hu false _ c).symm.trans (congrArg _ h.1), ?_⟩
      have := isCubeChain_push hu rest h.2
      rwa [hu true] at this

/-- …and reflects it, once injective on vertices. -/
theorem isCubeChain_of_push {L W : PrecubicalSet} {u : ∀ n : ℕ, L.cells n → W.cells n}
    (hu : ∀ (ε : Bool) (n : ℕ) (c : L.cells n), u 0 (L.vertexEnd ε c) = W.vertexEnd ε (u n c))
    (hinj : Function.Injective (u 0)) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) (a b : L.cells 0),
    IsCubeChain (u 0 a) (cubes.map (cubePush u)) (u 0 b) → IsCubeChain a cubes b
  | [], _, _, h => hinj h
  | ⟨n, c⟩ :: rest, _, b, h => by
      refine ⟨hinj ((hu false _ c).trans h.1), ?_⟩
      refine isCubeChain_of_push hu hinj rest (L.vertexEnd true c) b ?_
      rw [hu true]; exact h.2

/-- A presheaf morphism's cell maps are compatible with the extremal vertices. -/
theorem cellsMap_vertexEnd {L W : PrecubicalSet} (φ : L ⟶ W) (ε : Bool) (n : ℕ) (c : L.cells n) :
    cellsMap φ 0 (L.vertexEnd ε c) = W.vertexEnd ε (cellsMap φ n c) :=
  PrecubicalSet.map_vertexEnd ε φ c

/-- **A pointwise-injective map reflects `IsCubeChain`.**  Only injectivity on vertices is used;
the `ℕ`-indexed hypothesis is what call sites have to hand. -/
theorem isCubeChain_of_map_injective {L W : PrecubicalSet} (φ : L ⟶ W)
    (hinj : ∀ n : ℕ, Function.Injective (φ⟪n⟫)) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) (u v : L.cells 0),
    IsCubeChain (φ⟪0⟫ u) (cubes.map (cubePush (cellsMap φ))) (φ⟪0⟫ v) → IsCubeChain u cubes v :=
  isCubeChain_of_push (u := cellsMap φ) (cellsMap_vertexEnd φ) (hinj 0)

/-- **A map preserves `IsCubeChain`** — the converse direction, needing no injectivity. -/
theorem isCubeChain_map {L W : PrecubicalSet} (φ : L ⟶ W) :
    ∀ (cubes : List (Σ n : ℕ+, L.cells (n : ℕ))) {u v : L.cells 0},
    IsCubeChain u cubes v →
      IsCubeChain (φ⟪0⟫ u) (cubes.map (cubePush (cellsMap φ))) (φ⟪0⟫ v) :=
  isCubeChain_push (u := cellsMap φ) (cellsMap_vertexEnd φ)

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

/-- **`IsCubeChain → CubeChain`**, the inverse of `isCubeChain`. -/
def ofIsCubeChain (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (h : IsCubeChain K.init cubes K.final) : CubeChain K := ⟨cubes, h⟩

/-- A `CubeChain` is determined by its cubes (the chain condition is a `Prop`). -/
theorem eq_of_cubes {C₁ C₂ : CubeChain K} (hc : C₁.cubes = C₂.cubes) : C₁ = C₂ :=
  Subtype.ext hc

end CubeChain

namespace CubeChains

/-- An **all-edges chain** of `K`: a cube chain every one of whose cubes is an edge.  This is the
geometric shape of a run — `Run.equivEdgeChain`. -/
def EdgeChain (K : BPSet) : Type := {C : CubeChain K // ∀ c ∈ C.cubes, (c.1 : ℕ) = 1}

end CubeChains
