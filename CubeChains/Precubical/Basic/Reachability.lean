import CubeChains.Precubical.Basic.Altitude

/-!
# Precubical/Basic/Reachability

`PrecubicalSet`-level **reachability** of cells: the reflexive-transitive closure of the one-step
face relation `Face X`, its `ε`-oriented reading `ReachesEnd`, and the fact that every cell is
`ε`-related to its `vertexEnd ε`, by peeling cofaces.
-/

open CategoryTheory Opposite Relation StdCube

namespace PrecubicalSet

/-- The total type of cells of a precubical set across all dimensions. -/
abbrev TotalCell (X : PrecubicalSet) : Type := Σ n, X.cells n

/-- The one-step face relation: a *source* face `faceMap false i c` sits below its cell `c`, and
`c` sits below each of its *target* faces. -/
inductive Face (X : PrecubicalSet) : X.TotalCell → X.TotalCell → Prop
  | source {n} (i : Fin (n + 1)) (c : X.cells (n + 1)) :
      Face X ⟨n, X.faceMap false i c⟩ ⟨n + 1, c⟩
  | target {n} (i : Fin (n + 1)) (c : X.cells (n + 1)) :
      Face X ⟨n + 1, c⟩ ⟨n, X.faceMap true i c⟩

/-- **Reachability**: cells related by a chain of faces. -/
abbrev Reaches (X : PrecubicalSet) : X.TotalCell → X.TotalCell → Prop :=
  Relation.ReflTransGen (Face X)

/-- `Reaches` read in the direction picked by `ε`: `true` runs along target faces, `false`
backwards along source faces.  Both endpoint statements are one statement in `ε`. -/
def ReachesEnd (X : PrecubicalSet) (ε : Bool) (a b : X.TotalCell) : Prop :=
  cond ε (Reaches X a b) (Reaches X b a)

namespace ReachesEnd

variable {X : PrecubicalSet}

@[refl]
theorem refl (ε : Bool) (x : X.TotalCell) : ReachesEnd X ε x x := by
  cases ε <;> exact ReflTransGen.refl

theorem trans {ε : Bool} {x y z : X.TotalCell} (hxy : ReachesEnd X ε x y)
    (hyz : ReachesEnd X ε y z) : ReachesEnd X ε x z := by
  cases ε
  exacts [ReflTransGen.trans hyz hxy, ReflTransGen.trans hxy hyz]

/-- The two face constructors, said once: a cell is `ε`-related to each of its `ε`-faces. -/
theorem face (ε : Bool) {n : ℕ} (i : Fin (n + 1)) (c : X.cells (n + 1)) :
    ReachesEnd X ε ⟨n + 1, c⟩ ⟨n, X.faceMap ε i c⟩ := by
  cases ε
  exacts [ReflTransGen.single (Face.source i c), ReflTransGen.single (Face.target i c)]

end ReachesEnd

/-! ### Cell ↔ vertex reachability

The carried invariant is that every *fixed* coordinate of the classifying `□ᴺ`-cell takes a
single boolean value `ε`, so each peeled coface is the `ε`-face and the reachability direction
is uniform. -/

namespace StdCube

/-- A `□ᴺ`-cell whose every fixed (non-free) coordinate is `ε`. -/
def AllFixed {N k : ℕ} (a : Cell N k) (ε : Bool) : Prop :=
  ∀ j : Fin N, a.val j ≠ none → a.val j = some ε

theorem allFixed_constVertex (N : ℕ) (ε : Bool) :
    AllFixed (constVertex N ε) ε := by
  intro j _; rfl

theorem minFixedVal_of_allFixed {N k : ℕ} (a : Cell N k) (ε : Bool)
    (ha : AllFixed a ε) (h : k < N) : minFixedVal a h = ε := by
  have hne : a.val (minFixed a h) ≠ none := minFixed_val_ne_none a h
  have heq := ha _ hne
  rw [minFixed_val_eq a h] at heq
  exact Option.some.inj heq

theorem allFixed_freeMin {N k : ℕ} (a : Cell N k) (ε : Bool)
    (ha : AllFixed a ε) (h : k < N) : AllFixed (freeMin a h) ε := by
  intro j hj
  rw [freeMin_val] at hj ⊢
  by_cases hjm : j = minFixed a h
  · subst hjm; rw [Function.update_self] at hj; exact absurd rfl hj
  · rw [Function.update_of_ne hjm] at hj ⊢; exact ha j hj

end StdCube

open StdCube

variable {X : PrecubicalSet}

/-- **Peeling reachability.**  If every fixed coordinate of `c' : □ᴺ-cell` is `ε`, then `x`
is `ε`-related to the iterated face `X.map (Box.ofSign c').op x`: each coordinate peeled
off by `Cell.peelRec` contributes one `ε`-face. -/
theorem reaches_ofSign (ε : Bool) {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : Cell N k), AllFixed c' ε →
      ReachesEnd X ε ⟨N, x⟩ ⟨k, X.map (Box.ofSign c').op x⟩ := by
  intro k c'
  induction k, c' using Cell.peelRec with
  | top c' => intro _; rw [X.map_ofSign_top x c']
  | step k c' h ih =>
      intro hc'
      refine ReachesEnd.trans (ih (allFixed_freeMin c' ε hc' h)) ?_
      rw [X.map_ofSign_peel x c' h, minFixedVal_of_allFixed c' ε hc' h]
      exact ReachesEnd.face ε (minFixedIdx c' h) (X.map (Box.ofSign (freeMin c' h)).op x)

/-- Every cell is `ε`-related to its `ε`-extremal vertex. -/
theorem reaches_vertexEnd (ε : Bool) {n : ℕ} (c : X.cells n) :
    ReachesEnd X ε ⟨n, c⟩ ⟨0, X.vertexEnd ε c⟩ :=
  reaches_ofSign ε c (constVertex n ε) (allFixed_constVertex n ε)

/-! ### Functoriality

A precubical map `f : X ⟶ Y` carries a face to a face (naturality through cofaces), and
`ReflTransGen.lift` does the rest. -/

/-- The action of a precubical map on a total cell. -/
def mapCell {X Y : PrecubicalSet} (f : X ⟶ Y) (x : X.TotalCell) : Y.TotalCell :=
  ⟨x.1, f⟪x.1⟫ x.2⟩

/-- A precubical map carries `faceMap` to `faceMap` (naturality through the coface). -/
theorem map_faceMap {X Y : PrecubicalSet} (f : X ⟶ Y) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : X.cells (n + 1)) :
    f⟪n⟫ (X.faceMap ε i c)
      = Y.faceMap ε i (f⟪n + 1⟫ c) :=
  NatTrans.naturality_apply f (coface ε i).op c

/-- A precubical map carries a face to a face. -/
theorem Face.map {X Y : PrecubicalSet} (f : X ⟶ Y) {x y : X.TotalCell} (h : Face X x y) :
    Face Y (mapCell f x) (mapCell f y) := by
  cases h with
  | source i c =>
      change Face Y ⟨_, f⟪_⟫ (X.faceMap false i c)⟩ ⟨_, _⟩
      rw [map_faceMap f false i c]
      exact Face.source i (f⟪_⟫ c)
  | target i c =>
      change Face Y ⟨_, _⟩ ⟨_, f⟪_⟫ (X.faceMap true i c)⟩
      rw [map_faceMap f true i c]
      exact Face.target i (f⟪_⟫ c)

/-- **Functoriality of reachability.** -/
theorem Reaches.map {X Y : PrecubicalSet} (f : X ⟶ Y) {x y : X.TotalCell}
    (h : Reaches X x y) : Reaches Y (mapCell f x) (mapCell f y) :=
  h.lift (mapCell f) fun _ _ hab => hab.map f

/-- Vertex-reachability: the relation on `0`-cells `v ↦ w` whenever `⟨0,v⟩` reaches
`⟨0,w⟩`. -/
def VertexReaches (X : PrecubicalSet) (v w : X.cells 0) : Prop :=
  Reaches X ⟨0, v⟩ ⟨0, w⟩

end PrecubicalSet
