import CubeChains.Foundations.Altitude

/-!
# Foundations/Reachability

`PrecubicalSet`-level **reachability** of cells and the **connected components**
(`π₀`) of vertices.

This generalizes the bi-pointed `BPSet.Reach` (`Foundations/Altitude.lean`) to an
arbitrary precubical set `X : PrecubicalSet`, working with `X.cells`/`X.faceMap`:

* `PrecubicalSet.Reaches X` — the inductive one-step reachability relation
  (`source`/`target` faces, closed under `refl`+`trans`), reflexive and transitive
  (`Reaches.is_refl`/`Reaches.is_trans`, `Trans` instance), bundled as a `Preorder`
  (`reachesPreorder`).
* Cell↔vertex lemmas: every cell is reached *from* its initial vertex
  (`reaches_vertex₀`) and *reaches* its terminal vertex (`reaches_vertex₁`),
  proved by peeling cofaces (`canonicalMap_peel`) one source/target face at a time,
  mirroring `alt_map_eq`.
* Functoriality: a precubical map preserves reachability (`Reaches.map`).
* `PrecubicalSet.π₀ X` — the quotient of `X.cells 0` by the equivalence relation
  generated (`Relation.EqvGen`) by vertex-reachability, with `π₀.mk`, the induced
  `π₀.map`, `π₀.map_id`/`π₀.map_comp`, and `π₀.mapEquiv` turning an isomorphism of
  precubical sets into a bijection of `π₀`'s (the invariant downstream cobordism
  milestones use to obstruct invertibility of a "merge").

-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-- The total type of cells of a precubical set across all dimensions. -/
abbrev TotalCell (X : PrecubicalSet) : Type := Σ n, X.cells n

/-- The one-step reachability relation on the cells of a precubical set `X`, in all
dimensions: a *source* face `faceMap false i c` reaches its cell `c`, a cell `c`
reaches each of its *target* faces `faceMap true i c`, closed under reflexivity and
transitivity.  The `PrecubicalSet`-level generalization of `BPSet.Reach`. -/
inductive Reaches (X : PrecubicalSet) : X.TotalCell → X.TotalCell → Prop
  | refl (x : X.TotalCell) : Reaches X x x
  | source {n} (i : Fin (n + 1)) (c : X.cells (n + 1)) :
      Reaches X ⟨n, X.faceMap false i c⟩ ⟨n + 1, c⟩
  | target {n} (i : Fin (n + 1)) (c : X.cells (n + 1)) :
      Reaches X ⟨n + 1, c⟩ ⟨n, X.faceMap true i c⟩
  | trans {x y z} : Reaches X x y → Reaches X y z → Reaches X x z

namespace Reaches

variable {X : PrecubicalSet}

@[refl]
theorem is_refl (x : X.TotalCell) : Reaches X x x := Reaches.refl x

theorem is_trans {x y z : X.TotalCell} (hxy : Reaches X x y) (hyz : Reaches X y z) :
    Reaches X x z := Reaches.trans hxy hyz

instance : Trans (Reaches X) (Reaches X) (Reaches X) where
  trans := Reaches.trans

end Reaches

/-- Reachability as a `Preorder` on the total cell type. -/
@[reducible]
def reachesPreorder (X : PrecubicalSet) : Preorder X.TotalCell where
  le := Reaches X
  le_refl := Reaches.refl
  le_trans _ _ _ := Reaches.trans

/-! ### Cell ↔ vertex reachability

We relate the iterated-face vertices `vertex₀`/`vertex₁` to the inductive
`source`/`target` steps by peeling cofaces (`StdCube.canonicalMap_peel`), exactly
as `alt_map_eq` peels them for the altitude.  The carried invariant is that every
*fixed* coordinate of the classifying `□ᴺ`-cell takes a single boolean value `ε`,
so each peeled coface is the `ε`-face and the reachability direction is uniform. -/

namespace StdCube

open StdCube

/-- A `□ᴺ`-cell whose every fixed (non-free) coordinate is `ε`. -/
def AllFixed {N k : ℕ} (a : StdCube.cells N k) (ε : Bool) : Prop :=
  ∀ j : Fin N, a.val j ≠ none → a.val j = some ε

theorem allFixed_constVertex (N : ℕ) (ε : Bool) :
    AllFixed (StdCube.constVertex N ε) ε := by
  intro j _; rfl

theorem minFixedVal_of_allFixed {N k : ℕ} (a : StdCube.cells N k) (ε : Bool)
    (ha : AllFixed a ε) (h : k < N) : StdCube.minFixedVal a h = ε := by
  have hne : a.val (StdCube.minFixed a h) ≠ none := StdCube.minFixed_val_ne_none a h
  have heq := ha _ hne
  rw [StdCube.minFixed_val_eq a h] at heq
  exact Option.some.inj heq

theorem allFixed_freeMin {N k : ℕ} (a : StdCube.cells N k) (ε : Bool)
    (ha : AllFixed a ε) (h : k < N) : AllFixed (StdCube.freeMin a h) ε := by
  intro j hj
  rw [StdCube.freeMin_val] at hj ⊢
  by_cases hjm : j = StdCube.minFixed a h
  · subst hjm; rw [Function.update_self] at hj; exact absurd rfl hj
  · rw [Function.update_of_ne hjm] at hj ⊢; exact ha j hj

end StdCube

variable {X : PrecubicalSet}

/-- **Source-peeling reachability.**  If every fixed coordinate of `c' : □ᴺ-cell` is
`false`, then the iterated source face `X.map (canonicalMap c').op x` is reached
from `x`.  Strong induction on `N - k`, peeling the smallest fixed coordinate via
`canonicalMap_peel` (each step a `source` face). -/
theorem reaches_canonicalMap_false {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : StdCube.cells N k), StdCube.AllFixed c' false →
      Reaches X ⟨k, X.map (StdCube.canonicalMap c').op x⟩ ⟨N, x⟩ := by
  intro k c'
  induction hd : N - k using Nat.strong_induction_on generalizing k c' with
  | _ d ih =>
    intro hc'
    rcases Nat.lt_or_ge k N with h | h
    · have hval : StdCube.minFixedVal c' h = false :=
        StdCube.minFixedVal_of_allFixed c' false hc' h
      have e1 : X.map (StdCube.canonicalMap c').op x
          = X.map (PrecubicalSet.coface (StdCube.minFixedVal c' h)
              (StdCube.minFixedIdx c' h) ≫ StdCube.canonicalMap (StdCube.freeMin c' h)).op x :=
        congrArg (fun m => X.map (Quiver.Hom.op m) x) (StdCube.canonicalMap_peel c' h)
      have hstep : X.map (StdCube.canonicalMap c').op x
          = X.faceMap (StdCube.minFixedVal c' h) (StdCube.minFixedIdx c' h)
            (X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x) := by
        rw [e1, op_comp, Functor.map_comp]; rfl
      have hsrc : Reaches X
          ⟨k, X.map (StdCube.canonicalMap c').op x⟩
          ⟨k + 1, X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x⟩ := by
        rw [hstep, hval]
        exact Reaches.source (StdCube.minFixedIdx c' h)
          (X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x)
      exact hsrc.trans
        (ih (N - (k + 1)) (by omega) (StdCube.freeMin c' h) rfl
          (StdCube.allFixed_freeMin c' false hc' h))
    · have hkN : k = N := le_antisymm (StdCube.cells_card_le c') h
      subst hkN
      rw [StdCube.eq_topCell c']
      erw [StdCube.canonicalMap_topCell, op_id, X.map_id]
      exact Reaches.refl _

/-- **Target-peeling reachability.**  If every fixed coordinate of `c' : □ᴺ-cell` is
`true`, then `x` reaches the iterated target face `X.map (canonicalMap c').op x`. -/
theorem reaches_canonicalMap_true {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : StdCube.cells N k), StdCube.AllFixed c' true →
      Reaches X ⟨N, x⟩ ⟨k, X.map (StdCube.canonicalMap c').op x⟩ := by
  intro k c'
  induction hd : N - k using Nat.strong_induction_on generalizing k c' with
  | _ d ih =>
    intro hc'
    rcases Nat.lt_or_ge k N with h | h
    · have hval : StdCube.minFixedVal c' h = true :=
        StdCube.minFixedVal_of_allFixed c' true hc' h
      have e1 : X.map (StdCube.canonicalMap c').op x
          = X.map (PrecubicalSet.coface (StdCube.minFixedVal c' h)
              (StdCube.minFixedIdx c' h) ≫ StdCube.canonicalMap (StdCube.freeMin c' h)).op x :=
        congrArg (fun m => X.map (Quiver.Hom.op m) x) (StdCube.canonicalMap_peel c' h)
      have hstep : X.map (StdCube.canonicalMap c').op x
          = X.faceMap (StdCube.minFixedVal c' h) (StdCube.minFixedIdx c' h)
            (X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x) := by
        rw [e1, op_comp, Functor.map_comp]; rfl
      have htgt : Reaches X
          ⟨k + 1, X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x⟩
          ⟨k, X.map (StdCube.canonicalMap c').op x⟩ := by
        rw [hstep, hval]
        exact Reaches.target (StdCube.minFixedIdx c' h)
          (X.map (StdCube.canonicalMap (StdCube.freeMin c' h)).op x)
      exact (ih (N - (k + 1)) (by omega) (StdCube.freeMin c' h) rfl
        (StdCube.allFixed_freeMin c' true hc' h)).trans htgt
    · have hkN : k = N := le_antisymm (StdCube.cells_card_le c') h
      subst hkN
      rw [StdCube.eq_topCell c']
      erw [StdCube.canonicalMap_topCell, op_id, X.map_id]
      exact Reaches.refl _

/-- Every cell is reached **from** its initial (source) vertex `vertex₀`. -/
theorem reaches_vertex₀ {n : ℕ} (c : X.cells n) :
    Reaches X ⟨0, X.vertex₀ c⟩ ⟨n, c⟩ := by
  have h := reaches_canonicalMap_false c (StdCube.constVertex n false)
    (StdCube.allFixed_constVertex n false)
  exact h

/-- Every cell **reaches** its terminal (target) vertex `vertex₁`. -/
theorem reaches_vertex₁ {n : ℕ} (c : X.cells n) :
    Reaches X ⟨n, c⟩ ⟨0, X.vertex₁ c⟩ := by
  have h := reaches_canonicalMap_true c (StdCube.constVertex n true)
    (StdCube.allFixed_constVertex n true)
  exact h

/-! ### Functoriality

A precubical map `f : X ⟶ Y` carries reachability forward, by induction on the
witness: it commutes with face maps (naturality through cofaces). -/

/-- The action of a precubical map on a total cell. -/
def mapCell {X Y : PrecubicalSet} (f : X ⟶ Y) (x : X.TotalCell) : Y.TotalCell :=
  ⟨x.1, f.app (op (Box.ob x.1)) x.2⟩

/-- A precubical map carries `faceMap` to `faceMap` (naturality through the coface). -/
theorem map_faceMap {X Y : PrecubicalSet} (f : X ⟶ Y) (ε : Bool) {n : ℕ}
    (i : Fin (n + 1)) (c : X.cells (n + 1)) :
    f.app (op (Box.ob n)) (X.faceMap ε i c)
      = Y.faceMap ε i (f.app (op (Box.ob (n + 1))) c) :=
  NatTrans.naturality_apply f (coface ε i).op c

/-- **Functoriality of reachability.**  A precubical map `f : X ⟶ Y` preserves
reachability. -/
theorem Reaches.map {X Y : PrecubicalSet} (f : X ⟶ Y) {x y : X.TotalCell}
    (h : Reaches X x y) : Reaches Y (mapCell f x) (mapCell f y) := by
  induction h with
  | refl x => exact Reaches.refl _
  | source i c =>
      change Reaches Y ⟨_, f.app (op (Box.ob _)) (X.faceMap false i c)⟩ ⟨_, _⟩
      rw [map_faceMap f false i c]
      exact Reaches.source i (f.app (op (Box.ob _)) c)
  | target i c =>
      change Reaches Y ⟨_, _⟩ ⟨_, f.app (op (Box.ob _)) (X.faceMap true i c)⟩
      rw [map_faceMap f true i c]
      exact Reaches.target i (f.app (op (Box.ob _)) c)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Connected components of vertices (π₀)

`π₀ X` is the quotient of the `0`-cells (vertices) by the equivalence relation
*generated* by vertex-reachability.  A precubical map induces a map of `π₀`'s, an
isomorphism a bijection. -/

/-- Vertex-reachability: the relation on `0`-cells `v ↦ w` whenever `⟨0,v⟩` reaches
`⟨0,w⟩`. -/
def VertexReaches (X : PrecubicalSet) (v w : X.cells 0) : Prop :=
  Reaches X ⟨0, v⟩ ⟨0, w⟩

/-- The equivalence relation on vertices generated by vertex-reachability. -/
def vertexSetoid (X : PrecubicalSet) : Setoid (X.cells 0) where
  r v w := Relation.EqvGen (VertexReaches X) v w
  iseqv :=
    { refl := fun v => Relation.EqvGen.refl v
      symm := fun h => Relation.EqvGen.symm _ _ h
      trans := fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂ }

/-- **`π₀` of a precubical set**: connected components of its vertices, the quotient
of `0`-cells by the equivalence relation generated by reachability. -/
def π₀ (X : PrecubicalSet) : Type := Quotient X.vertexSetoid

namespace π₀

/-- The class of a vertex in `π₀`. -/
def mk {X : PrecubicalSet} (v : X.cells 0) : π₀ X := Quotient.mk X.vertexSetoid v

@[simp]
theorem mk_surjective {X : PrecubicalSet} : Function.Surjective (π₀.mk (X := X)) :=
  Quotient.mk_surjective

/-- Reachable vertices have equal `π₀` classes. -/
theorem sound {X : PrecubicalSet} {v w : X.cells 0} (h : Reaches X ⟨0, v⟩ ⟨0, w⟩) :
    π₀.mk v = π₀.mk w :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

/-- A precubical map respects the generating vertex-reachability relation, hence the
generated equivalence. -/
theorem map_eqvGen {X Y : PrecubicalSet} (f : X ⟶ Y) {v w : X.cells 0}
    (h : Relation.EqvGen (VertexReaches X) v w) :
    Relation.EqvGen (VertexReaches Y)
      (f.app (op (Box.ob 0)) v) (f.app (op (Box.ob 0)) w) := by
  induction h with
  | rel a b hab =>
      refine Relation.EqvGen.rel _ _ ?_
      have := (hab : Reaches X ⟨0, a⟩ ⟨0, b⟩).map f
      exact this
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The map on `π₀` induced by a precubical map. -/
def map {X Y : PrecubicalSet} (f : X ⟶ Y) : π₀ X → π₀ Y :=
  Quotient.lift (fun v => π₀.mk (f.app (op (Box.ob 0)) v))
    (fun _ _ h => Quotient.sound (map_eqvGen f h))

@[simp]
theorem map_mk {X Y : PrecubicalSet} (f : X ⟶ Y) (v : X.cells 0) :
    π₀.map f (π₀.mk v) = π₀.mk (f.app (op (Box.ob 0)) v) := rfl

@[simp]
theorem map_id (X : PrecubicalSet) : π₀.map (𝟙 X) = id := by
  funext p
  obtain ⟨v, rfl⟩ := π₀.mk_surjective p
  rfl

theorem map_comp {X Y Z : PrecubicalSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
    π₀.map (f ≫ g) = π₀.map g ∘ π₀.map f := by
  funext p
  obtain ⟨v, rfl⟩ := π₀.mk_surjective p
  rfl

/-- An **isomorphism** of precubical sets induces a **bijection** of `π₀`'s. -/
def mapEquiv {X Y : PrecubicalSet} (e : X ≅ Y) : π₀ X ≃ π₀ Y where
  toFun := π₀.map e.hom
  invFun := π₀.map e.inv
  left_inv p := by
    rw [← Function.comp_apply (f := π₀.map e.inv), ← map_comp, e.hom_inv_id,
      map_id, id_eq]
  right_inv p := by
    rw [← Function.comp_apply (f := π₀.map e.hom), ← map_comp, e.inv_hom_id,
      map_id, id_eq]

end π₀

end PrecubicalSet
