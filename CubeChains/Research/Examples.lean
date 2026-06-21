import CubeChains.Research.Conjectures

/-!
# Research/Examples

Type-level sanity checks (ClaudeSetup.md §8).
These exercise the API at the type level for the small cubes `□¹`, `□²` and the
dimension sequences `[2]`, `[1,1]` relevant to `Ch (□²)`.

**Two honest caveats** (see `DESIGN.md`):

* The "axis swap" of `□²` is **not** an automorphism in this *symmetry-free*
  precubical model: a coordinate swap does not commute with the count-indexed
  faces at the *same* index (it intertwines `face ε 0` with `face ε 1`).  This is
  exactly the absence of symmetries demanded by ClaudeSetup.md §9, so the §8
  axis-swap check does not apply here; `Aut (□ⁿ)` is correspondingly rigid.
* Exhibiting the *specific* chains of dimension sequence `[2]` and `[1,1]` and the
  morphism `[1,1] ⟶ [2]` as concrete data requires the map↔chain equivalence
  (the deferred cube Yoneda lemma), so those concrete witnesses are left for when
  `cubeRepr`/the equivalence are discharged.  The objects and the ambient
  category, however, are all available, as checked below.

**Layer:** Research.  **Imports:** `Research/Conjectures`.
-/

open CategoryTheory

namespace Examples

/-- The interval `□¹` and the square `□²` as bi-pointed precubical sets. -/
noncomputable example : BPSet := BPSet.cube 1
noncomputable example : BPSet := BPSet.cube 2

/-- The serial wedges for the dimension sequences `[2]` and `[1,1]`. -/
noncomputable example : BPSet := BPSet.serialWedge [2]
noncomputable example : BPSet := BPSet.serialWedge [1, 1]

/-- `Aut (□²)` is a group, and the lift to `Ch (□²)` is a group homomorphism. -/
noncomputable example : Group (Aut (BPSet.cube 2)) := inferInstance
noncomputable example : Aut (BPSet.cube 2) →* Aut (Ch.obj (BPSet.cube 2)) :=
  Aut.liftToCh (BPSet.cube 2)

/-- `Ch (□¹)` is a (large) category whose objects are the chains in `□¹`. -/
noncomputable example : Category (ChainCat.Obj (BPSet.cube 1)) := inferInstance

/-- The three side conditions are predicates on any bi-pointed precubical set. -/
example (K : BPSet) : Prop := K.NonSelfLinked
example (K : BPSet) : Prop := K.AdmitsAltitude
example (K : BPSet) : Prop := K.Accessible

/-- Orientation-preserving is a predicate on automorphisms of `Ch K`. -/
example (K : BPSet) (Φ : Aut (Ch.obj K)) : Prop := OrientationPreserving Φ

end Examples
