import CubeChains.Wedge
import CubeChains.Operations.WeakEquiv
import CubeChains.Operations.GroupoidTarget
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# The precubical cube-chain functor `ChP : PrecubicalSet ⥤ Cat` and its operations

This instantiates the generic weak-equivalence machinery (`Operations.Homotopical`,
`Operations.Span`) on the topos `PrecubicalSet = Boxᵒᵖ ⥤ Type`.

The chain category here is the **basepoint-free** variant of `Ch`: a chain is a
dimension sequence with a *plain precubical map* `□^∨(dims) ⟶ K`, and morphisms are
wedge maps over `K` that need not preserve basepoints.  Working over `PrecubicalSet`
rather than `BPSet` is deliberate — it has many more morphisms, which is what makes
the search for interesting operations `F` rich.

`Weq := Homotopical ChP` is then the `MorphismProperty PrecubicalSet` of operations
(maps `ChP` sends to an equivalence of chain categories); it inherits the full
weak-equivalence algebra (contains identities & isos, multiplicative,
two-out-of-three) from the generic layer.  Operations presented by spans are
`Operations.Span ChP`.
-/

open CategoryTheory Opposite

namespace Operations.Precubical

/-- A **chain** in a precubical set `K`: a dimension sequence with a precubical map of
the serial wedge `□^∨(dims)` into `K`.  Basepoints are *not* required to be preserved
(more morphisms than the bi-pointed `ChainCat.Obj`). -/
structure ChainObj (K : PrecubicalSet) where
  /-- The dimension sequence. -/
  dims : List ℕ+
  /-- The classifying precubical map `□^∨(dims) ⟶ K`. -/
  map : (BPSet.serialWedge dims).toPsh ⟶ K

/-- A morphism of chains: a precubical map of serial wedges commuting over `K`. -/
@[ext]
structure ChainHom {K : PrecubicalSet} (a b : ChainObj K) where
  /-- The underlying wedge map. -/
  φ : (BPSet.serialWedge a.dims).toPsh ⟶ (BPSet.serialWedge b.dims).toPsh
  /-- The triangle over `K` commutes. -/
  w : φ ≫ b.map = a.map

noncomputable instance (K : PrecubicalSet) : Category (ChainObj K) where
  Hom a b := ChainHom a b
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.φ ≫ g.φ, by rw [Category.assoc, g.w, f.w]⟩
  id_comp f := ChainHom.ext (Category.id_comp _)
  comp_id f := ChainHom.ext (Category.comp_id _)
  assoc f g h := ChainHom.ext (Category.assoc _ _ _)

@[simp] theorem id_φ {K : PrecubicalSet} (a : ChainObj K) :
    ChainHom.φ (𝟙 a) = 𝟙 _ := rfl

@[simp] theorem comp_φ {K : PrecubicalSet} {a b c : ChainObj K} (f : a ⟶ b) (g : b ⟶ c) :
    ChainHom.φ (f ≫ g) = ChainHom.φ f ≫ ChainHom.φ g := rfl

@[ext] theorem hom_ext' {K : PrecubicalSet} {a b : ChainObj K} {f g : a ⟶ b}
    (h : ChainHom.φ f = ChainHom.φ g) : f = g := ChainHom.ext h

/-- Post-composition functor `ChP K ⥤ ChP L` induced by `f : K ⟶ L`. -/
noncomputable def pushforward {K L : PrecubicalSet} (f : K ⟶ L) : ChainObj K ⥤ ChainObj L where
  obj a := ⟨a.dims, a.map ≫ f⟩
  map {a b} g := ⟨g.φ, by rw [← Category.assoc, g.w]⟩
  map_id a := rfl
  map_comp _ _ := rfl

theorem pushforward_id (K : PrecubicalSet) : pushforward (𝟙 K) = 𝟭 (ChainObj K) := rfl

theorem pushforward_comp {K L M : PrecubicalSet} (f : K ⟶ L) (g : L ⟶ M) :
    pushforward (f ≫ g) = pushforward f ⋙ pushforward g := rfl

/-- The **precubical cube-chain functor** `ChP : PrecubicalSet ⥤ Cat`: `K ↦ ChP K`,
`f ↦` post-composition.  The homotopy functor against which operations are measured. -/
noncomputable def ChP : PrecubicalSet ⥤ Cat where
  obj K := Cat.of (ChainObj K)
  map f := (pushforward f).toCatHom
  map_id K := Cat.ext (pushforward_id K)
  map_comp f g := Cat.ext (pushforward_comp f g)

/-- **Operations on precubical sets**: maps `ChP` sends to an equivalence of chain
categories.  `abbrev` so the weak-equivalence algebra from `Operations.Homotopical`
fires by instance resolution. -/
abbrev Weq : MorphismProperty PrecubicalSet := Homotopical ChP

/-- Operations form a multiplicative class with two-out-of-three. -/
example : Weq.IsMultiplicative := inferInstance
example : Weq.HasTwoOutOfThreeProperty := inferInstance

/-- Identities and isomorphisms (relabelings) are operations. -/
example (K : PrecubicalSet) : Weq (𝟙 K) := (Homotopical ChP).id_mem K
example {K L : PrecubicalSet} (e : K ≅ L) : Weq e.hom := homotopical_of_isIso ChP e.hom

/-- An operation `K ⤳ L` is presented by a span of weak equivalences, inducing an
equivalence of chain categories `ChP K ≌ ChP L` (design condition (1)). -/
noncomputable example {K L : PrecubicalSet} (s : Operations.Span ChP K L) :
    (ChP.obj K) ≌ (ChP.obj L) := s.equivalence

/-! ## The weakened class of operations

`Weq` (equivalence of chain categories) is too strict: e.g. including a boundary path
`E = □¹∨□¹` into the square `K = □²` is a directed-homotopy equivalence of path spaces
but **not** in `Weq` — `ChP E` has no `[2]`-chain while `ChP K` does, and `pushforward`
preserves dimension sequences, so the square is never in the essential image.

`WeqHo` measures operations against the homotopy invariant **π₀** (`Cat.connectedComponents`)
instead: `f ∈ WeqHo` iff it induces a *bijection on homotopy classes of d-paths*
`π₀(ChP K) ≃ π₀(ChP L)`.  This is strictly weaker (`Weq ⊆ WeqHo`, below) and the right
home for collapses/fillers like the square example.  When mathlib gains a Thomason
model structure, swap `Cat.connectedComponents` for the nerve invariant — no other change. -/
abbrev WeqHo : MorphismProperty PrecubicalSet :=
  Operations.InvertedBy (ChP ⋙ Cat.connectedComponents)

/-- `WeqHo` is also a multiplicative two-out-of-three class (inherited). -/
example : WeqHo.IsMultiplicative := inferInstance
example : WeqHo.HasTwoOutOfThreeProperty := inferInstance

/-- **The weakening is a genuine enlargement**: every (strong) operation is a
π₀-operation. -/
theorem weq_le_weqHo {K L : PrecubicalSet} {f : K ⟶ L} (hf : Weq f) : WeqHo f :=
  Operations.homotopical_le_connectedComponents hf

/-- A weak operation `K ⤳ L` induces the bijection of homotopy classes
`π₀(ChP K) ≃ π₀(ChP L)` — the surviving content of condition (1) under the weaker
invariant (e.g. the square example lands here, not in `Weq`). -/
noncomputable example {K L : PrecubicalSet}
    (s : Operations.WeakSpan (ChP ⋙ Cat.connectedComponents) K L) :
    ConnectedComponents (ChP.obj K) ≃ ConnectedComponents (ChP.obj L) :=
  s.homotopyClassEquiv

/-! ## The middle rung: groupoid-reflection weak equivalences

`WeqGrpd` measures a leg against the **groupoid reflection** `M = Ch(K)[Ch(K)⁻¹]` — the
Goldilocks invariant for lifting zigzags to `M` (see `Operations.GroupoidTarget`).  It
sits strictly between `Weq` (equivalence of chain categories) and `WeqHo` (π₀): the
reflection is coarser than `Cat`-equivalence yet finer than `π₀`. -/
def WeqGrpd : MorphismProperty PrecubicalSet :=
  fun _ _ f => (FreeGroupoid.map (ChP.map f).toFunctor).IsEquivalence

/-- **Tower top, concretely**: every (strong) operation is a groupoid-reflection weak
equivalence (`Weq ⊆ WeqGrpd`), by `freeGroupoid_map_isEquivalence`. -/
theorem weq_le_weqGrpd {K L : PrecubicalSet} {f : K ⟶ L} (hf : Weq f) : WeqGrpd f :=
  haveI : (ChP.map f).toFunctor.IsEquivalence := hf
  Operations.freeGroupoid_map_isEquivalence _

end Operations.Precubical
