import CubeChains.Chains.Category

/-!
# Endpoint-indexed cube-chain categories `Ch'`

`ChainCat.Obj K` is the cube-chain category of a **bi-pointed** precubical set
`K : BPSet`: its objects are the full chains `K.init → K.final`.  Since a `BPSet`
is just a presheaf together with two chosen `0`-cells, any precubical set can be
re-basepointed at *arbitrary* vertices, and the entire `ChainCat` API then applies
verbatim.

This file packages that re-basepointing.

* `Ch' (K : PrecubicalSet) (a b : K.cells 0)` is the cube-chain category of `K`
  with chains taken from `a` to `b` — the **endpoint-indexed** reuse of `Ch`.
* The original `Ch K` is the `(init, final)` case: `ChainCat.Obj K = Ch' K.init K.final`
  holds by `rfl` (`BPSet` η).
* On **objects** the basepoint-free total category `ChP K` is the disjoint union
  `⊔_{a,b} Ch' a b`: each `Ch' a b` is the endpoint-preserving fiber over the
  interface `(a, b)`.  But `ChP` additionally carries endpoint-*changing* morphisms
  (sub-chain inclusions that move the endpoints), so `ChP` is the strictly richer
  *total* category — the union statement is an objects-only identification.  (Prose
  only; no proof.)

The pivot here (see `Operations/CylinderPlan.md`, "REVISED STRATEGY (2026-06-18)")
is that a *local* edit of `K` respects its own interface `(s, t)` even when it
ignores `init`/`final`, so it is an operation on `Ch' s t`, later promoted to
`Ch' init final` by Segal whiskering.
-/

open CategoryTheory Opposite

namespace BPSet

/-- Re-basepoint a precubical set `K` at the vertices `a`, `b`.  This is the trivial
constructor `⟨K, a, b⟩`, named so that the endpoint-indexed chain category reads well. -/
@[simp] def rebase (K : PrecubicalSet) (a b : K.cells 0) : BPSet := ⟨K, a, b⟩

@[simp] theorem rebase_toPsh (K : PrecubicalSet) (a b : K.cells 0) :
    (rebase K a b).toPsh = K := rfl

@[simp] theorem rebase_init (K : PrecubicalSet) (a b : K.cells 0) :
    (rebase K a b).init = a := rfl

@[simp] theorem rebase_final (K : PrecubicalSet) (a b : K.cells 0) :
    (rebase K a b).final = b := rfl

end BPSet

/-- The **endpoint-indexed cube-chain category**: the cube chains of the precubical
set `K` running from the vertex `a` to the vertex `b`.

This is `ChainCat.Obj` of `K` re-basepointed at `(a, b)`; as an `abbrev` it
inherits the `Category` instance (and all `ChainCat` API) for free. -/
abbrev Ch' (K : PrecubicalSet) (a b : K.cells 0) : Type :=
  ChainCat.Obj (BPSet.rebase K a b)

/-- `Ch' K a b` is a category, inherited through the `abbrev` from
`ChainCat.Obj`. -/
noncomputable example (K : PrecubicalSet) (a b : K.cells 0) : Category (Ch' K a b) :=
  inferInstance

/-- The original bi-pointed chain category `Ch K` is exactly the `(init, final)`
case of the endpoint-indexed `Ch'` — definitionally, by `BPSet` η. -/
example (K : BPSet) : ChainCat.Obj K = Ch' K.toPsh K.init K.final := rfl

namespace Ch'

/-- Morphisms of `Ch' K a b` (a re-export of `ChainCat.Hom` for ergonomics). -/
abbrev Hom {K : PrecubicalSet} {a b : K.cells 0} (x y : Ch' K a b) : Type :=
  ChainCat.Hom x y

/-- **Pushforward of endpoint-indexed chains.**  An interface-preserving map — i.e. a
`BPSet` morphism `BPSet.rebase K a b ⟶ BPSet.rebase L a' b'`, which is a precubical
map `K ⟶ L` carrying `a ↦ a'` and `b ↦ b'` — post-composes every chain, giving a
functor `Ch' K a b ⥤ Ch' L a' b'`.  This is just `ChainCat.pushforward`. -/
noncomputable def pushforward {K L : PrecubicalSet} {a b : K.cells 0} {a' b' : L.cells 0}
    (f : BPSet.rebase K a b ⟶ BPSet.rebase L a' b') : Ch' K a b ⥤ Ch' L a' b' :=
  ChainCat.pushforward f

@[simp] theorem pushforward_map_φ {K L : PrecubicalSet} {a b : K.cells 0} {a' b' : L.cells 0}
    (f : BPSet.rebase K a b ⟶ BPSet.rebase L a' b') {x y : Ch' K a b} (g : x ⟶ y) :
    ChainCat.Hom.φ ((pushforward f).map g) = ChainCat.Hom.φ g := rfl

/-- `pushforward` of the identity interface map is the identity functor. -/
theorem pushforward_id {K : PrecubicalSet} {a b : K.cells 0} :
    pushforward (𝟙 (BPSet.rebase K a b)) = 𝟭 (Ch' K a b) :=
  ChainCat.pushforward_id _

/-- `pushforward` respects composition of interface maps. -/
theorem pushforward_comp {K L M : PrecubicalSet}
    {a b : K.cells 0} {a' b' : L.cells 0} {a'' b'' : M.cells 0}
    (f : BPSet.rebase K a b ⟶ BPSet.rebase L a' b')
    (g : BPSet.rebase L a' b' ⟶ BPSet.rebase M a'' b'') :
    pushforward (f ≫ g) = pushforward f ⋙ pushforward g :=
  ChainCat.pushforward_comp f g

end Ch'

/-! ### Examples exercising the API (hardening). -/

/-- The identity pushforward on `Ch' K a b` is the identity functor. -/
example (K : PrecubicalSet) (a b : K.cells 0) :
    Ch'.pushforward (𝟙 (BPSet.rebase K a b)) = 𝟭 (Ch' K a b) :=
  Ch'.pushforward_id

/-- A `BPSet` automorphism of `K` (rebased at `a, b`) pushes forward to an endofunctor
of `Ch' K a b`, and reading off a morphism's underlying wedge map is unchanged. -/
example (K : PrecubicalSet) (a b : K.cells 0)
    (f : BPSet.rebase K a b ⟶ BPSet.rebase K a b) {x y : Ch' K a b} (g : x ⟶ y) :
    ChainCat.Hom.φ ((Ch'.pushforward f).map g) = ChainCat.Hom.φ g := by
  simp
