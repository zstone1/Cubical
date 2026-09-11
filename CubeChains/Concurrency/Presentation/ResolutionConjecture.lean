import CubeChains.Concurrency.Presentation.ArtinDegreeZero
import CubeChains.Concurrency.Merge.CubeWeakEquiv
import CubeChains.Concurrency.Salvetti.WallCrossing

/-!
# Concurrency/Presentation/ResolutionConjecture — the degree filtration as a resolution

Statements, not theorems: every declaration is a `Prop` that is *defined* and never proved, so
nothing here is assumed and the tree carries no `sorry` and no `axiom`.

A `k`-cell is a degree-zero codimension-`k` cut out of a run.  At `k ≤ 2` over `Zbp` this is proved
and the result *is* Artin's polygraph on the nose (`runAtomEquiv`, `runSquareEquiv`, `runRelabel`).
Open: dimension three and up, the asphericity making it a resolution, and the readings at other `K`.
A boundary for `k ≥ 3` needs cells of dimension `≥ 3`, which `Polygraph` does not carry, so the
asphericity condition is named in prose and not stated.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## The cells

The `k`-cell is indexed by the **shape** a `k`-fold cut lands on, not by the cut: the cuts to a
fixed shape are a parabolic, and the boundary is read off the longest of them. -/

/-- A degree-zero codimension-`k` shape of `Ch K`: what a `k`-fold cut out of a run reaches. -/
structure ResShape (K : BPSet) (k : ℕ) where
  /-- the run it is cut from -/
  src : Ch K
  /-- …which is a run -/
  src_run : degree src = 0
  /-- the shape -/
  tgt : Ch K
  /-- reached by a cut of codimension `k` -/
  cut : ∃ f : src ⟶ tgt, codim f = k

/-- The `k`-fold cuts to a fixed shape. -/
def ResCuts {K : BPSet} {k : ℕ} (c : ResShape K k) : Type := c.src ⟶ c.tgt

/-! ## Dimensions zero, one and two are theorems elsewhere

`degree_eq_zero_iff_eq_run`, `runAtomEquiv`, `runSquareEquiv`, `runSquare_artin` and `runRelabel`
are the `k ≤ 2` content, proved in `ArtinDegreeZero`.  They are what the conjectures below are
required to extend. -/

/-- **The shapes of codimension `k` over `Zbp` are the `k`-subsets of the `N−1` junctions.**  At
`k = 1` this is `runAtomEquiv`, at `k = 2` it is `runSquareEquiv`. -/
def ShapesAreSubsets : Prop :=
  ∀ N k : ℕ, Nonempty ({ s : Finset (Fin (N - 1)) // s.card = k } ≃ ResShape Zbp k)

/-- **A shape's cuts have a longest one.**  They are the elements of the Young subgroup the shape
names (`Composition.parabolic`), so one of them crosses its Garside element — and *that* is the cut
whose factorisations give the cell its boundary.  At `k = 1` the two cuts are the merge and the
atom, and the longest is the atom. -/
def CutsHaveTop : Prop :=
  ∀ (k : ℕ) (c : ResShape Zbp k),
    ∃ f : c.src ⟶ c.tgt, ∀ g : c.src ⟶ c.tgt,
      permLen (crossPerm rfl g) ≤ permLen (crossPerm rfl f)

/-- **The factorisations of a `k`-fold cut form a `k`-cube**: by `nonempty_hom_iff` the shape order
is reverse inclusion of junction sets, and by `factorisationEquiv` the factorisations are the
intermediate shapes, so they are the Boolean lattice on the `k` junctions dropped. -/
def FactorisationsAreCubes : Prop :=
  ∀ (k : ℕ) (c : ResShape Zbp k) (f : c.src ⟶ c.tgt),
    codim f = k → Nonempty ({ d : Ch Zbp // ∃ (_ : c.src ⟶ d) (_ : d ⟶ c.tgt), True }
      ≃ Finset (Fin k))

/-! ## Dimension three -/

/-- An ordered triple of junctions. -/
structure JunctionTriple (N : ℕ) where
  /-- the least -/
  lo : Fin (N - 1)
  /-- the middle -/
  mid : Fin (N - 1)
  /-- the greatest -/
  hi : Fin (N - 1)
  /-- …in order -/
  lt₁ : (lo : ℕ) < (mid : ℕ)
  /-- …strictly -/
  lt₂ : (mid : ℕ) < (hi : ℕ)

/-- **The codimension-three shapes are the triples**, the `k = 3` case of `ShapesAreSubsets`. -/
def TriplesAreCells : Prop :=
  ∀ N : ℕ, Nonempty (JunctionTriple N ≃ ResShape Zbp 3)

/-- **The three species of a triple** are the adjacency patterns of `{i,j,k}`, which are the
rank-three parabolic types `A₁×A₁×A₁`, `A₂×A₁` and `A₃` — how Gaussent–Guiraud–Malbos index the
3-cells of a coherent presentation of an Artin monoid. -/
def TripleSpecies : Prop :=
  ∀ (N : ℕ) (t : JunctionTriple N),
    -- `A₃`: three consecutive junctions
    ((t.mid : ℕ) = (t.lo : ℕ) + 1 ∧ (t.hi : ℕ) = (t.mid : ℕ) + 1)
    -- `A₂ × A₁`: exactly one adjacency
      ∨ ((t.mid : ℕ) = (t.lo : ℕ) + 1 ∧ (t.mid : ℕ) + 1 < (t.hi : ℕ))
      ∨ ((t.lo : ℕ) + 1 < (t.mid : ℕ) ∧ (t.hi : ℕ) = (t.mid : ℕ) + 1)
    -- `A₁ × A₁ × A₁`: all three apart
      ∨ ((t.lo : ℕ) + 1 < (t.mid : ℕ) ∧ (t.mid : ℕ) + 1 < (t.hi : ℕ))

/-! ## The three landings

The resolution is *defined* by the degree filtration, which exists for every `K`; that it is
Salvetti at the decorated cube is then a theorem about that `K`, not part of the definition. -/

/-- **At `Zbp`: the truncation at two is Artin.**  This one is proved — `runRelabel` — and is
recorded here to fix what the higher-dimensional statements must extend. -/
def LandsOnArtin : Prop :=
  ∀ N : ℕ, Nonempty (Polygraph.loopPoly (RunAtom N) (RunSquare N) (runSrc N) (runTgt N)
    ≅ artinBP.P N)

/-- **At the decorated cube: the cells are Salvetti's.**  A Salvetti cell of a reflection
arrangement is a face together with a chamber above it; here a run is a chamber and a `k`-subset of
junctions is a codimension-`k` face of it, so the count is one cell per pair.  `hbpBraidSalEquiv`
identifies the chains with `Sal (braidCOM n)`, which is what would make this a reading of that
complex rather than a coincidence of counts. -/
def LandsOnSalvetti : Prop :=
  ∀ n k : ℕ, Nonempty (ResShape (Hbp.obj (□n)) k
    ≃ (Equiv.Perm (Fin n) × { s : Finset (Fin (n - 1)) // s.card = k }))

/-! ## What is still missing

`Polygraph` carries cells in dimensions `0, 1, 2` only, so the asphericity condition — every
parallel pair of `k`-cells filled by a `(k+1)`-cell, for `k ≥ 2` — cannot be stated here.  It needs
an `n`-polygraph type, which is bespoke: `polyEquivPresheaf` is sharp at two, so 3-polygraphs are
not a presheaf category and limits and colimits are not computed cellwise.

The reading at `□n` has **no statement here because none is settled**.  `locCubeWeakOrder` makes the
localization the weak Bruhat order, a lattice, so its nerve is contractible and whatever is
non-trivial there is the cell structure rather than the homotopy type.  Writing a `Prop` before
knowing which invariant is wanted would be a placeholder pretending to be a conjecture. -/

end ChainCat
