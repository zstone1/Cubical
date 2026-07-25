import CubeChains.Testing.Morphisms

/-!
# Testing/Graph — the concurrency graph of `Ch⋆(□n)`, combinatorially

An execution of `□n` is a cube chain with a linearization (edge chain) of each bead — the run-level
object of `Ch⋆(□n)`, presented so that **nothing touches the `Glue`-based run presheaf**: runs are
`EdgeChain`s, restriction along a refinement is `EdgeChain.restrict`, and each edge's permutation is
`permShadow`.  So the whole quiver — nodes, directed edges, permutation labels — computes fast.

From it the fundamental group follows: for the connected quiver the free rank is `E - V + 1`, and the
labels (the `Sₙ`-image of `ConcPos`, lifted positively per edge direction) generate the braid group.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube

/-- **A combinatorial execution of `□n`** — a cube chain together with a linearization (edge chain) of
each of its beads.  Indexing runs by cubes (not dims) keeps restriction cast-free.  `Fintype`-many,
matching `Ch⋆(□n)`. -/
def Exec (n : ℕ) : Type :=
  Σ C : CubeChain (cube n), ∀ i : Fin C.cubes.length, EdgeChain (cube ((C.cubes.get i).1 : ℕ))

instance instFintypeExec (n : ℕ) : Fintype (Exec n) := by unfold Exec; infer_instance

/-- **The run restriction along a refinement** — bead `j` of the finer chain, a face of bead
`refinement j` of the coarser one via `incl j`, inherits that bead's linearization pulled back along
the face (`EdgeChain.restrict`).  Cast-free, combinatorial. -/
def restrictRun {n : ℕ} {C₁ C₂ : CubeChain (cube n)}
    (cr : ChainRefine (cube n).init (cube n).final C₂.cubes C₁.cubes)
    (r : ∀ i : Fin C₁.cubes.length, EdgeChain (cube ((C₁.cubes.get i).1 : ℕ))) :
    ∀ j : Fin C₂.cubes.length, EdgeChain (cube ((C₂.cubes.get j).1 : ℕ)) :=
  fun j => EdgeChain.restrict (cr.incl j) (r (cr.refinement j))

/-- The out-edges of an execution `e` — one per refinement `cr` of its chain — as `⟨target, label⟩`,
the label being the crossing permutation `permShadow cr`.  (Ch⋆ arrows run coarse ⟶ fine.) -/
def outEdges {n : ℕ} (e : Exec n) : Multiset (Exec n × List ℕ) :=
  (Finset.univ : Finset (CubeChain (cube n))).val.bind fun C₂ =>
    (Finset.univ :
        Finset (ChainRefine (cube n).init (cube n).final C₂.cubes e.1.cubes)).val.map
      fun cr => (⟨C₂, restrictRun cr e.2⟩, permShadow cr)

/-! ## The boundary `∂□n` — executions avoiding the top cell -/

/-- A boundary execution: its chain uses no top (`n`-dimensional) cube. -/
def IsBdryExec (n : ℕ) (e : Exec n) : Prop := ∀ c ∈ e.1.cubes, (c.1 : ℕ) ≠ n

instance (n : ℕ) (e : Exec n) : Decidable (IsBdryExec n e) :=
  inferInstanceAs (Decidable (∀ c ∈ e.1.cubes, (c.1 : ℕ) ≠ n))

/-- The nodes of the boundary concurrency graph `Ch⋆(∂□n)`. -/
def bdryNodes (n : ℕ) : Multiset (Exec n) :=
  (Finset.univ : Finset (Exec n)).val.filter (IsBdryExec n)

/-- The directed, permutation-labeled edges of `Ch⋆(∂□n)` — `⟨source, target, label⟩`. -/
def bdryEdges (n : ℕ) : Multiset (Exec n × Exec n × List ℕ) :=
  (bdryNodes n).bind fun e => (outEdges e).map fun t => ⟨e, t.1, t.2⟩
