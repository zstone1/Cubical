import CubeChains.Testing.Graph
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Testing/ExecEquiv — `Exec n` *is* `Ch⋆(□n)`

The combinatorial execution type of `Testing/Graph` is not a lookalike: `execEquivChStar` is a proven
equivalence `Exec n ≃ Ch⋆(□n)`, assembled from the run decomposition (`runProdEquiv`), the
chain↔cube-list equivalence (`chEquivCubeChain`), and the run-classifier (`runPshEquiv`).  So the
graph's nodes are genuinely the executions, and (with `permShadow = permOf`) its labels are `ConcPos`.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube

/-! ## Decomposing a run of a wedge into one edge chain per bead -/

/-- The iterated bead-product is the `Fin`-indexed product of bead values. -/
def pshExtProdTypePi (F : PrecubicalSet) :
    (a : List ℕ+) → ChainCat.pshExtProdType F a ≃ ∀ i : Fin a.length, ChainCat.pshExt F (□(a.get i : ℕ))
  | [] =>
      { toFun := fun _ i => i.elim0
        invFun := fun _ => PUnit.unit
        left_inv := fun _ => rfl
        right_inv := fun _ => funext fun i => i.elim0 }
  | c :: rest =>
      (Equiv.prodCongr (Equiv.refl _) (pshExtProdTypePi F rest)).trans
        (Fin.consEquiv fun i : Fin (rest.length + 1) => ChainCat.pshExt F (□((c :: rest).get i : ℕ)))

/-- A bead value of the run presheaf is an edge chain of the cube. -/
def edgeBeadEquiv (d : ℕ) : ChainCat.pshExt runPresheaf (□d) ≃ EdgeChain (cube d) :=
  (cubeRunEquiv d).symm.trans (Run.equivEdgeChain (cube d))

/-- **A run of `⋁dims` is one edge chain per bead** — Segal splitting, then cube Yoneda per bead. -/
def runProdEquiv (dims : List ℕ+) :
    Run (⋁dims) ≃ ∀ i : Fin dims.length, EdgeChain (cube (dims.get i : ℕ)) :=
  (runSegalProd dims).trans
    ((pshExtProdTypePi runPresheaf dims).trans
      (Equiv.piCongrRight fun i => edgeBeadEquiv (dims.get i : ℕ)))

/-! ## Reindexing a chain's per-bead runs from `dims` to `cubes` -/

/-- The per-bead runs indexed by `dims` vs by `cubes` — the same data (`dims = cubes.map dim`). -/
def reindexRun {n : ℕ} (C : CubeChain (cube n)) :
    (∀ i : Fin C.dims.length, EdgeChain (cube (C.dims.get i : ℕ))) ≃
      ∀ j : Fin C.cubes.length, EdgeChain (cube ((C.cubes.get j).1 : ℕ)) :=
  (Equiv.piCongrLeft' _ (finCongr (by simp [CubeChain.dims]))).trans
    (Equiv.piCongrRight fun j =>
      Equiv.cast (congrArg (fun d => EdgeChain (cube d)) (by
        simp only [CubeChain.dims, List.get_eq_getElem, List.getElem_map]; rfl)))

/-! ## `Ch⋆ K` as a chain with a run -/

/-- **`Ch⋆ K` is a chain paired with a run of its wedge** — unfold the category of elements and read
the run classifier through `runPshEquiv`. -/
def chStarSigmaRun (K : BPSet) : Ch⋆ K ≃ Σ c : Ch K, Run (⋁c.dims) where
  toFun x := ⟨x.1.unop, runPshEquiv x.1.unop.dims x.2⟩
  invFun p := ⟨op p.1, (runPshEquiv p.1.dims).symm p.2⟩
  left_inv x := Sigma.ext rfl (by simp)
  right_inv p := Sigma.ext rfl (by simp)

/-! ## The equivalence -/

/-- **`Ch⋆(□n) ≃ Exec n`** — a chain-with-run is a cube chain with one edge chain per bead. -/
def chStarEquivExec (n : ℕ) : Ch⋆ (cube n) ≃ Exec n :=
  (chStarSigmaRun (cube n)).trans <|
    (Equiv.sigmaCongrLeft' (chEquivCubeChain (cube n))).trans <|
      (Equiv.sigmaCongrRight fun C =>
        (Equiv.cast (congrArg (fun d => Run (⋁d)) (chEquivCubeChain_symm_dims (cube n) C))).trans
          ((runProdEquiv _).trans (reindexRun C)))

/-- **`Exec n ≃ Ch⋆(□n)`** — the combinatorial executions are the real executions. -/
def execEquivChStar (n : ℕ) : Exec n ≃ Ch⋆ (cube n) := (chStarEquivExec n).symm
