import CubeChains.Precubical.Chains.Correspondence
import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Concurrency.Executions.Runs
import Mathlib.Data.Fintype.Pi

/-!
# Testing/Enumerate/Enumerate — verified finite enumeration of `Ch (□n)`

For the standard cube `□n` — finite and loop-free — `Ch (□n)` is a finite category, so its objects
and (thin) hom-sets can be enumerated with a completeness proof.  Bottom-up:

* `Cell N k` is a decidable finite subtype (`Fin N → Option Bool` with `k` free coordinates);
* hence `(cube n).cells k ≃ Cell n k` is finite and decidable (cube Yoneda);
* a chain of `□n` has `dimSum = n` (`wedgeDimSum_eq`), so `length ≤ n` — the bound that makes the
  object set finite.

Loops are the only obstruction: with a directed cycle `CubeChain K` is genuinely infinite.  The
cube's altitude (`cube_admitsAltitude`) rules that out.

Not built by `lake build CubeChains`.
-/

set_option linter.style.nativeDecide false

open CategoryTheory StdCube

namespace StdCube

instance instFintypeCell (N k : ℕ) : Fintype (Cell N k) :=
  inferInstanceAs (Fintype {c : Fin N → Option Bool // (noneSet c).card = k})

end StdCube

open StdCube BPSet CubeChains

/-- Cube Yoneda: a `k`-cell of `□n` is a `Cell n k` (a `k`-face of the `n`-cube). -/
def cubeCellEquiv (n k : ℕ) : (cube n).cells k ≃ Cell n k := cubeRepr (stdPre n) k

instance instFintypeCubeCells (n k : ℕ) : Fintype ((cube n).cells k) :=
  Fintype.ofEquiv (Cell n k) (cubeCellEquiv n k).symm

instance instDecidableEqCubeCells (n k : ℕ) : DecidableEq ((cube n).cells k) :=
  (cubeCellEquiv n k).decidableEq

/-! ## The chain-length bound: a chain of `□n` has `dimSum = n`, so `length ≤ n` -/

/-- **A cube chain of `□n` has total dimension `n`** — it traverses every direction exactly once
(`wedgeDimSum_eq`). -/
theorem CubeChain.dimSum_cube (n : ℕ) (C : CubeChain (cube n)) : dimSum C.dims = n :=
  CubeChains.wedgeDimSum_eq (CubeChain.wedgeOfChain C).2

/-- **A cube chain of `□n` has at most `n` cubes.** -/
theorem CubeChain.length_le_cube (n : ℕ) (C : CubeChain (cube n)) : C.cubes.length ≤ n := by
  have h := length_le_dimSum C.dims
  rw [CubeChain.dimSum_cube n C] at h
  simpa [CubeChain.dims] using h

/-! ## Decidability: chains and refinements are decidable data -/

/-- `IsCubeChain` is decidable — a fold of decidable vertex equalities. -/
instance decIsCubeChain (K : BPSet) [DecidableEq (K.cells 0)] :
    ∀ (a : K.cells 0) (l : List (Σ n : ℕ+, K.cells (n : ℕ))) (b : K.cells 0),
      Decidable (IsCubeChain a l b)
  | a, [], b => decEq a b
  | a, ⟨_, c⟩ :: rest, b =>
      have := decIsCubeChain K (K.toPsh.vertex₁ c) rest b
      inferInstanceAs (Decidable (K.toPsh.vertex₀ c = a ∧ IsCubeChain (K.toPsh.vertex₁ c) rest b))

instance instDecidableEqCubeOf (n : ℕ) : DecidableEq (Σ k : ℕ+, (cube n).cells k) :=
  inferInstance

instance instDecidableEqCubeChain (n : ℕ) : DecidableEq (CubeChain (cube n)) :=
  inferInstanceAs (DecidableEq {l : List (Σ k : ℕ+, (cube n).cells k) //
    IsCubeChain (cube n).init l (cube n).final})

/-! ## `Fintype (CubeChain (cube n))` — dimensions `1..n`, chains bounded by length `n` -/

/-- The cubes of `□n`: dimensions run `1..n`, so finitely many. -/
instance instFintypeCubeOf (n : ℕ) : Fintype (Σ k : ℕ+, (cube n).cells k) :=
  Fintype.ofEquiv {p : Σ k : Fin (n + 1), Cell n (k : ℕ) // 0 < (p.1 : ℕ)}
    { toFun := fun q => ⟨⟨(q.1.1 : ℕ), q.2⟩, (cubeCellEquiv n (q.1.1 : ℕ)).symm q.1.2⟩
      invFun := fun p => ⟨⟨⟨(p.1 : ℕ), by
          by_cases h : (p.1 : ℕ) < n + 1
          · exact h
          · exact ((instIsEmptyCell (N := n) (k := (p.1 : ℕ)) (by omega)).false
              (cubeCellEquiv n (p.1 : ℕ) p.2)).elim⟩,
          cubeCellEquiv n (p.1 : ℕ) p.2⟩, p.1.pos⟩
      left_inv := by
        rintro ⟨⟨kf, cell⟩, hpos⟩
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Equiv.apply_symm_apply _ _)))
      right_inv := by
        rintro ⟨k, c⟩
        exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Equiv.symm_apply_apply _ _)) }

/-- Cubes of `□n`, bundled with their dimension — a finite type. -/
abbrev CubeOf (n : ℕ) : Type := Σ k : ℕ+, (cube n).cells k

set_option linter.unusedSimpArgs false in
/-- Lists of length `≤ n` over a finite type are finite. -/
def listLeEquiv (α : Type*) (n : ℕ) :
    {l : List α // l.length ≤ n} ≃ Σ m : Fin (n + 1), List.Vector α (m : ℕ) where
  toFun l := ⟨⟨l.1.length, Nat.lt_succ_of_le l.2⟩, l.1, rfl⟩
  invFun p := ⟨p.2.1, by rw [p.2.2]; exact Nat.le_of_lt_succ p.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨m, hm⟩, v⟩
    obtain ⟨l, hl⟩ := v
    simp only [Fin.val_mk] at hl
    subst hl
    rfl

instance instFintypeListLe (α : Type*) [Fintype α] (n : ℕ) :
    Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofEquiv _ (listLeEquiv α n).symm

/-- **`Ch (□n)` is a finite category** — the objects are finite (chains have `≤ n` cubes, each from
the finite cube type).  Computable, so `Finset.univ` enumerates them. -/
instance instFintypeCubeChain (n : ℕ) : Fintype (CubeChain (cube n)) :=
  Fintype.ofEquiv {b : {l : List (CubeOf n) // l.length ≤ n} //
      IsCubeChain (cube n).init b.1 (cube n).final}
    { toFun := fun b => ⟨b.1.1, b.2⟩
      invFun := fun C => ⟨⟨C.1, CubeChain.length_le_cube n C⟩, C.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-! ## Runs are finite: `Ch⋆(□n)` = chains with a linearization of each bead -/

/-- Edge chains — a decidable subtype of chains — are finite when chains are. -/
instance instFintypeEdgeChain (K : BPSet) [Fintype (CubeChain K)] : Fintype (EdgeChain K) :=
  inferInstanceAs (Fintype {C : CubeChain K // ∀ c ∈ C.cubes, (c.1 : ℕ) = 1})

/-- A run of a cube is an edge chain of it, hence finite (the `d!` linearizations of `□d`). -/
instance instFintypeRunCube (d : ℕ) : Fintype (Run (□d)) :=
  Fintype.ofEquiv _ (Run.equivEdgeChain (cube d)).symm

/-- One bead's run values are finite. -/
instance instFintypePshExtCube (c : ℕ) : Fintype (ChainCat.pshExt runPresheaf (□c)) :=
  Fintype.ofEquiv _ (cubeRunEquiv c)

/-- The iterated product of bead-run values is finite. -/
def fintypePshExtProd :
    ∀ dims : List ℕ+, Fintype (ChainCat.pshExtProdType runPresheaf dims)
  | [] => inferInstanceAs (Fintype PUnit)
  | c :: rest =>
      letI := fintypePshExtProd rest
      inferInstanceAs
        (Fintype (ChainCat.pshExt runPresheaf (□(c : ℕ)) ×
          ChainCat.pshExtProdType runPresheaf rest))

/-- **A run of a serial wedge is finite** — one linearization per bead (`runSegalProd`). -/
instance instFintypeRunWedge (dims : List ℕ+) : Fintype (Run (⋁dims)) :=
  letI := fintypePshExtProd dims
  Fintype.ofEquiv _ (runSegalProd dims).symm

/-- **The runs refining a chain are finite** — `Lines K c = (⋁c.dims).toPsh ⟶ runPresheaf`. -/
instance instFintypeLines (K : BPSet) (c : (Ch K)ᵒᵖ) : Fintype ((Lines K).obj c) :=
  Fintype.ofEquiv _ (runPshEquiv c.unop.dims).symm

/-- The chains of `□n` are finite (transport of `CubeChain`). -/
instance instFintypeCh (n : ℕ) : Fintype (Ch (cube n)) :=
  Fintype.ofEquiv _ (chEquivCubeChain (cube n)).symm

instance instDecidableEqCh (n : ℕ) : DecidableEq (Ch (cube n)) :=
  (chEquivCubeChain (cube n)).decidableEq

instance instFintypeChOp (n : ℕ) : Fintype ((Ch (cube n))ᵒᵖ) :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- **`Ch⋆(□n)` is a finite category** — a chain with a linearization of each bead; the verified
enumeration of the *executions* of `□n`. -/
instance instFintypeChStar (n : ℕ) : Fintype (Ch⋆ (cube n)) :=
  inferInstanceAs (Fintype (Σ c : (Ch (cube n))ᵒᵖ, (Lines (cube n)).obj c))
