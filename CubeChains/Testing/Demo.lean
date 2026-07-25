import CubeChains.Testing.LoopWords
import CubeChains.Testing.LabelConcPos
import CubeChains.Testing.Boundary

/-!
# Testing/Demo — the slow computations, in one leaf

Every `#eval` and `native_decide` of the testing tower lives here.  They route through `Glue` `Quot`
reductions in the interpreter and so are slow; the library files (`Enumerate`, `Morphisms`, `Graph`,
`Pi1`, `LoopWords`, …) carry only definitions and build fast.  Nothing imports this file, so a change
upstream never re-runs these evals except when this leaf is built on purpose.

Not built by `lake build CubeChains`.  Build it only to read the numbers.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube RunWedge

/-! ## Enumeration counts (`Enumerate`) — `Ch`, `Ch⋆` are `Fintype`, and they compute -/

-- #eval Fintype.card (CubeChain (cube 1))    -- 1
-- #eval Fintype.card (CubeChain (cube 2))    -- 3  ([2] + its two linearizations [1,1])
-- #eval Fintype.card (CubeChain (cube 3))    -- 13 = 1[3] + 3[2,1] + 3[1,2] + 6[1,1,1]
--
-- /-- Machine-checked: `Ch(□3)` has exactly 13 objects. -/
-- example : Fintype.card (CubeChain (cube 3)) = 13 := by native_decide
--
-- #eval Fintype.card (Ch⋆ (cube 1))    -- 1
-- #eval Fintype.card (Ch⋆ (cube 2))    -- 4
-- #eval Fintype.card (Ch⋆ (cube 3))    -- 24
--
-- /-! ## Morphisms and braid words (`Morphisms`) -/
--
-- #eval chHomCount 1    -- 1
-- #eval chHomCount 2    -- 5  (identities + the two refinements [1,1] ⟶ [2])
--
-- #eval Multiset.card (allChStarMorph 2)          -- morphisms of Ch⋆(□2)
-- #eval (allBraidWords 2)                          -- the braid words
-- #eval (allBraidWords 2).filter (· ≠ [])          -- the non-trivial ones
--
-- #eval (allChainPerms 2).filter fun l => l ≠ List.range l.length   -- □2: {[1,0]} (the σ₁ swap)
-- #eval (allChainPerms 3).filter fun l => l ≠ List.range l.length   -- □3: the σ₁/σ₂ swaps
--
-- -- `permOf` (run-dependent) vs `permShadow` (run-free): they diverge — see the ⚠ in `Morphisms`.
-- #eval (allChStarMorph 2).map concPosPerm    -- the real `ConcPos` permutations
-- #eval (allChStarMorph 2).map combPerm       -- the combinatorial (run-free) shadows
--
-- /-! ## The combinatorial graph and its `π₁` (`Graph`, `Pi1`) -/
--
-- #eval Fintype.card (Exec 1)   -- 1
-- #eval Fintype.card (Exec 2)   -- 4
-- #eval Fintype.card (Exec 3)   -- 24  (matches `Ch⋆`)
--
-- #eval Multiset.card (bdryNodes 3)    -- V: nodes of Ch⋆(∂□³)
-- #eval Multiset.card (bdryEdges 3)    -- E: directed edges
-- #eval ((bdryEdges 3).map (·.2.2)).filter fun l => l ≠ List.range l.length   -- crossing labels
--
-- #eval graphSummary 3    -- ⟨V, E, components, π₁ free rank⟩
--
-- /-! ## The loop braid words (`LoopWords`) -/
--
-- #eval loopWords 3       -- ∂□³ loop words
-- #eval loopWordsFull 3   -- □³ loop words
--
