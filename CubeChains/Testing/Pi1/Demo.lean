import CubeChains.Testing.Pi1.Pi1

/-!
# Testing/Pi1/Demo — the numbers

A sub-precubical set of `□n` to a presentation of its concurrency `π₁`, with the braid word `Conc`
assigns each generator.  Every eval here runs in seconds, so they are live rather than commented.

Reading the tuples: `concSummary` is `⟨executions, non-identity arrows, Salvetti cells by dimension,
χ⟩`; the `concPi1` triples are `⟨generators, relations, components⟩`.

Not built by `lake build CubeChains`.
-/

open CubeChains

/-! ## Executions: `n! · 2^(n-1)` of them, enumerated output-linearly -/

#eval (List.range 6).map fun n => (execs (SubCube.full n)).length   -- 1, 1, 4, 24, 192, 1920
#eval (execs (SubCube.boundary 3)).length                            -- 18 = 24 - 3!
#eval (execs (SubCube.boundary 4)).length                            -- 168 = 192 - 4!

/-! ## Shape

For `□n` the cells are the Salvetti cells of the braid arrangement `A_{n-1}`: `n! · C(n-1,d)` in
dimension `d`, so `χ = 0` for `n ≥ 2`. -/

#eval concSummary (SubCube.full 2)        -- ⟨4, 4, [2,2,0], 0⟩
#eval concSummary (SubCube.full 3)        -- ⟨24, 96, [6,12,6,0], 0⟩
#eval concSummary (SubCube.full 4)        -- ⟨192, 2688, [24,72,72,24,0], 0⟩
#eval concSummary (SubCube.boundary 3)    -- ⟨18, 24, [6,12,0,0], -6⟩
#eval concSummary (SubCube.boundary 4)    -- ⟨168, 912, [24,72,72,0,0], 24⟩

/-! ## `π₁`

`π₁(Ch⋆(□n))` is the pure braid group `Pₙ`; `Ch⋆(∂□³)` has height 1, so its nerve *is* its graph and
`π₁` is free of rank `E - V + 1 = 24 - 18 + 1 = 7`. -/

#eval let P := concPi1 (SubCube.full 2); (P.nGens, P.rels.size, P.components)      -- ⟨1, 0, 1⟩ = ℤ
#eval let P := concPi1 (SubCube.full 3); (P.nGens, P.rels.size, P.components)      -- ⟨37, 36, 1⟩
#eval let P := concPi1 (SubCube.full 4); (P.nGens, P.rels.size, P.components)      -- ⟨673, 2796, 1⟩
#eval let P := concPi1 (SubCube.boundary 3); (P.nGens, P.rels.size, P.components)  -- ⟨7, 0, 1⟩ free
#eval let P := concPi1 (SubCube.boundary 4); (P.nGens, P.rels.size, P.components)  -- ⟨361, 384, 1⟩

/-! ## `H₁`

`Pₙ` abelianizes to `ℤ^C(n,2)`, free.  `∂□⁴` removes only the cells with a single `4`-block — the
`3`-dimensional ones — so it is the `2`-skeleton of the same complex and has the same `π₁`. -/

#eval (concPi1 (SubCube.full 2)).homology       -- (1, [])
#eval (concPi1 (SubCube.full 3)).homology       -- (3, [])
#eval (concPi1 (SubCube.full 4)).homology       -- (6, [])
#eval (concPi1 (SubCube.boundary 4)).homology   -- (6, []) — P₄ again
#eval (concPi1 (SubCube.boundary 3)).homology   -- (7, []) — free of rank 7, not P₃

/-! ## Identifying the group

Tietze-reducing `□³` lands on `⟨g₁,g₂,g₃ | [g₂,g₁], [g₃,g₂]⟩`: `g₂` is central and `g₁, g₃` are free
of it and each other — `F₂ × ℤ = P₃`.  The braid words name the textbook generators, with `g₂` the
full twist `(σ₁σ₂σ₁)² = (σ₁σ₂)³ = Δ²` on the nose. -/

#eval let P := (concPi1 (SubCube.full 3)).simplify
      (P.nGens, P.rels.toList, P.words.toList)   -- 3, [[g₂,g₁],[g₃,g₂]], [A₁₂, Δ², A₁₃]
#eval let P := (concPi1 (SubCube.full 4)).simplify
      (P.nGens, P.rels.size, P.homology)         -- 6 generators — optimal, since H₁ = ℤ⁶

/-! ## The braid words

`□²`'s single generator is `σ₁²` — the generator of `P₂ = ℤ ⊂ B₂`. -/

#eval (concPi1 (SubCube.full 2)).words.toList     -- [[1, 1]]
#eval (concPi1 (SubCube.boundary 3)).words.toList

-- Salvetti asphericity forces every generating loop of `□n` to be a pure braid.
#eval (concPure (SubCube.full 3), concPure (SubCube.full 4))   -- (true, true)

/-! ## Can `Conc` tell `∂□³` from `□³`?

Not by its image.  Every generator of both is pure, so both images sit in `P₃`; and `∂□³` already
realises `σ₁² = A₁₂`, `σ₂² = A₂₃`, `σ₂σ₁²σ₂⁻¹ = A₁₃` outright, so both images *are* `P₃`.  The
abelianizations agree too — each spans the same subgroup of `P₃^ab`.  The `2`-cells `□³` adds are
attached along the braid relation, which is `1` in `B₃`, so filling them cannot move the image.
What changes is faithfulness: `π₁` drops from `F₇` to `P₃`, and the kernel is what `Conc` loses. -/

#eval (concLinks (SubCube.boundary 3), (concLinks (SubCube.full 3)).eraseDups)
#eval ((concPi1 (SubCube.full 3)).simplify.words.toList.map (linkVec 3))  -- A₁₂, Δ², A₁₃

/-! ## Bring your own precubical set

`SubCube n` is any face-closed predicate on the cells of `□n`, so the pipeline is not limited to the
cube and its boundary. -/

#eval concSummary (SubCube.skeleton 2 4)   -- the 2-skeleton of □⁴
#eval let P := concPi1 (SubCube.skeleton 2 4); (P.nGens, P.rels.size, P.components)

/-! ## GAP

`Presentation.gap` emits the presentation and `Presentation.braids` the generators' braid words. -/

#eval (concPi1 (SubCube.boundary 3)).gap
