import CubeChains.Salvetti.SalLines

/-!
# Salvetti/RunHeightSplit — `runHeight` is bead-local

A run of a concatenated shape `b₁ ++ b₂` splits (`runAppend`), and so does the all-edges chain it
traces out: `wedgeToCubes` of `runAppend s₁ s₂ ≫ m` is the append of the two halves' cube lists.
Hence a coordinate flipped in the first half gets its own left-hand position as `runHeight`, and
one flipped in the second half gets that position shifted by `dimSum b₁`.
-/

open CategoryTheory Opposite CubeChain ChainCat StdCube BPSet SignType

namespace CubeChains

variable {n : ℕ}

/-! ## Part 1 — the cube list of a concatenated run -/

/-- A shape identity transports the serial wedge the same way at `BPSet` and presheaf level. -/
theorem serialWedge_eqToHom_hom {d₁ d₂ : List ℕ+} (e : d₁ = d₂) :
    (eqToHom (congrArg BPSet.serialWedge e) : ⋁d₁ ⟶ ⋁d₂).hom
      = eqToHom (congrArg (fun l => (⋁l).toPsh) e) := by
  cases e; simp

/-- **`wedgeToCubes` of a concatenated run.**  `runAppend` is `concatChainMap` sandwiched between
the source shape transport and the append iso (`runAppend_eq_concatChainMap`), so reading its
cubes is `wedgeToCubes_append` with both halves identified by `concatChainMap_inclL/R`. -/
theorem wedgeToCubes_runAppend {K : BPSet} (b₁ b₂ : List ℕ+) (s₁ : Run b₁) (s₂ : Run b₂)
    (φ : (⋁(b₁ ++ b₂)).toPsh ⟶ K.toPsh) :
    wedgeToCubes ⟨𝟙^(dimSum (b₁ ++ b₂)), (runAppend s₁ s₂).hom ≫ φ⟩
      = wedgeToCubes ⟨𝟙^(dimSum b₁), s₁.hom ≫ wedgeInclL b₁ b₂ ≫ φ⟩
        ++ wedgeToCubes ⟨𝟙^(dimSum b₂), s₂.hom ≫ wedgeInclR b₁ b₂ ≫ φ⟩ := by
  have h : 𝟙^(dimSum (b₁ ++ b₂)) = 𝟙^(dimSum b₁) ++ 𝟙^(dimSum b₂) :=
    replicate_dimSum_append b₁ b₂
  let A₁ : Ch (⋁b₁) := ⟨𝟙^(dimSum b₁), s₁⟩
  let A₂ : Ch (⋁b₂) := ⟨𝟙^(dimSum b₂), s₂⟩
  -- the map, after the shape transport is peeled off
  let ψ : (⋁(𝟙^(dimSum b₁) ++ 𝟙^(dimSum b₂))).toPsh ⟶ K.toPsh :=
    (concatChainMap (⋁b₁) (⋁b₂) A₁ A₂).hom ≫ (serialWedgeAppendHom b₁ b₂).hom ≫ φ
  have hsplit : ((runAppend s₁ s₂).hom ≫ φ : (⋁(𝟙^(dimSum (b₁ ++ b₂)))).toPsh ⟶ K.toPsh)
      = eqToHom (congrArg (fun l => (⋁l).toPsh) h) ≫ ψ := by
    have hr := congrArg BPSet.Hom.hom (runAppend_eq_concatChainMap s₁ s₂)
    rw [comp_hom, comp_hom] at hr
    rw [hr, serialWedge_eqToHom_hom h]
    simp only [Category.assoc]
    rfl
  have hL : wedgeInclL (𝟙^(dimSum b₁)) (𝟙^(dimSum b₂)) ≫ ψ = s₁.hom ≫ wedgeInclL b₁ b₂ ≫ φ := by
    have h₀ : wedgeInclL A₁.dims A₂.dims ≫ (concatChainMap (⋁b₁) (⋁b₂) A₁ A₂).hom
        = A₁.map.hom ≫ wedgeInl (⋁b₁) (⋁b₂) := concatChainMap_inclL (⋁b₁) (⋁b₂) A₁ A₂
    calc wedgeInclL (𝟙^(dimSum b₁)) (𝟙^(dimSum b₂)) ≫ ψ
        = (wedgeInclL A₁.dims A₂.dims ≫ (concatChainMap (⋁b₁) (⋁b₂) A₁ A₂).hom)
            ≫ (serialWedgeAppendHom b₁ b₂).hom ≫ φ := by rw [Category.assoc]
      _ = s₁.hom ≫ wedgeInclL b₁ b₂ ≫ φ := by
          rw [h₀, wedgeInclL, Category.assoc, Category.assoc]; rfl
  have hR : wedgeInclR (𝟙^(dimSum b₁)) (𝟙^(dimSum b₂)) ≫ ψ = s₂.hom ≫ wedgeInclR b₁ b₂ ≫ φ := by
    have h₀ : wedgeInclR A₁.dims A₂.dims ≫ (concatChainMap (⋁b₁) (⋁b₂) A₁ A₂).hom
        = A₂.map.hom ≫ wedgeInr (⋁b₁) (⋁b₂) := concatChainMap_inclR (⋁b₁) (⋁b₂) A₁ A₂
    calc wedgeInclR (𝟙^(dimSum b₁)) (𝟙^(dimSum b₂)) ≫ ψ
        = (wedgeInclR A₁.dims A₂.dims ≫ (concatChainMap (⋁b₁) (⋁b₂) A₁ A₂).hom)
            ≫ (serialWedgeAppendHom b₁ b₂).hom ≫ φ := by rw [Category.assoc]
      _ = s₂.hom ≫ wedgeInclR b₁ b₂ ≫ φ := by
          rw [h₀, wedgeInclR, Category.assoc, Category.assoc]; rfl
  calc wedgeToCubes ⟨𝟙^(dimSum (b₁ ++ b₂)), (runAppend s₁ s₂).hom ≫ φ⟩
      = wedgeToCubes ⟨𝟙^(dimSum (b₁ ++ b₂)),
          eqToHom (congrArg (fun l => (⋁l).toPsh) h) ≫ ψ⟩ :=
        congrArg (fun z : (⋁(𝟙^(dimSum (b₁ ++ b₂)))).toPsh ⟶ K.toPsh =>
          wedgeToCubes ⟨𝟙^(dimSum (b₁ ++ b₂)), z⟩) hsplit
    _ = wedgeToCubes ⟨𝟙^(dimSum b₁) ++ 𝟙^(dimSum b₂), ψ⟩ := wedgeToCubes_eqToHom h ψ
    _ = _ := by rw [wedgeToCubes_append _ _ ψ, hL, hR]; rfl

/-! ## Part 2 — block indices of an appended cube list -/

/-- A bead of the first half keeps its own position as block index. -/
theorem blockIndex_of_mem_left {L₁ L₂ : List (Σ d : ℕ+, (□n).cells (d : ℕ))}
    {x : RefineObj (□n).init (□n).final} (hx : x.cubes = L₁ ++ L₂)
    {i : ℕ} (hi : i < L₁.length) {p : Fin n}
    (hp : p ∈ noneSet (toStar L₁[i].2).val) :
    ((blockIndex x p : ℕ)) = i := by
  obtain ⟨cs, hch⟩ := x
  subst hx
  have hix : i < (L₁ ++ L₂).length := by rw [List.length_append]; omega
  refine congrArg Fin.val (blockIndex_unique _ (i := ⟨i, hix⟩) ?_)
  change p ∈ noneSet (toStar ((L₁ ++ L₂).get ⟨i, hix⟩).2).val
  rw [List.get_eq_getElem, List.getElem_append_left hi]
  exact hp

/-- A bead of the second half has its block index shifted by the first half's length. -/
theorem blockIndex_of_mem_right {L₁ L₂ : List (Σ d : ℕ+, (□n).cells (d : ℕ))}
    {x : RefineObj (□n).init (□n).final} (hx : x.cubes = L₁ ++ L₂)
    {j : ℕ} (hj : j < L₂.length) {p : Fin n}
    (hp : p ∈ noneSet (toStar L₂[j].2).val) :
    ((blockIndex x p : ℕ)) = j + L₁.length := by
  obtain ⟨cs, hch⟩ := x
  subst hx
  have hix : j + L₁.length < (L₁ ++ L₂).length := by rw [List.length_append]; omega
  refine congrArg Fin.val (blockIndex_unique _ (i := ⟨j + L₁.length, hix⟩) ?_)
  change p ∈ noneSet (toStar ((L₁ ++ L₂).get ⟨j + L₁.length, hix⟩).2).val
  rw [List.get_eq_getElem, ← List.getElem_append_right' L₁ hj]
  exact hp

/-! ## Part 3 — `runHeight` of a concatenated run -/

/-- The beads the first half of a concatenated run traces out in `□ⁿ`. -/
def runCubesL (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n) (s₁ : Run b₁) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  wedgeToCubes ⟨𝟙^(dimSum b₁), s₁.hom ≫ wedgeInclL b₁ b₂ ≫ m.hom⟩

/-- The beads the second half of a concatenated run traces out in `□ⁿ`. -/
def runCubesR (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n) (s₂ : Run b₂) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  wedgeToCubes ⟨𝟙^(dimSum b₂), s₂.hom ≫ wedgeInclR b₁ b₂ ≫ m.hom⟩

@[simp] theorem runCubesL_length (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n) (s₁ : Run b₁) :
    (runCubesL b₁ b₂ m s₁).length = dimSum b₁ := by
  rw [runCubesL, wedgeToCubes_length, List.length_replicate]

@[simp] theorem runCubesR_length (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n) (s₂ : Run b₂) :
    (runCubesR b₁ b₂ m s₂).length = dimSum b₂ := by
  rw [runCubesR, wedgeToCubes_length, List.length_replicate]

/-- **The beads of a concatenated run split.**  `runChain` of `runAppend s₁ s₂` reads off as the
two halves' bead lists, appended. -/
theorem runChain_cubes_runAppend (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n)
    (s₁ : Run b₁) (s₂ : Run b₂) :
    (wedgeToRefineObj (runChain ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂))).cubes
      = runCubesL b₁ b₂ m s₁ ++ runCubesR b₁ b₂ m s₂ := by
  change wedgeToCubes ⟨𝟙^(dimSum (b₁ ++ b₂)), (runAppend s₁ s₂ ≫ m).hom⟩ = _
  rw [comp_hom]
  exact wedgeToCubes_runAppend b₁ b₂ s₁ s₂ m.hom

variable (b₁ b₂ : List ℕ+) (m : ⋁(b₁ ++ b₂) ⟶ □n) (s₁ : Run b₁) (s₂ : Run b₂)

/-- The coordinates flipped by the `i`-th bead of the first half. -/
def leftBlock (i : Fin (runCubesL b₁ b₂ m s₁).length) : Finset (Fin n) :=
  noneSet (toStar ((runCubesL b₁ b₂ m s₁).get i).2).val

/-- The coordinates flipped by the `j`-th bead of the second half. -/
def rightBlock (j : Fin (runCubesR b₁ b₂ m s₂).length) : Finset (Fin n) :=
  noneSet (toStar ((runCubesR b₁ b₂ m s₂).get j).2).val

/-- **Height in the first half.**  A coordinate flipped by the `i`-th bead of the first half sits
at height `i` in the whole run. -/
theorem runHeight_runAppend_left (i : Fin (runCubesL b₁ b₂ m s₁).length) {p : Fin n}
    (hp : p ∈ leftBlock b₁ b₂ m s₁ i) :
    runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) p = ((i : ℕ) : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ))
    (blockIndex_of_mem_left (runChain_cubes_runAppend b₁ b₂ m s₁ s₂) i.isLt hp)

/-- **Height in the second half.**  A coordinate flipped by the `j`-th bead of the second half sits
at height `dimSum b₁ + j` — the first half's beads all come first. -/
theorem runHeight_runAppend_right (j : Fin (runCubesR b₁ b₂ m s₂).length) {p : Fin n}
    (hp : p ∈ rightBlock b₁ b₂ m s₂ j) :
    runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) p = (dimSum b₁ : ℤ) + ((j : ℕ) : ℤ) := by
  have h := blockIndex_of_mem_right (runChain_cubes_runAppend b₁ b₂ m s₁ s₂) j.isLt hp
  have h₂ : ((blockIndex (wedgeToRefineObj (runChain ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂)))
      p : ℕ)) = (j : ℕ) + dimSum b₁ := h.trans (congrArg _ (runCubesL_length b₁ b₂ m s₁))
  have h' : ((blockIndex (wedgeToRefineObj (runChain ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂)))
      p : ℕ) : ℤ) = (((j : ℕ) + dimSum b₁ : ℕ) : ℤ) := congrArg (fun k : ℕ => (k : ℤ)) h₂
  rw [Nat.cast_add] at h'
  rw [add_comm]
  exact h'

/-- **Every coordinate is flipped in exactly one half** — the blocks of the whole run cover
`Fin n`, and the whole run's bead list is the two halves appended. -/
theorem mem_leftBlock_or_rightBlock (p : Fin n) :
    (∃ i, p ∈ leftBlock b₁ b₂ m s₁ i) ∨ (∃ j, p ∈ rightBlock b₁ b₂ m s₂ j) := by
  set x := wedgeToRefineObj (runChain ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂))
  have hx : x.cubes = runCubesL b₁ b₂ m s₁ ++ runCubesR b₁ b₂ m s₂ :=
    runChain_cubes_runAppend b₁ b₂ m s₁ s₂
  have hmem : p ∈ noneSet (toStar (x.cubes.get (blockIndex x p)).2).val := blockIndex_mem x p
  have hlen : x.cubes.length
      = (runCubesL b₁ b₂ m s₁).length + (runCubesR b₁ b₂ m s₂).length := by
    rw [hx, List.length_append]
  have hklt : (blockIndex x p : ℕ)
      < (runCubesL b₁ b₂ m s₁).length + (runCubesR b₁ b₂ m s₂).length := by
    rw [← hlen]; exact (blockIndex x p).isLt
  rw [List.get_eq_getElem, List.getElem_of_eq hx] at hmem
  by_cases hcase : (blockIndex x p : ℕ) < (runCubesL b₁ b₂ m s₁).length
  · refine Or.inl ⟨⟨_, hcase⟩, ?_⟩
    change p ∈ noneSet (toStar ((runCubesL b₁ b₂ m s₁).get ⟨_, hcase⟩).2).val
    rw [List.get_eq_getElem, ← List.getElem_append_left (bs := runCubesR b₁ b₂ m s₂) hcase]
    exact hmem
  · rw [Nat.not_lt] at hcase
    refine Or.inr ⟨⟨(blockIndex x p : ℕ) - (runCubesL b₁ b₂ m s₁).length, by omega⟩, ?_⟩
    change p ∈ noneSet (toStar ((runCubesR b₁ b₂ m s₂).get ⟨_, _⟩).2).val
    rw [List.get_eq_getElem, ← List.getElem_append_right (bs := runCubesR b₁ b₂ m s₂) hcase]
    exact hmem

/-- **The first half runs first.**  A coordinate flipped in the first half has strictly smaller
height than one flipped in the second — this is what makes `runHeight` bead-local. -/
theorem runHeight_left_lt_right (i : Fin (runCubesL b₁ b₂ m s₁).length)
    (j : Fin (runCubesR b₁ b₂ m s₂).length) {p q : Fin n}
    (hp : p ∈ leftBlock b₁ b₂ m s₁ i) (hq : q ∈ rightBlock b₁ b₂ m s₂ j) :
    runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) p
      < runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) q := by
  rw [runHeight_runAppend_left b₁ b₂ m s₁ s₂ i hp,
    runHeight_runAppend_right b₁ b₂ m s₁ s₂ j hq]
  have hi : (i : ℕ) < dimSum b₁ := lt_of_lt_of_eq i.isLt (runCubesL_length b₁ b₂ m s₁)
  have : ((i : ℕ) : ℤ) < (dimSum b₁ : ℤ) := by exact_mod_cast hi
  omega

/-- **Order inside the first half** is the order of the first half's own bead indices. -/
theorem runHeight_lt_iff_left (i j : Fin (runCubesL b₁ b₂ m s₁).length) {p q : Fin n}
    (hp : p ∈ leftBlock b₁ b₂ m s₁ i) (hq : q ∈ leftBlock b₁ b₂ m s₁ j) :
    (runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) p
      < runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) q) ↔ i < j := by
  rw [runHeight_runAppend_left b₁ b₂ m s₁ s₂ i hp,
    runHeight_runAppend_left b₁ b₂ m s₁ s₂ j hq, Fin.lt_def]
  exact Int.ofNat_lt

/-- **Order inside the second half** is the order of the second half's own bead indices. -/
theorem runHeight_lt_iff_right (i j : Fin (runCubesR b₁ b₂ m s₂).length) {p q : Fin n}
    (hp : p ∈ rightBlock b₁ b₂ m s₂ i) (hq : q ∈ rightBlock b₁ b₂ m s₂ j) :
    (runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) p
      < runHeight ⟨b₁ ++ b₂, m⟩ (runAppend s₁ s₂) q) ↔ i < j := by
  rw [runHeight_runAppend_right b₁ b₂ m s₁ s₂ i hp,
    runHeight_runAppend_right b₁ b₂ m s₁ s₂ j hq, add_lt_add_iff_left, Fin.lt_def]
  exact Int.ofNat_lt

end CubeChains
