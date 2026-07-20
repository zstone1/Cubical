import CubeChains.Salvetti.RunOrderFace

/-!
# Salvetti/WallCrossing — the bead-local half of the Salvetti wall-crossing law

`wallCrossing_of_sameBlock` asks that restricting a run along `f : a ⟶ b` preserve the relative
order of any two coordinates lying in one bead of `a`.  The two halves of that argument live in
`RunOrderFace` (a single bead) and `Runs` (the concatenation).  Gluing them needs a height on
*raw cube lists* rather than on chains from `init` to `final`: a chain flips `p` exactly when `p`
is `0` at its source and `1` at its target (`flips_iff_endpoints`), so the halves a junction cuts
out carry no `blockIndex`.  `flipIdx` (`List.findIdx`, with `length` as the not-found sentinel) is
the total replacement, `flipIdx_eq_blockIndex` the bridge.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Part 0 — `flipIdx`: the position at which a cube list flips a coordinate

Defined on a raw list of cubes, with no chain condition, so that it survives the cut of a wedge
at a junction.  `List.findIdx` gives the append law for nothing; on an honest chain the block is
unique, so `flipIdx` *is* `blockIndex` (`flipIdx_eq_blockIndex`). -/

/-- The cubes a wedge map into `□ⁿ` traces out. -/
abbrev CubeList (n : ℕ) : Type := List (Σ d : ℕ+, (□n).cells (d : ℕ))

/-- "This cube flips coordinate `p`". -/
def flipsAt (p : Fin n) (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : Bool :=
  decide (p ∈ noneSet (toStar c.2).val)

@[simp] theorem flipsAt_eq_true {p : Fin n} {c : Σ d : ℕ+, (□n).cells (d : ℕ)} :
    flipsAt p c = true ↔ p ∈ noneSet (toStar c.2).val := by
  simp [flipsAt]

/-- **The height of a coordinate in a cube list**: the position of the cube that flips it, or the
length of the list if none does. -/
def flipIdx (L : CubeList n) (p : Fin n) : ℕ := L.findIdx (flipsAt p)

/-- **`L` flips `p` somewhere** — `flipIdx L p` is a genuine position and not the sentinel. -/
def Flips (L : CubeList n) (p : Fin n) : Prop := flipIdx L p < L.length

/-- Kept defeq to `Nat.decLt` so that `if Flips L p` and `if flipIdx L p < L.length` are the
same `ite`, which is what lets `List.findIdx_append` land as `flipIdx_append`. -/
instance (L : CubeList n) (p : Fin n) : Decidable (Flips L p) :=
  inferInstanceAs (Decidable (flipIdx L p < L.length))

/-- `Flips` spelled out over the list. -/
theorem flips_iff_exists (L : CubeList n) (p : Fin n) :
    Flips L p ↔ ∃ c ∈ L, p ∈ noneSet (toStar c.2).val := by
  rw [Flips, flipIdx, List.findIdx_lt_length]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, flipsAt_eq_true.mp h⟩,
    fun ⟨c, hc, h⟩ => ⟨c, hc, flipsAt_eq_true.mpr h⟩⟩

/-- The cube found at a coordinate's height does flip it. -/
theorem mem_noneSet_flipIdx {L : CubeList n} {p : Fin n} (h : Flips L p) :
    p ∈ noneSet (toStar (L[flipIdx L p]'h).2).val :=
  flipsAt_eq_true.mp (List.findIdx_getElem (w := h))

/-- **On a chain, `flipIdx` is `blockIndex`** — the block containing a coordinate is unique, so
the first block that flips it is the only one. -/
theorem flipIdx_eq_blockIndex (x : RefineObj (□n).init (□n).final) (p : Fin n) :
    flipIdx x.cubes p = ((blockIndex x p : ℕ)) := by
  have hex : Flips x.cubes p :=
    (flips_iff_exists _ _).mpr ⟨x.cubes.get (blockIndex x p), List.get_mem _ _, blockIndex_mem x p⟩
  refine congrArg Fin.val (blockIndex_unique x (i := ⟨flipIdx x.cubes p, hex⟩) ?_).symm
  change p ∈ noneSet (toStar (x.cubes.get ⟨flipIdx x.cubes p, hex⟩).2).val
  rw [List.get_eq_getElem]
  exact mem_noneSet_flipIdx hex

/-! ## Part 1 — the append calculus, stated once

Cube lists under `++` are a monoid and `flipIdx` reads it: found in the first half, or shifted
past it.  Both recursions cut a wedge at a junction, so both meet the same question — how a
comparison of two coordinates crosses a cut.  `lt_append_iff_of_tie` answers it once and for all,
against an abstract right-hand side `R` so that it serves the source recursion (where the target
run stays whole) and the target recursion (where it splits too) alike. -/

/-- `flipIdx` over an append: found in the first half, or shifted past it. -/
theorem flipIdx_append (L₁ L₂ : CubeList n) (p : Fin n) :
    flipIdx (L₁ ++ L₂) p = if Flips L₁ p then flipIdx L₁ p else flipIdx L₂ p + L₁.length :=
  List.findIdx_append

theorem flipIdx_append_left {L₁ L₂ : CubeList n} {p : Fin n} (h : Flips L₁ p) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₁ p := by rw [flipIdx_append, if_pos h]

theorem flipIdx_append_right {L₁ L₂ : CubeList n} {p : Fin n} (h : ¬ Flips L₁ p) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₂ p + L₁.length := by rw [flipIdx_append, if_neg h]

/-- **A tie does not straddle the junction.** -/
theorem flipIdx_sameSide {L₁ L₂ : CubeList n} {p q : Fin n}
    (h : flipIdx (L₁ ++ L₂) p = flipIdx (L₁ ++ L₂) q) (hp : Flips L₁ p) : Flips L₁ q := by
  have hp' : flipIdx L₁ p < L₁.length := hp
  by_contra hq
  rw [flipIdx_append_left hp, flipIdx_append_right hq] at h
  omega

theorem flipIdx_append_lt_iff_left {L₁ L₂ : CubeList n} {p q : Fin n}
    (hp : Flips L₁ p) (hq : Flips L₁ q) :
    (flipIdx (L₁ ++ L₂) p < flipIdx (L₁ ++ L₂) q ↔ flipIdx L₁ p < flipIdx L₁ q) := by
  rw [flipIdx_append_left hp, flipIdx_append_left hq]

theorem flipIdx_append_lt_iff_right {L₁ L₂ : CubeList n} {p q : Fin n}
    (hp : ¬ Flips L₁ p) (hq : ¬ Flips L₁ q) :
    (flipIdx (L₁ ++ L₂) p < flipIdx (L₁ ++ L₂) q ↔ flipIdx L₂ p < flipIdx L₂ q) := by
  rw [flipIdx_append_right hp, flipIdx_append_right hq]
  omega

/-- **The cut.**  Two coordinates tied by `X₁ ++ X₂` lie on one side of the junction, so a list
`U₁ ++ U₂` whose first half flips exactly what `X₁` flips compares them by that one side.  `R` is
whatever the comparison is being matched against. -/
theorem lt_append_iff_of_tie {X₁ X₂ U₁ U₂ : CubeList n} {p q : Fin n} {R : Prop}
    (hsupp : ∀ z, Flips U₁ z ↔ Flips X₁ z)
    (htie : flipIdx (X₁ ++ X₂) p = flipIdx (X₁ ++ X₂) q) (hfound : Flips (X₁ ++ X₂) p)
    (head : Flips X₁ p → Flips X₁ q → flipIdx X₁ p = flipIdx X₁ q →
      (flipIdx U₁ p < flipIdx U₁ q ↔ R))
    (tail : ¬ Flips X₁ p → ¬ Flips X₁ q → flipIdx X₂ p = flipIdx X₂ q → Flips X₂ p →
      (flipIdx U₂ p < flipIdx U₂ q ↔ R)) :
    (flipIdx (U₁ ++ U₂) p < flipIdx (U₁ ++ U₂) q ↔ R) := by
  have hf : flipIdx (X₁ ++ X₂) p < (X₁ ++ X₂).length := hfound
  by_cases hc : Flips X₁ p
  · have hcq : Flips X₁ q := flipIdx_sameSide htie hc
    rw [flipIdx_append_lt_iff_left ((hsupp p).mpr hc) ((hsupp q).mpr hcq)]
    rw [flipIdx_append_left hc, flipIdx_append_left hcq] at htie
    exact head hc hcq htie
  · have hcq : ¬ Flips X₁ q := fun h => hc (flipIdx_sameSide htie.symm h)
    rw [flipIdx_append_lt_iff_right (fun z => hc ((hsupp p).mp z))
      (fun z => hcq ((hsupp q).mp z))]
    rw [flipIdx_append_right hc, flipIdx_append_right hcq] at htie
    rw [flipIdx_append_right hc, List.length_append] at hf
    exact tail hc hcq (by omega) (show flipIdx X₂ p < X₂.length by omega)

/-- `OrderAgree X U V`: whenever the chain `X` flips `p` and `q` in one and the same bead, the
lists `U` and `V` order them alike.  `X` is the source chain, `U` the restricted run, `V` the
run being restricted. -/
def OrderAgree (X U V : CubeList n) : Prop :=
  ∀ p q : Fin n, flipIdx X p = flipIdx X q → Flips X p →
    (flipIdx U p < flipIdx U q ↔ flipIdx V p < flipIdx V q)

/-- The empty wedge flips nothing, so `OrderAgree` over it is vacuous. -/
theorem orderAgree_nil {X U V : CubeList n} (h : X.length = 0) : OrderAgree X U V := by
  intro p _ _ hfound
  have hp : flipIdx X p < X.length := hfound
  omega

/-- **`OrderAgree` is stable under a cut**, provided the halves' supports match the source's. -/
theorem OrderAgree.append {X₁ X₂ U₁ U₂ V₁ V₂ : CubeList n}
    (hU : ∀ z, Flips U₁ z ↔ Flips X₁ z) (hV : ∀ z, Flips V₁ z ↔ Flips X₁ z)
    (h₁ : OrderAgree X₁ U₁ V₁) (h₂ : OrderAgree X₂ U₂ V₂) :
    OrderAgree (X₁ ++ X₂) (U₁ ++ U₂) (V₁ ++ V₂) := by
  intro p q htie hfound
  refine lt_append_iff_of_tie hU htie hfound (fun hp hq h => ?_) (fun hp hq h hf => ?_)
  · exact (h₁ p q h hp).trans
      (flipIdx_append_lt_iff_left ((hV p).mpr hp) ((hV q).mpr hq)).symm
  · exact (h₂ p q h hf).trans
      (flipIdx_append_lt_iff_right (fun z => hp ((hV p).mp z))
        (fun z => hq ((hV q).mp z))).symm

/-! ## Part 2 — the cube lists a wedge map and a run trace out

`cubesOf` and `runCubes` are the only two shapes of cube list the recursions ever manipulate, and
`++` on them is `wedgeInclL`/`wedgeInclR` on one side and `runAppend` on the other.  The `_congr`
lemmas exist because the two spellings of a cut composite (`ι ≫ g ≫ Φ` versus `(ι ≫ g) ≫ Φ`) are
`rfl`-equal but not syntactically equal, so a bare `rw` will not move between them. -/

/-- The cube list a wedge map traces out in `□ⁿ`. -/
def cubesOf (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) : CubeList n := wedgeToCubes ⟨M, χ⟩

/-- The cube list a run over `χ` traces out: one edge per bead of the run.  A run of *any*
bi-pointed set will do — it carries its own dimension sequence, so nothing forces a wedge here. -/
def runCubes {X : BPSet} (s : Run X) (χ : X.toPsh ⟶ (□n).toPsh) : CubeList n :=
  cubesOf s.dims (s.map.hom ≫ χ)

@[simp] theorem cubesOf_length (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) :
    (cubesOf M χ).length = M.length := wedgeToCubes_length M χ

@[simp] theorem cubesOf_nil (χ : (⋁([] : List ℕ+)).toPsh ⟶ (□n).toPsh) : cubesOf [] χ = [] :=
  List.eq_nil_of_length_eq_zero (by simp)

theorem cubesOf_congr {M : List ℕ+} {χ₁ χ₂ : (⋁M).toPsh ⟶ (□n).toPsh} (h : χ₁ = χ₂) :
    cubesOf M χ₁ = cubesOf M χ₂ := congrArg (cubesOf M) h

theorem runCubes_congr {X : BPSet} (s : Run X) {χ₁ χ₂ : X.toPsh ⟶ (□n).toPsh}
    (h : χ₁ = χ₂) : runCubes s χ₁ = runCubes s χ₂ := congrArg (runCubes s) h

/-- A wedge cut at a junction cuts the cube list there. -/
theorem cubesOf_append (A B : List ℕ+) (χ : (⋁(A ++ B)).toPsh ⟶ (□n).toPsh) :
    cubesOf (A ++ B) χ = cubesOf A (wedgeInclL A B ≫ χ) ++ cubesOf B (wedgeInclR A B ≫ χ) :=
  wedgeToCubes_append A B χ

/-- **`runConcat` is `++` on cube lists** — the form the bead recursion meets, where the run is cut
at a `wedge2` rather than at a list junction.  `concatChainMap_inclL/R` are the whole content. -/
theorem runCubes_concat {X Y : BPSet} (s₁ : Run X) (s₂ : Run Y)
    (χ : (wedge2 X Y).toPsh ⟶ (□n).toPsh) :
    runCubes ((runConcat X Y).obj (s₁, s₂)) χ
      = runCubes s₁ (wedgeInl X Y ≫ χ) ++ runCubes s₂ (wedgeInr X Y ≫ χ) := by
  have hL : wedgeInclL s₁.dims s₂.dims ≫ (concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ
      = s₁.map.hom ≫ wedgeInl X Y ≫ χ := by
    rw [← Category.assoc, concatChainMap_inclL X Y s₁.chain s₂.chain, Category.assoc]
  have hR : wedgeInclR s₁.dims s₂.dims ≫ (concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ
      = s₂.map.hom ≫ wedgeInr X Y ≫ χ := by
    rw [← Category.assoc, concatChainMap_inclR X Y s₁.chain s₂.chain, Category.assoc]
  change cubesOf (s₁.dims ++ s₂.dims) ((concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ) = _
  rw [cubesOf_append s₁.dims s₂.dims, hL, hR]
  rfl

/-- `runAppend` is `++` on cube lists.  `runAppend` is `concatChainMap` followed by the append
iso, so this is `wedgeToCubes_append` with each half identified by `concatChainMap_inclL/R` —
and `wedgeInclL` *is* `wedgeInl ≫ serialWedgeAppendHom`, so the second step is definitional. -/
theorem runCubes_append {A B : List ℕ+} (s₁ : Run (⋁A)) (s₂ : Run (⋁B))
    (χ : (⋁(A ++ B)).toPsh ⟶ (□n).toPsh) :
    runCubes (runAppend s₁ s₂) χ
      = runCubes s₁ (wedgeInclL A B ≫ χ) ++ runCubes s₂ (wedgeInclR A B ≫ χ) := by
  have hL : wedgeInclL s₁.dims s₂.dims
        ≫ (concatChainMap (⋁A) (⋁B) s₁.chain s₂.chain ≫ serialWedgeAppendHom A B).hom ≫ χ
      = s₁.map.hom ≫ wedgeInclL A B ≫ χ := by
    rw [comp_hom, ← Category.assoc, ← Category.assoc,
      concatChainMap_inclL (⋁A) (⋁B) s₁.chain s₂.chain]
    simp only [wedgeInclL, Category.assoc]
  have hR : wedgeInclR s₁.dims s₂.dims
        ≫ (concatChainMap (⋁A) (⋁B) s₁.chain s₂.chain ≫ serialWedgeAppendHom A B).hom ≫ χ
      = s₂.map.hom ≫ wedgeInclR A B ≫ χ := by
    rw [comp_hom, ← Category.assoc, ← Category.assoc,
      concatChainMap_inclR (⋁A) (⋁B) s₁.chain s₂.chain]
    simp only [wedgeInclR, Category.assoc]
  change cubesOf (s₁.dims ++ s₂.dims)
      ((concatChainMap (⋁A) (⋁B) s₁.chain s₂.chain ≫ serialWedgeAppendHom A B).hom ≫ χ) = _
  rw [cubesOf_append s₁.dims s₂.dims, hL, hR]
  rfl

/-! ## Part 3 — the support of a chain is read off its two endpoints

A coordinate never un-flips (`Fval_mono`), so it is flipped somewhere along a chain exactly when
it is `0` at the source vertex and `1` at the target.  This is what replaces the covering argument
of `BraidPartition` once the recursion cuts a wedge at a junction: the two halves are chains with
their own endpoints, and comparing supports across the cut costs nothing. -/

/-- A `0`-cell has no free coordinate. -/
theorem zeroCell_ne_none (v : (□n).cells 0) (p : Fin n) : (toStar v).val p ≠ none := by
  intro hv
  have hmem : p ∈ noneSet (toStar v).val := mem_noneSet.mpr hv
  rw [Finset.card_eq_zero.mp (toStar v).prop] at hmem
  simp at hmem

/-- Trichotomy for a `0`-cell's value at a coordinate. -/
theorem eq_some_false_of_ne {v : Option Bool} (h1 : v ≠ none) (h2 : ¬ v = some true) :
    v = some false := by
  cases v with
  | none => exact absurd rfl h1
  | some b => cases b with
    | true => exact absurd rfl h2
    | false => rfl

/-- **The support of a chain is its pair of endpoints.**  Taking `u = (□ⁿ).init`,
`w = (□ⁿ).final` this is the covering property of `BraidPartition`; at any other pair of
endpoints it *fails*, which is why `blockIndex` does not reach the halves of a cut. -/
theorem flips_iff_endpoints {u w : (□n).cells 0} (x : RefineObj u w) (p : Fin n) :
    Flips x.cubes p
      ↔ ((toStar u).val p = some false ∧ (toStar w).val p = some true) := by
  have hzero : vtxCanon x.cubes w 0 = u := isCubeChain_vtx_zero u w x.cubes x.isChain
  have hlast : vtxCanon x.cubes w (Fin.last x.cubes.length) = w := vtxCanon_last _ _
  constructor
  · intro hlt
    have hb : p ∈ blockOf x ⟨flipIdx x.cubes p, hlt⟩ := by
      change p ∈ noneSet (toStar (x.cubes.get ⟨flipIdx x.cubes p, hlt⟩).2).val
      rw [List.get_eq_getElem]
      exact mem_noneSet_flipIdx hlt
    set i : Fin x.cubes.length := ⟨flipIdx x.cubes p, hlt⟩ with hi
    have hcs : Fval x p i.castSucc = false := by
      simp only [Fval]; rw [toStar_junc_castSucc x i p, if_pos hb]; rfl
    have hsc : Fval x p i.succ = true := by
      simp only [Fval]; rw [toStar_junc_succ x i p, if_pos hb]; rfl
    have h0 : Fval x p 0 = false :=
      le_antisymm (hcs ▸ Fval_mono x p (Fin.zero_le _)) (Bool.false_le _)
    have hL : Fval x p (Fin.last x.cubes.length) = true :=
      le_antisymm (Bool.le_true _) (hsc ▸ Fval_mono x p (Fin.le_last _))
    simp only [Fval] at h0 hL
    rw [hzero] at h0
    rw [hlast] at hL
    exact ⟨eq_some_false_of_ne (zeroCell_ne_none u p) (of_decide_eq_false h0), of_decide_eq_true hL⟩
  · rintro ⟨hu, hw⟩
    by_contra hnl
    have hnone : ∀ i : Fin x.cubes.length, p ∉ blockOf x i := fun i hi =>
      hnl ((flips_iff_exists _ _).mpr ⟨x.cubes.get i, List.get_mem _ _, hi⟩)
    have hstep : ∀ i : Fin x.cubes.length, Fval x p i.castSucc = Fval x p i.succ := by
      intro i
      simp only [Fval]
      rw [toStar_junc_castSucc x i p, toStar_junc_succ x i p, if_neg (hnone i), if_neg (hnone i)]
    have hconst : ∀ j : Fin (x.cubes.length + 1), Fval x p j = Fval x p 0 := by
      intro j
      induction j using Fin.induction with
      | zero => rfl
      | succ k ih => rw [← hstep k]; exact ih
    have hL := hconst (Fin.last x.cubes.length)
    simp only [Fval] at hL
    rw [hzero, hlast, hu, hw] at hL
    simp at hL

/-- The chain of `□ⁿ` a wedge map traces out, with its two endpoints. -/
def wedgeRefineObj (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) :
    RefineObj (χ⟪0⟫ (⋁M).init) (χ⟪0⟫ (⋁M).final) :=
  ⟨cubesOf M χ, wedgeToCubes_isCubeChain M χ⟩

/-- `flips_iff_endpoints` for the cube list of a wedge map.  Stated separately because `rw` will
not unfold `wedgeRefineObj`'s `.cubes` projection to reach `cubesOf`. -/
theorem flips_cubesOf_iff (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (cubesOf M χ) p
      ↔ ((toStar (χ⟪0⟫ (⋁M).init)).val p = some false
          ∧ (toStar (χ⟪0⟫ (⋁M).final)).val p = some true) :=
  flips_iff_endpoints (wedgeRefineObj M χ) p

/-- Two wedge maps with the same endpoints flip the same coordinates. -/
theorem flips_congr {M₁ M₂ : List ℕ+} (χ₁ : (⋁M₁).toPsh ⟶ (□n).toPsh)
    (χ₂ : (⋁M₂).toPsh ⟶ (□n).toPsh)
    (hi : χ₁⟪0⟫ (⋁M₁).init = χ₂⟪0⟫ (⋁M₂).init)
    (hf : χ₁⟪0⟫ (⋁M₁).final = χ₂⟪0⟫ (⋁M₂).final) (p : Fin n) :
    (Flips (cubesOf M₁ χ₁) p ↔ Flips (cubesOf M₂ χ₂) p) := by
  rw [flips_cubesOf_iff M₁ χ₁ p, flips_cubesOf_iff M₂ χ₂ p, hi, hf]

/-- **Precomposing with a bi-pointed map does not change the support** — the endpoints are
preserved.  Both a refinement `⋁A ⟶ ⋁L` and a run `runObj m ⟶ ⋁L` are of this shape, so this one
statement covers every support comparison the recursions need. -/
theorem flips_precomp {M₁ M₂ : List ℕ+} (h : ⋁M₂ ⟶ ⋁M₁) (χ : (⋁M₁).toPsh ⟶ (□n).toPsh)
    (p : Fin n) : Flips (cubesOf M₂ (h.hom ≫ χ)) p ↔ Flips (cubesOf M₁ χ) p := by
  refine flips_congr _ _ ?_ ?_ p
  · rw [← comp_app_cell (rfl : h.hom ≫ χ = h.hom ≫ χ) 0 ((⋁M₂).init), h.app_init]
  · rw [← comp_app_cell (rfl : h.hom ≫ χ = h.hom ≫ χ) 0 ((⋁M₂).final), h.app_final]

/-- A run flips exactly what the wedge it runs over flips. -/
theorem flips_runCubes {M : List ℕ+} (s : Run (⋁M)) (χ : (⋁M).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (runCubes s χ) p ↔ Flips (cubesOf M χ) p :=
  flips_precomp (M₂ := s.dims) s.map χ p

/-- A chain of `□ᵏ` flips every coordinate: it runs from the all-`0` vertex to the all-`1` one. -/
theorem flips_of_cube {M : List ℕ+} {k : ℕ} (χ : ⋁M ⟶ □k) (p : Fin k) :
    Flips (cubesOf M χ.hom) p := by
  rw [flips_cubesOf_iff M χ.hom p, χ.app_init, χ.app_final,
    show (□k).init = canonicalMap (constVertex k false) from rfl,
    show (□k).final = canonicalMap (constVertex k true) from rfl,
    toStar_canonicalMap, toStar_canonicalMap]
  exact ⟨rfl, rfl⟩

/-! ## Part 4 — pushing a cube list of `□ᵏ` forward along a face

A bead of a chain of `□ⁿ` *is* a face `▫d ⟶ ▫n`, so everything that happens inside one bead is a
chain of `□ᵈ` pushed forward.  On coordinates the pushforward is `faceEmb`, and `noneSet_app` says
the free coordinates travel along it — so `flipIdx` is unchanged. -/

/-- Push a cube list of `□ᵏ` forward along a face `▫k ⟶ ▫n`. -/
def pushCubes {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) : CubeList n :=
  L.map (fun c => ⟨c.1, (c.2 : ▫((c.1 : ℕ)) ⟶ ▫k) ≫ β⟩)

@[simp] theorem pushCubes_length {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) :
    (pushCubes β L).length = L.length := List.length_map _

/-- Yoneda turns a composite of cube maps into a composite of faces. -/
theorem yonedaEquiv_comp_face {a b c : ℕ} (f : (□a).toPsh ⟶ (□b).toPsh)
    (g : (□b).toPsh ⟶ (□c).toPsh) :
    yonedaEquiv (f ≫ g) = yonedaEquiv f ≫ yonedaEquiv g :=
  (map_yonedaEquiv g (yonedaEquiv f)).symm

/-- **Free coordinates travel along `faceEmb`.** -/
theorem mem_noneSet_comp_face {k d : ℕ} (c : (□k).cells d) (β : ▫k ⟶ ▫n) (p : Fin k) :
    faceEmb β p ∈ noneSet (toStar ((c : ▫d ⟶ ▫k) ≫ β)).val ↔ p ∈ noneSet (toStar c).val := by
  rw [show toStar ((c : ▫d ⟶ ▫k) ≫ β) = act (K := stdPre n) (toStar β) (toStar c) from
      ev_comp_app c β, noneSet_app (toStar β) (toStar c)]
  exact Finset.mem_map' (nones (toStar β)).toEmbedding

/-- `flipIdx` is invariant under the pushforward. -/
theorem flipIdx_pushCubes {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) (p : Fin k) :
    flipIdx (pushCubes β L) (faceEmb β p) = flipIdx L p := by
  rw [flipIdx, pushCubes, List.findIdx_map, flipIdx]
  refine congrArg (fun q => List.findIdx q L) (funext fun c => ?_)
  simp only [Function.comp_apply, flipsAt, decide_eq_decide]
  exact mem_noneSet_comp_face c.2 β p

/-- A coordinate is flipped by a pushed-forward chain exactly when it comes from one that the
original chain flips. -/
theorem flips_pushCubes {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) (p : Fin n) :
    Flips (pushCubes β L) p ↔ ∃ p', faceEmb β p' = p ∧ Flips L p' := by
  constructor
  · intro h
    obtain ⟨c, hc, hpc⟩ := (flips_iff_exists _ _).mp h
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
    rw [show toStar ((c₀.2 : ▫((c₀.1 : ℕ)) ⟶ ▫k) ≫ β)
        = act (K := stdPre n) (toStar β) (toStar c₀.2) from ev_comp_app c₀.2 β,
      noneSet_app (toStar β) (toStar c₀.2), Finset.mem_map] at hpc
    obtain ⟨p', hp', hpe⟩ := hpc
    exact ⟨p', hpe, (flips_iff_exists _ _).mpr ⟨c₀, hc₀, hp'⟩⟩
  · rintro ⟨p', rfl, hp'⟩
    change flipIdx (pushCubes β L) (faceEmb β p') < (pushCubes β L).length
    rw [flipIdx_pushCubes, pushCubes_length]
    exact hp'

/-- **Postcomposing a wedge map with a face is the pushforward of its cube list.**  Read off
`wedgeToCubes_eq_ofFn` bead by bead, rather than by a second recursion over the wedge. -/
theorem cubesOf_comp_face (M : List ℕ+) {k : ℕ} (χ : (⋁M).toPsh ⟶ (□k).toPsh)
    (G : (□k).toPsh ⟶ (□n).toPsh) :
    cubesOf M (χ ≫ G) = pushCubes (yonedaEquiv G) (cubesOf M χ) := by
  rw [cubesOf, cubesOf, wedgeToCubes_eq_ofFn, wedgeToCubes_eq_ofFn, pushCubes, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  refine congrArg (fun z : (□n).cells ((M.get i : ℕ+) : ℕ) =>
    (⟨M.get i, z⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))) ?_
  rw [← Category.assoc]
  exact yonedaEquiv_comp_face (ιᵂ M i ≫ χ) G

/-! ## Part 5 — one bead of the source, one bead of the target

The base case.  A one-bead chain of `□ⁿ` is a face `γ : ▫e ⟶ ▫n` and everything above it is the
pushforward of a chain of `□ᵉ`, so `RunOrderFace`'s law transfers verbatim along `faceEmb γ`. -/

/-- **A one-bead chain flips exactly the coordinates in its face.** -/
theorem flips_beadChain (e : ℕ+) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (cubesOf [e] ((serialWedge1 e).hom.hom ≫ γ)) p
      ↔ ∃ p', faceEmb (yonedaEquiv γ) p' = p := by
  rw [cubesOf_comp_face [e] _ γ, flips_pushCubes]
  exact ⟨fun ⟨p', hp', _⟩ => ⟨p', hp'⟩,
    fun ⟨p', hp'⟩ => ⟨p', hp', flips_of_cube (serialWedge1 e).hom p'⟩⟩

/-- **The height of a coordinate under a run of a cube**, read through the bead's face.  A run of
`□ᵉ` is an all-edges chain of `□ᵉ` outright, so no `⋁[e] ≅ □ᵉ` conjugation survives here. -/
theorem flipIdx_cubeRun (e : ℕ) (u : Run (□e)) (γ : (□e).toPsh ⟶ (□n).toPsh) (p' : Fin e) :
    (flipIdx (runCubes u γ) (faceEmb (cubeFace γ) p') : ℤ) = cubeRunHeight u p' := by
  have hcubes : runCubes u γ = pushCubes (cubeFace γ) (wedgeToRefineObj u.chain).cubes :=
    cubesOf_comp_face u.dims u.map.hom γ
  rw [hcubes, flipIdx_pushCubes]
  exact congrArg (fun k : ℕ => (k : ℤ)) (flipIdx_eq_blockIndex (wedgeToRefineObj u.chain) p')

/-- **The base case**: restricting along a single face preserves the order of a run, read in the
ambient `□ⁿ`. -/
theorem key_face {e c : ℕ} (F : (□e).toPsh ⟶ (□c).toPsh) (Φ : (□c).toPsh ⟶ (□n).toPsh)
    (t : Run (□c)) (p' q' : Fin e) :
    (flipIdx (runCubes (runRestrictFace F t) (F ≫ Φ)) (faceEmb (cubeFace (F ≫ Φ)) p')
        < flipIdx (runCubes (runRestrictFace F t) (F ≫ Φ)) (faceEmb (cubeFace (F ≫ Φ)) q')
      ↔ flipIdx (runCubes t Φ) (faceEmb (cubeFace (F ≫ Φ)) p')
        < flipIdx (runCubes t Φ) (faceEmb (cubeFace (F ≫ Φ)) q')) := by
  have hemb : ∀ x : Fin e, faceEmb (cubeFace (F ≫ Φ)) x
      = faceEmb (cubeFace Φ) (faceEmb (cubeFace F) x) := by
    intro x
    rw [cubeFace_comp]
    exact faceEmb_comp _ _ x
  have hL : ∀ x : Fin e,
      (flipIdx (runCubes (runRestrictFace F t) (F ≫ Φ)) (faceEmb (cubeFace (F ≫ Φ)) x) : ℤ)
        = cubeRunHeight (runRestrictFace F t) x :=
    fun x => flipIdx_cubeRun e (runRestrictFace F t) (F ≫ Φ) x
  have hR : ∀ x : Fin e,
      (flipIdx (runCubes t Φ) (faceEmb (cubeFace (F ≫ Φ)) x) : ℤ)
        = cubeRunHeight t (faceEmb (cubeFace F) x) := by
    intro x
    rw [hemb x]
    exact flipIdx_cubeRun c t Φ (faceEmb (cubeFace F) x)
  rw [← Nat.cast_lt (α := ℤ), ← Nat.cast_lt (α := ℤ), hL, hL, hR, hR]
  exact cubeRunHeight_runRestrictFace_lt_iff F t p' q'

/-! ## Part 6 — the source recursion: a wedge restricted onto one bead of the target

Bead-wise.  `runRestrictWedge_cons` cuts the run at `wedgeInl`/`wedgeInr`, and `wedgeToCubes` cuts
the source chain at the very same two maps — that is its own defining recursion — so both halves
are compared along one and the same face, and the `⋁[e] ≅ □e` conjugation the block-wise cut used
to need never appears. -/

/-- Cutting the source chain at its head bead: `wedgeToCubes`'s defining recursion, with `[·] ++ ·`
for `· :: ·` so `lt_append_iff_of_tie` applies. -/
theorem cubesOf_cons (e : ℕ+) (rest : List ℕ+) (χ : (⋁(e :: rest)).toPsh ⟶ (□n).toPsh) :
    cubesOf (e :: rest) χ
      = [(⟨e, cubeFace (wedgeInl (□(e : ℕ)) (⋁rest) ≫ χ)⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))]
        ++ cubesOf rest (wedgeInr (□(e : ℕ)) (⋁rest) ≫ χ) :=  by
  simp only [cubesOf, wedgeToCubes, cubeFace, List.singleton_append, wedgeInl, wedgeInr]
  rfl

/-- `⋁[e] ≅ □e` is the right unitor, so it cancels the head inclusion. -/
theorem wedgeInl_serialWedge1 (e : ℕ+) :
    wedgeInl (□(e : ℕ)) (⋁([] : List ℕ+)) ≫ (serialWedge1 e).hom.hom
      = 𝟙 ((□(e : ℕ)).toPsh) := wedge2RightUnitPsh_inl (□(e : ℕ))

/-- The one-bead source list, presented through its own cube. -/
theorem beadCubes_eq (e : ℕ+) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) :
    [(⟨e, cubeFace γ⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))]
      = cubesOf [e] ((serialWedge1 e).hom.hom ≫ γ) := by
  rw [cubesOf_cons e [] ((serialWedge1 e).hom.hom ≫ γ), cubesOf_nil, List.append_nil]
  refine congrArg (fun u => [(⟨e, cubeFace u⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))]) ?_
  -- term mode: the composite's middle object is `wedge2 (□e) (⋁[])` on the left and `⋁[e]` on
  -- the right, so `rw [← Category.assoc]` cannot match it.
  exact (((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ γ) (wedgeInl_serialWedge1 e))).trans (Category.id_comp γ)).symm

/-- **A one-bead source chain flips exactly the coordinates in its face.** -/
theorem flips_beadCubes (e : ℕ+) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips [(⟨e, cubeFace γ⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))] p
      ↔ ∃ p', faceEmb (cubeFace γ) p' = p := by
  rw [beadCubes_eq e γ]
  exact flips_beadChain e γ p

/-- **A chain of a cube flips exactly the coordinates in the face it is pushed along.** -/
theorem flips_cubesOf_cube {M : List ℕ+} {e : ℕ} (g : ⋁M ⟶ □e)
    (γ : (□e).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (cubesOf M (g.hom ≫ γ)) p ↔ ∃ p', faceEmb (cubeFace γ) p' = p := by
  rw [show cubesOf M (g.hom ≫ γ) = pushCubes (cubeFace γ) (cubesOf M g.hom) from
    cubesOf_comp_face M g.hom γ, flips_pushCubes]
  exact ⟨fun ⟨p', hp', _⟩ => ⟨p', hp'⟩, fun ⟨p', hp'⟩ => ⟨p', hp', flips_of_cube g p'⟩⟩

/-- **A run of a cube flips exactly the coordinates in the face it is pushed along.** -/
theorem flips_runCubes_cube {e : ℕ} (u : Run (□e)) (γ : (□e).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (runCubes u γ) p ↔ ∃ p', faceEmb (cubeFace γ) p' = p :=
  flips_cubesOf_cube u.map γ p

/-- **`runRestrictWedge` preserves the order of a run inside one bead of the source.**  Recursion
on the source list, cut by `runRestrictWedge_cons`: the head bead is `key_face`, the tail is the
recursive call, and `lt_append_iff_of_tie` glues them. -/
theorem key_wedge {c : ℕ} (Φ : (□c).toPsh ⟶ (□n).toPsh) (t : Run (□c)) :
    ∀ (A : List ℕ+) (g : (⋁A).toPsh ⟶ (□c).toPsh),
      OrderAgree (cubesOf A (g ≫ Φ)) (runCubes (runRestrictWedge t A g) (g ≫ Φ)) (runCubes t Φ)
  | [], _ => orderAgree_nil (by rw [cubesOf_length]; simp)
  | e :: rest, g => by
    have hassoc : wedgeInl (□(e : ℕ)) (⋁rest) ≫ g ≫ Φ
        = (wedgeInl (□(e : ℕ)) (⋁rest) ≫ g) ≫ Φ := (Category.assoc _ _ _).symm
    have hU : runCubes (runRestrictWedge t (e :: rest) g) (g ≫ Φ)
        = runCubes (runRestrictFace (wedgeInl (□(e : ℕ)) (⋁rest) ≫ g) t)
              (wedgeInl (□(e : ℕ)) (⋁rest) ≫ g ≫ Φ)
          ++ runCubes (runRestrictWedge t rest (wedgeInr (□(e : ℕ)) (⋁rest) ≫ g))
              (wedgeInr (□(e : ℕ)) (⋁rest) ≫ g ≫ Φ) :=
      runCubes_concat _ _ (g ≫ Φ)
    rw [cubesOf_cons e rest (g ≫ Φ), hU]
    intro p q htie hfound
    refine lt_append_iff_of_tie
      (fun z => (flips_runCubes_cube _ _ z).trans (flips_beadCubes e _ z).symm) htie hfound
      (fun hp hq _ => ?_) (fun _ _ h hf => ?_)
    · -- both coordinates are flipped inside the head bead
      obtain ⟨p', rfl⟩ := (flips_beadCubes e _ p).mp hp
      obtain ⟨q', rfl⟩ := (flips_beadCubes e _ q).mp hq
      rw [runCubes_congr _ hassoc, congrArg cubeFace hassoc]
      exact key_face (wedgeInl (□(e : ℕ)) (⋁rest) ≫ g) Φ t p' q'
    · -- both coordinates are flipped in the tail
      exact key_wedge Φ t rest (wedgeInr (□(e : ℕ)) (⋁rest) ≫ g) p q h hf

/-! ## Part 7 — the target recursion

`splitWedgeMorphism` cuts a map into `⋁(c :: rest)` at the head bead: the source shape is an append
and the map is the corresponding `concatChainMap`.  `runRestrict_concatChainMap` cuts the restricted
run at that same junction and `runCubes_concat` cuts the run being restricted, so the head is
`key_wedge` for an arbitrary source into the bead's own cube — no `⋁[c] ≅ □c` conjugation, hence no
one-bead-target lemma between the two recursions. -/

/-- **Restriction preserves the order of a run inside one bead of the source.** -/
theorem key_target : ∀ (L : List ℕ+) (A : List ℕ+) (f : ⋁A ⟶ ⋁L)
    (Φ : (⋁L).toPsh ⟶ (□n).toPsh) (r : Run (⋁L)) (X U V : CubeList n),
    X = cubesOf A (f.hom ≫ Φ) →
    U = runCubes (runRestrict f r) (f.hom ≫ Φ) →
    V = runCubes r Φ →
    OrderAgree X U V
  | [], A, f, Φ, _, X, _, _, hX, _, _ => by
      subst hX
      intro p _ _ hfound
      have h2 : flipIdx (cubesOf ([] : List ℕ+) Φ) p < (cubesOf ([] : List ℕ+) Φ).length :=
        (flips_precomp f Φ p).mp hfound
      rw [cubesOf_length] at h2
      simp at h2
  | c :: rest, A, f, Φ, r, X, U, V, hX, hU, hV => by
      obtain ⟨l, m, heq, hf⟩ :=
        splitWedgeMorphism (X := □(c : ℕ)) (Y := ⋁rest) (consAltitude c rest) A f
      subst heq
      obtain rfl : f = concatChainMap (□(c : ℕ)) (⋁rest) l m := hf.trans (Category.id_comp _)
      set s₁ : Run (□(c : ℕ)) := (runSplit (consAltitude c rest) r).1
      set s₂ : Run (⋁rest) := (runSplit (consAltitude c rest) r).2
      set ΦL : (□(c : ℕ)).toPsh ⟶ (□n).toPsh := wedgeInl (□(c : ℕ)) (⋁rest) ≫ Φ
      set ΦR : (⋁rest).toPsh ⟶ (□n).toPsh := wedgeInr (□(c : ℕ)) (⋁rest) ≫ Φ
      -- the junction cocycles, in term mode: `≫`'s object slot spells the target
      -- `wedge2 (□c) (⋁rest)` where the goal spells it `⋁(c :: rest)`.
      have hLcomp : wedgeInclL l.dims m.dims
            ≫ (concatChainMap (□(c : ℕ)) (⋁rest) l m).hom ≫ Φ = l.map.hom ≫ ΦL :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ Φ) (concatChainMap_inclL (□(c : ℕ)) (⋁rest) l m))).trans
            (Category.assoc _ _ _)
      have hRcomp : wedgeInclR l.dims m.dims
            ≫ (concatChainMap (□(c : ℕ)) (⋁rest) l m).hom ≫ Φ = m.map.hom ≫ ΦR :=
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ Φ) (concatChainMap_inclR (□(c : ℕ)) (⋁rest) l m))).trans
            (Category.assoc _ _ _)
      set v₁ : Run (⋁l.dims) := runRestrictWedge s₁ l.dims l.map.hom
      set v₂ : Run (⋁m.dims) := runRestrict m.map s₂
      -- the three cube lists all split at the junction
      have hXs : X = cubesOf l.dims (l.map.hom ≫ ΦL) ++ cubesOf m.dims (m.map.hom ≫ ΦR) :=
        hX.trans ((cubesOf_append l.dims m.dims _).trans
          (congrArg₂ (· ++ ·) (cubesOf_congr hLcomp) (cubesOf_congr hRcomp)))
      have hUs : U = runCubes v₁ (l.map.hom ≫ ΦL) ++ runCubes v₂ (m.map.hom ≫ ΦR) := by
        rw [hU, runRestrict_concatChainMap]
        exact (runCubes_append v₁ v₂ _).trans
          (congrArg₂ (· ++ ·) (runCubes_congr v₁ hLcomp) (runCubes_congr v₂ hRcomp))
      have hVs : V = runCubes s₁ ΦL ++ runCubes s₂ ΦR :=
        hV.trans ((congrArg (fun z : Run (⋁(c :: rest)) => runCubes z Φ)
          (runConcat_runSplit (consAltitude c rest) r).symm).trans (runCubes_concat s₁ s₂ Φ))
      rw [hXs, hUs, hVs]
      exact OrderAgree.append (fun z => flips_runCubes v₁ (l.map.hom ≫ ΦL) z)
        (fun z => (flips_runCubes_cube s₁ ΦL z).trans (flips_cubesOf_cube l.map ΦL z).symm)
        (key_wedge ΦL s₁ l.dims l.map.hom)
        (key_target rest m.dims m.map ΦR s₂ _ _ _ rfl rfl rfl)

/-! ## Part 8 — the wall-crossing law -/

/-- A sign of a difference is determined by the two strict orders. -/
theorem sign_sub_eq_of_lt_iff {x y z w : ℤ} (h1 : x < y ↔ z < w) (h2 : y < x ↔ w < z) :
    sign (x - y) = sign (z - w) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [sign_neg (by omega), sign_neg (by have := h1.mp h; omega)]
  · have hzw : ¬ z < w := fun hc => absurd (h1.mpr hc) (by omega)
    have hwz : ¬ w < z := fun hc => absurd (h2.mpr hc) (by omega)
    rw [show x - y = 0 by omega, show z - w = 0 by omega]
  · rw [sign_pos (by omega), sign_pos (by have := h2.mp h; omega)]

/-- The covector height of a chain, as a `flipIdx`. -/
theorem chCovectorHeight_eq_flipIdx (a : Ch (□n)) (p : Fin n) :
    chCovectorHeight a p = (flipIdx (cubesOf a.dims a.map.hom) p : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ)) (flipIdx_eq_blockIndex (wedgeToRefineObj a) p).symm

/-- The height of a coordinate under a run, as a `flipIdx`. -/
theorem runHeight_eq_flipIdx (a : Ch (□n)) (s : Run (⋁a.dims)) (p : Fin n) :
    runHeight a s p = (flipIdx (runCubes s a.map.hom) p : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ))
    (flipIdx_eq_blockIndex (wedgeToRefineObj (runChain a s)) p).symm

/-- **Restriction preserves the order of the run inside one bead of `a`.** -/
theorem runHeight_lt_iff_of_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (p q : Fin n) (heq : chCovectorHeight a p = chCovectorHeight a q) :
    (runHeight a (runRestrict f.φ r) p < runHeight a (runRestrict f.φ r) q
      ↔ runHeight b r p < runHeight b r q) := by
  have hw : f.φ.hom ≫ b.map.hom = a.map.hom := by
    have h := congrArg BPSet.Hom.hom f.w; rwa [comp_hom] at h
  have hpq : flipIdx (cubesOf a.dims a.map.hom) p = flipIdx (cubesOf a.dims a.map.hom) q := by
    have h2 := heq
    rw [chCovectorHeight_eq_flipIdx, chCovectorHeight_eq_flipIdx] at h2
    exact_mod_cast h2
  have hkey := key_target b.dims a.dims f.φ b.map.hom r _ _ _
    (cubesOf_congr hw.symm) (runCubes_congr _ hw.symm) rfl p q hpq (flips_of_cube a.map p)
  rw [runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx,
    Nat.cast_lt, Nat.cast_lt]
  exact hkey

/-- **The bead-local half of the Salvetti wall-crossing law** — the hypothesis of
`wallCrossing_of_sameBlock`, discharged. -/
theorem wallCrossing_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (e : BraidGround n) (heq : chCovectorHeight a e.1.1 = chCovectorHeight a e.1.2) :
    sign (runHeight a (runRestrict f.φ r) e.1.1 - runHeight a (runRestrict f.φ r) e.1.2)
      = sign (runHeight b r e.1.1 - runHeight b r e.1.2) :=
  sign_sub_eq_of_lt_iff (runHeight_lt_iff_of_sameBlock f r e.1.1 e.1.2 heq)
    (runHeight_lt_iff_of_sameBlock f r e.1.2 e.1.1 heq.symm)

/-- **The Salvetti wall-crossing law.**  Restricting a run along `f : a ⟶ b` composes `a`'s
covector into the run's tope. -/
theorem wallCrossing {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims)) :
    braidSign (runHeight a (runRestrict f.φ r))
      = braidSign (chCovectorHeight a) ⊙ braidSign (runHeight b r) :=
  wallCrossing_of_sameBlock f r (fun e he => wallCrossing_sameBlock f r e he)

/-! ## Part 9 — the Salvetti comparison of presheaves

`runTopeEquiv` is objectwise a bijection; `wallCrossing` is exactly its naturality square, since
`salFunctor`'s restriction map *is* the wall-crossing composition `X' ⊙ ·`. -/

/-- **Runs are the Salvetti presheaf of the braid arrangement.** -/
def salLinesIso (n : ℕ) :
    Lines (□n) ≅ (chFaceEquiv n).functor ⋙ COM.salFunctor (braidCOM n) :=
  NatIso.ofComponents (fun a => Equiv.toIso (runTopeEquiv a.unop)) (by
    intro a b f
    ext r
    exact Subtype.ext (wallCrossing f.unop r))

end CubeChains
