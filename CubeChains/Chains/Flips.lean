import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.Correspondence
import CubeChains.Chains.SegalSplit
import CubeChains.Foundations.WedgeMonoidal

/-!
# Chains/Flips — which coordinates of `□ⁿ` a cube list flips, and where

A bead of a chain of `□ⁿ` flips the coordinates its cell leaves free (`blockOf`), and a coordinate
never un-flips (`Fval_mono`), so a chain flips `p` exactly when `p` is `0` at its source vertex and
`1` at its target (`flips_iff_endpoints`).  `flipIdx` (`List.findIdx`, with `length` as the
not-found sentinel) records *where*; being total on raw cube lists, it survives the cut of a wedge
at a junction, which `blockIndex` does not.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Part 0 — the `toStar` transport laws -/

/-- `toStar` intertwines a cube-map pullback with the iterated-face map: pulling `c` back along a
box morphism `φ` reads concretely as `act (toStar c) (toStar φ)`. -/
theorem toStar_map_op {dy dx : ℕ} (φ : ▫dy ⟶ ▫dx) (c : (□n).cells dx) :
    toStar ((□n).toPsh.map φ.op c)
      = act (K := stdPre n) (toStar c) (toStar (φ : (□dx).cells dy)) := by
  have h : (□n).toPsh.map φ.op c = ((□n).toPsh.cubeMap c)⟪dy⟫ φ := by
    rw [PrecubicalSet.cubeMap]
    exact (yonedaEquiv_symm_app_apply c (op ▫dy) φ).symm
  rw [h, toStar_cubeMap_app]

/-- The concrete reading of the source vertex: the free coordinates are set to `0`. -/
theorem toStar_vertex₀ {d : ℕ} (c : (□n).cells d) :
    toStar ((□n).toPsh.vertex₀ c)
      = act (K := stdPre n) (toStar c) (constVertex d false) := by
  have h : (□n).toPsh.vertex₀ c
      = ((□n).toPsh.cubeMap c)⟪0⟫ (PrecubicalSet.initVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.initVertexMap, toStar_canonicalMap]

/-- The concrete reading of the target vertex: the free coordinates are set to `1`. -/
theorem toStar_vertex₁ {d : ℕ} (c : (□n).cells d) :
    toStar ((□n).toPsh.vertex₁ c)
      = act (K := stdPre n) (toStar c) (constVertex d true) := by
  have h : (□n).toPsh.vertex₁ c
      = ((□n).toPsh.cubeMap c)⟪0⟫ (PrecubicalSet.finalVertexMap d) := rfl
  rw [h, toStar_cubeMap_app, PrecubicalSet.finalVertexMap, toStar_canonicalMap]

/-- Value of `act w (constVertex ε)`: free coordinates of `w` take `ε`, fixed ones keep `w`. -/
theorem app_constVertex_val {N d : ℕ} (w : Cell N d) (ε : Bool) (p : Fin N) :
    (act (K := stdPre N) w (constVertex d ε)).val p
      = if p ∈ noneSet w.val then some ε else w.val p := by
  rw [app_val]
  by_cases h : p ∈ noneSet w.val
  · rw [dif_pos h, if_pos h]; rfl
  · rw [dif_neg h, if_neg h]

/-! ## Part 1 — blocks and disjointness (arbitrary endpoints)

Disjointness holds for a chain between *any* two vertices of `□ⁿ`; only the junction
monotonicity of the chain is used. -/

section
variable {u w : (□n).cells 0} (x : RefineObj u w)

/-- The **block** of bead `i`: the flipped (`none`/star) coordinates of the `i`-th cube. -/
def blockOf (i : Fin x.cubes.length) : Finset (Fin n) :=
  noneSet (toStar (x.cubes.get i).2).val

/-- A bead's block carries exactly the bead's dimension many coordinates. -/
theorem blockOf_card (i : Fin x.cubes.length) :
    (blockOf x i).card = ((x.cubes.get i).1 : ℕ) :=
  (toStar (x.cubes.get i).2).prop

/-- The `p`-value of junction `i` (the source of bead `i`): `0` on the block, else fixed. -/
theorem toStar_junc_castSucc (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes w i.castSucc)).val p
      = if p ∈ blockOf x i then some false else (toStar (x.cubes.get i).2).val p := by
  rw [vtxCanon_castSucc, toStar_vertex₀]
  exact app_constVertex_val (toStar (x.cubes.get i).2) false p

/-- The `p`-value of junction `i+1` (the target of bead `i`): `1` on the block, else fixed. -/
theorem toStar_junc_succ (i : Fin x.cubes.length) (p : Fin n) :
    (toStar (vtxCanon x.cubes w i.succ)).val p
      = if p ∈ blockOf x i then some true else (toStar (x.cubes.get i).2).val p := by
  rw [← isCubeChain_vtx_tgt u w x.cubes x.isChain i, toStar_vertex₁]
  exact app_constVertex_val (toStar (x.cubes.get i).2) true p

/-- The boolean "coordinate `p` is already flipped to `1` at junction `j`". -/
def Fval (p : Fin n) : Fin (x.cubes.length + 1) → Bool :=
  fun j => decide ((toStar (vtxCanon x.cubes w j)).val p = some true)

/-- **A coordinate never un-flips.** Once flipped to `1`, it stays `1` along the chain. -/
theorem Fval_mono (p : Fin n) : Monotone (Fval x p) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  by_cases hb : p ∈ blockOf x i
  · have hcs : Fval x p i.castSucc = false := by
      simp only [Fval]; rw [toStar_junc_castSucc x i p, if_pos hb]; rfl
    rw [hcs]; exact Bool.false_le _
  · have heq : Fval x p i.castSucc = Fval x p i.succ := by
      simp only [Fval]
      rw [toStar_junc_castSucc x i p, toStar_junc_succ x i p, if_neg hb, if_neg hb]
    exact le_of_eq heq

/-- **Blocks of distinct beads are disjoint** (in chain order): a coordinate flips at most once. -/
theorem blockOf_disjoint {i j : Fin x.cubes.length} (hij : i < j) :
    Disjoint (blockOf x i) (blockOf x j) := by
  rw [Finset.disjoint_left]
  intro p hi hj
  have h1 : Fval x p i.succ = true := by
    simp only [Fval]; rw [toStar_junc_succ x i p, if_pos hi]; rfl
  have h2 : Fval x p j.castSucc = false := by
    simp only [Fval]; rw [toStar_junc_castSucc x j p, if_pos hj]; rfl
  have hle : i.succ ≤ j.castSucc := by
    have hlt : (i : ℕ) < (j : ℕ) := hij
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
  have hmono := Fval_mono x p hle
  rw [h1, h2] at hmono
  exact absurd hmono (by decide)

/-- A coordinate lies in at most one block. -/
theorem blockOf_unique {i j : Fin x.cubes.length} {p : Fin n}
    (hi : p ∈ blockOf x i) (hj : p ∈ blockOf x j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hj (Finset.disjoint_left.mp (blockOf_disjoint x h) hi)
  · exact h
  · exact absurd hi (Finset.disjoint_left.mp (blockOf_disjoint x h) hj)

end

/-! ## Part 2 — the face classifying a map of cubes -/

/-- **The face classifying a map of cubes.**  `(□a).toPsh = yoneda.obj ▫a`, so Yoneda reads a
presheaf map between cubes as a map of boxes.

A wrapper, not `yonedaEquiv` inlined: under `yonedaEquiv` the source is spelled `yoneda.obj ▫a`,
while every composite the wedge recursion builds is spelled `(□a).toPsh`.  `rw`'s keyed matching
sees the two as distinct, so an inlined `yonedaEquiv` makes its own argument unrewritable. -/
def cubeFace {a b : ℕ} (f : (□a).toPsh ⟶ (□b).toPsh) : ▫a ⟶ ▫b := yonedaEquiv f

@[simp] theorem cubeFace_id (a : ℕ) : cubeFace (𝟙 ((□a).toPsh)) = 𝟙 (▫a) := rfl

/-! ## Part 3 — `flipIdx`: the position at which a cube list flips a coordinate

Defined on a raw list of cubes, with no chain condition, so that it survives the cut of a wedge
at a junction.  `List.findIdx` gives the append law for nothing. -/

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

/-- **`flipIdx` reads off the block.**  A coordinate lies in at most one block, so the first bead
that flips it is the only one. -/
theorem flipIdx_eq_of_mem_blockOf {u w : (□n).cells 0} (x : RefineObj u w)
    (i : Fin x.cubes.length) {p : Fin n} (h : p ∈ blockOf x i) : flipIdx x.cubes p = i.val := by
  have hf : Flips x.cubes p :=
    (flips_iff_exists _ _).mpr ⟨x.cubes.get i, List.get_mem _ _, h⟩
  have h2 : p ∈ blockOf x ⟨flipIdx x.cubes p, hf⟩ := by
    change p ∈ noneSet (toStar (x.cubes.get ⟨flipIdx x.cubes p, hf⟩).2).val
    rw [List.get_eq_getElem]
    exact mem_noneSet_flipIdx hf
  exact congrArg Fin.val (blockOf_unique x h2 h)

/-! ## Part 4 — the append calculus

Cube lists under `++` are a monoid and `flipIdx` reads it: found in the first half, or shifted
past it.  `List.findIdx` gives all three laws for nothing. -/

/-- `flipIdx` over an append: found in the first half, or shifted past it. -/
theorem flipIdx_append (L₁ L₂ : CubeList n) (p : Fin n) :
    flipIdx (L₁ ++ L₂) p = if Flips L₁ p then flipIdx L₁ p else flipIdx L₂ p + L₁.length :=
  List.findIdx_append

theorem flipIdx_append_left {L₁ L₂ : CubeList n} {p : Fin n} (h : Flips L₁ p) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₁ p := by rw [flipIdx_append, if_pos h]

theorem flipIdx_append_right {L₁ L₂ : CubeList n} {p : Fin n} (h : ¬ Flips L₁ p) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₂ p + L₁.length := by rw [flipIdx_append, if_neg h]


/-! ## Part 5 — the cube list a wedge map traces out

`++` on `cubesOf` is `wedgeInclL`/`wedgeInclR`. -/

/-- The cube list a wedge map traces out in `□ⁿ`. -/
def cubesOf (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) : CubeList n := wedgeToCubes ⟨M, χ⟩

@[simp] theorem cubesOf_length (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) :
    (cubesOf M χ).length = M.length := wedgeToCubes_length M χ

@[simp] theorem cubesOf_nil (χ : (⋁([] : List ℕ+)).toPsh ⟶ (□n).toPsh) : cubesOf [] χ = [] :=
  List.eq_nil_of_length_eq_zero (by simp)

/-- A wedge cut at a junction cuts the cube list there. -/
theorem cubesOf_append (A B : List ℕ+) (χ : (⋁(A ++ B)).toPsh ⟶ (□n).toPsh) :
    cubesOf (A ++ B) χ = cubesOf A (wedgeInclL A B ≫ χ) ++ cubesOf B (wedgeInclR A B ≫ χ) :=
  wedgeToCubes_append A B χ

/-! ## Part 6 — the support of a chain is read off its two endpoints

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

/-- The source vertex of `□ⁿ` is `0` at every coordinate. -/
theorem toStar_cube_init_val (p : Fin n) : (toStar ((□n).init)).val p = some false := by
  rw [show (□n).init = canonicalMap (constVertex n false) from rfl, toStar_canonicalMap]
  rfl

/-- The target vertex of `□ⁿ` is `1` at every coordinate. -/
theorem toStar_cube_final_val (p : Fin n) : (toStar ((□n).final)).val p = some true := by
  rw [show (□n).final = canonicalMap (constVertex n true) from rfl, toStar_canonicalMap]
  rfl

/-- **A chain of `□ⁿ` between its two vertices flips every coordinate.**  Both readings of "a
chain of the cube" — a `RefineObj` on `init`/`final`, and a bi-pointed map out of a wedge — are
this one endpoint computation. -/
theorem flips_of_init_final (x : RefineObj (□n).init (□n).final) (p : Fin n) : Flips x.cubes p :=
  (flips_iff_endpoints x p).mpr ⟨toStar_cube_init_val p, toStar_cube_final_val p⟩

/-- A chain of `□ᵏ` flips every coordinate: it runs from the all-`0` vertex to the all-`1` one. -/
theorem flips_of_cube {M : List ℕ+} {k : ℕ} (χ : ⋁M ⟶ □k) (p : Fin k) :
    Flips (cubesOf M χ.hom) p := by
  rw [flips_cubesOf_iff M χ.hom p, χ.app_init, χ.app_final]
  exact ⟨toStar_cube_init_val p, toStar_cube_final_val p⟩

/-! ## Part 7 — pushing a cube list of `□ᵏ` forward along a face

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


/-- **A chain of a cube flips exactly the coordinates in the face it is pushed along.** -/
theorem flips_cubesOf_cube {M : List ℕ+} {e : ℕ} (g : ⋁M ⟶ □e)
    (γ : (□e).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (cubesOf M (g.hom ≫ γ)) p ↔ ∃ p', faceEmb (cubeFace γ) p' = p := by
  rw [show cubesOf M (g.hom ≫ γ) = pushCubes (cubeFace γ) (cubesOf M g.hom) from
    cubesOf_comp_face M g.hom γ, flips_pushCubes]
  exact ⟨fun ⟨p', hp', _⟩ => ⟨p', hp'⟩, fun ⟨p', hp'⟩ => ⟨p', hp', flips_of_cube g p'⟩⟩

end CubeChains
