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

/-- The cube list a run over `χ` traces out: one edge per bead of the run. -/
def runCubes {M : List ℕ+} (s : Run M) (χ : (⋁M).toPsh ⟶ (□n).toPsh) : CubeList n :=
  cubesOf (𝟙^(dimSum M)) (s.hom ≫ χ)

@[simp] theorem cubesOf_length (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) :
    (cubesOf M χ).length = M.length := wedgeToCubes_length M χ

theorem cubesOf_congr {M : List ℕ+} {χ₁ χ₂ : (⋁M).toPsh ⟶ (□n).toPsh} (h : χ₁ = χ₂) :
    cubesOf M χ₁ = cubesOf M χ₂ := congrArg (cubesOf M) h

theorem runCubes_congr {M : List ℕ+} (s : Run M) {χ₁ χ₂ : (⋁M).toPsh ⟶ (□n).toPsh}
    (h : χ₁ = χ₂) : runCubes s χ₁ = runCubes s χ₂ := congrArg (runCubes s) h

/-- Cancelling the one-bead comparison `⋁[c] ≅ □c` at presheaf level. -/
theorem serialWedge1_hom_inv (c : ℕ+) :
    (serialWedge1 c).hom.hom ≫ (serialWedge1 c).inv.hom = 𝟙 ((⋁[c]).toPsh) :=
  congrArg BPSet.Hom.hom (serialWedge1 c).hom_inv_id

/-- A wedge cut at a junction cuts the cube list there. -/
theorem cubesOf_append (A B : List ℕ+) (χ : (⋁(A ++ B)).toPsh ⟶ (□n).toPsh) :
    cubesOf (A ++ B) χ = cubesOf A (wedgeInclL A B ≫ χ) ++ cubesOf B (wedgeInclR A B ≫ χ) :=
  wedgeToCubes_append A B χ

/-- `runAppend` is `++` on cube lists. -/
theorem runCubes_append {A B : List ℕ+} (s₁ : Run A) (s₂ : Run B)
    (χ : (⋁(A ++ B)).toPsh ⟶ (□n).toPsh) :
    runCubes (runAppend s₁ s₂) χ
      = runCubes s₁ (wedgeInclL A B ≫ χ) ++ runCubes s₂ (wedgeInclR A B ≫ χ) :=
  wedgeToCubes_runAppend (K := □n) A B s₁ s₂ χ

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
theorem flips_runCubes {M : List ℕ+} (s : Run M) (χ : (⋁M).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (runCubes s χ) p ↔ Flips (cubesOf M χ) p :=
  flips_precomp (M₂ := 𝟙^(dimSum M)) s χ p

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

/-- **The height of a coordinate under a one-bead run** is the run's own `runHeight`, read through
the bead's face. -/
theorem flipIdx_beadRun (e : ℕ+) (u : Run [e]) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh)
    (p' : Fin (e : ℕ)) :
    (flipIdx (runCubes u ((serialWedge1 e).hom.hom ≫ γ)) (faceEmb (yonedaEquiv γ) p') : ℤ)
      = runHeight (beadCh e) u p' := by
  have hcubes : runCubes u ((serialWedge1 e).hom.hom ≫ γ)
      = pushCubes (yonedaEquiv γ) (wedgeToRefineObj (runChain (beadCh e) u)).cubes :=
    (cubesOf_congr (Category.assoc u.hom (serialWedge1 e).hom.hom γ).symm).trans
      (cubesOf_comp_face (𝟙^(dimSum [e])) (u.hom ≫ (serialWedge1 e).hom.hom) γ)
  rw [hcubes, flipIdx_pushCubes]
  exact congrArg (fun k : ℕ => (k : ℤ))
    (flipIdx_eq_blockIndex (wedgeToRefineObj (runChain (beadCh e) u)) p')

/-- **The base case**: restricting along a single face preserves the order of a run, read in the
ambient `□ⁿ`. -/
theorem key_face {e c : ℕ+} (F : (□(e : ℕ)).toPsh ⟶ (□(c : ℕ)).toPsh)
    (Φ : (□(c : ℕ)).toPsh ⟶ (□n).toPsh) (t : Run [c]) (p' q' : Fin (e : ℕ)) :
    (flipIdx (runCubes (runRestrictFace F t) ((serialWedge1 e).hom.hom ≫ F ≫ Φ))
          (faceEmb (yonedaEquiv (F ≫ Φ)) p')
        < flipIdx (runCubes (runRestrictFace F t) ((serialWedge1 e).hom.hom ≫ F ≫ Φ))
          (faceEmb (yonedaEquiv (F ≫ Φ)) q')
      ↔ flipIdx (runCubes t ((serialWedge1 c).hom.hom ≫ Φ)) (faceEmb (yonedaEquiv (F ≫ Φ)) p')
        < flipIdx (runCubes t ((serialWedge1 c).hom.hom ≫ Φ))
            (faceEmb (yonedaEquiv (F ≫ Φ)) q')) := by
  have hemb : ∀ x : Fin (e : ℕ), faceEmb (yonedaEquiv (F ≫ Φ)) x
      = faceEmb (yonedaEquiv Φ) (faceEmb (yonedaEquiv F) x) := by
    intro x
    rw [yonedaEquiv_comp_face F Φ]
    exact faceEmb_comp _ _ x
  have hL : ∀ x : Fin (e : ℕ),
      (flipIdx (runCubes (runRestrictFace F t) ((serialWedge1 e).hom.hom ≫ F ≫ Φ))
          (faceEmb (yonedaEquiv (F ≫ Φ)) x) : ℤ)
        = runHeight (beadCh e) (runRestrictFace F t) x :=
    fun x => flipIdx_beadRun e (runRestrictFace F t) (F ≫ Φ) x
  have hR : ∀ x : Fin (e : ℕ),
      (flipIdx (runCubes t ((serialWedge1 c).hom.hom ≫ Φ))
          (faceEmb (yonedaEquiv (F ≫ Φ)) x) : ℤ)
        = runHeight (beadCh c) t (faceEmb (yonedaEquiv F) x) := by
    intro x
    rw [hemb x]
    exact flipIdx_beadRun c t Φ (faceEmb (yonedaEquiv F) x)
  rw [← Nat.cast_lt (α := ℤ), ← Nat.cast_lt (α := ℤ), hL, hL, hR, hR]
  exact runHeight_runRestrictFace_lt_iff F t p' q'

/-! ## Part 6 — the source recursion: a wedge restricted onto one bead of the target

The three cube lists are *parameters* with defining equations rather than literal terms in the
statement.  A cut composite has two `rfl`-equal but syntactically different spellings
(`ι ≫ g ≫ Φ` versus `(ι ≫ g) ≫ Φ`, `runObj m` versus `⋁(𝟙^m)`), and `rw` sees through neither;
against a plain variable it always does. -/

/-- **`runRestrictWedge` preserves the order of a run inside one bead of the source.**  Recursion
on the source list, cut by `runRestrictWedge_cons`: the head bead is `key_face`, the tail is the
recursive call, and `lt_append_iff_of_tie` glues them. -/
theorem key_wedge : ∀ (A : List ℕ+) (c : ℕ+) (g : (⋁A).toPsh ⟶ (□(c : ℕ)).toPsh)
    (Φ : (□(c : ℕ)).toPsh ⟶ (□n).toPsh) (t : Run [c]) (X U V : CubeList n),
    X = cubesOf A (g ≫ Φ) →
    U = runCubes (runRestrictWedge A g t) (g ≫ Φ) →
    V = runCubes t ((serialWedge1 c).hom.hom ≫ Φ) →
    OrderAgree X U V
  | [], c, g, Φ, t, X, U, V, hX, _, _ =>
      orderAgree_nil (by rw [hX, cubesOf_length]; simp)
  | e :: rest, c, g, Φ, t, X, U, V, hX, hU, hV => by
    set F : (□(e : ℕ)).toPsh ⟶ (□(c : ℕ)).toPsh :=
      (serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g with hF
    set u₁ : Run [e] := runRestrictFace F t
    set u₂ : Run rest := runRestrictWedge rest (wedgeInclR [e] rest ≫ g) t
    set ψL : (⋁[e]).toPsh ⟶ (□n).toPsh := wedgeInclL [e] rest ≫ g ≫ Φ with hψL
    set ψR : (⋁rest).toPsh ⟶ (□n).toPsh := wedgeInclR [e] rest ≫ g ≫ Φ
    -- the source chain and the restricted run both split at the junction
    have hXs : X = cubesOf [e] ψL ++ cubesOf rest ψR :=
      hX.trans (cubesOf_append [e] rest (g ≫ Φ))
    have hUs : U = runCubes u₁ ψL ++ runCubes u₂ ψR :=
      hU.trans (runCubes_append u₁ u₂ (g ≫ Φ))
    -- the head bead, presented through its own cube
    have hcancel : (serialWedge1 e).hom.hom ≫ F ≫ Φ = ψL := by
      rw [hF, hψL, show ((serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g) ≫ Φ
          = (serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g ≫ Φ by
            simp only [Category.assoc], ← Category.assoc, serialWedge1_hom_inv e,
        Category.id_comp]
    rw [hXs, hUs, hV]
    intro p q htie hfound
    refine lt_append_iff_of_tie (fun z => flips_runCubes u₁ ψL z) htie hfound
      (fun hp hq _ => ?_) (fun _ _ h hf => ?_)
    · -- both coordinates are flipped inside the head bead
      obtain ⟨p', hp'⟩ := (flips_beadChain e (F ≫ Φ) p).mp (cubesOf_congr hcancel.symm ▸ hp)
      obtain ⟨q', hq'⟩ := (flips_beadChain e (F ≫ Φ) q).mp (cubesOf_congr hcancel.symm ▸ hq)
      subst hp'
      subst hq'
      rw [runCubes_congr u₁ hcancel.symm]
      exact key_face F Φ t p' q'
    · -- both coordinates are flipped in the tail
      exact key_wedge rest c (wedgeInclR [e] rest ≫ g) Φ t _ _ _ rfl rfl rfl p q h hf

/-! ## Part 7 — one bead of the target, an arbitrary source -/

/-- `key_wedge` transported across `runRestrict_singleton`: the one-bead target, spelled with the
bi-pointed `f : ⋁A ⟶ ⋁[c]` that the target recursion produces. -/
theorem key_singleton (A : List ℕ+) (c : ℕ+) (f : ⋁A ⟶ ⋁[c])
    (Φ : (⋁[c]).toPsh ⟶ (□n).toPsh) (t : Run [c]) (X U V : CubeList n)
    (hX : X = cubesOf A (f.hom ≫ Φ))
    (hU : U = runCubes (runRestrict [c] A f t) (f.hom ≫ Φ))
    (hV : V = runCubes t Φ) :
    OrderAgree X U V := by
  have hgΦ : (f.hom ≫ (serialWedge1 c).hom.hom) ≫ ((serialWedge1 c).inv.hom ≫ Φ)
      = f.hom ≫ Φ := by
    rw [Category.assoc, ← Category.assoc ((serialWedge1 c).hom.hom), serialWedge1_hom_inv c,
      Category.id_comp]
  have htΦ : (serialWedge1 c).hom.hom ≫ (serialWedge1 c).inv.hom ≫ Φ = Φ := by
    rw [← Category.assoc, serialWedge1_hom_inv c, Category.id_comp]
  refine key_wedge A c (f.hom ≫ (serialWedge1 c).hom.hom) ((serialWedge1 c).inv.hom ≫ Φ) t
    X U V (hX.trans (cubesOf_congr hgΦ.symm)) ?_ (hV.trans (runCubes_congr t htΦ.symm))
  rw [hU, runRestrict_singleton f t]
  exact runCubes_congr _ hgΦ.symm

/-! ## Part 8 — the target recursion -/

/-- **Restriction preserves the order of a run inside one bead of the source.**  Recursion on the
target list: `wedge_split_tensor` cuts `f` at the head bead, `runRestrict_tensor'` cuts the
restricted run there too, `key_singleton` handles the head and `OrderAgree.append` glues. -/
theorem key_target : ∀ (L : List ℕ+) (A : List ℕ+) (f : ⋁A ⟶ ⋁L)
    (Φ : (⋁L).toPsh ⟶ (□n).toPsh) (r : Run L) (X U V : CubeList n),
    X = cubesOf A (f.hom ≫ Φ) →
    U = runCubes (runRestrict L A f r) (f.hom ≫ Φ) →
    V = runCubes r Φ →
    OrderAgree X U V
  | [], A, f, Φ, r, X, U, V, hX, _, _ =>
      have hA : A = [] := eq_nil_of_dimSum_zero (serialWedge_dimSum_eq f)
      orderAgree_nil (by rw [hX, cubesOf_length, hA]; simp)
  | c :: rest, A, f, Φ, r, X, U, V, hX, hU, hV => by
      obtain ⟨A₁, A₂, ha, f₁, f₂, hf⟩ := wedge_split_tensor [c] rest f
      subst ha
      have hf' : f = wedgeTensor f₁ f₂ := hf.trans (Category.id_comp _)
      subst hf'
      set s₁ : Run [c] := (Run.split r).1
      set s₂ : Run rest := (Run.split r).2
      set ΦL : (⋁[c]).toPsh ⟶ (□n).toPsh := wedgeInclL [c] rest ≫ Φ
      set ΦR : (⋁rest).toPsh ⟶ (□n).toPsh := wedgeInclR [c] rest ≫ Φ
      set v₁ : Run A₁ := runRestrict [c] A₁ f₁ s₁
      set v₂ : Run A₂ := runRestrict rest A₂ f₂ s₂
      have hLcomp : wedgeInclL A₁ A₂ ≫ (wedgeTensor f₁ f₂).hom ≫ Φ = f₁.hom ≫ ΦL := by
        rw [← Category.assoc, wedgeTensor_inclL, Category.assoc]
      have hRcomp : wedgeInclR A₁ A₂ ≫ (wedgeTensor f₁ f₂).hom ≫ Φ = f₂.hom ≫ ΦR := by
        rw [← Category.assoc, wedgeTensor_inclR, Category.assoc]
      -- the three cube lists all split at the junction
      have hXs : X = cubesOf A₁ (f₁.hom ≫ ΦL) ++ cubesOf A₂ (f₂.hom ≫ ΦR) :=
        hX.trans ((cubesOf_append A₁ A₂ _).trans
          (congrArg₂ (· ++ ·) (cubesOf_congr hLcomp) (cubesOf_congr hRcomp)))
      have hUs : U = runCubes v₁ (f₁.hom ≫ ΦL) ++ runCubes v₂ (f₂.hom ≫ ΦR) := by
        rw [hU, ← runAppend_split r, runRestrict_tensor' f₁ f₂ s₁ s₂]
        exact (runCubes_append v₁ v₂ _).trans
          (congrArg₂ (· ++ ·) (runCubes_congr v₁ hLcomp) (runCubes_congr v₂ hRcomp))
      have hVs : V = runCubes s₁ ΦL ++ runCubes s₂ ΦR := by
        rw [hV, ← runAppend_split r]
        exact runCubes_append s₁ s₂ Φ
      rw [hXs, hUs, hVs]
      exact OrderAgree.append (fun z => flips_runCubes v₁ (f₁.hom ≫ ΦL) z)
        (fun z => (flips_runCubes s₁ ΦL z).trans (flips_precomp f₁ ΦL z).symm)
        (key_singleton A₁ c f₁ ΦL s₁ _ _ _ rfl rfl rfl)
        (key_target rest A₂ f₂ ΦR s₂ _ _ _ rfl rfl rfl)

/-! ## Part 9 — the wall-crossing law -/

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
theorem runHeight_eq_flipIdx (a : Ch (□n)) (s : Run a.dims) (p : Fin n) :
    runHeight a s p = (flipIdx (runCubes s a.map.hom) p : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ))
    (flipIdx_eq_blockIndex (wedgeToRefineObj (runChain a s)) p).symm

/-- **Restriction preserves the order of the run inside one bead of `a`.** -/
theorem runHeight_lt_iff_of_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims)
    (p q : Fin n) (heq : chCovectorHeight a p = chCovectorHeight a q) :
    (runHeight a (runRestrict b.dims a.dims f.φ r) p
        < runHeight a (runRestrict b.dims a.dims f.φ r) q
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
theorem wallCrossing_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims)
    (e : BraidGround n) (heq : chCovectorHeight a e.1.1 = chCovectorHeight a e.1.2) :
    sign (runHeight a (runRestrict b.dims a.dims f.φ r) e.1.1
          - runHeight a (runRestrict b.dims a.dims f.φ r) e.1.2)
      = sign (runHeight b r e.1.1 - runHeight b r e.1.2) :=
  sign_sub_eq_of_lt_iff (runHeight_lt_iff_of_sameBlock f r e.1.1 e.1.2 heq)
    (runHeight_lt_iff_of_sameBlock f r e.1.2 e.1.1 heq.symm)

/-- **The Salvetti wall-crossing law.**  Restricting a run along `f : a ⟶ b` composes `a`'s
covector into the run's tope. -/
theorem wallCrossing {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims) :
    braidSign (runHeight a (runRestrict b.dims a.dims f.φ r))
      = braidSign (chCovectorHeight a) ⊙ braidSign (runHeight b r) :=
  wallCrossing_of_sameBlock f r (fun e he => wallCrossing_sameBlock f r e he)

/-! ## Part 10 — the Salvetti comparison of presheaves

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
