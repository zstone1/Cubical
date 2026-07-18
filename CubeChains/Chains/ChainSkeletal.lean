import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.Correspondence
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Chains/ChainSkeletal — `Ch(K)` is an acyclic, skeletal category

For **every** bi-pointed precubical set `K`, the cube-chain category `Ch(K)` has only identity
endomorphisms and is skeletal — no `NonSelfLinked`, no `AdmitsAltitude K`, no thinness.  The proof
uses only the serial wedge's own `trueCount` prefix-sum altitude (`serialWedge_admitsAltitude`),
which always exists.

* `serialWedge_bipointed_endo_id` — every bi-pointed endomorphism of a serial wedge is the identity.
* `ChainCat.endo_eq_id` — every endomorphism of `Ch(K)` is the identity.
* `ChainCat.eq_of_hom_hom` — `Ch(K)` is skeletal: `a ⟶ b` and `b ⟶ a` force `a = b`.
* `ChainCat.lt_dims_length_of_not_isIso` — a proper coarsening strictly drops the bead count.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet

namespace CubeChain

/-! ### Altitude of a bead read off a wedge map -/

/-- The altitude of the `k`-th read-off cube of a wedge map `hom : ⋁ed ⟶ ⋁cd`
whose source-init lands on `cd`'s init: it is the dimension prefix-sum of the earlier
cubes.  A packaging of `isCubeChain_alt_get` through `wedgeToCubes_get`. -/
theorem serialWedge_bead_alt {ed cd : List ℕ+}
    (alt : ∀ n, (⋁cd).cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude (⋁cd).toPsh alt)
    (h0 : alt 0 (⋁cd).init = 0)
    (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (q : (⋁cd).cells 0)
    (hci : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ed, hom⟩) q)
    (k : Fin ed.length) :
    alt (ed.get k : ℕ) (yonedaEquiv (ιᵂ ed k ≫ hom))
      = dimPrefixSum (wedgeToCubes ⟨ed, hom⟩) k.val := by
  have hlt : k.val < (wedgeToCubes ⟨ed, hom⟩).length := by
    rw [wedgeToCubes_length]; exact k.isLt
  have hcast : (⟨k.val, hlt⟩ : Fin (wedgeToCubes ⟨ed, hom⟩).length).cast
      (wedgeToCubes_length ed hom) = k := Fin.ext rfl
  have hget := wedgeToCubes_get ed hom ⟨k.val, hlt⟩
  have hg := isCubeChain_alt_get alt hax (wedgeToCubes ⟨ed, hom⟩)
    (⋁cd).init q hci k.val hlt
  rw [h0, zero_add] at hg
  rw [hget, hcast] at hg
  exact hg

/-! ### Block prefix-sum bounds (only the serial wedge's altitude) -/

/-- **Prefix-sum sandwich for `blockIdx`.**  For a wedge map `φ : ⋁ad ⟶ ⋁cd`
sending `ad`-init to `cd`-init, the block of source bead `i` (`blockIdx φ i`) is pinned
by the dimension prefix sums: its `cd`-prefix is `≤` bead `i`'s `ad`-prefix, which in
turn is `<` the next `cd`-prefix.  Uses **only** `serialWedge_admitsAltitude cd`. -/
theorem serialWedge_blockIdx_prefix_bound {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (blockIdx φ i).val
        ≤ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      ∧ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
        < dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
            ((blockIdx φ i).val + 1) := by
  obtain ⟨alt, hax, h0⟩ := serialWedge_admitsAltitude cd
  -- The taut (identity) chain of `⋁cd`.
  have hciT : IsCubeChain (⋁cd).init
      (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (⋁cd).final := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) cd
      (𝟙 (⋁cd).toPsh)
    simpa using h
  -- The pushed chain (`φ` read off) in `⋁cd`.
  have hciP : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ad, φ⟩)
      (φ⟪0⟫ (⋁ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) ad φ
    rwa [hinit] at h
  -- Bead altitudes.
  have hP_i := serialWedge_bead_alt alt hax h0 φ _ hciP i
  have hT_j := serialWedge_bead_alt alt hax h0 (𝟙 (⋁cd).toPsh) _ hciT
    (blockIdx φ i)
  rw [Category.comp_id] at hT_j
  -- The pushed bead `i` is the `cd`-bead `blockIdx φ i` pulled back along `blockFace φ i`.
  have hce : yonedaEquiv (ιᵂ ad i ≫ φ)
      = (⋁cd).toPsh.map (blockFace φ i).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ i))) :=
    (congrArg yonedaEquiv (blockFace_spec φ i)).trans
      (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ i)) (blockFace φ i)).symm
  have hc := PrecubicalSet.alt_cubeMap alt hax
    (yonedaEquiv (ιᵂ cd (blockIdx φ i))) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  -- The key equation of prefix sums.
  have haltrel : dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      = dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (blockIdx φ i).val
        + (trueCount (ev (blockFace φ i)) : ℤ) := by
    rw [← hP_i, ← hT_j, hce]; exact hc
  -- The `(blockIdx φ i)`-th successor of the taut prefix sum.
  have hjlt : (blockIdx φ i).val < (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).length := by
    rw [wedgeToCubes_length]; exact (blockIdx φ i).isLt
  have hgetfst : ((wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).get
      ⟨(blockIdx φ i).val, hjlt⟩).1 = cd.get (blockIdx φ i) := by
    rw [wedgeToCubes_get]; exact congrArg cd.get (Fin.ext rfl)
  have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) hjlt
  rw [hgetfst] at hsucc
  -- trueCount bounds: `0 ≤ tc < cd.get (blockIdx φ i)`.
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    cells_card_le (ev (blockFace φ i))
  have htle : trueCount (ev (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    trueCount_le (ev (blockFace φ i))
  have hipos : 0 < (ad.get i : ℕ) := (ad.get i).2
  have htN : trueCount (ev (blockFace φ i)) < (cd.get (blockIdx φ i) : ℕ) := by
    omega
  have htlt : (trueCount (ev (blockFace φ i)) : ℤ)
      < ((cd.get (blockIdx φ i) : ℕ) : ℤ) := by exact_mod_cast htN
  have hnn : (0 : ℤ) ≤ (trueCount (ev (blockFace φ i)) : ℤ) :=
    Int.natCast_nonneg _
  refine ⟨by omega, ?_⟩
  rw [hsucc]
  omega

/-! ### The core rigidity lemma -/

/-- **Every bi-pointed endomorphism of a serial wedge is the identity.**

For each bead `i`, `blockIdx φ i = i` (the prefix-sum sandwich collapses since both chains
have dimension list `dims`), so bead `i`'s image is a *full-dimensional* `Box`-face of bead
`i`, hence the identity face — thus `ι_i ≫ φ = ι_i`.  `serialWedge_hom_ext` then gives
`φ = 𝟙`.  Uses only the serial wedge's altitude. -/
theorem serialWedge_bipointed_endo_id (dims : List ℕ+)
    (φ : ⋁dims ⟶ ⋁dims) :
    φ = 𝟙 (⋁dims) := by
  -- Same dimension list on both sides ⟹ the two prefix sums coincide.
  have hdps : ∀ n : ℕ, dimPrefixSum (wedgeToCubes ⟨dims, φ.hom⟩) n
      = dimPrefixSum (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩) n := by
    intro n
    have hmap : (wedgeToCubes ⟨dims, φ.hom⟩).map (·.1)
        = (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩).map (·.1) := by
      rw [wedgeToCubes_dims, wedgeToCubes_dims]
    have key : (wedgeToCubes ⟨dims, φ.hom⟩).map (fun x => (x.1 : ℕ))
        = (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩).map (fun x => (x.1 : ℕ)) := by
      rw [show (fun x : Σ n : ℕ+, (⋁dims).cells (n : ℕ) => (x.1 : ℕ))
            = (fun p : ℕ+ => (p : ℕ)) ∘ (fun x => x.1) from rfl,
          ← List.map_map, ← List.map_map, hmap]
    simp only [dimPrefixSum]
    rw [List.map_take, List.map_take, key]
  -- The block-agreement, per bead.
  have hblock : ∀ i : Fin dims.length,
      ιᵂ dims i ≫ φ.hom = ιᵂ dims i := by
    intro i
    obtain ⟨r, incl, hincl⟩ := wedgeMap_block φ.hom i
    have hbound := serialWedge_blockIdx_prefix_bound φ.hom φ.app_init i
    rw [hdps] at hbound
    obtain ⟨hb1, hb2⟩ := hbound
    -- The sandwich pins `blockIdx φ.hom i = i`.
    have hilt : i.val < (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩).length := by
      rw [wedgeToCubes_length]; exact i.isLt
    have hidx : blockIdx φ.hom i = i := by
      by_contra hne
      rcases Nat.lt_or_ge (blockIdx φ.hom i).val i.val with hlt | hge
      · -- blockIdx < i : then `PT(blockIdx+1) ≤ PT(i)`, contradicting the strict bound.
        have hmono := dimPrefixSum_mono
          (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩)
          (show (blockIdx φ.hom i).val + 1 ≤ i.val by omega)
        omega
      · -- blockIdx ≥ i, but ≠ i, so blockIdx > i : `PT(i+1) ≤ PT(blockIdx)`.
        have hgt : i.val < (blockIdx φ.hom i).val := by
          rcases Nat.lt_or_ge i.val (blockIdx φ.hom i).val with h | h
          · exact h
          · exact absurd (Fin.ext (le_antisymm hge h)).symm hne
        have hsucc := dimPrefixSum_succ
          (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩) hilt
        have hgetfst : ((wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩).get
            ⟨i.val, hilt⟩).1 = dims.get i := by
          rw [wedgeToCubes_get]; exact congrArg dims.get (Fin.ext rfl)
        rw [hgetfst] at hsucc
        have hmono := dimPrefixSum_mono
          (wedgeToCubes ⟨dims, 𝟙 (⋁dims).toPsh⟩)
          (show i.val + 1 ≤ (blockIdx φ.hom i).val by omega)
        have hpos : 0 < (dims.get i : ℕ) := (dims.get i).2
        omega
    -- Hence `r = i` and the face `incl` is a `Box`-endo, so the identity.
    have hr : r = i := (blockIdx_eq_of_factor φ.hom i r incl hincl).trans hidx
    subst r
    have hincl_id : incl = 𝟙 ▫(dims.get i : ℕ) := by
      have htop : ev incl = topCell (dims.get i : ℕ) :=
        eq_topCell (ev incl)
      calc incl = canonicalMap (ev incl) :=
            ((cubeRepr (stdPre (dims.get i : ℕ)) (dims.get i : ℕ)).left_inv incl).symm
        _ = canonicalMap (topCell (dims.get i : ℕ)) := by rw [htop]
        _ = 𝟙 ▫(dims.get i : ℕ) := canonicalMap_topCell (dims.get i : ℕ)
    rw [hincl_id, CategoryTheory.Functor.map_id, Category.id_comp] at hincl
    exact hincl
  -- Assemble via the serial-wedge uniqueness.
  apply hom_ext
  rw [id_hom]
  refine serialWedge_hom_ext dims φ.hom (𝟙 (⋁dims).toPsh) (fun i => ?_) ?_
  · rw [Category.comp_id]; exact hblock i
  · rw [φ.app_init]; rfl

/-! ### Consequences for `Ch(K)` -/

/-! ### Skeletality helpers -/

/-- `blockIdx` of an identity map is the identity. -/
theorem blockIdx_id {dims : List ℕ+} (i : Fin dims.length) :
    blockIdx (𝟙 (⋁dims).toPsh) i = i :=
  (blockIdx_eq_of_factor (𝟙 (⋁dims).toPsh) i i
    (𝟙 ▫(dims.get i : ℕ)) (by
      rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp])).symm

/-- **`blockIdx` of a bi-pointed wedge map is monotone** — from the prefix-sum sandwich,
using only the serial wedge's altitude. -/
theorem serialWedge_blockIdx_monotone {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init) :
    Monotone (blockIdx φ) := by
  intro i i' hii
  rw [Fin.le_def]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨hb1, _⟩ := serialWedge_blockIdx_prefix_bound φ hinit i
  obtain ⟨_, hb2'⟩ := serialWedge_blockIdx_prefix_bound φ hinit i'
  have hmA := dimPrefixSum_mono (wedgeToCubes ⟨ad, φ⟩) (Fin.le_def.mp hii)
  have hmB := dimPrefixSum_mono (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
    (show (blockIdx φ i').val + 1 ≤ (blockIdx φ i).val by omega)
  omega

/-- Helper: a monotone bijection of `Fin`s (with the target length equal to the source
length) is the length-cast, so it fixes every index value. -/
theorem monotone_bij_fin_cast {m n : ℕ} (hmn : m = n) {R : Fin m → Fin n} {S : Fin n → Fin m}
    (hR : Monotone R) (hS : Monotone S) (h1 : ∀ i, S (R i) = i) (h2 : ∀ i, R (S i) = i)
    (i : Fin m) : (R i).val = i.val := by
  let e : Fin m ≃o Fin n :=
    { toEquiv := ⟨R, S, h1, h2⟩
      map_rel_iff' := by
        intro a b
        refine ⟨fun h => ?_, fun h => hR h⟩
        have h' : R a ≤ R b := h
        have := hS h'
        rwa [h1, h1] at this }
  have he : e = Fin.castOrderIso hmn := Subsingleton.elim _ _
  calc (R i).val = (e i).val := rfl
    _ = (Fin.castOrderIso hmn i).val := by rw [he]
    _ = i.val := by simp

/-! ### Dimension-sum preservation (serial-wedge level)

Any bi-pointed map `serialWedge ad ⟶ serialWedge cd` forces `∑ ad = ∑ cd`: the pushed cube chain
has dimension list `ad`, the taut chain has `cd`, and both span the same altitude gap in
`serialWedge cd` (whose own altitude always exists — `serialWedge_admitsAltitude`). -/

/-- **`∑ ad = ∑ cd` for a bi-pointed serial-wedge map**, via the serial wedge's own altitude. -/
theorem serialWedge_dimSum_eq {ad cd : List ℕ+}
    (φ : ⋁ad ⟶ ⋁cd) :
    dimSum ad = dimSum cd := by
  simp only [dimSum]
  obtain ⟨alt, hax, _⟩ := serialWedge_admitsAltitude cd
  have hmapEq : ∀ (dims : List ℕ+)
      (ψ : (⋁dims).toPsh ⟶ (⋁cd).toPsh),
      (wedgeToCubes ⟨dims, ψ⟩).map (fun c => (c.1 : ℕ)) = dims.map (fun d : ℕ+ => (d : ℕ)) := by
    intro dims ψ
    rw [show (fun c : Σ n : ℕ+, (⋁cd).cells (n : ℕ) => (c.1 : ℕ))
          = (fun d : ℕ+ => (d : ℕ)) ∘ (fun c => c.1) from rfl, ← List.map_map, wedgeToCubes_dims]
  have hciT : IsCubeChain (⋁cd).init
      (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (⋁cd).final := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) cd
      (𝟙 (⋁cd).toPsh)
    simpa using h
  have hciP : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ad, φ.hom⟩)
      (⋁cd).final := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) ad φ.hom
    rwa [φ.app_init, φ.app_final] at h
  have hT := isCubeChain_alt_final alt hax
    (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) _ _ hciT
  have hP := isCubeChain_alt_final alt hax (wedgeToCubes ⟨ad, φ.hom⟩) _ _ hciP
  rw [hmapEq cd _] at hT
  rw [hmapEq ad _] at hP
  have heq : ((ad.map (fun d : ℕ+ => (d : ℕ))).sum : ℤ)
      = ((cd.map (fun d : ℕ+ => (d : ℕ))).sum : ℤ) := add_left_cancel (hP.symm.trans hT)
  exact_mod_cast heq

/-! ### Prefix-sum monotonicity refinements (positive dimensions ⟹ strict) -/

/-- The dimension prefix-sum is **strictly** monotone up to the list length: every bead has
positive dimension (`ℕ+`). -/
theorem dimPrefixSum_strictMono {K : BPSet} (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    {i j : ℕ} (hj : j ≤ cubes.length) (hij : i < j) :
    dimPrefixSum cubes i < dimPrefixSum cubes j := by
  have hi : i < cubes.length := lt_of_lt_of_le hij hj
  have hstep : dimPrefixSum cubes i < dimPrefixSum cubes (i + 1) := by
    rw [dimPrefixSum_succ cubes hi]
    have hpos : (0 : ℤ) < (((cubes.get ⟨i, hi⟩).1 : ℕ) : ℤ) := by
      exact_mod_cast (cubes.get ⟨i, hi⟩).1.pos
    omega
  have hij' : i + 1 ≤ j := hij
  exact lt_of_lt_of_le hstep (dimPrefixSum_mono cubes hij')

/-- Prefix-sum reflects strict order (from monotonicity). -/
theorem dimPrefixSum_lt_reflect {K : BPSet} (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    {x y : ℕ} (h : dimPrefixSum cubes x < dimPrefixSum cubes y) : x < y := by
  by_contra hc; rw [not_lt] at hc
  exact absurd h (not_lt.mpr (dimPrefixSum_mono cubes hc))

/-- Prefix-sum reflects `≤` up to the list length (via strict monotonicity). -/
theorem dimPrefixSum_le_reflect {K : BPSet} (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    {x y : ℕ} (hx : x ≤ cubes.length) (h : dimPrefixSum cubes x ≤ dimPrefixSum cubes y) :
    x ≤ y := by
  by_contra hc; rw [not_le] at hc
  exact absurd h (not_le.mpr (dimPrefixSum_strictMono cubes hx hc))

/-- **Bucket lemma.**  A strictly-increasing prefix-sum sequence tiles `[0, total)`: any `m` with
`0 ≤ m < ∑ (all cubes)` lands in a unique half-open bead interval `[PT i, PT (i+1))`. -/
theorem exists_prefix_bucket {K : BPSet} (L : List (Σ n : ℕ+, K.cells (n : ℕ)))
    {m : ℤ} (h0 : 0 ≤ m) (hm : m < dimPrefixSum L L.length) :
    ∃ i, i < L.length ∧ dimPrefixSum L i ≤ m ∧ m < dimPrefixSum L (i + 1) := by
  classical
  set S := (Finset.range (L.length + 1)).filter (fun k => dimPrefixSum L k ≤ m) with hSdef
  have hmem0 : (0 : ℕ) ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos _, by rw [show dimPrefixSum L 0 = 0 by simp [dimPrefixSum]]; exact h0⟩
  have hne : S.Nonempty := ⟨0, hmem0⟩
  set i₀ := S.max' hne with hi₀
  have hmem : i₀ ∈ S := S.max'_mem hne
  rw [hSdef, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hlt1, hle⟩ := hmem
  have hmaxlt : i₀ < L.length := by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt1 with h | h
    · exact h
    · exfalso; rw [h] at hle; exact absurd hle (not_le.mpr hm)
  refine ⟨i₀, hmaxlt, hle, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hmemS1 : i₀ + 1 ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hcon⟩
  have hcontra := S.le_max' _ hmemS1
  rw [← hi₀] at hcontra
  omega

/-! ### The upper block-prefix bound and surjectivity of `blockIdx` -/

/-- **Upper prefix bound for `blockIdx`.**  The `(i+1)`-th `ad`-prefix does not exceed the
`(blockIdx φ i + 1)`-th `cd`-prefix: source bead `i` fits inside its target block.  Companion to
`serialWedge_blockIdx_prefix_bound`; uses only the serial wedge's altitude. -/
theorem serialWedge_blockIdx_prefix_upper {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) (i.val + 1)
      ≤ dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
          ((blockIdx φ i).val + 1) := by
  obtain ⟨alt, hax, h0⟩ := serialWedge_admitsAltitude cd
  have hciT : IsCubeChain (⋁cd).init
      (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (⋁cd).final := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) cd
      (𝟙 (⋁cd).toPsh)
    simpa using h
  have hciP : IsCubeChain (⋁cd).init (wedgeToCubes ⟨ad, φ⟩)
      (φ⟪0⟫ (⋁ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := ⋁cd) ad φ
    rwa [hinit] at h
  have hP_i := serialWedge_bead_alt alt hax h0 φ _ hciP i
  have hT_j := serialWedge_bead_alt alt hax h0 (𝟙 (⋁cd).toPsh) _ hciT
    (blockIdx φ i)
  rw [Category.comp_id] at hT_j
  have hce : yonedaEquiv (ιᵂ ad i ≫ φ)
      = (⋁cd).toPsh.map (blockFace φ i).op
          (yonedaEquiv (ιᵂ cd (blockIdx φ i))) :=
    (congrArg yonedaEquiv (blockFace_spec φ i)).trans
      (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ i)) (blockFace φ i)).symm
  have hc := PrecubicalSet.alt_cubeMap alt hax
    (yonedaEquiv (ιᵂ cd (blockIdx φ i))) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  have haltrel : dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      = dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (blockIdx φ i).val
        + (trueCount (ev (blockFace φ i)) : ℤ) := by
    rw [← hP_i, ← hT_j, hce]; exact hc
  have hjlt : (blockIdx φ i).val < (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).length := by
    rw [wedgeToCubes_length]; exact (blockIdx φ i).isLt
  have hgetfst : ((wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).get
      ⟨(blockIdx φ i).val, hjlt⟩).1 = cd.get (blockIdx φ i) := by
    rw [wedgeToCubes_get]; exact congrArg cd.get (Fin.ext rfl)
  have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) hjlt
  rw [hgetfst] at hsucc
  have hilt : i.val < (wedgeToCubes ⟨ad, φ⟩).length := by rw [wedgeToCubes_length]; exact i.isLt
  have hgetad : ((wedgeToCubes ⟨ad, φ⟩).get ⟨i.val, hilt⟩).1 = ad.get i := by
    rw [wedgeToCubes_get]; exact congrArg ad.get (Fin.ext rfl)
  have had_succ := dimPrefixSum_succ (wedgeToCubes ⟨ad, φ⟩) hilt
  rw [hgetad] at had_succ
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    cells_card_le (ev (blockFace φ i))
  have htle : trueCount (ev (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    trueCount_le (ev (blockFace φ i))
  omega

/-- **`blockIdx` of a bi-pointed serial-wedge map is surjective.**  Every coarse block is covered
by a fine bead: locate the fine bead whose half-open interval contains the coarse block's start
(`exists_prefix_bucket`), then the prefix sandwich pins its `blockIdx` to that block (via
`serialWedge_dimSum_eq` for the total and the two prefix bounds). -/
theorem blockIdx_surjective {ad cd : List ℕ+}
    (φ : ⋁ad ⟶ ⋁cd) :
    Function.Surjective (blockIdx φ.hom) := by
  intro j
  have hlenA : (wedgeToCubes ⟨ad, φ.hom⟩).length = ad.length := wedgeToCubes_length ad φ.hom
  have hlenC : (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).length = cd.length :=
    wedgeToCubes_length cd _
  have hmapEq : ∀ (dims : List ℕ+)
      (ψ : (⋁dims).toPsh ⟶ (⋁cd).toPsh),
      dimPrefixSum (wedgeToCubes ⟨dims, ψ⟩) (wedgeToCubes ⟨dims, ψ⟩).length
        = ((dims.map (fun d : ℕ+ => (d : ℕ))).sum : ℤ) := by
    intro dims ψ
    rw [dimPrefixSum, List.take_length]
    congr 1
    rw [show (fun c : Σ n : ℕ+, (⋁cd).cells (n : ℕ) => (c.1 : ℕ))
          = (fun d : ℕ+ => (d : ℕ)) ∘ (fun c => c.1) from rfl, ← List.map_map, wedgeToCubes_dims]
  have htot : dimPrefixSum (wedgeToCubes ⟨ad, φ.hom⟩) (wedgeToCubes ⟨ad, φ.hom⟩).length
      = dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
          (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩).length := by
    rw [hmapEq ad φ.hom, hmapEq cd _]; exact_mod_cast serialWedge_dimSum_eq φ
  -- The coarse block `j` starts at `Pc j`, strictly inside `[0, total)`.
  have hm0 : (0 : ℤ) ≤ dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) j.val := by
    rw [dimPrefixSum]; exact Int.natCast_nonneg _
  have hm : dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) j.val
      < dimPrefixSum (wedgeToCubes ⟨ad, φ.hom⟩) (wedgeToCubes ⟨ad, φ.hom⟩).length := by
    rw [htot]
    exact dimPrefixSum_strictMono _ (le_refl _) (by rw [hlenC]; exact j.isLt)
  obtain ⟨i, hi, hlo, hhi⟩ :=
    exists_prefix_bucket (wedgeToCubes ⟨ad, φ.hom⟩) hm0 hm
  have hiad : i < ad.length := by rw [← hlenA]; exact hi
  refine ⟨⟨i, hiad⟩, ?_⟩
  have hlow := serialWedge_blockIdx_prefix_bound φ.hom φ.app_init ⟨i, hiad⟩
  have hupp := serialWedge_blockIdx_prefix_upper φ.hom φ.app_init ⟨i, hiad⟩
  -- `blockIdx ⟨i⟩ ≤ j`: `Pc (blockIdx i) ≤ Pa i ≤ Pc j`.
  have hle1 : (blockIdx φ.hom ⟨i, hiad⟩).val ≤ j.val := by
    refine dimPrefixSum_le_reflect _
      (le_of_lt ((blockIdx φ.hom ⟨i, hiad⟩).isLt.trans_eq hlenC.symm)) ?_
    exact le_trans hlow.1 hlo
  -- `j ≤ blockIdx ⟨i⟩`: `Pc j < Pa (i+1) ≤ Pc (blockIdx i + 1)`.
  have hle2 : j.val ≤ (blockIdx φ.hom ⟨i, hiad⟩).val := by
    have hstep : dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) j.val
        < dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩)
            ((blockIdx φ.hom ⟨i, hiad⟩).val + 1) := lt_of_lt_of_le hhi hupp
    exact Nat.lt_succ_iff.mp (dimPrefixSum_lt_reflect _ hstep)
  exact Fin.ext (le_antisymm hle1 hle2)

end CubeChain

open CubeChain

/-! ### Consequences for the chain category `Ch(K)` -/

/-- **Every endomorphism of `Ch(K)` is the identity** — for every `K`. -/
theorem ChainCat.endo_eq_id {K : BPSet} {a : Ch K} (f : a ⟶ a) : f = 𝟙 a := by
  apply ChainCat.hom_ext'
  rw [ChainCat.id_φ]
  exact serialWedge_bipointed_endo_id a.dims f.φ

/-- **`Ch(K)` is skeletal**: any pair of morphisms `a ⟶ b`, `b ⟶ a` forces `a = b`.
The two composites are identities (`endo_eq_id`), so `blockIdx f.φ` is a monotone
bijection — hence the identity, giving `a.dims = b.dims` — and then `f.φ` is a
bi-pointed endo, so the identity, giving `a.map = b.map`. -/
theorem ChainCat.eq_of_hom_hom {K : BPSet} {a b : Ch K}
    (f : a ⟶ b) (g : b ⟶ a) : a = b := by
  -- The two composites are identities.
  have hfg : fᵂ ≫ gᵂ = 𝟙 (⋁a.dims).toPsh := by
    have h := congrArg (fun m : a ⟶ a => (ChainCat.Hom.φ m).hom) (ChainCat.endo_eq_id (f ≫ g))
    simpa only [ChainCat.comp_φ, comp_hom, ChainCat.id_φ, id_hom] using h
  have hgf : gᵂ ≫ fᵂ = 𝟙 (⋁b.dims).toPsh := by
    have h := congrArg (fun m : b ⟶ b => (ChainCat.Hom.φ m).hom) (ChainCat.endo_eq_id (g ≫ f))
    simpa only [ChainCat.comp_φ, comp_hom, ChainCat.id_φ, id_hom] using h
  -- `blockIdx fᵂ` and `blockIdx gᵂ` are mutually inverse.
  have hSR : ∀ i, blockIdx gᵂ (blockIdx fᵂ i) = i := by
    intro i
    have h := blockIdx_comp fᵂ gᵂ i
    rw [hfg, blockIdx_id] at h
    exact h.symm
  have hRS : ∀ j, blockIdx fᵂ (blockIdx gᵂ j) = j := by
    intro j
    have h := blockIdx_comp gᵂ fᵂ j
    rw [hgf, blockIdx_id] at h
    exact h.symm
  -- Length equality, monotonicity, and hence the index identity.
  have hlen : a.dims.length = b.dims.length :=
    Fin.equiv_iff_eq.mp ⟨⟨blockIdx fᵂ, blockIdx gᵂ, hSR, hRS⟩⟩
  have hmonoR := serialWedge_blockIdx_monotone fᵂ f.φ.app_init
  have hmonoS := serialWedge_blockIdx_monotone gᵂ g.φ.app_init
  have hReq : ∀ i, (blockIdx fᵂ i).val = i.val := fun i =>
    monotone_bij_fin_cast hlen hmonoR hmonoS hSR hRS i
  -- Dimension preservation (full-dimensional faces both ways).
  have hdimpres : ∀ i, a.dims.get i = b.dims.get (blockIdx fᵂ i) := by
    intro i
    have hle1 : (ChainCat.beadDim a i) ≤ (ChainCat.beadDim b (blockIdx fᵂ i)) :=
      cells_card_le (ev (blockFace fᵂ i))
    have hle2 : (ChainCat.beadDim b (blockIdx fᵂ i))
        ≤ (ChainCat.beadDim a (blockIdx gᵂ (blockIdx fᵂ i))) :=
      cells_card_le (ev (blockFace gᵂ (blockIdx fᵂ i)))
    rw [hSR i] at hle2
    have : (ChainCat.beadDim a i) = (ChainCat.beadDim b (blockIdx fᵂ i)) := le_antisymm hle1 hle2
    exact_mod_cast this
  -- `a.dims = b.dims`.
  have hdimseq : a.dims = b.dims := by
    apply List.ext_getElem hlen
    intro k h1 h2
    change a.dims.get ⟨k, h1⟩ = b.dims.get ⟨k, h2⟩
    rw [hdimpres ⟨k, h1⟩]
    exact congrArg b.dims.get (Fin.ext (hReq ⟨k, h1⟩))
  -- Conclude `a = b`.
  clear hfg hgf hSR hRS hlen hmonoR hmonoS hReq hdimpres g
  cases a with
  | mk da ma =>
    cases b with
    | mk db mb =>
      obtain rfl : da = db := hdimseq
      have hφ : f.φ = 𝟙 (⋁da) := serialWedge_bipointed_endo_id da f.φ
      have hmap : ma = mb := by
        have hw := f.w
        rw [hφ, Category.id_comp] at hw
        exact hw.symm
      rw [hmap]

/-- **Antisymmetry of the chain order** (`a ≤ b` := a morphism `a ⟶ b` exists).
With thinness (`chainCat_hom_subsingleton`, under `NonSelfLinked` + `AdmitsAltitude`),
`Ch(K)` is therefore a **poset**: the objects with `≤` form a partial order and the
category is thin, i.e. is that poset. -/
theorem ChainCat.le_antisymm {K : BPSet} {a b : Ch K}
    (hab : Nonempty (a ⟶ b)) (hba : Nonempty (b ⟶ a)) : a = b :=
  ChainCat.eq_of_hom_hom hab.some hba.some

/-! ### Bead-count monotonicity of coarsening (for the coarsest-chain well-foundedness)

A refinement `f : a ⟶ b` (`a` finer) has `blockIdx f` **surjective** (`blockIdx_surjective`), so the
coarse chain has no more beads than the fine one; equal bead counts force `a = b`. -/

/-- **A coarsening never increases the bead count.**  `blockIdx fᵂ` is a surjection
`ChainCat.Bead a ↠ ChainCat.Bead b`. -/
theorem ChainCat.dims_length_le_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    b.dims.length ≤ a.dims.length := by
  have h := Fintype.card_le_of_surjective _ (blockIdx_surjective f.φ)
  simpa using h

/-- **Equal bead counts force equal dimension lists.**  A monotone surjection between equal-length
`Fin`s is the identity cast; the source-face dimension bound plus `serialWedge_dimSum_eq` then pins
every dimension. -/
theorem ChainCat.dims_eq_of_hom_of_length_eq {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hlen : a.dims.length = b.dims.length) : a.dims = b.dims := by
  have hmono := serialWedge_blockIdx_monotone fᵂ f.φ.app_init
  have hbij : Function.Bijective (blockIdx fᵂ) := by
    rw [Fintype.bijective_iff_surjective_and_card]
    exact ⟨blockIdx_surjective f.φ, by simp [hlen]⟩
  set e := Equiv.ofBijective (blockIdx fᵂ) hbij with he
  have h1 : ∀ i, e.symm (blockIdx fᵂ i) = i := fun i => e.symm_apply_apply i
  have h2 : ∀ j, blockIdx fᵂ (e.symm j) = j := fun j => e.apply_symm_apply j
  have hSmono : Monotone (fun j => e.symm j) := by
    intro x y hxy
    by_contra hc; rw [not_le] at hc
    have hle : blockIdx fᵂ (e.symm y) ≤ blockIdx fᵂ (e.symm x) := hmono (le_of_lt hc)
    rw [h2, h2] at hle
    have hxy' : x = y := hxy.antisymm hle
    rw [hxy'] at hc; exact absurd hc (lt_irrefl _)
  have hval : ∀ i, (blockIdx fᵂ i).val = i.val := fun i =>
    monotone_bij_fin_cast hlen hmono hSmono h1 h2 i
  have hface : ∀ i, (ChainCat.beadDim a i) ≤ (ChainCat.beadDim b (blockIdx fᵂ i)) := fun i =>
    cells_card_le (ev (blockFace fᵂ i))
  have hsum_eq : (∑ i : ChainCat.Bead a, (ChainCat.beadDim a i))
      = ∑ i : ChainCat.Bead a, (ChainCat.beadDim b (blockIdx fᵂ i)) := by
    have e1 : (∑ i : ChainCat.Bead a, (ChainCat.beadDim a i))
        = dimSum a.dims := sum_get_eq_sum_map a.dims (fun d => (d : ℕ))
    have e2 : (∑ j : ChainCat.Bead b, (ChainCat.beadDim b j))
        = dimSum b.dims := sum_get_eq_sum_map b.dims (fun d => (d : ℕ))
    have e3 : (∑ i : ChainCat.Bead a, (ChainCat.beadDim b (blockIdx fᵂ i)))
        = ∑ j : ChainCat.Bead b, (ChainCat.beadDim b j) :=
      Fintype.sum_bijective (blockIdx fᵂ) hbij _ _ (fun _ => rfl)
    rw [e1, e3, e2, serialWedge_dimSum_eq f.φ]
  have hpt : ∀ i, (ChainCat.beadDim a i) = (ChainCat.beadDim b (blockIdx fᵂ i)) := fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hface i)).mp hsum_eq i (Finset.mem_univ i)
  apply List.ext_getElem hlen
  intro k h1' h2'
  change a.dims.get ⟨k, h1'⟩ = b.dims.get ⟨k, h2'⟩
  have heq1 : a.dims.get ⟨k, h1'⟩ = b.dims.get (blockIdx fᵂ ⟨k, h1'⟩) :=
    PNat.coe_injective (hpt ⟨k, h1'⟩)
  rw [heq1]
  exact congrArg b.dims.get (Fin.ext (hval ⟨k, h1'⟩))

/-- **Equal bead counts force equal chains.**  Combines `dims_eq_of_hom_of_length_eq` with the
serial-wedge endo-rigidity (`serialWedge_bipointed_endo_id`). -/
theorem ChainCat.eq_of_hom_of_dims_length_eq {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hlen : a.dims.length = b.dims.length) : a = b := by
  have hdimseq := ChainCat.dims_eq_of_hom_of_length_eq f hlen
  cases a with
  | mk da ma =>
    cases b with
    | mk db mb =>
      obtain rfl : da = db := hdimseq
      have hφ : f.φ = 𝟙 (⋁da) := serialWedge_bipointed_endo_id da f.φ
      have hmap : ma = mb := by
        have hw := f.w
        rw [hφ, Category.id_comp] at hw
        exact hw.symm
      rw [hmap]

/-- **A proper coarsening strictly drops the bead count.**  A non-isomorphism `g : a ⟶ c` has
`c.dims.length < a.dims.length`: equal length would force `a = c`, making `g` an endomorphism, hence
the identity (`ChainCat.endo_eq_id`), an isomorphism — contradiction.  The well-foundedness input
for `HasCoarsening`. -/
theorem ChainCat.lt_dims_length_of_not_isIso {K : BPSet} {a c : Ch K} (g : a ⟶ c)
    (hg : ¬ IsIso g) : c.dims.length < a.dims.length := by
  rcases (ChainCat.dims_length_le_of_hom g).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain rfl : a = c := ChainCat.eq_of_hom_of_dims_length_eq g h.symm
    exact hg (by rw [ChainCat.endo_eq_id g]; infer_instance)
