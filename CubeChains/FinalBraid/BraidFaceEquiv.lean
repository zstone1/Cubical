import CubeChains.FinalBraid.SalElements
import CubeChains.FinalBraid.SalBraidChain
import CubeChains.FinalBraid.BraidCovector
import CubeChains.FinalBraid.BraidPreorder

/-!
# FinalBraid/BraidFaceEquiv — `Face (braidCOM n) ≌ (RefineObj □ⁿ)ᵒᵖ`

The **object-level dictionary** of the braid-Salvetti comparison: the face poset of the braid
oriented matroid `braidCOM n` (covectors under the conformal order `faceLE`) is equivalent to the
*opposite* of the refinement category of cube chains of `□ⁿ`.

Orientation: `RefineObj` morphism `x ⟶ y` means *`x` refines `y`* (`x` finer); `faceLE X Y` means
`X` coarser.  So in `(RefineObj)ᵒᵖ` a morphism `op x ⟶ op y` is `y ⟶ x`, i.e. "`y` refines `x`",
and the backward functor `refineOpToFace` sends a chain to its ordered-set-partition covector
`braidSign (covectorHeight x)`, monotonically: a refinement `y ⟶ x` (y finer) produces
`faceLE (braidSign (covectorHeight x)) (braidSign (covectorHeight y))` (coarse ⊑ fine).

Main result:
`braidFaceEquiv n : COM.Face (braidCOM n) ≌ (RefineObj (cube n).init (cube n).final)ᵒᵖ`.

**Layer:** FinalBraid.  Not part of the default `CubeChains` target.
-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace FinalBraid

open SignVec

variable {n : ℕ}

/-! ## Part 0 — the `toStar` bridge for a pulled-back cell -/

/-- `toStar` intertwines a cube-map pullback with the iterated-face map: pulling `c` back along a
box morphism `φ` reads concretely as `StdCube.app (toStar c) (toStar φ)`. -/
theorem toStar_map_op {n dy dx : ℕ} (φ : Box.ob dy ⟶ Box.ob dx)
    (c : (BPSet.cube n).toPsh.cells dx) :
    toStar ((BPSet.cube n).toPsh.map φ.op c)
      = StdCube.app (K := StdCube.stdPre n) (toStar c)
          (toStar (φ : (BPSet.cube dx).toPsh.cells dy)) := by
  have h : (BPSet.cube n).toPsh.map φ.op c
      = ((BPSet.cube n).toPsh.cubeMap c).app (op (Box.ob dy)) φ := by
    rw [PrecubicalSet.cubeMap]
    exact (yonedaEquiv_symm_app_apply c (op (Box.ob dy)) φ).symm
  rw [h, toStar_cubeMap_app]

/-- Membership in the `none`-set of the `j`-th bead is exactly having block index `j`. -/
theorem mem_noneSet_get_iff (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (j : Fin x.cubes.length) (p : Fin n) :
    p ∈ StdCube.noneSet (toStar (x.cubes.get j).2).val ↔ blockIndex x p = j :=
  mem_block_iff x

/-! ## Part 1 — factoring a face through a coarser face (`faceFactor`) -/

/-- **The star vector realising `wy` as a face of `wx`.**  When `wy`'s free set is contained in
`wx`'s free set, `wy = app wx s` for the star vector `s t = wy.val (nones wx t)`. -/
noncomputable def faceFactor {N a b : ℕ} (wx : StdCube.cells N a) (wy : StdCube.cells N b)
    (hsub : StdCube.noneSet wy.val ⊆ StdCube.noneSet wx.val) : StdCube.cells a b :=
  ⟨fun t => wy.val (StdCube.nones wx t), by
    have hmap : StdCube.noneSet wy.val
        = (StdCube.noneSet (fun t => wy.val (StdCube.nones wx t))).map
            (StdCube.nones wx).toEmbedding := by
      ext y
      simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
      constructor
      · intro hy
        have hyx : y ∈ StdCube.noneSet wx.val := hsub hy
        refine ⟨StdCube.nonesIdx wx y hyx, ?_, StdCube.nones_nonesIdx wx y hyx⟩
        rw [StdCube.mem_noneSet, StdCube.nones_nonesIdx wx y hyx]
        exact StdCube.mem_noneSet.mp hy
      · rintro ⟨t, ht, rfl⟩
        rw [StdCube.mem_noneSet] at ht ⊢
        exact ht
    have hc : (StdCube.noneSet (fun t => wy.val (StdCube.nones wx t))).card
        = (StdCube.noneSet wy.val).card := by rw [hmap, Finset.card_map]
    rw [hc]; exact wy.prop⟩

/-- **`faceFactor` is a right inverse of `app wx`.**  If in addition `wx` and `wy` agree on `wx`'s
fixed coordinates, then `app wx (faceFactor wx wy hsub) = wy`. -/
theorem faceFactor_app {N a b : ℕ} (wx : StdCube.cells N a) (wy : StdCube.cells N b)
    (hsub : StdCube.noneSet wy.val ⊆ StdCube.noneSet wx.val)
    (hfix : ∀ p, p ∉ StdCube.noneSet wx.val → wx.val p = wy.val p) :
    StdCube.app (K := StdCube.stdPre N) wx (faceFactor wx wy hsub) = wy := by
  apply Subtype.ext
  funext p
  rw [app_val]
  by_cases hp : p ∈ StdCube.noneSet wx.val
  · rw [dif_pos hp]
    change wy.val (StdCube.nones wx (StdCube.nonesIdx wx p hp)) = wy.val p
    rw [StdCube.nones_nonesIdx wx p hp]
  · rw [dif_neg hp]
    exact hfix p hp

/-! ## Part 2 — the block-order dictionary -/

/-- Strict comparison of covector heights is strict comparison of block indices. -/
theorem covectorHeight_lt_iff (z : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (p q : Fin n) :
    covectorHeight z p < covectorHeight z q ↔ blockIndex z p < blockIndex z q := by
  simp only [covectorHeight, Nat.cast_lt]
  exact Fin.lt_def.symm

/-- Equality of covector heights is equality of block indices. -/
theorem covectorHeight_eq_iff (z : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (p q : Fin n) :
    covectorHeight z p = covectorHeight z q ↔ blockIndex z p = blockIndex z q := by
  simp only [covectorHeight, Nat.cast_inj]
  exact Fin.val_injective.eq_iff

/-! ## Part 3 — the two order-transfer facts of a `faceLE` -/

variable {xc yf : RefineObj (BPSet.cube n).init (BPSet.cube n).final}

/-- On an ordered pair `e`, a `faceLE` transfers the sign of the (nonzero) height difference. -/
theorem faceLE_sign_pair
    (hle : faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf)))
    (e : BraidGround n) (hne : covectorHeight xc e.1.1 ≠ covectorHeight xc e.1.2) :
    sign (covectorHeight xc e.1.1 - covectorHeight xc e.1.2)
      = sign (covectorHeight yf e.1.1 - covectorHeight yf e.1.2) := by
  have h := (faceLE_braidSign_iff (covectorHeight xc) (covectorHeight yf)).mp hle e
    ((braidSign_ne_zero_iff (covectorHeight xc) e).mpr hne)
  rw [braidSign_apply, braidSign_apply] at h
  exact h

/-- The unordered version: for any distinct-height pair, the sign of the height difference is
preserved by the finer chain. -/
theorem faceLE_sign
    (hle : faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf)))
    (p q : Fin n) (hne : covectorHeight xc p ≠ covectorHeight xc q) :
    sign (covectorHeight xc p - covectorHeight xc q)
      = sign (covectorHeight yf p - covectorHeight yf q) := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact faceLE_sign_pair hle ⟨(p, q), hpq⟩ hne
  · exact absurd (congrArg (covectorHeight xc) hpq) hne
  · have h : sign (covectorHeight xc q - covectorHeight xc p)
        = sign (covectorHeight yf q - covectorHeight yf p) :=
      faceLE_sign_pair hle ⟨(q, p), hpq⟩ (Ne.symm hne)
    rw [show covectorHeight xc p - covectorHeight xc q
          = -(covectorHeight xc q - covectorHeight xc p) by ring,
        show covectorHeight yf p - covectorHeight yf q
          = -(covectorHeight yf q - covectorHeight yf p) by ring,
        Left.sign_neg, Left.sign_neg, h]

/-- **Tie transfer.**  A tie of the finer chain forces a tie of the coarser chain. -/
theorem faceLE_eq_of_eq
    (hle : faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf)))
    (p q : Fin n) (h : blockIndex yf p = blockIndex yf q) :
    blockIndex xc p = blockIndex xc q := by
  by_contra hxne
  have hvxne : covectorHeight xc p ≠ covectorHeight xc q :=
    fun he => hxne ((covectorHeight_eq_iff xc p q).mp he)
  have hs := faceLE_sign hle p q hvxne
  have hlhs : sign (covectorHeight xc p - covectorHeight xc q) ≠ 0 :=
    sign_ne_zero.mpr (sub_ne_zero.mpr hvxne)
  rw [hs] at hlhs
  exact (sub_ne_zero.mp (sign_ne_zero.mp hlhs)) ((covectorHeight_eq_iff yf p q).mpr h)

/-- **Order transfer.**  A strict order of the finer chain implies a weak order of the coarser. -/
theorem faceLE_le_of_lt
    (hle : faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf)))
    (p q : Fin n) (h : blockIndex yf p < blockIndex yf q) :
    blockIndex xc p ≤ blockIndex xc q := by
  by_contra hlt
  rw [not_le] at hlt
  have hvxne : covectorHeight xc p ≠ covectorHeight xc q := by
    intro he; rw [(covectorHeight_eq_iff xc p q).mp he] at hlt; exact lt_irrefl _ hlt
  have hs := faceLE_sign hle p q hvxne
  have hvxq : covectorHeight xc q < covectorHeight xc p := (covectorHeight_lt_iff xc q p).mpr hlt
  have hvyp : covectorHeight yf p < covectorHeight yf q := (covectorHeight_lt_iff yf p q).mpr h
  rw [sign_pos (by linarith), sign_neg (by linarith)] at hs
  exact absurd hs (by decide)

/-! ## Part 4 — the per-bead face inclusion (`inclData`) -/

/-- **The inclusion datum for bead `j`.**  Given the two sub-claims relating block `j` of the finer
chain `yf` to block `r` of the coarser chain `xc`, produce the standard-cube face inclusion
`□^{dⱼ} ↪ □^{dᵣ}` pulling `xc`'s bead back to `yf`'s bead. -/
noncomputable def inclData (xc yf : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (j : Fin yf.cubes.length) (r : Fin xc.cubes.length)
    (hsub : ∀ p, blockIndex yf p = j → blockIndex xc p = r)
    (hlt : ∀ p, blockIndex xc p ≠ r → (blockIndex yf p < j ↔ blockIndex xc p < r)) :
    { f : Box.ob ((yf.cubes.get j).1 : ℕ) ⟶ Box.ob ((xc.cubes.get r).1 : ℕ) //
      (yf.cubes.get j).2 = (BPSet.cube n).toPsh.map f.op (xc.cubes.get r).2 } := by
  have hsubFF : StdCube.noneSet (toStar (yf.cubes.get j).2).val
      ⊆ StdCube.noneSet (toStar (xc.cubes.get r).2).val := fun p hp =>
    (mem_noneSet_get_iff xc r p).mpr (hsub p ((mem_noneSet_get_iff yf j p).mp hp))
  have hfix : ∀ p, p ∉ StdCube.noneSet (toStar (xc.cubes.get r).2).val →
      (toStar (xc.cubes.get r).2).val p = (toStar (yf.cubes.get j).2).val p := by
    intro p hp
    have hxr : blockIndex xc p ≠ r := fun h => hp ((mem_noneSet_get_iff xc r p).mpr h)
    have hyj : blockIndex yf p ≠ j := fun h => hxr (hsub p h)
    rw [toStar_get_val xc r p, toStar_get_val yf j p, if_neg hxr, if_neg hyj]
    congr 1
    rw [decide_eq_decide]
    exact (hlt p hxr).symm
  refine ⟨StdCube.canonicalMap
      (faceFactor (toStar (xc.cubes.get r).2) (toStar (yf.cubes.get j).2) hsubFF), ?_⟩
  apply toStar_injective
  rw [toStar_map_op, toStar_canonicalMap]
  exact (faceFactor_app (toStar (xc.cubes.get r).2) (toStar (yf.cubes.get j).2) hsubFF hfix).symm

/-! ## Part 5 — building a refinement from a `faceLE` -/

/-- **`faceLE` ⟹ refinement.**  If `braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)`
then `yf` refines `xc`: a `ChainRefine` from `yf` to `xc`. -/
noncomputable def chainRefineOfFaceLE (xc yf : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (hle : faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf))) :
    ChainRefine (BPSet.cube n).init (BPSet.cube n).final yf.cubes xc.cubes := by
  classical
  have hsurj := blockIndex_surjective yf
  set rep : Fin yf.cubes.length → Fin n := Function.surjInv hsurj with hrepdef
  have hrep : ∀ j, blockIndex yf (rep j) = j := fun j => Function.surjInv_eq hsurj j
  have hrefMap : ∀ p, blockIndex xc (rep (blockIndex yf p)) = blockIndex xc p :=
    fun p => faceLE_eq_of_eq hle (rep (blockIndex yf p)) p (hrep (blockIndex yf p))
  have hsub' : ∀ (j : Fin yf.cubes.length) (p : Fin n), blockIndex yf p = j →
      blockIndex xc p = blockIndex xc (rep j) := by
    intro j p hj; rw [← hrefMap p, hj]
  have hlt' : ∀ (j : Fin yf.cubes.length) (p : Fin n),
      blockIndex xc p ≠ blockIndex xc (rep j) →
      (blockIndex yf p < j ↔ blockIndex xc p < blockIndex xc (rep j)) := by
    intro j p hne
    constructor
    · intro hpj
      have h1 : blockIndex yf p < blockIndex yf (rep j) := by rw [hrep]; exact hpj
      exact lt_of_le_of_ne (faceLE_le_of_lt hle p (rep j) h1) hne
    · intro hpj
      by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub' j p heq.symm)
      · have h1 : blockIndex yf (rep j) < blockIndex yf p := by rw [hrep]; exact hgt
        exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hle (rep j) p h1))
  refine {
    chainx := yf.isChain
    chainy := xc.isChain
    refinement := fun j => blockIndex xc (rep j)
    refinementMono := ?_
    incl := fun j => (inclData xc yf j (blockIndex xc (rep j)) (hsub' j) (hlt' j)).1
    inclSpec := fun j => (inclData xc yf j (blockIndex xc (rep j)) (hsub' j) (hlt' j)).2 }
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst heq; exact le_refl _
  · exact faceLE_le_of_lt hle (rep i) (rep j) (by rw [hrep, hrep]; exact hlt)

/-! ## Part 6 — refinement ⟹ `faceLE` (the forward direction) -/

/-- **Refinement ⟹ `faceLE`.**  A `ChainRefine` from `yf` to `xc` (`yf` finer) yields
`braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)`. -/
theorem faceLE_of_chainRefine (xc yf : RefineObj (BPSet.cube n).init (BPSet.cube n).final)
    (g : ChainRefine (BPSet.cube n).init (BPSet.cube n).final yf.cubes xc.cubes) :
    faceLE (braidSign (covectorHeight xc)) (braidSign (covectorHeight yf)) := by
  have hbridge : ∀ p, blockIndex xc p = g.refinement (blockIndex yf p) := by
    intro p
    have hpn : (toStar (yf.cubes.get (blockIndex yf p)).2).val p = none :=
      StdCube.mem_noneSet.mp (blockIndex_mem yf p)
    rw [g.inclSpec (blockIndex yf p), toStar_map_op, app_val] at hpn
    by_cases hp : p ∈ StdCube.noneSet (toStar (xc.cubes.get (g.refinement (blockIndex yf p))).2).val
    · exact (mem_noneSet_get_iff xc (g.refinement (blockIndex yf p)) p).mp hp
    · rw [dif_neg hp] at hpn
      exact absurd (StdCube.mem_noneSet.mpr hpn) hp
  rw [faceLE_braidSign_iff_refinesTies]
  intro e hne
  have hxc_ne : blockIndex xc e.1.1 ≠ blockIndex xc e.1.2 :=
    fun h => hne ((covectorHeight_eq_iff xc e.1.1 e.1.2).mpr h)
  have hyf_ne : blockIndex yf e.1.1 ≠ blockIndex yf e.1.2 := by
    intro h; apply hxc_ne; rw [hbridge e.1.1, hbridge e.1.2, h]
  rw [braidSign_apply, braidSign_apply]
  rcases lt_or_gt_of_ne hyf_ne with h | h
  · have hxlt : blockIndex xc e.1.1 < blockIndex xc e.1.2 :=
      lt_of_le_of_ne (by rw [hbridge e.1.1, hbridge e.1.2]; exact g.refinementMono _ _ (le_of_lt h))
        hxc_ne
    rw [sign_neg (by have := (covectorHeight_lt_iff yf e.1.1 e.1.2).mpr h; linarith),
        sign_neg (by have := (covectorHeight_lt_iff xc e.1.1 e.1.2).mpr hxlt; linarith)]
  · have hxgt : blockIndex xc e.1.2 < blockIndex xc e.1.1 :=
      lt_of_le_of_ne (by rw [hbridge e.1.1, hbridge e.1.2]; exact g.refinementMono _ _ (le_of_lt h))
        (Ne.symm hxc_ne)
    rw [sign_pos (by have := (covectorHeight_lt_iff yf e.1.2 e.1.1).mpr h; linarith),
        sign_pos (by have := (covectorHeight_lt_iff xc e.1.2 e.1.1).mpr hxgt; linarith)]

/-! ## Part 7 — the backward functor and the equivalence -/

/-- **The opposite of a thin category is thin.**  Mathlib has no such instance; this is generic
and belongs upstream (or in `FinalBraid/Elements.lean` beside `Functor.elements_isThin`). -/
instance instIsThinOp {C : Type*} [Quiver C] [Quiver.IsThin C] : Quiver.IsThin Cᵒᵖ :=
  fun _ _ => ⟨fun f g => Opposite.unop_injective (Subsingleton.elim f.unop g.unop)⟩

/-- **The backward functor** `(RefineObj □ⁿ)ᵒᵖ ⥤ Face (braidCOM n)`: a chain `op x` maps to its
ordered-set-partition covector `braidSign (covectorHeight x)`, and a refinement to the induced
face relation. -/
noncomputable def refineOpToFace (n : ℕ) :
    (RefineObj (BPSet.cube n).init (BPSet.cube n).final)ᵒᵖ ⥤ COM.Face (braidCOM n) where
  obj x := ⟨braidSign (covectorHeight x.unop), ⟨covectorHeight x.unop, rfl⟩⟩
  map {x y} f := homOfLE (faceLE_of_chainRefine x.unop y.unop f.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

-- `Faithful` is free: mathlib derives it from a thin domain
-- (`CategoryTheory.Functor.instFaithful...` at `FullyFaithful.lean`, priority 100).

instance (n : ℕ) : (refineOpToFace n).Full where
  map_surjective := fun {X Y} φ =>
    ⟨Quiver.Hom.op (chainRefineOfFaceLE X.unop Y.unop (leOfHom φ) : Y.unop ⟶ X.unop),
      Subsingleton.elim _ _⟩

instance (n : ℕ) : (refineOpToFace n).EssSurj where
  mem_essImage X := by
    obtain ⟨w, hw⟩ := X.2
    refine ⟨Opposite.op (chainOf (blockMap w) (blockMap_surjective w)), ⟨eqToIso ?_⟩⟩
    apply Subtype.ext
    change braidSign (covectorHeight (chainOf (blockMap w) (blockMap_surjective w))) = X.1
    have hcov : covectorHeight (chainOf (blockMap w) (blockMap_surjective w))
        = fun p => ((blockMap w p : ℕ) : ℤ) := by
      funext p
      change (((blockIndex (chainOf (blockMap w) (blockMap_surjective w)) p : ℕ)) : ℤ)
          = ((blockMap w p : ℕ) : ℤ)
      rw [blockIndex_chainOf]
    rw [hcov, braidSign_blockMap]; exact hw

/-- **The object-level braid-Salvetti dictionary.**  The face poset of `braidCOM n` is equivalent
to the opposite of the refinement category of cube chains of `□ⁿ`. -/
noncomputable def braidFaceEquiv (n : ℕ) :
    COM.Face (braidCOM n) ≌ (RefineObj (BPSet.cube n).init (BPSet.cube n).final)ᵒᵖ :=
  haveI : (refineOpToFace n).IsEquivalence := { }
  (refineOpToFace n).asEquivalence.symm

end FinalBraid
