import CubeChains.Salvetti.BraidPartition
import CubeChains.Salvetti.Elements
import CubeChains.Arrangements.SalElements
import CubeChains.Arrangements.BraidCovector

/-!
# Salvetti/BraidFace — `Ch (□ⁿ)ᵒᵖ ≌ Face (braidCOM n)`

The object-level dictionary of the braid-Salvetti comparison: a cube chain of `□ⁿ` *is* an ordered
set partition of `Fin n`, hence a covector of the braid arrangement `A_{n-1}`.

Orientation: a `Ch` morphism `a ⟶ b` means `a` subdivides `b`, so `b`'s covector is the coarser
one — the bridge is contravariant.

Everything here is `Classical.choice`-free.  Two design points enforce that:
`signHeight` recovers a height function *from the covector itself* (rather than choosing a
witness out of `X ∈ Set.range braidSign`), and the inverse functor is written out explicitly
(rather than inverting an `EssSurj` proof through `asEquivalence`).
-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace CubeChains

open SignVec

variable {n : ℕ}

/-! ## Part 1 — a height function read off a covector

`Face (braidCOM n)` is a subtype over `Set.range braidSign`, so its membership proof is
`Prop`-truncated: extracting a height function from it needs choice.  `signHeight` avoids that by
*computing* a height function from the sign vector — the number of coordinates below `p` minus the
number above — which reproduces the same covector. -/

/-- "`q` sits strictly below `p`", read off a braid sign vector. -/
def sigLt (X : SignVec (BraidGround n)) (q p : Fin n) : Bool :=
  if h : q < p then decide (X ⟨(q, p), h⟩ = -1)
  else if h : p < q then decide (X ⟨(p, q), h⟩ = 1) else false

theorem sigLt_braidSign (w : Fin n → ℤ) (q p : Fin n) :
    sigLt (braidSign w) q p = decide (w q < w p) := by
  unfold sigLt
  by_cases h : q < p
  · rw [dif_pos h, braidSign_apply, decide_eq_decide]
    rw [sign_eq_neg_one_iff, sub_neg]
  · rw [dif_neg h]
    by_cases h' : p < q
    · rw [dif_pos h', braidSign_apply, decide_eq_decide]
      rw [sign_eq_one_iff, sub_pos]
    · obtain rfl : q = p := le_antisymm (not_lt.mp h') (not_lt.mp h)
      simp

/-- The coordinates strictly below `p`. -/
def sigBelow (X : SignVec (BraidGround n)) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun q => sigLt X q p)

/-- **A height function for the covector `X`**: `#(below p) − #(above p)`.  Computable, and a
section of `braidSign` on covectors (`braidSign_signHeight`). -/
def signHeight (X : SignVec (BraidGround n)) (p : Fin n) : ℤ :=
  ((sigBelow X p).card : ℤ) - ((Finset.univ.filter (fun q => sigLt X p q)).card : ℤ)

section
variable (w : Fin n → ℤ)

private theorem below_braidSign (p : Fin n) :
    sigBelow (braidSign w) p = Finset.univ.filter (fun q => w q < w p) := by
  ext q; simp [sigBelow, sigLt_braidSign]

private theorem above_braidSign (p : Fin n) :
    Finset.univ.filter (fun q => sigLt (braidSign w) p q)
      = Finset.univ.filter (fun q => w p < w q) := by
  ext q; simp [sigLt_braidSign]

private theorem signHeight_eq_of_eq {a b : Fin n} (h : w a = w b) :
    signHeight (braidSign w) a = signHeight (braidSign w) b := by
  simp only [signHeight, below_braidSign, above_braidSign, h]

private theorem signHeight_lt_of_lt {a b : Fin n} (h : w a < w b) :
    signHeight (braidSign w) a < signHeight (braidSign w) b := by
  simp only [signHeight, below_braidSign, above_braidSign]
  have hbelow : (Finset.univ.filter (fun q => w q < w a)).card
      < (Finset.univ.filter (fun q => w q < w b)).card := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact lt_trans hq h
    · simp [h]
    · simp
  have habove : (Finset.univ.filter (fun q => w b < w q)).card
      < (Finset.univ.filter (fun q => w a < w q)).card := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨b, ?_, ?_⟩)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact lt_trans h hq
    · simp [h]
    · simp
  omega

/-- **`signHeight` is a section of `braidSign`.** -/
theorem braidSign_signHeight : braidSign (signHeight (braidSign w)) = braidSign w := by
  funext e
  rw [braidSign_apply, braidSign_apply]
  rcases lt_trichotomy (w e.1.1) (w e.1.2) with h | h | h
  · rw [sign_neg (by linarith [signHeight_lt_of_lt w h]), sign_neg (by linarith)]
  · rw [signHeight_eq_of_eq w h, h, sub_self, sub_self]
  · rw [sign_pos (by linarith [signHeight_lt_of_lt w h]), sign_pos (by linarith)]

end

/-- `signHeight` realises every covector of `braidCOM n`. -/
theorem braidSign_signHeight_of_mem {X : SignVec (BraidGround n)}
    (hX : X ∈ (braidCOM n).covectors) : braidSign (signHeight X) = X := by
  obtain ⟨w, rfl⟩ := hX
  exact braidSign_signHeight w

/-! ## Part 2 — factoring a face through a coarser face -/

/-- **The star vector realising `wy` as a face of `wx`.**  When `wy`'s free set is contained in
`wx`'s free set, `wy = app wx s` for the star vector `s t = wy.val (nones wx t)`. -/
def faceFactor {N a b : ℕ} (wx : Cell N a) (wy : Cell N b)
    (hsub : noneSet wy.val ⊆ noneSet wx.val) : Cell a b :=
  ⟨fun t => wy.val (nones wx t), by
    have hmap : noneSet wy.val
        = (noneSet (fun t => wy.val (nones wx t))).map (nones wx).toEmbedding := by
      ext y
      simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
      constructor
      · intro hy
        have hyx : y ∈ noneSet wx.val := hsub hy
        refine ⟨nonesIdx wx y hyx, ?_, nones_nonesIdx wx y hyx⟩
        rw [mem_noneSet, nones_nonesIdx wx y hyx]
        exact mem_noneSet.mp hy
      · rintro ⟨t, ht, rfl⟩
        rw [mem_noneSet] at ht ⊢
        exact ht
    have hc : (noneSet (fun t => wy.val (nones wx t))).card = (noneSet wy.val).card := by
      rw [hmap, Finset.card_map]
    rw [hc]; exact wy.prop⟩

/-- **`faceFactor` is a right inverse of `app wx`**, given agreement on `wx`'s fixed
coordinates. -/
theorem faceFactor_app {N a b : ℕ} (wx : Cell N a) (wy : Cell N b)
    (hsub : noneSet wy.val ⊆ noneSet wx.val)
    (hfix : ∀ p, p ∉ noneSet wx.val → wx.val p = wy.val p) :
    act (K := stdPre N) wx (faceFactor wx wy hsub) = wy := by
  apply Subtype.ext
  funext p
  rw [app_val]
  by_cases hp : p ∈ noneSet wx.val
  · rw [dif_pos hp]
    change wy.val (nones wx (nonesIdx wx p hp)) = wy.val p
    rw [nones_nonesIdx wx p hp]
  · rw [dif_neg hp]
    exact hfix p hp

/-! ## Part 3 — the bead sign vector is forced by the partition -/

/-- **The bead's sign vector is forced by the partition.** At bead `j`, a coordinate `p` in
block `j` is free; otherwise its value records whether `p`'s block precedes `j`. -/
theorem toStar_get_val (x : RefineObj (□n).init (□n).final)
    (j : Fin x.cubes.length) (p : Fin n) :
    (toStar (x.cubes.get j).2).val p
      = if blockIndex x p = j then none else some (decide (blockIndex x p < j)) := by
  by_cases hj : blockIndex x p = j
  · rw [if_pos hj]
    exact mem_noneSet.mp ((mem_block_iff x).mpr hj)
  · rw [if_neg hj]
    have hnotj : p ∉ blockOf x j := fun h => hj ((mem_block_iff x).mp h)
    have h1 : (toStar (vtxCanon x.cubes (□n).final j.castSucc)).val p
        = (toStar (x.cubes.get j).2).val p := by
      rw [toStar_junc_castSucc, if_neg hnotj]
    have hVne : (toStar (x.cubes.get j).2).val p ≠ none := fun h => hnotj (mem_noneSet.mpr h)
    obtain ⟨c, hc⟩ : ∃ c, (toStar (x.cubes.get j).2).val p = some c := by
      cases h : (toStar (x.cubes.get j).2).val p with
      | none => exact absurd h hVne
      | some c => exact ⟨c, rfl⟩
    have hb : Fval x p j.castSucc = c := by
      change decide ((toStar (vtxCanon x.cubes (□n).final j.castSucc)).val p = some true) = c
      rw [h1, hc]
      cases c <;> rfl
    have hval_eq : (toStar (x.cubes.get j).2).val p = some (Fval x p j.castSucc) := by
      rw [hc, hb]
    have hj0 : p ∈ blockOf x (blockIndex x p) := blockIndex_mem x p
    have hf0c : Fval x p (blockIndex x p).castSucc = false := by
      change decide ((toStar (vtxCanon x.cubes (□n).final
        (blockIndex x p).castSucc)).val p = some true) = false
      rw [toStar_junc_castSucc, if_pos hj0]; rfl
    have hf0s : Fval x p (blockIndex x p).succ = true := by
      change decide ((toStar (vtxCanon x.cubes (□n).final
        (blockIndex x p).succ)).val p = some true) = true
      rw [toStar_junc_succ, if_pos hj0]; rfl
    have hFval_j : Fval x p j.castSucc = decide (blockIndex x p < j) := by
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hle : (blockIndex x p).succ ≤ j.castSucc := by
          have : (blockIndex x p : ℕ) < (j : ℕ) := hlt
          rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
        have hmono := Fval_mono x p hle
        rw [hf0s] at hmono
        have hfj : Fval x p j.castSucc = true := le_antisymm (Bool.le_true _) hmono
        rw [hfj]; symm; simp only [decide_eq_true_eq]; exact hlt
      · have hle : j.castSucc ≤ (blockIndex x p).castSucc := by
          have : (j : ℕ) < (blockIndex x p : ℕ) := hgt
          rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]; omega
        have hmono := Fval_mono x p hle
        rw [hf0c] at hmono
        have hfj : Fval x p j.castSucc = false := le_antisymm hmono (Bool.false_le _)
        rw [hfj]; symm; simp only [decide_eq_false_iff_not]; exact lt_asymm hgt
    rw [hval_eq, hFval_j]

/-- Every bead's block is nonempty, so `blockIndex x` is surjective. -/
theorem blockIndex_surjective (x : RefineObj (□n).init (□n).final) :
    Function.Surjective (blockIndex x) := by
  intro j
  have hpos : 0 < (blockOf x j).card := by
    rw [show (blockOf x j).card = ((x.cubes.get j).1 : ℕ) from (toStar (x.cubes.get j).2).prop]
    exact (x.cubes.get j).1.pos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, blockIndex_unique x hp⟩

/-! ## Part 4 — the per-bead face inclusion -/

/-- **The inclusion datum for bead `j`.**  Given the two sub-claims relating block `j` of the finer
chain `yf` to block `r` of the coarser chain `xc`, produce the standard-cube face inclusion
`□^{dⱼ} ↪ □^{dᵣ}` pulling `xc`'s bead back to `yf`'s bead. -/
def inclData (xc yf : RefineObj (□n).init (□n).final)
    (j : Fin yf.cubes.length) (r : Fin xc.cubes.length)
    (hsub : ∀ p, blockIndex yf p = j → blockIndex xc p = r)
    (hlt : ∀ p, blockIndex xc p ≠ r → (blockIndex yf p < j ↔ blockIndex xc p < r)) :
    { f : ▫((yf.cubes.get j).1 : ℕ) ⟶ ▫((xc.cubes.get r).1 : ℕ) //
      (yf.cubes.get j).2 = (□n).toPsh.map f.op (xc.cubes.get r).2 } := by
  have hsubFF : noneSet (toStar (yf.cubes.get j).2).val
      ⊆ noneSet (toStar (xc.cubes.get r).2).val := fun p hp =>
    (mem_noneSet_get_iff xc r p).mpr (hsub p ((mem_noneSet_get_iff yf j p).mp hp))
  have hfix : ∀ p, p ∉ noneSet (toStar (xc.cubes.get r).2).val →
      (toStar (xc.cubes.get r).2).val p = (toStar (yf.cubes.get j).2).val p := by
    intro p hp
    have hxr : blockIndex xc p ≠ r := fun h => hp ((mem_noneSet_get_iff xc r p).mpr h)
    have hyj : blockIndex yf p ≠ j := fun h => hxr (hsub p h)
    rw [toStar_get_val xc r p, toStar_get_val yf j p, if_neg hxr, if_neg hyj]
    congr 1
    rw [decide_eq_decide]
    exact (hlt p hxr).symm
  refine ⟨canonicalMap
      (faceFactor (toStar (xc.cubes.get r).2) (toStar (yf.cubes.get j).2) hsubFF), ?_⟩
  apply toStar_injective
  rw [toStar_map_op, toStar_canonicalMap]
  exact (faceFactor_app (toStar (xc.cubes.get r).2) (toStar (yf.cubes.get j).2) hsubFF hfix).symm

/-! ## Part 5 — building a refinement from a `faceLE`

The converse of `faceLE_of_chainRefine`.  A representative of each block is picked by
`Finset.min'`, not `Function.surjInv`: the refinement map is *data*, so a choice-based
representative would make the whole equivalence noncomputable. -/

/-- The least coordinate in bead `j`'s block. -/
def blockRep (x : RefineObj (□n).init (□n).final) (j : Fin x.cubes.length) : Fin n :=
  (blockOf x j).min' (by
    rw [← Finset.card_pos,
      show (blockOf x j).card = ((x.cubes.get j).1 : ℕ) from (toStar (x.cubes.get j).2).prop]
    exact (x.cubes.get j).1.pos)

@[simp] theorem blockIndex_blockRep (x : RefineObj (□n).init (□n).final)
    (j : Fin x.cubes.length) : blockIndex x (blockRep x j) = j :=
  blockIndex_unique x (Finset.min'_mem _ _)

/-- **`faceLE` ⟹ refinement.**  If `braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)`
then `yf` refines `xc`. -/
def chainRefineOfFaceLE (xc yf : RefineObj (□n).init (□n).final)
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)) :
    ChainRefine (□n).init (□n).final yf.cubes xc.cubes := by
  have hrefMap : ∀ p, blockIndex xc (blockRep yf (blockIndex yf p)) = blockIndex xc p :=
    fun p => faceLE_eq_of_eq hle _ p (blockIndex_blockRep yf (blockIndex yf p))
  have hsub' : ∀ (j : Fin yf.cubes.length) (p : Fin n), blockIndex yf p = j →
      blockIndex xc p = blockIndex xc (blockRep yf j) := by
    intro j p hj; rw [← hrefMap p, hj]
  have hlt' : ∀ (j : Fin yf.cubes.length) (p : Fin n),
      blockIndex xc p ≠ blockIndex xc (blockRep yf j) →
      (blockIndex yf p < j ↔ blockIndex xc p < blockIndex xc (blockRep yf j)) := by
    intro j p hne
    constructor
    · intro hpj
      have h1 : blockIndex yf p < blockIndex yf (blockRep yf j) := by
        rw [blockIndex_blockRep]; exact hpj
      exact lt_of_le_of_ne (faceLE_le_of_lt hle p (blockRep yf j) h1) hne
    · intro hpj
      by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub' j p heq.symm)
      · have h1 : blockIndex yf (blockRep yf j) < blockIndex yf p := by
          rw [blockIndex_blockRep]; exact hgt
        exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hle (blockRep yf j) p h1))
  refine {
    chainx := yf.isChain
    chainy := xc.isChain
    refinement := fun j => blockIndex xc (blockRep yf j)
    refinementMono := ?_
    incl := fun j => (inclData xc yf j _ (hsub' j) (hlt' j)).1
    inclSpec := fun j => (inclData xc yf j _ (hsub' j) (hlt' j)).2 }
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst heq; exact le_refl _
  · exact faceLE_le_of_lt hle _ _ (by rw [blockIndex_blockRep, blockIndex_blockRep]; exact hlt)

/-! ## Part 6 — the chain of an ordered set partition

Input: a surjection `β : Fin n → Fin k` — block `i` is the fibre `β⁻¹ i`, ordered by `i`. -/

variable {k : ℕ}

/-- **The star vector of bead `i`.** Block-`i` coordinates are free (`none`); a coordinate in
an earlier block has already flipped (`some true`); a later one has not (`some false`). -/
def blockStar (β : Fin n → Fin k) (i : Fin k) :
    Cell n (Finset.univ.filter (fun p => β p = i)).card :=
  ⟨fun p => if β p = i then none else some (decide (β p < i)), by
    have hns : noneSet (fun p => if β p = i then (none : Option Bool) else some (decide (β p < i)))
        = Finset.univ.filter (fun p => β p = i) := by
      ext p
      rw [mem_noneSet, Finset.mem_filter]
      by_cases h : β p = i <;> simp [h]
    rw [hns]⟩

@[simp] theorem blockStar_val (β : Fin n → Fin k) (i : Fin k) (p : Fin n) :
    (blockStar β i).val p = if β p = i then none else some (decide (β p < i)) := rfl

theorem mem_noneSet_blockStar (β : Fin n → Fin k) (i : Fin k) (p : Fin n) :
    p ∈ noneSet (blockStar β i).val ↔ β p = i := by
  rw [mem_noneSet, blockStar_val]
  by_cases h : β p = i <;> simp [h]

/-- Bead `i` as a cell of `(cube n).toPsh`. -/
def blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).cells (Finset.univ.filter (fun p => β p = i)).card :=
  canonicalMap (blockStar β i)

theorem toStar_blockCell (β : Fin n → Fin k) (i : Fin k) :
    toStar (blockCell β i) = blockStar β i :=
  toStar_canonicalMap (blockStar β i)

/-- The fibre of a surjection is nonempty. -/
theorem blockCard_pos (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    0 < (Finset.univ.filter (fun p => β p = i)).card := by
  obtain ⟨p, hp⟩ := hβ i
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩

/-- The `i`-th bead of the chain, as a dimension-tagged cell. -/
def bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    Σ m : ℕ+, (□n).cells (m : ℕ) :=
  ⟨⟨(Finset.univ.filter (fun p => β p = i)).card, blockCard_pos β hβ i⟩, blockCell β i⟩

theorem toStar_bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    toStar (bead β hβ i).2 = blockStar β i :=
  toStar_blockCell β i

/-- The junction vertex before bead `m`: a coordinate has flipped iff its block is `< m`. -/
def juncStar (β : Fin n → Fin k) (m : ℕ) : Cell n 0 :=
  ⟨fun p => some (decide ((β p : ℕ) < m)), by
    rw [Finset.card_eq_zero]
    ext p
    simp [mem_noneSet]⟩

@[simp] theorem juncStar_val (β : Fin n → Fin k) (m : ℕ) (p : Fin n) :
    (juncStar β m).val p = some (decide ((β p : ℕ) < m)) := rfl

/-- The junction vertex before bead `m` as a cell of `(cube n).toPsh`. -/
def juncVertex (β : Fin n → Fin k) (m : ℕ) : (□n).cells 0 :=
  canonicalMap (juncStar β m)

theorem toStar_juncVertex (β : Fin n → Fin k) (m : ℕ) :
    toStar (juncVertex β m) = juncStar β m :=
  toStar_canonicalMap (juncStar β m)

theorem juncVertex_zero (β : Fin n → Fin k) : juncVertex β 0 = (□n).init :=
  congrArg canonicalMap
    (show juncStar β 0 = constVertex n false by
      apply Subtype.ext; funext p; simp [juncStar, constVertex])

theorem juncVertex_top (β : Fin n → Fin k) {m : ℕ} (h : ∀ p, (β p : ℕ) < m) :
    juncVertex β m = (□n).final :=
  congrArg canonicalMap
    (show juncStar β m = constVertex n true by
      apply Subtype.ext; funext p; simp [juncStar, constVertex, h p])

theorem vertex₀_blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).toPsh.vertex₀ (blockCell β i) = juncVertex β (i : ℕ) := by
  apply toStar_injective
  rw [toStar_vertex₀, toStar_juncVertex, toStar_blockCell]
  apply Subtype.ext
  funext p
  rw [app_constVertex_val]
  by_cases hp : p ∈ noneSet (blockStar β i).val
  · rw [if_pos hp]
    have hbi : β p = i := (mem_noneSet_blockStar β i p).mp hp
    have hbi' : (β p : ℕ) = (i : ℕ) := by rw [hbi]
    change some false = (juncStar β (i : ℕ)).val p
    rw [juncStar_val, hbi']; simp
  · rw [if_neg hp]
    have hbi : β p ≠ i := fun h => hp ((mem_noneSet_blockStar β i p).mpr h)
    change (blockStar β i).val p = (juncStar β (i : ℕ)).val p
    rw [blockStar_val, if_neg hbi, juncStar_val]
    exact congrArg some (decide_eq_decide.mpr Fin.lt_def)

theorem vertex₁_blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).toPsh.vertex₁ (blockCell β i) = juncVertex β ((i : ℕ) + 1) := by
  apply toStar_injective
  rw [toStar_vertex₁, toStar_juncVertex, toStar_blockCell]
  apply Subtype.ext
  funext p
  rw [app_constVertex_val]
  by_cases hp : p ∈ noneSet (blockStar β i).val
  · rw [if_pos hp]
    have hbi : β p = i := (mem_noneSet_blockStar β i p).mp hp
    have hbi' : (β p : ℕ) = (i : ℕ) := by rw [hbi]
    change some true = (juncStar β ((i : ℕ) + 1)).val p
    rw [juncStar_val, hbi']; simp
  · rw [if_neg hp]
    have hbi : β p ≠ i := fun h => hp ((mem_noneSet_blockStar β i p).mpr h)
    have hne : (β p : ℕ) ≠ (i : ℕ) := fun h => hbi (Fin.ext h)
    change (blockStar β i).val p = (juncStar β ((i : ℕ) + 1)).val p
    rw [blockStar_val, if_neg hbi, juncStar_val]
    exact congrArg some (decide_eq_decide.mpr (by rw [Fin.lt_def]; omega))

theorem chainOf_isChain (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    IsCubeChain (□n).init (List.ofFn (bead β hβ)) (□n).final := by
  have key := isCubeChain_aux (K := □n) (List.ofFn (bead β hβ))
    (fun j => juncVertex β (j : ℕ))
    (fun i => by rw [List.get_ofFn]; exact vertex₀_blockCell β _)
    (fun i => by rw [List.get_ofFn]; exact vertex₁_blockCell β _)
  rw [← juncVertex_zero β,
    ← juncVertex_top β (m := (List.ofFn (bead β hβ)).length)
      (fun p => by rw [List.length_ofFn]; exact (β p).isLt)]
  exact key

/-- **The cube chain of `β`.** Bead `i` is classified by `blockStar β i`. -/
def chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    RefineObj (□n).init (□n).final where
  cubes := List.ofFn (bead β hβ)
  isChain := chainOf_isChain β hβ

theorem chainOf_cubes_length (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    (chainOf β hβ).cubes.length = k := List.length_ofFn

theorem chainOf_cubes_get (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    (chainOf β hβ).cubes.get (Fin.cast (chainOf_cubes_length β hβ).symm i) = bead β hβ i :=
  List.get_ofFn (bead β hβ) (Fin.cast (chainOf_cubes_length β hβ).symm i)

theorem blockOf_chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    blockOf (chainOf β hβ) (Fin.cast (chainOf_cubes_length β hβ).symm i)
      = Finset.univ.filter (fun p => β p = i) := by
  change noneSet (toStar
    ((chainOf β hβ).cubes.get (Fin.cast (chainOf_cubes_length β hβ).symm i)).2).val = _
  rw [chainOf_cubes_get, toStar_bead]
  ext p
  rw [mem_noneSet_blockStar, Finset.mem_filter]
  simp

/-- **`blockIndex` of `chainOf` recovers `β`.** Stated at `ℕ`-values to avoid `Fin`-cast pain. -/
theorem blockIndex_chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) (p : Fin n) :
    ((blockIndex (chainOf β hβ) p : ℕ)) = (β p : ℕ) := by
  have hmem : p ∈ blockOf (chainOf β hβ)
      (Fin.cast (chainOf_cubes_length β hβ).symm (β p)) := by
    rw [blockOf_chainOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, rfl⟩
  rw [blockIndex_unique (chainOf β hβ) hmem]
  simp

/-- Sigma-equality of two cube beads with equal dimension and equal sign vectors. -/
theorem bead_ext {d₁ : ℕ+} {c₁ : (□n).cells (d₁ : ℕ)} {d₂ : ℕ+} {c₂ : (□n).cells (d₂ : ℕ)}
    (hd : (d₁ : ℕ) = (d₂ : ℕ)) (hv : (toStar c₁).val = (toStar c₂).val) :
    (⟨d₁, c₁⟩ : Σ m : ℕ+, (□n).cells (m : ℕ)) = ⟨d₂, c₂⟩ := by
  obtain rfl : d₁ = d₂ := PNat.coe_injective hd
  rw [toStar_injective (Subtype.ext hv)]

/-- **`chainOf` of `blockIndex` recovers the chain.** -/
theorem chainOf_blockIndex (x : RefineObj (□n).init (□n).final) :
    chainOf (blockIndex x) (blockIndex_surjective x) = x := by
  apply RefineObj.ext'
  change List.ofFn (bead (blockIndex x) (blockIndex_surjective x)) = x.cubes
  have key : ∀ j : Fin x.cubes.length,
      bead (blockIndex x) (blockIndex_surjective x) j = x.cubes.get j := by
    intro j
    have hcard : (Finset.univ.filter (fun p => blockIndex x p = j)).card
        = ((x.cubes.get j).1 : ℕ) := by
      rw [show Finset.univ.filter (fun p => blockIndex x p = j) = blockOf x j by
        ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_block_iff]]
      exact (toStar (x.cubes.get j).2).prop
    have hv : (toStar (blockCell (blockIndex x) j)).val = (toStar (x.cubes.get j).2).val := by
      rw [toStar_blockCell]
      funext p
      rw [toStar_get_val]
      rfl
    exact bead_ext (d₁ := ⟨(Finset.univ.filter (fun p => blockIndex x p = j)).card,
        blockCard_pos (blockIndex x) (blockIndex_surjective x) j⟩)
      (c₁ := blockCell (blockIndex x) j)
      (d₂ := (x.cubes.get j).1) (c₂ := (x.cubes.get j).2) hcard hv
  rw [funext key]
  exact List.ofFn_get x.cubes

/-! ## Part 7 — the two functors -/

/-- **The opposite of a thin category is thin.** -/
instance instIsThinOp {C : Type*} [Quiver C] [Quiver.IsThin C] : Quiver.IsThin Cᵒᵖ :=
  fun _ _ => ⟨fun f g => Opposite.unop_injective (Subsingleton.elim f.unop g.unop)⟩

/-- **The braid-Salvetti bridge** `(Ch □ⁿ)ᵒᵖ ⥤ Face (braidCOM n)`: a chain maps to its
ordered-set-partition covector, a subdivision to the induced face relation. -/
def chToFace (n : ℕ) : (Ch (□n))ᵒᵖ ⥤ COM.Face (braidCOM n) where
  obj a := ⟨braidSign (chCovectorHeight a.unop), ⟨chCovectorHeight a.unop, rfl⟩⟩
  map f := homOfLE (faceLE_of_chHom f.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The chain of a covector: re-read the covector as a height function, take its block
partition, and build the chain. -/
def faceChain (X : COM.Face (braidCOM n)) : RefineObj (□n).init (□n).final :=
  chainOf (blockMap (signHeight X.1)) (blockMap_surjective _)

/-- `faceChain` is a section of the covector map — the counit equation. -/
theorem braidSign_covectorHeight_faceChain (X : COM.Face (braidCOM n)) :
    braidSign (covectorHeight (faceChain X)) = X.1 := by
  have hcov : covectorHeight (faceChain X) = fun p => ((blockMap (signHeight X.1) p : ℕ) : ℤ) := by
    funext p
    exact congrArg (Nat.cast : ℕ → ℤ) (blockIndex_chainOf _ _ p)
  rw [hcov, braidSign_blockMap]
  exact braidSign_signHeight_of_mem X.2

/-- Two ordered set partitions of `Fin n` with the same block indices give the same chain. -/
theorem chainOf_congr {k k' : ℕ} (β : Fin n → Fin k) (hβ : Function.Surjective β)
    (β' : Fin n → Fin k') (hβ' : Function.Surjective β') (h : ∀ p, (β p : ℕ) = (β' p : ℕ)) :
    chainOf β hβ = chainOf β' hβ' := by
  obtain rfl : k = k' := by
    rw [← numBlocks_of_surjective β hβ, ← numBlocks_of_surjective β' hβ']
    exact congrArg numBlocks (funext fun p => congrArg (Nat.cast : ℕ → ℤ) (h p))
  obtain rfl : β = β' := funext fun p => Fin.ext (h p)
  rfl

/-- **Unit round trip.**  Re-reading a chain's covector as a height function and rebuilding the
chain recovers it on the nose. -/
theorem chainOf_blockMap_signHeight (z : RefineObj (□n).init (□n).final) :
    chainOf (blockMap (signHeight (braidSign (covectorHeight z)))) (blockMap_surjective _) = z :=
  (chainOf_congr _ _ (blockIndex z) (blockIndex_surjective z) (fun p => by
    rw [blockMap_congr (braidSign_signHeight (covectorHeight z)) p]
    exact blockMap_of_surjective (blockIndex z) (blockIndex_surjective z) p)).trans
    (chainOf_blockIndex z)

/-- **The inverse bridge** `Face (braidCOM n) ⥤ (Ch □ⁿ)ᵒᵖ`, written out explicitly: inverting
`chToFace` through essential surjectivity would go via `Classical.choice`. -/
def faceToCh (n : ℕ) : COM.Face (braidCOM n) ⥤ (Ch (□n))ᵒᵖ where
  obj X := op ((refineToWedge (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)).obj
    (faceChain X))
  map {X Y} φ := Quiver.Hom.op
    ((refineToWedge (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)).map
      (chainRefineOfFaceLE (faceChain X) (faceChain Y) (by
        rw [braidSign_covectorHeight_faceChain, braidSign_covectorHeight_faceChain]
        exact leOfHom φ)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-! ## Part 8 — the equivalence

Both categories are thin, and both round trips are equalities on the nose, so unit and counit
are `eqToIso` and every coherence is `Subsingleton.elim`. -/

theorem faceChain_chToFace (a : Ch (□n)) :
    faceChain ((chToFace n).obj (op a)) = wedgeToRefineObj a :=
  chainOf_blockMap_signHeight (wedgeToRefineObj a)

theorem faceToCh_chToFace_obj (a : Ch (□n)) :
    (faceToCh n).obj ((chToFace n).obj (op a)) = op a := by
  apply Opposite.unop_injective
  change refineToWedgeObj (faceChain ((chToFace n).obj (op a))) = a
  rw [faceChain_chToFace]
  exact refineToWedgeObj_wedgeToRefineObj a

theorem chToFace_faceToCh_obj (X : COM.Face (braidCOM n)) :
    (chToFace n).obj ((faceToCh n).obj X) = X := by
  apply Subtype.ext
  change braidSign (covectorHeight (wedgeToRefineObj (refineToWedgeObj (faceChain X)))) = X.1
  rw [wedgeToRefineObj_refineToWedgeObj]
  exact braidSign_covectorHeight_faceChain X

/-- **The braid-Salvetti object dictionary.**  The opposite of the cube-chain category of `□ⁿ` is
equivalent to the face poset of the braid arrangement `A_{n-1}`. -/
def chFaceEquiv (n : ℕ) : (Ch (□n))ᵒᵖ ≌ COM.Face (braidCOM n) where
  functor := chToFace n
  inverse := faceToCh n
  unitIso := NatIso.ofComponents
    (fun a => eqToIso (by rw [← op_unop a]; exact (faceToCh_chToFace_obj a.unop).symm))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun X => eqToIso (chToFace_faceToCh_obj X))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end CubeChains
