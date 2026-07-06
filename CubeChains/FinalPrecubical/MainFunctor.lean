import CubeChains.FinalPrecubical.QuotientCat
import CubeChains.FinalPrecubical.Salvetti
import CubeChains.FinalPrecubical.Ev
import CubeChains.Chains.Category
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# FinalPrecubical / MainFunctor

The capstone (Step 4 of `BRAID_CHAINS_README.md`): the main functor

  `Φ n : ChZ n ⥤ (QuotCat (Sal₀Br n) (Equiv.Perm (Fin n)))ᵒᵖ`

comparing the grade-`n` cube chains of the **terminal** bi-pointed precubical set `Z`
with the (opposite of the) braid Salvetti quotient category.  `Φ` is proved a genuine
functor, **fully faithful** and **(essentially) surjective on objects**, hence an
**equivalence of categories** `PhiEquiv : ChZ n ≌ (QC n)ᵒᵖ`.

The whole development is sorry-free **except** the single geometric input
`blockIdx_monotone` (block-monotonicity of a wedge map — the well-definedness crux, an
open combinatorial fact also staged in `Research/Conjectures.lean`).  Faithfulness rests
on `Ev.ev_reconstruct` and fullness on `Ev.evValid_exists` (both proved in `Ev` modulo
its own deferred geometric inputs).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace FinalPrecubical

/-! ## §1. The terminal bi-pointed precubical set `Z` -/

/-- The terminal presheaf: the constant `PUnit`, written explicitly (rather than via
`Functor.const`) so that `Zpsh.obj c` reduces to `PUnit` at reducible transparency —
this is what lets the unique-map components elaborate as `PUnit`-valued functions. -/
@[reducible] def Zpsh : PrecubicalSet where
  obj _ := PUnit
  map _ := 𝟙 PUnit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The terminal bi-pointed precubical set: its underlying presheaf is the terminal
presheaf (constant `PUnit`), and both distinguished `0`-cells are its unique point.

⚠ This is NOT `cube 0`/`serialWedge []` (which has no cells above dimension `0`); it is
the genuine terminal object, with a unique cell in every dimension. -/
@[reducible] def Z : BPSet where
  toPsh := Zpsh
  init := PUnit.unit
  final := PUnit.unit

/-- The unique bi-pointed map into `Z`. -/
def toZ (X : BPSet) : X ⟶ Z where
  hom :=
    { app := fun c => ↾(fun (_ : X.toPsh.obj c) => PUnit.unit)
      naturality := fun _ _ _ => ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _ }
  app_init := rfl
  app_final := rfl

/-- **`Z` is terminal in `BPSet`.**  The underlying presheaf map is forced by
terminality of the constant-`PUnit` presheaf, and `init`/`final` preservation is
automatic since `Z`'s `0`-cells are a subsingleton. -/
def zTerminal : IsTerminal Z :=
  IsTerminal.ofUniqueHom toZ fun X m => by
    apply BPSet.hom_ext
    apply NatTrans.ext
    funext c
    exact ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim (α := Z.toPsh.obj c) _ _

/-- Any two bi-pointed maps into `Z` coincide (terminality). -/
theorem zHom_subsingleton (X : BPSet) : Subsingleton (X ⟶ Z) :=
  ⟨fun f g => zTerminal.hom_ext f g⟩

/-! ## §2. The grade-`n` chains `ChZ n` -/

/-- The object predicate cutting out grade `n`: chains whose dimension sequence has
dims-sum (event count) `n`.  Here `dimSum` is `Ev.dimSum`. -/
def ZGrade (n : ℕ) : ObjectProperty (ChainCat.Obj Z) := fun a => dimSum a.dims = n

/-- **Grade-`n` cube chains of `Z`** — the full subcategory of `Ch Z` on chains with
`dimSum` (path length / event count) equal to `n`. -/
abbrev ChZ (n : ℕ) : Type := (ZGrade n).FullSubcategory

/-- The dimension sequence of a grade-`n` chain. -/
abbrev ChZ.dims {n : ℕ} (a : ChZ n) : List ℕ+ := a.obj.dims

/-- The grade equation attached to a grade-`n` chain. -/
theorem ChZ.grade {n : ℕ} (a : ChZ n) : dimSum a.dims = n := a.property

/-- The underlying wedge map of a `ChZ`-morphism. -/
abbrev ChZ.wedgeMap {n : ℕ} {a b : ChZ n} (g : a ⟶ b) :
    BPSet.serialWedge a.dims ⟶ BPSet.serialWedge b.dims :=
  g.hom.φ

/-! ## §3. The layout bridge: Salvetti `blockOf` = Ev `globalEquiv` block index

Salvetti (`stdFaceAt`/`blockOf`) and Ev (`globalEquiv`/`finSigmaFinEquiv`) each lay
`Fin (dimSum A)` out in serial block order; we prove they agree, so the functor can
translate between `ev_blocks`/`ev_strictMonoOn` and the `Sal₀Br` order. -/

/-- The prefix-sum of block sizes as a `Finset` sum over the first `m` blocks — the
shape produced by `finSigmaFinEquiv_apply`. -/
theorem sum_castLE_eq_psum (A : List ℕ+) :
    ∀ (m : ℕ) (hm : m ≤ A.length),
      (∑ i' : Fin m, (A.get (Fin.castLE hm i') : ℕ)) = psum A m
  | 0, _ => by simp [psum_zero]
  | m + 1, hm => by
      rw [Fin.sum_univ_castSucc]
      have hm' : m ≤ A.length := Nat.le_of_succ_le hm
      have hmlen : m < A.length := hm
      have e1 : (∑ i' : Fin m, (A.get (Fin.castLE hm i'.castSucc) : ℕ))
          = ∑ i' : Fin m, (A.get (Fin.castLE hm' i') : ℕ) :=
        Finset.sum_congr rfl (fun i' _ => rfl)
      rw [e1, sum_castLE_eq_psum A m hm', psum_succ A hmlen]
      have hlast : (Fin.castLE hm (Fin.last m) : Fin A.length) = ⟨m, hmlen⟩ := Fin.ext rfl
      rw [hlast]

/-- `globalEquiv A ⟨i, q⟩` has global value `psum A i + q` (prefix of full blocks plus
the star offset). -/
theorem globalEquiv_val_psum {A : List ℕ+} (i : Fin A.length) (q : Fin (A.get i : ℕ)) :
    (globalEquiv A ⟨i, q⟩ : ℕ) = psum A (i : ℕ) + (q : ℕ) := by
  rw [globalEquiv_val, finSigmaFinEquiv_apply]
  dsimp only
  rw [sum_castLE_eq_psum A (i : ℕ) i.2.le]

/-- **The layout bridge.** The Salvetti block index `blockOf A` of the global position
`globalEquiv A ⟨i, q⟩` is exactly the source block `i`. -/
theorem blockOf_globalEquiv {A : List ℕ+} (i : Fin A.length) (q : Fin (A.get i : ℕ)) :
    blockOf A (globalEquiv A ⟨i, q⟩ : ℕ) = (i : ℕ) := by
  have hk : (globalEquiv A ⟨i, q⟩ : ℕ) < dimSum A := (globalEquiv A ⟨i, q⟩).2
  refine (blockOf_iff_psum A hk i.2).mpr ⟨?_, ?_⟩
  · rw [globalEquiv_val_psum]; exact Nat.le_add_right _ _
  · rw [globalEquiv_val_psum]
    have key : psum A ((i : ℕ) + 1) = psum A (i : ℕ) + (A.get i : ℕ) := by
      rw [psum_succ A i.2]
    have hq : (q : ℕ) < (A.get i : ℕ) := q.2
    omega

/-- The bridge in `symm` form: the Salvetti block index of a global position `t` equals
the Ev source-block index `((globalEquiv A).symm t).1`. -/
theorem blockOf_eq_globalEquiv_symm_fst {A : List ℕ+} (t : Fin (dimSum A)) :
    blockOf A (t : ℕ) = (((globalEquiv A).symm t).1 : ℕ) := by
  have h := blockOf_globalEquiv (A := A) ((globalEquiv A).symm t).1 ((globalEquiv A).symm t).2
  rwa [show (⟨((globalEquiv A).symm t).1, ((globalEquiv A).symm t).2⟩ :
      Σ i : Fin A.length, Fin (A.get i : ℕ)) = (globalEquiv A).symm t from rfl,
    Equiv.apply_symm_apply] at h

/-! ## §4. The event permutation of a graded morphism -/

/-- The underlying wedge map of the identity is the identity. -/
theorem ChZ.wedgeMap_id {n : ℕ} (a : ChZ n) :
    ChZ.wedgeMap (𝟙 a) = 𝟙 (BPSet.serialWedge a.dims) := rfl

/-- The underlying wedge map of a composite is the composite of wedge maps. -/
theorem ChZ.wedgeMap_comp {n : ℕ} {a b c : ChZ n} (g : a ⟶ b) (h : b ⟶ c) :
    ChZ.wedgeMap (g ≫ h) = ChZ.wedgeMap g ≫ ChZ.wedgeMap h := rfl

/-- The event permutation of a `ChZ n`-morphism, reindexed to `Fin n` by the two grade
equations. -/
noncomputable def evPermN {n : ℕ} {a b : ChZ n} (g : a ⟶ b) : Equiv.Perm (Fin n) :=
  (finCongr (ChZ.grade a).symm).trans ((evPerm (ChZ.wedgeMap g)).trans (finCongr (ChZ.grade b)))

theorem evPermN_apply {n : ℕ} {a b : ChZ n} (g : a ⟶ b) (x : Fin n) :
    (evPermN g x : ℕ) = (ev (ChZ.wedgeMap g) (finCongr (ChZ.grade a).symm x) : ℕ) := by
  simp only [evPermN, Equiv.trans_apply, evPerm_apply, finCongr_apply_coe]

/-- `evPermN (𝟙 a) = 1`. -/
theorem evPermN_id {n : ℕ} (a : ChZ n) : evPermN (𝟙 a) = 1 := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [evPermN_apply, ChZ.wedgeMap_id, ev_id]
  simp [Equiv.Perm.coe_one]

/-- `evPermN (g ≫ h) = evPermN h * evPermN g` (composition of permutations is `∘`). -/
theorem evPermN_comp {n : ℕ} {a b c : ChZ n} (g : a ⟶ b) (h : b ⟶ c) :
    evPermN (g ≫ h) = evPermN h * evPermN g := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  have harg : ev (ChZ.wedgeMap g) (finCongr (ChZ.grade a).symm x)
      = finCongr (ChZ.grade b).symm (evPermN g x) := by
    apply Fin.ext
    rw [finCongr_apply_coe, evPermN_apply]
  rw [Equiv.Perm.mul_apply, evPermN_apply, evPermN_apply, ChZ.wedgeMap_comp, ev_comp,
    Function.comp_apply, harg]

theorem evPermN_inv_apply {n : ℕ} {a b : ChZ n} (g : a ⟶ b) (y : Fin n) :
    ((evPermN g)⁻¹ y : ℕ)
      = ((evPerm (ChZ.wedgeMap g)).symm (finCongr (ChZ.grade b).symm y) : ℕ) := by
  change ((evPermN g).symm y : ℕ) = _
  simp only [evPermN, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply_coe]

/-! ## §5. Order-comparison helpers -/

/-- `finCongr` reflects and preserves `<` (it preserves the underlying value). -/
theorem finCongr_lt_iff {m k : ℕ} (h : m = k) (a b : Fin m) :
    finCongr h a < finCongr h b ↔ a < b := by
  rw [Fin.lt_def, Fin.lt_def, finCongr_apply_coe, finCongr_apply_coe]

/-- Within a fixed source block the global re-indexing is strictly monotone. -/
theorem globalEquiv_block_strictMono (A : List ℕ+) (r : Fin A.length) :
    StrictMono (fun q : Fin (A.get r : ℕ) => globalEquiv A ⟨r, q⟩) :=
  fun _ _ h => globalEquiv_block_lt r h

/-- **The tie core.** For two source events in the *same* source block `i`, `ev` is
strictly order-preserving (star positions are read in serial order) — the `<`-iff form
of `ev_strictMonoOn`. -/
theorem ev_lt_iff_of_blockeq {A B : List ℕ+} (φ : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    {i1 i2 : Fin A.length} (p1 : Fin (A.get i1 : ℕ)) (p2 : Fin (A.get i2 : ℕ)) (hi : i1 = i2) :
    (ev φ (globalEquiv A ⟨i1, p1⟩) < ev φ (globalEquiv A ⟨i2, p2⟩)
      ↔ globalEquiv A ⟨i1, p1⟩ < globalEquiv A ⟨i2, p2⟩) := by
  subst hi
  have h1 : (ev φ (globalEquiv A ⟨i1, p1⟩) < ev φ (globalEquiv A ⟨i1, p2⟩)) ↔ p1 < p2 := by
    rw [ev_apply, ev_apply]
    constructor
    · intro hlt
      exact (StdCube.nones (faceStar φ i1)).strictMono.lt_iff_lt.mp
        ((globalEquiv_block_strictMono B (blockIdx φ i1)).lt_iff_lt.mp hlt)
    · intro hlt
      exact globalEquiv_block_lt (blockIdx φ i1) ((StdCube.nones (faceStar φ i1)).strictMono hlt)
  have h2 : (globalEquiv A ⟨i1, p1⟩ < globalEquiv A ⟨i1, p2⟩) ↔ p1 < p2 := by
    constructor
    · exact fun hlt => (globalEquiv_block_strictMono A i1).lt_iff_lt.mp hlt
    · exact fun hlt => globalEquiv_block_lt i1 hlt
  rw [h1, h2]

/-- `ev` order-comparison for two source events in the same source block, phrased on
raw global positions (decode to `⟨i, p⟩` then apply `ev_lt_iff_of_blockeq`). -/
theorem ev_lt_iff_sameblock {A B : List ℕ+} (φ : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    {U1 U2 : Fin (dimSum A)}
    (hblk : ((globalEquiv A).symm U1).1 = ((globalEquiv A).symm U2).1) :
    (ev φ U1 < ev φ U2 ↔ U1 < U2) := by
  have e1 : globalEquiv A ⟨((globalEquiv A).symm U1).1, ((globalEquiv A).symm U1).2⟩ = U1 :=
    Equiv.apply_symm_apply (globalEquiv A) U1
  have e2 : globalEquiv A ⟨((globalEquiv A).symm U2).1, ((globalEquiv A).symm U2).2⟩ = U2 :=
    Equiv.apply_symm_apply (globalEquiv A) U2
  rw [← e1, ← e2]
  exact ev_lt_iff_of_blockeq φ _ _ hblk

/-! ## §6. Well-definedness of the functor `Φ`

The `Sal₀Br` order `stdPairAt b.dims hb ≤ evPermN g • stdPairAt a.dims ha` unfolds into
the **face part** (`Fpart_pointwise` + block-monotonicity) and the **tie part**
(`sigma_strictMono_block`). -/

/-- **Tie part core.** For two coordinates in the *same* source block, `evPermN g`
preserves and reflects the order (`ev_strictMonoOn` reindexed). -/
theorem sigma_strictMono_block {n : ℕ} {a b : ChZ n} (g : a ⟶ b) {u1 u2 : Fin n}
    (hblk : blockOf a.dims (u1 : ℕ) = blockOf a.dims (u2 : ℕ)) :
    (evPermN g u1 < evPermN g u2 ↔ u1 < u2) := by
  have hbU : ((globalEquiv a.dims).symm (finCongr (ChZ.grade a).symm u1)).1
      = ((globalEquiv a.dims).symm (finCongr (ChZ.grade a).symm u2)).1 := by
    apply Fin.ext
    rw [← blockOf_eq_globalEquiv_symm_fst, ← blockOf_eq_globalEquiv_symm_fst,
      finCongr_apply_coe, finCongr_apply_coe]
    exact hblk
  have hev := ev_lt_iff_sameblock (ChZ.wedgeMap g) hbU
  rw [Fin.lt_def, evPermN_apply, evPermN_apply, ← Fin.lt_def, hev, finCongr_lt_iff]

/-- **Face part, pointwise.** The standard target-block index of `y` equals the
`blockIdx`-image of the source block that `y` comes from. -/
theorem Fpart_pointwise {n : ℕ} {a b : ChZ n} (g : a ⟶ b) (y : Fin n) :
    (stdFaceAt b.dims b.property).f y
      = blockIdx (ChZ.wedgeMap g) ((evPermN g • stdFaceAt a.dims a.property).f y) := by
  have hsrc : (evPermN g • stdFaceAt a.dims a.property).f y
      = ((globalEquiv a.dims).symm
          ((evPerm (ChZ.wedgeMap g)).symm (finCongr (ChZ.grade b).symm y))).1 := by
    apply Fin.ext
    rw [BrFace.smul_f, stdFaceAt_f, ← blockOf_eq_globalEquiv_symm_fst, evPermN_inv_apply]
  rw [hsrc, ev_blocks (ChZ.wedgeMap g) (finCongr (ChZ.grade b).symm y)]
  apply Fin.ext
  rw [stdFaceAt_f, ← blockOf_eq_globalEquiv_symm_fst, finCongr_apply_coe]

/-- **DEFERRED — block-monotonicity of a wedge map (`Monotone (blockIdx φ)`).**

This is the ONE geometric input the well-definedness of `Φ` genuinely requires and
which is *not* provided by the combinatorial `ev`-API: a non-monotone `blockIdx` still
satisfies every conjunct of `Ev.IsEvValid` (block placement + covering + within-block
strict monotonicity), so monotonicity is an *extra* constraint carried only by genuine
wedge maps.  Geometrically it is `blockIdx φ i = blockOf B (psum A i)` — the source
spine is a directed path whose junction altitudes `psum A i` increase, so the target
blocks are visited in weakly increasing order (no junction re-crossing).  This is the
same open combinatorial fact staged, under an altitude hypothesis, as the Segal
splitting in `Research/Conjectures.lean` (`chConcat_essSurj`/`chConcat_full`). -/
theorem blockIdx_monotone {A B : List ℕ+} (φ : BPSet.serialWedge A ⟶ BPSet.serialWedge B) :
    Monotone (blockIdx φ) :=
  sorry

/-- **Well-definedness of `Φ.map`.**  The `Sal₀Br` order holds between `stdPairAt b`
and the `evPermN g`-twist of `stdPairAt a`. -/
theorem Phi_welldef {n : ℕ} {a b : ChZ n} (g : a ⟶ b) :
    stdPairAt b.dims b.property ≤ evPermN g • stdPairAt a.dims a.property := by
  refine ⟨⟨blockIdx (ChZ.wedgeMap g), blockIdx_monotone (ChZ.wedgeMap g), ?_⟩, ?_⟩
  · funext y
    exact Fpart_pointwise g y
  · intro y1 y2 htie
    have hblk : blockOf a.dims ((evPermN g)⁻¹ y1 : ℕ)
        = blockOf a.dims ((evPermN g)⁻¹ y2 : ℕ) := by
      have h2 := htie
      rw [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, BrFace.smul_f] at h2
      have h3 := congrArg (Fin.val) h2
      rw [stdFaceAt_f, stdFaceAt_f] at h3
      exact h3
    simp only [stdPairAt_C, stdChamber_f, id_eq, Sal₀Br.smul_C, BrFace.smul_f]
    -- goal: y1 < y2 ↔ (evPermN g)⁻¹ y1 < (evPermN g)⁻¹ y2
    have key := sigma_strictMono_block g (u1 := (evPermN g)⁻¹ y1) (u2 := (evPermN g)⁻¹ y2) hblk
    have e1 : evPermN g ((evPermN g)⁻¹ y1) = y1 := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have e2 : evPermN g ((evPermN g)⁻¹ y2) = y2 := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    rw [e1, e2] at key
    exact key

/-! ## §7. The main functor `Φ` -/

/-- The braid Salvetti quotient category at grade `n`. -/
abbrev QC (n : ℕ) : Type := QuotCat (Sal₀Br n) (Equiv.Perm (Fin n))

/-- The object of `QC n` classifying the chain `a`: the orbit of its standard pair. -/
noncomputable def stdObj {n : ℕ} (a : ChZ n) : QC n :=
  Quotient.mk'' (stdPairAt a.dims a.property)

/-- The span classifying `Φ.map g`: from `⟦stdPair b⟧` to `⟦stdPair a⟧`, with upper
endpoint the `evPermN g`-twist of `stdPair a`. -/
noncomputable def PhiSpan {n : ℕ} {a b : ChZ n} (g : a ⟶ b) :
    QuotCat.Span (stdObj b) (stdObj a) :=
  ⟨(stdPairAt b.dims b.property, evPermN g • stdPairAt a.dims a.property),
    Phi_welldef g, rfl, mk_smul_eq _ _⟩

/-- `Φ.map g` as a morphism of `QuotCat` (before taking the opposite). -/
noncomputable def PhiMor {n : ℕ} {a b : ChZ n} (g : a ⟶ b) : stdObj b ⟶ stdObj a :=
  Quotient.mk'' (PhiSpan g)

/-- `Φ` sends identities to identities (at the `QuotCat` level). -/
theorem PhiMor_id {n : ℕ} (a : ChZ n) : PhiMor (𝟙 a) = 𝟙 (stdObj a) := by
  apply Quotient.sound'
  refine ⟨align (Quotient.out (stdObj a)) (stdPairAt a.dims a.property)
      (Quotient.out_eq' _), ?_, ?_⟩
  · exact align_smul _ _ _
  · change align (Quotient.out (stdObj a)) (stdPairAt a.dims a.property) (Quotient.out_eq' _)
        • (evPermN (𝟙 a) • stdPairAt a.dims a.property) = Quotient.out (stdObj a)
    rw [evPermN_id, one_smul]
    exact align_smul _ _ _

/-- `Φ` respects composition (at the `QuotCat` level): the aligning element between the
two representatives at the middle object is `evPermN h`. -/
theorem PhiMor_comp {n : ℕ} {a b c : ChZ n} (g : a ⟶ b) (h : b ⟶ c) :
    PhiMor (g ≫ h) = PhiMor h ≫ PhiMor g := by
  have halign : QuotCat.alignPair (PhiSpan h) (PhiSpan g) = evPermN h :=
    smul_left_cancel (QuotCat.alignPair_smul (PhiSpan h) (PhiSpan g))
  change Quotient.mk'' (PhiSpan (g ≫ h))
      = QuotCat.compMor (Quotient.mk'' (PhiSpan h)) (Quotient.mk'' (PhiSpan g))
  rw [QuotCat.compMor_mk]
  apply Quotient.sound'
  refine ⟨1, ?_, ?_⟩
  · change (1 : Equiv.Perm (Fin n)) • stdPairAt c.dims c.property = stdPairAt c.dims c.property
    rw [one_smul]
  · change (1 : Equiv.Perm (Fin n)) • (evPermN (g ≫ h) • stdPairAt a.dims a.property)
        = QuotCat.alignPair (PhiSpan h) (PhiSpan g) • (evPermN g • stdPairAt a.dims a.property)
    rw [one_smul, halign, ← mul_smul, evPermN_comp]

/-- **The main functor** `Φ : ChZ n ⥤ (Sal₀Br n // Perm (Fin n))ᵒᵖ`. -/
noncomputable def Φ (n : ℕ) : ChZ n ⥤ (QC n)ᵒᵖ where
  obj a := Opposite.op (stdObj a)
  map g := (PhiMor g).op
  map_id a := by
    change (PhiMor (𝟙 a)).op = 𝟙 _
    rw [PhiMor_id]; rfl
  map_comp g h := by
    change (PhiMor (g ≫ h)).op = (PhiMor g).op ≫ (PhiMor h).op
    rw [PhiMor_comp, op_comp]

/-! ## §8. Faithfulness -/

/-- If two graded morphisms induce the same event permutation, their underlying wedge
maps agree (`ev_reconstruct`). -/
theorem wedgeMap_eq_of_evPermN_eq {n : ℕ} {a b : ChZ n} {g g' : a ⟶ b}
    (heq : evPermN g = evPermN g') : ChZ.wedgeMap g = ChZ.wedgeMap g' := by
  apply ev_reconstruct
  funext U
  apply Fin.ext
  have hx : finCongr (ChZ.grade a).symm (finCongr (ChZ.grade a) U) = U := by
    rw [← finCongr_symm]; exact Equiv.symm_apply_apply _ _
  have e := evPermN_apply g (finCongr (ChZ.grade a) U)
  have e' := evPermN_apply g' (finCongr (ChZ.grade a) U)
  rw [hx] at e e'
  rw [← e, ← e', heq]

/-- **`Φ n` is faithful.**  Distinct graded morphisms give distinct event permutations
(freeness of the action pins the twist), hence distinct wedge maps (`ev_reconstruct`). -/
instance Phi_faithful (n : ℕ) : (Φ n).Faithful where
  map_injective {a b g g'} h := by
    have hmor : PhiMor g = PhiMor g' := Quiver.Hom.op_inj h
    obtain ⟨γ, hγ1, hγ2⟩ := Quotient.exact' hmor
    change γ • stdPairAt b.dims b.property = stdPairAt b.dims b.property at hγ1
    have hγ : γ = 1 := eq_one_of_smul_eq γ _ hγ1
    change γ • (evPermN g • stdPairAt a.dims a.property)
      = evPermN g' • stdPairAt a.dims a.property at hγ2
    rw [hγ, one_smul] at hγ2
    have heq : evPermN g = evPermN g' := smul_left_cancel hγ2
    exact InducedCategory.hom_ext (ChainCat.hom_ext' (wedgeMap_eq_of_evPermN_eq heq))

/-! ## §9. Bijectivity on objects and essential surjectivity -/

/-- Build a grade-`n` chain of `Z` from a dimension sequence (the classifying map into
`Z` is forced by terminality). -/
noncomputable def mkChZ {n : ℕ} (A : List ℕ+) (h : dimSum A = n) : ChZ n :=
  ⟨⟨A, toZ (BPSet.serialWedge A)⟩, h⟩

@[simp] theorem mkChZ_dims {n : ℕ} (A : List ℕ+) (h : dimSum A = n) : (mkChZ A h).dims = A := rfl

/-- **The object map is surjective.**  Every orbit `⟦x⟧` is `stdObj` of the chain whose
dimension sequence is the level-size list of `x.F` (orbit lemma `exists_smul_stdPairAt`). -/
theorem stdObj_surjective (n : ℕ) : Function.Surjective (stdObj (n := n)) := by
  intro X
  induction X using Quotient.inductionOn' with
  | h x =>
    obtain ⟨σ, h', hx⟩ := exists_smul_stdPairAt x
    refine ⟨mkChZ (levelSizes x.F) h', ?_⟩
    change (Quotient.mk'' (stdPairAt (levelSizes x.F) h') : QC n) = Quotient.mk'' x
    rw [← mk_smul_eq σ (stdPairAt (levelSizes x.F) h'), ← hx]

/-- **`Φ n` is essentially surjective** (in fact surjective on objects). -/
instance Phi_essSurj (n : ℕ) : (Φ n).EssSurj where
  mem_essImage Y := by
    obtain ⟨A, hA⟩ := stdObj_surjective n Y.unop
    refine ⟨A, ⟨eqToIso ?_⟩⟩
    change Opposite.op (stdObj A) = Y
    rw [hA, Opposite.op_unop]

/-! ## §10. Fullness and the equivalence of categories

Fullness is proved by unfolding the `Sal₀Br` order into `Ev.IsEvValid` and invoking
`Ev.evValid_exists` (the reverse of `ev_valid`); `Phi_full_interface` packages that
reduction. -/

/-- **The fullness input, closed via `Ev.evValid_exists`.**  Given a permutation `σ`
whose twist of `stdPair a` sits above `stdPair b` in the `Sal₀Br` order, there is a
`ChZ`-morphism `g` realising it (`evPermN g = σ`).

The `Sal₀Br` order `hle` unfolds into exactly `Ev.IsEvValid` of the reindexed `σ'`: the
face part gives the block map (`BrFace.le`'s monotone merge), the tie part gives the
within-block strict monotonicity; `Ev.evValid_exists` then produces a wedge map, which we
wrap into `g` (the triangle over `Z` is free by terminality). -/
theorem Phi_full_interface {n : ℕ} {a b : ChZ n} (σ : Equiv.Perm (Fin n))
    (hle : stdPairAt b.dims b.property ≤ σ • stdPairAt a.dims a.property) :
    ∃ g : a ⟶ b, evPermN g = σ := by
  have ha := ChZ.grade a
  have hb := ChZ.grade b
  have hinv : ∀ x : Fin n, σ⁻¹ (σ x) = x := fun x => σ.symm_apply_apply x
  set σ' : Fin (dimSum a.dims) ≃ Fin (dimSum b.dims) :=
    (finCongr ha).trans (σ.trans (finCongr hb.symm)) with hσ'def
  have hσ'_val : ∀ e : Fin (dimSum a.dims), (σ' e : ℕ) = (σ (finCongr ha e) : ℕ) := by
    intro e; simp only [hσ'def, Equiv.trans_apply, finCongr_apply_coe]
  have hσ'symm_val : ∀ t : Fin (dimSum b.dims),
      (σ'.symm t : ℕ) = (σ⁻¹ (finCongr hb t) : ℕ) := by
    intro t; simp only [hσ'def, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply_coe]; rfl
  have hcancel : ∀ e : Fin (dimSum a.dims), finCongr hb (σ' e) = σ (finCongr ha e) := by
    intro e; apply Fin.ext; rw [finCongr_apply_coe, hσ'_val]
  -- tie part ⇒ `σ` preserves order within source blocks
  have hσ_block : ∀ {u1 u2 : Fin n},
      blockOf a.dims (u1 : ℕ) = blockOf a.dims (u2 : ℕ) → (σ u1 < σ u2 ↔ u1 < u2) := by
    intro u1 u2 hbl
    have hpre : (σ • stdPairAt a.dims a.property).F.f (σ u1)
        = (σ • stdPairAt a.dims a.property).F.f (σ u2) := by
      apply Fin.ext
      simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, hinv, stdFaceAt_f]
      exact hbl
    have hc := hle.2 (σ u1) (σ u2) hpre
    simpa only [stdPairAt_C, stdChamber_f, id_eq, Sal₀Br.smul_C, BrFace.smul_f,
      hinv] using hc
  -- face part ⇒ block map `m`
  obtain ⟨m, hm_mono, hm_eq⟩ := hle.1
  have hm_pt : ∀ y : Fin n,
      (stdPairAt b.dims b.property).F.f y = m ((σ • stdPairAt a.dims a.property).F.f y) :=
    fun y => congrFun hm_eq y
  have hvalid : IsEvValid σ' := by
    refine ⟨?_, m, ?_, ?_⟩
    · -- within-block strict monotonicity of `σ'`
      intro i p p' hpp
      rw [Fin.lt_def, hσ'_val, hσ'_val, ← Fin.lt_def]
      have hblk : blockOf a.dims (finCongr ha (globalEquiv a.dims ⟨i, p⟩) : ℕ)
          = blockOf a.dims (finCongr ha (globalEquiv a.dims ⟨i, p'⟩) : ℕ) := by
        rw [finCongr_apply_coe, finCongr_apply_coe, blockOf_globalEquiv, blockOf_globalEquiv]
      rw [hσ_block hblk, finCongr_lt_iff]
      exact globalEquiv_block_lt i hpp
    · -- block placement
      intro i p
      apply Fin.ext
      rw [← blockOf_eq_globalEquiv_symm_fst]
      have key : (stdPairAt b.dims b.property).F.f
            (finCongr hb (σ' (globalEquiv a.dims ⟨i, p⟩))) = m i := by
        rw [hm_pt]
        congr 1
        apply Fin.ext
        simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, stdFaceAt_f]
        rw [hcancel, hinv, finCongr_apply_coe, blockOf_globalEquiv]
      have hval := congrArg (Fin.val) key
      simp only [stdPairAt_F, stdFaceAt_f, finCongr_apply_coe] at hval
      exact hval
    · -- covering
      intro t
      have hmarg : ((globalEquiv a.dims).symm (σ'.symm t)).1
          = (σ • stdPairAt a.dims a.property).F.f (finCongr hb t) := by
        apply Fin.ext
        rw [← blockOf_eq_globalEquiv_symm_fst]
        simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, stdFaceAt_f]
        rw [hσ'symm_val]
      rw [hmarg, ← hm_pt]
      apply Fin.ext
      simp only [stdPairAt_F, stdFaceAt_f]
      rw [← blockOf_eq_globalEquiv_symm_fst, finCongr_apply_coe]
  obtain ⟨φ, hφ⟩ := evValid_exists σ' hvalid
  haveI : Subsingleton (BPSet.serialWedge a.dims ⟶ Z) := zHom_subsingleton _
  refine ⟨InducedCategory.homMk ⟨φ, Subsingleton.elim _ _⟩, ?_⟩
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [evPermN_apply]
  change (ev φ (finCongr (ChZ.grade a).symm x) : ℕ) = (σ x : ℕ)
  rw [← evPerm_apply, hφ, hσ'_val]
  congr 2

/-- The up-set representative of `Φ.map g` is exactly the `evPermN g`-twist of `stdPair a`
(the aligning element at the fixed source `stdPair b` is trivial). -/
theorem homEquivUpSet_PhiMor {n : ℕ} {a b : ChZ n} (g : a ⟶ b) :
    QuotCat.homEquivUpSet (stdPairAt b.dims b.property) (stdObj a) (PhiMor g)
      = ⟨evPermN g • stdPairAt a.dims a.property, Phi_welldef g, mk_smul_eq _ _⟩ := by
  apply Subtype.ext
  change align (stdPairAt b.dims b.property) (stdPairAt b.dims b.property) rfl
      • (evPermN g • stdPairAt a.dims a.property) = evPermN g • stdPairAt a.dims a.property
  rw [align_self, one_smul]

/-- **`Φ n` is full.**  A hom `Φ.obj a ⟶ Φ.obj b` picks (via `homEquivUpSet`) an upper
element above `stdPair b`, which is an orbit twist `τ • stdPair a`; `Phi_full_interface`
realises `τ` as `evPermN g`. -/
instance Phi_full (n : ℕ) : (Φ n).Full where
  map_surjective {a b} f := by
    set upper := QuotCat.homEquivUpSet (stdPairAt b.dims b.property) (stdObj a) f.unop with hupper
    obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact' upper.2.2)
    obtain ⟨g, hg⟩ := Phi_full_interface (a := a) (b := b) τ (by rw [hτ]; exact upper.2.1)
    refine ⟨g, ?_⟩
    have hmor : PhiMor g = f.unop := by
      apply (QuotCat.homEquivUpSet (stdPairAt b.dims b.property) (stdObj a)).injective
      rw [homEquivUpSet_PhiMor, ← hupper]
      apply Subtype.ext
      change evPermN g • stdPairAt a.dims a.property = upper.val
      rw [hg]; exact hτ
    change (PhiMor g).op = f
    rw [hmor]
    exact Quiver.Hom.op_unop f

/-- **`Φ n` is an equivalence of categories** (fully faithful + essentially surjective). -/
noncomputable instance Phi_isEquivalence (n : ℕ) : (Φ n).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **Main theorem.**  `Ch(Z)_n ≌ (Sal₀Br n // Perm (Fin n))ᵒᵖ`: the grade-`n` cube
chains of the terminal bi-pointed precubical set are equivalent to the opposite of the
braid Salvetti quotient category. -/
noncomputable def PhiEquiv (n : ℕ) : ChZ n ≌ (QC n)ᵒᵖ :=
  (Φ n).asEquivalence

end FinalPrecubical
