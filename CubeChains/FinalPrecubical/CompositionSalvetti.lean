import CubeChains.FinalPrecubical.Salvetti
import CubeChains.FinalPrecubical.Ev
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# FinalPrecubical / CompositionSalvetti

A clean, `Composition`-based foundation for a new proof of the braid theorem.  This
module replaces `Salvetti.lean`'s hand-rolled composition arithmetic
(`blockOf`/`psum`/`levelSizes`) with Mathlib's `Composition n`, and re-expresses the
braid Salvetti poset `Sal₀Br n` and Paris' order in those coordinates.

## Contents

1. **Mathlib `Composition` adapter** (`listPNatEquivComposition`).
   `Composition n` (an ordered tuple of *positive* block sizes summing to `n`) is
   bridged to the repo's `List ℕ+` + `dimSum` world by
   `listPNatEquivComposition : {A : List ℕ+ // dimSum A = n} ≃ Composition n`.
   The dictionary between the two APIs:

   | Mathlib `Composition c` | repo (`Salvetti`/`Ev`) |
   |---|---|
   | `c.blocks : List ℕ`             | `A.map (·:ℕ)` (see `toComposition_blocks`) |
   | `c.length`                      | `A.length` (`toComposition_length`) |
   | `c.blocksFun i`                 | `(A.get i : ℕ)` (`toComposition_blocksFun`) |
   | `c.sizeUpTo j`                  | `psum A j` (`sizeUpTo_toComposition`) |
   | `c.index k`                     | `blockOf A k` (`blockOf_eq_index`) |
   | `c.embedding i j` (`= sizeUpTo i + j`) | serial position `finSigmaFinEquiv ⟨i,j⟩` |
   | `c.blocksFinEquiv`              | `globalEquiv A` (both `⟨i,j⟩ ↦ ∑_{k<i}·+j`) |

2. **The Salvetti reformulation** (`salEquivComposition`).
   `salEquivComposition : Sal₀Br n ≃ Composition n × Equiv.Perm (Fin n)`, sending
   `(F, C) ↦ (F ∘ C⁻¹  as a Composition,  C as a permutation)`.  Concretely the
   `Composition` records the ordered block sizes `levelSizes F` and the permutation is
   the chamber `C.hC.toPerm`.  Built by composing the orbit lemma of `Salvetti.lean`
   (`exists_smul_stdPairAt`/`orbit_rep_unique`) with the adapter of (1).

3. **The `Perm (Fin n)` action** (`salEquivComposition_smul`).
   Under the equiv the existing `MulAction` becomes right-translation on the second
   factor: `σ • (A, C) = (A, C * σ⁻¹)` (with `C * σ⁻¹ = C ∘ σ⁻¹`, trivial on the
   `Composition`).  Consequently the orbit set is exactly `Composition n`
   (`salOrbitEquiv : QuotCat (Sal₀Br n) (Perm (Fin n)) ≃ Composition n`), i.e. the
   objects of `QC n`.

4. **Paris' order in the new coordinates** (`paris_le_iff`).
   `salEquivComposition.symm (A, σ) ≤ salEquivComposition.symm (B, τ)` iff
   `(∀ a b, B.index (τ a) ≤ B.index (τ b) → A.index (σ a) ≤ A.index (σ b))` and
   `(∀ a b, B.index (τ a) = B.index (τ b) → (σ a < σ b ↔ τ a < τ b))`.

Everything here is `sorry`-free.
-/

namespace FinalPrecubical

open Function

variable {n : ℕ}

/-! ## 1. The `Composition` ↔ `List ℕ+` adapter -/

/-- A `List ℕ+` summing (via `dimSum`) to `n`, read as a `Composition n`:
its `blocks` are the underlying naturals. -/
def toComposition (A : List ℕ+) (hA : dimSum A = n) : Composition n where
  blocks := A.map (fun p : ℕ+ => (p : ℕ))
  blocks_pos := by
    intro i hi
    rw [List.mem_map] at hi
    obtain ⟨p, _, rfl⟩ := hi
    exact p.pos
  blocks_sum := hA

@[simp] theorem toComposition_blocks (A : List ℕ+) (hA : dimSum A = n) :
    (toComposition A hA).blocks = A.map (fun p : ℕ+ => (p : ℕ)) := rfl

@[simp] theorem toComposition_length (A : List ℕ+) (hA : dimSum A = n) :
    (toComposition A hA).length = A.length := by
  simp [Composition.length, toComposition_blocks]

/-- `blocksFun` of the adapted composition is the underlying natural of `A[i]`. -/
theorem toComposition_blocksFun (A : List ℕ+) (hA : dimSum A = n) (i : ℕ)
    (hi : i < A.length) :
    (toComposition A hA).blocksFun ⟨i, by rw [toComposition_length]; exact hi⟩
      = (A[i] : ℕ) := by
  simp only [Composition.blocksFun, toComposition_blocks, List.get_eq_getElem,
    List.getElem_map]

/-- Reattach positivity: turn `c.blocks : List ℕ` back into a `List ℕ+`. -/
def toList (c : Composition n) : List ℕ+ :=
  c.blocks.pmap (fun k hk => (⟨k, hk⟩ : ℕ+)) (fun _ h => c.blocks_pos h)

/-- Mapping a re-attached list back to `ℕ` recovers `c.blocks`. -/
theorem coe_toList : ∀ (c : Composition n),
    (toList c).map (fun p : ℕ+ => (p : ℕ)) = c.blocks := by
  intro c
  rw [toList, List.map_pmap]
  -- `((⟨a, h⟩ : ℕ+) : ℕ) = a`, so the pmap is the identity map
  have : ∀ (l : List ℕ) (H : ∀ a ∈ l, 0 < a),
      l.pmap (fun a h => ((⟨a, h⟩ : ℕ+) : ℕ)) H = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih => intro H; simp only [List.pmap]; rw [ih]
  exact this _ _

/-- Turning `A : List ℕ+` into `ℕ` and reattaching positivity recovers `A`. -/
theorem toList_map_coe : ∀ (A : List ℕ+) (H : ∀ a ∈ A.map (fun p : ℕ+ => (p : ℕ)), 0 < a),
    (A.map (fun p : ℕ+ => (p : ℕ))).pmap (fun k hk => (⟨k, hk⟩ : ℕ+)) H = A := by
  intro A
  induction A with
  | nil => intro _; rfl
  | cons a A ih =>
    intro H
    simp only [List.map_cons, List.pmap]
    refine congr_arg₂ (· :: ·) ?_ (ih _)
    exact Subtype.ext rfl

theorem length_toList (c : Composition n) : (toList c).length = c.length := by
  have h := coe_toList c
  calc (toList c).length
      = ((toList c).map (fun p : ℕ+ => (p : ℕ))).length := (List.length_map _).symm
    _ = c.blocks.length := by rw [h]
    _ = c.length := rfl

theorem dimSum_toList (c : Composition n) : dimSum (toList c) = n := by
  have h := coe_toList c
  simp only [dimSum, h, Composition.blocks_sum]

/-- **The adapter.** `Composition n ≃ {A : List ℕ+ // dimSum A = n}`. -/
def listPNatEquivComposition : {A : List ℕ+ // dimSum A = n} ≃ Composition n where
  toFun A := toComposition A.1 A.2
  invFun c := ⟨toList c, dimSum_toList c⟩
  left_inv := by
    rintro ⟨A, hA⟩
    refine Subtype.ext ?_
    change toList (toComposition A hA) = A
    rw [toList]
    exact toList_map_coe A _
  right_inv := by
    intro c
    refine Composition.ext ?_
    change (toComposition (toList c) (dimSum_toList c)).blocks = c.blocks
    rw [toComposition_blocks]
    exact coe_toList c

@[simp] theorem listPNatEquivComposition_apply (A : List ℕ+) (hA : dimSum A = n) :
    listPNatEquivComposition ⟨A, hA⟩ = toComposition A hA := rfl

@[simp] theorem listPNatEquivComposition_symm (c : Composition n) :
    listPNatEquivComposition.symm c = ⟨toList c, dimSum_toList c⟩ := rfl

/-! ### `psum` ↔ `sizeUpTo`, `blockOf` ↔ `index` -/

/-- `psum` of a `List ℕ+` equals `Composition.sizeUpTo` of its adapted composition. -/
theorem sizeUpTo_toComposition (A : List ℕ+) (hA : dimSum A = n) (j : ℕ) :
    (toComposition A hA).sizeUpTo j = psum A j := by
  simp only [Composition.sizeUpTo, toComposition_blocks, psum]

theorem psum_toList (c : Composition n) (j : ℕ) : psum (toList c) j = c.sizeUpTo j := by
  simp only [psum, coe_toList, Composition.sizeUpTo]

/-- **`blockOf` ↔ `Composition.index`.**  The `blockOf` layout arithmetic of `Salvetti`
is Mathlib's `Composition.index`. -/
theorem blockOf_eq_index (A : List ℕ+) (hA : dimSum A = n) (j : Fin n) :
    blockOf A (j : ℕ) = ((toComposition A hA).index j : ℕ) := by
  set c := toComposition A hA with hc
  have hk : (j : ℕ) < dimSum A := by rw [hA]; exact j.2
  have hidx : ((c.index j : ℕ)) < A.length := by
    have h1 := (c.index j).2
    have h2 : c.length = A.length := toComposition_length A hA
    omega
  rw [blockOf_iff_psum A hk hidx]
  refine ⟨?_, ?_⟩
  · rw [← sizeUpTo_toComposition A hA]
    exact c.sizeUpTo_index_le j
  · rw [← sizeUpTo_toComposition A hA]
    have h := c.lt_sizeUpTo_index_succ j
    simpa [Nat.succ_eq_add_one] using h

/-- `blockOf` on the re-attached list is `Composition.index`. -/
theorem blockOf_toList_eq_index (c : Composition n) (j : Fin n) :
    blockOf (toList c) (j : ℕ) = (c.index j : ℕ) := by
  have hk : (j : ℕ) < dimSum (toList c) := by rw [dimSum_toList]; exact j.2
  have hlen : (toList c).length = c.length := length_toList c
  have hidx : ((c.index j : ℕ)) < (toList c).length := by
    have := (c.index j).2; omega
  rw [blockOf_iff_psum (toList c) hk hidx]
  refine ⟨?_, ?_⟩
  · rw [psum_toList]; exact c.sizeUpTo_index_le j
  · rw [psum_toList]
    have h := c.lt_sizeUpTo_index_succ j
    simpa [Nat.succ_eq_add_one] using h

/-- **`globalEquiv` ↔ `blocksFinEquiv`.**  Both re-index the disjoint union of blocks by
"prefix sum + within-block offset". -/
theorem globalEquiv_val_eq (A : List ℕ+) (s : Σ i : Fin A.length, Fin (A.get i : ℕ)) :
    (globalEquiv A s : ℕ) = ∑ i : Fin s.1, (A.get (Fin.castLE s.1.2.le i) : ℕ) + s.2 := by
  rw [globalEquiv_val, finSigmaFinEquiv_apply]

/-! ## 2. The Salvetti reformulation `Sal₀Br n ≃ Composition n × Perm (Fin n)` -/

/-- The `toPerm` of the standard chamber (identity relabeling) is the identity permutation. -/
theorem stdPairAt_toPerm (A : List ℕ+) (hA : dimSum A = n) :
    (stdPairAt A hA).hC.toPerm = 1 := by
  ext i
  simp only [IsChamber.toPerm_apply, stdPairAt_C, stdChamber_f, id_eq, Equiv.Perm.one_apply]

/-- The chamber permutation of `σ • x` is right-translated:
`(σ • x).hC.toPerm = x.hC.toPerm * σ⁻¹`. -/
theorem toPerm_smul (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    (σ • x).hC.toPerm = x.hC.toPerm * σ⁻¹ := by
  ext i
  simp only [Equiv.Perm.mul_apply, IsChamber.toPerm_apply, Sal₀Br.smul_C, BrFace.smul_f]

/-- **Reconstruction (the left inverse).**  Every `x` is `(x.hC.toPerm)⁻¹` applied to the
standard representative of its level sizes.  (Explicit form of `exists_smul_stdPairAt`.) -/
theorem key_recon (x : Sal₀Br n) :
    (x.hC.toPerm)⁻¹ • stdPairAt (levelSizes x.F) (dimSum_levelSizes x.F) = x := by
  refine Sal₀Br.ext ?_ ?_
  · refine BrFace.ext' ?_ (fun i => ?_)
    · rw [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_levels, stdFaceAt_levels, levelSizes_length]
    · simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, stdFaceAt_f, inv_inv,
        IsChamber.toPerm_apply]
      exact blockOf_levelSizes_chamber x i
  · refine BrFace.ext' ?_ (fun i => ?_)
    · rw [Sal₀Br.smul_C, stdPairAt_C, BrFace.smul_levels]
      exact x.hC.symm
    · simp only [Sal₀Br.smul_C, stdPairAt_C, BrFace.smul_f, stdChamber_f, id_eq, inv_inv,
        IsChamber.toPerm_apply]

/-- The orbit lemma packaged as an equivalence with `{A : List ℕ+ // dimSum A = n} × Perm`.
`x ↦ (level sizes of x.F,  x.C as a permutation)`; the inverse is
`(A, σ) ↦ σ⁻¹ • stdPairAt A`. -/
noncomputable def orbitEquiv :
    Sal₀Br n ≃ ({A : List ℕ+ // dimSum A = n} × Equiv.Perm (Fin n)) where
  toFun x := (⟨levelSizes x.F, dimSum_levelSizes x.F⟩, x.hC.toPerm)
  invFun p := p.2⁻¹ • stdPairAt p.1.1 p.1.2
  left_inv x := key_recon x
  right_inv := by
    rintro ⟨⟨A, hA⟩, σ⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      change levelSizes (σ⁻¹ • stdPairAt A hA).F = A
      rw [Sal₀Br.smul_F, stdPairAt_F, levelSizes_smul, levelSizes_stdFaceAt]
    · change (σ⁻¹ • stdPairAt A hA).hC.toPerm = σ
      rw [toPerm_smul, inv_inv, stdPairAt_toPerm, one_mul]

@[simp] theorem orbitEquiv_apply (x : Sal₀Br n) :
    orbitEquiv x = (⟨levelSizes x.F, dimSum_levelSizes x.F⟩, x.hC.toPerm) := rfl

@[simp] theorem orbitEquiv_symm_apply (A : List ℕ+) (hA : dimSum A = n)
    (σ : Equiv.Perm (Fin n)) :
    orbitEquiv.symm (⟨A, hA⟩, σ) = σ⁻¹ • stdPairAt A hA := rfl

/-- **The Salvetti reformulation.**
`Sal₀Br n ≃ Composition n × Perm (Fin n)`, `(F, C) ↦ (F ∘ C⁻¹ as a composition, C)`. -/
noncomputable def salEquivComposition : Sal₀Br n ≃ Composition n × Equiv.Perm (Fin n) :=
  orbitEquiv.trans (listPNatEquivComposition.prodCongr (Equiv.refl _))

@[simp] theorem salEquivComposition_apply (x : Sal₀Br n) :
    salEquivComposition x
      = (toComposition (levelSizes x.F) (dimSum_levelSizes x.F), x.hC.toPerm) := rfl

@[simp] theorem salEquivComposition_symm_apply (c : Composition n) (σ : Equiv.Perm (Fin n)) :
    salEquivComposition.symm (c, σ) = σ⁻¹ • stdPairAt (toList c) (dimSum_toList c) := rfl

/-! ## 3. The `Perm (Fin n)` action in the new coordinates -/

/-- **The action.**  Under `salEquivComposition` the `MulAction` on `Sal₀Br n` becomes
right-translation on the permutation factor, trivial on the composition:
`σ • (A, C) = (A, C * σ⁻¹)` (and `C * σ⁻¹ = C ∘ σ⁻¹`). -/
theorem salEquivComposition_smul (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    salEquivComposition (σ • x)
      = ((salEquivComposition x).1, (salEquivComposition x).2 * σ⁻¹) := by
  simp only [salEquivComposition_apply]
  refine Prod.ext ?_ ?_
  · -- composition component is unchanged
    refine Composition.ext ?_
    rw [toComposition_blocks, toComposition_blocks, Sal₀Br.smul_F, levelSizes_smul]
  · -- permutation component is right-translated
    exact toPerm_smul σ x

/-- Restated pointwise for the second (permutation) component. -/
theorem salEquivComposition_smul_snd (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    (salEquivComposition (σ • x)).2 = (salEquivComposition x).2 * σ⁻¹ := by
  rw [salEquivComposition_smul]

/-- The composition component is an orbit invariant. -/
theorem salEquivComposition_smul_fst (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    (salEquivComposition (σ • x)).1 = (salEquivComposition x).1 := by
  rw [salEquivComposition_smul]

open MulAction

/-- **Objects of `QC n`.**  Since the action fixes the `Composition` and is free-transitive
on the permutation factor, the orbit set is exactly `Composition n`:
`QuotCat (Sal₀Br n) (Perm (Fin n)) ≃ Composition n`. -/
noncomputable def salOrbitEquiv :
    QuotCat (Sal₀Br n) (Equiv.Perm (Fin n)) ≃ Composition n where
  toFun := fun q => Quotient.liftOn' q (fun x => (salEquivComposition x).1) (by
    intro x y h
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 h
    change (salEquivComposition x).1 = (salEquivComposition y).1
    rw [← hg, salEquivComposition_smul_fst])
  invFun c := Quotient.mk'' (salEquivComposition.symm (c, 1))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      apply Quotient.sound'
      change salEquivComposition.symm ((salEquivComposition x).1, 1) ∈ orbit _ x
      rw [mem_orbit_iff]
      refine ⟨x.hC.toPerm, ?_⟩
      apply salEquivComposition.injective
      rw [salEquivComposition_smul, Equiv.apply_symm_apply]
      refine Prod.ext rfl ?_
      simp [salEquivComposition_apply]
  right_inv := by
    intro c
    change (salEquivComposition (salEquivComposition.symm (c, 1))).1 = c
    rw [Equiv.apply_symm_apply]

/-! ## 4. Paris' order in `Composition × Perm` coordinates -/

/-- The face value of `salEquivComposition.symm (A, σ)` is `A.index (σ i)`. -/
theorem symm_F_val (A : Composition n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ((salEquivComposition.symm (A, σ)).F.f i : ℕ) = (A.index (σ i) : ℕ) := by
  rw [salEquivComposition_symm_apply]
  simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, stdFaceAt_f, inv_inv]
  exact blockOf_toList_eq_index A (σ i)

/-- The chamber value of `salEquivComposition.symm (A, σ)` is `σ i`. -/
theorem symm_C_val (A : Composition n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ((salEquivComposition.symm (A, σ)).C.f i : ℕ) = (σ i : ℕ) := by
  rw [salEquivComposition_symm_apply]
  simp only [Sal₀Br.smul_C, stdPairAt_C, BrFace.smul_f, stdChamber_f, id_eq, inv_inv]

/-- Face order of `salEquivComposition.symm (A, σ)` in `Composition.index` terms. -/
theorem symm_F_le_iff (A : Composition n) (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (salEquivComposition.symm (A, σ)).F.f a ≤ (salEquivComposition.symm (A, σ)).F.f b
      ↔ A.index (σ a) ≤ A.index (σ b) := by
  rw [Fin.le_def, Fin.le_def, symm_F_val, symm_F_val]

/-- Face ties of `salEquivComposition.symm (A, σ)` in `Composition.index` terms. -/
theorem symm_F_eq_iff (A : Composition n) (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (salEquivComposition.symm (A, σ)).F.f a = (salEquivComposition.symm (A, σ)).F.f b
      ↔ A.index (σ a) = A.index (σ b) := by
  rw [Fin.ext_iff, Fin.ext_iff, symm_F_val, symm_F_val]

/-- Chamber comparisons of `salEquivComposition.symm (A, σ)` in `σ` terms. -/
theorem symm_C_lt_iff (A : Composition n) (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (salEquivComposition.symm (A, σ)).C.f a < (salEquivComposition.symm (A, σ)).C.f b
      ↔ σ a < σ b := by
  rw [Fin.lt_def, Fin.lt_def, symm_C_val, symm_C_val]

/-- **Paris' order in the new coordinates** (the combinatorial lemma for the morphism side).
`(A, σ) ≤ (B, τ)` (via `salEquivComposition.symm`) iff the composition `A ∘ σ` is a
monotone merge of `B ∘ τ`, and on every tie of `B ∘ τ` the two permutations rank the pair
the same way. -/
theorem paris_le_iff (A B : Composition n) (σ τ : Equiv.Perm (Fin n)) :
    salEquivComposition.symm (A, σ) ≤ salEquivComposition.symm (B, τ) ↔
      (∀ a b, B.index (τ a) ≤ B.index (τ b) → A.index (σ a) ≤ A.index (σ b)) ∧
      (∀ a b, B.index (τ a) = B.index (τ b) → (σ a < σ b ↔ τ a < τ b)) := by
  change Sal₀Br.le _ _ ↔ _
  rw [Sal₀Br.le, BrFace.le_iff]
  refine and_congr ?_ ?_
  · refine forall_congr' (fun a => forall_congr' (fun b => ?_))
    rw [symm_F_le_iff, symm_F_le_iff]
  · refine forall_congr' (fun a => forall_congr' (fun b => ?_))
    rw [symm_F_eq_iff]
    exact imp_congr_right
      (fun _ => iff_congr (symm_C_lt_iff A σ a b) (symm_C_lt_iff B τ a b))

end FinalPrecubical
