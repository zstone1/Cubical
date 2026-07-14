import CubeChains.Braid.BlockPerm
import CubeChains.Salvetti.BraidFunctor
import CubeChains.Salvetti.FreeGroupoidProd
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Salvetti/BraidDeloop — juxtaposition of braids, the delooping, and the closure of a loop

`BraidCat n` (`Salvetti/BraidFunctor.lean`) is the braid arrangement's action category on `n`
strands.  Strand counts **add** under juxtaposition, so the braids of all widths at once form a
monoidal category whose tensor is `+` on the index; its **delooping** (one object, 1-cells = braids,
horizontal composition = juxtaposition) is the target of any 2-functor out of a category whose
1-cell composition concatenates runs.

    BraidCat n × BraidCat m  --braidTensor-->  BraidCat (n + m)

On objects, juxtaposition places block 1 entirely **before** block 2: within a block the covector is
unchanged, and every cross-block pair `(i, j)` with `i` in block 1 gets the sign `-1` (the `⊑`-least
strict comparison of `BraidGround`, `sign (wᵢ − wⱼ)` with `wᵢ < wⱼ`).  On morphisms it is the block
sum of permutations.

**Sign convention.** `BraidGround N = {(a, b) : a < b}` and `braidSign w (a,b) = sign (wₐ − w_b)`,
so "`a` happens before `b`" is the sign `−1` — the same convention as the identity chamber
`braidSign (rankHt n)` (`braidSign_rankHt`), which is `−1` everywhere.

**Strictness.**  `n + 0` is definitionally `n`, so the right unit is *strict*.  `0 + n` and
`(n + m) + k` are only propositionally equal to `n` and `n + (m + k)`, so the left unitor and the
associator are the reindexing isomorphisms `braidRecast` along `finCongr`;
`salTensor_assoc`/`blockPerm_assoc` say the tensor is strictly associative *after* that reindexing,
on objects and on permutations alike.
-/

open CategoryTheory Opposite SignType

namespace CubeChains

variable {n m k : ℕ}

/-! ## Sign vectors are their sign matrices -/

/-- Two braid covectors agree iff their antisymmetric matrices do. -/
theorem signVec_ext {N : ℕ} {X Y : SignVec (BraidGround N)}
    (h : ∀ a b, signMat X a b = signMat Y a b) : X = Y := by
  rw [← ofSignMat_signMat X, ← ofSignMat_signMat Y]
  exact congrArg ofSignMat (funext fun a => funext fun b => h a b)

/-- Two Salvetti cells agree iff their faces and topes do. -/
theorem salCell_ext {E : Type*} {L : COM E} {a b : Sal L}
    (hf : a.face = b.face) (ht : a.tope = b.tope) : a = b :=
  Subtype.ext (Prod.ext_iff.mpr ⟨hf, ht⟩)

/-! ## Reindexing a braid covector along a bijection of strands

The `Sₙ`-action of `BraidFunctor` is the special case `e : Perm (Fin n)`; the general case is what
transports a braid across an equality `n = m` of strand counts (`finCongr`). -/

section Reindex

/-- Reindex a braid covector along a bijection of strand sets (pullback: contravariant, so the
covariant reindexing reads the matrix along `e.symm`). -/
def signReindex (e : Fin n ≃ Fin m) (X : SignVec (BraidGround n)) : SignVec (BraidGround m) :=
  ofSignMat fun a b => signMat X (e.symm a) (e.symm b)

theorem signReindex_apply (e : Fin n ≃ Fin m) (X : SignVec (BraidGround n)) (f : BraidGround m) :
    signReindex e X f = signMat X (e.symm f.1.1) (e.symm f.1.2) := rfl

theorem signMat_signReindex (e : Fin n ≃ Fin m) (X : SignVec (BraidGround n)) (a b : Fin m) :
    signMat (signReindex e X) a b = signMat X (e.symm a) (e.symm b) :=
  congrFun (congrFun (signMat_ofSignMat _ fun i j => signMat_antisymm X (e.symm i) (e.symm j)) a) b

@[simp] theorem signReindex_refl (X : SignVec (BraidGround n)) :
    signReindex (Equiv.refl (Fin n)) X = X := ofSignMat_signMat X

theorem signReindex_braidSign (e : Fin n ≃ Fin m) (w : Fin n → ℤ) :
    signReindex e (braidSign w) = braidSign (w ∘ ⇑e.symm) := by
  funext f
  rw [signReindex_apply, signMat_braidSign, braidSign_apply]
  rfl

theorem signReindex_mem_covectors (e : Fin n ≃ Fin m) {X : SignVec (BraidGround n)}
    (h : X ∈ (braidCOM n).covectors) : signReindex e X ∈ (braidCOM m).covectors := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w ∘ ⇑e.symm, (signReindex_braidSign e w).symm⟩

theorem signReindex_isTope (e : Fin n ≃ Fin m) {T : SignVec (BraidGround n)}
    (h : (braidCOM n).IsTope T) : (braidCOM m).IsTope (signReindex e T) := by
  rw [braidCOM_isTope_iff_injective] at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u ∘ ⇑e.symm, hu.comp e.symm.injective, signReindex_braidSign e u⟩

theorem signReindex_faceLE (e : Fin n ≃ Fin m) {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) :
    signReindex e X ⊑ signReindex e Y := by
  intro f
  rw [signReindex_apply, signReindex_apply]
  exact signMat_faceLE h _ _

theorem signReindex_comp (e : Fin n ≃ Fin m) (X Y : SignVec (BraidGround n)) :
    signReindex e (X ⊙ Y) = signReindex e X ⊙ signReindex e Y := by
  funext f
  rw [signReindex_apply, signMat_comp]
  change _ = if signReindex e X f = 0 then signReindex e Y f else signReindex e X f
  rw [signReindex_apply, signReindex_apply]

/-- Reindexing intertwines the `Sₙ`-action with `Equiv.permCongr`. -/
theorem signReindex_smul (e : Fin n ≃ Fin m) (σ : Equiv.Perm (Fin n))
    (X : SignVec (BraidGround n)) :
    signReindex e (σ • X) = (e.permCongr σ) • signReindex e X := by
  refine signVec_ext fun a b => ?_
  rw [signMat_signReindex, signMat_smul, signMat_smul, signMat_signReindex]
  have hinv : ∀ c : Fin m, e.symm ((e.permCongr σ)⁻¹ c) = σ⁻¹ (e.symm c) := by
    intro c
    have : (e.permCongr σ)⁻¹ = e.permCongr σ⁻¹ := rfl
    rw [this, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hinv, hinv]

/-- Reindexing a Salvetti cell of `braidCOM n`. -/
def salReindex (e : Fin n ≃ Fin m) (a : Sal (braidCOM n)) : Sal (braidCOM m) :=
  ⟨(signReindex e a.face, signReindex e a.tope),
    signReindex_mem_covectors e a.2.1,
    signReindex_isTope e a.2.2.1,
    signReindex_faceLE e a.2.2.2⟩

@[simp] theorem salReindex_face (e : Fin n ≃ Fin m) (a : Sal (braidCOM n)) :
    (salReindex e a).face = signReindex e a.face := rfl

@[simp] theorem salReindex_tope (e : Fin n ≃ Fin m) (a : Sal (braidCOM n)) :
    (salReindex e a).tope = signReindex e a.tope := rfl

@[simp] theorem salReindex_refl (a : Sal (braidCOM n)) :
    salReindex (Equiv.refl (Fin n)) a = a :=
  salCell_ext (signReindex_refl _) (signReindex_refl _)

theorem salReindex_le (e : Fin n ≃ Fin m) {a b : Sal (braidCOM n)} (h : a ≤ b) :
    salReindex e a ≤ salReindex e b := by
  refine ⟨signReindex_faceLE e h.1, ?_⟩
  change signReindex e b.tope = signReindex e b.face ⊙ signReindex e a.tope
  rw [← signReindex_comp, ← h.2]

theorem salReindex_smul (e : Fin n ≃ Fin m) (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    salReindex e (σ • a) = (e.permCongr σ) • salReindex e a :=
  salCell_ext (signReindex_smul e σ a.face) (signReindex_smul e σ a.tope)

/-- **Transport of braids across an equality of strand counts.**  An isomorphism of categories
(`braidRecast_obj_refl`: it is the identity when `h` is `rfl`). -/
def braidRecast (h : n = m) : BraidCat n ⥤ BraidCat m where
  obj x := ⟨salReindex (finCongr h) x.cell⟩
  map {x y} f := ⟨(finCongr h).permCongr f.1, by
    rw [← salReindex_smul]
    exact salReindex_le _ f.2⟩
  map_id x := Subtype.ext (by
    simp only [braidCat_id_val]
    exact Equiv.ext fun a => by simp)
  map_comp f g := Subtype.ext (by
    apply Equiv.ext
    intro a
    simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply])

@[simp] theorem braidRecast_obj (h : n = m) (x : BraidCat n) :
    (braidRecast h).obj x = ⟨salReindex (finCongr h) x.cell⟩ := rfl

theorem braidRecast_obj_refl (x : BraidCat n) : (braidRecast (rfl : n = n)).obj x = x := by
  have : finCongr (rfl : n = n) = Equiv.refl (Fin n) := rfl
  rw [braidRecast_obj, this, salReindex_refl]

end Reindex

/-! ## Juxtaposition of strands -/

section Tensor

/-- The antisymmetric matrix of the juxtaposed covector: the two blocks on the diagonal, and every
cross-block pair pointing from block 1 to block 2. -/
def blockMat (X : SignVec (BraidGround n)) (Y : SignVec (BraidGround m)) (a b : Fin (n + m)) :
    SignType :=
  if ha : (a : ℕ) < n then
    if hb : (b : ℕ) < n then signMat X ⟨a, ha⟩ ⟨b, hb⟩ else -1
  else
    if _hb : (b : ℕ) < n then 1
    else signMat Y ⟨(a : ℕ) - n, by have := a.isLt; omega⟩ ⟨(b : ℕ) - n, by have := b.isLt; omega⟩

variable (X : SignVec (BraidGround n)) (Y : SignVec (BraidGround m))

theorem blockMat_ll {a b : Fin (n + m)} (ha : (a : ℕ) < n) (hb : (b : ℕ) < n) :
    blockMat X Y a b = signMat X ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp only [blockMat, dif_pos ha, dif_pos hb]

theorem blockMat_lr {a b : Fin (n + m)} (ha : (a : ℕ) < n) (hb : ¬ (b : ℕ) < n) :
    blockMat X Y a b = -1 := by
  simp only [blockMat, dif_pos ha, dif_neg hb]

theorem blockMat_rl {a b : Fin (n + m)} (ha : ¬ (a : ℕ) < n) (hb : (b : ℕ) < n) :
    blockMat X Y a b = 1 := by
  simp only [blockMat, dif_neg ha, dif_pos hb]

theorem blockMat_rr {a b : Fin (n + m)} (ha : ¬ (a : ℕ) < n) (hb : ¬ (b : ℕ) < n)
    (ha' : (a : ℕ) - n < m) (hb' : (b : ℕ) - n < m) :
    blockMat X Y a b = signMat Y ⟨(a : ℕ) - n, ha'⟩ ⟨(b : ℕ) - n, hb'⟩ := by
  simp only [blockMat, dif_neg ha, dif_neg hb]

/-- `blockMat` on two named block-1 strands. -/
theorem blockMat_ll' (a b : Fin (n + m)) (i j : Fin n)
    (hai : (a : ℕ) = (i : ℕ)) (hbj : (b : ℕ) = (j : ℕ)) :
    blockMat X Y a b = signMat X i j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [blockMat_ll X Y (show (a : ℕ) < n by omega) (show (b : ℕ) < n by omega)]
  congr 1
  · exact Fin.ext hai
  · exact Fin.ext hbj

/-- `blockMat` on two named block-2 strands. -/
theorem blockMat_rr' (a b : Fin (n + m)) (i j : Fin m)
    (hai : (a : ℕ) = n + (i : ℕ)) (hbj : (b : ℕ) = n + (j : ℕ)) :
    blockMat X Y a b = signMat Y i j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [blockMat_rr X Y (show ¬ (a : ℕ) < n by omega) (show ¬ (b : ℕ) < n by omega)
    (by omega) (by omega)]
  congr 1
  · exact Fin.ext (by simp; omega)
  · exact Fin.ext (by simp; omega)

theorem blockMat_antisymm (a b : Fin (n + m)) :
    blockMat X Y b a = -blockMat X Y a b := by
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · rw [blockMat_ll X Y hb ha, blockMat_ll X Y ha hb, signMat_antisymm]
  · rw [blockMat_rl X Y hb ha, blockMat_lr X Y ha hb]
    decide
  · rw [blockMat_lr X Y hb ha, blockMat_rl X Y ha hb]
  · rw [blockMat_rr X Y hb ha (by omega) (by omega), blockMat_rr X Y ha hb (by omega) (by omega),
      signMat_antisymm]

/-- **Juxtaposition of braid covectors.** -/
def tensorSign (X : SignVec (BraidGround n)) (Y : SignVec (BraidGround m)) :
    SignVec (BraidGround (n + m)) := ofSignMat (blockMat X Y)

@[simp] theorem signMat_tensorSign : signMat (tensorSign X Y) = blockMat X Y :=
  signMat_ofSignMat _ (blockMat_antisymm X Y)

/-- The height realising a juxtaposed covector: block 1 is squeezed into `[0, n)` by its dense rank,
block 2 is lifted above `n`. -/
def blockHt (x : Fin n → ℤ) (y : Fin m → ℤ) (a : Fin (n + m)) : ℤ :=
  if h : (a : ℕ) < n then denseRank x ⟨a, h⟩
  else (n : ℤ) + denseRank y ⟨(a : ℕ) - n, by have := a.isLt; omega⟩

theorem sign_denseRank_sub (x : Fin n → ℤ) (i j : Fin n) :
    SignType.sign (denseRank x i - denseRank x j) = SignType.sign (x i - x j) := by
  have h := congrArg (fun Z => signMat Z i j) (braidSign_denseRank x)
  simpa only [signMat_braidSign] using h

theorem braidSign_blockHt (x : Fin n → ℤ) (y : Fin m → ℤ) :
    braidSign (blockHt x y) = tensorSign (braidSign x) (braidSign y) := by
  funext e
  obtain ⟨⟨a, b⟩, -⟩ := e
  change SignType.sign (blockHt x y a - blockHt x y b) = blockMat (braidSign x) (braidSign y) a b
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · rw [blockMat_ll _ _ ha hb, blockHt, dif_pos ha, blockHt, dif_pos hb, signMat_braidSign,
      sign_denseRank_sub]
  · rw [blockMat_lr _ _ ha hb, blockHt, dif_pos ha, blockHt, dif_neg hb]
    refine sign_neg ?_
    have h1 := denseRank_lt x ⟨a, ha⟩
    have h2 := denseRank_nonneg y ⟨(b : ℕ) - n, by omega⟩
    omega
  · rw [blockMat_rl _ _ ha hb, blockHt, dif_neg ha, blockHt, dif_pos hb]
    refine sign_pos ?_
    have h1 := denseRank_lt x ⟨b, hb⟩
    have h2 := denseRank_nonneg y ⟨(a : ℕ) - n, by omega⟩
    omega
  · rw [blockMat_rr _ _ ha hb (by omega) (by omega), blockHt, dif_neg ha, blockHt, dif_neg hb,
      signMat_braidSign]
    rw [show (n : ℤ) + denseRank y ⟨(a : ℕ) - n, by omega⟩
          - ((n : ℤ) + denseRank y ⟨(b : ℕ) - n, by omega⟩)
        = denseRank y ⟨(a : ℕ) - n, by omega⟩ - denseRank y ⟨(b : ℕ) - n, by omega⟩ from by ring]
    exact sign_denseRank_sub y _ _

theorem denseRank_injective {x : Fin n → ℤ} (hx : Function.Injective x) :
    Function.Injective (denseRank x) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne (fun hc => hne (hx hc)) with hl | hl
  · exact absurd h (ne_of_lt (denseRank_strictMono x hl))
  · exact absurd h (ne_of_gt (denseRank_strictMono x hl))

theorem blockHt_injective {x : Fin n → ℤ} {y : Fin m → ℤ}
    (hx : Function.Injective x) (hy : Function.Injective y) :
    Function.Injective (blockHt x y) := by
  intro a b h
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · rw [blockHt, dif_pos ha, blockHt, dif_pos hb] at h
    have h2 : (⟨(a : ℕ), ha⟩ : Fin n) = ⟨(b : ℕ), hb⟩ := denseRank_injective hx h
    exact Fin.ext (by simpa using h2)
  · rw [blockHt, dif_pos ha, blockHt, dif_neg hb] at h
    have h1 := denseRank_lt x ⟨a, ha⟩
    have h2 := denseRank_nonneg y ⟨(b : ℕ) - n, by omega⟩
    omega
  · rw [blockHt, dif_neg ha, blockHt, dif_pos hb] at h
    have h1 := denseRank_lt x ⟨b, hb⟩
    have h2 := denseRank_nonneg y ⟨(a : ℕ) - n, by omega⟩
    omega
  · rw [blockHt, dif_neg ha, blockHt, dif_neg hb] at h
    have h' : denseRank y ⟨(a : ℕ) - n, by omega⟩ = denseRank y ⟨(b : ℕ) - n, by omega⟩ := by omega
    have h2 : (⟨(a : ℕ) - n, by omega⟩ : Fin m) = ⟨(b : ℕ) - n, by omega⟩ :=
      denseRank_injective hy h'
    have h3 : (a : ℕ) - n = (b : ℕ) - n := by simpa using h2
    exact Fin.ext (by omega)

theorem tensorSign_mem_covectors {X : SignVec (BraidGround n)} {Y : SignVec (BraidGround m)}
    (hX : X ∈ (braidCOM n).covectors) (hY : Y ∈ (braidCOM m).covectors) :
    tensorSign X Y ∈ (braidCOM (n + m)).covectors := by
  obtain ⟨x, rfl⟩ := hX
  obtain ⟨y, rfl⟩ := hY
  exact ⟨blockHt x y, braidSign_blockHt x y⟩

theorem tensorSign_isTope {T : SignVec (BraidGround n)} {S : SignVec (BraidGround m)}
    (hT : (braidCOM n).IsTope T) (hS : (braidCOM m).IsTope S) :
    (braidCOM (n + m)).IsTope (tensorSign T S) := by
  rw [braidCOM_isTope_iff_injective] at hT hS ⊢
  obtain ⟨x, hx, rfl⟩ := hT
  obtain ⟨y, hy, rfl⟩ := hS
  exact ⟨blockHt x y, blockHt_injective hx hy, (braidSign_blockHt x y).symm⟩

theorem tensorSign_faceLE {X X' : SignVec (BraidGround n)} {Y Y' : SignVec (BraidGround m)}
    (hX : X ⊑ X') (hY : Y ⊑ Y') : tensorSign X Y ⊑ tensorSign X' Y' := by
  intro e
  obtain ⟨⟨a, b⟩, -⟩ := e
  change blockMat X Y a b = 0 ∨ blockMat X Y a b = blockMat X' Y' a b
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · rw [blockMat_ll X Y ha hb, blockMat_ll X' Y' ha hb]
    exact signMat_faceLE hX _ _
  · rw [blockMat_lr X Y ha hb, blockMat_lr X' Y' ha hb]; exact Or.inr rfl
  · rw [blockMat_rl X Y ha hb, blockMat_rl X' Y' ha hb]; exact Or.inr rfl
  · rw [blockMat_rr X Y ha hb (by omega) (by omega), blockMat_rr X' Y' ha hb (by omega) (by omega)]
    exact signMat_faceLE hY _ _

theorem tensorSign_comp (X X' : SignVec (BraidGround n)) (Y Y' : SignVec (BraidGround m)) :
    tensorSign (X ⊙ X') (Y ⊙ Y') = tensorSign X Y ⊙ tensorSign X' Y' := by
  refine signVec_ext fun a b => ?_
  simp only [signMat_tensorSign, signMat_comp]
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · rw [blockMat_ll _ _ ha hb, blockMat_ll X Y ha hb, blockMat_ll X' Y' ha hb, signMat_comp]
  · rw [blockMat_lr _ _ ha hb, blockMat_lr X Y ha hb,
      if_neg (by decide : ¬ ((-1 : SignType) = 0))]
  · rw [blockMat_rl _ _ ha hb, blockMat_rl X Y ha hb,
      if_neg (by decide : ¬ ((1 : SignType) = 0))]
  · rw [blockMat_rr _ _ ha hb (by omega) (by omega), blockMat_rr X Y ha hb (by omega) (by omega),
      blockMat_rr X' Y' ha hb (by omega) (by omega), signMat_comp]

/-- **Juxtaposition intertwines the two `Sₙ`-actions.** -/
theorem tensorSign_smul (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (X : SignVec (BraidGround n)) (Y : SignVec (BraidGround m)) :
    blockPerm σ τ • tensorSign X Y = tensorSign (σ • X) (τ • Y) := by
  refine signVec_ext fun a b => ?_
  simp only [signMat_smul, signMat_tensorSign]
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n <;> by_cases hb : (b : ℕ) < n
  · have ea := blockPerm_inv_val_lt σ τ a ⟨(a : ℕ), ha⟩ rfl
    have eb := blockPerm_inv_val_lt σ τ b ⟨(b : ℕ), hb⟩ rfl
    have ha' : (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) < n := by
      rw [ea]; exact (σ⁻¹ ⟨(a : ℕ), ha⟩).isLt
    have hb' : (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) < n := by
      rw [eb]; exact (σ⁻¹ ⟨(b : ℕ), hb⟩).isLt
    rw [blockMat_ll X Y ha' hb', blockMat_ll _ _ ha hb, signMat_smul]
    congr 1
    · exact Fin.ext ea
    · exact Fin.ext eb
  · have hB2 : (b : ℕ) - n < m := by omega
    have ea := blockPerm_inv_val_lt σ τ a ⟨(a : ℕ), ha⟩ rfl
    have eb := blockPerm_inv_val_ge σ τ b ⟨(b : ℕ) - n, hB2⟩
      (by exact (Nat.add_sub_cancel' (by omega)).symm)
    have ha' : (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) < n := by
      rw [ea]; exact (σ⁻¹ ⟨(a : ℕ), ha⟩).isLt
    have hb' : ¬ (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) < n := by rw [eb]; omega
    rw [blockMat_lr X Y ha' hb', blockMat_lr _ _ ha hb]
  · have hA2 : (a : ℕ) - n < m := by omega
    have ea := blockPerm_inv_val_ge σ τ a ⟨(a : ℕ) - n, hA2⟩
      (by exact (Nat.add_sub_cancel' (by omega)).symm)
    have eb := blockPerm_inv_val_lt σ τ b ⟨(b : ℕ), hb⟩ rfl
    have ha' : ¬ (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) < n := by rw [ea]; omega
    have hb' : (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) < n := by
      rw [eb]; exact (σ⁻¹ ⟨(b : ℕ), hb⟩).isLt
    rw [blockMat_rl X Y ha' hb', blockMat_rl _ _ ha hb]
  · have hA2 : (a : ℕ) - n < m := by omega
    have hB2 : (b : ℕ) - n < m := by omega
    set i : Fin m := ⟨(a : ℕ) - n, hA2⟩ with hi
    set j : Fin m := ⟨(b : ℕ) - n, hB2⟩ with hj
    have ea := blockPerm_inv_val_ge σ τ a i (by exact (Nat.add_sub_cancel' (by omega)).symm)
    have eb := blockPerm_inv_val_ge σ τ b j (by exact (Nat.add_sub_cancel' (by omega)).symm)
    have hτa := (τ⁻¹ i).isLt
    have hτb := (τ⁻¹ j).isLt
    have ha' : ¬ (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) < n := by omega
    have hb' : ¬ (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) < n := by omega
    have ha'' : (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) - n < m := by omega
    have hb'' : (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) - n < m := by omega
    have ka : (⟨(((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) - n, ha''⟩ : Fin m) = τ⁻¹ i := by
      refine Fin.ext ?_
      change (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) - n = ((τ⁻¹ i : Fin m) : ℕ)
      omega
    have kb : (⟨(((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) - n, hb''⟩ : Fin m) = τ⁻¹ j := by
      refine Fin.ext ?_
      change (((blockPerm σ τ)⁻¹ b : Fin (n + m)) : ℕ) - n = ((τ⁻¹ j : Fin m) : ℕ)
      omega
    rw [blockMat_rr X Y ha' hb' ha'' hb'', blockMat_rr _ _ ha hb hA2 hB2, signMat_smul, ka, kb]

end Tensor

/-! ## The tensor of braid categories -/

/-- **Juxtaposition of Salvetti cells**: the two bead partitions side by side, block 1 first. -/
def salTensor (a : Sal (braidCOM n)) (b : Sal (braidCOM m)) : Sal (braidCOM (n + m)) :=
  ⟨(tensorSign a.face b.face, tensorSign a.tope b.tope),
    tensorSign_mem_covectors a.2.1 b.2.1,
    tensorSign_isTope a.2.2.1 b.2.2.1,
    tensorSign_faceLE a.2.2.2 b.2.2.2⟩

@[simp] theorem salTensor_face (a : Sal (braidCOM n)) (b : Sal (braidCOM m)) :
    (salTensor a b).face = tensorSign a.face b.face := rfl

@[simp] theorem salTensor_tope (a : Sal (braidCOM n)) (b : Sal (braidCOM m)) :
    (salTensor a b).tope = tensorSign a.tope b.tope := rfl

theorem salTensor_smul (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (a : Sal (braidCOM n)) (b : Sal (braidCOM m)) :
    blockPerm σ τ • salTensor a b = salTensor (σ • a) (τ • b) :=
  salCell_ext (tensorSign_smul σ τ a.face b.face) (tensorSign_smul σ τ a.tope b.tope)

theorem salTensor_le {a a' : Sal (braidCOM n)} {b b' : Sal (braidCOM m)}
    (ha : a ≤ a') (hb : b ≤ b') : salTensor a b ≤ salTensor a' b' := by
  refine ⟨tensorSign_faceLE ha.1 hb.1, ?_⟩
  change tensorSign a'.tope b'.tope = tensorSign a'.face b'.face ⊙ tensorSign a.tope b.tope
  rw [← tensorSign_comp, ← ha.2, ← hb.2]

/-- **Juxtaposition of braids**: side-by-side strands.  On objects it is `salTensor` (block 1
entirely before block 2); on morphisms it is the block sum of permutations. -/
def braidTensor (n m : ℕ) : BraidCat n × BraidCat m ⥤ BraidCat (n + m) where
  obj p := ⟨salTensor p.1.cell p.2.cell⟩
  map {p q} f := ⟨blockPerm f.1.1 f.2.1, by
    rw [salTensor_smul]
    exact salTensor_le f.1.2 f.2.2⟩
  map_id p := Subtype.ext (by
    change blockPerm (𝟙 p.1 : p.1 ⟶ p.1).1 (𝟙 p.2 : p.2 ⟶ p.2).1 = 1
    rw [braidCat_id_val, braidCat_id_val, blockPerm_one])
  map_comp f g := Subtype.ext (by
    change blockPerm (f.1 ≫ g.1).1 (f.2 ≫ g.2).1 = blockPerm g.1.1 g.2.1 * blockPerm f.1.1 f.2.1
    rw [braidCat_comp_val, braidCat_comp_val, blockPerm_mul])

@[simp] theorem braidTensor_obj (p : BraidCat n × BraidCat m) :
    (braidTensor n m).obj p = ⟨salTensor p.1.cell p.2.cell⟩ := rfl

@[simp] theorem braidTensor_map_val {p q : BraidCat n × BraidCat m} (f : p ⟶ q) :
    ((braidTensor n m).map f).1 = blockPerm f.1.1 f.2.1 := rfl

/-! ## Coherence: strict on the right, reindexed on the left and in the middle -/

section Coherence

/-- The empty braid.  `Sal (braidCOM 0)` is a singleton (`BraidGround 0` is empty). -/
def braidUnit : BraidCat 0 :=
  ⟨⟨(braidSign 0, braidSign 0), ⟨0, rfl⟩,
    (braidCOM_isTope_iff_injective _).mpr
      ⟨0, fun a _ _ => Subsingleton.elim a _, rfl⟩,
    SignVec.faceLE_refl _⟩⟩

/-- **Right unitality is strict**: `n + 0` is definitionally `n`. -/
theorem tensorSign_unit_right (X : SignVec (BraidGround n)) (U : SignVec (BraidGround 0)) :
    tensorSign X U = X := by
  refine signVec_ext fun a b => ?_
  have hp : (⟨(a : ℕ), a.isLt⟩ : Fin n) = a := Fin.ext rfl
  have hq : (⟨(b : ℕ), b.isLt⟩ : Fin n) = b := Fin.ext rfl
  rw [signMat_tensorSign, blockMat_ll X U a.isLt b.isLt, hp, hq]

theorem salTensor_unit_right (a : Sal (braidCOM n)) : salTensor a braidUnit.cell = a :=
  salCell_ext (tensorSign_unit_right a.face braidUnit.cell.face)
    (tensorSign_unit_right a.tope braidUnit.cell.tope)

@[simp] theorem braidTensor_unit_right (x : BraidCat n) :
    (braidTensor n 0).obj (x, braidUnit) = x := by
  rw [braidTensor_obj, salTensor_unit_right]
  rfl

/-- **Left unitality**, after the reindexing `0 + n = n`. -/
theorem tensorSign_unit_left (U : SignVec (BraidGround 0)) (X : SignVec (BraidGround n)) :
    signReindex (finCongr (Nat.zero_add n)) (tensorSign U X) = X := by
  refine signVec_ext fun a b => ?_
  rw [signMat_signReindex, signMat_tensorSign]
  have ha : ¬ (((finCongr (Nat.zero_add n)).symm a : Fin (0 + n)) : ℕ) < 0 := by omega
  have hb : ¬ (((finCongr (Nat.zero_add n)).symm b : Fin (0 + n)) : ℕ) < 0 := by omega
  rw [blockMat_rr U X ha hb (by simp) (by simp)]
  congr 1

theorem salTensor_unit_left (a : Sal (braidCOM n)) :
    salReindex (finCongr (Nat.zero_add n)) (salTensor braidUnit.cell a) = a :=
  salCell_ext (tensorSign_unit_left braidUnit.cell.face a.face)
    (tensorSign_unit_left braidUnit.cell.tope a.tope)

/-- **Associativity**, after the reindexing `(n + m) + k = n + (m + k)`. -/
theorem tensorSign_assoc (X : SignVec (BraidGround n)) (Y : SignVec (BraidGround m))
    (Z : SignVec (BraidGround k)) :
    signReindex (finCongr (Nat.add_assoc n m k)) (tensorSign (tensorSign X Y) Z)
      = tensorSign X (tensorSign Y Z) := by
  refine signVec_ext fun a b => ?_
  simp only [signMat_signReindex, signMat_tensorSign]
  -- `finCongr` preserves the underlying natural number, so every block test is on `a.val`, `b.val`
  set a' : Fin (n + m + k) := (finCongr (Nat.add_assoc n m k)).symm a with ha'def
  set b' : Fin (n + m + k) := (finCongr (Nat.add_assoc n m k)).symm b with hb'def
  have hav : (a' : ℕ) = (a : ℕ) := rfl
  have hbv : (b' : ℕ) = (b : ℕ) := rfl
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : (a : ℕ) < n
  · by_cases hb : (b : ℕ) < n
    · -- both strands in `X`
      rw [blockMat_ll' (tensorSign X Y) Z a' b'
            (⟨(a : ℕ), by omega⟩ : Fin (n + m)) (⟨(b : ℕ), by omega⟩ : Fin (n + m)) rfl rfl,
        signMat_tensorSign,
        blockMat_ll' X Y _ _ (⟨(a : ℕ), ha⟩ : Fin n) (⟨(b : ℕ), hb⟩ : Fin n) rfl rfl,
        blockMat_ll' X (tensorSign Y Z) a b
          (⟨(a : ℕ), ha⟩ : Fin n) (⟨(b : ℕ), hb⟩ : Fin n) rfl rfl]
    · by_cases hb2 : (b : ℕ) < n + m
      · -- `X`, then `Y`
        rw [blockMat_ll' (tensorSign X Y) Z a' b'
              (⟨(a : ℕ), by omega⟩ : Fin (n + m)) (⟨(b : ℕ), hb2⟩ : Fin (n + m)) rfl rfl,
          signMat_tensorSign,
          @blockMat_lr n m X Y ⟨(a : ℕ), by omega⟩ ⟨(b : ℕ), hb2⟩ ha hb,
          blockMat_lr X (tensorSign Y Z) ha hb]
      · -- `X`, then `Z`
        rw [@blockMat_lr (n + m) k (tensorSign X Y) Z a' b' (by omega) (by omega),
          blockMat_lr X (tensorSign Y Z) ha hb]
  · by_cases hb : (b : ℕ) < n
    · by_cases ha2 : (a : ℕ) < n + m
      · rw [blockMat_ll' (tensorSign X Y) Z a' b'
              (⟨(a : ℕ), ha2⟩ : Fin (n + m)) (⟨(b : ℕ), by omega⟩ : Fin (n + m)) rfl rfl,
          signMat_tensorSign,
          @blockMat_rl n m X Y ⟨(a : ℕ), ha2⟩ ⟨(b : ℕ), by omega⟩ ha hb,
          blockMat_rl X (tensorSign Y Z) ha hb]
      · rw [@blockMat_rl (n + m) k (tensorSign X Y) Z a' b' (by omega) (by omega),
          blockMat_rl X (tensorSign Y Z) ha hb]
    · -- both strands past the first block
      by_cases ha2 : (a : ℕ) < n + m <;> by_cases hb2 : (b : ℕ) < n + m
      · -- both in `Y`
        rw [blockMat_ll' (tensorSign X Y) Z a' b'
              (⟨(a : ℕ), ha2⟩ : Fin (n + m)) (⟨(b : ℕ), hb2⟩ : Fin (n + m)) rfl rfl,
          signMat_tensorSign,
          blockMat_rr' X Y _ _ (⟨(a : ℕ) - n, by omega⟩ : Fin m) (⟨(b : ℕ) - n, by omega⟩ : Fin m)
            (by exact (show (a : ℕ) = n + ((a : ℕ) - n) by omega))
            (by exact (show (b : ℕ) = n + ((b : ℕ) - n) by omega)),
          blockMat_rr' X (tensorSign Y Z) a b
            (⟨(a : ℕ) - n, by omega⟩ : Fin (m + k)) (⟨(b : ℕ) - n, by omega⟩ : Fin (m + k))
            (by exact (show (a : ℕ) = n + ((a : ℕ) - n) by omega))
            (by exact (show (b : ℕ) = n + ((b : ℕ) - n) by omega)),
          signMat_tensorSign,
          blockMat_ll' Y Z _ _ (⟨(a : ℕ) - n, by omega⟩ : Fin m) (⟨(b : ℕ) - n, by omega⟩ : Fin m)
            rfl rfl]
      · -- `Y`, then `Z`
        rw [@blockMat_lr (n + m) k (tensorSign X Y) Z a' b' (by omega) (by omega),
          blockMat_rr' X (tensorSign Y Z) a b
            (⟨(a : ℕ) - n, by omega⟩ : Fin (m + k)) (⟨(b : ℕ) - n, by omega⟩ : Fin (m + k))
            (by exact (show (a : ℕ) = n + ((a : ℕ) - n) by omega))
            (by exact (show (b : ℕ) = n + ((b : ℕ) - n) by omega)),
          signMat_tensorSign,
          @blockMat_lr m k Y Z ⟨(a : ℕ) - n, by omega⟩ ⟨(b : ℕ) - n, by omega⟩
            (by exact (show (a : ℕ) - n < m by omega)) (by exact (show ¬ (b : ℕ) - n < m by omega))]
      · -- `Z`, then `Y`
        rw [@blockMat_rl (n + m) k (tensorSign X Y) Z a' b' (by omega) (by omega),
          blockMat_rr' X (tensorSign Y Z) a b
            (⟨(a : ℕ) - n, by omega⟩ : Fin (m + k)) (⟨(b : ℕ) - n, by omega⟩ : Fin (m + k))
            (by exact (show (a : ℕ) = n + ((a : ℕ) - n) by omega))
            (by exact (show (b : ℕ) = n + ((b : ℕ) - n) by omega)),
          signMat_tensorSign,
          @blockMat_rl m k Y Z ⟨(a : ℕ) - n, by omega⟩ ⟨(b : ℕ) - n, by omega⟩
            (by exact (show ¬ (a : ℕ) - n < m by omega)) (by exact (show (b : ℕ) - n < m by omega))]
      · -- both in `Z`
        rw [blockMat_rr' (tensorSign X Y) Z a' b'
              (⟨(a : ℕ) - n - m, by omega⟩ : Fin k) (⟨(b : ℕ) - n - m, by omega⟩ : Fin k)
              (by exact (show (a : ℕ) = n + m + ((a : ℕ) - n - m) by omega))
              (by exact (show (b : ℕ) = n + m + ((b : ℕ) - n - m) by omega)),
          blockMat_rr' X (tensorSign Y Z) a b
            (⟨(a : ℕ) - n, by omega⟩ : Fin (m + k)) (⟨(b : ℕ) - n, by omega⟩ : Fin (m + k))
            (by exact (show (a : ℕ) = n + ((a : ℕ) - n) by omega))
            (by exact (show (b : ℕ) = n + ((b : ℕ) - n) by omega)),
          signMat_tensorSign,
          blockMat_rr' Y Z _ _
            (⟨(a : ℕ) - n - m, by omega⟩ : Fin k) (⟨(b : ℕ) - n - m, by omega⟩ : Fin k)
            (by exact (show (a : ℕ) - n = m + ((a : ℕ) - n - m) by omega))
            (by exact (show (b : ℕ) - n = m + ((b : ℕ) - n - m) by omega))]

theorem salTensor_assoc (a : Sal (braidCOM n)) (b : Sal (braidCOM m)) (c : Sal (braidCOM k)) :
    salReindex (finCongr (Nat.add_assoc n m k)) (salTensor (salTensor a b) c)
      = salTensor a (salTensor b c) :=
  salCell_ext (tensorSign_assoc _ _ _) (tensorSign_assoc _ _ _)

end Coherence

/-! ## The braid category `𝔅raid` and its delooping

`BraidSig` is the disjoint union of the `BraidCat n` (its objects are a strand count together with a
Salvetti cell; there are no morphisms between different strand counts).  `braidTensorSig` is
juxtaposition; `BraidGrpdSig` is its groupoidification, whose vertex groups are the braid groups.

    delooping:   one object  ★
                 1-cells     objects of `BraidGrpdSig`  =  Σ n, Sal (braidCOM n)
                 2-cells     morphisms of `BraidGrpdSig` (empty between different strand counts)
                 ∘           braidDeloopComp   (= juxtaposition, so strand counts ADD)

This is data + coherence lemmas, not a `Bicategory` instance: the associator is an `eqToIso` across
`Nat.add_assoc` (`braidTensorSig_assoc`) and mathlib's monoidal API buys nothing here. -/

section Deloop

open CategoryTheory.Sigma

/-- **The braid category**: braids of every width at once. -/
abbrev BraidSig : Type := Σ n : ℕ, BraidCat n

/-- Juxtaposition on objects. -/
def braidTensorSigObj (p : BraidSig × BraidSig) : BraidSig :=
  ⟨p.1.1 + p.2.1, ⟨salTensor p.1.2.cell p.2.2.cell⟩⟩

/-- Juxtaposing `x` (on `i` strands) with the `j`-strand braids. -/
def braidTensorFam (i j : ℕ) (x : BraidCat i) : BraidCat j ⥤ BraidSig :=
  (Functor.curryObj (braidTensor i j)).obj x ⋙ Sigma.incl (i + j)

/-- Juxtaposition with a fixed left-hand braid.

Gotcha: this goes through `Sigma.desc` and the *curried* `braidTensor` on purpose — a direct
pattern-match on a **pair** of `SigmaHom`s makes the equation compiler diverge, because the
resulting index `?i + ?j` is not a unification pattern. -/
def braidTensorCurry (i : ℕ) : BraidCat i ⥤ (BraidSig ⥤ BraidSig) where
  obj x := Sigma.desc fun j => braidTensorFam i j x
  map {x y} f := Sigma.natTrans fun j =>
    (Sigma.inclDesc (fun j => braidTensorFam i j x) j).hom ≫
      Functor.whiskerRight ((Functor.curryObj (braidTensor i j)).map f) (Sigma.incl (i + j)) ≫
      (Sigma.inclDesc (fun j => braidTensorFam i j y) j).inv
  map_id x := by
    ext ⟨j, y⟩
    simp [Functor.curryObj, braidTensorFam]
  map_comp f g := by
    ext ⟨j, y⟩
    simp [Functor.curryObj, braidTensorFam]

/-- **The tensor of the braid category**: juxtaposition, adding strand counts. -/
def braidTensorSig : BraidSig × BraidSig ⥤ BraidSig :=
  Functor.uncurry.obj (Sigma.desc braidTensorCurry)

@[simp] theorem braidTensorSig_obj (p : BraidSig × BraidSig) :
    braidTensorSig.obj p = braidTensorSigObj p := rfl

/-- Transporting an object of `BraidSig` along an equality of strand counts is the identity. -/
theorem braidSig_recast (h : n = m) (x : BraidCat n) :
    (⟨n, x⟩ : BraidSig) = ⟨m, (braidRecast h).obj x⟩ := by
  cases h
  rw [braidRecast_obj_refl]

/-- **The associator of the braid category**: juxtaposition is associative up to the strand-count
recast `(n + m) + k = n + (m + k)`. -/
theorem braidTensorSig_assoc (x : BraidCat n) (y : BraidCat m) (z : BraidCat k) :
    braidTensorSigObj (braidTensorSigObj (⟨n, x⟩, ⟨m, y⟩), ⟨k, z⟩)
      = braidTensorSigObj (⟨n, x⟩, braidTensorSigObj (⟨m, y⟩, ⟨k, z⟩)) := by
  change (⟨n + m + k, ⟨salTensor (salTensor x.cell y.cell) z.cell⟩⟩ : BraidSig)
    = ⟨n + (m + k), ⟨salTensor x.cell (salTensor y.cell z.cell)⟩⟩
  rw [braidSig_recast (Nat.add_assoc n m k)]
  exact congrArg (fun w : Sal (braidCOM (n + (m + k))) => (⟨n + (m + k), ⟨w⟩⟩ : BraidSig))
    (salTensor_assoc x.cell y.cell z.cell)

/-- The unit of the braid category. -/
def braidSigUnit : BraidSig := ⟨0, braidUnit⟩

@[simp] theorem braidTensorSig_unit_right (x : BraidCat n) :
    braidTensorSigObj (⟨n, x⟩, braidSigUnit) = ⟨n, x⟩ := by
  change (⟨n + 0, ⟨salTensor x.cell braidUnit.cell⟩⟩ : BraidSig) = ⟨n, x⟩
  rw [salTensor_unit_right]
  rfl

theorem braidTensorSig_unit_left (x : BraidCat n) :
    braidTensorSigObj (braidSigUnit, ⟨n, x⟩) = ⟨n, x⟩ := by
  change (⟨0 + n, ⟨salTensor braidUnit.cell x.cell⟩⟩ : BraidSig) = ⟨n, x⟩
  rw [braidSig_recast (Nat.zero_add n) (⟨salTensor braidUnit.cell x.cell⟩ : BraidCat (0 + n))]
  exact congrArg (fun w : Sal (braidCOM n) => (⟨n, ⟨w⟩⟩ : BraidSig)) (salTensor_unit_left x.cell)

/-- **The delooping's 2-cells**: the groupoidification of the braid category.  Its vertex groups are
the braid groups `Bₙ` (`BraidGrpd n` sits inside by `braidGrpdIncl`). -/
abbrev BraidGrpdSig : Type _ := FreeGroupoid BraidSig

/-- **Horizontal composition in the delooping** = juxtaposition, so strand counts ADD.  This is the
whole point: a 2-functor into the delooping sends composition of 1-cells to `+` on strands. -/
noncomputable def braidDeloopComp : BraidGrpdSig × BraidGrpdSig ⥤ BraidGrpdSig :=
  (freeGroupoidProdEquiv BraidSig BraidSig).inverse ⋙ FreeGroupoid.map braidTensorSig

/-- The width-`n` braid groupoid inside the delooping. -/
def braidGrpdIncl (n : ℕ) : BraidGrpd n ⥤ BraidGrpdSig :=
  FreeGroupoid.map (Sigma.incl n)

end Deloop

/-! ## Closure of a loop

The **closure** of a braid glues its top strand ends to its bottom strand ends.  For a general
2-cell `γ : x ⟶ y` with `x ≠ y` the two ends are *different* Salvetti cells and there is no
canonical gluing — the closure is only canonical for a **loop** `γ : x ⟶ x`.  For a loop of the flow
category, the `n` events are the independent operations of one iteration, the orbits of
`braidPerm γ` are the "threads" of the closure, and the braid is **pure** exactly when every
operation returns to itself, i.e. when the closure has `n` components. -/

section Closure

/-- The projection of the braid groupoid to `Sₙ` (`Bₙ ↠ Sₙ` on vertex groups). -/
noncomputable def braidPermGrpd (n : ℕ) : BraidGrpd n ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  FreeGroupoid.lift (braidPermFunctor n)

/-- **The underlying permutation of a braid.** -/
noncomputable def braidPerm {x y : BraidGrpd n} (γ : x ⟶ y) : Equiv.Perm (Fin n) :=
  (braidPermGrpd n).map γ

@[simp] theorem braidPerm_id (x : BraidGrpd n) : braidPerm (𝟙 x) = 1 :=
  (braidPermGrpd n).map_id x

theorem braidPerm_comp {x y z : BraidGrpd n} (γ : x ⟶ y) (δ : y ⟶ z) :
    braidPerm (γ ≫ δ) = braidPerm δ * braidPerm γ :=
  (braidPermGrpd n).map_comp γ δ

@[simp] theorem braidPerm_homMk {x y : BraidCat n} (f : x ⟶ y) :
    braidPerm (FreeGroupoid.homMk f) = f.1 :=
  FreeGroupoid.lift_map_homMk (braidPermFunctor n) f

/-- The braid group of a cell projects onto `Sₙ`. -/
noncomputable def braidPermHom (x : BraidGrpd n) : Aut x →* Equiv.Perm (Fin n) where
  toFun γ := braidPerm γ.hom
  map_one' := braidPerm_id x
  map_mul' f g := braidPerm_comp g.hom f.hom

/-- The number of orbits (cycles) of a permutation of `Fin n`. -/
noncomputable def cycleCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ))

theorem cycleCount_eq_iff_one (σ : Equiv.Perm (Fin n)) : cycleCount σ = n ↔ σ = 1 := by
  have hsurj : Function.Surjective (Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) :=
    Quotient.mk_surjective
  have hcardFin : Nat.card (Fin n) = n := by simp
  constructor
  · intro h
    have hbij : Function.Bijective (Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) :=
      (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcardFin.trans h.symm⟩
    refine Equiv.ext fun a => ?_
    have hsame : Equiv.Perm.SameCycle σ a (σ a) := ⟨1, by simp⟩
    exact (hbij.1 (Quotient.sound hsame)).symm
  · rintro rfl
    have hinj : Function.Injective (Quotient.mk (Equiv.Perm.SameCycle.setoid
        (1 : Equiv.Perm (Fin n)))) := fun a b hab =>
      Equiv.Perm.sameCycle_one.mp (Quotient.exact hab)
    have hcard := Nat.card_eq_of_bijective
      (Quotient.mk (Equiv.Perm.SameCycle.setoid (1 : Equiv.Perm (Fin n)))) ⟨hinj, hsurj⟩
    rw [hcardFin] at hcard
    exact hcard.symm

/-- **The number of components of the closure link** of a braid loop: the orbits of its underlying
permutation.  (Only a loop has a canonical closure — see the section docstring.) -/
noncomputable def closureComponents {x : BraidGrpd n} (γ : x ⟶ x) : ℕ :=
  cycleCount (braidPerm γ)

/-- **A loop's closure has `n` components exactly when its braid is pure.** -/
theorem closureComponents_eq_iff_pure {x : BraidGrpd n} (γ : x ⟶ x) :
    closureComponents γ = n ↔ braidPerm γ = 1 :=
  cycleCount_eq_iff_one _

@[simp] theorem closureComponents_id (x : BraidGrpd n) : closureComponents (𝟙 x) = n :=
  (closureComponents_eq_iff_pure _).mpr (braidPerm_id x)

end Closure

end CubeChains
