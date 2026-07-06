import CubeChains.FinalPrecubical.QuotientCat
import Mathlib.GroupTheory.OrderOfElement

/-!
# FinalPrecubical / Salvetti

The braid-arrangement Salvetti poset `Sal₀Br n` in **level-function** coordinates,
and its order-free `Perm (Fin n)`-action.  This is Step 2 of the braid-chains
program (see `BRAID_CHAINS_README.md`).

A `BrFace n` is a surjection `f : Fin n → Fin levels`: it records a partition of the
`n` coordinates into `levels` blocks (level `j` = fibre `f⁻¹ j`).  The face order
`F ≤ F'` (coarser `≤` finer) says `F` is a monotone merge of `F'`.  A **chamber** is a
face with `levels = n` (all blocks singletons, i.e. `f` a bijection).  `Sal₀Br n`
packages a face `F` together with a chamber `C` adjacent to it (`F ≤ C`); the order is
Paris' order.

`Perm (Fin n)` relabels coordinates by `σ • f := f ∘ σ⁻¹` (a left action), and this
action is `OrderFreeAction` — the hypothesis needed to feed `Sal₀Br n` into the
quotient category `QuotCat` of Step 1.
-/

namespace FinalPrecubical

open Function

variable {n : ℕ}

/-! ## A monotone bijection of `Fin k` is the identity -/

/-- A monotone surjective self-map of `Fin k` is the identity.  (It is automatically
injective, hence a strictly monotone order-isomorphism, and the only such is `refl`.) -/
theorem monotone_surjective_eq_id {k : ℕ} {t : Fin k → Fin k}
    (hm : Monotone t) (hs : Surjective t) : t = id := by
  have hinj : Injective t := (Finite.injective_iff_surjective).mpr hs
  have hsm : StrictMono t := hm.strictMono_of_injective hinj
  have hsub : Subsingleton (Fin k ≃o Fin k) := inferInstance
  have he : StrictMono.orderIsoOfSurjective t hsm hs = OrderIso.refl (Fin k) :=
    Subsingleton.elim _ _
  have hcoe : (⇑(StrictMono.orderIsoOfSurjective t hsm hs) : Fin k → Fin k) = t :=
    StrictMono.coe_orderIsoOfSurjective t hsm hs
  rw [he] at hcoe
  simpa using hcoe.symm

/-! ## Braid faces -/

/-- A braid face on `n` coordinates: a surjection onto its levels. -/
structure BrFace (n : ℕ) where
  /-- the number of blocks/levels -/
  levels : ℕ
  /-- the level of each coordinate -/
  f : Fin n → Fin levels
  /-- every level is hit -/
  surj : Surjective f

/-- Structure equality for faces with the same `levels`, once the level functions agree. -/
theorem BrFace.mk_eq {l : ℕ} {g₁ g₂ : Fin n → Fin l}
    {p₁ : Surjective g₁} {p₂ : Surjective g₂} (h : g₁ = g₂) :
    (⟨l, g₁, p₁⟩ : BrFace n) = ⟨l, g₂, p₂⟩ := by
  subst h; rfl

/-! ### The face order -/

/-- `F ≤ F'` when `F` is a monotone merge of `F'`: some monotone
`m : Fin F'.levels → Fin F.levels` has `F.f = m ∘ F'.f`. -/
protected def BrFace.le (F F' : BrFace n) : Prop :=
  ∃ m : Fin F'.levels → Fin F.levels, Monotone m ∧ F.f = m ∘ F'.f

instance : PartialOrder (BrFace n) where
  le := BrFace.le
  le_refl F := ⟨id, monotone_id, (Function.id_comp F.f).symm⟩
  le_trans F F' F'' := by
    rintro ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
    exact ⟨m₁ ∘ m₂, hm₁.comp hm₂, by rw [e₁, e₂, Function.comp_assoc]⟩
  le_antisymm := by
    rintro F F' ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
    have hm₁surj : Surjective m₁ := fun k => by
      obtain ⟨a, ha⟩ := F.surj k; exact ⟨F'.f a, by rw [← ha, e₁]; rfl⟩
    have hm₂surj : Surjective m₂ := fun k => by
      obtain ⟨a, ha⟩ := F'.surj k; exact ⟨F.f a, by rw [← ha, e₂]; rfl⟩
    have hlev : F.levels = F'.levels := by
      have h₁ := Fintype.card_le_of_surjective m₁ hm₁surj
      have h₂ := Fintype.card_le_of_surjective m₂ hm₂surj
      simp only [Fintype.card_fin] at h₁ h₂
      omega
    obtain ⟨l, f, s⟩ := F
    obtain ⟨l', f', s'⟩ := F'
    subst hlev
    -- m₁ : Fin l → Fin l is a monotone surjection, hence id
    have hid : m₁ = id := monotone_surjective_eq_id hm₁ hm₁surj
    rw [hid, Function.id_comp] at e₁
    exact BrFace.mk_eq e₁

/-- The pointwise characterization of the face order. -/
theorem BrFace.le_iff {F F' : BrFace n} :
    F ≤ F' ↔ ∀ a b, F'.f a ≤ F'.f b → F.f a ≤ F.f b := by
  constructor
  · rintro ⟨m, hm, e⟩ a b hab
    rw [show F.f a = m (F'.f a) from congrFun e a, show F.f b = m (F'.f b) from congrFun e b]
    exact hm hab
  · intro h
    choose g hg using F'.surj
    refine ⟨fun j => F.f (g j), ?_, ?_⟩
    · intro i j hij
      exact h (g i) (g j) (by rw [hg, hg]; exact hij)
    · funext a
      exact le_antisymm (h a (g (F'.f a)) (hg (F'.f a)).ge)
        (h (g (F'.f a)) a (hg (F'.f a)).le)

/-- The face order via strict inequalities (the contrapositive form). -/
theorem BrFace.le_iff_lt {F F' : BrFace n} :
    F ≤ F' ↔ ∀ a b, F.f a < F.f b → F'.f a < F'.f b := by
  rw [BrFace.le_iff]
  constructor
  · intro h a b hlt
    by_contra hcon
    exact absurd (h b a (not_lt.mp hcon)) (not_le.mpr hlt)
  · intro h a b hle
    by_contra hcon
    exact absurd (h b a (not_le.mp hcon)) (not_lt.mpr hle)

/-- Two coordinates in the same level of the finer face are in the same level of the
coarser face. -/
theorem BrFace.tie {F F' : BrFace n} (h : F ≤ F') {a b : Fin n}
    (hab : F'.f a = F'.f b) : F.f a = F.f b := by
  obtain ⟨m, _, e⟩ := h
  rw [show F.f a = m (F'.f a) from congrFun e a, show F.f b = m (F'.f b) from congrFun e b, hab]

/-! ### Chambers -/

/-- A face is a *chamber* when it has the maximal number of levels. -/
def IsChamber (F : BrFace n) : Prop := F.levels = n

theorem IsChamber.bijective {C : BrFace n} (h : IsChamber C) : Bijective C.f :=
  (Fintype.bijective_iff_surjective_and_card C.f).mpr
    ⟨C.surj, by simp only [Fintype.card_fin]; exact h.symm⟩

theorem IsChamber.injective {C : BrFace n} (h : IsChamber C) : Injective C.f :=
  h.bijective.injective

/-- **Adjacency to a chamber** (README Step 2): `F ≤ C` iff `C.f` strictly separates
whatever `F.f` strictly separates.  (Holds for any target `F'`; the chamber hypothesis
is only mentioned in the README for orientation.) -/
theorem BrFace.adj_chamber_iff {F C : BrFace n} :
    F ≤ C ↔ ∀ a b, F.f a < F.f b → C.f a < C.f b := BrFace.le_iff_lt

/-- Two chambers inducing the same strict order are equal. -/
theorem BrFace.chamber_ext {C C' : BrFace n} (hC : IsChamber C) (hC' : IsChamber C')
    (h : ∀ a b, C.f a < C.f b ↔ C'.f a < C'.f b) : C = C' := by
  obtain ⟨lC, fC, sC⟩ := C
  obtain ⟨lC', fC', sC'⟩ := C'
  have hCe : lC = n := hC
  have hCe' : lC' = n := hC'
  subst lC; subst lC'
  have hbC : Bijective fC := Finite.surjective_iff_bijective.mp sC
  have hbC' : Bijective fC' := Finite.surjective_iff_bijective.mp sC'
  suffices hff : fC = fC' by subst hff; rfl
  obtain ⟨e, he⟩ : ∃ e : Equiv.Perm (Fin n), ∀ x, e x = fC x :=
    ⟨Equiv.ofBijective fC hbC, fun _ => rfl⟩
  have hmono : Monotone (fC' ∘ e.symm) := by
    intro u v huv
    simp only [Function.comp_apply]
    have hu : fC (e.symm u) = u := by rw [← he]; exact e.apply_symm_apply u
    have hv : fC (e.symm v) = v := by rw [← he]; exact e.apply_symm_apply v
    rcases eq_or_lt_of_le huv with heq | hlt
    · exact le_of_eq (congrArg (fun z => fC' (e.symm z)) heq)
    · exact le_of_lt ((h (e.symm u) (e.symm v)).mp (hu.trans_lt (hlt.trans_eq hv.symm)))
  have hsurj : Surjective (fC' ∘ e.symm) := hbC'.surjective.comp e.symm.surjective
  have hid : fC' ∘ e.symm = id := monotone_surjective_eq_id hmono hsurj
  funext x
  have hx := congrFun hid (e x)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] at hx
  exact (hx.trans (he x)).symm

/-! ### The `Perm (Fin n)`-action on faces -/

instance : MulAction (Equiv.Perm (Fin n)) (BrFace n) where
  smul σ F := ⟨F.levels, F.f ∘ ⇑σ⁻¹, F.surj.comp σ⁻¹.surjective⟩
  one_smul F := BrFace.mk_eq (by funext x; simp)
  mul_smul σ τ F := BrFace.mk_eq (by
    funext x
    change F.f (⇑(σ * τ)⁻¹ x) = F.f (⇑τ⁻¹ (⇑σ⁻¹ x))
    rw [mul_inv_rev]; rfl)

@[simp] theorem BrFace.smul_levels (σ : Equiv.Perm (Fin n)) (F : BrFace n) :
    (σ • F).levels = F.levels := rfl

@[simp] theorem BrFace.smul_f (σ : Equiv.Perm (Fin n)) (F : BrFace n) (x : Fin n) :
    (σ • F).f x = F.f (σ⁻¹ x) := rfl

/-- The face order is invariant under relabeling coordinates. -/
theorem BrFace.smul_le_smul_iff (σ : Equiv.Perm (Fin n)) {F F' : BrFace n} :
    σ • F ≤ σ • F' ↔ F ≤ F' := by
  have hinv : ∀ y : Fin n, σ⁻¹ (σ y) = y := fun y => σ.symm_apply_apply y
  simp only [BrFace.le_iff, BrFace.smul_f]
  constructor
  · intro h a b hab
    have H := h (σ a) (σ b)
    simp only [hinv] at H
    exact H hab
  · intro h a b hab
    exact h (σ⁻¹ a) (σ⁻¹ b) hab

/-! ## The Salvetti poset -/

/-- A point of the braid Salvetti complex: a face `F` adjacent to a chamber `C`. -/
structure Sal₀Br (n : ℕ) where
  /-- the face -/
  F : BrFace n
  /-- the adjacent chamber -/
  C : BrFace n
  /-- `C` is a chamber -/
  hC : IsChamber C
  /-- `F` is adjacent to `C` -/
  adj : F ≤ C

/-- Structure equality for `Sal₀Br` from equality of the two faces. -/
theorem Sal₀Br.ext {x y : Sal₀Br n} (hF : x.F = y.F) (hC : x.C = y.C) : x = y := by
  obtain ⟨xF, xC, xhC, xadj⟩ := x
  obtain ⟨yF, yC, yhC, yadj⟩ := y
  subst hF; subst hC; rfl

/-! ### Paris' order -/

/-- Paris' order: `(F,C) ≤ (F',C')` when `F ≤ F'` and, on every tie of the finer face
`F'`, the two chambers order the pair the same way. -/
protected def Sal₀Br.le (x y : Sal₀Br n) : Prop :=
  x.F ≤ y.F ∧
    ∀ a b, y.F.f a = y.F.f b → (x.C.f a < x.C.f b ↔ y.C.f a < y.C.f b)

instance : PartialOrder (Sal₀Br n) where
  le := Sal₀Br.le
  le_refl x := ⟨le_refl _, fun _ _ _ => Iff.rfl⟩
  le_trans x y z := by
    rintro ⟨hF₁, hC₁⟩ ⟨hF₂, hC₂⟩
    refine ⟨hF₁.trans hF₂, fun a b hab => ?_⟩
    exact (hC₁ a b (BrFace.tie hF₂ hab)).trans (hC₂ a b hab)
  le_antisymm x y := by
    rintro ⟨hF₁, hC₁⟩ ⟨hF₂, hC₂⟩
    have hFeq : x.F = y.F := le_antisymm hF₁ hF₂
    have hCeq : x.C = y.C := by
      refine BrFace.chamber_ext x.hC y.hC (fun a b => ?_)
      by_cases htie : x.F.f a = x.F.f b
      · exact hC₁ a b (BrFace.tie hF₂ htie)
      · rcases lt_or_gt_of_ne htie with hlt | hgt
        · have hx : x.C.f a < x.C.f b := (BrFace.le_iff_lt.mp x.adj) a b hlt
          have hyF : y.F.f a < y.F.f b := (BrFace.le_iff_lt.mp hF₁) a b hlt
          exact iff_of_true hx ((BrFace.le_iff_lt.mp y.adj) a b hyF)
        · have hx : x.C.f b < x.C.f a := (BrFace.le_iff_lt.mp x.adj) b a hgt
          have hyF : y.F.f b < y.F.f a := (BrFace.le_iff_lt.mp hF₁) b a hgt
          exact iff_of_false (asymm hx) (asymm ((BrFace.le_iff_lt.mp y.adj) b a hyF))
    exact Sal₀Br.ext hFeq hCeq

/-! ### The action on `Sal₀Br` -/

instance : MulAction (Equiv.Perm (Fin n)) (Sal₀Br n) where
  smul σ x := ⟨σ • x.F, σ • x.C, x.hC, (BrFace.smul_le_smul_iff σ).mpr x.adj⟩
  one_smul x := Sal₀Br.ext (one_smul (Equiv.Perm (Fin n)) x.F) (one_smul (Equiv.Perm (Fin n)) x.C)
  mul_smul σ τ x := Sal₀Br.ext (mul_smul σ τ x.F) (mul_smul σ τ x.C)

@[simp] theorem Sal₀Br.smul_F (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    (σ • x).F = σ • x.F := rfl

@[simp] theorem Sal₀Br.smul_C (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n) :
    (σ • x).C = σ • x.C := rfl

/-! ### `OrderFreeAction` -/

/-- Paris' order is invariant under relabeling. -/
theorem Sal₀Br.smul_le_smul_iff (σ : Equiv.Perm (Fin n)) {x y : Sal₀Br n} :
    σ • x ≤ σ • y ↔ x ≤ y := by
  constructor
  · rintro ⟨hF, hC⟩
    have hinv : ∀ y : Fin n, σ⁻¹ (σ y) = y := fun y => σ.symm_apply_apply y
    refine ⟨(BrFace.smul_le_smul_iff σ).mp hF, fun a b hab => ?_⟩
    have H := hC (σ a) (σ b)
    simp only [Sal₀Br.smul_F, Sal₀Br.smul_C, BrFace.smul_f, hinv] at H
    exact H hab
  · rintro ⟨hF, hC⟩
    refine ⟨(BrFace.smul_le_smul_iff σ).mpr hF, fun a b hab => ?_⟩
    simp only [Sal₀Br.smul_F, Sal₀Br.smul_C, BrFace.smul_f] at hab ⊢
    exact hC (σ⁻¹ a) (σ⁻¹ b) hab

/-- The key freeness input: only the identity can weakly move a point up. -/
theorem Sal₀Br.eq_one_of_le_smul (σ : Equiv.Perm (Fin n)) (x : Sal₀Br n)
    (h : x ≤ σ • x) : σ = 1 := by
  -- the whole orbit `σ^i • x` is weakly increasing above `x`
  have key : ∀ i : ℕ, x ≤ σ ^ i • x := by
    intro i
    induction i with
    | zero => simp
    | succ k ih =>
      have step : σ • x ≤ σ • (σ ^ k • x) := (Sal₀Br.smul_le_smul_iff σ).mpr ih
      rw [← mul_smul, ← pow_succ'] at step
      exact h.trans step
  have hpos : 0 < orderOf σ := orderOf_pos σ
  have hfix : σ • (σ ^ (orderOf σ - 1) • x) = x := by
    rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one, one_smul]
  have hle : σ • x ≤ x := by
    have := (Sal₀Br.smul_le_smul_iff σ).mpr (key (orderOf σ - 1))
    rwa [hfix] at this
  have hxeq : σ • x = x := le_antisymm hle h
  -- freeness via injectivity of the chamber
  have hCC : σ • x.C = x.C := congrArg Sal₀Br.C hxeq
  have hfix : ∀ i, σ⁻¹ i = i := by
    intro i
    apply x.hC.injective
    exact Fin.ext (congrArg (fun F : BrFace n => (F.f i).val) hCC)
  have : σ⁻¹ = 1 := Equiv.ext fun i => (hfix i).trans (Equiv.Perm.one_apply i).symm
  exact inv_eq_one.mp this

instance : OrderFreeAction (Equiv.Perm (Fin n)) (Sal₀Br n) where
  smul_le_smul_iff := Sal₀Br.smul_le_smul_iff
  eq_one_of_le_smul := Sal₀Br.eq_one_of_le_smul

/-! ## Standard representatives

`A : List ℕ+` names a chain in `Ch Z`: the `j`-th block has `A[j]` coordinates
("events").  Its ambient dimension is the **dims-sum** `dimSum A`, *not* the length;
`stdFace A` groups the `dimSum A` coordinates into `A.length` contiguous blocks. -/

/-- The number of coordinates/events of the chain `A` — the dims-sum.
Kept byte-identical to `Ev.dimSum` so the two are defeq for `MainFunctor`.

NOTE (name-clash resolution): `Ev.lean` independently declares a `FinalPrecubical.dimSum`
with a byte-identical body.  Two modules cannot both export the same top-level name, and
`MainFunctor` must import *both* `Salvetti` and `Ev`.  We therefore mark this copy (and its
two `nil`/`cons` lemmas) `private` so it does not collide with `Ev.dimSum`; downstream
(`MainFunctor`) uses `Ev.dimSum` by name and reaches this file's `dimSum`-typed API
(`stdPairAt`, `exists_smul_stdPairAt`, `orbit_rep_unique`, …) through the defeq of the two
byte-identical bodies. -/
private abbrev dimSum (A : List ℕ+) : ℕ := (A.map (fun n : ℕ+ => (n : ℕ))).sum

@[simp] private theorem dimSum_nil : dimSum [] = 0 := rfl

@[simp] private theorem dimSum_cons (a : ℕ+) (A : List ℕ+) :
    dimSum (a :: A) = (a : ℕ) + dimSum A := by simp [dimSum]

/-- The block index of coordinate `i` in the contiguous layout of block-sizes `A`. -/
def blockOf : List ℕ+ → ℕ → ℕ
  | [], _ => 0
  | a :: A, i => if i < (a : ℕ) then 0 else blockOf A (i - (a : ℕ)) + 1

theorem blockOf_mono (A : List ℕ+) : Monotone (blockOf A) := by
  induction A with
  | nil => intro i j _; simp [blockOf]
  | cons a A' ih =>
    intro i j hij
    simp only [blockOf]
    split_ifs with hi hj hj
    · exact le_refl 0
    · exact Nat.zero_le _
    · omega
    · exact Nat.succ_le_succ (ih (by omega))

theorem blockOf_lt (A : List ℕ+) {i : ℕ} (hi : i < dimSum A) : blockOf A i < A.length := by
  induction A generalizing i with
  | nil => simp only [dimSum_nil, Nat.not_lt_zero] at hi
  | cons a A' ih =>
    simp only [blockOf, List.length_cons]
    by_cases h : i < (a : ℕ)
    · simp only [h, if_true]; omega
    · rw [dimSum_cons] at hi
      simp only [h, if_false]
      exact Nat.succ_lt_succ (ih (by omega))

theorem blockOf_surj (A : List ℕ+) {j : ℕ} (hj : j < A.length) :
    ∃ i, i < dimSum A ∧ blockOf A i = j := by
  induction A generalizing j with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hj
  | cons a A' ih =>
    cases j with
    | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [dimSum_cons]; have := a.pos; omega
      · simp only [blockOf]; exact if_pos a.pos
    | succ j' =>
      obtain ⟨i', hi'lt, hi'eq⟩ := ih (by simpa using hj)
      refine ⟨(a : ℕ) + i', ?_, ?_⟩
      · rw [dimSum_cons]; omega
      · simp only [blockOf]
        rw [if_neg (by omega), Nat.add_sub_cancel_left, hi'eq]

/-- The standard chamber on `Fin m`: the identity relabeling. -/
def stdChamber (m : ℕ) : BrFace m where
  levels := m
  f := id
  surj := surjective_id

@[simp] theorem stdChamber_f (m : ℕ) : (stdChamber m).f = id := rfl

theorem stdChamber_isChamber (m : ℕ) : IsChamber (stdChamber m) := rfl

/-- The standard face of the chain `A`: coordinate `i` lands in the contiguous block
`blockOf A i`. -/
def stdFace (A : List ℕ+) : BrFace (dimSum A) where
  levels := A.length
  f i := ⟨blockOf A i, blockOf_lt A i.2⟩
  surj := by
    intro j
    obtain ⟨i, hi, hij⟩ := blockOf_surj A j.2
    exact ⟨⟨i, hi⟩, Fin.ext hij⟩

@[simp] theorem stdFace_f (A : List ℕ+) (i : Fin (dimSum A)) :
    ((stdFace A).f i : ℕ) = blockOf A i := rfl

@[simp] theorem stdFace_levels (A : List ℕ+) : (stdFace A).levels = A.length := rfl

/-- The standard face is adjacent to the standard chamber: the block index is monotone. -/
theorem stdFace_le_stdChamber (A : List ℕ+) :
    stdFace A ≤ stdChamber (dimSum A) := by
  rw [BrFace.le_iff]
  intro a b hab
  simp only [stdChamber_f, id_eq] at hab
  exact blockOf_mono A hab

/-- The standard Salvetti representative of the chain `A`. -/
def stdPair (A : List ℕ+) : Sal₀Br (dimSum A) where
  F := stdFace A
  C := stdChamber (dimSum A)
  hC := stdChamber_isChamber _
  adj := stdFace_le_stdChamber A

@[simp] theorem stdPair_F (A : List ℕ+) : (stdPair A).F = stdFace A := rfl

@[simp] theorem stdPair_C (A : List ℕ+) : (stdPair A).C = stdChamber (dimSum A) := rfl

/-! ## The chamber permutation and the orbit lemma -/

/-- A chamber `C` read as a permutation of `Fin n` (via `C.f` bijective).  The orbit
lemma reconstructs `x` from `stdPair` by relabeling with `(x.hC.toPerm)⁻¹`. -/
noncomputable def IsChamber.toPerm {C : BrFace n} (h : IsChamber C) : Equiv.Perm (Fin n) :=
  (Equiv.ofBijective C.f h.bijective).trans (Fin.castOrderIso h).toEquiv

@[simp] theorem IsChamber.toPerm_apply {C : BrFace n} (h : IsChamber C) (i : Fin n) :
    (h.toPerm i : ℕ) = (C.f i : ℕ) := rfl

/-- Value-level extensionality for faces. -/
theorem BrFace.ext' {F F' : BrFace n} (hlev : F.levels = F'.levels)
    (hf : ∀ i, (F.f i : ℕ) = (F'.f i : ℕ)) : F = F' := by
  obtain ⟨lF, fF, sF⟩ := F
  obtain ⟨lF', fF', sF'⟩ := F'
  subst hlev
  exact BrFace.mk_eq (funext fun i => Fin.ext (hf i))

/-- The ordered list of level sizes (fibre cardinalities) of a face — the chain `A`
recovered from `x.F` by the orbit lemma. -/
noncomputable def levelSizes (F : BrFace n) : List ℕ+ :=
  (List.finRange F.levels).map fun j =>
    ⟨(Finset.univ.filter fun i => F.f i = j).card,
      Finset.card_pos.mpr <| by
        obtain ⟨i, hi⟩ := F.surj j; exact ⟨i, by simp [hi]⟩⟩

@[simp] theorem levelSizes_length (F : BrFace n) : (levelSizes F).length = F.levels := by
  simp [levelSizes]

theorem dimSum_levelSizes (F : BrFace n) : dimSum (levelSizes F) = n := by
  classical
  have hsum : dimSum (levelSizes F)
      = ∑ j : Fin F.levels, (Finset.univ.filter fun i => F.f i = j).card := by
    simp only [dimSum, levelSizes, List.map_map]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rfl
  rw [hsum]
  have hfib := Finset.card_eq_sum_card_fiberwise (f := F.f)
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin F.levels)))
    (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  exact hfib.symm

/-- The standard face of chain `A` living at a chosen ambient `Fin n` (`dimSum A = n`).
Equal to `stdFace A` on coordinate values; avoids `▸`-transport for `MainFunctor`. -/
def stdFaceAt (A : List ℕ+) (h : dimSum A = n) : BrFace n where
  levels := A.length
  f i := ⟨blockOf A i, blockOf_lt A (by rw [h]; exact i.2)⟩
  surj := by
    intro j
    obtain ⟨iv, hlt, heq⟩ := blockOf_surj A j.2
    exact ⟨⟨iv, h ▸ hlt⟩, Fin.ext heq⟩

@[simp] theorem stdFaceAt_f (A : List ℕ+) (h : dimSum A = n) (i : Fin n) :
    ((stdFaceAt A h).f i : ℕ) = blockOf A (i : ℕ) := rfl

@[simp] theorem stdFaceAt_levels (A : List ℕ+) (h : dimSum A = n) :
    (stdFaceAt A h).levels = A.length := rfl

/-- The standard Salvetti representative of chain `A` at ambient `Fin n`. -/
def stdPairAt (A : List ℕ+) (h : dimSum A = n) : Sal₀Br n where
  F := stdFaceAt A h
  C := stdChamber n
  hC := stdChamber_isChamber n
  adj := by
    rw [BrFace.le_iff]; intro a b hab
    simp only [stdChamber_f, id_eq] at hab
    exact blockOf_mono A hab

@[simp] theorem stdPairAt_F (A : List ℕ+) (h : dimSum A = n) :
    (stdPairAt A h).F = stdFaceAt A h := rfl

@[simp] theorem stdPairAt_C (A : List ℕ+) (h : dimSum A = n) :
    (stdPairAt A h).C = stdChamber n := rfl

/-! ### Prefix sums of block sizes

`psum A j` is the sum of the first `j` block sizes of `A`; it locates block `j` as the
half-open interval `[psum A j, psum A (j+1))`, which drives both the reconstruction
identity below and the round-trip `levelSizes (stdFace A) = A`. -/

/-- Sum of the first `j` block sizes of `A`. -/
def psum (A : List ℕ+) (j : ℕ) : ℕ := ((A.map (fun p : ℕ+ => (p : ℕ))).take j).sum

@[simp] theorem psum_zero (A : List ℕ+) : psum A 0 = 0 := by simp [psum]

theorem psum_cons_succ (a : ℕ+) (A : List ℕ+) (j : ℕ) :
    psum (a :: A) (j + 1) = (a : ℕ) + psum A j := by
  simp [psum, List.map_cons, List.take_succ_cons, List.sum_cons]

theorem psum_succ (A : List ℕ+) {j : ℕ} (hj : j < A.length) :
    psum A (j + 1) = psum A j + (A.get ⟨j, hj⟩ : ℕ) := by
  unfold psum
  rw [List.take_add_one, List.sum_append]
  congr 1
  rw [List.getElem?_map, List.getElem?_eq_getElem hj]
  simp [List.get_eq_getElem]

theorem psum_le_dimSum (A : List ℕ+) (j : ℕ) : psum A j ≤ dimSum A := by
  have h : psum A j + ((A.map (fun p : ℕ+ => (p : ℕ))).drop j).sum = dimSum A := by
    rw [psum, ← List.sum_append, List.take_append_drop]
  omega

/-- Block `j` of `A` is exactly the half-open interval `[psum A j, psum A (j+1))`. -/
theorem blockOf_iff_psum (A : List ℕ+) {k j : ℕ} (hk : k < dimSum A) (hj : j < A.length) :
    blockOf A k = j ↔ psum A j ≤ k ∧ k < psum A (j + 1) := by
  induction A generalizing k j with
  | nil => simp only [dimSum_nil, Nat.not_lt_zero] at hk
  | cons a A' ih =>
    rw [dimSum_cons] at hk
    simp only [blockOf]
    split_ifs with hka
    · cases j with
      | zero => rw [psum_zero, psum_cons_succ, psum_zero]; omega
      | succ j' => rw [psum_cons_succ, psum_cons_succ]; omega
    · cases j with
      | zero => rw [psum_zero, psum_cons_succ, psum_zero]; omega
      | succ j' =>
        have hj' : j' < A'.length := by simp only [List.length_cons] at hj; omega
        have hk' : k - a < dimSum A' := by omega
        rw [psum_cons_succ, psum_cons_succ]
        constructor
        · intro hbl
          have hb : blockOf A' (k - a) = j' := by omega
          have := (ih hk' hj').mp hb
          omega
        · intro hpp
          have hb : psum A' j' ≤ k - a ∧ k - a < psum A' (j' + 1) := by omega
          have := (ih hk' hj').mpr hb
          omega

/-- The value of a chamber at `i` is its rank: the number of coordinates it sends below
`C.f i`. -/
theorem chamber_val_eq_card {C : BrFace n} (hC : IsChamber C) (i : Fin n) :
    (C.f i : ℕ) = (Finset.univ.filter (fun i' => C.f i' < C.f i)).card := by
  classical
  have hbij := hC.bijective
  symm
  rw [← Finset.card_range (C.f i : ℕ)]
  apply Finset.card_bij (fun i' _ => (C.f i' : ℕ))
  · intro i' hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
    rw [Finset.mem_range]; exact Fin.lt_def.mp hi'
  · intro a _ b _ hab; exact hbij.injective (Fin.val_inj.mp hab)
  · intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k < C.levels := lt_trans hk (C.f i).is_lt
    obtain ⟨i', hi'⟩ := hbij.surjective (⟨k, hkn⟩ : Fin C.levels)
    refine ⟨i', ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi']; exact Fin.lt_def.mpr hk
    · rw [hi']

/-- The `j`-th entry of `levelSizes F` is the size of level `j`. -/
theorem levelSizes_get (F : BrFace n) {j : ℕ} (hj : j < (levelSizes F).length) :
    ((levelSizes F).get ⟨j, hj⟩ : ℕ)
      = (Finset.univ.filter (fun i => (F.f i : ℕ) = j)).card := by
  have hj' : j < F.levels := by rw [levelSizes_length] at hj; exact hj
  simp only [levelSizes, List.get_eq_getElem, List.getElem_map, List.getElem_finRange,
    PNat.mk_coe]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.ext_iff]
  simp

/-- The `j`-th prefix sum of `levelSizes F` counts the coordinates in blocks below `j`. -/
theorem psum_levelSizes (F : BrFace n) : ∀ {m : ℕ}, m ≤ F.levels →
    psum (levelSizes F) m
      = (Finset.univ.filter (fun i => (F.f i : ℕ) < m)).card := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    rw [psum_zero]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => Nat.not_lt_zero _
  | succ m' ih =>
    intro hm
    have hm' : m' < F.levels := hm
    have hlen : m' < (levelSizes F).length := by rw [levelSizes_length]; exact hm'
    rw [psum_succ (levelSizes F) hlen, ih (le_of_lt hm')]
    -- the increment: the block size at level m'
    rw [levelSizes_get F hlen]
    -- split the count below m'+1 into (below m') plus (equal m')
    have hsplit : (Finset.univ.filter (fun i => (F.f i : ℕ) < m' + 1))
        = (Finset.univ.filter (fun i => (F.f i : ℕ) < m'))
          ∪ (Finset.univ.filter (fun i => (F.f i : ℕ) = m')) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro i _
      exact Nat.lt_succ_iff_lt_or_eq
    have hdisj : Disjoint (Finset.univ.filter (fun i => (F.f i : ℕ) < m'))
        (Finset.univ.filter (fun i => (F.f i : ℕ) = m')) := by
      apply Finset.disjoint_filter.mpr
      intro i _ h; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj]

/-- **Block-index reconstruction identity** (the combinatorial heart of the orbit
lemma).  The block (in the level-size layout of `x.F`) containing the `C`-position of
coordinate `i` is exactly the level of `i`.  Holds because adjacency `x.F ≤ x.C` lays
the coordinates out level-by-level in `C`-order, so block `j` occupies the positions
`[prefix j, prefix (j+1))`.

BLOCKED: the full proof is a `Finset.card` rank argument (position of `i` in `C`-order
equals `#{i' | x.F.f i' < x.F.f i}` plus a within-level offset `< |level|`); deferred. -/
theorem blockOf_levelSizes_chamber (x : Sal₀Br n) (i : Fin n) :
    blockOf (levelSizes x.F) (x.C.f i : ℕ) = (x.F.f i : ℕ) := by
  classical
  have hadj : x.F ≤ x.C := x.adj
  have hj : (x.F.f i : ℕ) < (levelSizes x.F).length := by
    rw [levelSizes_length]; exact (x.F.f i).is_lt
  have hk : (x.C.f i : ℕ) < dimSum (levelSizes x.F) := by
    have hlev : x.C.levels = n := x.hC
    rw [dimSum_levelSizes]
    exact lt_of_lt_of_le (x.C.f i).is_lt (le_of_eq hlev)
  refine (blockOf_iff_psum (levelSizes x.F) hk hj).mpr ⟨?_, ?_⟩
  · -- lower bound: psum at level `F.f i` ≤ (C.f i).val
    rw [psum_levelSizes x.F (le_of_lt (x.F.f i).is_lt), chamber_val_eq_card x.hC i]
    apply Finset.card_le_card
    intro i' hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    exact (BrFace.le_iff_lt.mp hadj) i' i (Fin.lt_def.mpr hi')
  · -- upper bound: (C.f i).val < psum at level `F.f i + 1`
    rw [psum_levelSizes x.F ((x.F.f i).is_lt), chamber_val_eq_card x.hC i]
    have hsub : Finset.univ.filter (fun i' => x.C.f i' < x.C.f i) ⊆
        Finset.univ.filter (fun i' => (x.F.f i' : ℕ) < (x.F.f i : ℕ) + 1) := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
      by_contra hcon
      rw [not_lt] at hcon
      have : x.F.f i < x.F.f i' := Fin.lt_def.mpr (by omega)
      exact absurd hi' (asymm ((BrFace.le_iff_lt.mp hadj) i i' this))
    have hmem_t : i ∈ Finset.univ.filter (fun i' => (x.F.f i' : ℕ) < (x.F.f i : ℕ) + 1) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hmem_s : i ∉ Finset.univ.filter (fun i' => x.C.f i' < x.C.f i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false,
        not_false_iff]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i, hmem_t, hmem_s⟩)

/-- **Orbit lemma, existence.**  Every `x : Sal₀Br n` is `σ • stdPairAt A h` for
`A = levelSizes x.F` (the level sizes of the face), `h : dimSum A = n`, and the
relabeling `σ = (x.hC.toPerm)⁻¹` (i.e. `σ = x.C.f⁻¹`). -/
theorem exists_smul_stdPairAt (x : Sal₀Br n) :
    ∃ (σ : Equiv.Perm (Fin n)) (h : dimSum (levelSizes x.F) = n),
      x = σ • stdPairAt (levelSizes x.F) h := by
  refine ⟨(x.hC.toPerm)⁻¹, dimSum_levelSizes x.F, Sal₀Br.ext ?_ ?_⟩
  · -- the face component
    refine BrFace.ext' (levelSizes_length x.F).symm (fun i => ?_)
    simp only [Sal₀Br.smul_F, stdPairAt_F, BrFace.smul_f, stdFaceAt_f, inv_inv,
      IsChamber.toPerm_apply]
    exact (blockOf_levelSizes_chamber x i).symm
  · -- the chamber component
    refine BrFace.ext' x.hC (fun i => ?_)
    simp [Sal₀Br.smul_C, stdPairAt_C, BrFace.smul_f, stdChamber_f]

/-- **Orbit lemma, uniqueness of the relabeling.**  For a fixed representative,
`σ` is determined (the action is free). -/
theorem smul_stdPairAt_left_cancel {A : List ℕ+} (h : dimSum A = n)
    {σ σ' : Equiv.Perm (Fin n)} (hσ : σ • stdPairAt A h = σ' • stdPairAt A h) : σ = σ' :=
  smul_left_cancel hσ

/-! ### Uniqueness of the chain `A` in the orbit representative

The level SIZES of a face are permutation-invariant and round-trip through `stdFace`, so
`A` is recovered from `x.F` — pinning `A` in `⟦σ • stdPairAt A h⟧`. -/

/-- Counting `Fin m` in a half-open value interval `[a, b)` (with `b ≤ m`). -/
theorem card_filter_Ico (m a b : ℕ) (hb : b ≤ m) :
    (Finset.univ.filter (fun i : Fin m => a ≤ (i : ℕ) ∧ (i : ℕ) < b)).card = b - a := by
  classical
  rw [← Nat.card_Ico a b]
  apply Finset.card_bij (fun (i : Fin m) _ => (i : ℕ))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_Ico]; exact hi
  · intro a₁ _ a₂ _ hh; exact Fin.val_injective hh
  · intro k hk
    rw [Finset.mem_Ico] at hk
    exact ⟨⟨k, lt_of_lt_of_le hk.2 hb⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk, rfl⟩

/-- The fibre of `blockOf A` over block `j` has exactly `A.get j` coordinates: this is the
round-trip `levelSizes (stdFace A) = A` at the level of a single block. -/
theorem stdFace_fiber_card (A : List ℕ+) {m : ℕ} (hm : dimSum A = m) (j : Fin A.length) :
    (Finset.univ.filter (fun i : Fin m => blockOf A (i : ℕ) = (j : ℕ))).card
      = (A.get j : ℕ) := by
  classical
  have hlt : (j : ℕ) < A.length := j.is_lt
  have hb : psum A ((j : ℕ) + 1) ≤ m := by rw [← hm]; exact psum_le_dimSum A _
  have hset : (Finset.univ.filter (fun i : Fin m => blockOf A (i : ℕ) = (j : ℕ)))
      = (Finset.univ.filter (fun i : Fin m =>
          psum A (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < psum A ((j : ℕ) + 1))) := by
    apply Finset.filter_congr
    intro i _
    have hik : (i : ℕ) < dimSum A := by rw [hm]; exact i.is_lt
    rw [blockOf_iff_psum A hik hlt]
  rw [hset, card_filter_Ico m (psum A (j : ℕ)) (psum A ((j : ℕ) + 1)) hb, psum_succ A hlt]
  simp

/-- **Level sizes are permutation-invariant.**  Relabeling coordinates by `σ` permutes the
fibres of the level function without changing their cardinalities or order. -/
theorem levelSizes_smul (σ : Equiv.Perm (Fin n)) (F : BrFace n) :
    levelSizes (σ • F) = levelSizes F := by
  classical
  have hcard : ∀ j : Fin F.levels,
      (Finset.univ.filter (fun i => (σ • F).f i = j)).card
        = (Finset.univ.filter (fun i => F.f i = j)).card := by
    intro j
    apply Finset.card_bij (fun i _ => σ⁻¹ i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, BrFace.smul_f] at hi ⊢
      exact hi
    · intro a _ b _ hab; exact σ⁻¹.injective hab
    · intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      refine ⟨σ i', ?_, σ.symm_apply_apply i'⟩
      have hff : (σ • F).f (σ i') = j := by
        rw [BrFace.smul_f, show σ⁻¹ (σ i') = i' from σ.symm_apply_apply i']
        exact hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hff
  unfold levelSizes
  simp only [BrFace.smul_levels]
  apply List.map_congr_left
  intro j _
  exact Subtype.ext (hcard j)

/-- **Round-trip.**  The level sizes of the standard face of `A` recover `A`. -/
theorem levelSizes_stdFace (A : List ℕ+) : levelSizes (stdFace A) = A := by
  apply List.ext_getElem
  · rw [levelSizes_length, stdFace_levels]
  · intro k h1 h2
    have hlt : k < A.length := by simpa using h2
    apply PNat.coe_injective
    have hg : ((levelSizes (stdFace A)).get ⟨k, h1⟩ : ℕ)
        = (Finset.univ.filter (fun i => ((stdFace A).f i : ℕ) = k)).card :=
      levelSizes_get (stdFace A) h1
    rw [List.get_eq_getElem] at hg
    rw [hg]
    simp only [stdFace_f]
    exact stdFace_fiber_card A rfl ⟨k, hlt⟩

/-- **Round-trip at a chosen ambient dimension.** -/
theorem levelSizes_stdFaceAt (A : List ℕ+) (h : dimSum A = n) :
    levelSizes (stdFaceAt A h) = A := by
  apply List.ext_getElem
  · rw [levelSizes_length, stdFaceAt_levels]
  · intro k h1 h2
    have hlt : k < A.length := by simpa using h2
    apply PNat.coe_injective
    have hg : ((levelSizes (stdFaceAt A h)).get ⟨k, h1⟩ : ℕ)
        = (Finset.univ.filter (fun i => ((stdFaceAt A h).f i : ℕ) = k)).card :=
      levelSizes_get (stdFaceAt A h) h1
    rw [List.get_eq_getElem] at hg
    rw [hg]
    simp only [stdFaceAt_f]
    exact stdFace_fiber_card A h ⟨k, hlt⟩

/-- **Orbit lemma, uniqueness of the representative.**  Both the chain `A` and the
relabeling `σ` are determined by the point `σ • stdPairAt A h`.  (The `A`-part uses level
sizes; the `σ`-part is freeness.) -/
theorem orbit_rep_unique {A A' : List ℕ+} (hA : dimSum A = n) (hA' : dimSum A' = n)
    {σ σ' : Equiv.Perm (Fin n)}
    (heq : σ • stdPairAt A hA = σ' • stdPairAt A' hA') : A = A' ∧ σ = σ' := by
  have hFeq : σ • (stdPairAt A hA).F = σ' • (stdPairAt A' hA').F :=
    congrArg Sal₀Br.F heq
  have hAeq : A = A' := by
    have hL : levelSizes (σ • (stdPairAt A hA).F)
        = levelSizes (σ' • (stdPairAt A' hA').F) := congrArg levelSizes hFeq
    rw [stdPairAt_F, stdPairAt_F, levelSizes_smul, levelSizes_smul,
      levelSizes_stdFaceAt, levelSizes_stdFaceAt] at hL
    exact hL
  subst hAeq
  refine ⟨rfl, ?_⟩
  have hcancel : σ • stdPairAt A hA = σ' • stdPairAt A hA := heq
  exact smul_stdPairAt_left_cancel hA hcancel

/-! ## Direction tests (n = 2) -/

section Tests

/-- The action on level functions is `σ • f = f ∘ σ⁻¹`. -/
example (F : BrFace 2) (σ : Equiv.Perm (Fin 2)) (i : Fin 2) :
    (σ • F).f i = F.f (σ⁻¹ i) := rfl

/-- It is a *left* action: `(σ * τ) • F = σ • (τ • F)`. -/
example (σ τ : Equiv.Perm (Fin 2)) (F : BrFace 2) :
    (σ * τ) • F = σ • (τ • F) := mul_smul σ τ F

/-- On `Sal₀Br`, the action moves both components by `∘ σ⁻¹`. -/
example (σ : Equiv.Perm (Fin 2)) (x : Sal₀Br 2) (i : Fin 2) :
    (σ • x).C.f i = x.C.f (σ⁻¹ i) := rfl

/-- **Orbit `σ` convention.**  The relabeling that returns `stdChamber` to the given
chamber `C` is `σ := (C.f as a permutation)⁻¹`: with `σ = (x.hC.toPerm)⁻¹` one has
`(σ • stdChamber).f = x.C.f` (up to the `levels = n` identification).  This pins the
orbit lemma's `σ = C.f⁻¹` (not `C.f`). -/
example (x : Sal₀Br 2) (i : Fin 2) :
    (((x.hC.toPerm)⁻¹ • stdChamber 2).f i : ℕ) = (x.C.f i : ℕ) := by
  simp [BrFace.smul_f, stdChamber_f]

end Tests

end FinalPrecubical
