import CubeChains.Salvetti.Normalize
import CubeChains.Schedule.Orientation
import CubeChains.Arrangements.BraidPreorder
import Mathlib.GroupTheory.Perm.Basic

/-!
# Salvetti/BraidFunctor — the braid functor of an arbitrary `K`

For **every** bi-pointed precubical set `K` — no `NonSelfLinked`, no `AdmitsAltitude`, no thinness —
the concurrency category maps to the braid arrangement:

    Ψ : ConcCatN K n ⥤ BraidCat n ,      Φ = FreeGroupoid.map Ψ : ConcGrpdN K n ⥤ BraidGrpd n

`ConcCatN K n` is the part of `ConcCat K` on the executions with `n` events (`card (EventObj ·)` is
constant along morphisms, `card_eventObj_eq_of_hom`, so this is a union of components).
`BraidCat n` is the **action category** of `Sₙ` on the Salvetti poset `Sal (braidCOM n)`: a morphism
`x ⟶ y` is a `σ : Perm (Fin n)` with `σ • x ≤ y`.  Its vertex groups are the braid group `B n` (the
extension of `Sₙ` by the pure braid group `P n` = the `σ = 1` part, `PureBraid`).

An execution `(a, L)` names its events `EventObj a ≃ Fin n` by the line's total order `evKey`
(bead first, then the bead chamber's rank).  In that frame:

    face := braidSign (bead index of the k-th event)      (the concurrency covector)
    tope := braidSign (k)                                 (the identity chamber — always the same!)

A morphism is a refinement, and `eventMap` identifies the two event sets, so the two `evKey` frames
differ by a permutation `evPerm f : Perm (Fin n)`, and `evPerm f • Ψ x ≤ Ψ y` is the Salvetti
wall-crossing law.  Its whole content is:

* fine beads increase along the `evKey` order (lex, bead first);
* `blockIdx` is monotone (`serialWedge_blockIdx_monotone`) — a refinement never reorders beads;
* within one *fine* bead the coarse chamber restricts to the fine one
  (`linesRestrict` ∘ `Chamber.restrict`), so the coarse `evKey` order agrees there
  (`evKey_eventMap_lt`).

Gotcha: `SignVec`'s `Sₙ`-action is a **pullback**, so it is contravariant on the nose; the left
action is `σ • X := (pullback along σ⁻¹)`, whence `σ • braidSign w = braidSign (w ∘ σ⁻¹)`
(`smul_braidSign`).  Cross-bead pairs never need the coarse order: there the finer face already
decides the composite `⊙`.
-/

open CategoryTheory Opposite CubeChain SignType

namespace CubeChains

/-! ## The `Sₙ` action on braid sign vectors

A sign vector on `BraidGround n` (the pairs `i < j`) is the same thing as an antisymmetric matrix
(`signMat`/`ofSignMat`); permutations act on matrices by reindexing, which is where the sign flips
of the reversed pairs come from. -/

section SignAction

variable {n : ℕ}

/-- The antisymmetric matrix of a braid covector: `signMat X i j` is `X`'s sign at the pair
`{i, j}`, negated when the pair is read backwards. -/
def signMat (X : SignVec (BraidGround n)) (i j : Fin n) : SignType :=
  if h : i < j then X ⟨(i, j), h⟩ else if h' : j < i then -X ⟨(j, i), h'⟩ else 0

/-- A matrix, read back as a braid covector (only the `i < j` entries are seen). -/
def ofSignMat (M : Fin n → Fin n → SignType) : SignVec (BraidGround n) := fun e => M e.1.1 e.1.2

@[simp] theorem ofSignMat_apply (M : Fin n → Fin n → SignType) (e : BraidGround n) :
    ofSignMat M e = M e.1.1 e.1.2 := rfl

theorem signMat_lt (X : SignVec (BraidGround n)) {i j : Fin n} (h : i < j) :
    signMat X i j = X ⟨(i, j), h⟩ := dif_pos h

theorem signMat_gt (X : SignVec (BraidGround n)) {i j : Fin n} (h : j < i) :
    signMat X i j = -X ⟨(j, i), h⟩ := by
  rw [signMat, dif_neg (asymm h), dif_pos h]

theorem signMat_self (X : SignVec (BraidGround n)) (i : Fin n) : signMat X i i = 0 := by
  rw [signMat, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

theorem ofSignMat_signMat (X : SignVec (BraidGround n)) : ofSignMat (signMat X) = X := by
  funext e
  rw [ofSignMat_apply, signMat_lt X e.2]
  exact congrArg X (Subtype.ext rfl)

/-- `signMat` is antisymmetric. -/
theorem signMat_antisymm (X : SignVec (BraidGround n)) (i j : Fin n) :
    signMat X j i = -signMat X i j := by
  rcases lt_trichotomy i j with h | h | h
  · rw [signMat_gt X h, signMat_lt X h]
  · subst h; rw [signMat_self, neg_zero]
  · rw [signMat_lt X h, signMat_gt X h, neg_neg]

/-- A sign is its own negative only when it is zero. -/
theorem signType_eq_zero_of_eq_neg {s : SignType} (h : s = -s) : s = 0 := by
  revert h; revert s; decide

theorem neg_signType_eq_zero_iff (s : SignType) : -s = 0 ↔ s = 0 := by
  revert s; decide

/-- An antisymmetric matrix is recovered from its `i < j` entries. -/
theorem signMat_ofSignMat (M : Fin n → Fin n → SignType) (hM : ∀ i j, M j i = -M i j) :
    signMat (ofSignMat M) = M := by
  funext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [signMat_lt _ h, ofSignMat_apply]
  · subst h
    rw [signMat_self]
    exact (signType_eq_zero_of_eq_neg (hM i i)).symm
  · rw [signMat_gt _ h, ofSignMat_apply, hM i j, neg_neg]

/-- The **`Sₙ` action on braid covectors**: reindex the antisymmetric matrix.  Pullback is
contravariant, so the *left* action reindexes along `σ⁻¹`. -/
instance : SMul (Equiv.Perm (Fin n)) (SignVec (BraidGround n)) where
  smul σ X := ofSignMat fun i j => signMat X (σ⁻¹ i) (σ⁻¹ j)

theorem smul_signVec_apply (σ : Equiv.Perm (Fin n)) (X : SignVec (BraidGround n))
    (e : BraidGround n) : (σ • X) e = signMat X (σ⁻¹ e.1.1) (σ⁻¹ e.1.2) := rfl

theorem signMat_smul (σ : Equiv.Perm (Fin n)) (X : SignVec (BraidGround n)) (i j : Fin n) :
    signMat (σ • X) i j = signMat X (σ⁻¹ i) (σ⁻¹ j) := by
  have h : signMat (ofSignMat fun i j => signMat X (σ⁻¹ i) (σ⁻¹ j))
      = fun i j => signMat X (σ⁻¹ i) (σ⁻¹ j) :=
    signMat_ofSignMat _ fun i j => signMat_antisymm X (σ⁻¹ i) (σ⁻¹ j)
  exact congrFun (congrFun h i) j

instance : MulAction (Equiv.Perm (Fin n)) (SignVec (BraidGround n)) where
  one_smul X := by
    funext e
    rw [smul_signVec_apply]
    exact congrFun (ofSignMat_signMat X) e
  mul_smul σ τ X := by
    funext e
    rw [smul_signVec_apply, smul_signVec_apply, signMat_smul]
    rfl

/-- The action reads on heights as precomposition with `σ⁻¹`. -/
theorem signMat_braidSign (w : Fin n → ℤ) (i j : Fin n) :
    signMat (braidSign w) i j = SignType.sign (w i - w j) := by
  rcases lt_trichotomy i j with h | h | h
  · rw [signMat_lt _ h, braidSign_apply]
  · subst h; rw [signMat_self, sub_self, sign_zero]
  · rw [signMat_gt _ h, braidSign_apply, ← Left.sign_neg, neg_sub]

theorem smul_braidSign (σ : Equiv.Perm (Fin n)) (w : Fin n → ℤ) :
    σ • braidSign w = braidSign (w ∘ ⇑σ⁻¹) := by
  funext e
  rw [smul_signVec_apply, signMat_braidSign, braidSign_apply]
  rfl

/-! ### The action preserves the COM structure -/

theorem signMat_faceLE {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) (i j : Fin n) :
    signMat X i j = 0 ∨ signMat X i j = signMat Y i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [signMat_lt X hij, signMat_lt Y hij]; exact h _
  · subst hij; exact Or.inl (signMat_self X i)
  · rw [signMat_gt X hij, signMat_gt Y hij]
    rcases h ⟨(j, i), hij⟩ with h0 | he
    · exact Or.inl (by rw [h0, neg_zero])
    · exact Or.inr (by rw [he])

theorem signMat_comp (X Y : SignVec (BraidGround n)) (i j : Fin n) :
    signMat (X ⊙ Y) i j = if signMat X i j = 0 then signMat Y i j else signMat X i j := by
  rcases lt_trichotomy i j with h | h | h
  · rw [signMat_lt _ h, signMat_lt X h, signMat_lt Y h]; rfl
  · subst h; rw [signMat_self, signMat_self, if_pos rfl, signMat_self]
  · rw [signMat_gt _ h, signMat_gt X h, signMat_gt Y h]
    change -(if X ⟨(j, i), h⟩ = 0 then Y ⟨(j, i), h⟩ else X ⟨(j, i), h⟩) = _
    by_cases h0 : X ⟨(j, i), h⟩ = 0
    · rw [if_pos h0, if_pos ((neg_signType_eq_zero_iff _).mpr h0)]
    · rw [if_neg h0, if_neg (fun hc => h0 ((neg_signType_eq_zero_iff _).mp hc))]

theorem smul_faceLE (σ : Equiv.Perm (Fin n)) {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) :
    σ • X ⊑ σ • Y := by
  intro e
  rw [smul_signVec_apply, smul_signVec_apply]
  exact signMat_faceLE h _ _

theorem smul_comp (σ : Equiv.Perm (Fin n)) (X Y : SignVec (BraidGround n)) :
    σ • (X ⊙ Y) = (σ • X) ⊙ (σ • Y) := by
  funext e
  rw [smul_signVec_apply, signMat_comp]
  change _ = if (σ • X) e = 0 then (σ • Y) e else (σ • X) e
  rw [smul_signVec_apply, smul_signVec_apply]

theorem smul_mem_braidCovectors (σ : Equiv.Perm (Fin n)) {X : SignVec (BraidGround n)}
    (h : X ∈ (braidCOM n).covectors) : σ • X ∈ (braidCOM n).covectors := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w ∘ ⇑σ⁻¹, (smul_braidSign σ w).symm⟩

theorem smul_isTope (σ : Equiv.Perm (Fin n)) {T : SignVec (BraidGround n)}
    (h : (braidCOM n).IsTope T) : (braidCOM n).IsTope (σ • T) := by
  rw [braidCOM_isTope_iff_injective] at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u ∘ ⇑σ⁻¹, hu.comp (Equiv.injective _), smul_braidSign σ u⟩

/-! ### The action on the Salvetti poset -/

/-- `Sₙ` acts on the Salvetti cells of the braid arrangement (both components at once). -/
instance : SMul (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  smul σ a := ⟨(σ • a.face, σ • a.tope),
    smul_mem_braidCovectors σ a.2.1, smul_isTope σ a.2.2.1, smul_faceLE σ a.2.2.2⟩

@[simp] theorem salSmul_face (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (σ • a).face = σ • a.face := rfl

@[simp] theorem salSmul_tope (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (σ • a).tope = σ • a.tope := rfl

instance : MulAction (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  one_smul _ := Subtype.ext (Prod.ext_iff.mpr ⟨one_smul _ _, one_smul _ _⟩)
  mul_smul _ _ _ := Subtype.ext (Prod.ext_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩)

/-- The action is by order automorphisms of the Salvetti (Paris) order. -/
theorem salSmul_le (σ : Equiv.Perm (Fin n)) {a b : Sal (braidCOM n)} (h : a ≤ b) :
    σ • a ≤ σ • b := by
  refine ⟨smul_faceLE σ h.1, ?_⟩
  change σ • b.tope = (σ • b.face) ⊙ (σ • a.tope)
  rw [← smul_comp, ← h.2]

end SignAction

/-! ## The braid action category -/

/-- An object of the **braid action category**: a Salvetti cell of `braidCOM n`. -/
structure BraidCat (n : ℕ) where
  /-- The Salvetti cell. -/
  cell : Sal (braidCOM n)

/-- The action category of `Sₙ` on `Sal (braidCOM n)`: a morphism `x ⟶ y` is a permutation `σ`
carrying `x` below `y`.  Its vertex groups are the braid group `B n` — the extension of `Sₙ` (the
permutation part) by `π₁ (Sal (braidCOM n)) = P n` (the `σ = 1` part, `PureBraid`). -/
instance braidCatCategory (n : ℕ) : Category (BraidCat n) where
  Hom x y := { σ : Equiv.Perm (Fin n) // σ • x.cell ≤ y.cell }
  id x := ⟨1, (one_smul _ x.cell).le⟩
  comp {x y z} f g := ⟨g.1 * f.1, by
    rw [mul_smul]
    exact le_trans (salSmul_le g.1 f.2) g.2⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

@[simp] theorem braidCat_comp_val {n : ℕ} {x y z : BraidCat n} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).1 = g.1 * f.1 := rfl

@[simp] theorem braidCat_id_val {n : ℕ} (x : BraidCat n) : (𝟙 x : x ⟶ x).1 = 1 := rfl

/-- The **braid groupoid**: the groupoidification of the braid action category. -/
abbrev BraidGrpd (n : ℕ) : Type _ := FreeGroupoid (BraidCat n)

/-! ## Executions with a fixed number of events -/

variable {K : BPSet} {n : ℕ}

/-- The executions of `K` with exactly `n` events. -/
def ConcN (K : BPSet) (n : ℕ) : ObjectProperty (ConcCat K) :=
  fun x => Fintype.card (EventObj x.chain) = n

/-- The full subcategory of executions with `n` events.  Morphisms preserve the event count
(`card_eventObj_eq_of_hom`), so this is a union of connected components of `ConcCat K`. -/
abbrev ConcCatN (K : BPSet) (n : ℕ) : Type _ := (ConcN K n).FullSubcategory

/-- The groupoidification: the `n`-event part of the concurrency braid groupoid. -/
abbrev ConcGrpdN (K : BPSet) (n : ℕ) : Type _ := FreeGroupoid (ConcCatN K n)

/-- The **event names** of an execution: its events listed in the order of its line
(`evKey` — bead first, then the bead chamber's rank). -/
noncomputable def evIdx (x : ConcCatN K n) : EventObj x.obj.chain ≃ Fin n :=
  (keyEquiv (evKey x.obj.line) (evKey_injective _)).trans (finCongr x.property)

theorem evIdx_val (x : ConcCatN K n) (e : EventObj x.obj.chain) :
    ((evIdx x e : Fin n) : ℕ) = keyRank (evKey x.obj.line) e := rfl

/-- The event names enumerate the `evKey` order. -/
theorem evIdx_lt_iff (x : ConcCatN K n) (e e' : EventObj x.obj.chain) :
    evIdx x e < evIdx x e' ↔ evKey x.obj.line e < evKey x.obj.line e' := by
  rw [Fin.lt_def, evIdx_val, evIdx_val]
  refine ⟨fun h => ?_, keyRank_strictMono _⟩
  rcases lt_trichotomy (evKey x.obj.line e) (evKey x.obj.line e') with hl | he | hg
  · exact hl
  · exact absurd (congrArg (keyRank (evKey x.obj.line)) (evKey_injective _ he)) (Nat.ne_of_lt h)
  · exact absurd (keyRank_strictMono (evKey x.obj.line) hg) (by omega)

theorem evKey_symm_lt (x : ConcCatN K n) {k l : Fin n} (h : k < l) :
    evKey x.obj.line ((evIdx x).symm k) < evKey x.obj.line ((evIdx x).symm l) := by
  rw [← evIdx_lt_iff]
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The bead of the `k`-th event of `x`. -/
noncomputable def fineBead (x : ConcCatN K n) (k : Fin n) : ChainCat.Bead x.obj.chain :=
  ((evIdx x).symm k).1

/-- The **concurrency covector** of `x`, as a height: the bead index of the `k`-th event. -/
noncomputable def beadHt (x : ConcCatN K n) (k : Fin n) : ℤ := ((fineBead x k : ℕ) : ℤ)

/-- The **identity chamber** height: the `evKey` position itself. -/
def rankHt (n : ℕ) (k : Fin n) : ℤ := ((k : ℕ) : ℤ)

theorem rankHt_injective (n : ℕ) : Function.Injective (rankHt n) := by
  intro k l h
  have h' : ((k : ℕ) : ℤ) = ((l : ℕ) : ℤ) := h
  exact Fin.ext (by exact_mod_cast h')

/-- Two events in `evKey` order sit in weakly increasing beads (the key is lex, bead first). -/
theorem fineBead_le (x : ConcCatN K n) {k l : Fin n} (h : k < l) : fineBead x k ≤ fineBead x l := by
  have hk := evKey_symm_lt x h
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at hk
  rcases hk with h1 | ⟨h1, _⟩
  · exact le_of_lt (Fin.lt_def.mpr h1)
  · exact le_of_eq (Fin.ext h1)

theorem beadHt_le (x : ConcCatN K n) {k l : Fin n} (h : k < l) : beadHt x k ≤ beadHt x l := by
  have := fineBead_le x h
  simp only [beadHt]
  exact_mod_cast Fin.le_def.mp this

/-- Two `evKey`-consecutive events of the *same* bead are ordered by the bead's chamber. -/
theorem chamberRank_lt_of_lt (x : ConcCatN K n) {k l : Fin n} (h : k < l)
    (hb : fineBead x k = fineBead x l) :
    chamberRank (x.obj.line (fineBead x k)) ((evIdx x).symm k).2
      < chamberRank (x.obj.line (fineBead x l)) ((evIdx x).symm l).2 := by
  have hk := evKey_symm_lt x h
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at hk
  rcases hk with h1 | ⟨_, h2⟩
  · exact absurd (congrArg (fun i : ChainCat.Bead x.obj.chain => (i : ℕ)) hb) (Nat.ne_of_lt h1)
  · exact h2

/-! ## The Salvetti cell of an execution -/

theorem braidSign_neg_of_lt {m : ℕ} (w : Fin m → ℤ) (e : BraidGround m)
    (h : w e.1.1 < w e.1.2) : braidSign w e = -1 := by
  rw [braidSign_apply, sign_neg (by omega)]

theorem braidSign_rankHt (e : BraidGround n) : braidSign (rankHt n) e = -1 :=
  braidSign_neg_of_lt _ e (by
    have := e.2
    simp only [rankHt]
    exact_mod_cast Fin.lt_def.mp this)

/-- The concurrency covector lies below the identity chamber: a cross-bead pair is ordered the same
way by the beads and by the `evKey` positions (`fineBead_le`), and a within-bead pair is a tie. -/
theorem braidCell_faceLE (x : ConcCatN K n) :
    braidSign (beadHt x) ⊑ braidSign (rankHt n) := by
  rw [faceLE_braidSign_iff_refinesTies]
  intro e hne
  rw [braidSign_rankHt]
  exact (braidSign_neg_of_lt _ e (lt_of_le_of_ne (beadHt_le x e.2) hne)).symm

/-- **The Salvetti cell of an execution**: its bead partition (the face) inside the identity chamber
(the tope) of the `evKey` frame. -/
noncomputable def braidCell (x : ConcCatN K n) : Sal (braidCOM n) :=
  ⟨(braidSign (beadHt x), braidSign (rankHt n)),
    ⟨beadHt x, rfl⟩,
    (braidCOM_isTope_iff_injective _).mpr ⟨rankHt n, rankHt_injective n, rfl⟩,
    braidCell_faceLE x⟩

@[simp] theorem braidCell_face (x : ConcCatN K n) : (braidCell x).face = braidSign (beadHt x) := rfl

@[simp] theorem braidCell_tope (x : ConcCatN K n) : (braidCell x).tope = braidSign (rankHt n) := rfl

/-! ## The event permutation of a morphism -/

/-- The refinement underlying a morphism of executions (`y`'s chain refines `x`'s). -/
noncomputable def concRefine {x y : ConcCatN K n} (f : x ⟶ y) :
    y.obj.chain ⟶ x.obj.chain := f.hom.1.unop

theorem concRefine_line {x y : ConcCatN K n} (f : x ⟶ y) :
    linesRestrict (concRefine f) x.obj.line = y.obj.line := f.hom.2

theorem concRefine_id (x : ConcCatN K n) : concRefine (𝟙 x) = 𝟙 x.obj.chain := rfl

theorem concRefine_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    concRefine (f ≫ g) = concRefine g ≫ concRefine f := rfl

/-- **The event permutation** of a morphism: the discrepancy between the two `evKey` frames,
`eventMap` identifying the two event sets. -/
noncomputable def evPerm {x y : ConcCatN K n} (f : x ⟶ y) : Equiv.Perm (Fin n) :=
  ((evIdx x).symm.trans (eventEquiv (concRefine f)).symm).trans (evIdx y)

theorem evPerm_inv_apply {x y : ConcCatN K n} (f : x ⟶ y) (l : Fin n) :
    (evPerm f)⁻¹ l = evIdx x (eventMap (concRefine f) ((evIdx y).symm l)) := rfl

theorem evPerm_id (x : ConcCatN K n) : evPerm (𝟙 x) = 1 := by
  apply Equiv.ext
  intro k
  change evIdx x ((eventEquiv (concRefine (𝟙 x))).symm ((evIdx x).symm k)) = k
  rw [concRefine_id, eventEquiv_id]
  simp

theorem evPerm_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    evPerm (f ≫ g) = evPerm g * evPerm f := by
  apply Equiv.ext
  intro k
  change evIdx z ((eventEquiv (concRefine (f ≫ g))).symm ((evIdx x).symm k))
    = evIdx z ((eventEquiv (concRefine g)).symm
        ((evIdx y).symm (evIdx y ((eventEquiv (concRefine f)).symm ((evIdx x).symm k)))))
  rw [Equiv.symm_apply_apply, concRefine_comp, eventEquiv_comp, Equiv.symm_trans_apply]

/-! ## The wall-crossing law

`evPerm f • Ψ x ≤ Ψ y`.  The two halves:

* **face** — a cross-bead pair of `y` maps to a cross-bead pair of `x` *in the same order*
  (`serialWedge_blockIdx_monotone`);
* **tope** — a within-bead pair of `y` maps to a within-bead pair of `x` ordered by the *same*
  chamber (`evKey_eventMap_lt`), and a cross-bead pair is decided by `y`'s own face, so the coarse
  order never enters. -/

/-- The coarse bead of the `l`-th event of `y`. -/
theorem beadHt_evPerm_inv {x y : ConcCatN K n} (f : x ⟶ y) (l : Fin n) :
    beadHt x ((evPerm f)⁻¹ l) = ((blockIdx (concRefine f)ᵂ (fineBead y l) : ℕ) : ℤ) := by
  rw [beadHt, fineBead, evPerm_inv_apply, Equiv.symm_apply_apply]
  rfl

theorem rankHt_evPerm_inv {x y : ConcCatN K n} (f : x ⟶ y) (l : Fin n) :
    rankHt n ((evPerm f)⁻¹ l)
      = ((evIdx x (eventMap (concRefine f) ((evIdx y).symm l)) : ℕ) : ℤ) := by
  rw [rankHt, evPerm_inv_apply]

/-- **The within-bead core.**  Two events of one bead of the finer chain land in one bead of the
coarser chain, ordered by the *same* chamber: the fine bead's chamber is the coarse one restricted
along the free-coordinate embedding (`linesRestrict`). -/
theorem evKey_eventMap_lt {x y : ConcCatN K n} (f : x ⟶ y) {e e' : EventObj y.obj.chain}
    (hb : e.1 = e'.1) (h : evKey y.obj.line e < evKey y.obj.line e') :
    evKey x.obj.line (eventMap (concRefine f) e)
      < evKey x.obj.line (eventMap (concRefine f) e') := by
  obtain ⟨i, δ⟩ := e
  obtain ⟨i', δ'⟩ := e'
  subst hb
  -- the fine chamber is the coarse chamber, restricted
  have hline : y.obj.line i
      = (x.obj.line (blockIdx (concRefine f)ᵂ i)).restrict
          (faceEmb (blockFace (concRefine f)ᵂ i))
          (faceEmb (blockFace (concRefine f)ᵂ i)).injective :=
    congrFun (concRefine_line f).symm i
  -- the fine order of the two directions
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex] at h
  have hfine : chamberRank (y.obj.line i) δ < chamberRank (y.obj.line i) δ' := by
    rcases h with h1 | ⟨_, h2⟩
    · exact absurd h1 (lt_irrefl _)
    · exact h2
  have hcoarse : chamberRank (x.obj.line (blockIdx (concRefine f)ᵂ i))
        (faceEmb (blockFace (concRefine f)ᵂ i) δ)
      < chamberRank (x.obj.line (blockIdx (concRefine f)ᵂ i))
        (faceEmb (blockFace (concRefine f)ᵂ i) δ') := by
    rw [chamberRank_lt_iff]
    have := (chamberRank_lt_iff (y.obj.line i) δ δ').mp hfine
    rw [hline] at this
    exact this
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, hcoarse⟩

/-- **The wall-crossing law for an arbitrary `K`**: the event permutation carries the Salvetti cell
of `x` below that of `y`. -/
theorem evPerm_smul_le {x y : ConcCatN K n} (f : x ⟶ y) :
    evPerm f • braidCell x ≤ braidCell y := by
  set σ := evPerm f with hσ
  have hmono : Monotone (blockIdx (concRefine f)ᵂ) :=
    serialWedge_blockIdx_monotone (concRefine f)ᵂ (concRefine f).φ.app_init
  -- the fine bead order, and the coarse bead order it induces
  have hfine : ∀ e : BraidGround n, fineBead y e.1.1 ≤ fineBead y e.1.2 := fun e =>
    fineBead_le y e.2
  have hcoarse : ∀ e : BraidGround n,
      blockIdx (concRefine f)ᵂ (fineBead y e.1.1) ≤ blockIdx (concRefine f)ᵂ (fineBead y e.1.2) :=
    fun e => hmono (hfine e)
  -- `y`'s face is `-1` off its ties
  have hyface : ∀ e : BraidGround n, fineBead y e.1.1 ≠ fineBead y e.1.2 →
      braidSign (beadHt y) e = -1 := by
    intro e hne
    refine braidSign_neg_of_lt _ e ?_
    have : fineBead y e.1.1 < fineBead y e.1.2 := lt_of_le_of_ne (hfine e) hne
    simp only [beadHt]
    exact_mod_cast Fin.lt_def.mp this
  constructor
  · -- FACE: `σ • (x's face) ⊑ y's face`
    simp only [salSmul_face, braidCell_face, smul_braidSign]
    rw [faceLE_braidSign_iff_refinesTies]
    intro e hne
    have hc : (beadHt x ∘ ⇑σ⁻¹) e.1.1 ≠ (beadHt x ∘ ⇑σ⁻¹) e.1.2 := hne
    rw [Function.comp_apply, Function.comp_apply, beadHt_evPerm_inv, beadHt_evPerm_inv] at hc
    have hcne : blockIdx (concRefine f)ᵂ (fineBead y e.1.1)
        ≠ blockIdx (concRefine f)ᵂ (fineBead y e.1.2) := by
      intro hcon
      exact hc (by rw [hcon])
    have hbne : fineBead y e.1.1 ≠ fineBead y e.1.2 := fun hcon => hcne (by rw [hcon])
    rw [hyface e hbne]
    refine (braidSign_neg_of_lt _ e ?_).symm
    rw [Function.comp_apply, Function.comp_apply, beadHt_evPerm_inv, beadHt_evPerm_inv]
    have : blockIdx (concRefine f)ᵂ (fineBead y e.1.1)
        < blockIdx (concRefine f)ᵂ (fineBead y e.1.2) := lt_of_le_of_ne (hcoarse e) hcne
    exact_mod_cast Fin.lt_def.mp this
  · -- TOPE: `y's tope = y's face ⊙ (σ • x's tope)`
    simp only [salSmul_tope, braidCell_face, braidCell_tope, smul_braidSign]
    funext e
    change braidSign (rankHt n) e
      = if braidSign (beadHt y) e = 0 then braidSign (rankHt n ∘ ⇑σ⁻¹) e
        else braidSign (beadHt y) e
    rw [braidSign_rankHt]
    by_cases hz : braidSign (beadHt y) e = 0
    · -- within one bead of `y`: the coarse chamber restricts to the fine one
      rw [if_pos hz]
      have hbe : fineBead y e.1.1 = fineBead y e.1.2 := by
        by_contra hcon
        rw [hyface e hcon] at hz
        exact absurd hz (by decide)
      refine (braidSign_neg_of_lt _ e ?_).symm
      rw [Function.comp_apply, Function.comp_apply, rankHt_evPerm_inv, rankHt_evPerm_inv]
      have hlt : evIdx x (eventMap (concRefine f) ((evIdx y).symm e.1.1))
          < evIdx x (eventMap (concRefine f) ((evIdx y).symm e.1.2)) := by
        rw [evIdx_lt_iff]
        exact evKey_eventMap_lt f hbe (evKey_symm_lt y e.2)
      exact_mod_cast Fin.lt_def.mp hlt
    · -- across beads of `y`: `y`'s own face decides, the coarse order never enters
      rw [if_neg hz]
      have hbe : fineBead y e.1.1 ≠ fineBead y e.1.2 := by
        intro hcon
        exact hz (by rw [braidSign_zero_iff, beadHt, beadHt, hcon])
      rw [hyface e hbe]

/-! ## The braid functor -/

/-- **The braid functor of an arbitrary `K`** (`Ψ`): an execution goes to its bead partition inside
the identity chamber of its own `evKey` frame; a refinement goes to the permutation relating the two
frames.  **No side conditions**: `NonSelfLinked`, `AdmitsAltitude` and thinness are all unused. -/
noncomputable def braidPsi (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ BraidCat n where
  obj x := ⟨braidCell x⟩
  map f := ⟨evPerm f, evPerm_smul_le f⟩
  map_id x := Subtype.ext (evPerm_id x)
  map_comp f g := Subtype.ext (evPerm_comp f g)

/-- **The braid functor** `Φ : ConcGrpd K ⥤ BraidGrpd n` (on the `n`-event part), by the universal
property of the free groupoid — no presentation of `ConcGrpd K` is needed. -/
noncomputable def braidFunctor (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ BraidGrpd n :=
  FreeGroupoid.map (braidPsi K n)

/-! ## The event monodromy

Forgetting the Salvetti cell leaves the permutation: the composite of `Ψ` with the projection to
`Sₙ` is the **event monodromy** — the `evKey`-frame transition permutation of a refinement.  Its
image is contained in the pure braid group exactly when all these permutations are trivial, which is
`HasGlobalEventNaming` restricted to the `evKey` frames (not proved here).  Its sign is `orSign`
(`Schedule/Orientation.lean`) twisted by the per-object sign comparing `evKey`'s order with the lex
order `eventObjLinearOrder` — the two differ by a coboundary, not on the nose. -/

/-- The permutation part of a braid morphism. -/
def braidPermFunctor (n : ℕ) : BraidCat n ⥤ SingleObj (Equiv.Perm (Fin n)) where
  obj _ := SingleObj.star _
  map f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The **event monodromy** of `K`: the permutation of the `evKey` event frames along a
refinement. -/
noncomputable def eventMonodromy (K : BPSet) (n : ℕ) :
    ConcCatN K n ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  braidPsi K n ⋙ braidPermFunctor n

@[simp] theorem eventMonodromy_map {x y : ConcCatN K n} (f : x ⟶ y) :
    (eventMonodromy K n).map f = evPerm f := rfl

end CubeChains
