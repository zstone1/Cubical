import CubeChains.Concurrency.Executions.ExecData
import CubeChains.Concurrency.Salvetti.SalCompare

/-!
# Concurrency/Salvetti/SalExec — the executions of `□n` are the Salvetti poset of the braid
arrangement

`braidSalEquiv` is `salCompare` at `K = □n`, `L = braidCOM n`: the base comparison is
`chFaceCatEquiv` (chains are faces), the fibre comparison `linesTopeIso` (the runs refining a chain
are the topes above its face).  Naturality of the latter is the Salvetti wall crossing
`T' = X' ⊙ T` read as the arrow rule (`Concurrency/Executions/RunWord`): `X' ≠ 0` is
`runWord_group` (across beads the finer end runs in its own bead order), `X' = 0` is
`runWord_within` (inside a bead it inherits the coarser order).
-/

open CategoryTheory Opposite CubeChain BPSet SignType

namespace CubeChains

open ChStar SignVec

variable {n : ℕ}

/-! ## Topes are run words

A run word's chain is all edges, so its covector has no ties — a tope.  Conversely a tope's chain
has injective `beadOf`, hence one direction per bead, hence *is* a word chain. -/

/-- The topes (chambers) of the braid arrangement on `n` strands. -/
abbrev Tope (n : ℕ) : Type := {T : SignVec (BraidGround n) // (braidCOM n).IsTope T}

/-- The braid tope a run word names. -/
def wordTope (w : Equiv.Perm (Fin n)) : SignVec (BraidGround n) := (chFace (wordChain w)).1

theorem wordTope_apply (w : Equiv.Perm (Fin n)) (e : BraidGround n) :
    wordTope w e = sign (((w.symm e.1.1 : ℕ) : ℤ) - ((w.symm e.1.2 : ℕ) : ℤ)) := by
  change braidSign (fun q => ((beadOf (wordChain w) q : ℕ) : ℤ)) e = _
  simp only [braidSign_apply, beadOf_wordChain]

theorem wordTope_eq_braidSign (w : Equiv.Perm (Fin n)) :
    wordTope w = braidSign (fun q => ((w.symm q : ℕ) : ℤ)) := by
  funext e
  rw [wordTope_apply, braidSign_apply]

/-- **A run word's covector is a tope** — its height `w⁻¹` is injective. -/
theorem isTope_wordTope (w : Equiv.Perm (Fin n)) : (braidCOM n).IsTope (wordTope w) :=
  (braidCOM_isTope_iff_injective _).mpr
    ⟨fun q => ((w.symm q : ℕ) : ℤ),
      fun _ _ h => w.symm.injective (Fin.ext (Nat.cast_injective h)), wordTope_eq_braidSign w⟩

theorem wordTope_injective : Function.Injective (wordTope (n := n)) := fun w w' h => by
  have hc : wordChain w = wordChain w' := chFaceEquiv.injective (Subtype.ext h)
  have hs : w.symm = w'.symm :=
    Equiv.ext fun q => Fin.ext (by rw [← beadOf_wordChain, ← beadOf_wordChain, hc])
  simpa using congrArg Equiv.symm hs

/-- A face is the face of its own chain. -/
theorem chFace_symm_val (X : COM.Face (braidCOM n)) : (chFace (chFaceEquiv.symm X)).1 = X.1 :=
  congrArg Subtype.val (chFaceEquiv.apply_symm_apply X)

/-- **A tope's chain separates the directions** — a tope's covector has no ties. -/
theorem beadOf_injective_of_isTope {C : Ch (□n)} (hT : (braidCOM n).IsTope (chFace C).1) :
    Function.Injective (beadOf C) := by
  obtain ⟨σ, hσ, hs⟩ := (braidCOM_isTope_iff_injective _).mp hT
  have hsign : braidSign (fun q => ((beadOf C q : ℕ) : ℤ)) = braidSign σ := hs
  exact fun p q hpq =>
    hσ ((eq_iff_of_braidSign_eq hsign p q).mp (congrArg (fun i : Fin _ => ((i : ℕ) : ℤ)) hpq))

/-- **A tope's chain is all edges** — `beadOf` is a bijection, so the `n` directions fall into `n`
beads of total dimension `n`. -/
theorem isRun_of_isTope {C : Ch (□n)} (hT : (braidCOM n).IsTope (chFace C).1) :
    ∀ d ∈ C.dims, d = 1 :=
  ones_of_dimSum_eq_length <|
    (wedgeDimSum_eq C.map).trans <|
      (Fintype.card_fin n).symm.trans <|
        (Fintype.card_of_bijective
          ⟨beadOf_injective_of_isTope hT, beadOf_surjective C⟩).trans (Fintype.card_fin _)

/-- The run a tope names — its own chain, which is all edges. -/
def topeRun (T : Tope n) : Run (□n) :=
  ⟨chFaceEquiv.symm ⟨T.1, T.2.1⟩, isRun_of_isTope (by rw [chFace_symm_val]; exact T.2)⟩

/-- **The run word of a tope**: the order its chain performs the `n` directions. -/
def topeWord (T : Tope n) : Equiv.Perm (Fin n) := (localStep (topeRun T)).symm

theorem wordChain_topeWord (T : Tope n) : wordChain (topeWord T) = (topeRun T).chain :=
  congrArg Run.chain (runOfPerm_localStep (topeRun T))

/-- **Every tope is a run word** — a run of `□n` is its own step order (`runOfPerm_localStep`). -/
theorem wordTope_topeWord (T : Tope n) : wordTope (topeWord T) = T.1 :=
  (congrArg (fun C : Ch (□n) => (chFace C).1) (wordChain_topeWord T)).trans
    (chFace_symm_val ⟨T.1, T.2.1⟩)

theorem topeWord_wordTope (w : Equiv.Perm (Fin n)) :
    topeWord ⟨wordTope w, isTope_wordTope w⟩ = w :=
  congrArg Equiv.symm
    ((congrArg localStep (Run.ext (chFaceEquiv.symm_apply_eq.mpr (Subtype.ext rfl)))).trans
      (localStep_runOfPerm w.symm))

/-- **Topes are run words** — computable: a tope's chain is a run, and a run of `□n` *is* a
permutation of its axes. -/
def wordTopeEquiv : Equiv.Perm (Fin n) ≃ Tope n where
  toFun w := ⟨wordTope w, isTope_wordTope w⟩
  invFun := topeWord
  left_inv := topeWord_wordTope
  right_inv T := Subtype.ext (wordTope_topeWord T)

@[simp] theorem wordTopeEquiv_val (w : Equiv.Perm (Fin n)) :
    (wordTopeEquiv w).1 = wordTope w := rfl

@[simp] theorem wordTope_symm (T : Tope n) : wordTope (wordTopeEquiv.symm T) = T.1 :=
  congrArg Subtype.val (wordTopeEquiv.apply_symm_apply T)

/-! ### Cells of a face

`topeCell T` is the top-dimensional cell `(T, T)` — the all-edges execution of that word;
`faceCell X T₀` is the apex `(X, T₀)`. -/

/-- The maximal Salvetti cell of a tope, `(T, T)`. -/
def topeCell (T : Tope n) : Sal (braidCOM n) := ⟨(T.1, T.1), T.2.1, T.2, faceLE_refl _⟩

@[simp] theorem topeCell_face (T : Tope n) : (topeCell T).face = T.1 := rfl
@[simp] theorem topeCell_tope (T : Tope n) : (topeCell T).tope = T.1 := rfl

/-- The cell of a face together with a chosen tope above it. -/
def faceCell (X : COM.Face (braidCOM n)) (T₀ : Tope n) (h : X.1 ⊑ T₀.1) : Sal (braidCOM n) :=
  ⟨(X.1, T₀.1), X.2, T₀.2, h⟩

/-- **Every tope above `X` lies above the single cell `(X, T₀)`.**  The face clause is the
hypothesis `X ⊑ T`; the wall-crossing clause is *free*, because a tope absorbs
(`comp_eq_left_of_isTope`). -/
theorem faceCell_le_topeCell {X : COM.Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T : Tope n} (hT : X.1 ⊑ T.1) : faceCell X T₀ h ≤ topeCell T :=
  ⟨hT, (COM.comp_eq_left_of_isTope T.2 T₀.2.1).symm⟩

/-! ## The wall crossing

The Salvetti order's second clause `T' = X' ⊙ T` — "keep `X'`'s signs where it has them, `T`'s
elsewhere" — is the arrow rule, one clause per branch of `⊙`. -/

/-- **The arrow rule is the Salvetti wall crossing.**  Along `f : x ⟶ y` the finer end's tope is
`chFace y.chain ⊙` the coarser one's. -/
theorem wordTope_runWord {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    wordTope (runWord y) = (chFace y.chain).1 ⊙ wordTope (runWord x) := by
  funext e
  have hface : (chFace y.chain).1 e
      = sign (((beadOf y.chain e.1.1 : ℕ) : ℤ) - ((beadOf y.chain e.1.2 : ℕ) : ℤ)) := rfl
  rw [SignVec.comp_apply, wordTope_apply, wordTope_apply, hface]
  by_cases hz : sign (((beadOf y.chain e.1.1 : ℕ) : ℤ) - ((beadOf y.chain e.1.2 : ℕ) : ℤ)) = 0
  · -- inside a bead: `y` inherits `x`'s order
    have hb : beadOf y.chain e.1.1 = beadOf y.chain e.1.2 := by
      have hz0 := sign_eq_zero_iff.mp hz
      exact Fin.ext (by omega)
    rw [if_pos hz, sign_eq_sign_iff]
    refine ⟨?_, ?_⟩
    · rw [sub_neg, sub_neg, Nat.cast_lt, Nat.cast_lt]
      exact runWord_within f hb
    · rw [sub_pos, sub_pos, Nat.cast_lt, Nat.cast_lt]
      exact runWord_within f hb.symm
  · -- across beads: `y` runs in its own bead order, whatever `x` did
    have hb : beadOf y.chain e.1.1 ≠ beadOf y.chain e.1.2 := fun hc => hz (by rw [hc]; simp)
    rw [if_neg hz, sign_eq_sign_iff]
    refine ⟨?_, ?_⟩
    · rw [sub_neg, sub_neg, Nat.cast_lt, Nat.cast_lt]
      exact runWord_lt_iff_beadOf_lt y hb
    · rw [sub_pos, sub_pos, Nat.cast_lt, Nat.cast_lt]
      exact runWord_lt_iff_beadOf_lt y (Ne.symm hb)

/-! ## Objects: the runs over a chain are the topes above its face

`ExecData`'s side condition and the cell condition `X ⊑ T` are the same inequality, once
`wordTope` reads a run word as a tope. -/

namespace ChStar

/-- The run of `x`, read over a chain equal to `x`'s. -/
def lineAt {K : BPSet} {C : Ch K} (x : Ch⋆ K) (h : x.chain = C) : (Lines K).obj (op C) :=
  (Lines K).map (eqToHom (congrArg op h)) x.2

theorem mk_lineAt {K : BPSet} {C : Ch K} (x : Ch⋆ K) (h : x.chain = C) :
    (⟨op C, lineAt x h⟩ : Ch⋆ K) = x :=
  (Functor.Elements.ext x ⟨op C, lineAt x h⟩ (congrArg op h) rfl).symm

end ChStar

/-- The execution of `C` performing the word of a tope above it. -/
def topeExec (C : Ch (□n)) (T : Tope n) (h : (chFace C).1 ⊑ T.1) : Ch⋆ (□n) :=
  ofExecData ⟨(C, topeWord T), by
    change (chFace C).1 ⊑ wordTope (topeWord T)
    rw [wordTope_topeWord]
    exact h⟩

@[simp] theorem chain_topeExec (C : Ch (□n)) (T : Tope n) (h : (chFace C).1 ⊑ T.1) :
    (topeExec C T h).chain = C := chain_ofExecData _

@[simp] theorem runWord_topeExec (C : Ch (□n)) (T : Tope n) (h : (chFace C).1 ⊑ T.1) :
    runWord (topeExec C T h) = topeWord T := runWord_ofExecData _

/-- **The runs refining a chain are the topes above its face** — the fibres of the comparison. -/
def linesTopeEquiv (C : Ch (□n)) :
    (Lines (□n)).obj (op C) ≃ (COM.salFunctor (braidCOM n)).obj (chFace C) where
  toFun ρ := ⟨wordTope (runWord ⟨op C, ρ⟩), isTope_wordTope _, (execData ⟨op C, ρ⟩).2⟩
  invFun T := lineAt (topeExec C ⟨T.1, T.2.1⟩ T.2.2) (chain_topeExec _ _ _)
  left_inv ρ := sigma_mk_injective <| (mk_lineAt _ _).trans <|
    ext_runWord (chain_topeExec _ _ _) ((runWord_topeExec _ _ _).trans (topeWord_wordTope _))
  right_inv T := Subtype.ext <| by
    change wordTope (runWord (⟨op C, lineAt (topeExec C ⟨T.1, T.2.1⟩ T.2.2) _⟩ : Ch⋆ (□n))) = T.1
    rw [mk_lineAt, runWord_topeExec, wordTope_topeWord]

/-! ## The comparison

The base is `chFaceCatEquiv`, the fibres `linesTopeEquiv`; `salCompare` assembles them. -/

/-- **The runs of `□n` are the topes of `braidCOM n`, naturally** — the presheaf half of the
comparison, its naturality square the arrow rule `wordTope_runWord`. -/
def linesTopeIso : Lines (□n) ≅ chFaceCatEquiv.functor ⋙ COM.salFunctor (braidCOM n) :=
  NatIso.ofComponents (fun X => (linesTopeEquiv X.unop).toIso) (by
    intro X Y f
    ext ρ
    exact Subtype.ext
      (wordTope_runWord (x := ⟨X, ρ⟩) (y := ⟨Y, (Lines (□n)).map f ρ⟩) ⟨f, rfl⟩))

/-- **The executions of the cube are the Salvetti poset of the braid arrangement.** -/
def braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□n) :=
  (salCompare chFaceCatEquiv linesTopeIso).symm

@[simp] theorem face_braidSalEquiv_inverse (x : Ch⋆ (□n)) :
    (braidSalEquiv.inverse.obj x).face = (chFace x.chain).1 := rfl

@[simp] theorem tope_braidSalEquiv_inverse (x : Ch⋆ (□n)) :
    (braidSalEquiv.inverse.obj x).tope = wordTope (runWord x) := rfl

/-- The unit as an equality — `Sal` is a poset, so an iso of cells is an equality of cells. -/
theorem braidSalEquiv_inverse_functor (a : Sal (braidCOM n)) :
    braidSalEquiv.inverse.obj (braidSalEquiv.functor.obj a) = a :=
  le_antisymm (leOfHom (braidSalEquiv.unitIso.inv.app a))
    (leOfHom (braidSalEquiv.unitIso.hom.app a))

@[simp] theorem chFace_braidSalEquiv (a : Sal (braidCOM n)) :
    (chFace (braidSalEquiv.functor.obj a).chain).1 = a.face :=
  congrArg COM.SalCell.face (braidSalEquiv_inverse_functor a)

@[simp] theorem wordTope_braidSalEquiv (a : Sal (braidCOM n)) :
    wordTope (runWord (braidSalEquiv.functor.obj a)) = a.tope :=
  congrArg COM.SalCell.tope (braidSalEquiv_inverse_functor a)

end CubeChains
