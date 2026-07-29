import CubeChains.Salvetti.ExecData
import CubeChains.Salvetti.Elements

/-!
# Salvetti/SalExec — the executions of `□n` are the Salvetti poset of the braid arrangement

`salChStarEquiv : Sal (braidCOM n) ≃ Ch⋆ (□n)` and its categorical form `braidSalEquiv`.

A Salvetti cell is a face below a tope; `chFaceEquiv` reads faces as chains and `wordTope` reads
topes as run words, so the cell condition `X ⊑ T` *is* `ExecData`'s.  On morphisms the Salvetti
order's wall crossing `T' = X' ⊙ T` is the arrow rule (`Salvetti/RunWord`): `X' ≠ 0` is
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

/-- **Every tope is a run word.**  Its chain's `beadOf` is injective (no ties) and surjective
(beads are nonempty), so the chain has one direction per bead and `beadOf` transposes to `w⁻¹`. -/
theorem exists_wordTope {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T) :
    ∃ w : Equiv.Perm (Fin n), wordTope w = T := by
  obtain ⟨σ, hσ, rfl⟩ := (braidCOM_isTope_iff_injective T).mp hT
  set C : Ch (□n) := chFaceEquiv.symm ⟨braidSign σ, ⟨σ, rfl⟩⟩ with hC
  have hface : (chFace C).1 = braidSign σ :=
    congrArg Subtype.val (chFaceEquiv.apply_symm_apply _)
  have hfaceS : braidSign (fun q => ((beadOf C q : ℕ) : ℤ)) = braidSign σ := hface
  have hinj : Function.Injective (beadOf C) := fun p q hpq =>
    hσ ((eq_iff_of_braidSign_eq hfaceS p q).mp (congrArg (fun i : Fin _ => ((i : ℕ) : ℤ)) hpq))
  have hbij : Function.Bijective (beadOf C) := ⟨hinj, beadOf_surjective C⟩
  have hlen : C.dims.length = n :=
    (Fintype.card_fin C.dims.length).symm.trans
      ((Fintype.card_of_bijective hbij).symm.trans (Fintype.card_fin n))
  refine ⟨((Equiv.ofBijective _ hbij).trans (finCongr hlen)).symm, ?_⟩
  have hwc : wordChain ((Equiv.ofBijective _ hbij).trans (finCongr hlen)).symm = C :=
    eq_of_beadOf fun q => by rw [beadOf_wordChain]; rfl
  rw [wordTope, hwc]
  exact hface

/-- **Topes are run words.** -/
noncomputable def wordTopeEquiv : Equiv.Perm (Fin n) ≃ Tope n :=
  Equiv.ofBijective (fun w => ⟨wordTope w, isTope_wordTope w⟩)
    ⟨fun _ _ h => wordTope_injective (by simpa using h),
      fun T => (exists_wordTope T.2).imp fun _ hw => Subtype.ext hw⟩

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

/-! ## Objects: a Salvetti cell is an execution

`ExecData`'s side condition and the cell condition `X ⊑ T` are the same inequality, read through
`chFaceEquiv` on the left and `wordTopeEquiv` on the right. -/

/-- A Salvetti cell as chain-plus-word. -/
noncomputable def salExecData (a : Sal (braidCOM n)) : ExecData n :=
  ⟨(chFaceEquiv.symm ⟨a.face, a.2.1⟩, wordTopeEquiv.symm ⟨a.tope, a.2.2.1⟩), by
    have h1 : (chFace (chFaceEquiv.symm ⟨a.face, a.2.1⟩)).1 = a.face :=
      congrArg Subtype.val (chFaceEquiv.apply_symm_apply _)
    change (chFace (chFaceEquiv.symm ⟨a.face, a.2.1⟩)).1 ⊑ wordTope (wordTopeEquiv.symm _)
    rw [wordTope_symm, h1]
    exact a.2.2.2⟩

/-- …and back: a chain-plus-word is the cell of its face and its word's tope. -/
def execSal (p : ExecData n) : Sal (braidCOM n) :=
  ⟨((chFace p.1.1).1, wordTope p.1.2), (chFace p.1.1).2, isTope_wordTope p.1.2, p.2⟩

/-- **A Salvetti cell of `braidCOM n` is an execution of `□n`** (objects). -/
noncomputable def salChStarEquiv : Sal (braidCOM n) ≃ Ch⋆ (□n) :=
  (Equiv.mk salExecData execSal
    (fun a => Subtype.ext (Prod.ext
      (congrArg Subtype.val (chFaceEquiv.apply_symm_apply ⟨a.face, a.2.1⟩))
      (wordTope_symm ⟨a.tope, a.2.2.1⟩)))
    (fun p => Subtype.ext (Prod.ext
      (chFaceEquiv.symm_apply_apply p.1.1)
      (wordTopeEquiv.symm_apply_apply p.1.2)))).trans execEquiv.symm

@[simp] theorem chFace_salChStarEquiv (a : Sal (braidCOM n)) :
    (chFace (salChStarEquiv a).chain).1 = a.face := by
  change (chFace (ofExecData (salExecData a)).chain).1 = a.face
  rw [chain_ofExecData]
  exact congrArg Subtype.val (chFaceEquiv.apply_symm_apply _)

@[simp] theorem wordTope_salChStarEquiv (a : Sal (braidCOM n)) :
    wordTope (runWord (salChStarEquiv a)) = a.tope := by
  change wordTope (runWord (ofExecData (salExecData a))) = a.tope
  rw [runWord_ofExecData]
  exact wordTope_symm _

@[simp] theorem face_salChStarEquiv_symm (x : Ch⋆ (□n)) :
    (salChStarEquiv.symm x).face = (chFace x.chain).1 := rfl

@[simp] theorem tope_salChStarEquiv_symm (x : Ch⋆ (□n)) :
    (salChStarEquiv.symm x).tope = wordTope (runWord x) := rfl

/-! ## Morphisms: the Salvetti order is the refinement order

`Ch⋆`'s arrows are already known to satisfy the two Salvetti clauses (`chFace_faceLE` and
`wordTope_runWord`); the converse builds the base arrow with `reflectHom` and lets the discrete
opfibration `π` force the run. -/

/-- **The Salvetti order gives an arrow.**  `reflectHom` supplies the base refinement, `π` forces
its target, and `wordTope_injective` identifies that target with `y`. -/
theorem exists_hom {x y : Ch⋆ (□n)}
    (hface : (chFace x.chain).1 ⊑ (chFace y.chain).1)
    (htope : wordTope (runWord y) = (chFace y.chain).1 ⊙ wordTope (runWord x)) :
    Nonempty (x ⟶ y) := by
  let g : y.chain ⟶ x.chain := reflectHom hface
  let y₀ : Ch⋆ (□n) := ⟨op y.chain, (Lines (□n)).map g.op x.2⟩
  let f₀ : x ⟶ y₀ := ⟨g.op, rfl⟩
  have hchain : y₀.chain = y.chain := rfl
  have hw : runWord y₀ = runWord y :=
    wordTope_injective ((wordTope_runWord f₀).trans (by rw [hchain, ← htope]))
  exact ⟨f₀ ≫ eqToHom (ext_runWord hchain hw)⟩

instance : Quiver.IsThin (Sal (braidCOM n)) := fun _ _ => inferInstance

/-- The forward functor: a cell to its execution, an order relation to the forced refinement. -/
noncomputable def salChStarFunctor : Sal (braidCOM n) ⥤ Ch⋆ (□n) where
  obj := salChStarEquiv
  map {a b} h :=
    (exists_hom (x := salChStarEquiv a) (y := salChStarEquiv b)
      (by rw [chFace_salChStarEquiv, chFace_salChStarEquiv]; exact (leOfHom h).1)
      (by rw [wordTope_salChStarEquiv, wordTope_salChStarEquiv, chFace_salChStarEquiv]
          exact (leOfHom h).2)).some
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse functor: an execution to its cell, a refinement to the two Salvetti clauses. -/
noncomputable def chStarSalFunctor : Ch⋆ (□n) ⥤ Sal (braidCOM n) where
  obj := salChStarEquiv.symm
  map {_ _} f := homOfLE ⟨chFace_faceLE f.1.unop, wordTope_runWord f⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The executions of the cube are the Salvetti poset of the braid arrangement.**  Both sides are
thin, so unit, counit and every coherence are `Subsingleton.elim`. -/
noncomputable def braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□n) where
  functor := salChStarFunctor
  inverse := chStarSalFunctor
  unitIso := NatIso.ofComponents
    (fun a => eqToIso (salChStarEquiv.symm_apply_apply a).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun x => eqToIso (salChStarEquiv.apply_symm_apply x))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp] theorem braidSalEquiv_functor_obj (a : Sal (braidCOM n)) :
    braidSalEquiv.functor.obj a = salChStarEquiv a := rfl

end CubeChains
