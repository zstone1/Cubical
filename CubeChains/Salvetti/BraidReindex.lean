import CubeChains.Arrangements.BraidSymmetry
import CubeChains.Salvetti.BraidIso
import CubeChains.Salvetti.ConcGroupoid

/-!
# Salvetti/BraidReindex — the `Sₙ` action on the Salvetti category, transported to concurrency

`reorient σ` (`Arrangements/BraidSymmetry`) is a monotone self-bijection of `Sal (braidCOM n)`,
hence a functor `salReindex σ`; the family is a left `Equiv.Perm (Fin n)`-action (`MulAction`).
Conjugating by `braidSalEquiv n` carries it to the concurrency category `ConcCat (□n)`
(`concReindex`) and, via `freeGroupoidCongr`, to the groupoid `ConcGrpd (□n)` (`concGrpdReindex`).

Cubes are rigid (`Aut (□n) = 1`), so this symmetry cannot act on `□n` directly; it rides in from the
braid arrangement.
-/

open CategoryTheory

namespace CubeChains

open SignVec COM

variable {n : ℕ}

/-! ### `reorient` distributes over composition `⊙` -/

/-- `signAt` of a composite is the branchwise composite of `signAt`s (indices unordered). -/
theorem signAt_comp (X Y : SignVec (BraidGround n)) (p q : Fin n) :
    signAt (X ⊙ Y) p q = if signAt X p q = 0 then signAt Y p q else signAt X p q := by
  rcases lt_trichotomy p q with h | h | h
  · rw [signAt_lt (X ⊙ Y) h, signAt_lt X h, signAt_lt Y h]; rfl
  · subst h; simp only [signAt_self, ite_self]
  · rw [signAt_gt (X ⊙ Y) h, signAt_gt X h, signAt_gt Y h]
    simp only [comp]
    by_cases h0 : X ⟨(q, p), h⟩ = 0
    · rw [if_pos h0, if_pos (SignType.neg_eq_zero_iff.mpr h0)]
    · rw [if_neg h0, if_neg (fun hc => h0 (SignType.neg_eq_zero_iff.mp hc))]

/-- Reorientation distributes over composition `⊙`. -/
theorem reorient_comp (σ : Equiv.Perm (Fin n)) (X Y : SignVec (BraidGround n)) :
    reorient σ (X ⊙ Y) = reorient σ X ⊙ reorient σ Y := by
  funext e
  rw [reorient_apply, signAt_comp]
  simp only [comp, reorient_apply]

/-! ### The `Sₙ`-action on Salvetti cells -/

/-- Object map of `salReindex σ`: reorient both the face and the tope of a cell. -/
def salReindexObj (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) : Sal (braidCOM n) :=
  ⟨(reorient σ a.1.1, reorient σ a.1.2),
    reorient_mem_covectors σ a.2.1, reorient_isTope σ a.2.2.1, reorient_faceLE σ a.2.2.2⟩

theorem salReindexObj_one (a : Sal (braidCOM n)) : salReindexObj 1 a = a := by
  apply Subtype.ext
  change (reorient 1 a.1.1, reorient 1 a.1.2) = a.1
  rw [reorient_one, reorient_one]

theorem salReindexObj_mul (σ τ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    salReindexObj (σ * τ) a = salReindexObj σ (salReindexObj τ a) := by
  apply Subtype.ext
  change (reorient (σ * τ) a.1.1, reorient (σ * τ) a.1.2)
      = (reorient σ (reorient τ a.1.1), reorient σ (reorient τ a.1.2))
  rw [reorient_mul, reorient_mul]

/-- The left `Sₙ`-action on Salvetti cells by reorientation. -/
instance : MulAction (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  smul := salReindexObj
  one_smul := salReindexObj_one
  mul_smul := salReindexObj_mul

theorem salReindexObj_inv_left (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    salReindexObj σ⁻¹ (salReindexObj σ a) = a := by
  rw [← salReindexObj_mul, inv_mul_cancel, salReindexObj_one]

theorem salReindexObj_inv_right (σ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    salReindexObj σ (salReindexObj σ⁻¹ a) = a := by
  rw [← salReindexObj_mul, mul_inv_cancel, salReindexObj_one]

/-- Reorientation is monotone for the Salvetti order (`reorient_faceLE` on faces, `reorient_comp` on
the wall-crossing projection of the tope). -/
theorem salReindexObj_monotone (σ : Equiv.Perm (Fin n)) : Monotone (salReindexObj σ) := by
  intro a b hab
  rw [SalCell.le_iff] at hab ⊢
  refine ⟨reorient_faceLE σ hab.1, ?_⟩
  change reorient σ b.tope = reorient σ b.face ⊙ reorient σ a.tope
  rw [hab.2, reorient_comp]

/-! ### `salReindex σ` as a functor / equivalence -/

/-- `reorient σ` as an order isomorphism of the Salvetti poset. -/
def salReindexOrderIso (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) ≃o Sal (braidCOM n) where
  toFun := salReindexObj σ
  invFun := salReindexObj σ⁻¹
  left_inv := salReindexObj_inv_left σ
  right_inv := salReindexObj_inv_right σ
  map_rel_iff' := by
    intro a b
    change salReindexObj σ a ≤ salReindexObj σ b ↔ a ≤ b
    refine ⟨fun h => ?_, fun h => salReindexObj_monotone σ h⟩
    have := salReindexObj_monotone σ⁻¹ h
    rwa [salReindexObj_inv_left, salReindexObj_inv_left] at this

/-- The reindexing functor `salReindex σ : Sal (braidCOM n) ⥤ Sal (braidCOM n)`. -/
def salReindex (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) ⥤ Sal (braidCOM n) :=
  (salReindexObj_monotone σ).functor

/-- `salReindex σ` as an equivalence (a poset auto-iso). -/
def salReindexEquiv (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) ≌ Sal (braidCOM n) :=
  (salReindexOrderIso σ).equivalence

/-- Action law: `salReindex 1 ≅ 𝟭`. -/
def salReindexOneIso : salReindex (1 : Equiv.Perm (Fin n)) ≅ 𝟭 (Sal (braidCOM n)) :=
  NatIso.ofComponents (fun a => eqToIso (salReindexObj_one a))
    (fun {_ _} _ => Subsingleton.elim _ _)

/-- Action law: `salReindex (σ * τ) ≅ salReindex τ ⋙ salReindex σ` (left action). -/
def salReindexMulIso (σ τ : Equiv.Perm (Fin n)) :
    salReindex (σ * τ) ≅ salReindex τ ⋙ salReindex σ :=
  NatIso.ofComponents (fun a => eqToIso (salReindexObj_mul σ τ a))
    (fun {_ _} _ => Subsingleton.elim _ _)

/-! ### Transport to the concurrency category and groupoid -/

/-- The `Sₙ`-action on `ConcCat (□n)`, conjugating `salReindexEquiv` through `braidSalEquiv`. -/
noncomputable def concReindex (σ : Equiv.Perm (Fin n)) : ConcCat (□n) ≌ ConcCat (□n) :=
  (braidSalEquiv n).symm.trans ((salReindexEquiv σ).trans (braidSalEquiv n))

/-- The `Sₙ`-action on the concurrency groupoid `ConcGrpd (□n)`. -/
noncomputable def concGrpdReindex (σ : Equiv.Perm (Fin n)) : ConcGrpd (□n) ≌ ConcGrpd (□n) :=
  freeGroupoidCongr (concReindex σ)

/-- Transported unit law: `concReindex 1 ≅ 𝟭` (the conjugated `salReindexOneIso`). -/
noncomputable def concReindexOneIso :
    (concReindex (1 : Equiv.Perm (Fin n))).functor ≅ 𝟭 (ConcCat (□n)) :=
  Functor.isoWhiskerLeft (braidSalEquiv n).inverse
      (Functor.isoWhiskerRight salReindexOneIso (braidSalEquiv n).functor
        ≪≫ (braidSalEquiv n).functor.leftUnitor)
    ≪≫ (braidSalEquiv n).counitIso

end CubeChains
