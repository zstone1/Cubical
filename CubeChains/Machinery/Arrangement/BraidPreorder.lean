import CubeChains.Machinery.Arrangement.Braid

/-!
# Machinery/Arrangement/BraidPreorder — the Sal-side dictionary for the braid COM

Combinatorial characterisation of the covectors, topes, and face order of the braid arrangement
`braidCOM n` (`Machinery/Arrangement/Braid.lean`), phrased entirely in `Fin n` / `braidSign` terms:
a coordinate `braidSign w e = 0` is a **tie** `wᵢ = wⱼ`; `braidSign v ⊑ braidSign w` means `w`
preserves every strict comparison of `v`; and a **tope** is a covector with no tie, equivalently the
`braidSign` of an injective height.  These feed the comparison `Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)`.

-/

open SignType

namespace CubeChains

open SignVec

variable {n : ℕ}

/-- A braid covector coordinate is zero exactly at a tie: `braidSign w e = 0 ↔ wᵢ = wⱼ`. -/
theorem braidSign_zero_iff (w : Fin n → ℤ) (e : BraidGround n) :
    braidSign w e = 0 ↔ w e.1.1 = w e.1.2 := by
  rw [braidSign_apply, sign_eq_zero_iff, sub_eq_zero]

/-- A braid covector coordinate is nonzero exactly at a strict comparison. -/
theorem braidSign_ne_zero_iff (w : Fin n → ℤ) (e : BraidGround n) :
    braidSign w e ≠ 0 ↔ w e.1.1 ≠ w e.1.2 :=
  not_congr (braidSign_zero_iff w e)

/-- **Face order as order agreement**: `⊑` is "`w` refines `v`'s ties", read at every ordered pair.
The unordered pairs come from `faceLE_iff_signAt`. -/
theorem braidSign_faceLE_iff {v w : Fin n → ℤ} :
    braidSign v ⊑ braidSign w ↔ ∀ i j, v i ≠ v j → (v i < v j ↔ w i < w j) := by
  rw [faceLE_iff_signAt]
  simp only [signAt_braidSign, sign_eq_zero_iff, sub_eq_zero, sign_eq_sign_iff, sub_neg, sub_pos]
  refine ⟨fun h i j hne => ((h i j).resolve_left hne).1, fun h p q => ?_⟩
  by_cases hz : v p = v q
  · exact Or.inl hz
  · exact Or.inr ⟨h p q hz, h q p (Ne.symm hz)⟩

/-- **Tope characterisation.** A braid covector is a tope iff it is a covector with no tie.  A tie
is always breakable: doubling the height and bumping one of the tied coordinates refines the tie and
keeps every strict comparison (the bump is too small to reverse a gap of `2`). -/
theorem braidCOM_isTope_iff (T : SignVec (BraidGround n)) :
    (braidCOM n).IsTope T ↔ (T ∈ braidCovectors n ∧ ∀ e, T e ≠ 0) := by
  constructor
  · rintro ⟨⟨w, rfl⟩, hmax⟩
    refine ⟨⟨w, rfl⟩, fun e he0 => ?_⟩
    have htie : w e.1.1 = w e.1.2 := (braidSign_zero_iff w e).mp he0
    have hne21 : e.1.2 ≠ e.1.1 := e.2.ne'
    set w' : Fin n → ℤ := fun q => 2 * w q + (if q = e.1.1 then 1 else 0) with hw'
    have hface : braidSign w ⊑ braidSign w' :=
      braidSign_faceLE_iff.mpr fun p q hpq => by simp only [hw']; split_ifs <;> omega
    have hne : braidSign w' e ≠ 0 := by
      have h1 : w' e.1.1 = 2 * w e.1.1 + 1 := by simp [hw']
      have h2 : w' e.1.2 = 2 * w e.1.2 := by simp [hw', hne21]
      rw [braidSign_ne_zero_iff, h1, h2]
      omega
    exact hne ((hmax (braidSign w') ⟨w', rfl⟩ hface) ▸ he0)
  · rintro ⟨hTcov, hnz⟩
    exact ⟨hTcov, fun X _ hface => funext fun f => ((hface f).resolve_left (hnz f)).symm⟩

/-- **Tope ↔ injective height.** A braid covector is a tope iff it is realised by an injective
height function. -/
theorem braidCOM_isTope_iff_injective (T : SignVec (BraidGround n)) :
    (braidCOM n).IsTope T ↔ ∃ σ : Fin n → ℤ, Function.Injective σ ∧ T = braidSign σ := by
  rw [braidCOM_isTope_iff]
  constructor
  · rintro ⟨⟨w, rfl⟩, hnz⟩
    refine ⟨w, ?_, rfl⟩
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hnz ⟨(i, j), h⟩ ((braidSign_zero_iff w ⟨(i, j), h⟩).mpr hij)
    · exact hnz ⟨(j, i), h⟩ ((braidSign_zero_iff w ⟨(j, i), h⟩).mpr hij.symm)
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨⟨σ, rfl⟩, ?_⟩
    intro e hc
    exact e.2.ne (hσ ((braidSign_zero_iff σ e).mp hc))

end CubeChains
