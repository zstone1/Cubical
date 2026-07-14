import CubeChains.Arrangements.Braid

/-!
# Arrangements/BraidPreorder — the Sal-side dictionary for the braid COM

Combinatorial characterisation of the covectors, topes, and face order of the braid arrangement
`braidCOM n` (`Arrangements/Braid.lean`), phrased entirely in `Fin n` / `braidSign` terms: a
coordinate `braidSign w e = 0` is a **tie** `wᵢ = wⱼ`; a **tope** is a covector with no tie,
equivalently the `braidSign` of an injective height; and `braidSign v ⊑ braidSign w`
means `w` preserves every strict comparison of `v`.  These feed the comparison
`Sal (braidCOM n) ≃o Int(Lines(□ⁿ))`.

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

/-- Doubling and adding a `{0,1}`-bump preserves every strict sign: if `braidSign w e ≠ 0` then
`braidSign (2·w + b) e = braidSign w e`. -/
theorem braidSign_double_add_bump (w b : Fin n → ℤ) (hb : ∀ i, b i = 0 ∨ b i = 1)
    (e : BraidGround n) (he : braidSign w e ≠ 0) :
    braidSign (fun i => 2 * w i + b i) e = braidSign w e := by
  simp only [braidSign_apply] at he ⊢
  have hune : w e.1.1 - w e.1.2 ≠ 0 := fun h => he (by rw [h, sign_zero])
  have hb1 := hb e.1.1
  have hb2 := hb e.1.2
  have harg : 2 * w e.1.1 + b e.1.1 - (2 * w e.1.2 + b e.1.2)
      = 2 * (w e.1.1 - w e.1.2) - (-(b e.1.1 - b e.1.2)) := by ring
  rw [harg]
  refine SignInt.sign_dom_sub ?_ ?_ ?_ hune <;> omega

/-- **Tope characterisation.** A braid covector is a tope iff it is a covector with no tie. -/
theorem braidCOM_isTope_iff (T : SignVec (BraidGround n)) :
    (braidCOM n).IsTope T ↔ (T ∈ braidCovectors n ∧ ∀ e, T e ≠ 0) := by
  constructor
  · rintro ⟨hTcov, hmax⟩
    obtain ⟨w, rfl⟩ := hTcov
    refine ⟨⟨w, rfl⟩, ?_⟩
    intro e he0
    have he_lt : e.1.1 < e.1.2 := e.2
    have htie : w e.1.1 = w e.1.2 := (braidSign_zero_iff w e).mp he0
    set b : Fin n → ℤ := fun i => if i = e.1.1 then 1 else 0 with hbdef
    set w' : Fin n → ℤ := fun i => 2 * w i + b i with hw'def
    have hbval : ∀ i, b i = 0 ∨ b i = 1 := by
      intro i
      rcases eq_or_ne i e.1.1 with h | h
      · exact Or.inr (by simp [hbdef, h])
      · exact Or.inl (by simp [hbdef, h])
    have hface : braidSign w ⊑ braidSign w' := by
      intro f
      by_cases hf : braidSign w f = 0
      · exact Or.inl hf
      · refine Or.inr ?_
        rw [hw'def]
        exact (braidSign_double_add_bump w b hbval f hf).symm
    have hcov : braidSign w' ∈ (braidCOM n).covectors := ⟨w', rfl⟩
    have hEq := hmax (braidSign w') hcov hface
    have hb1 : b e.1.1 = 1 := by simp [hbdef]
    have hb2 : b e.1.2 = 0 := by simp [hbdef, he_lt.ne']
    have hne : braidSign w' e ≠ 0 := by
      rw [braidSign_ne_zero_iff]
      intro hcon
      simp only [hw'def] at hcon
      rw [hb1, hb2, htie] at hcon
      omega
    rw [hEq] at hne
    exact hne he0
  · rintro ⟨hTcov, hnz⟩
    refine ⟨hTcov, ?_⟩
    intro X hX hface
    funext f
    rcases hface f with h | h
    · exact absurd h (hnz f)
    · exact h.symm

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

/-- **Face order in braid terms.** `braidSign v ⊑ braidSign w` iff `braidSign v` agrees
with `braidSign w` on every strict comparison of `v`. -/
theorem faceLE_braidSign_iff (v w : Fin n → ℤ) :
    braidSign v ⊑ braidSign w ↔
      ∀ e, braidSign v e ≠ 0 → braidSign v e = braidSign w e := by
  constructor
  · intro h e hne
    exact (h e).resolve_left hne
  · intro h e
    by_cases hz : braidSign v e = 0
    · exact Or.inl hz
    · exact Or.inr (h e hz)

/-- **Face order as tie-refinement.** `braidSign v ⊑ braidSign w` iff `w` preserves the sign of
every strict comparison `vᵢ ≠ vⱼ` of `v`. -/
theorem faceLE_braidSign_iff_refinesTies (v w : Fin n → ℤ) :
    braidSign v ⊑ braidSign w ↔
      ∀ e, v e.1.1 ≠ v e.1.2 → braidSign w e = braidSign v e := by
  rw [faceLE_braidSign_iff]
  constructor
  · intro h e hne
    exact (h e ((braidSign_ne_zero_iff v e).mpr hne)).symm
  · intro h e hne
    exact (h e ((braidSign_ne_zero_iff v e).mp hne)).symm

end CubeChains
