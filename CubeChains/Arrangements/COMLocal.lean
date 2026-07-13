import CubeChains.Arrangements.Sal

/-!
# Arrangements/COMLocal — the local COM at a covector

For an arrangement, `X` is the covector of a point `p`; the covectors of the points near `p` are
exactly the `Y` with `X ⊑ Y` (walls through `p` may be crossed, walls missing `p` keep `X`'s sign),
and restricting those to the walls *through* `p` — the coordinates of `zeroSet X` — gives the local
structure at `p`.  That restricted covector set is `COM.localAt`, and it is always an oriented
matroid: the restriction of `X` itself is the zero covector.

-/

namespace CubeChains

namespace SignVec
variable {E : Type*}

/-- In `SignType` only `0` is its own negative — this is what forbids a separator coordinate
where two covectors both agree with a nonzero sign of `X`. -/
theorem eq_zero_of_eq_neg {s : SignType} (h : s = -s) : s = 0 := by
  revert h; cases s <;> decide

/-- Restriction of `Y` to the walls through `X` (the coordinates where `X` vanishes). -/
def restrictZero (X Y : SignVec E) : SignVec {e : E // X e = 0} := fun e => Y e.1

variable (X Y Y' : SignVec E)

@[simp] theorem restrictZero_comp :
    restrictZero X (Y ⊙ Y') = restrictZero X Y ⊙ restrictZero X Y' := rfl

@[simp] theorem restrictZero_neg : restrictZero X (-Y) = -(restrictZero X Y) := rfl

/-- A covector restricts to `0` on its own walls — the point sits *on* every wall through it. -/
@[simp] theorem restrictZero_self : restrictZero X X = 0 := funext fun e => e.2

theorem mem_sep_restrictZero {e : {e : E // X e = 0}} :
    e ∈ sep (restrictZero X Y) (restrictZero X Y') ↔ e.1 ∈ sep Y Y' := Iff.rfl

/-- No wall passes through a generic point: a zero-free covector has empty local ground set. -/
theorem isEmpty_zeroSubtype {X : SignVec E} (h : ∀ e, X e ≠ 0) : IsEmpty {e : E // X e = 0} :=
  ⟨fun e => h e.1 e.2⟩

end SignVec

open SignVec

namespace COM
variable {E : Type*} (L : COM E) {X : SignVec E}

/-- **The local COM at a covector `X`:** the covectors `Y ⊒ X` of `L`, restricted to the walls
through `X`.  Nonemptiness (and `IsOM`) come from `Y = X`, whose restriction is `0`. -/
def localAt (hX : X ∈ L.covectors) : COM {e : E // X e = 0} where
  covectors := {Z | ∃ Y ∈ L.covectors, X ⊑ Y ∧ Z = restrictZero X Y}
  carrier_nonempty := ⟨0, X, hX, faceLE_refl X, (restrictZero_self X).symm⟩
  faceSymm := by
    rintro _ ⟨Y, hY, hXY, rfl⟩ _ ⟨Y', hY', hXY', rfl⟩
    refine ⟨Y ⊙ (-Y'), L.faceSymm _ hY _ hY', fun e => ?_, rfl⟩
    by_cases he : X e = 0
    · exact Or.inl he
    · have hYe : Y e = X e := ((hXY e).resolve_left he).symm
      exact Or.inr (by simp [comp, hYe, he])
  strongElim := by
    rintro _ ⟨Y, hY, hXY, rfl⟩ _ ⟨Y', hY', hXY', rfl⟩ e he
    obtain ⟨Z, hZ, hZe, hZf⟩ := L.strongElim Y hY Y' hY' e.1 he
    -- Off `zeroSet X` the two covectors agree with `X`, so no separator coordinate lies there;
    -- hence `Z` agrees with `Y ⊙ Y' = X` there, giving `X ⊑ Z`.
    have hsep : ∀ f, X f ≠ 0 → f ∉ sep Y Y' := by
      intro f hf hmem
      have hYf : Y f = X f := ((hXY f).resolve_left hf).symm
      have hY'f : Y' f = X f := ((hXY' f).resolve_left hf).symm
      have hneg : X f = -X f := by have := hmem.1; rwa [hYf, hY'f] at this
      exact hf (eq_zero_of_eq_neg hneg)
    refine ⟨restrictZero X Z, ⟨Z, hZ, fun f => ?_, rfl⟩, hZe, fun f hf => hZf f.1 hf⟩
    by_cases hfX : X f = 0
    · exact Or.inl hfX
    · have hYf : Y f = X f := ((hXY f).resolve_left hfX).symm
      exact Or.inr (by rw [hZf f (hsep f hfX)]; simp [comp, hYf, hfX])

@[simp] theorem mem_localAt_covectors (hX : X ∈ L.covectors) {Z : SignVec {e : E // X e = 0}} :
    Z ∈ (L.localAt hX).covectors ↔ ∃ Y ∈ L.covectors, X ⊑ Y ∧ Z = restrictZero X Y := Iff.rfl

/-- The local COM is an oriented matroid: `X` itself restricts to the zero covector. -/
theorem localAt_isOM (hX : X ∈ L.covectors) : (L.localAt hX).IsOM :=
  ⟨X, hX, faceLE_refl X, (restrictZero_self X).symm⟩

/-- The local COM at a zero-free covector is the (unique) COM on the empty ground set
(`SignVec.isEmpty_zeroSubtype`). -/
theorem localAt_covectors_of_forall_ne_zero (hX : X ∈ L.covectors) (h : ∀ e, X e ≠ 0) :
    (L.localAt hX).covectors = {0} :=
  Set.eq_singleton_iff_unique_mem.mpr
    ⟨L.localAt_isOM hX, fun _ _ => funext fun e => absurd e.2 (h e.1)⟩

end COM

end CubeChains
