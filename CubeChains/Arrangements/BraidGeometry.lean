import CubeChains.Arrangements.Braid
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.OrderClosed

/-!
# Arrangements/BraidGeometry — the braid arrangement as open convex cones in `ℝⁿ`

Phase 1 of the *timing geometry* program.  The schedule space of `n` concurrent events is
`ℝⁿ = Fin n → ℝ` (a real time per event); the walls of the braid arrangement `A_{n-1}` are the
diagonals `tᵢ = tⱼ`, and this file realises every face/covector of the braid oriented matroid
(`Arrangements/Braid.lean`) as an **open convex cone** — the *open star* of the covector.

For a timing `t : Fin n → ℝ` its real covector is `braidCovectorR t {i,j} = sign (tᵢ − tⱼ)`
(the mirror over `ℝ` of `braidSign` over `ℤ`).  For a covector `X` the **open star cone**
`starCone X` constrains only the *support* of `X`:

> `starCone X = {t | ∀ e, X e ≠ 0 → braidCovectorR t e = X e}`.

Constraining the support alone (not forcing `tᵢ = tⱼ` on the zero set) is exactly what makes it
an open, full-dimensional cone rather than a lower-dimensional cell.  We prove it open and convex
(a finite intersection of open half-spaces `tᵢ < tⱼ` / `tᵢ > tⱼ`), establish the order/lattice
substrate (`starCone_antitone`, `starCone_inter_subset`, `starCone_zero`), and its realizability
(every covector of `braidCOM n` has a nonempty star cone).

Everything here is **assumption-free** beyond `n : ℕ`: no precubical/chain/NSL/altitude
machinery, just `braidCOM` and mathlib convexity.

-/

open SignType Set

namespace CubeChains

variable {n : ℕ}

/-! ### Finiteness of the ground set -/

/-- The braid ground set is finite (a subtype of the finite `Fin n × Fin n`). -/
instance instFiniteBraidGround (n : ℕ) : Finite (BraidGround n) := Subtype.finite

/-! ### The real covector of a timing -/

/-- The **real covector** of a timing `t : Fin n → ℝ`: `braidCovectorR t {i,j} = sign (tᵢ − tⱼ)`.
Mirrors `braidSign` over `ℝ` instead of `ℤ`.  (Noncomputable: `sign` on `ℝ` uses the classical
`Real.decidableLT`.) -/
noncomputable def braidCovectorR (t : Fin n → ℝ) : SignVec (BraidGround n) :=
  fun e => sign (t e.1.1 - t e.1.2)

@[simp] theorem braidCovectorR_apply (t : Fin n → ℝ) (e : BraidGround n) :
    braidCovectorR t e = sign (t e.1.1 - t e.1.2) := rfl

/-- The real covector agrees with `braidSign` on any integer height function cast into `ℝ`. -/
theorem braidCovectorR_intCast (x : Fin n → ℤ) :
    braidCovectorR (fun i => (x i : ℝ)) = braidSign x := by
  funext e
  simp only [braidCovectorR_apply, braidSign_apply, ← Int.cast_sub, sign_intCast]

/-! ### The functional `t ↦ tᵢ − tⱼ` -/

/-- The coordinate-difference functional `t ↦ tᵢ − tⱼ` on `ℝⁿ` is `ℝ`-linear. -/
theorem isLinear_diff {ι : Type*} (i j : ι) : IsLinearMap ℝ (fun t : ι → ℝ => t i - t j) where
  map_add x y := by simp only [Pi.add_apply]; ring
  map_smul c x := by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-! ### The open star cone -/

/-- The **open star cone** of a covector `X`: the timings whose real covector matches `X` on the
*support* of `X` (nothing is required on `X`'s zero set).  This open, full-dimensional cone is
the open star of the cell `X` in the braid arrangement. -/
def starCone (X : SignVec (BraidGround n)) : Set (Fin n → ℝ) :=
  {t | ∀ e, X e ≠ 0 → braidCovectorR t e = X e}

/-- Membership in the star cone. -/
theorem mem_starCone_iff (X : SignVec (BraidGround n)) (t : Fin n → ℝ) :
    t ∈ starCone X ↔ ∀ e, X e ≠ 0 → braidCovectorR t e = X e := Iff.rfl

/-- The star cone as the (finite) intersection of the per-coordinate constraint sets. -/
theorem starCone_eq_iInter (X : SignVec (BraidGround n)) :
    starCone X = ⋂ e, {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e} := by
  ext t
  simp only [starCone, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h e
    rcases eq_or_ne (X e) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (h e h0)
  · intro h e he
    exact (h e).resolve_left he

/-- Each per-coordinate constraint set is both open and convex: for `X e = ±` it is the open
half-space `tᵢ < tⱼ` / `tᵢ > tⱼ`, and for `X e = 0` it is the whole space. -/
theorem isOpen_convex_coord (X : SignVec (BraidGround n)) (e : BraidGround n) :
    IsOpen {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e}
      ∧ Convex ℝ {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e} := by
  rcases SignType.trichotomy (X e) with hn | hz | hp
  · -- `X e = −1`: the open half-space `{t | tᵢ − tⱼ < 0}`.
    have hset : {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e}
        = {t | t e.1.1 - t e.1.2 < 0} := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hn, braidCovectorR_apply, sign_eq_neg_one_iff]
      constructor
      · rintro (h | h)
        · exact absurd h (by decide)
        · exact h
      · exact fun h => Or.inr h
    rw [hset]
    exact ⟨isOpen_lt ((continuous_apply e.1.1).sub (continuous_apply e.1.2)) continuous_const,
      convex_halfSpace_lt (isLinear_diff e.1.1 e.1.2) 0⟩
  · -- `X e = 0`: the whole space.
    have hset : {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e} = Set.univ := by
      ext t
      constructor
      · intro _; trivial
      · intro _; exact Or.inl hz
    rw [hset]
    exact ⟨isOpen_univ, convex_univ⟩
  · -- `X e = 1`: the open half-space `{t | 0 < tᵢ − tⱼ}`.
    have hset : {t : Fin n → ℝ | X e = 0 ∨ braidCovectorR t e = X e}
        = {t | (0 : ℝ) < t e.1.1 - t e.1.2} := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hp, braidCovectorR_apply, sign_eq_one_iff]
      constructor
      · rintro (h | h)
        · exact absurd h (by decide)
        · exact h
      · exact fun h => Or.inr h
    rw [hset]
    exact ⟨isOpen_lt continuous_const ((continuous_apply e.1.1).sub (continuous_apply e.1.2)),
      convex_halfSpace_gt (isLinear_diff e.1.1 e.1.2) 0⟩

/-- **The star cone is open.**  A finite intersection of open half-spaces `tᵢ < tⱼ` / `tᵢ > tⱼ`. -/
theorem isOpen_starCone (X : SignVec (BraidGround n)) : IsOpen (starCone X) := by
  rw [starCone_eq_iInter]
  exact isOpen_iInter_of_finite fun e => (isOpen_convex_coord X e).1

/-- **The star cone is convex.**  A finite intersection of convex half-spaces. -/
theorem convex_starCone (X : SignVec (BraidGround n)) : Convex ℝ (starCone X) := by
  rw [starCone_eq_iInter]
  exact convex_iInter fun e => (isOpen_convex_coord X e).2

/-! ### Order / lattice behaviour -/

/-- The empty-support covector `0` has the whole space as its (top) cone. -/
theorem starCone_zero : starCone (0 : SignVec (BraidGround n)) = Set.univ := by
  ext t
  constructor
  · intro _; trivial
  · intro _ e he; exact absurd rfl he

/-- **Antitone in the face order.**  A finer face `Y` (`X ⊑ Y`, more nonzero coordinates) has a
smaller cone: `starCone Y ⊆ starCone X`. -/
theorem starCone_antitone {X Y : SignVec (BraidGround n)} (h : X ⊑ Y) :
    starCone Y ⊆ starCone X := by
  intro t ht e he
  have hxy : X e = Y e := (h e).resolve_left he
  rw [hxy]
  exact ht e (hxy ▸ he)

/-- **Intersection into the composite.**  The intersection of two star cones lands in the star
cone of the composition `X ∘ Y` (support `= supp X ∪ supp Y`). -/
theorem starCone_inter_subset (X Y : SignVec (BraidGround n)) :
    starCone X ∩ starCone Y ⊆ starCone (X ⊙ Y) := by
  rintro t ⟨hX, hY⟩ e he
  by_cases h0 : X e = 0
  · have hc : (X ⊙ Y) e = Y e := if_pos h0
    rw [hc] at he ⊢
    exact hY e he
  · have hc : (X ⊙ Y) e = X e := if_neg h0
    rw [hc] at he ⊢
    exact hX e he

/-- **Intersection equals the composite cone** when `X` and `Y` agree on the overlap of their
supports.  Then `starCone X ∩ starCone Y = starCone (X ∘ Y)`. -/
theorem starCone_inter_eq_comp (X Y : SignVec (BraidGround n))
    (hagree : ∀ e, X e ≠ 0 → Y e ≠ 0 → X e = Y e) :
    starCone X ∩ starCone Y = starCone (X ⊙ Y) := by
  apply Set.Subset.antisymm (starCone_inter_subset X Y)
  intro t ht
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · -- `t ∈ starCone X`
    have hc : (X ⊙ Y) e = X e := if_neg he
    have h := ht e (by rw [hc]; exact he)
    rwa [hc] at h
  · -- `t ∈ starCone Y`
    by_cases h0 : X e = 0
    · have hc : (X ⊙ Y) e = Y e := if_pos h0
      have h := ht e (by rw [hc]; exact he)
      rwa [hc] at h
    · have hc : (X ⊙ Y) e = X e := if_neg h0
      have hXY : X e = Y e := hagree e h0 he
      have h := ht e (by rw [hc]; exact h0)
      rw [hc, hXY] at h; exact h

/-! ### Nonemptiness / realizability -/

/-- Any timing lies in the star cone of *its own* covector. -/
theorem mem_starCone_self (x : Fin n → ℝ) : x ∈ starCone (braidCovectorR x) := by
  intro e _; rfl

/-- **Realizability.**  Every covector of the braid arrangement has a nonempty open star cone. -/
theorem starCone_nonempty_of_mem {X : SignVec (BraidGround n)} (hX : X ∈ braidCovectors n) :
    (starCone X).Nonempty := by
  obtain ⟨x, rfl⟩ := hX
  exact ⟨fun i => (x i : ℝ), by rw [← braidCovectorR_intCast]; exact mem_starCone_self _⟩

/-- The star cone of the covector of any integer height function is nonempty, witnessed by the
real timing `i ↦ (x i : ℝ)`. -/
theorem starCone_nonempty_of_braidSign (x : Fin n → ℤ) :
    (starCone (braidSign x)).Nonempty :=
  starCone_nonempty_of_mem ⟨x, rfl⟩

/-- **Realizability at a chamber.**  For any height function `σ` (in particular an injective one,
i.e. a tope/chamber) the open star cone of `braidSign σ` is nonempty, witnessed by the real
timing `i ↦ (σ i : ℝ)`.  Injectivity is *not* needed for nonemptiness. -/
theorem starCone_nonempty_of_tope (σ : Fin n → ℤ) :
    (starCone (braidSign σ)).Nonempty :=
  starCone_nonempty_of_braidSign σ

end CubeChains
