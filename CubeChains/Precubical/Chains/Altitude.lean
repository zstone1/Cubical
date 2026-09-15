import CubeChains.Precubical.Basic.Altitude
import CubeChains.Precubical.Chains.WedgeMap
import CubeChains.Precubical.Wedge.CubeMerge

/-!
# Precubical/Chains/Altitude — the cube's grading, and what a chain climbs

`□ⁿ` is graded by the number of coordinates fixed at `1` (`cube_admitsAltitude`).  Along a chain
the altitude rises by each cube's dimension (`isCubeChain_alt_final`, `isCubeChain_alt_get`), and a
serial wedge is graded by pulling the grading back along its merge into a cube
(`serialWedge_admitsAltitude`).
-/

open CategoryTheory Opposite StdCube

namespace BPSet

/-- The altitude on `□ᴺ`: the number of coordinates a cell fixes at `1`. -/
def cubeAlt (N : ℕ) : ∀ m, (□N).cells m → ℤ :=
  fun _ x => (trueCount (Box.sign x) : ℤ)

/-- A face raises `trueCount` by `ε` (`Box.sign_coface_comp`). -/
theorem cube_isAltitude (N : ℕ) : (□N).toPsh.IsAltitude (cubeAlt N) := fun ε i x => by
  change (trueCount (Box.sign ((□N).toPsh.faceMap ε i x)) : ℤ)
    = (trueCount (Box.sign x) : ℤ) + (if ε then 1 else 0)
  rw [show Box.sign ((□N).toPsh.faceMap ε i x) = faceCell ε i (Box.sign x) from
    Box.sign_coface_comp ε i x, trueCount_face]
  push_cast
  ring

theorem cubeAlt_vtx (N : ℕ) (ε : Bool) : cubeAlt N 0 ((□N).vtx ε) = if ε then N else 0 := by
  cases ε
  · exact congrArg Nat.cast (trueCount_constVertex_false N)
  · exact congrArg Nat.cast (trueCount_constVertex_true N)

/-- **The standard cube admits an altitude.** -/
theorem cube_admitsAltitude (N : ℕ) : (□N).AdmitsAltitude :=
  ⟨cubeAlt N, cube_isAltitude N, cubeAlt_vtx N false⟩

/-- **Every serial wedge admits an altitude** — pulled back along its merge into a cube. -/
theorem serialWedge_admitsAltitude (d : List ℕ+) : (⋁d).AdmitsAltitude :=
  (CubeChains.nonempty_toCube d).elim fun χ => (cube_admitsAltitude _).of_hom χ

end BPSet

namespace CubeChain

variable {K : BPSet}

/-- **Altitude gap of a chain = its total dimension** — each cube contributes its dimension via
`alt_vertex₀`/`alt_vertex₁` across the junction. -/
theorem isCubeChain_alt_final (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q →
      alt 0 q = alt 0 p + ((BPSet.dimSum (cubes.map (·.1)) : ℕ) : ℤ)
  | [], p, q, h => by
      simp only [List.map_nil, BPSet.dimSum, List.sum_nil, Nat.cast_zero, add_zero]
      rw [h]
  | ⟨n, c⟩ :: rest, p, q, h => by
      obtain ⟨hsrc, hrest⟩ := h
      have ih := isCubeChain_alt_final alt hax rest (K.toPsh.vertexEnd true c) q hrest
      have h0 := PrecubicalSet.alt_vertex₀ alt hax c
      have h1 := PrecubicalSet.alt_vertex₁ alt hax c
      rw [hsrc] at h0
      simp only [List.map_cons, BPSet.dimSum, List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih, h1, ← h0]; simp only [BPSet.dimSum, List.map_map]; ring

/-- **Cube altitudes along a chain**: the `i`-th cube sits at the prefix sum of the earlier
cubes' dimensions. -/
theorem isCubeChain_alt_get (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) (p q : K.cells 0),
      IsCubeChain p cubes q → ∀ (i : ℕ) (h : i < cubes.length),
      alt _ (cubes.get ⟨i, h⟩).2 = alt 0 p + ((beadStart (cubes.map (·.1)) i : ℕ) : ℤ)
  | [], _, _, _, _, h => absurd h (by simp)
  | ⟨n, c⟩ :: rest, p, _, hchain, 0, _ => by
      obtain ⟨h1, _⟩ := hchain
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      simp only [beadStart_zero, Nat.cast_zero, add_zero]
      exact hc
  | ⟨n, c⟩ :: rest, p, q, hchain, k + 1, h => by
      obtain ⟨h1, h2⟩ := hchain
      have hk : k < rest.length := by simpa using h
      have ih := isCubeChain_alt_get alt hax rest (K.toPsh.vertexEnd true c) q h2 k hk
      have hc : alt (n : ℕ) c = alt 0 p := by rw [← h1, PrecubicalSet.alt_vertex₀ alt hax]
      have hv1 : alt 0 (K.toPsh.vertexEnd true c) = alt 0 p + ((n : ℕ) : ℤ) := by
        rw [PrecubicalSet.alt_vertex₁ alt hax, hc]
      change alt ((rest.get ⟨k, hk⟩).1 : ℕ) (rest.get ⟨k, hk⟩).2
          = alt 0 p + ((beadStart ((⟨n, c⟩ :: rest).map (·.1)) (k + 1) : ℕ) : ℤ)
      rw [ih, hv1, List.map_cons, beadStart_cons_succ]
      push_cast
      ring

end CubeChain
