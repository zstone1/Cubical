import CubeChains.Precubical.Basic.Altitude
import CubeChains.Precubical.Chains.WedgeMap
import CubeChains.Precubical.Wedge.CubeMerge

/-!
# Precubical/Chains/Altitude — the cube's grading, and what a chain climbs

`□ⁿ` is graded by the number of coordinates fixed at `1` (`cube_admitsAltitude`).  Along a chain
the altitude rises by each cube's dimension (`isCubeChain_alt_final`), so a chain of `□ⁿ` has `n`
events (`wedgeDimSum_eq`); a serial wedge is graded by pulling the grading back along its merge
into a cube (`serialWedge_admitsAltitude`), and a map of serial wedges keeps the event count.
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

/-- Where bead `i` of a dimension word starts: the total dimension of the earlier beads. -/
def beadStart (dims : List ℕ+) (i : ℕ) : ℕ := BPSet.dimSum (dims.take i)

@[simp] theorem beadStart_zero (dims : List ℕ+) : beadStart dims 0 = 0 := rfl

@[simp] theorem beadStart_length (dims : List ℕ+) :
    beadStart dims dims.length = BPSet.dimSum dims := by
  rw [beadStart, List.take_length]

/-- Peeling the head bead. -/
theorem beadStart_cons_succ (c : ℕ+) (rest : List ℕ+) (i : ℕ) :
    beadStart (c :: rest) (i + 1) = (c : ℕ) + beadStart rest i := by
  simp [beadStart, BPSet.dimSum]

/-- One-step increment: bead `i` occupies `[beadStart i, beadStart i + dims.get i)`. -/
theorem beadStart_succ (dims : List ℕ+) (i : Fin dims.length) :
    beadStart dims (i.val + 1) = beadStart dims i + (dims.get i : ℕ) := by
  simp only [beadStart, BPSet.dimSum, List.map_take]
  rw [List.sum_take_succ _ _ (by simp [i.isLt])]
  simp

theorem beadStart_mono (dims : List ℕ+) : Monotone (beadStart dims) := by
  intro i j hij
  obtain ⟨k, rfl⟩ := Nat.le.dest hij
  simp only [beadStart, BPSet.dimSum, List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- No bead starts past the end. -/
theorem beadStart_le_dimSum (d : List ℕ+) (j : ℕ) : beadStart d j ≤ BPSet.dimSum d := by
  rcases le_or_gt j d.length with hj | hj
  · exact (beadStart_mono d hj).trans_eq (beadStart_length d)
  · rw [beadStart, List.take_of_length_le hj.le]

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

/-- **A chain of `□m` has `m` events**: its cubes climb the grading from `0` to `m`. -/
theorem CubeChains.wedgeDimSum_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) : BPSet.dimSum a = m := by
  have h := CubeChain.isCubeChain_alt_final _ (BPSet.cube_isAltitude m) _ _ _
    (CubeChain.beadCell_isCubeChain (K := □m) a χ.hom)
  rw [χ.app_init, χ.app_final, Beads.map_fst_toList] at h
  have h0 := BPSet.cubeAlt_vtx m false
  have h1 := BPSet.cubeAlt_vtx m true
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  change BPSet.cubeAlt m 0 ((□m).vtx true) = BPSet.cubeAlt m 0 ((□m).vtx false) + _ at h
  rw [h0, h1] at h
  omega

/-- **A map of serial wedges keeps the event count**: read in the cube the target merges into,
both are chains of it. -/
theorem CubeChain.serialWedge_dimSum_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    BPSet.dimSum ad = BPSet.dimSum cd :=
  (CubeChains.nonempty_toCube cd).elim fun χ => CubeChains.wedgeDimSum_eq (φ ≫ χ)
