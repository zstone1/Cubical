import CubeChains.FinalBraid.EventNaming
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

/-!
# FinalBraid/EventInduction — sorry-free scaffolding (the altitude induction is REFUTED)

⛔ **The theorem this file was written to prove is FALSE.**  It attempted the reduction
`EventNamingGoal K → EventFiberInjective K` (via `hasGlobalEventNaming_iff`) followed by an
**altitude strong induction** to conclude `NonSelfLinked ∧ AdmitsAltitude ⟹ HasGlobalEventNaming`.
`Testing/EventNamingCounterexample.lean` refutes exactly that implication (the *trinity*): a
non-self-linked, altitude-graded `K` whose event naming folds a single line's two events (a genuine
monodromy around three filling squares).  The inductive step `efi_step` is therefore **unprovable**
and has been removed together with the false theorem `hasGlobalEventNaming_of_nsl_altitude` (see the
`REFUTED` note at the end of this file).  The working approach — supply the labelling as **input
data** (an HDA), so coherence is *free* — lives in `FinalBraid/HDA.lean`.

## What survives (sorry-free, reusable scaffolding)

* `BPSet.reBase u v` (+ `reBase_self`/`nonSelfLinked_reBase`): `K` re-based at a new endpoint pair,
  so `ChainCat.Obj (K.reBase u v)` is "cube chains from `u` to `v`".
* The **altitude counting identity** `chainDimSum_eq` (via the telescoping `alt_isCubeChain`):
  every chain from `u` to `v` has `dimSum = alt v − alt u`, a well-defined span grading.
* `eventObj_card` / `eventObj_subsingleton_of_dimSum_le_one` and the base case `efi_base`
  (a chain with `≤ 1` event is fold-free).
* `nsl_faces_distinct`: distinct box-faces of a cube have distinct images (NSL rigidity).

**Layer:** FinalBraid.  **Imports:** `FinalBraid.EventNaming` (which brings `Lines`, `Category`,
`WedgeMap`, `Altitude`), mathlib big-operators/`Fintype`.
-/

open CategoryTheory Opposite CubeChain

/-! ## Re-basing: the general-endpoint chain category

`reBase` must live in the `BPSet` namespace (not `FinalBraid.BPSet`) so that dot-notation
`K.reBase u v` resolves. -/

namespace BPSet

/-- **Re-base** a bi-pointed set at a new pair of vertices.  `K.reBase u v` has the same underlying
precubical set but `init := u`, `final := v`, so `ChainCat.Obj (K.reBase u v)` is the category of
cube chains from `u` to `v`.  `NonSelfLinked`/`IsAltitude` are properties of `toPsh`, hence
unchanged. -/
def reBase (K : BPSet) (u v : K.toPsh.cells 0) : BPSet where
  toPsh := K.toPsh
  init := u
  final := v

@[simp] theorem reBase_toPsh (K : BPSet) (u v : K.toPsh.cells 0) :
    (K.reBase u v).toPsh = K.toPsh := rfl

@[simp] theorem reBase_init (K : BPSet) (u v : K.toPsh.cells 0) :
    (K.reBase u v).init = u := rfl

@[simp] theorem reBase_final (K : BPSet) (u v : K.toPsh.cells 0) :
    (K.reBase u v).final = v := rfl

/-- Re-basing at the original endpoints is the identity (structure eta). -/
theorem reBase_self (K : BPSet) : K.reBase K.init K.final = K := rfl

/-- Non-self-linkedness is unchanged by re-basing (it only refers to `toPsh`). -/
theorem nonSelfLinked_reBase (K : BPSet) (u v : K.toPsh.cells 0)
    (h : K.NonSelfLinked) : (K.reBase u v).NonSelfLinked := h

end BPSet

namespace FinalBraid

variable {K : BPSet}

/-! ## The number of events of a chain, and its subsingleton base case -/

/-- The **event count** of a chain: `Σᵢ (dims i)`, the number of `EventObj` elements. -/
def dimSum (a : ChainCat.Obj K) : ℕ := (a.dims.map (fun d : ℕ+ => (d : ℕ))).sum

/-- Rewriting the finite sum `Σ i, (l.get i)` of a `ℕ+`-list as the plain list sum. -/
theorem sum_fin_pnat (l : List ℕ+) :
    (∑ i : Fin l.length, ((l.get i : ℕ+) : ℕ)) = (l.map (fun d : ℕ+ => (d : ℕ))).sum := by
  rw [Fin.sum_univ_def,
    show (fun i : Fin l.length => ((l.get i : ℕ+) : ℕ)) = (fun d : ℕ+ => (d : ℕ)) ∘ l.get from rfl,
    ← List.map_map, ← List.ofFn_eq_map, List.ofFn_get]

/-- The `ℤ`-cast of `dimSum` distributes over the list. -/
theorem cast_map_sum (l : List ℕ+) : ((l.map (fun d : ℕ+ => (d : ℕ))).sum : ℤ)
    = (l.map (fun d : ℕ+ => (d : ℤ))).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-- The event set of a chain is a finite type (a `Σ` of `Fin`s). -/
noncomputable instance eventObjFintype (a : ChainCat.Obj K) : Fintype (EventObj a) := by
  unfold EventObj; infer_instance

/-- The event set of a chain has exactly `dimSum a` elements. -/
theorem eventObj_card (a : ChainCat.Obj K) : Fintype.card (EventObj a) = dimSum a := by
  unfold dimSum
  rw [show Fintype.card (EventObj a)
        = Fintype.card (Σ i : Fin a.dims.length, Fin ((a.dims.get i : ℕ+) : ℕ)) from rfl,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_fin_pnat a.dims

/-- **Base case, cardinality form.**  A chain with `≤ 1` event has a subsingleton event set. -/
theorem eventObj_subsingleton_of_dimSum_le_one (a : ChainCat.Obj K) (h : dimSum a ≤ 1) :
    Subsingleton (EventObj a) := by
  rw [← Fintype.card_le_one_iff_subsingleton, eventObj_card]; exact h

/-! ## The altitude counting identity

`alt_isCubeChain` telescopes the altitude across a folded cube chain; combined with the
`wedgeToCubes` read-off it yields `chainDimSum_eq`, the fact that every chain from `u` to `v` has
`dimSum = alt v − alt u`. -/

/-- **Altitude telescopes across a cube chain.**  For a folded chain `p → cubes → q`, the altitude
of the endpoint exceeds that of the start by the sum of the cubes' dimensions.  Each bead of dim
`k` raises altitude by exactly `k` (`alt_vertex₀`/`alt_vertex₁`). -/
theorem alt_isCubeChain (alt : ∀ n, K.toPsh.cells n → ℤ) (hax : K.toPsh.IsAltitude alt) :
    ∀ (p q : K.toPsh.cells 0) (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))),
      IsCubeChain p cubes q →
      alt 0 q = alt 0 p + (cubes.map (fun c => (c.1 : ℤ))).sum
  | p, q, [], h => by
      simp only [List.map_nil, List.sum_nil, add_zero]
      exact congrArg (alt 0) h.symm
  | p, q, ⟨n, c⟩ :: rest, h => by
      obtain ⟨hhead, htail⟩ := h
      have h0 : alt 0 p = alt (n : ℕ) c := by
        rw [← hhead]; exact PrecubicalSet.alt_vertex₀ alt hax c
      have h1 : alt 0 (K.toPsh.vertex₁ c) = alt (n : ℕ) c + (n : ℕ) :=
        PrecubicalSet.alt_vertex₁ alt hax c
      have hrest := alt_isCubeChain alt hax (K.toPsh.vertex₁ c) q rest htail
      rw [hrest, h1, h0]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- **Every chain from `u` to `v` has `dimSum = alt v − alt u`** (as integers).  Read off the
junction-vertex cube list with `wedgeToCubes`; its dimensions are `a.dims`
(`wedgeToCubes_dims`) and it is a chain from `a.map init = K.init` to `a.map final = K.final`
(`wedgeToCubes_isCubeChain`), so `alt_isCubeChain` applies. -/
theorem chainDimSum_eq (alt : ∀ n, K.toPsh.cells n → ℤ) (hax : K.toPsh.IsAltitude alt)
    (a : ChainCat.Obj K) : (dimSum a : ℤ) = alt 0 K.final - alt 0 K.init := by
  have hchain := wedgeToCubes_isCubeChain a.dims a.map.hom
  rw [a.map.app_init, a.map.app_final] at hchain
  have hsum := alt_isCubeChain alt hax K.init K.final _ hchain
  have hmap : (wedgeToCubes ⟨a.dims, a.map.hom⟩).map (fun c => (c.1 : ℤ))
      = a.dims.map (fun d : ℕ+ => (d : ℤ)) := by
    rw [show (fun c : (Σ n : ℕ+, K.toPsh.cells (n : ℕ)) => (c.1 : ℤ))
          = (fun d : ℕ+ => (d : ℤ)) ∘ (fun c : (Σ n : ℕ+, K.toPsh.cells (n : ℕ)) => c.1) from rfl,
        ← List.map_map, wedgeToCubes_dims]
  rw [hsum, hmap]
  have hcancel : alt 0 K.init + (a.dims.map (fun d : ℕ+ => (d : ℤ))).sum - alt 0 K.init
      = (a.dims.map (fun d : ℕ+ => (d : ℤ))).sum := by ring
  rw [hcancel]
  exact cast_map_sum a.dims

/-! ## NSL rigidity (the concrete cube-boundary distinguishability)

The one genuinely concrete consequence of non-self-linkedness that feeds the `∂□ᵏ`-coherence:
distinct box-faces of a cube have distinct images.  This is `NonSelfLinked` applied through the
cube's canonical map, and is sorry-free. -/

/-- **NSL ⟹ distinct faces stay distinct.**  Two distinct box morphisms `x ≠ y : □ᵐ ⟶ □ᵏ` name
distinct `m`-cells of any `k`-cube `c` (the canonical map `□ᵏ ⟶ K` is injective in every
dimension).  The `k` axis-directions of a cube are a special case (`x, y` the two axis edges),
so they are globally distinguishable — the cell-level core of the `∂□ᵏ`-coherence lemma. -/
theorem nsl_faces_distinct (hnsl : K.NonSelfLinked) {k m : ℕ} (c : K.toPsh.cells k)
    (x y : Box.ob m ⟶ Box.ob k)
    (hxy : x ≠ y) :
    (K.toPsh.cubeMap c).app (op (Box.ob m)) x ≠ (K.toPsh.cubeMap c).app (op (Box.ob m)) y :=
  fun h => hxy (hnsl k c m h)

/-! ## Base case and the strong-induction skeleton -/

/-- **Base case (fold-freeness for a single chain with ≤ 1 event).**  Immediate from
`Subsingleton (EventObj a)`.  Sorry-free. -/
theorem efi_base (a : ChainCat.Obj K) (h : dimSum a ≤ 1) :
    Function.Injective
      (fun e : EventObj a => canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a)) := by
  haveI := eventObj_subsingleton_of_dimSum_le_one a h
  exact fun x y _ => Subsingleton.elim x y

/-! ## REFUTED — the altitude induction does not close (kept for scaffolding only)

⛔ **REFUTED, do not use.**  The strategy this file was written to execute — reduce `EventNamingGoal`
to `EventFiberInjective` and prove the latter by altitude strong induction — is **false**.  Its
crux, the step

    efi_step :  peel one altitude level, re-attach the top cubes so every new loop is `∂□ᵏ`-shaped
                and NSL-trivial

is **unprovable**: `Testing/EventNamingCounterexample.lean` exhibits the *trinity* `T` (three lines
`a ⤳ d`, each pair filled by a square), which is `NonSelfLinked` and altitude-graded yet whose event
naming folds the two events of a single line — a genuine monodromy around the three squares.
Consequently the target theorem

    hasGlobalEventNaming_of_nsl_altitude :
      K.NonSelfLinked → K.AdmitsAltitude → HasGlobalEventNaming K

is **FALSE**.  It has been removed, along with the `sorry`-backed `efi_step`/`efi_aux` and the
speculative sub-lemmas (`MergeCoherence`/`LoopFillCoherence`/`LoopsAreCubeBoundary`) that only
served its refuted proof plan.  The fix — make the labelling **input data** (an HDA), so coherence
is *free* (no monodromy to reconstruct) and only fibre-injectivity (`RunInjective`) remains — is in
`FinalBraid/HDA.lean` (`hasGlobalEventNaming_of_labelling`).  Everything above this note is
sorry-free and reusable regardless of the naming strategy. -/

end FinalBraid
