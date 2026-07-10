import CubeChains.FinalBraid.EventNaming
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

/-!
# FinalBraid/EventInduction — the altitude induction for `EventFiberInjective`

This file carries out (as far as it is currently proved) the **altitude strong induction** that
underwrites `hasGlobalEventNaming_of_nsl_altitude`.  Recall (`EventNaming.lean`) that by
`hasGlobalEventNaming_iff` the whole content of the global-event-naming lemma is

    `EventFiberInjective K` :  the canonical event quotient never folds two events of one chain.

The strategy (see the "Proof plan" docstring at the end of `EventNaming.lean`) is a strong
induction on the **altitude span** `n = alt(v) − alt(u)` of a *general* pair of endpoints `u, v`,
because peeling the top vertex disconnects the space.  We realise the general-endpoint chain
category by **re-basing** the bi-pointed set: `K.reBase u v` is `K` with `init := u`, `final := v`,
so `ChainCat.Obj (K.reBase u v)` is exactly "cube chains from `u` to `v`", and `EventObj`,
`eventMap`, `canonicalName`, `EventFiberInjective` all apply verbatim.

## What is proved here (sorry-free)

* `BPSet.reBase`, and `reBase_self` (`K.reBase K.init K.final = K`).
* The **altitude counting identity** `chainDimSum_eq`:
  `(dimSum a : ℤ) = alt 0 K.final − alt 0 K.init` for every chain `a` — via the telescoping
  `alt_isCubeChain` over the junction-vertex cube list read off by `wedgeToCubes`.  Consequently
  every chain from `u` to `v` has the *same* number of events, `alt v − alt u`; this is what makes
  the span a well-defined grading.
* `eventObj_card` / `eventObj_subsingleton_of_dimSum_le_one`: a chain with `≤ 1` event has a
  subsingleton event set.
* The **base case** of the induction (`efi_base`): any chain with `dimSum ≤ 1` is fold-free,
  because its event set is a subsingleton.  Sorry-free.
* The **strong-induction wiring** `efi_aux` and the **main theorem**
  `hasGlobalEventNaming_of_nsl_altitude`: the whole theorem is reduced to the single inductive
  step `efi_step`.
* The concrete **NSL rigidity** corollary `nsl_faces_distinct` (distinct box-faces of a cube have
  distinct images).

## What is open (each `sorry` names the exact missing fact)

* `efi_step` — the inductive step (peel one altitude level, re-attach the top cubes; steps 4–5 of
  the plan).  This is the mathematical heart.  It is stated so that it consumes the strong-IH and
  concludes fold-freeness at span `n`.  Its intended decomposition into the precise sub-lemmas
  `MergeCoherence`, `LoopFillCoherence` and the crux `LoopsAreCubeBoundary` is stated below.

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

/-- **THE INDUCTIVE STEP (steps 4–5 of the plan).**  Given fold-freeness for *all* strictly smaller
altitude spans and *all* endpoints (the strong-IH), prove it at span `n ≥ 2` for endpoints `u, v`.

The intended proof (see the sub-lemma statements below):

* Peel the top altitude level: a chain's last bead is a cube ending at `v` of dim `k ≥ 1`, from a
  vertex `u₀` at altitude `alt v − k`; the strong-IH gives fold-freeness on `Ch(u, u₀)`.
* Re-attach the top cubes in increasing dimension.  Each attachment is a `MergeCoherence` merge of
  two built components (a pushout; NSL makes the identification injective) or a
  `LoopFillCoherence` loop-closing fill inside one component (the loop is `∂□ᵏ`-shaped and NSL
  makes it event-trivial).  `LoopsAreCubeBoundary` (the crux) guarantees every new loop is one of
  these two kinds.

**This is the mathematical heart and is currently unproved.** -/
theorem efi_step (hnsl : K.NonSelfLinked) (alt : ∀ n, K.toPsh.cells n → ℤ)
    (hax : K.toPsh.IsAltitude alt) (n : ℕ) (hn : 1 < n) (u v : K.toPsh.cells 0)
    (hbound : ∀ a : ChainCat.Obj (K.reBase u v), dimSum a ≤ n)
    (IH : ∀ m, m < n → ∀ (u' v' : K.toPsh.cells 0),
        (∀ a : ChainCat.Obj (K.reBase u' v'), dimSum a ≤ m)
        → EventFiberInjective (K.reBase u' v')) :
    EventFiberInjective (K.reBase u v) :=
  -- [OPEN — steps 4–5 of the plan]  The peel/re-attach argument.  Needs `MergeCoherence`,
  -- `LoopFillCoherence`, and the crux `LoopsAreCubeBoundary` (all stated below), plus the
  -- concrete monodromy/connectivity bookkeeping of the event colimit that this scaffold does not
  -- yet build.  This is a genuine research crux, not a routine gap.
  sorry

/-- **Strong induction on the altitude span, generalised over both endpoints.**  The hypothesis
`∀ a, dimSum a ≤ n` is the combinatorial bound the induction descends on; by `chainDimSum_eq` it is
implied by (indeed equal to) the altitude span, so at the top level it holds with `n = alt v −
alt u`.  The base case `n ≤ 1` is `efi_base`; the inductive step is `efi_step`. -/
theorem efi_aux (hnsl : K.NonSelfLinked) (alt : ∀ n, K.toPsh.cells n → ℤ)
    (hax : K.toPsh.IsAltitude alt) :
    ∀ (n : ℕ) (u v : K.toPsh.cells 0),
      (∀ a : ChainCat.Obj (K.reBase u v), dimSum a ≤ n)
      → EventFiberInjective (K.reBase u v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro u v hbound
    rcases Nat.lt_or_ge 1 n with hn | hn
    · exact efi_step hnsl alt hax n hn u v hbound IH
    · intro a
      exact efi_base a (le_trans (hbound a) hn)

/-- **THE TARGET LEMMA.**  Every non-self-linked, altitude-admitting bi-pointed precubical set has a
globally coherent event naming.  Reduced (`hasGlobalEventNaming_iff`) to `EventFiberInjective K`,
which is the top-level instance of the altitude strong induction `efi_aux` at `u = init`,
`v = final`, `n = alt final − alt init`. -/
theorem hasGlobalEventNaming_of_nsl_altitude {K : BPSet}
    (hnsl : K.NonSelfLinked) (halt : K.AdmitsAltitude) : HasGlobalEventNaming K := by
  rw [hasGlobalEventNaming_iff]
  obtain ⟨alt, hax, _hinit⟩ := halt
  have hmain := efi_aux hnsl alt hax (alt 0 K.final - alt 0 K.init).toNat K.init K.final ?_
  · exact hmain
  · intro a
    have hd : (dimSum a : ℤ)
        = alt 0 (K.reBase K.init K.final).final - alt 0 (K.reBase K.init K.final).init :=
      chainDimSum_eq alt hax a
    simp only [BPSet.reBase_final, BPSet.reBase_init] at hd
    omega

/-! ## The precise sub-lemmas the crux decomposes into (statements + analysis)

The inductive step `efi_step` is intended to be assembled from the following three statements.  They
are given here as precise `Prop`s so the remaining mathematical content is pinned down; their proofs
are the genuine research crux (step 5) and are **not** attempted in this scaffold. -/

/-- **Merge coherence (step 4, merge case).**  When two events `e ≠ e'` of a chain `a` are carried,
under refinements into two chains `b`, `b'` whose top cubes are *distinct* beads (a genuine merge of
two built sub-components), their images stay distinct — equivalently, the pushout that glues the two
sub-components along their shared boundary identifies events injectively.  NSL is what makes the
gluing injective (distinct beads meet only along a common face, whose events already agree by the
strong-IH). -/
def MergeCoherence (K : BPSet) : Prop :=
  ∀ (a : ChainCat.Obj K) (e e' : EventObj a),
    -- the two events lie under distinct top beads of every common coarsening ⇒ distinct names
    (∀ (b : ChainCat.Obj K) (f : a ⟶ b), (eventMap f e).1 ≠ (eventMap f e').1) →
    canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a) ≠ canonicalName ⟨a, e'⟩

/-- **Loop-fill / `∂□ᵏ`-coherence (step 4, fill case).**  When the new relation closes a loop inside
a *single* component — the loop being the boundary of a `k`-cube `c` — the two boundary
decompositions assign the *same* name to each of the `k` axis-directions, and *distinct* names to
distinct axes.  Concretely: fold-freeness of the one-bead chain of `c`.  NSL supplies it because the
`k` directions of `c` are its `k` globally-rigid axes (`nsl_faces_distinct`). -/
def LoopFillCoherence (K : BPSet) : Prop :=
  ∀ {k : ℕ} (c : K.toPsh.cells (k + 1)) (a : ChainCat.Obj (K.reBase (K.toPsh.vertex₀ c)
      (K.toPsh.vertex₁ c))),
    -- `a` is the single-bead chain of `c`
    a.dims = [(⟨k + 1, Nat.succ_pos k⟩ : ℕ+)] →
    Function.Injective (fun e : EventObj a =>
      canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj (K.reBase (K.toPsh.vertex₀ c)
        (K.toPsh.vertex₁ c)), EventObj a))

/-- **The crux (step 5): every new loop is cube-boundary-generated.**  In the permutohedral
2-skeleton of the path space, any relation `canonicalName ⟨a,e⟩ = canonicalName ⟨a,e'⟩` between two
events of one chain is generated by the two elementary moves of the previous two lemmas — a merge of
distinct components, or a fill of a single-cube (`∂□ᵏ`) loop.  Equivalently: the event colimit has
no monodromy beyond the cube-boundary 2-cells.  This is the hard geometric core.

Formalised as: `MergeCoherence K` and `LoopFillCoherence K` together imply `EventFiberInjective K`
— i.e. controlling the two elementary loop types controls *all* folding. -/
def LoopsAreCubeBoundary (K : BPSet) : Prop :=
  MergeCoherence K → LoopFillCoherence K → EventFiberInjective K

end FinalBraid
