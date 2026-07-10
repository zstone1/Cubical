import CubeChains.FinalBraid.Lines
import CubeChains.Foundations.Altitude

/-!
# FinalBraid/EventNaming — the global event-naming lemma (formulation only)

This file **states** (does not yet prove) the lemma that underwrites the "one ambient braid
arrangement per component" program: for a non-self-linked, altitude-admitting `K`, the events of a
`v₀ → v₁` component of `Ch(K)` admit a **globally coherent naming** — equivalently, the event
local system has trivial monodromy, so the global event set `E_C` exists.

## The event system (reusing `Lines.lean`)

For a cube chain `a`, its **local events** are the pairs `(bead i, direction δ)` — the directions
of `a`'s beads (`EventObj a`), of which there are `dimSum a`.  A refinement `f : a ⟶ b` (`a` finer)
carries each fine event to the coarse event it sits inside, via the *same* `blockIdx`/`blockFace`/
`faceEmb` data that `linesRestrict` uses (`eventMap`).  This is a bijection
`EventObj a ≅ EventObj b` (both have `dimSum` elements, constant on a component).

## What "globally coherent naming" means (the thing to review)

`HasGlobalEventNaming K` asks for one naming of all events of all chains that is

* **coherent** — events matched by a refinement share a name:
  `name ⟨b, eventMap f e⟩ = name ⟨a, e⟩`;
* **faithful** — the `dimSum a` events of any *single* chain get *distinct* names.

Coherence pins the naming down along refinements (the transitions); faithfulness forbids two
events of one chain being folded together.  Together: the colimit of the event system is full-rank
on every component — no monodromy, i.e. the global labeling exists.

Design notes on the formulation:

* **Global, but fiberwise-faithful.**  Because refinements only relate chains in the *same*
  component, one global `name` with faithfulness *per chain* automatically encodes per-component
  coherence — no need to define "component" explicitly.  Different components are simply
  unconstrained relative to one another.
* **Just the naming, deliberately.**  This is only the *identification* of events across chains; it
  carries **no order/covector data**.  The forced-order functor `ι` into `Face(braidCOM n)` (the
  `refineOpToFace` generalization) is built *on top of* a naming — the monodromy obstruction lives
  entirely at this naming layer, so we isolate it here.
* Equivalent phrasings, if a different shape is preferred: (a) the event functor `Ch(K) ⥤ Type`
  (valued in bijections) is naturally isomorphic, on each component, to a constant functor; (b) each
  canonical map `EventObj a → colim` is injective.

**Layer:** FinalBraid.  **Imports:** `FinalBraid.Lines`, `Foundations.Altitude`.
Not part of the default `CubeChains` target.
-/

open CategoryTheory CubeChain

namespace FinalBraid

variable {K : BPSet}

/-- The **local events** of a cube chain `a`: the pairs `(bead i, direction δ)`.  There are
`Σᵢ (a.dims.get i) = dimSum a` of them (constant on a component of `Ch(K)`). -/
def EventObj (a : ChainCat.Obj K) : Type :=
  Σ i : Fin a.dims.length, Fin ((a.dims.get i : ℕ))

/-- The **event transition** along a refinement `f : a ⟶ b` (`a` finer than `b`): the fine event
`(bead i, direction δ)` is carried to the coarse event `(blockIdx f i, faceEmb (blockFace f i) δ)` —
the bead of `b` that `a`'s bead `i` refines, and the direction of that bead it occupies.  Same
`blockIdx`/`blockFace`/`faceEmb` data as `linesRestrict`; a bijection of the `dimSum`-element
sets. -/
noncomputable def eventMap {a b : ChainCat.Obj K} (f : a ⟶ b) (e : EventObj a) : EventObj b :=
  ⟨blockIdx f.φ.hom e.1, faceEmb (blockFace f.φ.hom e.1) e.2⟩

/-- **A globally coherent event naming for `K`.**  A set `σ` and a name for every event of every
chain such that refinements identify names (`coherent`) while the events of any one chain stay
distinct (`faithful`).  This is precisely "the global event structure exists" — the event local
system has trivial monodromy on every component. -/
def HasGlobalEventNaming (K : BPSet) : Prop :=
  ∃ (σ : Type) (name : (Σ a : ChainCat.Obj K, EventObj a) → σ),
    (∀ {a b : ChainCat.Obj K} (f : a ⟶ b) (e : EventObj a),
        name ⟨b, eventMap f e⟩ = name ⟨a, e⟩) ∧
    (∀ a : ChainCat.Obj K, Function.Injective fun e : EventObj a => name ⟨a, e⟩)

/-! ## The canonical naming — coherence is free, injectivity is everything

Rather than search for a naming, take the **universal** one: quotient all events by the relation
"`e` maps to `e'` under some refinement".  Any coherent naming factors through this quotient, so it
is initial; coherence holds by construction, and `HasGlobalEventNaming K` collapses to the single
statement that the quotient does not fold two events of one chain together
(`hasGlobalEventNaming_iff`).  This is the shape the induction actually attacks. -/

/-- The relation identifying an event with its image under a refinement `f : a ⟶ b`. -/
def EventRel (K : BPSet) :
    (Σ a : ChainCat.Obj K, EventObj a) → (Σ a : ChainCat.Obj K, EventObj a) → Prop :=
  fun p q => ∃ f : p.1 ⟶ q.1, eventMap f p.2 = q.2

/-- The **canonical (universal) event naming**: the quotient of all events by `EventRel`. -/
def canonicalName {K : BPSet} (p : Σ a : ChainCat.Obj K, EventObj a) : Quot (EventRel K) :=
  Quot.mk _ p

/-- The canonical naming is coherent by construction. -/
theorem canonicalName_coherent {K : BPSet} {a b : ChainCat.Obj K} (f : a ⟶ b) (e : EventObj a) :
    canonicalName (⟨b, eventMap f e⟩ : Σ a : ChainCat.Obj K, EventObj a)
      = canonicalName ⟨a, e⟩ :=
  (Quot.sound ⟨f, rfl⟩).symm

/-- **Reframing.**  A globally coherent event naming exists **iff** the canonical quotient is
injective on every chain's events.  Coherence is automatic; the whole content is "no folding". -/
theorem hasGlobalEventNaming_iff (K : BPSet) :
    HasGlobalEventNaming K ↔
      ∀ a : ChainCat.Obj K,
        Function.Injective fun e : EventObj a =>
          canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a) := by
  constructor
  · rintro ⟨σ, name, hcoh, hinj⟩ a e e' he
    have hresp : ∀ p q : Σ a : ChainCat.Obj K, EventObj a, EventRel K p q → name p = name q := by
      rintro p q ⟨f, hf⟩
      calc name p
          = name (⟨q.1, eventMap f p.2⟩ : Σ a : ChainCat.Obj K, EventObj a) := (hcoh f p.2).symm
        _ = name q := by rw [hf]
    have hlift : name (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a) = name ⟨a, e'⟩ :=
      congrArg (Quot.lift name hresp) he
    exact hinj a hlift
  · intro hinj
    exact ⟨Quot (EventRel K), canonicalName, fun f e => canonicalName_coherent f e, hinj⟩

/-- The reduced goal: the canonical naming is fibrewise injective (no folding). -/
def EventFiberInjective (K : BPSet) : Prop :=
  ∀ a : ChainCat.Obj K,
    Function.Injective fun e : EventObj a =>
      canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a)

/-- **THE TARGET LEMMA (statement).**  Every non-self-linked, altitude-admitting bi-pointed
precubical set has a globally coherent event naming.  By `hasGlobalEventNaming_iff` this is exactly
`EventFiberInjective K` — the fold-freeness the altitude induction proves. -/
def EventNamingGoal (K : BPSet) : Prop :=
  K.NonSelfLinked → K.AdmitsAltitude → HasGlobalEventNaming K

/-! ## Proof plan for `EventNamingGoal` (via `EventFiberInjective`)

The engine is: the canonical naming is trivial on the 1-skeleton (a spanning tree forces no
conflicts) and every 2-cell relation is `∂□ᵏ`-shaped, so NSL makes it fold-free.  Concretely:

1. **Reduce** `EventNamingGoal K` to `EventFiberInjective K` (done: `hasGlobalEventNaming_iff`).
2. **Strong induction on `n = alt(endpoint) − alt(start)`**, generalised over *both* endpoints
   (`Ch(a,b,·)`), because peeling the top vertex disconnects (the □² centre dies with its corner).
   Base `n ≤ 1`: `Ch` is discrete, fibres are singletons, injective trivially.
3. **Peel one altitude level.** A chain's last bead is a cube `c` ending at `b` of some dim `k ≥ 1`,
   from an initial vertex `u` at altitude `alt(b) − k`; strong-IH gives fold-freeness on
   `Ch(a,u,n−k)`.
4. **Re-attach the top cubes in increasing dimension**, so each cube's boundary is complete before
   it is filled.  Each attachment is either
   * a **merge** of two distinct built components — free (pushout), NSL makes the identification
     injective; or
   * a **loop-closing fill** within one component — the closed loop is `∂□ᵏ`-shaped, and NSL makes
     `∂□ᵏ` event-trivial (a cube's `k` directions are globally its `k` axes), so it does not fold.
5. **Crux sub-lemma:** every new loop is cube-boundary-generated (the permutohedral 2-skeleton of
   the path space) — so step 4 never meets a loop that is not a `∂`-cube.  This is the real work.
-/

end FinalBraid
