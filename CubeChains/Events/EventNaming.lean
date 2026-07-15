import CubeChains.Salvetti.Lines
import CubeChains.Foundations.Altitude

/-!
# Events/EventNaming — events of a chain and the global naming property

The **events** of a cube chain `a` are the pairs `(bead i, direction δ)` (`EventObj a`); a
refinement `f : a ⟶ b` carries each to the coarse event it sits inside (`eventMap`, the same
block data as `linesRestrict`).  `HasGlobalEventNaming K` asks for one naming of all events that
is **coherent** (refinements identify names) and **fibre-injective** (distinct events of one chain
get distinct names).  Taking the universal naming (quotient by "matched by a refinement") makes
coherence automatic, so `hasGlobalEventNaming_iff` reduces the property to fibre-injectivity alone.
-/

open CategoryTheory CubeChain

namespace CubeChains

variable {K : BPSet}

/-- The **local events** of a cube chain `a`: the pairs `(bead i, direction δ)`.  There are
`Σᵢ (a.dims.get i) = dimSum a` of them (constant on a component of `Ch(K)`). -/
def EventObj (a : Ch K) : Type :=
  Σ i : ChainCat.Bead a, Fin (ChainCat.beadDim a i)

/-- The event set of a chain is finite (a `Σ` of `Fin`s). -/
instance eventObjFintype (a : Ch K) : Fintype (EventObj a) := by
  unfold EventObj; infer_instance

/-- The **event transition** along a refinement `f : a ⟶ b` (`a` finer than `b`): the fine event
`(bead i, direction δ)` is carried to the coarse event `(blockIdx f i, faceEmb (blockFace f i) δ)` —
the bead of `b` that `a`'s bead `i` refines, and the direction of that bead it occupies.  Same
`blockIdx`/`blockFace`/`faceEmb` data as `linesRestrict`; a bijection of the `dimSum`-element
sets. -/
noncomputable def eventMap {a b : Ch K} (f : a ⟶ b) (e : EventObj a) : EventObj b :=
  ⟨blockIdx fᵂ e.1, faceEmb (blockFace fᵂ e.1) e.2⟩

/-- **A globally coherent event naming for `K`.**  A set `σ` and a name for every event of every
chain such that refinements identify names (`coherent`) while the events of any one chain stay
distinct (`faithful`).  This is precisely "the global event structure exists" — the event local
system has trivial monodromy on every component. -/
def HasGlobalEventNaming (K : BPSet) : Prop :=
  ∃ (σ : Type) (name : (Σ a : Ch K, EventObj a) → σ),
    (∀ {a b : Ch K} (f : a ⟶ b) (e : EventObj a),
        name ⟨b, eventMap f e⟩ = name ⟨a, e⟩) ∧
    (∀ a : Ch K, Function.Injective fun e : EventObj a => name ⟨a, e⟩)

/-! ## The canonical naming — coherence is free, injectivity is everything

Rather than search for a naming, take the **universal** one: quotient all events by the relation
"`e` maps to `e'` under some refinement".  Any coherent naming factors through this quotient, so it
is initial; coherence holds by construction, and `HasGlobalEventNaming K` collapses to the single
statement that the quotient does not fold two events of one chain together
(`hasGlobalEventNaming_iff`).  This is the shape the induction actually attacks. -/

/-- The relation identifying an event with its image under a refinement `f : a ⟶ b`. -/
def EventRel (K : BPSet) :
    (Σ a : Ch K, EventObj a) → (Σ a : Ch K, EventObj a) → Prop :=
  fun p q => ∃ f : p.1 ⟶ q.1, eventMap f p.2 = q.2

/-- The **canonical (universal) event naming**: the quotient of all events by `EventRel`. -/
def canonicalName {K : BPSet} (p : Σ a : Ch K, EventObj a) : Quot (EventRel K) :=
  Quot.mk _ p

/-- The canonical naming is coherent by construction. -/
theorem canonicalName_coherent {K : BPSet} {a b : Ch K} (f : a ⟶ b) (e : EventObj a) :
    canonicalName (⟨b, eventMap f e⟩ : Σ a : Ch K, EventObj a)
      = canonicalName ⟨a, e⟩ :=
  (Quot.sound ⟨f, rfl⟩).symm

/-- **Reframing.**  A globally coherent event naming exists **iff** the canonical quotient is
injective on every chain's events.  Coherence is automatic; the whole content is "no folding". -/
theorem hasGlobalEventNaming_iff (K : BPSet) :
    HasGlobalEventNaming K ↔
      ∀ a : Ch K,
        Function.Injective fun e : EventObj a =>
          canonicalName (⟨a, e⟩ : Σ a : Ch K, EventObj a) := by
  constructor
  · rintro ⟨σ, name, hcoh, hinj⟩ a e e' he
    have hresp : ∀ p q : Σ a : Ch K, EventObj a, EventRel K p q → name p = name q := by
      rintro p q ⟨f, hf⟩
      calc name p
          = name (⟨q.1, eventMap f p.2⟩ : Σ a : Ch K, EventObj a) := (hcoh f p.2).symm
        _ = name q := by rw [hf]
    have hlift : name (⟨a, e⟩ : Σ a : Ch K, EventObj a) = name ⟨a, e'⟩ :=
      congrArg (Quot.lift name hresp) he
    exact hinj a hlift
  · intro hinj
    exact ⟨Quot (EventRel K), canonicalName, fun f e => canonicalName_coherent f e, hinj⟩

/-- The reduced goal: the canonical naming is fibrewise injective (no folding). -/
def EventFiberInjective (K : BPSet) : Prop :=
  ∀ a : Ch K,
    Function.Injective fun e : EventObj a =>
      canonicalName (⟨a, e⟩ : Σ a : Ch K, EventObj a)

end CubeChains
