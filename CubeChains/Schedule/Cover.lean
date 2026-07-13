import CubeChains.Schedule.Atlas
import CubeChains.Schedule.Space
import CubeChains.Schedule.LabelSpace

/-!
# Schedule/Cover — the cover of `Sched K` by chain stars

The **star** of a chain `a` is the image of its chart: `star a = range (chartSched a)`.  Membership
is purely categorical (`mem_star_iff`): `x ∈ star a` iff `x`'s own (finest) chain refines `a`.  So
the fibre of the cover over a schedule `x` — the chains whose star contains it — is the **principal
up-set** of `x.chain` (`fibre_isPrincipal`, `fibre_isLeast`).  That is the load-bearing fact: it is
the contractibility hypothesis of the projection lemma (homotopy colimit), the Čech nerve being the
wrong tool here (cone intersections can be disconnected — `DESIGN.md` L7).

The stars of the *coarsest* chains already cover (`star_coarsest_cover`), and under `IsAtlas` every
star is open (`isOpen_star`) — a star pulls back, in any chart, to a union of open sub-cones.

Gotcha: `star a` is *not* the set of schedules of shape `a`; it is the whole open star of that
stratum (all its refinements), which is why membership is a `Nonempty` of a hom, not an equality.
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

variable {K : BPSet}

/-! ## Stars -/

/-- The **star** of a chain: the schedules its chart names. -/
def star (a : Ch K) : Set (Sched K) :=
  Set.range (chartSched a)

/-- Membership in a star is categorical: `chartSched` forgets the refinement but keeps the chain. -/
theorem mem_star_iff {a : Ch K} {x : Sched K} : x ∈ star a ↔ Nonempty (x.chain ⟶ a) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.2.1⟩
  · rintro ⟨f⟩
    exact ⟨⟨x.1, f, x.2⟩, rfl⟩

/-- Stars grow with coarsening: a refinement `f : a ⟶ b` composes onto the witness. -/
theorem star_mono {a b : Ch K} (f : a ⟶ b) : star a ⊆ star b := fun _ hx =>
  mem_star_iff.mpr ((mem_star_iff.mp hx).elim fun g => ⟨g ≫ f⟩)

/-! ## The fibre of the cover is a principal up-set

**This is the load-bearing lemma.**  For every schedule `x`, the chains whose star contains `x` are
exactly the coarsenings of `x.chain`, and `x.chain` is least among them — the fibre poset is
`↑(x.chain)`, hence contractible.  That, not a good-cover/Čech argument, is what feeds the
projection lemma `colim ≃ hocolim ≃ |N(Ch K)|`. -/

/-- Every schedule lies in the star of its own chain (the identity refinement). -/
theorem self_mem_star (x : Sched K) : x ∈ star x.chain :=
  mem_star_iff.mpr ⟨𝟙 x.chain⟩

/-- The fibre over `x` is the principal up-set of `x.chain` in the coarsening preorder. -/
theorem fibre_isPrincipal (x : Sched K) :
    {a : Ch K | x ∈ star a} = {a : Ch K | Nonempty (x.chain ⟶ a)} :=
  Set.ext fun _ => mem_star_iff

/-- `IsLeast` for the coarsening preorder `a ≤ b ↔ Nonempty (a ⟶ b)`, spelled out (no `Preorder`
instance on `Ch K`: it would collide with the category via `CategoryTheory.smallCategory`). -/
theorem fibre_isLeast (x : Sched K) :
    x.chain ∈ {a : Ch K | x ∈ star a} ∧
      ∀ a ∈ {a : Ch K | x ∈ star a}, Nonempty (x.chain ⟶ a) :=
  ⟨self_mem_star x, fun _ ha => mem_star_iff.mp ha⟩

/-! ## The coarsest-chain cover -/

/-- The stars of the coarsest chains already cover: every chain coarsens to a coarsest one
(`hasCoarsening`) and `star_mono` carries its schedules along. -/
theorem star_coarsest_cover (K : BPSet) :
    (⋃ b ∈ {b : Ch K | IsCoarsest b}, star b) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨b, hbmax, ⟨f⟩⟩ := hasCoarsening K x.chain
  exact Set.mem_iUnion₂.mpr ⟨b, hbmax, mem_star_iff.mpr ⟨f⟩⟩

/-! ## Chart restriction along a refinement -/

/-- Restrict a chart along `f : c ⟶ b`: a refinement of `c` is one of `b`. -/
noncomputable def chartIncl {c b : Ch K} (f : c ⟶ b) : Chart c → Chart b :=
  fun p => ⟨p.1, p.2.1 ≫ f, p.2.2⟩

/-- Functoriality of the event bijection. -/
theorem eventEquiv_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    eventEquiv (f ≫ g) = (eventEquiv f).trans (eventEquiv g) :=
  Equiv.ext fun e => eventMap_comp f g e

/-- Restricting a chart reindexes its coordinates along the event bijection. -/
theorem chartCoord_chartIncl {c b : Ch K} (f : c ⟶ b) (p : Chart c) (e : EventObj b) :
    chartCoord b (chartIncl f p) e = chartCoord c p ((eventEquiv f).symm e) := by
  have key : (eventEquiv (p.2.1 ≫ f)).symm e
      = (eventEquiv p.2.1).symm ((eventEquiv f).symm e) := by
    rw [eventEquiv_comp]
    exact Equiv.symm_trans_apply _ _ e
  change p.2.2.1 ((eventEquiv (p.2.1 ≫ f)).symm e).1
      = p.2.2.1 ((eventEquiv p.2.1).symm ((eventEquiv f).symm e)).1
  rw [key]

/-- Pull an event-timing of `b` back to `c` along `f : c ⟶ b` (a coordinate permutation). -/
noncomputable def evPull {c b : Ch K} (f : c ⟶ b) : (EventObj b → ℝ) → (EventObj c → ℝ) :=
  fun t e => t (eventMap f e)

theorem continuous_evPull {c b : Ch K} (f : c ⟶ b) : Continuous (evPull f) :=
  continuous_pi fun e => continuous_apply (eventMap f e)

theorem continuous_chartCoord (a : Ch K) : Continuous (chartCoord a) :=
  continuous_induced_dom

/-- `evPull` undoes the reindexing of `chartIncl`: `c`'s chart is `b`'s chart pulled back. -/
theorem evPull_chartCoord {c b : Ch K} (f : c ⟶ b) (p : Chart c) :
    evPull f (chartCoord b (chartIncl f p)) = chartCoord c p := by
  funext e
  change chartCoord b (chartIncl f p) (eventMap f e) = chartCoord c p e
  rw [chartCoord_chartIncl]
  exact congrArg (chartCoord c p) ((eventEquiv f).symm_apply_apply e)

/-- The image of `chartIncl f` is cut out of `b`'s chart by `c`'s cone: a chart point of `b` comes
from `c` iff its timing, read in `c`'s events, honours `c`'s bead order.  Both halves of `IsAtlas`
are used — the range at `c` (to produce the point) and injectivity at `b` (to identify it). -/
theorem range_chartIncl (h : IsAtlas K) {c b : Ch K} (f : c ⟶ b) :
    Set.range (chartIncl f) = (fun p => evPull f (chartCoord b p)) ⁻¹' schedCone c := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change evPull f (chartCoord b (chartIncl f q)) ∈ schedCone c
    rw [evPull_chartCoord]
    exact chartCoord_mem_cone c q
  · intro hp
    have hr : evPull f (chartCoord b p) ∈ Set.range (chartCoord c) := by
      rw [(h c).2]; exact hp
    obtain ⟨q, hq⟩ := hr
    refine ⟨q, (h b).1 ?_⟩
    funext e
    rw [chartCoord_chartIncl, hq]
    change chartCoord b p (eventMap f ((eventEquiv f).symm e)) = chartCoord b p e
    exact congrArg (chartCoord b p) ((eventEquiv f).apply_symm_apply e)

theorem isOpen_range_chartIncl (h : IsAtlas K) {c b : Ch K} (f : c ⟶ b) :
    IsOpen (Set.range (chartIncl f)) := by
  rw [range_chartIncl h f]
  exact (isOpen_schedCone c).preimage ((continuous_evPull f).comp (continuous_chartCoord b))

/-! ## Stars are open -/

/-- Openness in `Sched K` is chartwise, by definition of the final topology. -/
theorem isOpen_sched_iff (S : Set (Sched K)) :
    IsOpen S ↔ ∀ b : Ch K, IsOpen (chartSched b ⁻¹' S) := by
  constructor
  · exact fun hS b => (continuous_chartSched b).isOpen_preimage _ hS
  · exact fun hb => isOpen_coinduced.mpr (isOpen_sigma_iff.mpr fun b => hb b)

/-- In `b`'s chart, `star a` is the union of the images of the charts of the chains refining `a`:
a chart point of `b` names a schedule of `star a` iff its own chain refines `a`, and then it already
lies in the image of that chain's chart. -/
theorem chartSched_preimage_star (a b : Ch K) :
    chartSched b ⁻¹' star a
      = ⋃ (c : Ch K) (_ : Nonempty (c ⟶ a)) (f : c ⟶ b), Set.range (chartIncl f) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hp
    obtain ⟨k⟩ := mem_star_iff.mp hp
    refine ⟨p.1, ⟨k⟩, p.2.1, ⟨⟨p.1, 𝟙 p.1, p.2.2⟩, ?_⟩⟩
    change (⟨p.1, 𝟙 p.1 ≫ p.2.1, p.2.2⟩ : Chart b) = p
    rw [Category.id_comp]
    rfl
  · rintro ⟨c, ⟨k⟩, f, ⟨q, rfl⟩⟩
    exact mem_star_iff.mpr ⟨q.2.1 ≫ k⟩

/-- Stars are open: chartwise a star is a union of open sub-cones (`isOpen_range_chartIncl`).
`ChartsFaithful` is *not* needed — the chartwise preimage only sees the chain of a chart point. -/
theorem isOpen_star_of_isAtlas (h : IsAtlas K) (a : Ch K) : IsOpen (star a) := by
  refine (isOpen_sched_iff _).mpr fun b => ?_
  rw [chartSched_preimage_star]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun f =>
    isOpen_range_chartIncl h f

/-- `IsAtlas` is a theorem (`isAtlas`), so the stars are open with no hypothesis at all. -/
theorem isOpen_star (a : Ch K) : IsOpen (star a) :=
  isOpen_star_of_isAtlas (isAtlas K) a

end CubeChains
