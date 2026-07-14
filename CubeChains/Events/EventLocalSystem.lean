import CubeChains.Events.EventNaming
import CubeChains.Chains.ChainSkeletal
import CubeChains.Salvetti.SalBraidPartition

/-!
# Events/EventLocalSystem — functoriality of the event system + the cube base case

This file establishes the **event local system** structure on top of `EventNaming.lean` and proves
the **cube base case** of the global event-naming lemma, `EventFiberInjective (□n)`.

## Contents

1. **Functoriality of `eventMap`** (`eventMap_id`, `eventMap_comp`): the event transition is a
   covariant functor `Ch K → Type` valued in the event sets.  Mirrors
   `linesRestrict_id`/`linesRestrict_comp` in `Lines.lean` (the exact same block data, pushed
   forward instead of pulled back), via the block-factoring helper `eventMap_factor`.

2. **The terminal engine** (`eventFiberInjective_of_terminal`): in a thin `Ch K`, a
   chain `t` that every chain maps into (`∀ a, Nonempty (a ⟶ t)`), together with fibrewise
   injectivity of `eventMap` into `t`, forces `EventFiberInjective K`.  The naming is
   `name a e := eventMap (a⟶t) e`; coherence is `eventMap_comp` + hom-uniqueness (thinness),
   fibre-injectivity is the hypothesis.

3. **The cube base case** (`cube_hasGlobalEventNaming`, `cube_eventFiberInjective`): for the
   standard cube `□ⁿ` we use the **coordinate naming** — an event `(bead i, direction δ)` of a
   chain `a` is named by the `□ⁿ`-coordinate `nones (toStar (beadCell a i)) δ : Fin n` it flips.
   Coherence is the `nones_app` face computation (a sub-cube's direction is the same ambient axis);
   fibre-injectivity is the `blockOf` partition of `Fin n` (`SalBraidPartition`) on the chain beads.

4. **Bijectivity of `eventMap`** (`eventMap_injective`, `cube_eventMap_bijective`):
   `EventFiberInjective K` makes every `eventMap f` injective (coherence + fibre-injectivity of the
   canonical name), and for the cube both event sets have `Σ dims = n` elements, so `eventMap f` is
   a bijection.

-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

variable {K : BPSet}

/-! ## 1. Functoriality of `eventMap`

The block-factoring helper `eventMap_factor` is the covariant mirror of `restrict_factor`
(`Lines.lean`): any block factorization `ι_i ≫ φ = yoneda.map g ≫ ι_r` computes `eventMap` through
`g`.  From it, functoriality follows exactly as for `linesRestrict`. -/

/-- **Block-factoring of `eventMap`.**  If `ι_i ≫ φ = yoneda.map g ≫ ι_r`, then the `eventMap`
image `(blockIdx φ i, faceEmb (blockFace φ i) x)` equals `(r, faceEmb g x)`.  Covariant analogue of
`restrict_factor`. -/
theorem eventMap_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i) : ℕ) ⟶ ▫((cd.get r) : ℕ))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r)
    (x : Fin ((ad.get i) : ℕ)) :
    (⟨blockIdx φ i, faceEmb (blockFace φ i) x⟩ : Σ j : Fin cd.length, Fin ((cd.get j) : ℕ))
      = ⟨r, faceEmb g x⟩ := by
  obtain rfl : r = blockIdx φ i := blockIdx_eq_of_factor φ i r g h
  have hg : blockFace φ i = g := by
    apply serialWedge_ι_app_injective cd (blockIdx φ i)
    have hy := congrArg yonedaEquiv ((blockFace_spec φ i).symm.trans h)
    rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at hy
  rw [hg]

/-- **`eventMap` preserves identities.**  `eventMap (𝟙 a) e = e`. -/
theorem eventMap_id {a : Ch K} (e : EventObj a) : eventMap (𝟙 a) e = e := by
  obtain ⟨i, x⟩ := e
  have h : ιᵂ a.dims i ≫ (𝟙 ((⋁a.dims).toPsh))
      = yoneda.map (𝟙 ▫(ChainCat.beadDim a i)) ≫ ιᵂ a.dims i := by
    simp
  refine (eventMap_factor (𝟙 ((⋁a.dims).toPsh)) i i
      (𝟙 ▫(ChainCat.beadDim a i)) h x).trans ?_
  exact congrArg (Sigma.mk i) (faceEmb_id _ x)

/-- **`eventMap` preserves composition.**  `eventMap (f ≫ g) e = eventMap g (eventMap f e)`. -/
theorem eventMap_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) (e : EventObj a) :
    eventMap (f ≫ g) e = eventMap g (eventMap f e) := by
  obtain ⟨i, x⟩ := e
  refine (eventMap_factor (f ≫ g)ᵂ i
      (blockIdx gᵂ (blockIdx fᵂ i))
      (blockFace fᵂ i ≫ blockFace gᵂ (blockIdx fᵂ i))
      (blockFace_spec_comp fᵂ gᵂ i) x).trans ?_
  exact congrArg (Sigma.mk (blockIdx gᵂ (blockIdx fᵂ i)))
    (faceEmb_comp (blockFace fᵂ i) (blockFace gᵂ (blockIdx fᵂ i)) x)

/-! ## 2. The terminal engine

If `Ch K` is thin and admits a chain `t` that receives a map from every chain, then the
canonical naming `name a e := eventMap (a ⟶ t) e` is coherent (thinness collapses the triangle) and
fibrewise injective exactly when `eventMap` into `t` is, giving `EventFiberInjective K`. -/

/-- **Terminal ⟹ fibre-injective.**  In a thin `Ch K`, if `t` receives a morphism from
every chain and every `eventMap (· ⟶ t)` is injective, then the canonical event naming does not fold
two events of one chain: `EventFiberInjective K`.

The naming `⟨a, e⟩ ↦ eventMap (a ⟶ t) e : EventObj t` is coherent by `eventMap_comp` together with
the uniqueness of `a ⟶ t` (thinness), and fibrewise injective by hypothesis. -/
theorem eventFiberInjective_of_terminal [Quiver.IsThin (Ch K)]
    (t : Ch K) (hne : ∀ a : Ch K, Nonempty (a ⟶ t))
    (hinj : ∀ (a : Ch K) (f : a ⟶ t), Function.Injective (eventMap f)) :
    EventFiberInjective K := by
  refine (hasGlobalEventNaming_iff K).mp
    ⟨EventObj t, fun p => eventMap (hne p.1).some p.2, ?_, ?_⟩
  · intro a b f e
    change eventMap (hne b).some (eventMap f e) = eventMap (hne a).some e
    rw [← eventMap_comp]
    have huniq : f ≫ (hne b).some = (hne a).some := Subsingleton.elim _ _
    rw [huniq]
  · intro a
    exact hinj a (hne a).some

/-! ## 3. Injectivity of `eventMap` from fibre-injectivity

`EventFiberInjective K` says the canonical name is fibrewise injective.  Since the name is coherent
(`canonicalName_coherent`), it factors through `eventMap`, forcing every `eventMap f` to be
injective — the general injective half of the bijection statement. -/

/-- The **bead-dimension sum** of a chain: `Σᵢ (a.dims.get i)`, i.e. the number of events. -/
def dimSum (a : Ch K) : ℕ := (a.dims.map (fun d : ℕ+ => (d : ℕ))).sum

/-- The event set of a chain has exactly `dimSum a` elements (a `Σ` of `Fin`s). -/
theorem eventObj_card (a : Ch K) : Fintype.card (EventObj a) = dimSum a := by
  rw [show Fintype.card (EventObj a)
        = Fintype.card (Σ i : ChainCat.Bead a, Fin (ChainCat.beadDim a i)) from rfl,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_get_eq_sum_map a.dims (fun d => (d : ℕ))

/-- Bead dimensions sum to the same total along any refinement — the serial wedge's own altitude
(`serialWedge_dimSum_eq`), so no `AdmitsAltitude`/`NonSelfLinked` on `K`. -/
theorem dimSum_eq_of_hom {a b : Ch K} (f : a ⟶ b) : dimSum a = dimSum b :=
  serialWedge_dimSum_eq f.φ

/-- A refinement does not change the number of events. -/
theorem card_eventObj_eq_of_hom {a b : Ch K} (f : a ⟶ b) :
    Fintype.card (EventObj a) = Fintype.card (EventObj b) := by
  rw [eventObj_card, eventObj_card, dimSum_eq_of_hom f]

/-- **`EventFiberInjective ⟹ eventMap` injective.**  If the canonical event quotient is fibrewise
injective, then for every refinement `f : a ⟶ b` the transition `eventMap f` is injective: it is a
right factor of the injective fibre naming `canonicalName ⟨a, ·⟩` (via `canonicalName_coherent`). -/
theorem eventMap_injective (hfi : EventFiberInjective K) {a b : Ch K} (f : a ⟶ b) :
    Function.Injective (eventMap f) := by
  intro e e' he
  refine hfi a ?_
  change canonicalName (⟨a, e⟩ : Σ a : Ch K, EventObj a) = canonicalName ⟨a, e'⟩
  rw [← canonicalName_coherent f e, ← canonicalName_coherent f e', he]

/-! ## 4. The cube base case (coordinate naming)

For `K = □n`, a chain's bead `i` is a cube cell `beadCell a i`, and an event
`(bead i, direction δ)` names the `□ⁿ`-coordinate `nones (toStar (beadCell a i)) δ ∈ Fin n` that
bead `i` flips in direction `δ`.  This naming is coherent and fibrewise injective. -/

section Cube

variable {n : ℕ}

/-- The **cell of bead `i`** of a chain `a` of `K`: the `□^{dims i} ⟶ K` face traversed by bead `i`,
read off `a.map` at the `i`-th block inclusion. -/
noncomputable def beadCell {K : BPSet} (a : Ch K) (i : ChainCat.Bead a) :
    K.cells (ChainCat.beadDim a i) :=
  yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)

/-- The chain `a` of `□ⁿ` presented as a `RefineObj` (its bead cells read off by `wedgeToCubes`), so
the `SalBraidPartition` block machinery (`blockOf`, its disjointness) applies to it. -/
noncomputable def chainRefineObj (a : Ch (□n)) :
    RefineObj (□n).init (□n).final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- The `k`-th block of `chainRefineObj a` is the `none`-set of that bead's cell — i.e. exactly the
set of `□ⁿ`-coordinates the bead flips. -/
theorem blockOf_chainRefineObj (a : Ch (□n))
    (k : Fin (chainRefineObj a).cubes.length) :
    blockOf (chainRefineObj a) k
      = noneSet
          (toStar (beadCell a (Fin.cast (wedgeToCubes_length a.dims a.map.hom) k))).val :=
  congrArg (fun s : (Σ m : ℕ+, (□n).cells (m : ℕ)) =>
      noneSet (toStar s.2).val)
    (wedgeToCubes_get a.dims a.map.hom k)

/-- **The coordinate naming.**  An event `(bead i, direction δ)` of a chain of `□ⁿ` is named by the
`□ⁿ`-coordinate it flips: `nones (toStar (beadCell a i)) δ ∈ Fin n`. -/
noncomputable def cubeName (a : Ch (□n)) (e : EventObj a) : Fin n :=
  nones (toStar (beadCell a e.1)) e.2

/-- **Coherence of the coordinate naming.**  A refinement identifies an event's coordinate with its
image's coordinate: `cubeName b (eventMap f e) = cubeName a e`.  Bead `i`'s cell factors through the
target bead's cell along `blockFace f i`, so `nones_app` matches the two coordinates. -/
theorem cubeName_coherent {a b : Ch (□n)} (f : a ⟶ b) (e : EventObj a) :
    cubeName b (eventMap f e) = cubeName a e := by
  obtain ⟨i, x⟩ := e
  have hw : fᵂ ≫ b.map.hom = a.map.hom := congrArg (fun m => m.hom) f.w
  have hmor : ιᵂ a.dims i ≫ a.map.hom
      = yoneda.map (blockFace fᵂ i)
        ≫ (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom) :=
    calc ιᵂ a.dims i ≫ a.map.hom
        = ιᵂ a.dims i ≫ (fᵂ ≫ b.map.hom) := by rw [hw]
      _ = (ιᵂ a.dims i ≫ fᵂ) ≫ b.map.hom := (Category.assoc _ _ _).symm
      _ = (yoneda.map (blockFace fᵂ i)
            ≫ ιᵂ b.dims (blockIdx fᵂ i)) ≫ b.map.hom :=
          congrArg (· ≫ b.map.hom) (blockFace_spec fᵂ i)
      _ = yoneda.map (blockFace fᵂ i)
            ≫ (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom) := Category.assoc _ _ _
  have hcell : beadCell a i
      = (□n).toPsh.map (blockFace fᵂ i).op (beadCell b (blockIdx fᵂ i)) := by
    change yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)
        = (□n).toPsh.map (blockFace fᵂ i).op
            (yonedaEquiv (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom))
    rw [yonedaEquiv_naturality]
    exact congrArg yonedaEquiv hmor
  have hmapop : toStar ((□n).toPsh.map (blockFace fᵂ i).op
        (beadCell b (blockIdx fᵂ i)))
      = act (K := stdPre n) (toStar (beadCell b (blockIdx fᵂ i)))
          (ev (blockFace fᵂ i)) := by
    have hh : (□n).toPsh.map (blockFace fᵂ i).op (beadCell b (blockIdx fᵂ i))
        = ((□n).toPsh.cubeMap (beadCell b (blockIdx fᵂ i)))⟪ChainCat.beadDim a i⟫
            (blockFace fᵂ i) := by
      rw [PrecubicalSet.cubeMap]
      exact (yonedaEquiv_symm_app_apply _ _ _).symm
    rw [hh, toStar_cubeMap_app]; rfl
  change nones (toStar (beadCell b (blockIdx fᵂ i)))
        (faceEmb (blockFace fᵂ i) x)
      = nones (toStar (beadCell a i)) x
  rw [hcell, hmapop, nones_app]; rfl

/-- **Fibre-injectivity of the coordinate naming.**  Distinct events of one chain flip distinct
`□ⁿ`-coordinates.  Same bead: `nones` is an order embedding.  Distinct beads: their
flipped-coordinate sets are disjoint blocks (`blockOf` partitions `Fin n`). -/
theorem cubeName_faithful (a : Ch (□n)) :
    Function.Injective (fun e : EventObj a => cubeName a e) := by
  rintro ⟨i, x⟩ ⟨i', x'⟩ heq
  have heq' : nones (toStar (beadCell a i)) x
      = nones (toStar (beadCell a i')) x' := heq
  have hmem : nones (toStar (beadCell a i)) x
      ∈ blockOf (chainRefineObj a) (Fin.cast (wedgeToCubes_length a.dims a.map.hom).symm i) := by
    rw [blockOf_chainRefineObj]
    exact Finset.orderEmbOfFin_mem _ (toStar (beadCell a i)).prop x
  have hmem' : nones (toStar (beadCell a i)) x
      ∈ blockOf (chainRefineObj a) (Fin.cast (wedgeToCubes_length a.dims a.map.hom).symm i') := by
    rw [blockOf_chainRefineObj, heq']
    exact Finset.orderEmbOfFin_mem _ (toStar (beadCell a i')).prop x'
  have key : i = i' := by
    have hc := blockOf_unique (chainRefineObj a) hmem hmem'
    have hval : (i : ℕ) = (i' : ℕ) := by simpa using congrArg Fin.val hc
    exact Fin.ext hval
  subst key
  exact congrArg (Sigma.mk i) ((nones (toStar (beadCell a i))).injective heq')

/-- **The cube has a globally coherent event naming.**  The coordinate naming realises
`HasGlobalEventNaming (□n)`. -/
theorem cube_hasGlobalEventNaming (n : ℕ) : HasGlobalEventNaming (□n) := by
  refine ⟨Fin n, fun p => cubeName p.1 p.2, ?_, ?_⟩
  · intro a b f e
    exact cubeName_coherent f e
  · intro a
    exact cubeName_faithful a

/-- **The cube base case.**  `EventFiberInjective (□n)` — the canonical event quotient
never folds two events of one chain of `□ⁿ`.  Immediate from `cube_hasGlobalEventNaming` via
`hasGlobalEventNaming_iff`. -/
theorem cube_eventFiberInjective (n : ℕ) : EventFiberInjective (□n) :=
  (hasGlobalEventNaming_iff (□n)).mp (cube_hasGlobalEventNaming n)

/-- The event set of a chain of `□ⁿ` has exactly `n` elements: its bead dimensions sum to `n`
(the chain runs from altitude `0` to altitude `n`), via `cubes_dims_sum`. -/
theorem eventObj_card_cube (a : Ch (□n)) :
    Fintype.card (EventObj a) = n := by
  rw [eventObj_card, dimSum]
  have e3 : (chainRefineObj a).cubes.map (fun c => (c.1 : ℕ))
      = a.dims.map (fun d : ℕ+ => (d : ℕ)) := by
    rw [← wedgeToCubes_dims a.dims a.map.hom, List.map_map]; rfl
  rw [← e3]
  exact cubes_dims_sum (chainRefineObj a)

/-- **Bijectivity of `eventMap` on the cube.**  For any refinement `f : a ⟶ b` of chains of `□ⁿ`,
`eventMap f` is a bijection: injective by `eventMap_injective` (using `cube_eventFiberInjective`),
and both event sets have `n` elements (`eventObj_card_cube`), so injective ⟹ bijective. -/
theorem cube_eventMap_bijective {a b : Ch (□n)} (f : a ⟶ b) :
    Function.Bijective (eventMap f) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨eventMap_injective (cube_eventFiberInjective n) f,
    (eventObj_card_cube a).trans (eventObj_card_cube b).symm⟩

end Cube

end CubeChains
