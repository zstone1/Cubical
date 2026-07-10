import CubeChains.FinalBraid.EventNaming
import CubeChains.FinalBraid.SalBraidPartition

/-!
# FinalBraid/EventLocalSystem — functoriality of the event system + the cube base case

This file establishes the **event local system** structure on top of `EventNaming.lean` and proves
the **cube base case** of the global event-naming lemma, `EventFiberInjective (BPSet.cube n)`.

## Contents

1. **Functoriality of `eventMap`** (`eventMap_id`, `eventMap_comp`): the event transition is a
   covariant functor `ChainCat.Obj K → Type` valued in the event sets.  Mirrors
   `linesRestrict_id`/`linesRestrict_comp` in `Lines.lean` (the exact same block data, pushed
   forward instead of pulled back), via the block-factoring helper `eventMap_factor`.

2. **The terminal engine** (`eventFiberInjective_of_terminal`): in a thin `ChainCat.Obj K`, a
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

**Layer:** FinalBraid.  **Imports:** `FinalBraid.EventNaming`, `FinalBraid.SalBraidPartition`.
Not part of the default `CubeChains` target.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace FinalBraid

variable {K : BPSet}

/-! ## 1. Functoriality of `eventMap`

The block-factoring helper `eventMap_factor` is the covariant mirror of `restrict_factor`
(`Lines.lean`): any block factorization `ι_i ≫ φ = yoneda.map g ≫ ι_r` computes `eventMap` through
`g`.  From it, functoriality follows exactly as for `linesRestrict`. -/

/-- **Block-factoring of `eventMap`.**  If `ι_i ≫ φ = yoneda.map g ≫ ι_r`, then the `eventMap`
image `(blockIdx φ i, faceEmb (blockFace φ i) x)` equals `(r, faceEmb g x)`.  Covariant analogue of
`restrict_factor`. -/
theorem eventMap_factor {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : Box.ob ((ad.get i) : ℕ) ⟶ Box.ob ((cd.get r) : ℕ))
    (h : BPSet.serialWedge.ι ad i ≫ φ = yoneda.map g ≫ BPSet.serialWedge.ι cd r)
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
theorem eventMap_id {a : ChainCat.Obj K} (e : EventObj a) : eventMap (𝟙 a) e = e := by
  obtain ⟨i, x⟩ := e
  have h : BPSet.serialWedge.ι a.dims i ≫ (𝟙 ((BPSet.serialWedge a.dims).toPsh))
      = yoneda.map (𝟙 (Box.ob ((a.dims.get i) : ℕ))) ≫ BPSet.serialWedge.ι a.dims i := by
    simp
  refine (eventMap_factor (𝟙 ((BPSet.serialWedge a.dims).toPsh)) i i
      (𝟙 (Box.ob ((a.dims.get i) : ℕ))) h x).trans ?_
  exact congrArg (Sigma.mk i) (faceEmb_id _ x)

/-- **`eventMap` preserves composition.**  `eventMap (f ≫ g) e = eventMap g (eventMap f e)`. -/
theorem eventMap_comp {a b c : ChainCat.Obj K} (f : a ⟶ b) (g : b ⟶ c) (e : EventObj a) :
    eventMap (f ≫ g) e = eventMap g (eventMap f e) := by
  obtain ⟨i, x⟩ := e
  refine (eventMap_factor (f ≫ g).φ.hom i
      (blockIdx g.φ.hom (blockIdx f.φ.hom i))
      (blockFace f.φ.hom i ≫ blockFace g.φ.hom (blockIdx f.φ.hom i))
      (blockFace_spec_comp f.φ.hom g.φ.hom i) x).trans ?_
  exact congrArg (Sigma.mk (blockIdx g.φ.hom (blockIdx f.φ.hom i)))
    (faceEmb_comp (blockFace f.φ.hom i) (blockFace g.φ.hom (blockIdx f.φ.hom i)) x)

/-! ## 2. The terminal engine

If `ChainCat.Obj K` is thin and admits a chain `t` that receives a map from every chain, then the
canonical naming `name a e := eventMap (a ⟶ t) e` is coherent (thinness collapses the triangle) and
fibrewise injective exactly when `eventMap` into `t` is, giving `EventFiberInjective K`. -/

/-- **Terminal ⟹ fibre-injective.**  In a thin `ChainCat.Obj K`, if `t` receives a morphism from
every chain and every `eventMap (· ⟶ t)` is injective, then the canonical event naming does not fold
two events of one chain: `EventFiberInjective K`.

The naming `⟨a, e⟩ ↦ eventMap (a ⟶ t) e : EventObj t` is coherent by `eventMap_comp` together with
the uniqueness of `a ⟶ t` (thinness), and fibrewise injective by hypothesis. -/
theorem eventFiberInjective_of_terminal [Quiver.IsThin (ChainCat.Obj K)]
    (t : ChainCat.Obj K) (hne : ∀ a : ChainCat.Obj K, Nonempty (a ⟶ t))
    (hinj : ∀ (a : ChainCat.Obj K) (f : a ⟶ t), Function.Injective (eventMap f)) :
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

/-- The event set of a chain is finite (a `Σ` of `Fin`s). -/
noncomputable instance eventObjFintype (a : ChainCat.Obj K) : Fintype (EventObj a) := by
  unfold EventObj; infer_instance

/-- **`EventFiberInjective ⟹ eventMap` injective.**  If the canonical event quotient is fibrewise
injective, then for every refinement `f : a ⟶ b` the transition `eventMap f` is injective: it is a
right factor of the injective fibre naming `canonicalName ⟨a, ·⟩` (via `canonicalName_coherent`). -/
theorem eventMap_injective (hfi : EventFiberInjective K) {a b : ChainCat.Obj K} (f : a ⟶ b) :
    Function.Injective (eventMap f) := by
  intro e e' he
  refine hfi a ?_
  change canonicalName (⟨a, e⟩ : Σ a : ChainCat.Obj K, EventObj a) = canonicalName ⟨a, e'⟩
  rw [← canonicalName_coherent f e, ← canonicalName_coherent f e', he]

/-! ## 4. The cube base case (coordinate naming)

For `K = BPSet.cube n`, a chain's bead `i` is a cube cell `beadCell a i`, and an event
`(bead i, direction δ)` names the `□ⁿ`-coordinate `nones (toStar (beadCell a i)) δ ∈ Fin n` that
bead `i` flips in direction `δ`.  This naming is coherent and fibrewise injective. -/

section Cube

variable {n : ℕ}

/-- The **cell of bead `i`** of a chain of `□ⁿ`: the `□^{dims i} ⟶ □ⁿ` face traversed by bead `i`,
read off `a.map` at the `i`-th block inclusion. -/
noncomputable def beadCell (a : ChainCat.Obj (BPSet.cube n)) (i : Fin a.dims.length) :
    (BPSet.cube n).toPsh.cells ((a.dims.get i) : ℕ) :=
  yonedaEquiv (BPSet.serialWedge.ι a.dims i ≫ a.map.hom)

/-- The chain `a` of `□ⁿ` presented as a `RefineObj` (its bead cells read off by `wedgeToCubes`), so
the `SalBraidPartition` block machinery (`blockOf`, its disjointness) applies to it. -/
noncomputable def chainRefineObj (a : ChainCat.Obj (BPSet.cube n)) :
    RefineObj (BPSet.cube n).init (BPSet.cube n).final where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom⟩
  isChain := by
    have h := wedgeToCubes_isCubeChain a.dims a.map.hom
    rwa [a.map.app_init, a.map.app_final] at h

/-- The `k`-th block of `chainRefineObj a` is the `none`-set of that bead's cell — i.e. exactly the
set of `□ⁿ`-coordinates the bead flips. -/
theorem blockOf_chainRefineObj (a : ChainCat.Obj (BPSet.cube n))
    (k : Fin (chainRefineObj a).cubes.length) :
    blockOf (chainRefineObj a) k
      = StdCube.noneSet
          (toStar (beadCell a (Fin.cast (wedgeToCubes_length a.dims a.map.hom) k))).val :=
  congrArg (fun s : (Σ m : ℕ+, (BPSet.cube n).toPsh.cells (m : ℕ)) =>
      StdCube.noneSet (toStar s.2).val)
    (wedgeToCubes_get a.dims a.map.hom k)

/-- **The coordinate naming.**  An event `(bead i, direction δ)` of a chain of `□ⁿ` is named by the
`□ⁿ`-coordinate it flips: `nones (toStar (beadCell a i)) δ ∈ Fin n`. -/
noncomputable def cubeName (a : ChainCat.Obj (BPSet.cube n)) (e : EventObj a) : Fin n :=
  StdCube.nones (toStar (beadCell a e.1)) e.2

/-- **Coherence of the coordinate naming.**  A refinement identifies an event's coordinate with its
image's coordinate: `cubeName b (eventMap f e) = cubeName a e`.  Bead `i`'s cell factors through the
target bead's cell along `blockFace f i`, so `nones_app` matches the two coordinates. -/
theorem cubeName_coherent {a b : ChainCat.Obj (BPSet.cube n)} (f : a ⟶ b) (e : EventObj a) :
    cubeName b (eventMap f e) = cubeName a e := by
  obtain ⟨i, x⟩ := e
  have hw : f.φ.hom ≫ b.map.hom = a.map.hom := congrArg (fun m => m.hom) f.w
  have hmor : BPSet.serialWedge.ι a.dims i ≫ a.map.hom
      = yoneda.map (blockFace f.φ.hom i)
        ≫ (BPSet.serialWedge.ι b.dims (blockIdx f.φ.hom i) ≫ b.map.hom) :=
    calc BPSet.serialWedge.ι a.dims i ≫ a.map.hom
        = BPSet.serialWedge.ι a.dims i ≫ (f.φ.hom ≫ b.map.hom) := by rw [hw]
      _ = (BPSet.serialWedge.ι a.dims i ≫ f.φ.hom) ≫ b.map.hom := (Category.assoc _ _ _).symm
      _ = (yoneda.map (blockFace f.φ.hom i)
            ≫ BPSet.serialWedge.ι b.dims (blockIdx f.φ.hom i)) ≫ b.map.hom :=
          congrArg (· ≫ b.map.hom) (blockFace_spec f.φ.hom i)
      _ = yoneda.map (blockFace f.φ.hom i)
            ≫ (BPSet.serialWedge.ι b.dims (blockIdx f.φ.hom i) ≫ b.map.hom) := Category.assoc _ _ _
  have hcell : beadCell a i
      = (BPSet.cube n).toPsh.map (blockFace f.φ.hom i).op (beadCell b (blockIdx f.φ.hom i)) := by
    change yonedaEquiv (BPSet.serialWedge.ι a.dims i ≫ a.map.hom)
        = (BPSet.cube n).toPsh.map (blockFace f.φ.hom i).op
            (yonedaEquiv (BPSet.serialWedge.ι b.dims (blockIdx f.φ.hom i) ≫ b.map.hom))
    rw [yonedaEquiv_naturality]
    exact congrArg yonedaEquiv hmor
  have hmapop : toStar ((BPSet.cube n).toPsh.map (blockFace f.φ.hom i).op
        (beadCell b (blockIdx f.φ.hom i)))
      = StdCube.app (K := StdCube.stdPre n) (toStar (beadCell b (blockIdx f.φ.hom i)))
          (StdCube.ev (blockFace f.φ.hom i)) := by
    have hh : (BPSet.cube n).toPsh.map (blockFace f.φ.hom i).op (beadCell b (blockIdx f.φ.hom i))
        = ((BPSet.cube n).toPsh.cubeMap (beadCell b (blockIdx f.φ.hom i))).app
            (op (Box.ob ((a.dims.get i) : ℕ))) (blockFace f.φ.hom i) := by
      rw [PrecubicalSet.cubeMap]
      exact (yonedaEquiv_symm_app_apply _ _ _).symm
    rw [hh, toStar_cubeMap_app]; rfl
  change StdCube.nones (toStar (beadCell b (blockIdx f.φ.hom i)))
        (faceEmb (blockFace f.φ.hom i) x)
      = StdCube.nones (toStar (beadCell a i)) x
  rw [hcell, hmapop, nones_app]; rfl

/-- **Fibre-injectivity of the coordinate naming.**  Distinct events of one chain flip distinct
`□ⁿ`-coordinates.  Same bead: `nones` is an order embedding.  Distinct beads: their
flipped-coordinate sets are disjoint blocks (`blockOf` partitions `Fin n`). -/
theorem cubeName_faithful (a : ChainCat.Obj (BPSet.cube n)) :
    Function.Injective (fun e : EventObj a => cubeName a e) := by
  rintro ⟨i, x⟩ ⟨i', x'⟩ heq
  have heq' : StdCube.nones (toStar (beadCell a i)) x
      = StdCube.nones (toStar (beadCell a i')) x' := heq
  have hmem : StdCube.nones (toStar (beadCell a i)) x
      ∈ blockOf (chainRefineObj a) (Fin.cast (wedgeToCubes_length a.dims a.map.hom).symm i) := by
    rw [blockOf_chainRefineObj]
    exact Finset.orderEmbOfFin_mem _ (toStar (beadCell a i)).prop x
  have hmem' : StdCube.nones (toStar (beadCell a i)) x
      ∈ blockOf (chainRefineObj a) (Fin.cast (wedgeToCubes_length a.dims a.map.hom).symm i') := by
    rw [blockOf_chainRefineObj, heq']
    exact Finset.orderEmbOfFin_mem _ (toStar (beadCell a i')).prop x'
  have key : i = i' := by
    have hc := blockOf_unique (chainRefineObj a) hmem hmem'
    have hval : (i : ℕ) = (i' : ℕ) := by simpa using congrArg Fin.val hc
    exact Fin.ext hval
  subst key
  exact congrArg (Sigma.mk i) ((StdCube.nones (toStar (beadCell a i))).injective heq')

/-- **The cube has a globally coherent event naming.**  The coordinate naming realises
`HasGlobalEventNaming (BPSet.cube n)`. -/
theorem cube_hasGlobalEventNaming (n : ℕ) : HasGlobalEventNaming (BPSet.cube n) := by
  refine ⟨Fin n, fun p => cubeName p.1 p.2, ?_, ?_⟩
  · intro a b f e
    exact cubeName_coherent f e
  · intro a
    exact cubeName_faithful a

/-- **The cube base case.**  `EventFiberInjective (BPSet.cube n)` — the canonical event quotient
never folds two events of one chain of `□ⁿ`.  Immediate from `cube_hasGlobalEventNaming` via
`hasGlobalEventNaming_iff`. -/
theorem cube_eventFiberInjective (n : ℕ) : EventFiberInjective (BPSet.cube n) :=
  (hasGlobalEventNaming_iff (BPSet.cube n)).mp (cube_hasGlobalEventNaming n)

/-- The event set of a chain of `□ⁿ` has exactly `n` elements: its bead dimensions sum to `n`
(the chain runs from altitude `0` to altitude `n`), via `cubes_dims_sum`. -/
theorem eventObj_card_cube (a : ChainCat.Obj (BPSet.cube n)) :
    Fintype.card (EventObj a) = n := by
  have e1 : Fintype.card (EventObj a) = ∑ i : Fin a.dims.length, ((a.dims.get i : ℕ)) := by
    rw [show Fintype.card (EventObj a)
          = Fintype.card (Σ i : Fin a.dims.length, Fin ((a.dims.get i : ℕ))) from rfl,
      Fintype.card_sigma]
    simp only [Fintype.card_fin]
  have e2 : ∑ i : Fin a.dims.length, ((a.dims.get i : ℕ))
      = (a.dims.map (fun d : ℕ+ => (d : ℕ))).sum := sum_get_eq_sum_map a.dims (fun d => (d : ℕ))
  have hd : (chainRefineObj a).cubes.map (fun c => c.1) = a.dims :=
    wedgeToCubes_dims a.dims a.map.hom
  have e3 : (chainRefineObj a).cubes.map (fun c => (c.1 : ℕ))
      = a.dims.map (fun d : ℕ+ => (d : ℕ)) := by
    rw [← hd, List.map_map]; rfl
  rw [e1, e2, ← e3]
  exact cubes_dims_sum (chainRefineObj a)

/-- **Bijectivity of `eventMap` on the cube.**  For any refinement `f : a ⟶ b` of chains of `□ⁿ`,
`eventMap f` is a bijection: injective by `eventMap_injective` (using `cube_eventFiberInjective`),
and both event sets have `n` elements (`eventObj_card_cube`), so injective ⟹ bijective. -/
theorem cube_eventMap_bijective {a b : ChainCat.Obj (BPSet.cube n)} (f : a ⟶ b) :
    Function.Bijective (eventMap f) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨eventMap_injective (cube_eventFiberInjective n) f,
    (eventObj_card_cube a).trans (eventObj_card_cube b).symm⟩

end Cube

end FinalBraid
