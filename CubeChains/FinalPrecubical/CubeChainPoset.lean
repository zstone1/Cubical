import CubeChains.FinalPrecubical.Ev

/-!
# FinalPrecubical/CubeChainPoset — the single-cube equivalence

The **keystone** of the shrunk `Ch(Z)` proof: the cube-chain category of a single
standard cube, `Ch(□ᵐ) = ChainCat.Obj (BPSet.cube m)`, is a **thin** category
equivalent to the **poset of ordered set partitions of `Fin m`** (refinement order).

This file reuses the single-cube owner-rule core built in `Ev.lean`
(`OwnerData`, `chainOwner`, `cornerChain`, `chainFace`, `chainCoordMono`, …) and the
chain↔wedge correspondence of `Chains/Correspondence.lean`.

## What is proved

* **`cube_nonSelfLinked (m) : (BPSet.cube m).NonSelfLinked`** — every standard cube is
  non-self-linked (an independently valuable fact: it upgrades `Slice.lean` for cubes,
  and unlocks `descent_mono`/thinness for `Ch(□ᵐ)`).  Route: the topos `cubeMap`
  application `toStar`-bridges to the concrete iterated-face map `StdCube.app`, whose
  injectivity (`stdApp_injective`) is the read-off of star positions.
* **`cube_chainCat_isThin`/`cube_refineObj_isThin`** — thinness of `Ch(□ᵐ)` and of
  `RefineObj (□ᵐ)`, from `chainCat_hom_subsingleton` + `cube_nonSelfLinked`
  + `cube_admitsAltitude`.
* **`OrderedSetPartition m := Σ a : List ℕ+, OwnerData a m`** — the poset of ordered set
  partitions of `Fin m`.
* **`refineObjEquivOSP m : RefineObj (□ᵐ) ≃ OrderedSetPartition m`** — the object
  bijection (chains in `□ᵐ` ↔ ordered set partitions), the combinatorial heart.
* **`chainObjEquivOSP m : ChainCat.Obj (□ᵐ) ≃ OrderedSetPartition m`** — the same
  bijection transported to `Ch(□ᵐ)` through the object part of `equivWedgeCat`.

**Layer:** FinalPrecubical.  **Imports:** `FinalPrecubical.Ev`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace FinalPrecubical

open BPSet CubeChain PrecubicalSet StdCube

/-! ## Part 1. Standard cubes are non-self-linked

`NonSelfLinked (cube m)` asks that the topos-level cube map `((cube m).cubeMap c).app`
is injective for every cell `c`.  The concrete↔topos bridge `toStar` (= `StdCube.ev`)
turns this into injectivity of the iterated-face map `StdCube.app (toStar c)` — which
holds because a star position of `toStar c` reads back the source coordinate. -/

/-- **Injectivity of the iterated-face map.**  For a fixed sign vector `w : cells m n`,
the map `v ↦ StdCube.app w v` is injective: at the `j`-th free (star) position of `w`,
`app w v` reads off `v`'s value at source coordinate `j` (`app_val`), so `v` is
recovered coordinatewise. -/
theorem stdApp_injective {m n : ℕ} (w : StdCube.cells m n) {k : ℕ} :
    Function.Injective
      (StdCube.app (K := StdCube.stdPre m) w : StdCube.cells n k → StdCube.cells m k) := by
  intro v1 v2 h
  apply Subtype.ext
  funext j
  have hc : StdCube.nones w j ∈ StdCube.noneSet w.val :=
    Finset.orderEmbOfFin_mem _ w.prop j
  have hidx : StdCube.nonesIdx w (StdCube.nones w j) hc = j :=
    (StdCube.nones w).injective (StdCube.nones_nonesIdx w _ hc)
  have e1 := app_val w v1 (StdCube.nones w j)
  have e2 := app_val w v2 (StdCube.nones w j)
  rw [dif_pos hc, hidx] at e1 e2
  have hval : (StdCube.app (K := StdCube.stdPre m) w v1).val (StdCube.nones w j)
      = (StdCube.app (K := StdCube.stdPre m) w v2).val (StdCube.nones w j) := by rw [h]
  rw [e1, e2] at hval
  exact hval

/-- **The `toStar`-bridge for the cube map.**  Reading the `(k)`-cell
`((cube m).cubeMap c).app g` as a sign vector is the iterated-face map of the sign
vectors of `c` and `g`: `toStar` intertwines the topos cube map with `StdCube.app`.
(`yonedaEquiv_symm_app_apply` unfolds the cube map to precomposition `g ≫ c`, then
`ev_comp` + `app_unique` land it in `StdCube.app`.) -/
theorem toStar_cubeMap_app {m n k : ℕ} (c : (cube m).toPsh.cells n)
    (g : (cube n).toPsh.cells k) :
    toStar (((cube m).toPsh.cubeMap c).app (op (Box.ob k)) g)
      = StdCube.app (K := StdCube.stdPre m) (toStar c) (toStar g) := by
  simp only [toStar_eq]
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  change StdCube.ev ((g : Box.ob k ⟶ Box.ob n) ≫ c) = _
  rw [StdCube.ev_comp]
  exact StdCube.app_unique (K := StdCube.stdPre m) c rfl (StdCube.ev g)

/-- **Standard cubes are non-self-linked.**  For every cube cell `c`, the cube map
`((cube m).cubeMap c).app` is injective: bridge to `StdCube.app (toStar c)` via
`toStar_cubeMap_app`, which is injective (`stdApp_injective`); `toStar` itself is
injective, so the original map is too. -/
theorem cube_nonSelfLinked (m : ℕ) : (BPSet.cube m).NonSelfLinked := by
  intro n c k g1 g2 h
  apply toStar_injective
  apply stdApp_injective (toStar c)
  rw [← toStar_cubeMap_app c g1, ← toStar_cubeMap_app c g2, h]

/-! ## Part 2. Thinness of `Ch(□ᵐ)`

With `cube_nonSelfLinked` and `cube_admitsAltitude`, the general thinness lemma
`chainCat_hom_subsingleton` (and its refine-side sibling) apply directly. -/

/-- `Ch(□ᵐ)` is a thin category (a poset). -/
instance cube_chainCat_isThin (m : ℕ) : Quiver.IsThin (ChainCat.Obj (BPSet.cube m)) :=
  fun a b => chainCat_hom_subsingleton (cube_nonSelfLinked m) (cube_admitsAltitude m) a b

/-- `RefineObj (□ᵐ)` is a thin category (a poset). -/
instance cube_refineObj_isThin (m : ℕ) :
    Quiver.IsThin (RefineObj (BPSet.cube m).init (BPSet.cube m).final) :=
  fun x y => refineObj_hom_subsingleton (cube_nonSelfLinked m) (cube_admitsAltitude m) x y

/-! ## Part 3. The object bijection: chains in `□ᵐ` ↔ ordered set partitions

An **ordered set partition of `Fin m`** is a block-dimension sequence `a : List ℕ+`
together with an `OwnerData a m` (an owner assignment `Fin m → Fin a.length` with block
`i` of size `a.get i`).  A directed `init → final` chain in `□ᵐ` classifies exactly such
data: block `i` is the face turning coordinate `c` on, and `chainOwner` records the owner
(`Ev.lean`'s single-cube owner rule).  The reverse is the cumulative-OR corner chain
`cornerChain`. -/

/-- **The poset of ordered set partitions of `Fin m`**: a block-dimension sequence
together with an owner assignment of that shape. -/
def OrderedSetPartition (m : ℕ) : Type := Σ a : List ℕ+, OwnerData a m

/-- **Cube-cell extensionality (sigma form).**  Two cube cells with equal dimension and
equal sign vectors give equal `Σ`-entries — the `toStar`-injective packaging that keeps
the chain↔partition round-trips `HEq`-free. -/
theorem cube_cell_ext {m : ℕ} {n1 n2 : ℕ+} (hn : n1 = n2)
    {x : (BPSet.cube m).toPsh.cells (n1 : ℕ)} {y : (BPSet.cube m).toPsh.cells (n2 : ℕ)}
    (hval : ∀ c, (toStar x).val c = (toStar y).val c) :
    (⟨n1, x⟩ : Σ n : ℕ+, (BPSet.cube m).toPsh.cells (n : ℕ)) = ⟨n2, y⟩ := by
  subst hn
  have hxy : x = y := toStar_injective (Subtype.ext (funext hval))
  rw [hxy]

/-- The coordinates owned by block `j` of a single-cube chain are exactly `j`'s star set
(the fibre of `chainOwner` is `chainStarSet`). -/
theorem chainOwner_filter {m : ℕ}
    (cubes : List (Σ n : ℕ+, (BPSet.cube m).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (BPSet.cube m).init cubes (BPSet.cube m).final) (j : Fin cubes.length) :
    Finset.univ.filter (fun c => chainOwner cubes h c = j) = chainStarSet cubes j := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hoc; rw [← hoc]; exact chainOwner_mem cubes h c
  · intro hmem; exact (chainOwner_unique cubes h hmem).symm

/-- **The owner data read off a chain.**  Block `i` owns exactly the coordinates it turns
on, of which there are `a.get i` (`chainStarSet_card`). -/
noncomputable def chainOwnerData {m : ℕ}
    (x : RefineObj (BPSet.cube m).init (BPSet.cube m).final) : OwnerData (x.cubes.map (·.1)) m where
  owner := fun c => (chainOwner x.cubes x.isChain c).cast (List.length_map ..).symm
  card := fun i => by
    have hlen : (x.cubes.map (·.1)).length = x.cubes.length := by simp
    have h1 : (Finset.univ.filter (fun c => (chainOwner x.cubes x.isChain c).cast
          (List.length_map ..).symm = i)).card = ((x.cubes.get (i.cast hlen)).1 : ℕ) := by
      rw [← chainStarSet_card x.cubes (i.cast hlen),
        ← chainOwner_filter x.cubes x.isChain (i.cast hlen)]
      refine congrArg Finset.card (Finset.filter_congr fun c _ => ?_)
      simp only [Fin.ext_iff, Fin.val_cast]
    rw [h1]
    simp [List.getElem_map, List.get_eq_getElem, Fin.val_cast]

/-- **Forward map (chain ↦ ordered set partition).** -/
noncomputable def chainToOSP {m : ℕ}
    (x : RefineObj (BPSet.cube m).init (BPSet.cube m).final) : OrderedSetPartition m :=
  ⟨x.cubes.map (·.1), chainOwnerData x⟩

/-- **Backward map (ordered set partition ↦ chain).**  The cumulative-OR corner chain of
the owner data (`cornerChain`), which is a directed `init → final` chain
(`cornerChain_isChain`). -/
noncomputable def ospToChain {m : ℕ} (o : OrderedSetPartition m) :
    RefineObj (BPSet.cube m).init (BPSet.cube m).final :=
  ⟨cornerChain o.2, cornerChain_isChain o.2⟩

/-- **Round-trip A (chain → partition → chain = id).**  Rebuilding the corner chain from
the owner data read off a chain `x` recovers `x` on the nose: each cube is pinned by its
sign vector, and `chainFace_eq_owner` (the owner rule) says that vector is exactly the
corner model `cornerFaceVal`. -/
theorem ospToChain_chainToOSP {m : ℕ}
    (x : RefineObj (BPSet.cube m).init (BPSet.cube m).final) :
    ospToChain (chainToOSP x) = x := by
  apply RefineObj.ext'
  show cornerChain (chainOwnerData x) = x.cubes
  apply List.ext_getElem
  · simp [cornerChain]
  · intro n h1 h2
    have hn1 : n < (x.cubes.map (·.1)).length := by
      simpa [cornerChain] using h1
    have hentry : (cornerChain (chainOwnerData x))[n]'h1
        = ⟨(x.cubes.map (·.1)).get ⟨n, hn1⟩, cornerCell (chainOwnerData x) ⟨n, hn1⟩⟩ := by
      simp only [cornerChain, List.getElem_ofFn]
    rw [hentry]
    refine cube_cell_ext (by simp [List.getElem_map, List.get_eq_getElem]) (fun c => ?_)
    have howner : (chainOwnerData x).owner c
        = (chainOwner x.cubes x.isChain c).cast (List.length_map ..).symm := rfl
    have hRHS : (toStar (x.cubes.get ⟨n, h2⟩).2).val c
        = (chainFace x.cubes ⟨n, h2⟩).val c := rfl
    rw [hRHS, chainFace_eq_owner x.cubes x.isChain ⟨n, h2⟩ c]
    simp only [cornerCell, toStar_canonicalMap, cornerFace, howner, cornerFaceVal,
      Fin.ext_iff, Fin.val_cast]

/-- **`OwnerData` heterogeneous extensionality.**  Two owner assignments over
propositionally-equal shapes that agree coordinatewise (in `ℕ`) are `HEq` — the card
field is a `Prop`, so it is irrelevant. -/
theorem ownerData_heq {a1 a2 : List ℕ+} {m : ℕ} (ha : a1 = a2)
    {o1 : OwnerData a1 m} {o2 : OwnerData a2 m}
    (ho : ∀ c, (o1.owner c : ℕ) = (o2.owner c : ℕ)) : HEq o1 o2 := by
  subst ha
  apply heq_of_eq
  cases o1 with | mk owner1 card1 =>
  cases o2 with | mk owner2 card2 =>
  have howner : owner1 = owner2 := funext fun c => Fin.ext (ho c)
  subst howner
  rfl

/-- **Owner recovery.**  The owner read off the cumulative-OR corner chain of `o` is `o`'s
own owner: each corner face `cornerFace o j` is free exactly on the coordinates `j` owns
(`cornerFaceVal_none_iff`), so `chainOwner (cornerChain o) = o.owner`
(via `chainOwner_unique`). -/
theorem chainOwner_cornerChain_val {a : List ℕ+} {m : ℕ} (o : OwnerData a m) (c : Fin m) :
    (chainOwner (cornerChain o) (cornerChain_isChain o) c : ℕ) = (o.owner c : ℕ) := by
  have hlen : a.length = (cornerChain o).length := by simp [cornerChain]
  have hget : (cornerChain o).get ((o.owner c).cast hlen)
      = ⟨a.get (o.owner c), cornerCell o (o.owner c)⟩ := by
    simp only [cornerChain, List.get_ofFn]
    simp
  have hval : (chainFace (cornerChain o) ((o.owner c).cast hlen)).val c = none := by
    show (toStar ((cornerChain o).get ((o.owner c).cast hlen)).2).val c = none
    rw [hget]
    show (toStar (StdCube.canonicalMap (cornerFace o (o.owner c)))).val c = none
    rw [toStar_canonicalMap]
    exact (cornerFaceVal_none_iff o (o.owner c) c).mpr rfl
  have hmem : c ∈ chainStarSet (cornerChain o) ((o.owner c).cast hlen) :=
    StdCube.mem_noneSet.mpr hval
  have huniq := chainOwner_unique (cornerChain o) (cornerChain_isChain o) hmem
  rw [← huniq, Fin.val_cast]

/-- **Round-trip B (partition → chain → partition = id).**  The owner data read off the
corner chain of `o` recovers `o`: the shape by `List.map_ofFn`, the owner by
`chainOwner_cornerChain_val`. -/
theorem chainToOSP_ospToChain {m : ℕ} (o : OrderedSetPartition m) :
    chainToOSP (ospToChain o) = o := by
  obtain ⟨a, od⟩ := o
  have ha : (cornerChain od).map (·.1) = a := by
    simp only [cornerChain, List.map_ofFn]
    exact List.ofFn_get a
  have hheq : HEq (chainOwnerData (ospToChain ⟨a, od⟩)) od :=
    ownerData_heq ha fun c => by
      show ((chainOwner (cornerChain od) (cornerChain_isChain od) c).cast
          (List.length_map ..).symm : ℕ) = (od.owner c : ℕ)
      rw [Fin.val_cast]; exact chainOwner_cornerChain_val od c
  show (⟨(cornerChain od).map (·.1), chainOwnerData (ospToChain ⟨a, od⟩)⟩ : OrderedSetPartition m)
      = ⟨a, od⟩
  exact Sigma.ext ha hheq

/-- **The object bijection.**  Directed `init → final` chains in `□ᵐ` are exactly the
ordered set partitions of `Fin m` (chains ↦ owner data, partitions ↦ corner chain). -/
noncomputable def refineObjEquivOSP (m : ℕ) :
    RefineObj (BPSet.cube m).init (BPSet.cube m).final ≃ OrderedSetPartition m where
  toFun := chainToOSP
  invFun := ospToChain
  left_inv := ospToChain_chainToOSP
  right_inv := chainToOSP_ospToChain

/-! ## Part 4. The categorical equivalence

`equivWedgeCat` (RESULT 1) specialises, via `cube_nonSelfLinked` + `cube_admitsAltitude`,
to a categorical equivalence between the refinement category of `□ᵐ` and `Ch(□ᵐ)`.
Composed with the object bijection `refineObjEquivOSP`, this exhibits `Ch(□ᵐ)` as the
poset of ordered set partitions (both sides thin). -/

/-- **`Ch(□ᵐ) ≌ RefineObj (□ᵐ)`** — `equivWedgeCat` specialised to a single cube. -/
noncomputable def cubeChainRefineEquiv (m : ℕ) :
    RefineObj (BPSet.cube m).init (BPSet.cube m).final ≌ ChainCat.Obj (BPSet.cube m) :=
  equivWedgeCat (cube_nonSelfLinked m) (cube_admitsAltitude m)

/-- The object map `ordered set partition ↦ its chain in `Ch(□ᵐ)`` — the composite of
`ospToChain` with the refinement→chain descent. -/
noncomputable def ospInducedMap (m : ℕ) :
    OrderedSetPartition m → ChainCat.Obj (BPSet.cube m) :=
  fun o => refineToWedgeObj (ospToChain o)

/-- **The poset of ordered set partitions of `Fin m` as a category**: the refinement
order, realised as the category induced on `OrderedSetPartition m` from `Ch(□ᵐ)` along the
object bijection (`InducedCategory`).  Both sides are thin, so this order *is* the
refinement order on partitions. -/
abbrev OSPcat (m : ℕ) : Type :=
  CategoryTheory.InducedCategory (ChainCat.Obj (BPSet.cube m)) (ospInducedMap m)

/-- The induced functor `OSPcat m ⥤ Ch(□ᵐ)` is **essentially surjective**: every chain `a`
is (isomorphic to) the realisation of the partition read off it — `ospToChain` recovers
`wedgeToRefineObj a` (round-trip A), whose descent is `a` up to the `dims`-transport
(`counitObjIso`). -/
instance ospInduced_essSurj (m : ℕ) :
    (CategoryTheory.inducedFunctor (ospInducedMap m)).EssSurj where
  mem_essImage a := ⟨chainToOSP (wedgeToRefineObj a),
    ⟨(eqToIso (congrArg refineToWedgeObj
        (ospToChain_chainToOSP (wedgeToRefineObj a)))).trans
      (CubeChain.counitObjIso (cube_nonSelfLinked m) (cube_admitsAltitude m) a)⟩⟩

/-- The induced functor is an equivalence: fully faithful (`InducedCategory`) + essentially
surjective (`ospInduced_essSurj`). -/
instance ospInduced_isEquivalence (m : ℕ) :
    (CategoryTheory.inducedFunctor (ospInducedMap m)).IsEquivalence where

/-- **The keystone equivalence.**  `Ch(□ᵐ)` is equivalent, as a category, to the poset of
ordered set partitions of `Fin m` under refinement.  The `inducedFunctor` is fully faithful
by construction (`InducedCategory`) and essentially surjective by `ospInduced_essSurj`,
hence an equivalence. -/
noncomputable def cubeChainEquivOSP (m : ℕ) :
    ChainCat.Obj (BPSet.cube m) ≌ OSPcat m :=
  (CategoryTheory.inducedFunctor (ospInducedMap m)).asEquivalence.symm

end FinalPrecubical
