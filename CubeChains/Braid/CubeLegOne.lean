import CubeChains.Braid.SalQuotZ
import CubeChains.Salvetti.FZSurj
import CubeChains.Braid.CubeCovering
import CubeChains.Foundations.QuotientCovering

/-!
# Braid/CubeLegOne — `FZ` is star-bijective

`FZ = braidSalEquiv.functor ⋙ concToZ` is *star*-bijective: every outgoing morphism of `(FZ n).obj a`
lifts uniquely to an outgoing morphism of `a`.  `concToZ` is star-bijective (`CubeCovering`) and
`braidSalEquiv.functor` is star-bijective as a full, faithful, object-bijective functor; the star of
a composite is the composite of stars.

This is the covering-inversion engine for the descent functor `Ψ : ConcCat Zbp ⥤ QuotCat …` and the
categorical `Pₙ ↪ Bₙ` injection built on top of it.
-/

open CategoryTheory OrderQuotient Quiver CubeChain Opposite StdCube

namespace CubeChains

/-! ## A fully faithful, object-bijective functor is star-bijective -/

/-- **Star-bijectivity from full faithfulness + object bijectivity.**  If `F` is full, faithful,
and its object map is a bijection, then `F.star` is a bijection at every vertex: surjectivity is
essential surjectivity + fullness, injectivity is object-injectivity + faithfulness. -/
theorem star_bijective_of_ff_of_objBij {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful]
    (hinj : Function.Injective F.obj) (hsurj : Function.Surjective F.obj) (X : C) :
    Function.Bijective (F.toPrefunctor.star X) := by
  constructor
  · rintro ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ hEq
    simp only [Prefunctor.star_apply] at hEq
    have h1 : F.obj Y₁ = F.obj Y₂ := congrArg Sigma.fst hEq
    obtain rfl := hinj h1
    have h2 : F.map f₁ = F.map f₂ := eq_of_heq (Sigma.ext_iff.mp hEq).2
    obtain rfl := F.map_injective h2
    rfl
  · rintro ⟨Z, g⟩
    obtain ⟨Y, hY⟩ := hsurj Z
    subst hY
    refine ⟨Quiver.Star.mk (F.preimage g), ?_⟩
    rw [Prefunctor.star_apply]
    show Quiver.Star.mk (F.map (F.preimage g)) = Quiver.Star.mk g
    exact congrArg Quiver.Star.mk (F.map_preimage g)

/-- `braidSalEquiv.functor` is injective on objects: an object equality yields an isomorphism
(full + faithful), which in the Salvetti *poset* is an equality. -/
theorem braidSalEquiv_functor_obj_injective (n : ℕ) :
    Function.Injective (braidSalEquiv n).functor.obj := by
  haveI := (braidSalEquiv n).fullyFaithfulFunctor.full
  haveI := (braidSalEquiv n).fullyFaithfulFunctor.faithful
  intro Y₁ Y₂ h
  have iso : Y₁ ≅ Y₂ := (braidSalEquiv n).fullyFaithfulFunctor.preimageIso (eqToIso h)
  exact le_antisymm (leOfHom iso.hom) (leOfHom iso.inv)

/-- `braidSalEquiv.functor` is star-bijective: it is an equivalence (full + faithful),
object-injective (poset), and object-surjective (`braidSalEquiv_obj_surjective`). -/
theorem braidSalEquiv_functor_star_bijective (n : ℕ) (a : Sal (braidCOM n)) :
    Function.Bijective ((braidSalEquiv n).functor.toPrefunctor.star a) := by
  haveI := (braidSalEquiv n).fullyFaithfulFunctor.full
  haveI := (braidSalEquiv n).fullyFaithfulFunctor.faithful
  exact star_bijective_of_ff_of_objBij _ (braidSalEquiv_functor_obj_injective n)
    (braidSalEquiv_obj_surjective n) a

/-! ## Step A — `FZ` is star-bijective

`FZ = braidSalEquiv.functor ⋙ concToZ`, and `Prefunctor.star` of a composite is the composite of
stars; both factors are star-bijective. -/

/-- **`FZ n` is star-bijective.**  Every outgoing morphism of `(FZ n).obj a` lifts uniquely to an
outgoing morphism of `a`. -/
theorem FZ_star_bijective (n : ℕ) (a : Sal (braidCOM n)) :
    Function.Bijective ((FZ n).toPrefunctor.star a) := by
  have hcomp : (FZ n).toPrefunctor
      = (braidSalEquiv n).functor.toPrefunctor ⋙q (concToZ (□n)).toPrefunctor := rfl
  rw [hcomp, Prefunctor.star_comp]
  exact (concToZ_star_bijective _).comp (braidSalEquiv_functor_star_bijective n a)

/-! ## Endgame reduction — `φ_x` injectivity from `coverZ` faithfulness

`FZ.obj` is **not** injective: its fibre over the all-`1`-dim terminal run is a full `Sₙ`-orbit —
every one of the `n!` diagonal tope-cells sequentialises to the *one* terminal execution with
trivial line — so `braidSal_concToZ_fiber` genuinely returns a nontrivial `σ`.  The covering
inversion therefore runs through the `Sₙ`-**quotient** covering `quotCover`, not `FZ` itself.
These lemmas package the two ends of that descent so the remaining obligation is exactly one fact:
`(coverZ n).Faithful`, i.e. the descent `coverZ ⋙ FreeGroupoid.map Ψ = quotCover` for the (still to
be built) `Ψ : ConcCat Zbp ⥤ QuotCat (Sal (braidCOM n)) (Perm (Fin n))`. -/

/-- The `Sₙ`-quotient covering is faithful — "a covering is `π₁`-injective"
(`quotFunctor_freeMap_faithful`) for the free reorientation action. -/
theorem quotCover_faithful (n : ℕ) : (quotCover n).Faithful :=
  quotFunctor_freeMap_faithful

/-- **Cancel the refinement equivalence.**  `coverZ = concCubeEquiv.functor ⋙ map concToZ` and
`concCubeEquiv` is an equivalence, so faithfulness of `coverZ` descends to `map concToZ`
(conjugate by `concCubeEquiv.inverse` and collapse with the counit). -/
theorem concToZ_freeMap_faithful_of_coverZ_faithful (n : ℕ)
    (h : (coverZ n).Faithful) :
    (FreeGroupoid.map (concToZ (□n))).Faithful := by
  haveI := h
  exact Functor.Faithful.of_iso
    (F := (concCubeEquiv n).inverse ⋙ coverZ n)
    ((Functor.associator (concCubeEquiv n).inverse (concCubeEquiv n).functor
          (FreeGroupoid.map (concToZ (□n)))).symm
      ≪≫ Functor.isoWhiskerRight (concCubeEquiv n).counitIso (FreeGroupoid.map (concToZ (□n)))
      ≪≫ Functor.leftUnitor (FreeGroupoid.map (concToZ (□n))))

/-- **`φ_x` injectivity from `coverZ` faithfulness.**  Combines the equivalence cancellation with
`concToZAut_injective_of_faithful`.  The one remaining input `(coverZ n).Faithful` is
`quotCover_faithful` transported across the descent `coverZ ⋙ FreeGroupoid.map Ψ = quotCover`. -/
theorem concToZAut_injective_of_coverZ_faithful (n : ℕ)
    (h : (coverZ n).Faithful) (x : ConcCat (□n)) :
    Function.Injective (concToZAut n x) :=
  concToZAut_injective_of_faithful n
    (concToZ_freeMap_faithful_of_coverZ_faithful n h) x

/-! ## Crux scaffolding — a `ConcCat` morphism is pinned by its wedge map

The wedge-map σ-invariance crux (needed to descend `Ψ`'s `map_comp` past the `Sₙ`-reorientation)
compares two `ConcCat Zbp` morphisms with the same endpoints via their underlying wedge maps.  Same
endpoints (not `HEq`), so the plain extensionality below — not `ConcCat.hom_heq_of_φ`. -/

/-- Two `ConcCat` morphisms between the *same* objects agree once their underlying wedge maps do
(`CategoryOfElements.ext` + `ChainCat.hom_ext'`). -/
theorem ConcCat_hom_ext_of_φ {K : BPSet} {X Y : ConcCat K} {g₁ g₂ : X ⟶ Y}
    (h : ChainCat.Hom.φ g₁.1.unop = ChainCat.Hom.φ g₂.1.unop) : g₁ = g₂ :=
  CategoryOfElements.ext (Lines K) g₁ g₂
    (Quiver.Hom.unop_inj (ChainCat.hom_ext' h))

/-! ## (E) Order rigidity for chambers — the crux core

A `Chamber d` is a strict total order on `Fin d`.  A permutation `π` restricting it to itself is an
order-automorphism of that order, hence the identity.  This is the wedge-invariance crux's real
content: the within-block permutation `π_j` induced by an `Sₙ`-reorientation that fixes a fibre
must be trivial.  The proof mirrors `perm_eq_one_of_braidSign_comp` by reading the order off its
injective `chamberRank`. -/

/-- **Order rigidity (chambers).**  A permutation `π` that pulls a chamber back to itself
(`c.restrict π = c`) is the identity: `π` is an order-automorphism of `c.lt`, so its `chamberRank`
relabelling has the same braid sign, and `perm_eq_one_of_braidSign_comp` finishes. -/
theorem chamber_restrict_perm_eq_one {d : ℕ} (c : Chamber d) {π : Equiv.Perm (Fin d)}
    (h : c.restrict (⇑π) π.injective = c) : π = 1 := by
  have hlt : ∀ a b, c.lt (π a) (π b) ↔ c.lt a b := fun a b => by
    rw [← Chamber.restrict_lt c (⇑π) π.injective, h]
  apply perm_eq_one_of_braidSign_comp (ρ := chamberRank c) (chamberRank_injective c)
  funext e
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  have hπne : π e.1.1 ≠ π e.1.2 := fun hh => hne (π.injective hh)
  simp only [braidSign_apply]
  rw [sign_sub_of_ne (fun hh => hπne (chamberRank_injective c hh)),
      sign_sub_of_ne (fun hh => hne (chamberRank_injective c hh))]
  have hiff : (chamberRank c (π e.1.1) < chamberRank c (π e.1.2))
      ↔ (chamberRank c e.1.1 < chamberRank c e.1.2) := by
    rw [chamberRank_lt_iff, chamberRank_lt_iff]; exact hlt e.1.1 e.1.2
  by_cases hc : chamberRank c e.1.1 < chamberRank c e.1.2
  · rw [if_pos hc, if_pos (hiff.mpr hc)]
  · rw [if_neg hc, if_neg (fun x => hc (hiff.mp x))]

/-- **Order rigidity, injective-map form.**  An injective self-map fixing a chamber
(`c.restrict f = c`) is the identity — build the permutation and apply
`chamber_restrict_perm_eq_one`. -/
theorem chamber_restrict_inj_eq_id {d : ℕ} (c : Chamber d) {f : Fin d → Fin d}
    (hf : Function.Injective f) (h : c.restrict f hf = c) (a : Fin d) : f a = a := by
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩
  have hone : Equiv.ofBijective f hbij = 1 :=
    chamber_restrict_perm_eq_one c (π := Equiv.ofBijective f hbij) h
  calc f a = (Equiv.ofBijective f hbij) a := rfl
    _ = (1 : Equiv.Perm (Fin d)) a := by rw [hone]
    _ = a := rfl

/-! ## (A) Thinness reduction — a wedge map of `braidSalEquiv` is a `refineWedgeMap`

`Ch (□n)` is thin (`cube_chainCat_isThin`), so the wedge map underlying `braidSalEquiv.map f` is
*the* morphism between its endpoints.  Reading those endpoints as `cubeChainRefineEquiv.obj` of
ordered-set-partitions `ya`, `yb` (`braidSalEquiv_functor_obj_read`), it equals — transported by the
object equalities — `cubeChainRefineEquiv.map ρ` for any refinement `ρ : yb ⟶ ya`, whose `φ` is a
`refineWedgeMap` (`WallCrossing.functor_map_φ`).  So `σ`-invariance of the wedge map is reduced to
`σ`-invariance of the induced `refineWedgeMap` data. -/

/-- **(A).**  By thinness of `Ch (□n)`, the wedge map underlying `braidSalEquiv.map f` is the
`cubeChainRefineEquiv`-image of any refinement `ρ : yb ⟶ ya` matching its endpoints (transported). -/
theorem braidSalEquiv_map_φ_thin {n : ℕ} {a b : Sal (braidCOM n)} (f : a ⟶ b)
    {ya yb : RefineObj (□n).init (□n).final} (ρ : yb ⟶ ya)
    (hA : ((braidSalEquiv n).functor.obj a).1.unop = (cubeChainRefineEquiv n).functor.obj ya)
    (hB : ((braidSalEquiv n).functor.obj b).1.unop = (cubeChainRefineEquiv n).functor.obj yb) :
    ChainCat.Hom.φ (((braidSalEquiv n).functor.map f).1.unop)
      = ChainCat.Hom.φ
          (eqToHom hB ≫ (cubeChainRefineEquiv n).functor.map ρ ≫ eqToHom hA.symm) := by
  haveI := cube_chainCat_isThin n
  exact congrArg ChainCat.Hom.φ (Subsingleton.elim _ _)

/-! ## Star-lift inversion for `FZ` — the outgoing-morphism engine of `Ψ`

`FZ n` is star-bijective (`FZ_star_bijective`), so every outgoing terminal morphism of `(FZ n).obj a`
lifts uniquely to an outgoing Salvetti morphism of `a`.  `FZstarInv` is that inverse, with the two
projection lemmas recovering the target object (`_obj`) and the lifted map (`_map_heq`). -/

/-- The unique lift of an outgoing terminal morphism along `FZ n`. -/
noncomputable def FZstarInv (n : ℕ) (a : Sal (braidCOM n)) :
    Quiver.Star ((FZ n).obj a) → Quiver.Star a :=
  (Equiv.ofBijective _ (FZ_star_bijective n a)).symm

/-- The lifted target: `FZ` sends the lift's endpoint back to the given one. -/
theorem FZstarInv_obj (n : ℕ) (a : Sal (braidCOM n)) (E : Quiver.Star ((FZ n).obj a)) :
    (FZ n).obj (FZstarInv n a E).1 = E.1 :=
  congrArg Sigma.fst ((Equiv.ofBijective _ (FZ_star_bijective n a)).apply_symm_apply E)

/-- The lifted map: `FZ` sends the lift's map back to the given one (heterogeneously). -/
theorem FZstarInv_map_heq (n : ℕ) (a : Sal (braidCOM n)) (E : Quiver.Star ((FZ n).obj a)) :
    HEq ((FZ n).map (FZstarInv n a E).2) E.2 :=
  (Sigma.ext_iff.mp ((Equiv.ofBijective _ (FZ_star_bijective n a)).apply_symm_apply E)).2

/-! ## `Ψ`'s object map — image characterization and junk case

`psiObj` (`SalQuotZ`) is `⟦a⟧` on the image of `FZ n` and a fixed junk orbit off it; the image is
exactly the `nEvents = n` stratum (`FZ_essSurj` one way, `nEvents_FZ` the other). -/

/-- A terminal execution lies in the image of `FZ n` exactly on the `n`-event stratum. -/
theorem exists_FZ_preimage_iff (n : ℕ) (y : ConcCat Zbp) :
    (∃ a : Sal (braidCOM n), (FZ n).obj a = y) ↔ nEvents y = n :=
  ⟨fun ⟨_, ha⟩ => ha ▸ nEvents_FZ n _, fun h => FZ_essSurj h⟩

/-- Off the image of `FZ n`, `psiObj` is the fixed junk orbit `⟦defaultCell⟧`. -/
theorem psiObj_junk (n : ℕ) (y : ConcCat Zbp)
    (h : ¬ ∃ a : Sal (braidCOM n), (FZ n).obj a = y) :
    psiObj n y = Quotient.mk'' (defaultCell n) := dif_neg h

/-! ## (D) Rung 1 — a canonical height is determined by its braid sign

`covectorHeight` (and any canonical height `q ↦ (β q : ℤ)` of a surjection `β`) is its own
`denseRank` normal form (`denseRank_natCast_val`), and `denseRank` is a `braidSign` invariant
(`denseRank_eq_of_braidSign_eq`).  So two such heights with the *same* covector are equal: the
pairwise order recorded by `braidSign` pins the actual rank values, closing the "(D) missing
sub-step". -/

/-- The canonical height of a surjection is a `denseRank` fixed point. -/
theorem denseRank_natCast_surj {n k : ℕ} {β : Fin n → Fin k} (hβ : Function.Surjective β) :
    denseRank (fun q => ((β q : ℕ) : ℤ)) = fun q => ((β q : ℕ) : ℤ) :=
  funext fun p => denseRank_natCast_val β hβ p

/-- **Rung 1 (general).**  Two canonical heights of surjections with equal braid sign are equal. -/
theorem canonHeight_determined {n k k' : ℕ} {β : Fin n → Fin k} {β' : Fin n → Fin k'}
    (hβ : Function.Surjective β) (hβ' : Function.Surjective β')
    (h : braidSign (fun q => ((β q : ℕ) : ℤ)) = braidSign (fun q => ((β' q : ℕ) : ℤ))) :
    (fun q => ((β q : ℕ) : ℤ)) = fun q => ((β' q : ℕ) : ℤ) := by
  rw [← denseRank_natCast_surj hβ, ← denseRank_natCast_surj hβ', denseRank_eq_of_braidSign_eq h]

/-- **Rung 1.**  `covectorHeight` is determined by its braid sign: two chains realising the same
face covector have the same covector height (block partition). -/
theorem covectorHeight_determined_by_braidSign {n : ℕ}
    (z z' : RefineObj (□n).init (□n).final)
    (h : braidSign (covectorHeight z) = braidSign (covectorHeight z')) :
    covectorHeight z = covectorHeight z' :=
  canonHeight_determined (blockIndex_surjective z) (blockIndex_surjective z') h

/-! ## Rung 2 — reindexing pulls back the covector height by `σ⁻¹`

If `z'` realises the reoriented covector `reorient σ (braidSign (covectorHeight z))`, then its own
covector height is the `σ⁻¹`-precomposite of `z`'s (`reorient_braidSign` + rung 1).  Applied to the
partitions read off `σ • a` and `a`, this is `blockIdx y_{σa} = blockIdx y_a ∘ σ⁻¹`. -/

/-- **Rung 2.**  Reindexing a Salvetti face by `σ` pulls the realising chain's covector height back
by `σ⁻¹`.  `reorient σ` on the covector becomes `σ⁻¹`-precomposition (`reorient_braidSign`), and
rung 1 upgrades the equal braid signs to equal heights. -/
theorem covectorHeight_reindex {n : ℕ} (z z' : RefineObj (□n).init (□n).final)
    (σ : Equiv.Perm (Fin n))
    (h : braidSign (covectorHeight z') = reorient σ (braidSign (covectorHeight z))) :
    covectorHeight z' = fun i => covectorHeight z (σ⁻¹ i) := by
  rw [reorient_braidSign] at h
  exact canonHeight_determined (β := blockIndex z') (β' := fun i => blockIndex z (σ⁻¹ i))
    (blockIndex_surjective z') ((blockIndex_surjective z).comp (Equiv.surjective σ⁻¹)) h

/-! ## Rung 3 scaffolding — the routing half of `refineWedgeMap_reindex_invariant`

The routing map of `chainRefineOfFaceLE xc yf` is `fun j => blockIndex xc (rep yf j)`, `rep` a chosen
section of `blockIndex yf`.  Under a `σ`-reindex of both `xc` and `yf` (rung 2 at the block level),
this routing is `σ`-invariant on the nose (as `Fin`-values): the block index is constant on `yf`
blocks (`faceLE_eq_of_eq`) and the two sections land in the same block. -/

/-- **Block index reindex (values).**  A `σ`-reindexed covector height pulls the block index back by
`σ⁻¹` — at the level of `Fin`-values (the lengths agree, so this is the usable form). -/
theorem blockIndex_val_reindex {n : ℕ} {z z' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (h : covectorHeight z' = fun i => covectorHeight z (σ⁻¹ i)) (p : Fin n) :
    (blockIndex z' p).val = (blockIndex z (σ⁻¹ p)).val := by
  have hp := congrFun h p
  simp only [covectorHeight] at hp
  exact_mod_cast hp

/-- A chosen section of `blockIndex` (the `rep` used inside `chainRefineOfFaceLE`). -/
noncomputable def blockRep {n : ℕ} (z : RefineObj (□n).init (□n).final) :
    Fin z.cubes.length → Fin n :=
  Function.surjInv (blockIndex_surjective z)

theorem blockIndex_blockRep {n : ℕ} (z : RefineObj (□n).init (□n).final)
    (j : Fin z.cubes.length) : blockIndex z (blockRep z j) = j :=
  Function.surjInv_eq (blockIndex_surjective z) j

/-- The routing of `chainRefineOfFaceLE` is `fun j => blockIndex xc (blockRep yf j)`. -/
theorem chainRefineOfFaceLE_refinement {n : ℕ} (xc yf : RefineObj (□n).init (□n).final)
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf)) :
    (chainRefineOfFaceLE xc yf hle).refinement = fun j => blockIndex xc (blockRep yf j) := rfl

/-- **Routing is `σ`-invariant.**  When `(xc', yf')` is the `σ`-reindex of `(xc, yf)` at the
covector level, the `chainRefineOfFaceLE` routing agrees (as `Fin`-values) on corresponding beads:
the block index is constant on `yf`-blocks and the two sections land in the same `yf`-block. -/
theorem chainRefineOfFaceLE_refinement_reindex {n : ℕ}
    {xc yf xc' yf' : RefineObj (□n).init (□n).final} (σ : Equiv.Perm (Fin n))
    (hxc : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    (hyf : covectorHeight yf' = fun i => covectorHeight yf (σ⁻¹ i))
    (hle : braidSign (covectorHeight xc) ⊑ braidSign (covectorHeight yf))
    (j : Fin yf'.cubes.length) (j0 : Fin yf.cubes.length) (hj : j.val = j0.val) :
    (blockIndex xc' (blockRep yf' j)).val = (blockIndex xc (blockRep yf j0)).val := by
  rw [blockIndex_val_reindex σ hxc (blockRep yf' j)]
  have hyfeq : blockIndex yf (σ⁻¹ (blockRep yf' j)) = blockIndex yf (blockRep yf j0) := by
    apply Fin.ext
    rw [← blockIndex_val_reindex σ hyf (blockRep yf' j)]
    simp only [blockIndex_blockRep]
    exact hj
  rw [faceLE_eq_of_eq hle (σ⁻¹ (blockRep yf' j)) (blockRep yf j0) hyfeq]

/-- **Covector reindex from a reoriented cell.**  A chain realising `σ • a`'s face and a chain
realising `a`'s face have `σ⁻¹`-related covector heights: `σ`'s face reorientation becomes
`σ⁻¹`-precomposition (rung 2).  This is the "same `σ`" content that makes the routing invariant —
it needs only the *face* half of the fiber equality, not the line. -/
theorem covectorHeight_read_reindex {n : ℕ} (a : Sal (braidCOM n)) (σ : Equiv.Perm (Fin n))
    {ya ya' : RefineObj (□n).init (□n).final}
    (hya : a.face = braidSign (covectorHeight ya))
    (hya' : (salReindexObj σ a).face = braidSign (covectorHeight ya')) :
    covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i) := by
  apply covectorHeight_reindex ya ya' σ
  rw [← hya', ← hya]
  rfl

/-! ## Rung 3 inclusion half — bead-cell σ-reindex

Under a `σ`-reindex of the covector height (rung 2), the number of beads is preserved and each
bead's `toStar` cell reindexes on the nose by `σ⁻¹`: `toStar_get_val` shows a bead's sign vector is
a pure function of `blockIndex`, and `blockIndex_val_reindex` moves `blockIndex` by `σ⁻¹`.  This is
the chain-data half of the inclusion invariance (the line/chamber half is the HEq crux below). -/

/-- The image of `blockIndex`'s underlying `ℕ`-values is `range (number of beads)` — the block
index is a surjection onto the beads. -/
theorem image_blockIndex_val_eq_range {n : ℕ} (z : RefineObj (□n).init (□n).final) :
    Finset.image (fun p => (blockIndex z p).val) Finset.univ
      = Finset.range z.cubes.length := by
  apply Finset.ext
  intro k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨p, rfl⟩; exact (blockIndex z p).isLt
  · intro hk
    obtain ⟨p, hp⟩ := blockIndex_surjective z ⟨k, hk⟩
    exact ⟨p, by rw [hp]⟩

/-- **Bead count is `σ`-reindex invariant.**  Reindexing the covector height by `σ⁻¹` permutes the
coordinates within blocks but keeps the block partition, hence the same number of beads. -/
theorem cubes_length_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i)) :
    xc'.cubes.length = xc.cubes.length := by
  have key : Finset.range xc'.cubes.length = Finset.range xc.cubes.length := by
    rw [← image_blockIndex_val_eq_range xc', ← image_blockIndex_val_eq_range xc]
    have h1 : (fun p => (blockIndex xc' p).val)
        = (fun p => (blockIndex xc p).val) ∘ ⇑(σ⁻¹ : Equiv.Perm (Fin n)) := by
      funext p; exact blockIndex_val_reindex σ hcov p
    rw [h1, ← Finset.image_image]
    congr 1
    apply Finset.eq_univ_of_forall
    intro q
    rw [Finset.mem_image]
    exact ⟨σ q, Finset.mem_univ _, by simp⟩
  have := congrArg Finset.card key
  rwa [Finset.card_range, Finset.card_range] at this

/-- **Bead cell σ-reindex.**  On corresponding beads (`j'.val = j.val`), the `σ`-reindexed chain's
bead-`j'` cell is the original bead-`j` cell precomposed with `σ⁻¹`: both are the same pure function
of `blockIndex` (`toStar_get_val`), and `blockIndex` moves by `σ⁻¹` (`blockIndex_val_reindex`). -/
theorem toStar_get_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    (j : Fin xc.cubes.length) (j' : Fin xc'.cubes.length) (hjj : j'.val = j.val) (p : Fin n) :
    (toStar (xc'.cubes.get j').2).val p = (toStar (xc.cubes.get j).2).val (σ⁻¹ p) := by
  rw [toStar_get_val xc' j' p, toStar_get_val xc j (σ⁻¹ p)]
  have hbi : (blockIndex xc' p).val = (blockIndex xc (σ⁻¹ p)).val := blockIndex_val_reindex σ hcov p
  by_cases h : blockIndex xc' p = j'
  · have hxj : blockIndex xc (σ⁻¹ p) = j := by
      apply Fin.ext; rw [← hbi, h]; exact hjj
    rw [if_pos h, if_pos hxj]
  · have hne : blockIndex xc (σ⁻¹ p) ≠ j := by
      intro he; exact h (Fin.ext (by rw [hbi, he]; exact hjj.symm))
    rw [if_neg h, if_neg hne]
    congr 1
    rw [decide_eq_decide, Fin.lt_def, Fin.lt_def, hbi, hjj]

/-- **Block set σ-reindex.**  On corresponding beads, the `σ`-reindexed chain's block is the
`σ`-image of the original block. -/
theorem blockOf_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    (j : Fin xc.cubes.length) (j' : Fin xc'.cubes.length) (hjj : j'.val = j.val) :
    blockOf xc' j' = Finset.image σ (blockOf xc j) := by
  ext p
  rw [Finset.mem_image]
  constructor
  · intro hp
    have hbi := (mem_block_iff xc').mp hp
    refine ⟨σ⁻¹ p, ?_, by simp⟩
    rw [mem_block_iff]
    apply Fin.ext
    rw [← blockIndex_val_reindex σ hcov p, hbi]
    exact hjj
  · rintro ⟨q, hq, rfl⟩
    rw [mem_block_iff]
    apply Fin.ext
    rw [blockIndex_val_reindex σ hcov (σ q)]
    have hqq : (σ⁻¹ : Equiv.Perm (Fin n)) (σ q) = q := by simp
    rw [hqq, (mem_block_iff xc).mp hq]
    exact hjj.symm

/-- **Bead dimension is σ-reindex invariant** (corresponding beads have equal dimension): the block
is `σ`-imaged, and `σ` is injective. -/
theorem beadDim_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    (j : Fin xc.cubes.length) (j' : Fin xc'.cubes.length) (hjj : j'.val = j.val) :
    ((xc'.cubes.get j').1 : ℕ) = ((xc.cubes.get j).1 : ℕ) := by
  have h1 : (blockOf xc' j').card = ((xc'.cubes.get j').1 : ℕ) := (toStar (xc'.cubes.get j').2).prop
  have h2 : (blockOf xc j).card = ((xc.cubes.get j).1 : ℕ) := (toStar (xc.cubes.get j).2).prop
  rw [← h1, ← h2, blockOf_reindex σ hcov j j' hjj,
    Finset.card_image_of_injective _ σ.injective]

/-- `σ⁻¹` carries a `σ`-reindexed block back to the original block. -/
theorem blockOf_reindex_mem {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    (j : Fin xc.cubes.length) (j' : Fin xc'.cubes.length) (hjj : j'.val = j.val)
    {p : Fin n} (hp : p ∈ blockOf xc' j') : σ⁻¹ p ∈ blockOf xc j := by
  rw [blockOf_reindex σ hcov j j' hjj, Finset.mem_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have : (σ⁻¹ : Equiv.Perm (Fin n)) (σ q) = q := by simp
  rwa [this]

/-- **The dimension sequence is σ-reindex invariant.**  Corresponding beads have equal dimension
(`beadDim_reindex`) and the bead count agrees (`cubes_length_reindex`), so the whole dimension list
is unchanged — this is `hdims` for the wedge-map transport. -/
theorem dims_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i)) :
    xc'.cubes.map (·.1) = xc.cubes.map (·.1) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_map]; exact cubes_length_reindex σ hcov
  · intro i h1 h2
    rw [List.length_map] at h1
    rw [List.length_map] at h2
    rw [List.getElem_map, List.getElem_map]
    apply PNat.coe_injective
    exact beadDim_reindex σ hcov ⟨i, h2⟩ ⟨i, h1⟩ rfl

/-! ## Rung 3 inclusion half — the chamber-rigidity core (B1 + B3)

Given the covector reindex (rung 2), the tope relation (rung 2 on the tope), **and** the per-bead
height equality `hval` (the line half, `L_{σa} = L_a` re-expressed on heights), the free-coordinate
enumerations commute with `σ` on the nose: `nones` of the `σ`-reindexed bead is `σ ∘ nones`.  The
within-block permutation `τ` induced by `σ` pulls the height-ordered chamber `chamberOfInj` back to
itself (tope relation for one direction, `hval` for the other), so `chamber_restrict_inj_eq_id`
forces `τ = id`. -/

/-- **`nones` commutes with `σ` on corresponding beads.**  This is `π_i = 1` unfolded: the
within-block coordinate reordering induced by the reindex is trivial once the lines agree. -/
theorem nones_reindex {n : ℕ} {xc xc' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight xc' = fun i => covectorHeight xc (σ⁻¹ i))
    {L : (RefineLines n).obj (op xc)} {L' : (RefineLines n).obj (op xc')}
    (htope : braidSign (heightOf xc' L') = braidSign (fun p => heightOf xc L (σ⁻¹ p)))
    (j : Fin xc.cubes.length) (j' : Fin xc'.cubes.length) (hjj : j'.val = j.val)
    (hval : ∀ a : Fin ((xc.cubes.get j).1 : ℕ),
      heightOf xc' L' (nones (toStar (xc'.cubes.get j').2)
          (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm a))
        = heightOf xc L (nones (toStar (xc.cubes.get j).2) a))
    (a : Fin ((xc.cubes.get j).1 : ℕ)) :
    nones (toStar (xc'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm a)
      = σ (nones (toStar (xc.cubes.get j).2) a) := by
  set hd := beadDim_reindex σ hcov j j' hjj with hdd
  set nx := nones (toStar (xc.cubes.get j).2) with hnx
  set nx' := nones (toStar (xc'.cubes.get j').2) with hnx'
  have hmem : ∀ b : Fin ((xc.cubes.get j).1 : ℕ),
      σ⁻¹ (nx' (Fin.cast hd.symm b)) ∈ blockOf xc j := fun b =>
    blockOf_reindex_mem σ hcov j j' hjj (nones_mem _ _)
  set τRaw : Fin ((xc.cubes.get j).1 : ℕ) → Fin ((xc.cubes.get j).1 : ℕ) :=
    fun b => nonesIdx (toStar (xc.cubes.get j).2) (σ⁻¹ (nx' (Fin.cast hd.symm b))) (hmem b)
    with hτ
  have hnxτ : ∀ b, nx (τRaw b) = σ⁻¹ (nx' (Fin.cast hd.symm b)) := fun b =>
    nones_nonesIdx (toStar (xc.cubes.get j).2) _ (hmem b)
  have hτinj : Function.Injective τRaw := by
    intro b c hbc
    have hh := congrArg nx hbc
    rw [hnxτ, hnxτ] at hh
    exact Fin.cast_injective hd.symm
      (nx'.injective ((σ⁻¹ : Equiv.Perm (Fin n)).injective hh))
  have hhinj : Function.Injective (fun b => heightOf xc L (nx b)) :=
    fun b c hbc => nx.injective (heightOf_injective xc L hbc)
  have hrestrict : (chamberOfInj (fun b => heightOf xc L (nx b)) hhinj).restrict τRaw hτinj
      = chamberOfInj (fun b => heightOf xc L (nx b)) hhinj := by
    apply Chamber.ext
    funext b e
    simp only [Chamber.restrict_lt, chamberOfInj_lt]
    rw [hnxτ b, hnxτ e]
    apply propext
    rw [← hval b, ← hval e]
    exact (lt_iff_of_braidSign_eq htope (nx' (Fin.cast hd.symm b)) (nx' (Fin.cast hd.symm e))).symm
  have hτid := chamber_restrict_inj_eq_id
    (chamberOfInj (fun b => heightOf xc L (nx b)) hhinj) hτinj hrestrict a
  have key := hnxτ a
  rw [hτid] at key
  rw [key]
  simp

/-- Equal terminal executions have `HEq` lines (the chain part changes, so the line — a
`LinesObj` of the chain — is heterogeneous). -/
theorem concToZ_line_heq {n : ℕ} {x y : ConcCat (□n)}
    (h : (concToZ (□n)).obj x = (concToZ (□n)).obj y) :
    HEq ((concToZ (□n)).obj x).line ((concToZ (□n)).obj y).line := by
  rw [h]

/-- `chamberRank` transported across equal dimensions and `HEq` chamber / index. -/
theorem chamberRank_heq {d d' : ℕ} (hdd : d' = d) {c' : Chamber d'} {c : Chamber d}
    (hc : HEq c' c) {i' : Fin d'} {i : Fin d} (hi : HEq i' i) :
    chamberRank c' i' = chamberRank c i := by
  subst hdd; rw [eq_of_heq hc, eq_of_heq hi]

/-- Applying two `HEq` chamber tuples (over equal dimension lists) at `HEq` indices gives
`HEq` chambers — the reverse of `Function.hfunext` for the `LinesObj` `Pi`-type. -/
theorem pi_chamber_apply_heq {D' D : List ℕ+} (hD : D' = D)
    {L' : (i : Fin D'.length) → Chamber ((D'.get i : ℕ))}
    {L : (i : Fin D.length) → Chamber ((D.get i : ℕ))}
    (hL : HEq L' L) {i' : Fin D'.length} {i : Fin D.length} (hi : HEq i' i) :
    HEq (L' i') (L i) := by
  subst hD
  obtain rfl := eq_of_heq hL
  obtain rfl := eq_of_heq hi
  rfl

/-- **(B2) bridge.**  A `HEq` line equality gives the per-bead height equality `hval` fed to
`nones_reindex`: `heightOf_nones` splits both heights into `n·bead + chamberRank`, the bead offsets
agree (`hjj`), and the chamber ranks agree by transporting the line `HEq` to the bead
(`pi_chamber_apply_heq` + `chamberRank_heq`). -/
theorem hval_of_line_heq {n : ℕ} {ya ya' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcov : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i))
    {L : (RefineLines n).obj (op ya)} {L' : (RefineLines n).obj (op ya')}
    (hHEq : HEq L' L)
    (j : Fin ya.cubes.length) (j' : Fin ya'.cubes.length) (hjj : j'.val = j.val)
    (a : Fin ((ya.cubes.get j).1 : ℕ)) :
    heightOf ya' L'
        (nones (toStar (ya'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm a))
      = heightOf ya L (nones (toStar (ya.cubes.get j).2) a) := by
  rw [heightOf_nones ya' L' j' (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm a),
      heightOf_nones ya L j a]
  have hdd : (((cubeChainRefineEquiv n).functor.obj ya').dims.get
        (Fin.cast (dseqLen ya').symm j') : ℕ)
      = (((cubeChainRefineEquiv n).functor.obj ya).dims.get (Fin.cast (dseqLen ya).symm j) : ℕ) := by
    rw [dseqGetNat ya' j', dseqGetNat ya j]; exact beadDim_reindex σ hcov j j' hjj
  have hlen : ((cubeChainRefineEquiv n).functor.obj ya').dims.length
      = ((cubeChainRefineEquiv n).functor.obj ya).dims.length := by
    rw [dseqLen, dseqLen]; exact cubes_length_reindex σ hcov
  have hc : HEq (L' (Fin.cast (dseqLen ya').symm j')) (L (Fin.cast (dseqLen ya).symm j)) := by
    refine pi_chamber_apply_heq (dims_reindex σ hcov) hHEq ?_
    exact (Fin.heq_ext_iff hlen).mpr (by simp only [Fin.coe_cast]; exact hjj)
  have hi_a : HEq
      (Fin.cast (dseqGetNat ya' j').symm (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm a))
      (Fin.cast (dseqGetNat ya j).symm a) :=
    (Fin.heq_ext_iff hdd).mpr (by simp only [Fin.coe_cast])
  congr 1
  · congr 1
    exact_mod_cast hjj
  · exact chamberRank_heq hdd hc hi_a

/-- **(B2) + core, packaged.**  From equal terminal executions `(FZ n).obj (σ • a) = (FZ n).obj a`,
the realising chains of `a` and `σ • a` have `σ⁻¹`-related covectors and their free-coordinate
enumerations commute with `σ` on the nose — the inclusion data of any refinement is therefore
`σ`-invariant. -/
theorem nones_reindex_of_FZ_eq {n : ℕ} (a : Sal (braidCOM n)) (σ : Equiv.Perm (Fin n))
    (hσa : (FZ n).obj (salReindexObj σ a) = (FZ n).obj a) :
    ∃ (ya ya' : RefineObj (□n).init (□n).final)
      (hcov : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i)),
      braidSign (covectorHeight ya) = a.face
      ∧ braidSign (covectorHeight ya') = (salReindexObj σ a).face
      ∧ ∀ (j : Fin ya.cubes.length) (j' : Fin ya'.cubes.length) (hjj : j'.val = j.val)
          (b : Fin ((ya.cubes.get j).1 : ℕ)),
          nones (toStar (ya'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcov j j' hjj).symm b)
            = σ (nones (toStar (ya.cubes.get j).2) b) := by
  obtain ⟨ya, hle_a, hface_a, hobj_a⟩ := braidSalEquiv_functor_obj a
  obtain ⟨ya', hle_σa, hface_σa, hobj_σa⟩ := braidSalEquiv_functor_obj (salReindexObj σ a)
  have hcov : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i) :=
    covectorHeight_read_reindex a σ hface_a.symm hface_σa.symm
  refine ⟨ya, ya', hcov, hface_a, hface_σa, ?_⟩
  intro j j' hjj b
  set L := toLines ya ⟨a.tope, a.2.2.1, hle_a⟩ with hLdef
  set L' := toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩ with hL'def
  have hHEq0 : HEq ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj (salReindexObj σ a))).line
      ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj a)).line := concToZ_line_heq hσa
  have hline_a : HEq (ConcCat.line ((braidSalEquiv n).functor.obj a)) L := by rw [hobj_a]; rfl
  have hline_σa : HEq (ConcCat.line ((braidSalEquiv n).functor.obj (salReindexObj σ a))) L' := by
    rw [hobj_σa]; rfl
  have hHEq : HEq L' L := hline_σa.symm.trans (hHEq0.trans hline_a)
  have hTa : braidSign (heightOf ya L) = a.tope :=
    congrArg Subtype.val (ofLines_toLines ya ⟨a.tope, a.2.2.1, hle_a⟩)
  have hTσa : braidSign (heightOf ya' L') = (salReindexObj σ a).tope :=
    congrArg Subtype.val
      (ofLines_toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩)
  have htope : braidSign (heightOf ya' L') = braidSign (fun p => heightOf ya L (σ⁻¹ p)) := by
    rw [hTσa, ← reorient_braidSign, hTa]; rfl
  exact nones_reindex σ hcov htope j j' hjj
    (fun c => hval_of_line_heq σ hcov hHEq j j' hjj c) b

/-- **(B2) chain half.**  Reindexing preserves the terminal execution's chain: `Zbp` is terminal
(`chZbp_ext`), so the chain is pinned by its dims, and those are `σ`-reindex invariant
(`dims_reindex`) — no line propagation needed.  Leaves only the line HEq for the full `FZ.obj`
equality. -/
theorem FZ_obj_chain_reindex (a : Sal (braidCOM n)) (σ : Equiv.Perm (Fin n)) :
    ((FZ n).obj (salReindexObj σ a)).1.unop = ((FZ n).obj a).1.unop := by
  obtain ⟨ya, _, hface_a, hobj_a⟩ := braidSalEquiv_functor_obj a
  obtain ⟨ya', _, hface_σa, hobj_σa⟩ := braidSalEquiv_functor_obj (salReindexObj σ a)
  have hcov : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i) :=
    covectorHeight_read_reindex a σ hface_a.symm hface_σa.symm
  apply chZbp_ext
  have e1 : ((FZ n).obj (salReindexObj σ a)).1.unop.dims = ya'.cubes.map (·.1) := by
    rw [show ((FZ n).obj (salReindexObj σ a)).1.unop.dims
        = ((braidSalEquiv n).functor.obj (salReindexObj σ a)).1.unop.dims from rfl, hobj_σa]
    rfl
  have e2 : ((FZ n).obj a).1.unop.dims = ya.cubes.map (·.1) := by
    rw [show ((FZ n).obj a).1.unop.dims
        = ((braidSalEquiv n).functor.obj a).1.unop.dims from rfl, hobj_a]
    rfl
  rw [e1, e2, dims_reindex σ hcov]

/-! ## (A) inclusion invariance — the `faceFactor` value core

`inclData = canonicalMap ∘ faceFactor`, whose underlying map is
`t ↦ (toStar yf_j).val (nones (toStar xc_r) t)`.  The coarse-side `nones` reindexes by `σ`
(`nones_reindex_of_FZ_eq`), the fine-side `.val` reindexes by `σ⁻¹` (`toStar_get_reindex`), so the
two cancel and the `faceFactor` value is `σ`-invariant on the nose (up to the bead-dimension cast). -/

/-- **`faceFactor` value σ-invariance.**  The underlying `faceFactor` map of `ρ'.incl` equals that of
`ρ.incl` after the coarse-bead dimension cast: `σ` on the coarse `nones` cancels `σ⁻¹` on the fine
values. -/
theorem faceFactor_val_reindex {n : ℕ} {xc xc' yf yf' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    {r : Fin xc.cubes.length} {r' : Fin xc'.cubes.length}
    {j : Fin yf.cubes.length} {j' : Fin yf'.cubes.length}
    (hdr : ((xc'.cubes.get r').1 : ℕ) = ((xc.cubes.get r).1 : ℕ))
    (hnones : ∀ t : Fin ((xc.cubes.get r).1 : ℕ),
        nones (toStar (xc'.cubes.get r').2) (Fin.cast hdr.symm t)
          = σ (nones (toStar (xc.cubes.get r).2) t))
    (hyval : ∀ p, (toStar (yf'.cubes.get j').2).val p
        = (toStar (yf.cubes.get j).2).val (σ⁻¹ p))
    (t : Fin ((xc.cubes.get r).1 : ℕ)) :
    (toStar (yf'.cubes.get j').2).val (nones (toStar (xc'.cubes.get r').2) (Fin.cast hdr.symm t))
      = (toStar (yf.cubes.get j).2).val (nones (toStar (xc.cubes.get r).2) t) := by
  rw [hyval, hnones t]
  simp

/-! ## (A)-full — the `inclData` box morphism reindexes on the nose

Lifting `faceFactor_val_reindex` (a value equality) to an equality of `Box`-morphisms: `ρ'.incl`
equals `ρ.incl` conjugated by the bead-dimension `eqToHom`s.  `inclData`'s underlying map is
`canonicalMap (faceFactor …)`, so `toStar_injective` reduces the box equality to that value
equality; the `eqToHom` sandwich collapses under `subst` of the dimension casts. -/

/-- `toStar` of the `inclData` box morphism is the `faceFactor` cell: its value at `t` is the
`yf`-bead sign vector read at the `xc`-bead's `t`-th free coordinate. -/
theorem inclData_toStar_val {n : ℕ} (xc yf : RefineObj (□n).init (□n).final)
    (j : Fin yf.cubes.length) (r : Fin xc.cubes.length)
    (hsub : ∀ p, blockIndex yf p = j → blockIndex xc p = r)
    (hlt : ∀ p, blockIndex xc p ≠ r → (blockIndex yf p < j ↔ blockIndex xc p < r))
    (t : Fin ((xc.cubes.get r).1 : ℕ)) :
    (toStar ((inclData xc yf j r hsub hlt).1
        : (□((xc.cubes.get r).1 : ℕ)).cells ((yf.cubes.get j).1 : ℕ))).val t
      = (toStar (yf.cubes.get j).2).val (nones (toStar (xc.cubes.get r).2) t) := by
  show (toStar (canonicalMap (faceFactor (toStar (xc.cubes.get r).2)
      (toStar (yf.cubes.get j).2) _) : (□((xc.cubes.get r).1 : ℕ)).cells _)).val t = _
  rw [toStar_canonicalMap]
  rfl

/-- `toStar` of a box morphism sandwiched by dimension-cast `eqToHom`s: source relabelling is
invisible, target relabelling is a `Fin.cast`. -/
theorem toStar_box_sandwich_val {da db da' db' : ℕ}
    (g : ▫da ⟶ ▫db) (ha : da' = da) (hb : db' = db) (t : Fin db') :
    (toStar ((eqToHom (congrArg Box.ob ha) ≫ g ≫ eqToHom (congrArg Box.ob hb.symm) : ▫da' ⟶ ▫db')
        : (□db').cells da')).val t
      = (toStar (g : (□db).cells da)).val (Fin.cast hb t) := by
  subst ha; subst hb
  simp

/-- **(A)-full.**  The `σ`-reindexed `inclData` box morphism is `inclData` conjugated by the
bead-dimension `eqToHom`s: `toStar_injective` reduces to `faceFactor_val_reindex`. -/
theorem incl_reindex {n : ℕ} {xc xc' yf yf' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    {j : Fin yf.cubes.length} {j' : Fin yf'.cubes.length}
    {r : Fin xc.cubes.length} {r' : Fin xc'.cubes.length}
    (hsub : ∀ p, blockIndex yf p = j → blockIndex xc p = r)
    (hlt : ∀ p, blockIndex xc p ≠ r → (blockIndex yf p < j ↔ blockIndex xc p < r))
    (hsub' : ∀ p, blockIndex yf' p = j' → blockIndex xc' p = r')
    (hlt' : ∀ p, blockIndex xc' p ≠ r' → (blockIndex yf' p < j' ↔ blockIndex xc' p < r'))
    (hdr : ((xc'.cubes.get r').1 : ℕ) = ((xc.cubes.get r).1 : ℕ))
    (hdj : ((yf'.cubes.get j').1 : ℕ) = ((yf.cubes.get j).1 : ℕ))
    (hnones : ∀ t : Fin ((xc.cubes.get r).1 : ℕ),
        nones (toStar (xc'.cubes.get r').2) (Fin.cast hdr.symm t)
          = σ (nones (toStar (xc.cubes.get r).2) t))
    (hyval : ∀ p, (toStar (yf'.cubes.get j').2).val p
        = (toStar (yf.cubes.get j).2).val (σ⁻¹ p)) :
    (inclData xc' yf' j' r' hsub' hlt').1
      = eqToHom (congrArg Box.ob hdj) ≫ (inclData xc yf j r hsub hlt).1
          ≫ eqToHom (congrArg Box.ob hdr.symm) := by
  apply toStar_injective
  apply Subtype.ext
  funext s
  rw [inclData_toStar_val xc' yf' j' r' hsub' hlt' s,
      toStar_box_sandwich_val (inclData xc yf j r hsub hlt).1 hdj hdr s,
      inclData_toStar_val xc yf j r hsub hlt (Fin.cast hdr s)]
  have hcc : (Fin.cast hdr.symm (Fin.cast hdr s)
      : Fin ((xc'.cubes.get r').1 : ℕ)) = s := by apply Fin.ext; simp
  have key := faceFactor_val_reindex σ (r := r) (r' := r') (j := j) (j' := j')
    hdr hnones hyval (Fin.cast hdr s)
  rw [hcc] at key
  exact key

/-! ## (B2) — the reindex propagation `FZ.obj (σ • a) = FZ.obj a → FZ.obj (σ • b) = FZ.obj b`

`FZ.obj` is pinned by its chain (dims, free via `chZbp_ext`) and its line.  The line is a
`chambersOf`, determined by `nones`; a σ that fixes the terminal execution of a coarse cell fixes
it on every finer cell because the fine free-coordinates factor through the coarse ones
(`nones_incl`), the refinement's inclusion data is σ-reindexed (`incl_reindex`), and the routing
matches (`chainRefineOfFaceLE_refinement_reindex`). -/

/-- A serial-wedge inclusion transported along a dimension-list equality is a bead inclusion (at the
`val`-matched bead) conjugated by the box `eqToHom`. -/
theorem wedgeι_eqToHom_toPsh {D D' : List ℕ+} (hD : D' = D) (i : Fin D'.length) (j : Fin D.length)
    (hij : i.val = j.val) :
    BPSet.serialWedge.ι D' i ≫ eqToHom (congrArg (fun L : List ℕ+ => (⋁L).toPsh) hD)
      = eqToHom (show (□((D'.get i : ℕ+) : ℕ)).toPsh = (□((D.get j : ℕ+) : ℕ)).toPsh by
            subst hD; obtain rfl : i = j := Fin.ext hij; rfl)
        ≫ BPSet.serialWedge.ι D j := by
  subst hD; obtain rfl : i = j := Fin.ext hij; simp

/-- **`nones` commutes with `σ`, propagated coarse → fine.**  Given σ-commutation of the free
coordinates on a coarse realising chain (`hnc_a`), it holds on any finer chain: the fine
free-coordinates factor through the coarse ones (`nones_incl`) and the refinement inclusion data is
σ-reindexed (`incl_reindex`). -/
theorem nones_commute_propagate {n : ℕ} {ya ya' yb yb' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcova : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i))
    (hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i))
    (hlea : braidSign (covectorHeight ya) ⊑ braidSign (covectorHeight yb))
    (hlea' : braidSign (covectorHeight ya') ⊑ braidSign (covectorHeight yb'))
    (hnc_a : ∀ (J : Fin ya.cubes.length) (J' : Fin ya'.cubes.length) (hJ : J'.val = J.val)
        (c : Fin ((ya.cubes.get J).1 : ℕ)),
        nones (toStar (ya'.cubes.get J').2) (Fin.cast (beadDim_reindex σ hcova J J' hJ).symm c)
          = σ (nones (toStar (ya.cubes.get J).2) c))
    (j : Fin yb.cubes.length) (j' : Fin yb'.cubes.length) (hj : j'.val = j.val)
    (t : Fin ((yb.cubes.get j).1 : ℕ)) :
    nones (toStar (yb'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcovb j j' hj).symm t)
      = σ (nones (toStar (yb.cubes.get j).2) t) := by
  classical
  set r : Fin ya.cubes.length := blockIndex ya (blockRep yb j) with hr
  set r' : Fin ya'.cubes.length := blockIndex ya' (blockRep yb' j') with hr'
  have hrr : r'.val = r.val :=
    chainRefineOfFaceLE_refinement_reindex σ hcova hcovb hlea j' j hj
  have hsub : ∀ p, blockIndex yb p = j → blockIndex ya p = r := by
    intro p hp
    exact faceLE_eq_of_eq hlea p (blockRep yb j) (by rw [hp, blockIndex_blockRep])
  have hlt : ∀ p, blockIndex ya p ≠ r → (blockIndex yb p < j ↔ blockIndex ya p < r) := by
    intro p hne
    refine ⟨fun hpj => ?_, fun hpj => ?_⟩
    · exact lt_of_le_of_ne (faceLE_le_of_lt hlea p (blockRep yb j)
        (by rw [blockIndex_blockRep]; exact hpj)) hne
    · by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea (blockRep yb j) p
          (by rw [blockIndex_blockRep]; exact hgt)))
  have hsub' : ∀ p, blockIndex yb' p = j' → blockIndex ya' p = r' := by
    intro p hp
    exact faceLE_eq_of_eq hlea' p (blockRep yb' j') (by rw [hp, blockIndex_blockRep])
  have hlt' : ∀ p, blockIndex ya' p ≠ r' → (blockIndex yb' p < j' ↔ blockIndex ya' p < r') := by
    intro p hne
    refine ⟨fun hpj => ?_, fun hpj => ?_⟩
    · exact lt_of_le_of_ne (faceLE_le_of_lt hlea' p (blockRep yb' j')
        (by rw [blockIndex_blockRep]; exact hpj)) hne
    · by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub' p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea' (blockRep yb' j') p
          (by rw [blockIndex_blockRep]; exact hgt)))
  set hdj : ((yb'.cubes.get j').1 : ℕ) = ((yb.cubes.get j).1 : ℕ) :=
    beadDim_reindex σ hcovb j j' hj with hdjdef
  set hdr : ((ya'.cubes.get r').1 : ℕ) = ((ya.cubes.get r).1 : ℕ) :=
    beadDim_reindex σ hcova r r' hrr with hdrdef
  have hincl_j : nones (toStar (yb.cubes.get j).2) t
      = nones (toStar (ya.cubes.get r).2) (faceEmb (inclData ya yb j r hsub hlt).1 t) :=
    nones_incl (chainRefineOfFaceLE ya yb hlea) j t
  have hincl_j' : nones (toStar (yb'.cubes.get j').2) (Fin.cast hdj.symm t)
      = nones (toStar (ya'.cubes.get r').2)
          (faceEmb (inclData ya' yb' j' r' hsub' hlt').1 (Fin.cast hdj.symm t)) :=
    nones_incl (chainRefineOfFaceLE ya' yb' hlea') j' (Fin.cast hdj.symm t)
  have hbox := incl_reindex σ hsub hlt hsub' hlt' hdr hdj
    (fun c => hnc_a r r' hrr c) (fun p => toStar_get_reindex σ hcovb j j' hj p)
  have hcast : (Fin.cast hdj (Fin.cast hdj.symm t) : Fin ((yb.cubes.get j).1 : ℕ)) = t := by
    apply Fin.ext; simp
  have hface : faceEmb (inclData ya' yb' j' r' hsub' hlt').1 (Fin.cast hdj.symm t)
      = Fin.cast hdr.symm (faceEmb (inclData ya yb j r hsub hlt).1 t) := by
    rw [hbox, faceEmb_comp, faceEmb_comp, faceEmb_eqToHom, faceEmb_eqToHom]
    · exact congrArg (fun x => Fin.cast hdr.symm (faceEmb (inclData ya yb j r hsub hlt).1 x)) hcast
    · exact hdj
  rw [hincl_j', hface, hnc_a r r' hrr (faceEmb (inclData ya yb j r hsub hlt).1 t), ← hincl_j]

/-- `chamberOfInj` is `HEq`-invariant under a dimension equality and a `HEq` of the height. -/
theorem chamberOfInj_heq {d d' : ℕ} (hdd : d' = d) {f' : Fin d' → ℤ} {f : Fin d → ℤ}
    (hf' : Function.Injective f') (hf : Function.Injective f) (hff : HEq f' f) :
    HEq (chamberOfInj f' hf') (chamberOfInj f hf) := by
  subst hdd; obtain rfl := eq_of_heq hff; rfl

/-- **`chambersOf` reindex.**  σ-commutation of `nones` upgrades to a `HEq` of the chamber tuples
of a realiser and its `σ⁻¹`-precomposite. -/
theorem chambersOf_reindex_heq {n : ℕ} {yb yb' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i))
    {h : Fin n → ℤ} (hinj : Function.Injective h)
    (hnc : ∀ (j : Fin yb.cubes.length) (j' : Fin yb'.cubes.length) (hj : j'.val = j.val)
        (t : Fin ((yb.cubes.get j).1 : ℕ)),
        nones (toStar (yb'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcovb j j' hj).symm t)
          = σ (nones (toStar (yb.cubes.get j).2) t)) :
    HEq (chambersOf yb' (fun i => h (σ⁻¹ i)) (hinj.comp (Equiv.injective (σ⁻¹ : Equiv.Perm (Fin n)))))
        (chambersOf yb h hinj) := by
  have hDeq : ((cubeChainRefineEquiv n).functor.obj yb').dims
      = ((cubeChainRefineEquiv n).functor.obj yb).dims := by
    rw [refineChain_dims, refineChain_dims]; exact dims_reindex σ hcovb
  have hLeq : ((cubeChainRefineEquiv n).functor.obj yb').dims.length
      = ((cubeChainRefineEquiv n).functor.obj yb).dims.length := congrArg List.length hDeq
  apply Function.hfunext
  · exact congrArg Fin hLeq
  · intro j' j hjj
    have hjj' : (j'.cast (dseqLen yb')).val = (j.cast (dseqLen yb)).val := by
      simp only [Fin.coe_cast]
      exact (Fin.heq_ext_iff hLeq).mp hjj
    have hbd : ((yb'.cubes.get (j'.cast (dseqLen yb'))).1 : ℕ)
        = ((yb.cubes.get (j.cast (dseqLen yb))).1 : ℕ) :=
      beadDim_reindex σ hcovb (j.cast (dseqLen yb)) (j'.cast (dseqLen yb')) hjj'
    have hdd : (((cubeChainRefineEquiv n).functor.obj yb').dims.get j' : ℕ)
        = (((cubeChainRefineEquiv n).functor.obj yb).dims.get j : ℕ) :=
      (dseqGetNat yb' (j'.cast (dseqLen yb'))).trans
        (hbd.trans (dseqGetNat yb (j.cast (dseqLen yb))).symm)
    simp only [chambersOf]
    apply chamberOfInj_heq hdd
    apply Function.hfunext
    · exact congrArg Fin hdd
    · intro a' a haa
      have haav : a'.val = a.val := (Fin.heq_ext_iff hdd).mp haa
      set J := j.cast (dseqLen yb) with hJ
      set J' := j'.cast (dseqLen yb') with hJ'
      have hcastarg : (Fin.cast (dseqGetNat yb' J') a' : Fin ((yb'.cubes.get J').1 : ℕ))
          = Fin.cast (beadDim_reindex σ hcovb J J' hjj').symm (Fin.cast (dseqGetNat yb J) a) := by
        apply Fin.ext; simp only [Fin.coe_cast]; exact haav
      have hkey := hnc J J' hjj' (Fin.cast (dseqGetNat yb J) a)
      apply heq_of_eq
      show h (σ⁻¹ (nones (toStar (yb'.cubes.get J').2) (Fin.cast (dseqGetNat yb' J') a')))
          = h (nones (toStar (yb.cubes.get J).2) (Fin.cast (dseqGetNat yb J) a))
      rw [hcastarg, hkey]
      simp

/-- **`toLines` reindex.**  The line of a reoriented tope is the `σ`-reindexed line (`HEq`), given
σ-commutation of `nones`. -/
theorem toLines_reindex_heq {n : ℕ} {yb yb' : RefineObj (□n).init (□n).final}
    (σ : Equiv.Perm (Fin n))
    (hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i))
    (Tb : {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight yb) ⊑ T})
    (Tb' : {T : SignVec (BraidGround n) //
      (braidCOM n).IsTope T ∧ braidSign (covectorHeight yb') ⊑ T})
    (hT : Tb'.1 = reorient σ Tb.1)
    (hnc : ∀ (j : Fin yb.cubes.length) (j' : Fin yb'.cubes.length) (hj : j'.val = j.val)
        (t : Fin ((yb.cubes.get j).1 : ℕ)),
        nones (toStar (yb'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcovb j j' hj).symm t)
          = σ (nones (toStar (yb.cubes.get j).2) t)) :
    HEq (toLines yb' Tb') (toLines yb Tb) := by
  obtain ⟨h, hinj, hbraid⟩ := (braidCOM_isTope_iff_injective Tb.1).mp Tb.2.1
  have hbraid' : Tb'.1 = braidSign (fun i => h (σ⁻¹ i)) := by
    rw [hT, hbraid, reorient_braidSign]
  rw [toLines_eq yb Tb hinj hbraid,
    toLines_eq yb' Tb' (hinj.comp (Equiv.injective (σ⁻¹ : Equiv.Perm (Fin n)))) hbraid']
  exact chambersOf_reindex_heq σ hcovb hinj hnc

/-- **(B2).**  A reorientation fixing a coarse cell's terminal execution fixes it on every finer
cell: chains agree by dims (`chZbp_ext`), lines agree by σ-commutation of `nones`
(`nones_commute_propagate` + `toLines_reindex_heq`). -/
theorem FZ_obj_reindex_propagate {n : ℕ} {a b : Sal (braidCOM n)} (σ : Equiv.Perm (Fin n))
    (hab : a ≤ b) (hfix : (FZ n).obj (salReindexObj σ a) = (FZ n).obj a) :
    (FZ n).obj (salReindexObj σ b) = (FZ n).obj b := by
  obtain ⟨ya, hle_a, hface_a, hobj_a⟩ := braidSalEquiv_functor_obj a
  obtain ⟨ya', hle_σa, hface_σa, hobj_σa⟩ := braidSalEquiv_functor_obj (salReindexObj σ a)
  obtain ⟨yb, hle_b, hface_b, hobj_b⟩ := braidSalEquiv_functor_obj b
  obtain ⟨yb', hle_σb, hface_σb, hobj_σb⟩ := braidSalEquiv_functor_obj (salReindexObj σ b)
  have hcova : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i) :=
    covectorHeight_read_reindex a σ hface_a.symm hface_σa.symm
  have hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i) :=
    covectorHeight_read_reindex b σ hface_b.symm hface_σb.symm
  have hlea : braidSign (covectorHeight ya) ⊑ braidSign (covectorHeight yb) := by
    rw [hface_a, hface_b]; exact (COM.SalCell.le_iff a b).mp hab |>.1
  have hlea' : braidSign (covectorHeight ya') ⊑ braidSign (covectorHeight yb') := by
    rw [hface_σa, hface_σb]
    exact (COM.SalCell.le_iff _ _).mp (salReindexObj_monotone σ hab) |>.1
  have hnc_a : ∀ (J : Fin ya.cubes.length) (J' : Fin ya'.cubes.length) (hJ : J'.val = J.val)
      (c : Fin ((ya.cubes.get J).1 : ℕ)),
      nones (toStar (ya'.cubes.get J').2) (Fin.cast (beadDim_reindex σ hcova J J' hJ).symm c)
        = σ (nones (toStar (ya.cubes.get J).2) c) := by
    intro J J' hJ c
    set L := toLines ya ⟨a.tope, a.2.2.1, hle_a⟩ with hLdef
    set L' := toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩ with hL'def
    have hHEq0 : HEq ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj (salReindexObj σ a))).line
        ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj a)).line := concToZ_line_heq hfix
    have hline_a : HEq (ConcCat.line ((braidSalEquiv n).functor.obj a)) L := by rw [hobj_a]; rfl
    have hline_σa : HEq (ConcCat.line ((braidSalEquiv n).functor.obj (salReindexObj σ a))) L' := by
      rw [hobj_σa]; rfl
    have hHEq : HEq L' L := hline_σa.symm.trans (hHEq0.trans hline_a)
    have hTa : braidSign (heightOf ya L) = a.tope :=
      congrArg Subtype.val (ofLines_toLines ya ⟨a.tope, a.2.2.1, hle_a⟩)
    have hTσa : braidSign (heightOf ya' L') = (salReindexObj σ a).tope :=
      congrArg Subtype.val
        (ofLines_toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩)
    have htope : braidSign (heightOf ya' L') = braidSign (fun p => heightOf ya L (σ⁻¹ p)) := by
      rw [hTσa, ← reorient_braidSign, hTa]; rfl
    exact nones_reindex σ hcova htope J J' hJ
      (fun c => hval_of_line_heq σ hcova hHEq J J' hJ c) c
  have hnc_b : ∀ (j : Fin yb.cubes.length) (j' : Fin yb'.cubes.length) (hj : j'.val = j.val)
      (t : Fin ((yb.cubes.get j).1 : ℕ)),
      nones (toStar (yb'.cubes.get j').2) (Fin.cast (beadDim_reindex σ hcovb j j' hj).symm t)
        = σ (nones (toStar (yb.cubes.get j).2) t) :=
    fun j j' hj t => nones_commute_propagate σ hcova hcovb hlea hlea' hnc_a j j' hj t
  have hlineHEq : HEq (toLines yb' ⟨(salReindexObj σ b).tope, (salReindexObj σ b).2.2.1, hle_σb⟩)
      (toLines yb ⟨b.tope, b.2.2.1, hle_b⟩) :=
    toLines_reindex_heq σ hcovb ⟨b.tope, b.2.2.1, hle_b⟩
      ⟨(salReindexObj σ b).tope, (salReindexObj σ b).2.2.1, hle_σb⟩ rfl hnc_b
  show (concToZ (□n)).obj ((braidSalEquiv n).functor.obj (salReindexObj σ b))
      = (concToZ (□n)).obj ((braidSalEquiv n).functor.obj b)
  rw [hobj_σb, hobj_b]
  refine Sigma.ext ?_ hlineHEq
  refine congrArg op (chZbp_ext ?_)
  show ((cubeChainRefineEquiv n).functor.obj yb').dims
      = ((cubeChainRefineEquiv n).functor.obj yb).dims
  rw [refineChain_dims, refineChain_dims]; exact dims_reindex σ hcovb

/-! ## (B1) — the wedge-map σ-invariance `rwm_reindex`

The wedge map of a `σ`-reindexed refinement equals (transported by the σ-invariant dims) the
original's: block-by-block (`serialWedge_hom_ext`), routing matches
(`chainRefineOfFaceLE_refinement_reindex`), inclusions match (`incl_reindex`).  Box-morphism
equalities go through `toStar_injective` (the codebase idiom), not `eqToHom` collapse. -/

/-- `toStar` of a box morphism sandwiched by two arbitrary box `eqToHom`s. -/
theorem toStar_eqToHom_sandwich {da db da' db' : ℕ} (g : ▫da ⟶ ▫db)
    (h1 : (▫da' : Box) = ▫da) (h2 : (▫db : Box) = ▫db') (t : Fin db') :
    (toStar (eqToHom h1 ≫ g ≫ eqToHom h2 : ▫da' ⟶ ▫db')).val t
      = (toStar g).val (Fin.cast (congrArg Box.dim h2).symm t) := by
  obtain rfl : da = da' := (congrArg Box.dim h1).symm
  obtain rfl : db = db' := congrArg Box.dim h2
  simp

/-- `toStar` of a `gbridge` box morphism reads off its face inclusion (bead-dimension `Fin.cast`). -/
theorem toStar_gbridge_sandwich {n : ℕ} {y x : RefineObj (□n).init (□n).final} (f : y ⟶ x)
    (j : Fin y.cubes.length)
    (s : Fin (((x.cubes.map (·.1)).get (yc (f.refinement j)) : ℕ+) : ℕ)) :
    (toStar (gbridge f j)).val s
      = (toStar (f.incl j)).val (Fin.cast (congrArg (·.val) (dimGet (f.refinement j))) s) := by
  rw [gbridge]
  exact toStar_box_sandwich_val (f.incl j) (congrArg (·.val) (dimGet j))
    (congrArg (·.val) (dimGet (f.refinement j))) s

/-- A serial-wedge `eqToHom` (from a dimension-list equality) fixes the initial vertex. -/
theorem eqToHom_toPsh_init {D D' : List ℕ+} (h : D = D') :
    (eqToHom (congrArg (fun L : List ℕ+ => (⋁L).toPsh) h))⟪0⟫ (⋁D).init = (⋁D').init := by
  subst h; simp

/-- **(B1).**  The wedge map of `braidSalEquiv.map` on a `σ`-reindexed refinement equals, up to the
σ-invariant dimension `eqToHom`s, the wedge map on the original refinement. -/
theorem rwm_reindex {n : ℕ} {ya ya' yb yb' : RefineObj (□n).init (□n).final} (σ : Equiv.Perm (Fin n))
    (hcova : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i))
    (hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i))
    (hlea : braidSign (covectorHeight ya) ⊑ braidSign (covectorHeight yb))
    (hlea' : braidSign (covectorHeight ya') ⊑ braidSign (covectorHeight yb'))
    (hnc_a : ∀ (J : Fin ya.cubes.length) (J' : Fin ya'.cubes.length) (hJ : J'.val = J.val)
        (c : Fin ((ya.cubes.get J).1 : ℕ)),
        nones (toStar (ya'.cubes.get J').2) (Fin.cast (beadDim_reindex σ hcova J J' hJ).symm c)
          = σ (nones (toStar (ya.cubes.get J).2) c)) :
    (rwm (chainRefineOfFaceLE ya' yb' hlea')).hom
      = eqToHom (congrArg (fun L : List ℕ+ => (⋁L).toPsh) (dims_reindex σ hcovb))
        ≫ (rwm (chainRefineOfFaceLE ya yb hlea)).hom
        ≫ eqToHom (congrArg (fun L : List ℕ+ => (⋁L).toPsh) (dims_reindex σ hcova).symm) := by
  refine serialWedge_hom_ext _ _ _ (fun i => ?_) ?_
  · set j' : Fin yb'.cubes.length := i.cast (by rw [List.length_map]) with hj'
    set j0 : Fin yb.cubes.length := j'.cast (cubes_length_reindex σ hcovb) with hj0
    have hjj : j'.val = j0.val := by simp [hj0]
    have hi : i = yc j' := by apply Fin.ext; simp [yc, hj']
    set r : Fin ya.cubes.length := (chainRefineOfFaceLE ya yb hlea).refinement j0 with hr
    set r' : Fin ya'.cubes.length := (chainRefineOfFaceLE ya' yb' hlea').refinement j' with hr'
    have hrr : r'.val = r.val :=
      chainRefineOfFaceLE_refinement_reindex σ hcova hcovb hlea j' j0 hjj
    have hsub : ∀ p, blockIndex yb p = j0 → blockIndex ya p = r := fun p hp =>
      faceLE_eq_of_eq hlea p (blockRep yb j0) (by rw [hp, blockIndex_blockRep])
    have hlt : ∀ p, blockIndex ya p ≠ r → (blockIndex yb p < j0 ↔ blockIndex ya p < r) := by
      intro p hne
      refine ⟨fun hpj => lt_of_le_of_ne (faceLE_le_of_lt hlea p (blockRep yb j0)
          (by rw [blockIndex_blockRep]; exact hpj)) hne, fun hpj => ?_⟩
      by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea (blockRep yb j0) p
          (by rw [blockIndex_blockRep]; exact hgt)))
    have hsub' : ∀ p, blockIndex yb' p = j' → blockIndex ya' p = r' := fun p hp =>
      faceLE_eq_of_eq hlea' p (blockRep yb' j') (by rw [hp, blockIndex_blockRep])
    have hlt' : ∀ p, blockIndex ya' p ≠ r' → (blockIndex yb' p < j' ↔ blockIndex ya' p < r') := by
      intro p hne
      refine ⟨fun hpj => lt_of_le_of_ne (faceLE_le_of_lt hlea' p (blockRep yb' j')
          (by rw [blockIndex_blockRep]; exact hpj)) hne, fun hpj => ?_⟩
      by_contra hnn
      rw [not_lt] at hnn
      rcases eq_or_lt_of_le hnn with heq | hgt
      · exact hne (hsub' p heq.symm)
      · exact absurd hpj (not_lt.mpr (faceLE_le_of_lt hlea' (blockRep yb' j') p
          (by rw [blockIndex_blockRep]; exact hgt)))
    have hdj : ((yb'.cubes.get j').1 : ℕ) = ((yb.cubes.get j0).1 : ℕ) :=
      beadDim_reindex σ hcovb j0 j' hjj
    have hdr : ((ya'.cubes.get r').1 : ℕ) = ((ya.cubes.get r).1 : ℕ) :=
      beadDim_reindex σ hcova r r' hrr
    have hincl_eq : (chainRefineOfFaceLE ya' yb' hlea').incl j'
        = eqToHom (congrArg Box.ob hdj) ≫ (chainRefineOfFaceLE ya yb hlea).incl j0
          ≫ eqToHom (congrArg Box.ob hdr.symm) :=
      incl_reindex σ hsub hlt hsub' hlt' hdr hdj (fun c => hnc_a r r' hrr c)
        (fun p => toStar_get_reindex σ hcovb j0 j' hjj p)
    have bA := congrArg Box.ob
      ((congrArg (fun p : ℕ+ => (p : ℕ)) (dimGet j')).trans
        (hdj.trans (congrArg (fun p : ℕ+ => (p : ℕ)) (dimGet j0)).symm))
    have bB := congrArg Box.ob
      ((congrArg (fun p : ℕ+ => (p : ℕ))
          (dimGet ((chainRefineOfFaceLE ya yb hlea).refinement j0))).trans
        (hdr.symm.trans (congrArg (fun p : ℕ+ => (p : ℕ))
          (dimGet ((chainRefineOfFaceLE ya' yb' hlea').refinement j'))).symm))
    have hgb : gbridge (chainRefineOfFaceLE ya' yb' hlea') j'
        = eqToHom bA ≫ gbridge (chainRefineOfFaceLE ya yb hlea) j0 ≫ eqToHom bB := by
      apply toStar_injective
      apply Subtype.ext
      funext s
      rw [toStar_gbridge_sandwich, hincl_eq,
        toStar_box_sandwich_val ((chainRefineOfFaceLE ya yb hlea).incl j0) hdj hdr,
        toStar_eqToHom_sandwich (gbridge (chainRefineOfFaceLE ya yb hlea) j0),
        toStar_gbridge_sandwich]
      congr 1
    have hbf := refineWedgeMap_block_factor (chainRefineOfFaceLE ya yb hlea) j0
    have hw1 := wedgeι_eqToHom_toPsh (dims_reindex σ hcovb) (yc j') (yc j0) (by simp [yc, hjj])
    have hw2 := wedgeι_eqToHom_toPsh (dims_reindex σ hcova).symm
      (yc ((chainRefineOfFaceLE ya yb hlea).refinement j0))
      (yc ((chainRefineOfFaceLE ya' yb' hlea').refinement j'))
      (by show (yc r).val = (yc r').val; simp only [yc, Fin.coe_cast]; exact hrr.symm)
    rw [hi, refineWedgeMap_block_factor (chainRefineOfFaceLE ya' yb' hlea') j',
      ← Category.assoc, hw1, Category.assoc,
      ← Category.assoc (BPSet.serialWedge.ι (yb.cubes.map (·.1)) (yc j0)), hbf]
    erw [Category.assoc, hw2, hgb]
    simp only [Functor.map_comp, eqToHom_map]
    rfl
  · rw [NatTrans.comp_app, NatTrans.comp_app, types_comp_apply, types_comp_apply,
      eqToHom_toPsh_init (dims_reindex σ hcovb),
      (rwm (chainRefineOfFaceLE ya yb hlea)).app_init,
      eqToHom_toPsh_init (dims_reindex σ hcova).symm,
      (rwm (chainRefineOfFaceLE ya' yb' hlea')).app_init]

/-! ## The wedge-map σ-invariance of `FZ.map`, as a `HEq`

`rwm_reindex` (a `.hom` equality of wedge maps) upgrades to the statement `FZ.map ((salReindex σ).map
f) ≍ FZ.map f`: read both `FZ.map`s off their wedge maps (`braidSalEquiv_map_φ_thin`, `pushforward`),
match them via `rwm_reindex`, and re-assemble with the `ConcCat` heterogeneous extensionality. -/

/-- Generic HEq congruence for a two-step composite. -/
theorem comp_heq_comp {C : Type*} [Category C] {a b c a' b' c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {f : a ⟶ b} {f' : a' ⟶ b'} {g : b ⟶ c} {g' : b' ⟶ c'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst ha; subst hb; subst hc
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

/-- Two `ConcCat` morphisms with possibly-different but equal endpoints agree once their wedge maps
`HEq`-agree. -/
theorem ConcCat.hom_heq_of_φ' {K : BPSet} {x₁ y₁ x₂ y₂ : ConcCat K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {g₁ : x₁ ⟶ y₁} {g₂ : x₂ ⟶ y₂}
    (hφ : HEq (ChainCat.Hom.φ g₁.val.unop) (ChainCat.Hom.φ g₂.val.unop)) : HEq g₁ g₂ := by
  subst hx; subst hy; exact ConcCat.hom_heq_of_φ rfl hφ

/-- `ChainCat.Hom.φ` of an `eqToHom` reads off as the wedge transport of its dimension sequences. -/
theorem chain_eqToHom_φ {K : BPSet} {X Y : Ch K} (p : X = Y) :
    ChainCat.Hom.φ (eqToHom p) = eqToHom (congrArg (fun c : Ch K => ⋁c.dims) p) := by
  subst p; rfl

/-- `eqToHom` in `BPSet` reads off as `eqToHom` on underlying presheaves. -/
theorem bpset_eqToHom_hom {K L : BPSet} (h : K = L) :
    (eqToHom h : K ⟶ L).hom = eqToHom (congrArg BPSet.toPsh h) := by
  subst h; rfl

/-- **(B1) as a `HEq`.**  Reindexing a Salvetti morphism by `σ` leaves the `FZ`-image morphism
heterogeneously unchanged, given that `σ` fixes the source's terminal execution (`hfa`). -/
theorem FZ_map_salReindex_heq {n : ℕ} {a b : Sal (braidCOM n)} (σ : Equiv.Perm (Fin n))
    (f : a ⟶ b) (hfa : (FZ n).obj (salReindexObj σ a) = (FZ n).obj a) :
    HEq ((FZ n).map ((salReindex σ).map f)) ((FZ n).map f) := by
  have hab : a ≤ b := leOfHom f
  have hfb : (FZ n).obj (salReindexObj σ b) = (FZ n).obj b :=
    FZ_obj_reindex_propagate σ hab hfa
  refine ConcCat.hom_heq_of_φ' hfa hfb ?_
  obtain ⟨ya, hle_a, hface_a, hobj_a⟩ := braidSalEquiv_functor_obj a
  obtain ⟨yb, hle_b, hface_b, hobj_b⟩ := braidSalEquiv_functor_obj b
  obtain ⟨ya', hle_σa, hface_σa, hobj_σa⟩ := braidSalEquiv_functor_obj (salReindexObj σ a)
  obtain ⟨yb', hle_σb, hface_σb, hobj_σb⟩ := braidSalEquiv_functor_obj (salReindexObj σ b)
  have hcova : covectorHeight ya' = fun i => covectorHeight ya (σ⁻¹ i) :=
    covectorHeight_read_reindex a σ hface_a.symm hface_σa.symm
  have hcovb : covectorHeight yb' = fun i => covectorHeight yb (σ⁻¹ i) :=
    covectorHeight_read_reindex b σ hface_b.symm hface_σb.symm
  have hlea : braidSign (covectorHeight ya) ⊑ braidSign (covectorHeight yb) := by
    rw [hface_a, hface_b]; exact ((COM.SalCell.le_iff a b).mp hab).1
  have hlea' : braidSign (covectorHeight ya') ⊑ braidSign (covectorHeight yb') := by
    rw [hface_σa, hface_σb]
    exact ((COM.SalCell.le_iff _ _).mp (salReindexObj_monotone σ hab)).1
  have hnc_a : ∀ (J : Fin ya.cubes.length) (J' : Fin ya'.cubes.length) (hJ : J'.val = J.val)
      (c : Fin ((ya.cubes.get J).1 : ℕ)),
      nones (toStar (ya'.cubes.get J').2) (Fin.cast (beadDim_reindex σ hcova J J' hJ).symm c)
        = σ (nones (toStar (ya.cubes.get J).2) c) := by
    intro J J' hJ c
    set L := toLines ya ⟨a.tope, a.2.2.1, hle_a⟩ with hLdef
    set L' := toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩ with hL'def
    have hHEq0 : HEq ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj (salReindexObj σ a))).line
        ((concToZ (□n)).obj ((braidSalEquiv n).functor.obj a)).line := concToZ_line_heq hfa
    have hline_a : HEq (ConcCat.line ((braidSalEquiv n).functor.obj a)) L := by rw [hobj_a]; rfl
    have hline_σa : HEq (ConcCat.line ((braidSalEquiv n).functor.obj (salReindexObj σ a))) L' := by
      rw [hobj_σa]; rfl
    have hHEq : HEq L' L := hline_σa.symm.trans (hHEq0.trans hline_a)
    have hTa : braidSign (heightOf ya L) = a.tope :=
      congrArg Subtype.val (ofLines_toLines ya ⟨a.tope, a.2.2.1, hle_a⟩)
    have hTσa : braidSign (heightOf ya' L') = (salReindexObj σ a).tope :=
      congrArg Subtype.val
        (ofLines_toLines ya' ⟨(salReindexObj σ a).tope, (salReindexObj σ a).2.2.1, hle_σa⟩)
    have htope : braidSign (heightOf ya' L') = braidSign (fun p => heightOf ya L (σ⁻¹ p)) := by
      rw [hTσa, ← reorient_braidSign, hTa]; rfl
    exact nones_reindex σ hcova htope J J' hJ
      (fun c => hval_of_line_heq σ hcova hHEq J J' hJ c) c
  have hA : ((braidSalEquiv n).functor.obj a).1.unop = (cubeChainRefineEquiv n).functor.obj ya :=
    congrArg (fun w : ConcCat (□n) => w.1.unop) hobj_a
  have hB : ((braidSalEquiv n).functor.obj b).1.unop = (cubeChainRefineEquiv n).functor.obj yb :=
    congrArg (fun w : ConcCat (□n) => w.1.unop) hobj_b
  have hA' : ((braidSalEquiv n).functor.obj (salReindexObj σ a)).1.unop
      = (cubeChainRefineEquiv n).functor.obj ya' :=
    congrArg (fun w : ConcCat (□n) => w.1.unop) hobj_σa
  have hB' : ((braidSalEquiv n).functor.obj (salReindexObj σ b)).1.unop
      = (cubeChainRefineEquiv n).functor.obj yb' :=
    congrArg (fun w : ConcCat (□n) => w.1.unop) hobj_σb
  -- read both wedge maps off refinements
  change HEq (ChainCat.Hom.φ ((braidSalEquiv n).functor.map ((salReindex σ).map f)).val.unop)
             (ChainCat.Hom.φ ((braidSalEquiv n).functor.map f).val.unop)
  rw [braidSalEquiv_map_φ_thin ((salReindex σ).map f)
        (chainRefineOfFaceLE ya' yb' hlea') hA' hB',
      braidSalEquiv_map_φ_thin f (chainRefineOfFaceLE ya yb hlea) hA hB,
      ChainCat.comp_φ, ChainCat.comp_φ, ChainCat.comp_φ, ChainCat.comp_φ,
      chain_eqToHom_φ, chain_eqToHom_φ, chain_eqToHom_φ,
      chain_eqToHom_φ, functor_map_φ, functor_map_φ]
  -- goal: HEq of two `eqToHom ≫ rwm ≫ eqToHom` composites in `BPSet`
  have hdimsB : ((braidSalEquiv n).functor.obj ((salReindex σ).obj b)).1.unop.dims
      = ((braidSalEquiv n).functor.obj b).1.unop.dims := by
    show ((braidSalEquiv n).functor.obj (salReindexObj σ b)).1.unop.dims = _
    rw [hB', hB, refineChain_dims, refineChain_dims]; exact dims_reindex σ hcovb
  have hdimsA : ((braidSalEquiv n).functor.obj ((salReindex σ).obj a)).1.unop.dims
      = ((braidSalEquiv n).functor.obj a).1.unop.dims := by
    show ((braidSalEquiv n).functor.obj (salReindexObj σ a)).1.unop.dims = _
    rw [hA', hA, refineChain_dims, refineChain_dims]; exact dims_reindex σ hcova
  have hrwm : rwm (chainRefineOfFaceLE ya' yb' hlea')
      = eqToHom (congrArg BPSet.serialWedge (dims_reindex σ hcovb))
        ≫ rwm (chainRefineOfFaceLE ya yb hlea)
        ≫ eqToHom (congrArg BPSet.serialWedge (dims_reindex σ hcova).symm) := by
    apply BPSet.hom_ext
    simp only [BPSet.comp_hom, bpset_eqToHom_hom]
    exact rwm_reindex σ hcova hcovb hlea hlea' hnc_a
  rw [← conj_eqToHom_iff_heq _ _ (congrArg BPSet.serialWedge hdimsB)
    (congrArg BPSet.serialWedge hdimsA), hrwm]
  simp only [refineChain_dims, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end CubeChains
