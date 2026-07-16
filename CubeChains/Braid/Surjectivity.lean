import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.Generated
import CubeChains.Braid.CubeIso
import Mathlib.GroupTheory.Schreier

/-!
# Braid/Surjectivity — every pure braid is a concurrency loop

`concPureBraidHom n x` is onto `Pₙ` (`Cubical-xhj.6`, surjectivity half).

**Schreier's lemma** on `Pₙ = ker (Bₙ ↠ Sₙ)` with the transversal `range ofPerm` presents `Pₙ` by
the generators `ofPerm σ · ofPerm (adjT j) · ofPerm (σ · adjT j)⁻¹` (`pureBraid_le_of_schreier`).
Each is the braid of a `schreierLoop`: three lines `L₀, Lₐ, L_b` of one coarse chain, whose runs are
joined by `elemBraid`s into a triangle of executions — a genuine endomorphism, no cross-chain
matching.  On the single-`n`-cube basepoint `x₀`, whose lines realise *every* event order
(`keyEquiv_surjective`), the three lines are picked to hit any prescribed Schreier generator.

Gotcha: keep the realisation **parametric in the basepoint**
(`concPureBraidHom_surjective_of_lines`).  At a concrete `x₀`, unifying `keyEquiv (evKey L)` forces
`Equiv.ofBijective`/`keyRank` over the cube's event set — a `whnf` blowup; with `x` a variable those
stay opaque.
-/

open CategoryTheory Equiv

namespace CubeChains

variable {n : ℕ}

/-! ## The permutation transversal of the pure braids

`permHom : Bₙ ↠ Sₙ` has the set-section `ofPerm`, so `range ofPerm` meets every coset of
`Pₙ = ker permHom` exactly once: it is a right-transversal complement. -/

/-- **`range ofPerm` is a transversal of `Pₙ`.**  The unique representative in the coset of `g` is
`ofPerm (permHom g)`, because `permHom (ofPerm τ) = τ` pins `τ` down. -/
theorem isComplement_range_ofPerm (n : ℕ) :
    Subgroup.IsComplement (PureBraid n : Set (Braid n))
      (Set.range (ofPerm : Perm (Fin n) → Braid n)) := by
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  refine ⟨⟨ofPerm (permHom n g), permHom n g, rfl⟩, ?_, ?_⟩
  · change g * (ofPerm (permHom n g))⁻¹ ∈ (PureBraid n : Set (Braid n))
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, permHom_ofPerm, mul_inv_cancel]
  · rintro ⟨_, τ, rfl⟩ ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, permHom_ofPerm,
      mul_inv_eq_one] at ht
    exact Subtype.ext (congrArg ofPerm ht).symm

/-- **`1 ∈ range ofPerm`.** -/
theorem one_mem_range_ofPerm (n : ℕ) :
    (1 : Braid n) ∈ Set.range (ofPerm : Perm (Fin n) → Braid n) :=
  ⟨1, ofPerm_one⟩

/-- The transversal representative of `g` is `ofPerm (permHom g)`. -/
theorem toRightFun_range_ofPerm (n : ℕ) (g : Braid n) :
    ((isComplement_range_ofPerm n).toRightFun g : Braid n) = ofPerm (permHom n g) := by
  have hu := (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp
    (isComplement_range_ofPerm n)) g
  have e1 : g * ((isComplement_range_ofPerm n).toRightFun g : Braid n)⁻¹
      ∈ (PureBraid n : Set (Braid n)) := by
    rw [SetLike.mem_coe]; exact (isComplement_range_ofPerm n).mul_inv_toRightFun_mem g
  have e2 : g * (ofPerm (permHom n g))⁻¹ ∈ (PureBraid n : Set (Braid n)) := by
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, permHom_ofPerm, mul_inv_cancel]
  exact congrArg Subtype.val
    (hu.unique (y₁ := (isComplement_range_ofPerm n).toRightFun g)
      (y₂ := ⟨ofPerm (permHom n g), permHom n g, rfl⟩) e1 e2)

/-! ## The Schreier reduction

Adjacent transpositions generate `Bₙ` (`Braid.eq_closure_ofPerm_adjT`), so Schreier's lemma
presents `Pₙ` on the generators `ofPerm σ · ofPerm (adjT j) · ofPerm (σ · adjT j)⁻¹`. -/

/-- **Schreier reduction.**  A subgroup `G ≤ Bₙ` that contains every Schreier generator
`ofPerm σ · ofPerm (adjT j) · ofPerm (σ · adjT j)⁻¹` already contains all of `Pₙ`. -/
theorem pureBraid_le_of_schreier (n : ℕ) (G : Subgroup (Braid n))
    (h : ∀ (σ : Perm (Fin n)) (j : Fin (n - 1)),
        ofPerm σ * ofPerm (adjT j) * (ofPerm (σ * adjT j))⁻¹ ∈ G) :
    PureBraid n ≤ G := by
  have hkey := Subgroup.closure_mul_image_eq (isComplement_range_ofPerm n)
    (one_mem_range_ofPerm n) (Braid.eq_closure_ofPerm_adjT n)
  rw [← hkey, Subgroup.closure_le]
  rintro y ⟨g, hg, rfl⟩
  obtain ⟨r, hr, s, hs, rfl⟩ := hg
  obtain ⟨σ, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hs
  rw [SetLike.mem_coe]
  dsimp only
  rw [toRightFun_range_ofPerm, map_mul, permHom_ofPerm, permHom_ofPerm]
  exact h σ j

/-! ## The permutation braids generate `Bₙ`

The group-theoretic core of "the concurrency category's target is the *full* braid category": the
permutation braids `ofPerm σ` — each of which is realised by a concurrency transport — generate all
of `Bₙ`. -/

/-- **The permutation braids generate `Bₙ`.**  Since the adjacent transpositions do
(`Braid.eq_closure_ofPerm_adjT`) and each is an `ofPerm σ`. -/
theorem closure_range_ofPerm (n : ℕ) :
    Subgroup.closure (Set.range (ofPerm : Perm (Fin n) → Braid n)) = ⊤ := by
  rw [eq_top_iff, ← Braid.eq_closure_ofPerm_adjT n, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact Subgroup.subset_closure ⟨adjT j, rfl⟩

/-! ## Surjectivity, reduced to the geometric realisation

What remains is to hit each Schreier generator by a concurrency loop.  `concBraidHom n x` lands in
`Braid (nEvents x)`, so the reduction is stated at that strand count (`nEvents x = n` on the cube,
only propositionally). -/

/-- **Surjectivity of `concPureBraidHom`, reduced to Schreier realisation.**  If every Schreier
generator lies in the image of the concurrency braid map, then `concPureBraidHom n x` is onto the
pure braids.  (The `⊆` half is purity, `concBraidHom_mem_pure`; this supplies `⊇`.) -/
theorem concPureBraidHom_surjective_of_realizes (n : ℕ) (x : ConcCat (□n))
    (h : ∀ (σ : Perm (Fin (nEvents x))) (j : Fin (nEvents x - 1)),
        ofPerm σ * ofPerm (adjT j) * (ofPerm (σ * adjT j))⁻¹
          ∈ MonoidHom.range (concBraidHom n x)) :
    Function.Surjective (concPureBraidHom n x) := by
  have hle : PureBraid (nEvents x) ≤ MonoidHom.range (concBraidHom n x) :=
    pureBraid_le_of_schreier (nEvents x) _ h
  intro p
  obtain ⟨a, ha⟩ := hle p.2
  exact ⟨a, Subtype.ext ha⟩

/-! ## Ranking a prescribed bijection

`keyEquiv f` depends only on the *order* `f` induces, and for the tautological key
`a ↦ (τ a : ℤ)` of a bijection `τ : α ≃ Fin (card α)` it *is* `τ`.  Together these turn "build a
line whose event order is a prescribed permutation" into "pick the chamber `chamberOfInj`." -/

/-- The key rank counts `<`-predecessors, so it depends only on the order `f` induces. -/
theorem keyRank_congr_order {α : Type} [Fintype α] {γ γ' : Type} [LinearOrder γ] [LinearOrder γ']
    (f : α → γ) (g : α → γ') (h : ∀ x y, f x < f y ↔ g x < g y) (e : α) :
    keyRank f e = keyRank g e := by
  classical
  rw [keyRank, keyRank]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h y e

/-- Two injective keys inducing the same order have the same `keyEquiv`. -/
theorem keyEquiv_congr_order {α : Type} [Fintype α] {γ γ' : Type} [LinearOrder γ] [LinearOrder γ']
    (f : α → γ) (g : α → γ') (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x y, f x < f y ↔ g x < g y) :
    keyEquiv f hf = keyEquiv g hg := by
  apply Equiv.ext; intro e; apply Fin.ext
  rw [keyEquiv_val, keyEquiv_val]
  exact keyRank_congr_order f g h e

/-- The tautological key `a ↦ (τ a : ℤ)` ranks `α` exactly by `τ`. -/
theorem keyRank_of_equiv {α : Type} [Fintype α] (τ : α ≃ Fin (Fintype.card α)) (e : α) :
    keyRank (fun a => ((τ a : ℕ) : ℤ)) e = (τ e : ℕ) := by
  classical
  rw [keyRank]
  have hset : (Finset.univ.filter (fun y => ((τ y : ℕ) : ℤ) < ((τ e : ℕ) : ℤ)))
        = Finset.univ.filter (fun y => (τ y : ℕ) < (τ e : ℕ)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_lt]
  rw [hset]
  have hcard : (Finset.univ.filter (fun y => (τ y : ℕ) < (τ e : ℕ))).card
        = (Finset.Iio (τ e)).card := by
    refine Finset.card_bij' (fun y _ => τ y) (fun k _ => τ.symm k) ?_ ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_Iio.mpr (Fin.lt_def.mpr (Finset.mem_filter.mp hy).2)
    · intro k hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa using Fin.lt_def.mp (Finset.mem_Iio.mp hk)
    · intro y _; simp
    · intro k _; simp
  rw [hcard, Fin.card_Iio]

/-- The tautological key of a bijection `τ` has `keyEquiv = τ`. -/
theorem keyEquiv_of_equiv {α : Type} [Fintype α] (τ : α ≃ Fin (Fintype.card α)) :
    keyEquiv (fun a => ((τ a : ℕ) : ℤ))
        (fun _ _ hxy => τ.injective (Fin.ext (Nat.cast_injective hxy))) = τ := by
  apply Equiv.ext; intro e; apply Fin.ext
  rw [keyEquiv_val]
  exact keyRank_of_equiv τ e

/-! ## Reading the braid on a fixed strand count

`readBraid n` collapses `𝔅` onto the fixed fibre `SingleObj (Braid n)`, keeping the braid
(recast when `a = n`, trivial otherwise) — the braid-preserving analogue of `readPerm`. -/

/-- A braid recast along `a = n`, as a monoid hom. -/
noncomputable def braidEqHom {a n : ℕ} (h : a = n) : Braid a →* Braid n where
  toFun := braidCast h
  map_one' := by subst h; rfl
  map_mul' x y := by subst h; rfl

/-- Read a braid on `a` strands as one on `n` strands: recast when `a = n`, else trivial. -/
noncomputable def braidSelfHom (n a : ℕ) : Braid a →* Braid n :=
  if h : a = n then braidEqHom h else 1

theorem braidSelfHom_eq (n : ℕ) {a : ℕ} (h : a = n) (b : Braid a) :
    braidSelfHom n a b = braidCast h b := by
  rw [braidSelfHom, dif_pos h]; rfl

/-- Collapse `𝔅` onto `SingleObj (Braid n)`, keeping the braid recast to `n` strands. -/
noncomputable def readBraid (n : ℕ) : Braids ⥤ SingleObj (Braid n) :=
  CategoryTheory.Sigma.desc fun a =>
    SingleObj.mapHom (Braid a) (Braid n) (braidSelfHom n a)

theorem readBraid_map_braidHom (n : ℕ) {a : ℕ} (b : Braid a) :
    (readBraid n).map (braidHom b) = braidSelfHom n a b := rfl

/-! ## The single-`n`-cube basepoint

The coarsest chain of `□n` — one bead of dimension `n`, whose lines range over *all* `n!` orderings
of the events.  It is the only chain whose event order is unconstrained by beads, so it is where the
transports `ofPerm σ` all live. -/

section Basepoint

variable {n : ℕ}

/-- The constant surjection collapsing all `n` coordinates into one block (needs `n ≥ 1`). -/
def collapseβ (n : ℕ) : Fin n → Fin 1 := fun _ => 0

theorem collapseβ_surjective (hn : 0 < n) : Function.Surjective (collapseβ n) :=
  fun _ => ⟨⟨0, hn⟩, Subsingleton.elim _ _⟩

/-- The **coarsest chain** of `□n`: one bead of dimension `n`. -/
noncomputable def cubeChain (hn : 0 < n) : Ch (□n) :=
  CubeChain.refineToWedgeObj (chainOf (collapseβ n) (collapseβ_surjective hn))

theorem cubeChain_dims_length (hn : 0 < n) : (cubeChain hn).dims.length = 1 := by
  change ((chainOf (collapseβ n) (collapseβ_surjective hn)).cubes.map (·.1)).length = 1
  rw [List.length_map, chainOf_cubes_length]

/-- The coarsest chain has one bead, so its `Bead` index type is a singleton. -/
noncomputable instance uniqueBead (hn : 0 < n) : Unique (ChainCat.Bead (cubeChain hn)) :=
  haveI hss : Subsingleton (ChainCat.Bead (cubeChain hn)) :=
    Fin.subsingleton_iff_le_one.mpr (le_of_eq (cubeChain_dims_length hn))
  { default := ⟨0, by rw [cubeChain_dims_length hn]; norm_num⟩
    uniq := fun i => Subsingleton.elim _ _ }

/-! ### Every line's event order is realizable

For the single bead, `LinesObj` ranges over `Chamber n`, and the event key `evKey L'` orders the
events exactly by the chamber.  So a *prescribed* bijection `τ` of the events is the key order of
the chamber `chamberOfInj (τ ·)`, giving `keyEquiv (evKey L') = τ`. -/

open Equiv in
/-- **Every event order is a line's key order.**  `L' ↦ keyEquiv (evKey L')` is onto the bijections
`EventObj ≃ Fin (card)` — the crux that the single cube realizes every permutation. -/
theorem keyEquiv_surjective (hn : 0 < n) :
    Function.Surjective (fun L' : LinesObj (cubeChain hn) =>
        keyEquiv (evKey L') (evKey_injective L')) := by
  classical
  intro τ
  have hinj : ∀ i : ChainCat.Bead (cubeChain hn),
      Function.Injective
        (fun δ : Fin (ChainCat.beadDim (cubeChain hn) i) => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) := by
    intro i a b hab
    have h1 : (⟨i, a⟩ : EventObj (cubeChain hn)) = ⟨i, b⟩ :=
      τ.injective (Fin.ext (Nat.cast_injective hab))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  refine ⟨fun i => chamberOfInj (fun δ => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) (hinj i), ?_⟩
  set L' : LinesObj (cubeChain hn) :=
    fun i => chamberOfInj (fun δ => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) (hinj i) with hL'
  have horder : ∀ e' e : EventObj (cubeChain hn),
      evKey L' e' < evKey L' e ↔ ((τ e' : ℕ) : ℤ) < ((τ e : ℕ) : ℤ) := by
    rintro ⟨i', δ'⟩ ⟨i, δ⟩
    obtain rfl : i' = default := Subsingleton.elim _ _
    obtain rfl : i = default := Subsingleton.elim _ _
    simp only [evKey, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or,
      true_and, chamberRank_lt_iff, hL', chamberOfInj_lt, Nat.cast_lt]
  change keyEquiv (evKey L') (evKey_injective L') = τ
  rw [keyEquiv_congr_order (evKey L') (fun a => ((τ a : ℕ) : ℤ)) (evKey_injective L')
    (fun _ _ hxy => τ.injective (Fin.ext (Nat.cast_injective hxy))) horder]
  exact keyEquiv_of_equiv τ

/-- The single-`n`-cube **execution** basepoint (line = the natural order per bead). -/
noncomputable def x₀ (hn : 0 < n) : ConcCat (□n) :=
  ⟨Opposite.op (cubeChain hn), fun i => natChamber (ChainCat.beadDim (cubeChain hn) i)⟩

@[simp] theorem x₀_chain (hn : 0 < n) : (x₀ hn).chain = cubeChain hn := rfl

theorem nEvents_x₀ (hn : 0 < n) : nEvents (x₀ hn) = n := eventObj_card_cube (cubeChain hn)

open Equiv in
/-- **The transports are onto all permutations.**  `L' ↦ evPerm' (seqMor x₀ L')` is surjective onto
`Perm (Fin (nEvents x₀))`: post-composing the onto `keyEquiv` with the fixed frame `evIdx' x₀`. -/
theorem transport_surjective (hn : 0 < n) :
    Function.Surjective (fun L' : LinesObj (cubeChain hn) => evPerm' (seqMor (x₀ hn) L')) := by
  intro π
  obtain ⟨L', hL'⟩ := keyEquiv_surjective hn ((evIdx' (x₀ hn)).trans π)
  have hL'' : keyEquiv (evKey (a := (x₀ hn).chain) L') (evKey_injective L')
      = (evIdx' (x₀ hn)).trans π := hL'
  refine ⟨L', ?_⟩
  have key : evPerm' (seqMor (x₀ hn) L') = π := by
    rw [evPerm'_seqMor, hL'']
    apply Equiv.ext
    intro k
    exact (Equiv.trans_apply _ _ _).trans
      ((Equiv.trans_apply _ _ _).trans (congrArg π (Equiv.apply_symm_apply _ _)))
  exact key

/-! ### The transports realize every `ofPerm σ`

`elemBraid x₀ L'` is a concurrency iso between the two runs `seq(x₀, x₀.line)` and `seq(x₀, L')`,
whose braid is `ofPerm (evPerm' (seqMor x₀ L'))` (`braidGrpd_map_elemBraid`).  Ranging `L'` over all
lines, every simple braid is realized. -/

/-- **Every simple braid is a run-to-run transport.**  For each `π`, the elementary iso
`elemBraid x₀ L'` (between two runs) has braid `ofPerm π`, read through the strand recasts. -/
theorem braidGrpd_transport (hn : 0 < n) (π : Perm (Fin (nEvents (x₀ hn)))) :
    ∃ L' : LinesObj (cubeChain hn),
      (braidGrpd (□n)).map (elemBraid (x₀ hn) L').hom
        = eqToHom (congrArg strands (nEvents_eq (seqMor (x₀ hn) (x₀ hn).line))).symm
          ≫ braidHom (ofPerm π)
          ≫ eqToHom (congrArg strands (nEvents_eq (seqMor (x₀ hn) L'))) := by
  obtain ⟨L', hL'⟩ := transport_surjective hn π
  have hL'' : evPerm' (seqMor (x₀ hn) L') = π := hL'
  exact ⟨L', by rw [braidGrpd_map_elemBraid, hL'']⟩

/-- **The transports generate the full braid group.**  The braids of the run-to-run transports
`ofPerm (evPerm' (seqMor x₀ L'))` — the values `braidGrpd` assigns to `elemBraid x₀ L'` — generate
all of `Braid (nEvents x₀)`.  This is the group-level "the concurrency target is the *full* braid
group", localised to the single-cube run component. -/
theorem braidGrpd_surjective_onBraid (hn : 0 < n) :
    Subgroup.closure
        { b : Braid (nEvents (x₀ hn)) |
          ∃ L' : LinesObj (cubeChain hn), b = ofPerm (evPerm' (seqMor (x₀ hn) L')) } = ⊤ := by
  rw [eq_top_iff, ← closure_range_ofPerm (nEvents (x₀ hn))]
  apply Subgroup.closure_mono
  rintro _ ⟨σ, rfl⟩
  obtain ⟨L', hL'⟩ := transport_surjective hn σ
  have hL'' : evPerm' (seqMor (x₀ hn) L') = σ := hL'
  exact ⟨L', (congrArg ofPerm hL'').symm⟩

end Basepoint

/-! ## The triangle loop: realizing Schreier generators without cross-chain matching

Three executions sharing a single chain `x.chain` (differing only in their line `L₀, L₁, L₂`) give
a genuine loop through the three runs `run Lᵢ`.  Because all three runs are sequentializations of
lines of the *same* chain, they coincide as objects with no cross-chain identification.  The loop's
braid is `ofPerm δ₂ · ofPerm δ₁ · ofPerm δ₀`, one simple braid per leg; on the single-cube `x₀`,
where every ordering is a line, the `δᵢ` range freely enough to hit every Schreier generator. -/

section Triangle

variable {n : ℕ}

/-- The **triangle loop** through the runs of `L₀, L₁, L₂` (lines of `x.chain`), based at `run L₀`.
Its three legs are `elemBraid`s of the three executions `⟨x.1, Lᵢ⟩` sharing `x`'s chain. -/
noncomputable def triLoop (x : ConcCat (□n)) (L₀ L₁ L₂ : LinesObj x.chain) :
    (FreeGroupoid.mk (runExec (seqChain L₀) (seqChain_isRun L₀)) : ConcGrpd (□n))
      ≅ FreeGroupoid.mk (runExec (seqChain L₀) (seqChain_isRun L₀)) :=
  elemBraid (⟨x.1, L₀⟩ : ConcCat (□n)) L₁ ≪≫ elemBraid (⟨x.1, L₁⟩ : ConcCat (□n)) L₂
    ≪≫ elemBraid (⟨x.1, L₂⟩ : ConcCat (□n)) L₀

/-- `readBraid` kills the strand-count recasts. -/
theorem readBraid_map_eqToHom (n : ℕ) {X Y : Braids} (h : X = Y) :
    (readBraid n).map (eqToHom h) = 𝟙 _ := by
  rw [eqToHom_map]; rfl

/-- The braid of an `elemBraid` leg, collapsed to `Braid n`: the recasts vanish and the event
permutation survives. -/
theorem readBraid_map_elemBraid (x : ConcCat (□n)) (L' : LinesObj x.chain) (hx : nEvents x = n) :
    (readBraid n).map ((braidGrpd (□n)).map (elemBraid x L').hom)
      = braidCast hx (ofPerm (evPerm' (seqMor x L'))) := by
  rw [braidGrpd_map_elemBraid]
  erw [Functor.map_comp, Functor.map_comp, readBraid_map_eqToHom, readBraid_map_eqToHom,
    readBraid_map_braidHom]
  rw [braidSelfHom_eq n hx]
  erw [Category.id_comp, Category.comp_id]

/-- A strand-count recast is a monoid map on products. -/
theorem braidCast_mul {a m : ℕ} (h : a = m) (x y : Braid a) :
    braidCast h (x * y) = braidCast h x * braidCast h y :=
  map_mul (braidEqHom h) x y

/-- A strand-count recast is a monoid map on inverses. -/
theorem braidCast_inv {a m : ℕ} (h : a = m) (x : Braid a) :
    braidCast h x⁻¹ = (braidCast h x)⁻¹ :=
  map_inv (braidEqHom h) x

/-- The braid of a *reversed* `elemBraid` leg: the inverse simple braid. -/
theorem readBraid_map_elemBraid_symm (x : ConcCat (□n)) (L' : LinesObj x.chain)
    (hx : nEvents x = n) :
    (readBraid n).map ((braidGrpd (□n)).map (elemBraid x L').symm.hom)
      = (braidCast hx (ofPerm (evPerm' (seqMor x L'))))⁻¹ := by
  have hh : (elemBraid x L').symm.hom = CategoryTheory.inv (elemBraid x L').hom :=
    (IsIso.inv_eq_of_hom_inv_id (elemBraid x L').hom_inv_id).symm
  rw [hh, Functor.map_inv]
  erw [Functor.map_inv, SingleObj.inv_as_inv, readBraid_map_elemBraid x L' hx]

/-- The event permutation of the leg from the `L`-ordering to the `L'`-run: the `L`-frame read
through the `L'`-frame, in `x`'s strand count (independent of the leg, unlike `evPerm'`). -/
noncomputable def legPerm (x : ConcCat (□n)) (L L' : LinesObj x.chain) : Perm (Fin (nEvents x)) :=
  (keyEquiv (evKey L) (evKey_injective L)).symm.trans (keyEquiv (evKey L') (evKey_injective L'))

/-- The leg permutation is the sequentialization permutation of the `⟨x.1, L⟩` execution. -/
theorem legPerm_eq (x : ConcCat (□n)) (L L' : LinesObj x.chain) :
    evPerm' (seqMor (⟨x.1, L⟩ : ConcCat (□n)) L') = legPerm x L L' := by
  rw [evPerm'_seqMor]; rfl

/-- **The braid of the triangle loop, collapsed to `Braid n`.**  One simple braid per leg,
multiplied in leg order (`endBraid` reverses `≫`, so leg 3 · leg 2 · leg 1). -/
theorem readBraid_triLoop (x : ConcCat (□n)) (L₀ L₁ L₂ : LinesObj x.chain) (hx : nEvents x = n) :
    (readBraid n).map ((braidGrpd (□n)).map (triLoop x L₀ L₁ L₂).hom)
      = braidCast hx (ofPerm (legPerm x L₂ L₀) * ofPerm (legPerm x L₁ L₂)
          * ofPerm (legPerm x L₀ L₁)) := by
  rw [triLoop, Iso.trans_hom, Iso.trans_hom, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  erw [readBraid_map_elemBraid (⟨x.1, L₀⟩ : ConcCat (□n)) L₁ hx,
    readBraid_map_elemBraid (⟨x.1, L₁⟩ : ConcCat (□n)) L₂ hx,
    readBraid_map_elemBraid (⟨x.1, L₂⟩ : ConcCat (□n)) L₀ hx]
  rw [legPerm_eq, legPerm_eq, legPerm_eq, SingleObj.comp_as_mul, SingleObj.comp_as_mul,
    braidCast_mul, braidCast_mul]
  rfl

/-- **The Schreier loop.**  A triangle loop with the first leg reversed, so its braid carries a
genuine inverse: `ofPerm (leg₃) · ofPerm (leg₂) · (ofPerm (leg₁))⁻¹` — the shape of a Schreier
generator `ofPerm σ · ofPerm (adjT j) · (ofPerm (σ · adjT j))⁻¹`. -/
noncomputable def schreierLoop (x : ConcCat (□n)) (L₀ Lₐ L_b : LinesObj x.chain) :
    (FreeGroupoid.mk (runExec (seqChain L₀) (seqChain_isRun L₀)) : ConcGrpd (□n))
      ≅ FreeGroupoid.mk (runExec (seqChain L₀) (seqChain_isRun L₀)) :=
  (elemBraid (⟨x.1, Lₐ⟩ : ConcCat (□n)) L₀).symm ≪≫ elemBraid (⟨x.1, Lₐ⟩ : ConcCat (□n)) L_b
    ≪≫ elemBraid (⟨x.1, L_b⟩ : ConcCat (□n)) L₀

/-- **The braid of the Schreier loop, collapsed to `Braid n`.** -/
theorem readBraid_schreierLoop (x : ConcCat (□n)) (L₀ Lₐ L_b : LinesObj x.chain)
    (hx : nEvents x = n) :
    (readBraid n).map ((braidGrpd (□n)).map (schreierLoop x L₀ Lₐ L_b).hom)
      = braidCast hx (ofPerm (legPerm x L_b L₀) * ofPerm (legPerm x Lₐ L_b)
          * (ofPerm (legPerm x Lₐ L₀))⁻¹) := by
  rw [schreierLoop, Iso.trans_hom, Iso.trans_hom, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  erw [readBraid_map_elemBraid_symm (⟨x.1, Lₐ⟩ : ConcCat (□n)) L₀ hx,
    readBraid_map_elemBraid (⟨x.1, Lₐ⟩ : ConcCat (□n)) L_b hx,
    readBraid_map_elemBraid (⟨x.1, L_b⟩ : ConcCat (□n)) L₀ hx]
  rw [legPerm_eq, legPerm_eq, legPerm_eq, SingleObj.comp_as_mul, SingleObj.comp_as_mul,
    braidCast_mul, braidCast_mul, braidCast_inv]
  rfl

/-- Two recasts compose. -/
theorem braidCast_trans {a m k : ℕ} (h₁ : a = m) (h₂ : m = k) (y : Braid a) :
    braidCast h₂ (braidCast h₁ y) = braidCast (h₁.trans h₂) y := by
  subst h₁; subst h₂; rfl

/-- A recast and its inverse cancel. -/
theorem braidCast_leftInverse {a m : ℕ} (h : a = m) (y : Braid a) :
    braidCast h.symm (braidCast h y) = y := by subst h; rfl

/-- Read the braid of a strand-`m` endomorphism through `readBraid n` (when `m = n`). -/
theorem endBraid_of_readBraid {m : ℕ} (M : strands m ⟶ strands m) (hm : m = n) :
    endBraid M = braidCast hm.symm ((readBraid n).map M) := by
  have hval : (readBraid n).map M = braidCast hm (endBraid M) := by
    conv_lhs => rw [← braidHom_endBraid M]
    rw [readBraid_map_braidHom, braidSelfHom_eq n hm]
  rw [hval, braidCast_leftInverse]

/-- Reading `legPerm` off two prescribed key frames. -/
theorem legPerm_of_keys {x : ConcCat (□n)} (L L' : LinesObj x.chain)
    {A B : EventObj x.chain ≃ Fin (nEvents x)}
    (hL : keyEquiv (evKey L) (evKey_injective L) = A)
    (hL' : keyEquiv (evKey L') (evKey_injective L') = B) :
    legPerm x L L' = A.symm.trans B := by
  subst hL hL'; rfl

/-- `(A.trans B.symm).symm.trans A = B`, the frame-cancellation shape behind the leg perms. -/
theorem frameCancel {α : Type} {m : ℕ} (A : α ≃ Fin m) (B : Fin m ≃ Fin m) :
    (A.trans B.symm).symm.trans A = B := by
  apply Equiv.ext; intro k
  simp only [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

end Triangle

/-- `(A.trans C.symm).symm.trans (A.trans B.symm) = B⁻¹ * C`: the frame difference of two
prescribed key frames. -/
theorem frameCancel2 {α : Type} {m : ℕ} (A : α ≃ Fin m) (B C : Perm (Fin m)) :
    (A.trans C.symm).symm.trans (A.trans B.symm) = B⁻¹ * C := by
  apply Equiv.ext; intro k
  simp only [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

/-! ## Surjectivity at the canonical run basepoint

The three lines needed to hit a Schreier generator are picked by `keyEquiv_surjective`, and the
loop's braid is read to be exactly `ofPerm σ · ofPerm (adjT j) · (ofPerm (σ · adjT j))⁻¹`. -/

/-- **`concPureBraidHom` is onto the pure braids** at any basepoint whose lines realize *every*
event order (`hsurj`).  Every Schreier generator is the braid of a `schreierLoop` through three
such lines.  Kept parametric in `x`: the concrete cube is never unfolded, so `keyEquiv (evKey L)`
stays opaque and the `isDefEq` search never dives into `Equiv.ofBijective`/`keyRank`. -/
theorem concPureBraidHom_surjective_of_lines (n : ℕ) (x : ConcCat (□n)) (hx : nEvents x = n)
    (hsurj : Function.Surjective
      (fun L' : LinesObj x.chain => keyEquiv (evKey L') (evKey_injective L'))) :
    Function.Surjective (concPureBraidHom n (seqExec x)) := by
  -- `seqExec x` is defeq to the run `runExec (seqChain x.line) …`, but the latter is the spelling
  -- `schreierLoop`/`readBraid_schreierLoop` use.  Bridging the defeq *once* here keeps the whole
  -- proof in a single strand-count frame, so `group`/`rw`-rfl never choke on defeq atoms.
  change Function.Surjective
    (concPureBraidHom n (runExec (seqChain x.line) (seqChain_isRun x.line)))
  have hb : nEvents (runExec (seqChain x.line) (seqChain_isRun x.line)) = n := eventObj_card_cube _
  refine concPureBraidHom_surjective_of_realizes n
    (runExec (seqChain x.line) (seqChain_isRun x.line)) (fun σ j => ?_)
  set P := keyEquiv (evKey x.line) (evKey_injective x.line) with hP
  set g := permCongrHom (finCongr (hx.trans hb.symm)).symm with hg
  set σ₀ := g σ with hσ₀
  set ρ₀ := g (σ * adjT j) with hρ₀
  obtain ⟨L_b, hLb⟩ := hsurj (P.trans σ₀.symm)
  obtain ⟨Lₐ, hLa⟩ := hsurj (P.trans ρ₀.symm)
  have hleg_b : legPerm x L_b x.line = σ₀ := by
    rw [legPerm_of_keys L_b x.line hLb hP.symm]; exact frameCancel P σ₀
  have hleg_a : legPerm x Lₐ x.line = ρ₀ := by
    rw [legPerm_of_keys Lₐ x.line hLa hP.symm]; exact frameCancel P ρ₀
  have hleg_ab : legPerm x Lₐ L_b = σ₀⁻¹ * ρ₀ := by
    rw [legPerm_of_keys Lₐ L_b hLa hLb]; exact frameCancel2 P σ₀ ρ₀
  have hround : ∀ ρ, (finCongr (hx.trans hb.symm)).permCongr (g ρ) = ρ := fun ρ => by
    rw [hg, permCongrHom_apply, ← Equiv.permCongr_symm]; exact Equiv.apply_symm_apply _ ρ
  have h1 : (finCongr (hx.trans hb.symm)).permCongr σ₀ = σ := hround σ
  have h2 : (finCongr (hx.trans hb.symm)).permCongr ρ₀ = σ * adjT j := hround (σ * adjT j)
  have h3 : (finCongr (hx.trans hb.symm)).permCongr (σ₀⁻¹ * ρ₀) = adjT j := by
    have hgadj : σ₀⁻¹ * ρ₀ = g (adjT j) := by
      rw [hσ₀, hρ₀, ← map_inv g, ← map_mul g]; congr 1; group
    rw [hgadj, hround]
  refine ⟨schreierLoop x x.line Lₐ L_b, ?_⟩
  -- Bridge `concBraidHom` to the `readBraid` read-off as a *term* (defeq handles both
  -- `concBraidHom_apply` and the `endBraid` strand count); the RHS is in `braidGrpd.obj` form so
  -- `readBraid_schreierLoop` matches syntactically.  Rewrite inside `key`, then close by `exact`.
  have key : concBraidHom n (runExec (seqChain x.line) (seqChain_isRun x.line))
        (schreierLoop x x.line Lₐ L_b)
      = braidCast hb.symm ((readBraid n).map
          ((braidGrpd (□n)).map (schreierLoop x x.line Lₐ L_b).hom)) :=
    endBraid_of_readBraid _ hb
  rw [readBraid_schreierLoop x x.line Lₐ L_b hx, braidCast_trans,
    hleg_b, hleg_ab, hleg_a, braidCast_mul, braidCast_mul, braidCast_inv,
    braidCast_ofPerm, braidCast_ofPerm, braidCast_ofPerm, h1, h3, h2] at key
  exact key

/-- **`concPureBraidHom` is onto the pure braids** at the single-cube's canonical run. -/
theorem concPureBraidHom_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (concPureBraidHom n (seqExec (x₀ hn))) :=
  concPureBraidHom_surjective_of_lines n (x₀ hn) (nEvents_x₀ hn) (keyEquiv_surjective hn)

end CubeChains
