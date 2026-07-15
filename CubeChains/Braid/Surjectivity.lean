import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.Generated
import CubeChains.Braid.CubeIso
import Mathlib.GroupTheory.Schreier

/-!
RESTART NOTE (read first)
=========================

STATUS
  STEP 3 (Schreier wiring): **DONE** — the whole group-theoretic spine compiles, sorry-free.
    The extension `Pₙ = ker (permHom) ≤ Bₙ = ⟨ofPerm (adjT j)⟩` is presented by Schreier, and
    surjectivity is reduced to a purely geometric hypothesis (`..._of_realizes`).
  STEP 1 (elementary-braiding loop = `ofPerm (adjT j)`): **OPEN** — geometry, not yet started here.
  STEP 2 (transports `t σ` with braid `ofPerm σ`): **OPEN** — geometry, not yet started here.

WHAT COMPILES (this file), signatures:
  · isComplement_range_ofPerm (n) :
      Subgroup.IsComplement (PureBraid n : Set (Braid n)) (Set.range (ofPerm : Perm (Fin n) → _))
  · one_mem_range_ofPerm (n) : (1 : Braid n) ∈ Set.range (ofPerm : Perm (Fin n) → Braid n)
  · toRightFun_range_ofPerm (n) (g) :
      ((isComplement_range_ofPerm n).toRightFun g : Braid n) = ofPerm (permHom n g)
  · pureBraid_le_of_schreier (n) (G : Subgroup (Braid n))
      (h : ∀ σ j, ofPerm σ * ofPerm (adjT j) * (ofPerm (σ * adjT j))⁻¹ ∈ G) : PureBraid n ≤ G
  · closure_range_ofPerm (n) :
      Subgroup.closure (Set.range (ofPerm : Perm (Fin n) → Braid n)) = ⊤
      -- group-theory core of "the concurrency target is the FULL braid category"
  · concPureBraidHom_surjective_of_realizes (n) (x : ConcCat (□n))
      (h : ∀ σ j, ofPerm σ * ofPerm (adjT j) * (ofPerm (σ * adjT j))⁻¹
             ∈ MonoidHom.range (concBraidHom n x)) :
      Function.Surjective (concPureBraidHom n x)

EXACT NEXT LEMMA TO PROVE (closes everything):
  discharge the hypothesis `h` of `concPureBraidHom_surjective_of_realizes` at a basepoint, i.e.
    realize  `ofPerm σ · ofPerm (adjT j) · ofPerm (σ · adjT j)⁻¹ ∈ range (concBraidHom n x₀)`
  as the braid of a concurrency LOOP  `t σ ≫ e_{σ,j} ≫ (t (σ·adjT j))⁻¹`  at a run basepoint x₀.

GEOMETRY STILL NEEDED (the real content; needs NEW cube-execution infrastructure):
  (A) The single n-cube execution `x₀ : ConcCat (□n)` — one bead of dim n, so `LinesObj x₀.chain`
      is ALL of `Chamber n` (n! orderings).  Build via `SalBraidChain.chainOf (β : Fin n → Fin 1)`
      (constant β) wrapped into `Ch (□n)` (needs the RefineObj→Ch glue in `Chains/Correspondence`),
      then `⟨op x₀chain, someChamber⟩`.  Chambers from a permutation: `chamberOfInj` (SalBraidTope)
      or a pullback of `<` — one per σ.
  (B) TRANSPORTS.  For a line L of x₀.chain, `elemBraid x₀ L : mk(run x₀.line) ≅ mk(run L)` already
      has braid `ofPerm (evPerm' (seqMor x₀ L))` (via `braidGrpd_map_elemBraid`).  Since
      `evPerm' (seqMor x₀ L) = (evIdx' x₀).symm.trans (keyEquiv (evKey L))` and, on the single cube,
      L ↦ keyEquiv (evKey L) ranges over ALL bijections, EVERY `ofPerm σ` is a transport braid.
      NB this avoids the STEP-2 "chain elementary braidings" frame bookkeeping the plan feared:
      transports are single `elemBraid`s off ONE cube — no telescoping, no per-step frame.
  (C) The elementary braiding LOOP for `adjT j`.  A single square-bead execution gives only a span
      (flat, trivial holonomy — verified for □²).  The nontrivial loop uses BOTH chambers of a
      "run with one square at position j" execution ω: it is
          elemBraid ω_ab L_ba  ≫  elemBraid ω_ba L_ab  :  mk(run_ab) → mk(run_ba) → mk(run_ab),
      the □²-style generator of Pₙ (its braid = ofPerm(adjT j)·ofPerm(adjT j), the full twist).
      For the Schreier generator, splice the two halves between transports.

OBSTRUCTIONS / GOTCHAS to mind on restart:
  · `endBraid` ONLY typechecks on genuine LOOPS (`strands a ⟶ strands a`).  A transport between two
    DISTINCT runs has `nEvents` equal only PROPOSITIONALLY (not defeq), so `endBraid (map (t σ))`
    is ILL-TYPED.  State transports with the eqToHom recasts kept, exactly like
    `braidGrpd_map_elemBraid` (`… = eqToHom _ ≫ braidHom (ofPerm σ) ≫ eqToHom _`), NOT via endBraid.
    `endBraid` is only legitimate on the final Schreier LOOP at x₀ (source = target).
  · Gap (a) in the plan ("endBraid (elemBraid …) = ofPerm (swap …)") is thus a mirage for a bare
    `elemBraid`; only the composed loop is an endomorphism.  Use `braidGrpd_map_elemBraid` +
    `endBraid_comp` (reversal!) to read the loop braid, plus `endBraid_braidHom` and that
    `endBraid (eqToHom _)` is absorbed once source = target.
  · `endBraid_comp` reverses: `endBraid (F ≫ G) = endBraid G * endBraid F`.  A loop `A ≫ B ≫ C`
    has braid `braid C · braid B · braid A`.  The Schreier generator wanted is
    `ofPerm σ · ofPerm(adjT j) · ofPerm(σ·adjT j)⁻¹`; pick the loop orientation/transport
    conventions to land exactly this (range is a subgroup, so match it precisely).

# Braid/Surjectivity — every pure braid is a concurrency loop

Target (`Cubical-xhj.6`, surjectivity half): `concPureBraidHom n x` is onto `Pₙ`.

The strategy climbs into the presented extension `Bₙ = ⟨ofPerm (adjT j)⟩` and applies **Schreier's
lemma** to `Pₙ = ker (Bₙ ↠ Sₙ)` with the transversal `R = range ofPerm`.  Schreier presents `Pₙ` by
the generators `ofPerm σ · ofPerm (adjT j) · ofPerm (σ · adjT j)⁻¹`, each of which is a loop of
executions: a transport to the `σ`-run, an adjacent braiding, a transport back.

This file is the group-theoretic spine (`pureBraid_le_of_schreier`) and the reduction of
surjectivity to realising those Schreier generators (`concPureBraidHom_surjective_of_realizes`).
The geometric realisation — the transports and the elementary braiding loop — is the remaining
input.
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

end CubeChains
