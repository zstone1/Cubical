import CubeChains.Salvetti.BraidFace
import CubeChains.Salvetti.Runs
import CubeChains.Chains.WedgeSplitHom

/-!
# Salvetti/SalLines — runs refining a chain ↔ topes above its covector

A run of `a : Ch (□ⁿ)` traces out an all-edges chain of `□ⁿ` (`runChain`), whose ordered set
partition is a *linear* order on `Fin n` — a tope of the braid arrangement, lying above `a`'s own
covector because the run is itself a chain morphism onto `a`.
Backwards: a tope above `a`'s covector is a face of the braid arrangement whose chain
(`faceChain`) is all edges, and `chainRefineOfFaceLE` factors it through `a`.
The two directions are inverse by mono-cancellation against `a.map`: `Ch (□ⁿ)` is thin.
-/

open CategoryTheory Opposite CubeChain StdCube SignType BPSet

namespace CubeChains

open SignVec

variable {n : ℕ}

/-! ## Part 1 — the all-edges chain traced out by a run -/

/-- The chain of `□ⁿ` a run traces out: the run's own beads, classified through `a`.  This is
`Run.pushforward a.map` on the nose — a run of `⋁a.dims` pushed into `□ⁿ`. -/
def runChain (a : Ch (□n)) (r : Run (⋁a.dims)) : Ch (□n) :=
  ((Run.pushforward a.map).obj r).chain

@[simp] theorem runChain_dims (a : Ch (□n)) (r : Run (⋁a.dims)) :
    (runChain a r).dims = r.dims := rfl

/-- A run **is** a chain morphism onto the chain it refines — the fact every property of
`runChain` is read off. -/
def runHom (a : Ch (□n)) (r : Run (⋁a.dims)) : runChain a r ⟶ a := ⟨r.map, rfl⟩

@[simp] theorem runHom_φ (a : Ch (□n)) (r : Run (⋁a.dims)) : (runHom a r).φ = r.map := rfl

/-- The beads read off a chain are its dimension sequence. -/
theorem wedgeToRefineObj_dims {K : BPSet} (a : Ch K) :
    (wedgeToRefineObj a).cubes.map (·.1) = a.dims :=
  wedgeToCubes_dims _ _

/-- Every bead of the chain traced out by a run is an edge — now just `Run.ones`, since a run
carries its own all-ones dimension sequence. -/
theorem runChain_bead_dim (a : Ch (□n)) (r : Run (⋁a.dims))
    (i : Fin (wedgeToRefineObj (runChain a r)).cubes.length) :
    (((wedgeToRefineObj (runChain a r)).cubes.get i).1 : ℕ) = 1 := by
  have hd := wedgeToRefineObj_dims (runChain a r)
  have hmem : ((wedgeToRefineObj (runChain a r)).cubes.get i).1 ∈ r.dims := by
    rw [← runChain_dims a r, ← hd]
    exact List.mem_map_of_mem (List.get_mem _ _)
  exact congrArg PNat.val (r.ones _ hmem)

/-- An all-edges chain has singleton blocks, so its block index is injective. -/
theorem blockIndex_injective_of_dim_one (x : RefineObj (□n).init (□n).final)
    (h1 : ∀ i, ((x.cubes.get i).1 : ℕ) = 1) : Function.Injective (blockIndex x) := by
  intro p q hpq
  have hp := blockIndex_mem x p
  have hq : q ∈ blockOf x (blockIndex x p) := (mem_block_iff x).mpr hpq.symm
  have hcard : (blockOf x (blockIndex x p)).card = 1 := by
    rw [blockOf_card x]; exact h1 _
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  rw [hz, Finset.mem_singleton] at hp hq
  rw [hp, hq]

/-- **The height function of a run**: the position at which each coordinate is flipped. -/
def runHeight (a : Ch (□n)) (r : Run (⋁a.dims)) : Fin n → ℤ :=
  chCovectorHeight (runChain a r)

/-- **A run has no ties.**  Its chain is all edges, so each block is a single coordinate. -/
theorem runHeight_injective (a : Ch (□n)) (r : Run (⋁a.dims)) :
    Function.Injective (runHeight a r) := by
  intro p q hpq
  have hpq' : ((blockIndex (wedgeToRefineObj (runChain a r)) p : ℕ) : ℤ)
      = ((blockIndex (wedgeToRefineObj (runChain a r)) q : ℕ) : ℤ) := hpq
  exact blockIndex_injective_of_dim_one _ (runChain_bead_dim a r) (Fin.ext (by exact_mod_cast hpq'))

/-- **A run is a tope.** -/
theorem isTope_runHeight (a : Ch (□n)) (r : Run (⋁a.dims)) :
    (braidCOM n).IsTope (braidSign (runHeight a r)) :=
  (braidCOM_isTope_iff_injective _).mpr ⟨runHeight a r, runHeight_injective a r, rfl⟩

/-- **A run's tope lies above the chain it refines** — because the run is a chain morphism. -/
theorem faceLE_runHeight (a : Ch (□n)) (r : Run (⋁a.dims)) :
    braidSign (chCovectorHeight a) ⊑ braidSign (runHeight a r) :=
  faceLE_of_chHom (runHom a r)

/-- The topes lying above the covector of a chain — the value of the Salvetti presheaf there. -/
abbrev TopeOver (a : Ch (□n)) : Type :=
  {T : SignVec (BraidGround n) //
    (braidCOM n).IsTope T ∧ braidSign (chCovectorHeight a) ⊑ T}

/-- **Run ↦ tope.** -/
def ofRun (a : Ch (□n)) (r : Run (⋁a.dims)) : TopeOver a :=
  ⟨braidSign (runHeight a r), isTope_runHeight a r, faceLE_runHeight a r⟩

/-! ## Part 2 — the chain of a tope is all edges -/

/-- The total dimension of a chain of `□ⁿ` is `n`. -/
theorem dimSum_dims (a : Ch (□n)) : dimSum a.dims = n := by
  rw [← wedgeToRefineObj_dims a, dimSum_sum, List.map_map]
  exact cubes_dims_sum (wedgeToRefineObj a)

/-- The tope, read as a face of the braid arrangement. -/
def topeFace {a : Ch (□n)} (T : TopeOver a) : COM.Face (braidCOM n) := ⟨T.1, T.2.1.1⟩

@[simp] theorem topeFace_val {a : Ch (□n)} (T : TopeOver a) : (topeFace T).1 = T.1 := rfl

/-- **A tope's block map is injective**: a tie of the block map is a zero of the covector. -/
theorem blockMap_injective_of_tope {a : Ch (□n)} (T : TopeOver a) :
    Function.Injective (blockMap (signHeight T.1)) := by
  have hbs : braidSign (fun p => ((blockMap (signHeight T.1) p : ℕ) : ℤ)) = T.1 := by
    rw [braidSign_blockMap]
    exact braidSign_signHeight_of_mem T.2.1.1
  have hnz := ((braidCOM_isTope_iff T.1).mp T.2.1).2
  intro p q hpq
  by_contra hne
  have key : ∀ e : BraidGround n,
      ((blockMap (signHeight T.1) e.1.1 : ℕ) : ℤ)
        = ((blockMap (signHeight T.1) e.1.2 : ℕ) : ℤ) → False := by
    intro e he
    exact hnz e (by rw [← hbs]; exact (braidSign_zero_iff _ e).mpr he)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key ⟨(p, q), h⟩ (by rw [hpq])
  · exact key ⟨(q, p), h⟩ (by rw [hpq])

/-- A tope has as many blocks as coordinates. -/
theorem numBlocks_tope {a : Ch (□n)} (T : TopeOver a) : numBlocks (signHeight T.1) = n := by
  have h : Fintype.card (Fin n) = Fintype.card (Fin (numBlocks (signHeight T.1))) :=
    Fintype.card_of_bijective ⟨blockMap_injective_of_tope T, blockMap_surjective _⟩
  simpa using h.symm

/-- Each block of a tope is a single coordinate. -/
theorem tope_block_card {a : Ch (□n)} (T : TopeOver a) (i : Fin (numBlocks (signHeight T.1))) :
    (Finset.univ.filter (fun p => blockMap (signHeight T.1) p = i)).card = 1 := by
  obtain ⟨p, hp⟩ := blockMap_surjective (signHeight T.1) i
  refine Finset.card_eq_one.mpr ⟨p, ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => blockMap_injective_of_tope T (h.trans hp.symm), fun h => by rw [h, hp]⟩

/-- **The chain of a tope is all edges**, of the same length as the chain it lies above. -/
theorem faceChain_dims {a : Ch (□n)} (T : TopeOver a) :
    (faceChain (topeFace T)).cubes.map (·.1) = 𝟙^(dimSum a.dims) := by
  have hbead : ∀ i, (bead (blockMap (signHeight T.1)) (blockMap_surjective _) i).1 = (1 : ℕ+) :=
    fun i => PNat.coe_injective (tope_block_card T i)
  change (List.ofFn (bead (blockMap (signHeight (topeFace T).1))
    (blockMap_surjective _))).map (·.1) = _
  rw [List.map_ofFn]
  rw [show ((·.1) ∘ bead (blockMap (signHeight (topeFace T).1)) (blockMap_surjective _))
      = fun _ => (1 : ℕ+) from funext hbead]
  have hk : numBlocks (signHeight (topeFace T).1) = dimSum a.dims :=
    (numBlocks_tope T).trans (dimSum_dims a).symm
  rw [List.ofFn_const, hk]

/-! ## Part 3 — the run of a tope -/

/-- The chain of the tope, as an object of `Ch (□ⁿ)`. -/
def topeCh {a : Ch (□n)} (T : TopeOver a) : Ch (□n) :=
  refineToWedgeObj (faceChain (topeFace T))

theorem faceLE_topeCh {a : Ch (□n)} (T : TopeOver a) :
    braidSign (covectorHeight (wedgeToRefineObj a))
      ⊑ braidSign (covectorHeight (faceChain (topeFace T))) := by
  rw [braidSign_covectorHeight_faceChain]
  exact T.2.2

/-- **The tope's chain refines `a`** — `chainRefineOfFaceLE`, packaged as a `Ch` morphism. -/
def topeChHom {a : Ch (□n)} (T : TopeOver a) : topeCh T ⟶ a :=
  (refineToWedge (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)).map
      (chainRefineOfFaceLE (wedgeToRefineObj a) (faceChain (topeFace T)) (faceLE_topeCh T))
    ≫ eqToHom (refineToWedgeObj_wedgeToRefineObj a)

theorem topeCh_dims {a : Ch (□n)} (T : TopeOver a) :
    (topeCh T).dims = (faceChain (topeFace T)).cubes.map (·.1) := rfl

/-- **Tope ↦ run.**  The tope's chain is already all edges, and it carries its own dimension
sequence — so this is `topeChHom` repackaged, with no reindexing. -/
def toRun {a : Ch (□n)} (T : TopeOver a) : Run (⋁a.dims) :=
  ⟨⟨(topeCh T).dims, (topeChHom T).φ⟩, fun d hd =>
    List.eq_of_mem_replicate (by rw [← faceChain_dims T]; exact hd)⟩

/-! ## Part 4 — the two round trips

`a.map` is a mono, so a run is determined by the chain it traces out. -/

/-- `□ⁿ`'s descent maps are monomorphisms. -/
theorem chain_map_mono (a : Ch (□n)) : Mono a.map.hom :=
  descent_mono (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n) a

/-- **Runs are determined by the chain they trace out.**  `runChain a` is `Run.pushforward a.map`,
and `a.map` is a mono, so it is injective on objects — a run's dimension sequence is read off the
traced chain and its map is then cancelled. -/
theorem run_ext {a : Ch (□n)} {r s : Run (⋁a.dims)} (h : runChain a r = runChain a s) : r = s := by
  haveI := chain_map_mono a
  obtain ⟨hd, hm⟩ := ChainCat.Obj.eq_mk_iff h
  refine Run.ext (ChainCat.Obj.mk_eq_mk hd ?_)
  have hm' : r.map ≫ a.map = (⋁≡hd ≫ s.map) ≫ a.map := hm.trans (Category.assoc _ _ _).symm
  have h' := congrArg BPSet.Hom.hom hm'
  rw [comp_hom, comp_hom] at h'
  exact BPSet.hom_ext ((cancel_mono a.map.hom).mp h')

/-- The chain traced out by the run of a tope is the tope's own chain — `topeChHom`'s triangle,
with nothing else to say. -/
theorem runChain_toRun {a : Ch (□n)} (T : TopeOver a) :
    runChain a (toRun T) = topeCh T :=
  congrArg (ChainCat.Obj.mk (topeCh T).dims) (topeChHom T).w

/-- **Round trip: tope → run → tope.** -/
theorem ofRun_toRun (a : Ch (□n)) (T : TopeOver a) :
    ofRun a (toRun T) = T := by
  apply Subtype.ext
  change braidSign (chCovectorHeight (runChain a (toRun T))) = T.1
  rw [runChain_toRun T]
  change braidSign (covectorHeight (wedgeToRefineObj
    (refineToWedgeObj (faceChain (topeFace T))))) = T.1
  rw [wedgeToRefineObj_refineToWedgeObj]
  exact braidSign_covectorHeight_faceChain (topeFace T)

/-- The tope's chain, for the tope of a run, is the run's own chain. -/
theorem topeCh_ofRun (a : Ch (□n)) (r : Run (⋁a.dims)) :
    topeCh (ofRun a r) = runChain a r := by
  change refineToWedgeObj (faceChain (topeFace (ofRun a r))) = _
  rw [show faceChain (topeFace (ofRun a r)) = wedgeToRefineObj (runChain a r) from
    chainOf_blockMap_signHeight (wedgeToRefineObj (runChain a r))]
  exact refineToWedgeObj_wedgeToRefineObj (runChain a r)

/-- **Round trip: run → tope → run.**  Both round trips are now the same two facts composed. -/
theorem toRun_ofRun (a : Ch (□n)) (r : Run (⋁a.dims)) : toRun (ofRun a r) = r :=
  run_ext ((runChain_toRun (ofRun a r)).trans (topeCh_ofRun a r))

/-! ## Part 5 — the objectwise bijection -/

/-- **Runs refining `a` are the topes above `a`'s covector.** -/
def runTopeEquiv (a : Ch (□n)) : Run (⋁a.dims) ≃ TopeOver a where
  toFun := ofRun a
  invFun := toRun
  left_inv := toRun_ofRun a
  right_inv := ofRun_toRun a

/-! ## Part 6 — the naturality law, reduced to its bead-local half

Naturality of `runTopeEquiv` is the Salvetti wall-crossing law: restricting a run along a
subdivision `f : a ⟶ b` composes the finer covector into the run's tope.  Across two blocks of `a`
the law is the face order the restricted run already satisfies (`faceLE_runHeight`); within a block
of `a` it says the restriction *preserves the relative order of `r`*, which is a statement about
`runRestrict` alone. -/

/-- Across distinct blocks of `a`, a restricted run reproduces `a`'s own covector — it refines
`a`, and `faceLE` transfers strict signs. -/
theorem wallCrossing_cross_block {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (e : BraidGround n) (hne : chCovectorHeight a e.1.1 ≠ chCovectorHeight a e.1.2) :
    braidSign (runHeight a (runRestrict f.φ r)) e
      = braidSign (chCovectorHeight a) e := by
  have h := (faceLE_braidSign_iff (chCovectorHeight a)
      (runHeight a (runRestrict f.φ r))).mp
    (faceLE_runHeight a (runRestrict f.φ r)) e
    ((braidSign_ne_zero_iff (chCovectorHeight a) e).mpr hne)
  exact h.symm

/-- **Wall crossing from the bead-local law.**  Given that restriction preserves the relative
order of the run inside each block of `a`, the tope of the restricted run is the Salvetti
composite — which is exactly naturality of `runTopeEquiv`. -/
theorem wallCrossing_of_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (hsame : ∀ e : BraidGround n, chCovectorHeight a e.1.1 = chCovectorHeight a e.1.2 →
      sign (runHeight a (runRestrict f.φ r) e.1.1
            - runHeight a (runRestrict f.φ r) e.1.2)
        = sign (runHeight b r e.1.1 - runHeight b r e.1.2)) :
    braidSign (runHeight a (runRestrict f.φ r))
      = braidSign (chCovectorHeight a) ⊙ braidSign (runHeight b r) := by
  funext e
  change _ = if braidSign (chCovectorHeight a) e = 0 then braidSign (runHeight b r) e
    else braidSign (chCovectorHeight a) e
  by_cases hz : braidSign (chCovectorHeight a) e = 0
  · rw [if_pos hz, braidSign_apply, braidSign_apply]
    exact hsame e ((braidSign_zero_iff (chCovectorHeight a) e).mp hz)
  · rw [if_neg hz]
    exact wallCrossing_cross_block f r e ((braidSign_ne_zero_iff (chCovectorHeight a) e).mp hz)

end CubeChains
