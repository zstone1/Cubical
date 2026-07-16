import CubeChains.Braid.Surjectivity
import CubeChains.Braid.ChGrading
import CubeChains.Foundations.Terminal

/-!
# Braid/TerminalSurj — the concurrency braid map on the terminal `Zbp` is onto the whole `Bₙ`

On `□n` purity confines the vertex-group image to `Pₙ`.  On the terminal `Zbp` there is no
refinement-invariant axis name, so the single `[n]`-bead's `n!` refinements to the run realise
*every* permutation braid `ofPerm σ`, and those generate all of `Braid n` — no Schreier climb.

The key terminal fact: any two `Ch Zbp` with the same `dims` are equal (`Zbp` is terminal, so
the wedge map is forced), hence all `n!` runs `seqChain L` coincide as *one* object.  A refinement
`bₙ ⟶ run` therefore closes up into a loop at the run, whose braid is `ofPerm σ`.
-/

open CategoryTheory Opposite Equiv

namespace CubeChains

/-! ## `Zbp` is terminal: chains with equal dims coincide -/

/-- Every bi-pointed map into `Zbp` is forced: `Zbp` is terminal (a single vertex in each dim). -/
instance Zbp_hom_subsingleton (X : BPSet) : Subsingleton (X ⟶ Zbp) :=
  ⟨fun f g => BPSet.hom_ext (isTerminalZ.hom_ext f.hom g.hom)⟩

/-- **Terminal extensionality.**  Two chains of `Zbp` with the same dimension sequence are equal:
the classifying wedge map is forced. -/
theorem chZbp_ext {a b : Ch Zbp} (h : a.dims = b.dims) : a = b := by
  obtain ⟨da, ma⟩ := a
  obtain ⟨db, mb⟩ := b
  obtain rfl : da = db := h
  rw [Subsingleton.elim ma mb]

/-! ## Runs have all-`1` dims of length the event count -/

variable {K : BPSet}

/-- A run's dimension sequence is all `1`s. -/
theorem run_dims_eq_replicate {r : Ch K} (h : IsRun r) :
    r.dims = List.replicate r.dims.length 1 :=
  List.eq_replicate_of_mem fun b hb => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hb1 : (r.dims[i] : ℕ) = 1 := h ⟨i, hi⟩
    exact Subtype.ext hb1

/-- A run has one bead per event: its dimension length is the event count. -/
theorem run_card_length {r : Ch K} (h : IsRun r) :
    Fintype.card (EventObj r) = r.dims.length := by
  rw [show Fintype.card (EventObj r)
        = Fintype.card (Σ i : ChainCat.Bead r, Fin (ChainCat.beadDim r i)) from rfl,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- **All runs of a `Zbp`-chain coincide.**  The sequentialisations along any two lines have equal
dims (all `1`s, of length the shared event count) so are the same chain. -/
theorem seqChain_eq_terminal (a : Ch Zbp) (L L' : LinesObj a) : seqChain L = seqChain L' := by
  apply chZbp_ext
  rw [run_dims_eq_replicate (seqChain_isRun L), run_dims_eq_replicate (seqChain_isRun L'),
    ← run_card_length (seqChain_isRun L), ← run_card_length (seqChain_isRun L'),
    card_eventObj_eq_of_hom (seqRefine L), card_eventObj_eq_of_hom (seqRefine L')]

/-- `runExec` transports along an equality of chains (the run line is forced). -/
theorem runExec_congr {a a' : Ch K} (h : a = a') (ha : IsRun a) (ha' : IsRun a') :
    runExec a ha = runExec a' ha' := by subst h; rfl

/-! ## The elementary braiding iso and its braid, for a general `K`

`elemBraid`/`braidGrpd_map_elemBraid`/`readBraid_map_elemBraid` are stated for `□n` but use only
general-`K` machinery; here are the `K`-general versions. -/

/-- The two runs obtained by sequentialising `x` along its own line and along `L'` are canonically
isomorphic, via `x`. -/
noncomputable def elemBraidGen (x : ConcCat K) (L' : LinesObj x.chain) :
    (FreeGroupoid.mk (runExec (seqChain x.line) (seqChain_isRun x.line)) : ConcGrpd K)
      ≅ FreeGroupoid.mk (runExec (seqChain L') (seqChain_isRun L')) :=
  (asIso (FreeGroupoid.homMk (seqMor x x.line))).symm ≪≫
    asIso (FreeGroupoid.homMk (seqMor x L'))

/-- The braid of `elemBraidGen x L'`, through the strand recasts: only `L'`'s event
permutation survives (the `x.line` leg is trivial). -/
theorem braidGrpd_map_elemBraidGen (x : ConcCat K) (L' : LinesObj x.chain) :
    (braidGrpd K).map (elemBraidGen x L').hom
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm
        ≫ braidHom (ofPerm (evPerm' (seqMor x L')))
        ≫ eqToHom (congrArg strands (nEvents_eq (seqMor x L'))) := by
  have ha : (braidGrpd K).map (FreeGroupoid.homMk (seqMor x x.line))
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))) := by
    rw [braidGrpd_homMk, evPerm'_seqMor_self, ofPerm_one]
    exact Category.id_comp _
  have hinv : (braidGrpd K).map (inv (FreeGroupoid.homMk (seqMor x x.line)))
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm := by
    rw [Functor.map_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [ha]
    simp
  have hkey : (elemBraidGen x L').hom
      = inv (FreeGroupoid.homMk (seqMor x x.line)) ≫ FreeGroupoid.homMk (seqMor x L') := by
    rw [elemBraidGen, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  rw [hkey, Functor.map_comp, hinv]
  exact congrArg (fun m => eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm ≫ m)
    (braidGrpd_homMk (seqMor x L'))

/-- The braid of `elemBraidGen x L'`, collapsed to `Braid m`: the recasts vanish. -/
theorem readBraid_map_elemBraidGen (x : ConcCat K) (L' : LinesObj x.chain) {m : ℕ}
    (hx : nEvents x = m) :
    (readBraid m).map ((braidGrpd K).map (elemBraidGen x L').hom)
      = braidCast hx (ofPerm (evPerm' (seqMor x L'))) := by
  rw [braidGrpd_map_elemBraidGen]
  erw [Functor.map_comp, Functor.map_comp, readBraid_map_eqToHom, readBraid_map_eqToHom,
    readBraid_map_braidHom]
  rw [braidSelfHom_eq m hx]
  erw [Category.id_comp, Category.comp_id]

/-- `readBraid` kills a `braidGrpd`-image of an `eqToHom` (an object recast). -/
theorem readBraid_braidGrpd_eqToHom {X Y : ConcGrpd K} (h : X = Y) (m : ℕ) :
    (readBraid m).map ((braidGrpd K).map (eqToHom h)) = 𝟙 _ := by
  rw [eqToHom_map]; exact readBraid_map_eqToHom m _

/-! ## The vertex-group map of `braidGrpd K`, landing in the whole `Braid (nEvents x)` -/

/-- **The concurrency braid of a loop.**  The vertex-group map of `braidGrpd K`, into the *whole*
braid group `Braid (nEvents x)` (no purity restriction — `K` need not be a cube). -/
noncomputable def concBraidHomGen (x : ConcCat K) :
    ConcBraid K x →* Braid (nEvents x) :=
  (autStrandsBraid (nEvents x)).toMonoidHom.comp ((braidGrpd K).mapAut (FreeGroupoid.mk x))

@[simp] theorem concBraidHomGen_apply (x : ConcCat K) (a : ConcBraid K x) :
    concBraidHomGen x a = endBraid ((braidGrpd K).map a.hom) := rfl

/-! ## The terminal basepoint `bₙ` and its run `R` -/

section Basepoint

variable (n : ℕ) (hn : 0 < n)

/-- The single-`[n]`-bead chain of `Zbp` (the map into `Zbp` is forced). -/
def cZn : Ch Zbp := ⟨[⟨n, hn⟩], ⟨toZ _, rfl, rfl⟩⟩

/-- The **coarse basepoint**: the single-`[n]`-bead execution with the standard event order. -/
def bZ : ConcCat Zbp := ⟨op (cZn n hn), stdLine _⟩

@[simp] theorem bZ_chain : (bZ n hn).chain = cZn n hn := rfl

theorem dimSum_cZn : dimSum (cZn n hn) = n := by
  change ((cZn n hn).dims.map (fun d : ℕ+ => (d : ℕ))).sum = n
  simp [cZn]

theorem nEvents_bZ : nEvents (bZ n hn) = n := by
  change Fintype.card (EventObj (bZ n hn).chain) = n
  rw [eventObj_card]
  exact dimSum_cZn n hn

/-- The **run basepoint**: the sequentialisation of `bₙ` (one object; all `n!` runs coincide). -/
def RZ : ConcCat Zbp := runExec (seqChain (bZ n hn).line) (seqChain_isRun (bZ n hn).line)

theorem hxZ : nEvents (bZ n hn) = nEvents (RZ n hn) :=
  nEvents_eq (seqMor (bZ n hn) (bZ n hn).line)

theorem nEvents_RZ : nEvents (RZ n hn) = n := (hxZ n hn).symm.trans (nEvents_bZ n hn)

/-! ### Every event order is realised by a line of the single bead -/

open scoped Classical in
/-- **Every event order is a line's key order.**  `L' ↦ keyEquiv (evKey L')` is onto the bijections
`EventObj bₙ.chain ≃ Fin (card)` — the single `[n]`-bead realises every permutation. -/
theorem keyEquiv_surjective_Z :
    Function.Surjective (fun L' : LinesObj (bZ n hn).chain =>
        keyEquiv (evKey L') (evKey_injective L')) := by
  classical
  haveI hlen : ((bZ n hn).chain).dims.length = 1 := rfl
  haveI hss : Subsingleton (ChainCat.Bead (bZ n hn).chain) :=
    Fin.subsingleton_iff_le_one.mpr (le_of_eq hlen)
  haveI hinh : Inhabited (ChainCat.Bead (bZ n hn).chain) := ⟨⟨0, by rw [hlen]; norm_num⟩⟩
  intro τ
  have hinj : ∀ i : ChainCat.Bead (bZ n hn).chain,
      Function.Injective
        (fun δ : Fin (ChainCat.beadDim (bZ n hn).chain i) => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) := by
    intro i a b hab
    have h1 : (⟨i, a⟩ : EventObj (bZ n hn).chain) = ⟨i, b⟩ :=
      τ.injective (Fin.ext (Nat.cast_injective hab))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  refine ⟨fun i => chamberOfInj (fun δ => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) (hinj i), ?_⟩
  set L' : LinesObj (bZ n hn).chain :=
    fun i => chamberOfInj (fun δ => ((τ ⟨i, δ⟩ : ℕ) : ℤ)) (hinj i) with hL'
  have horder : ∀ e' e : EventObj (bZ n hn).chain,
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

/-- **The transports realise every permutation.**  `L' ↦ evPerm' (seqMor bₙ L')` is onto
`Perm (Fin (nEvents bₙ))`. -/
theorem transport_surjective_Z :
    Function.Surjective (fun L' : LinesObj (bZ n hn).chain => evPerm' (seqMor (bZ n hn) L')) := by
  intro π
  obtain ⟨L', hL'⟩ := keyEquiv_surjective_Z n hn ((evIdx' (bZ n hn)).trans π)
  have hL'' : keyEquiv (evKey (a := (bZ n hn).chain) L') (evKey_injective L')
      = (evIdx' (bZ n hn)).trans π := hL'
  refine ⟨L', ?_⟩
  have key : evPerm' (seqMor (bZ n hn) L') = π := by
    rw [evPerm'_seqMor, hL'']
    apply Equiv.ext
    intro k
    exact (Equiv.trans_apply _ _ _).trans
      ((Equiv.trans_apply _ _ _).trans (congrArg π (Equiv.apply_symm_apply _ _)))
  exact key

/-! ## The loops `L_σ` and their braids -/

/-- All runs coincide: `run L = R`. -/
theorem runL_eq_RZ (L : LinesObj (bZ n hn).chain) :
    runExec (seqChain L) (seqChain_isRun L) = RZ n hn :=
  runExec_congr (seqChain_eq_terminal (bZ n hn).chain L (bZ n hn).line)
    (seqChain_isRun L) (seqChain_isRun (bZ n hn).line)

/-- **The loop `L_σ`**: refine `bₙ` to the run via `L` (out), then identify with `R` (back via id).
On `Zbp` the two runs are the same object, so this is a genuine loop at `R`. -/
noncomputable def loopZ (L : LinesObj (bZ n hn).chain) : ConcBraid Zbp (RZ n hn) :=
  elemBraidGen (bZ n hn) L ≪≫ eqToIso (congrArg FreeGroupoid.mk (runL_eq_RZ n hn L))

/-- **The braid of the loop `L_σ` is `ofPerm σ`** (read in the run's frame).  Kept parametric in the
execution `x`: the concrete run is never unfolded, so `nEvents (run x.line)` stays opaque and no
strand-count `whnf` blowup occurs (as in `concPureBraidHom_surjective_of_lines`). -/
theorem concBraidHomGen_loop_general (x : ConcCat K) (L' : LinesObj x.chain) {m : ℕ}
    (hx : nEvents x = m)
    (hR : nEvents (runExec (seqChain x.line) (seqChain_isRun x.line)) = m)
    (hco : runExec (seqChain L') (seqChain_isRun L')
         = runExec (seqChain x.line) (seqChain_isRun x.line)) :
    concBraidHomGen (runExec (seqChain x.line) (seqChain_isRun x.line))
        (elemBraidGen x L' ≪≫ eqToIso (congrArg FreeGroupoid.mk hco))
      = ofPerm ((finCongr (hx.trans hR.symm)).permCongr (evPerm' (seqMor x L'))) := by
  have hread : (readBraid m).map ((braidGrpd K).map
        (elemBraidGen x L' ≪≫ eqToIso (congrArg FreeGroupoid.mk hco)).hom)
      = braidCast hx (ofPerm (evPerm' (seqMor x L'))) := by
    rw [Iso.trans_hom, eqToIso.hom, Functor.map_comp, Functor.map_comp]
    erw [readBraid_map_elemBraidGen x L' hx, readBraid_braidGrpd_eqToHom, Category.comp_id]
  have key : concBraidHomGen (runExec (seqChain x.line) (seqChain_isRun x.line))
        (elemBraidGen x L' ≪≫ eqToIso (congrArg FreeGroupoid.mk hco))
      = braidCast hR.symm ((readBraid m).map ((braidGrpd K).map
          (elemBraidGen x L' ≪≫ eqToIso (congrArg FreeGroupoid.mk hco)).hom)) :=
    endBraid_of_readBraid _ hR
  rw [key, hread, braidCast_trans, braidCast_ofPerm]

/-- **The braid of the loop `L_σ` at the terminal basepoint is `ofPerm σ`.** -/
theorem concBraidHomGen_loopZ (L : LinesObj (bZ n hn).chain) :
    concBraidHomGen (RZ n hn) (loopZ n hn L)
      = ofPerm ((finCongr (hxZ n hn)).permCongr (evPerm' (seqMor (bZ n hn) L))) :=
  concBraidHomGen_loop_general (bZ n hn) L (nEvents_bZ n hn) (nEvents_RZ n hn) (runL_eq_RZ n hn L)

/-! ## Surjectivity onto the whole braid group -/

/-- **The concurrency braid map at the terminal basepoint is onto the whole `Braid (nEvents R)`.**
Every `ofPerm σ` is the braid of a loop `L_σ`, and those generate `Braid (nEvents R)`
(`closure_range_ofPerm`) — no purity, no Schreier. -/
theorem concBraidHomGen_surjective_Z :
    Function.Surjective (concBraidHomGen (RZ n hn)) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_ofPerm (nEvents (RZ n hn)),
    Subgroup.closure_le]
  rintro _ ⟨σ, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_range]
  obtain ⟨L, hL⟩ := transport_surjective_Z n hn ((finCongr (hxZ n hn)).symm.permCongr σ)
  have hL' : evPerm' (seqMor (bZ n hn) L) = (finCongr (hxZ n hn)).symm.permCongr σ := hL
  refine ⟨loopZ n hn L, ?_⟩
  rw [concBraidHomGen_loopZ n hn L, hL', ← Equiv.permCongr_symm,
    Equiv.apply_symm_apply]

/-- **Onto `Braid n`.**  Recast to the fixed strand count `n` (`nEvents R = n`), the map is still
onto — `Zbp` realises the *whole* braid group at its coarse `[n]`-bead basepoint. -/
theorem concBraidHomGen_surjective_Zn :
    Function.Surjective ((braidEqHom (nEvents_RZ n hn)).comp (concBraidHomGen (RZ n hn))) := by
  have hcast : Function.Surjective (braidEqHom (nEvents_RZ n hn)) := fun y =>
    ⟨braidCast (nEvents_RZ n hn).symm y, braidCast_leftInverse (nEvents_RZ n hn).symm y⟩
  rw [MonoidHom.coe_comp]
  exact hcast.comp (concBraidHomGen_surjective_Z n hn)

end Basepoint

end CubeChains
