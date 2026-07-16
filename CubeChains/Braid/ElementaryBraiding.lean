import CubeChains.Braid.CubeIso
import CubeChains.Braid.Artin

/-!
# Braid/ElementaryBraiding — the elementary braiding step (WIP)

Two runs of `□n` differing by swapping the events at adjacent positions `j, j+1` are joined by a
canonical iso of `ConcGrpd (□n)` whose braid is the adjacent transposition `ofPerm (adjT j)`.
-/

open CategoryTheory Opposite CubeChain StdCube Equiv

namespace CubeChains

variable {K : BPSet}

/-! ## Polymorphic chambers -/

/-- The chamber of `□ᵈ` given by the natural order `<` on directions. -/
def natChamber (d : ℕ) : Chamber d where
  lt a b := a < b
  decLt a b := inferInstanceAs (Decidable (a < b))
  sto := inferInstanceAs (IsStrictTotalOrder (Fin d) (· < ·))

/-- The chamber of `□ᵈ` given by the reversed order `>` on directions. -/
def revChamber (d : ℕ) : Chamber d where
  lt a b := b < a
  decLt a b := inferInstanceAs (Decidable (b < a))
  sto := inferInstanceAs (IsStrictTotalOrder (Fin d) (· > ·))

/-! ## The run frame counts beads

For a run every bead is a singleton, so the `evKey` rank of an event is just its bead index. -/

theorem chamberRank_trivial {d : ℕ} (hd : d ≤ 1) (i : Fin d) :
    chamberRank (Chamber.trivial hd) i = 0 := by
  classical
  simp only [chamberRank]
  norm_cast
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  exact not_false

/-- On a run, `evKey` is just the bead index: the chamber-rank component vanishes. -/
theorem evKey_runLine {r : Ch K} (h : IsRun r) (x : EventObj r) :
    evKey (runLine r h) x = toLex (((x.1 : ℕ)), (0 : ℤ)) := by
  rw [evKey, show (runLine r h) x.1 = Chamber.trivial (le_of_eq (h x.1)) from rfl,
    chamberRank_trivial]

/-- **The run frame is the bead order.**  For a run, the `keyRank` of an event equals its bead
index: every bead is a singleton, so exactly the `x.1.val` earlier events precede it. -/
theorem keyRank_runLine {r : Ch K} (h : IsRun r) (x : EventObj r) :
    keyRank (evKey (runLine r h)) x = (x.1 : ℕ) := by
  classical
  have hpred : ∀ y : EventObj r, (evKey (runLine r h) y < evKey (runLine r h) x)
      ↔ (y.1 : ℕ) < (x.1 : ℕ) := by
    intro y
    rw [evKey_runLine, evKey_runLine, Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro (h1 | ⟨_, h2⟩)
      · exact h1
      · exact absurd h2 (lt_irrefl _)
    · exact fun h1 => Or.inl h1
  have hpos : ∀ i : ChainCat.Bead r, 0 < ChainCat.beadDim r i := fun i => by rw [h i]; norm_num
  rw [keyRank]
  simp only [hpred]
  conv_rhs => rw [← Fin.card_Iio x.1]
  refine Finset.card_bij' (fun y _ => y.1) (fun i _ => (⟨i, ⟨0, hpos i⟩⟩ : EventObj r)) ?_ ?_ ?_ ?_
  · intro y hy
    exact Finset.mem_Iio.mpr (Fin.lt_def.mpr (Finset.mem_filter.mp hy).2)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.lt_def.mp (Finset.mem_Iio.mp hi)⟩
  · intro y _
    obtain ⟨i, δ⟩ := y
    haveI : Subsingleton (Fin (ChainCat.beadDim r i)) :=
      Fin.subsingleton_iff_le_one.mpr (le_of_eq (h i))
    exact congrArg (Sigma.mk i) (Subsingleton.elim _ δ)
  · intro i _
    rfl

/-! ## The event permutation of a sequentialization morphism

`seqMor x M` refines `x` into the run `seqChain M` for *any* line `M` of `x.chain` (the chamber
condition is free — the target is a run).  Its event permutation reads `x`'s frame through `M`'s. -/

/-- Refine `x` into the run `seqChain M`, along an arbitrary line `M` of `x.chain`. -/
def seqMor (x : ConcCat K) (M : LinesObj x.chain) :
    x ⟶ runExec (seqChain M) (seqChain_isRun M) :=
  ⟨(seqRefine M).op, @Subsingleton.elim _ (linesObj_subsingleton (seqChain_isRun M)) _ _⟩

/-- **The event permutation of a sequentialization.**  In `x`'s own frame it is the composite
`(evIdx' x)⁻¹ ; keyEquiv (evKey M)`: position `k` goes to the `M`-rank of the event at `k`. -/
theorem evPerm'_seqMor (x : ConcCat K) (M : LinesObj x.chain) :
    evPerm' (seqMor x M) = (evIdx' x).symm.trans (keyEquiv (evKey M) (evKey_injective M)) := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  set pr := prefine (seqBeta M) (seqBeta_surjective M) (seqBeta_mono M) with hpr
  have hev : eventMap pr ((eventEquiv pr).symm ((evIdx' x).symm k)) = (evIdx' x).symm k := by
    change (eventEquiv pr) ((eventEquiv pr).symm ((evIdx' x).symm k)) = _
    exact Equiv.apply_symm_apply _ _
  have hL : (evPerm' (seqMor x M) k : ℕ)
      = (((eventEquiv pr).symm ((evIdx' x).symm k)).1 : ℕ) := by
    rw [evPerm']
    simp only [Equiv.trans_apply]
    rw [finCongr_symm, finCongr_apply, Fin.coe_cast]
    exact keyRank_runLine (seqChain_isRun M) _
  have hR : (((evIdx' x).symm.trans (keyEquiv (evKey M) (evKey_injective M))) k : ℕ)
      = (((eventEquiv pr).symm ((evIdx' x).symm k)).1 : ℕ) := by
    have hb := beta_eventMap (seqBeta M) (seqBeta_surjective M) (seqBeta_mono M)
      ((eventEquiv pr).symm ((evIdx' x).symm k))
    rw [hev] at hb
    rw [Equiv.trans_apply]
    exact hb
  rw [hL]
  exact hR.symm

/-- Sequentializing along `x`'s own line has trivial event permutation. -/
theorem evPerm'_seqMor_self (x : ConcCat K) : evPerm' (seqMor x x.line) = 1 := by
  rw [evPerm'_seqMor]
  exact Equiv.symm_trans_self (evIdx' x)

/-! ## Reindexing a key frame

Precomposing the key by a bijection `σ` composes the frame with `σ`; conjugating two frames that
differ by a value-swap on two events yields the transposition of their two ranks. -/

/-- `keyEquiv (f ∘ σ) = σ ; keyEquiv f`: a relabelling of the underlying set relabels the frame. -/
theorem keyEquiv_comp_equiv {α : Type} [Fintype α] {γ : Type} [LinearOrder γ]
    (f : α → γ) (hf : Function.Injective f) (σ : α ≃ α)
    (hfσ : Function.Injective (fun a => f (σ a))) :
    keyEquiv (fun a => f (σ a)) hfσ = σ.trans (keyEquiv f hf) := by
  classical
  apply Equiv.ext
  intro e
  apply Fin.ext
  change keyRank (fun a => f (σ a)) e = keyRank f (σ e)
  rw [keyRank, keyRank]
  refine Finset.card_bij' (fun y _ => σ y) (fun z _ => σ.symm z) ?_ ?_ ?_ ?_
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  · intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa using (Finset.mem_filter.mp hz).2
  · intro y _; simp
  · intro z _; simp

open scoped Classical in
/-- **Two frames differing by an event-swap are the transposition of the two ranks.**  If `evKey L'`
is `evKey L` precomposed with the swap of `e0, e1`, then the frame change `(L)⁻¹ ; (L')` is the
transposition of the two positions `L` assigns to `e0` and `e1`. -/
theorem frame_swap_of_evKey {a : Ch K} (L L' : LinesObj a) (e0 e1 : EventObj a)
    (hkey : ∀ e, evKey L' e = evKey L (Equiv.swap e0 e1 e)) :
    (keyEquiv (evKey L) (evKey_injective L)).symm.trans
        (keyEquiv (evKey L') (evKey_injective L'))
      = Equiv.swap (keyEquiv (evKey L) (evKey_injective L) e0)
          (keyEquiv (evKey L) (evKey_injective L) e1) := by
  set KL := keyEquiv (evKey L) (evKey_injective L) with hKLdef
  have hKL' : ∀ e, keyEquiv (evKey L') (evKey_injective L') e = KL (Equiv.swap e0 e1 e) := by
    intro e
    apply Fin.ext
    change keyRank (evKey L') e = keyRank (evKey L) (Equiv.swap e0 e1 e)
    rw [keyRank, keyRank]
    refine Finset.card_bij' (fun y _ => Equiv.swap e0 e1 y) (fun z _ => Equiv.swap e0 e1 z)
      ?_ ?_ ?_ ?_
    · intro y hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := (Finset.mem_filter.mp hy).2
      rw [hkey y, hkey e] at h
      exact h
    · intro z hz
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := (Finset.mem_filter.mp hz).2
      rw [hkey (Equiv.swap e0 e1 z), hkey e, Equiv.swap_apply_self]
      exact h
    · intro y _; simp
    · intro z _; simp
  have hconj : ∀ x, KL (Equiv.swap e0 e1 x) = Equiv.swap (KL e0) (KL e1) (KL x) := by
    intro x
    by_cases h0 : x = e0
    · subst h0; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases h1 : x = e1
      · subst h1; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · have hk0 : KL x ≠ KL e0 := fun h => h0 (KL.injective h)
        have hk1 : KL x ≠ KL e1 := fun h => h1 (KL.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1, Equiv.swap_apply_of_ne_of_ne hk0 hk1]
  apply Equiv.ext
  intro k
  rw [Equiv.trans_apply, hKL', hconj, Equiv.apply_symm_apply]

/-! ## The elementary braiding iso and its braid -/

variable {n : ℕ}

/-- **The elementary braiding iso.**  In `ConcGrpd (□n)`, the two runs obtained by sequentializing
`x` along its own line and along `L'` are canonically isomorphic, via `x`. -/
noncomputable def elemBraid (x : ConcCat (□n)) (L' : LinesObj x.chain) :
    (FreeGroupoid.mk (runExec (seqChain x.line) (seqChain_isRun x.line)) : ConcGrpd (□n))
      ≅ FreeGroupoid.mk (runExec (seqChain L') (seqChain_isRun L')) :=
  (asIso (FreeGroupoid.homMk (seqMor x x.line))).symm ≪≫
    asIso (FreeGroupoid.homMk (seqMor x L'))

set_option maxHeartbeats 1000000 in
-- `braidHom b` is `SigmaHom.mk b`; reducing the `endBraid` match through `strands` is defeq-heavy.
/-- `endBraid` inverts `braidHom`. -/
theorem endBraid_braidHom {a : ℕ} (b : Braid a) : endBraid (braidHom b) = b := rfl

/-- The braid of `elemBraid x L'`, read through the strand-count recasts.  The `x.line` leg is
trivial (`evPerm' = 1`), so only `L'`'s event permutation survives. -/
theorem braidGrpd_map_elemBraid (x : ConcCat (□n)) (L' : LinesObj x.chain) :
    (braidGrpd (□n)).map (elemBraid x L').hom
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm
        ≫ braidHom (ofPerm (evPerm' (seqMor x L')))
        ≫ eqToHom (congrArg strands (nEvents_eq (seqMor x L'))) := by
  have ha : (braidGrpd (□n)).map (FreeGroupoid.homMk (seqMor x x.line))
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))) := by
    rw [braidGrpd_homMk, evPerm'_seqMor_self, ofPerm_one]
    exact Category.id_comp _
  have hinv : (braidGrpd (□n)).map (inv (FreeGroupoid.homMk (seqMor x x.line)))
      = eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm := by
    rw [Functor.map_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [ha]
    simp
  have hkey : (elemBraid x L').hom
      = inv (FreeGroupoid.homMk (seqMor x x.line)) ≫ FreeGroupoid.homMk (seqMor x L') := by
    rw [elemBraid, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
  rw [hkey, Functor.map_comp, hinv]
  exact congrArg (fun m => eqToHom (congrArg strands (nEvents_eq (seqMor x x.line))).symm ≫ m)
    (braidGrpd_homMk (seqMor x L'))

open scoped Classical in
/-- **The elementary braiding lemma, at the permutation level.**  If `L'` is `x`'s line with the two
concurrent events `e0, e1` swapped, then the event permutation of `elemBraid x L'` is the
transposition of their two positions — the braid of `elemBraid x L'` is `ofPerm (Equiv.swap ..)`.

For adjacent positions `j, j+1` (`evIdx' x e0 = j`, `evIdx' x e1 = j+1`) this transposition is
`adjT j`, so the braid is `ofPerm (adjT j)`: concurrency **is** braiding. -/
theorem evPerm'_elemBraid {n : ℕ} (x : ConcCat (□n)) (L' : LinesObj x.chain)
    (e0 e1 : EventObj x.chain) (hkey : ∀ e, evKey L' e = evKey x.line (Equiv.swap e0 e1 e)) :
    evPerm' (seqMor x L') = Equiv.swap (evIdx' x e0) (evIdx' x e1) := by
  rw [evPerm'_seqMor]
  exact frame_swap_of_evKey x.line L' e0 e1 hkey

end CubeChains
