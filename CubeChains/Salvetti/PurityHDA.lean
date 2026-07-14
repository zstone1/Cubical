import CubeChains.Salvetti.BraidCharacters

/-!
# Salvetti/PurityHDA — purity of the braid functor **is** the global event naming

`BraidCharacters` proves `HasGlobalEventNaming K ⟹ every vertex-group braid of
`Φ = braidFunctor K n` is pure`.  Here is the converse, hence

    HasGlobalEventNaming K  ↔  BraidPure K            (`hasGlobalEventNaming_iff_braidPure`)

Two inputs.

**Lines lift** (`linesRestrict_surjective`).  A coarse bead's directions *are* the fine events
sitting inside it — `eventEquiv` is a bijection for every `K` — so ordering them by the fine line's
`evKey` (bead, then chamber rank) defines a coarse chamber restricting to the fine ones
(`lineLift`).

**Closing the lifted zigzag** (`exists_lineShift`).  A `Ch K` zigzag lifts to a zigzag of
*executions* only up to the line at the far end, so the lift of a loop of chains need not be a loop
of executions.  It is closed by

    (a, L)  --seqRefine L'-->  seq (a,L')  <--seqRefine L'--  (a, L')

— the *same* refinement on both legs (a run has a unique line), so the two event bijections cancel
and the closing zigzag moves no event.  Purity then applies to the closed loop.
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

variable {K : BPSet} {n : ℕ}

/-! ## Chambers from an injective key -/

/-- The chamber ordering the directions by an injective key. -/
def Chamber.ofKey {d : ℕ} {β : Type} [LinearOrder β] (key : Fin d → β)
    (hkey : Function.Injective key) : Chamber d where
  lt p q := key p < key q
  sto :=
    { trichotomous := fun _ _ h1 h2 => hkey (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
      irrefl := fun p => lt_irrefl (key p)
      trans := fun _ _ _ h1 h2 => lt_trans h1 h2 }

@[simp] theorem Chamber.ofKey_lt {d : ℕ} {β : Type} [LinearOrder β] (key : Fin d → β)
    (hkey : Function.Injective key) (p q : Fin d) :
    (Chamber.ofKey key hkey).lt p q = (key p < key q) := rfl

/-! ## `linesRestrict` is surjective

The coarse line induced by a fine one: a direction of a coarse bead names a fine event
(`eventEquiv`), and the fine line's `evKey` totally orders those. -/

/-- The coarse line induced by a line of the finer chain, along `f : a ⟶ b`: order the directions
of a bead of `b` by the `evKey` of the `a`-events they name. -/
noncomputable def lineLift {a b : Ch K} (f : a ⟶ b) (M : LinesObj a) : LinesObj b :=
  fun r => Chamber.ofKey (fun p => evKey M ((eventEquiv f).symm (⟨r, p⟩ : EventObj b)))
    (fun p q hpq => by
      have h1 : (eventEquiv f).symm (⟨r, p⟩ : EventObj b)
          = (eventEquiv f).symm (⟨r, q⟩ : EventObj b) := evKey_injective M hpq
      exact eq_of_heq (congr_arg_heq Sigma.snd ((eventEquiv f).symm.injective h1)))

/-- `lineLift` is a section of `linesRestrict`: the fine bead `i` occupies the directions of
`blockIdx f i` named by its own events, which the coarse key orders by `M i`. -/
theorem linesRestrict_lineLift {a b : Ch K} (f : a ⟶ b) (M : LinesObj a) :
    linesRestrict f (lineLift f M) = M := by
  funext i
  apply Chamber.ext
  funext δ δ'
  have key : ∀ p : Fin (ChainCat.beadDim a i),
      (eventEquiv f).symm
          (⟨blockIdx fᵂ i, faceEmb (blockFace fᵂ i) p⟩ : EventObj b)
        = (⟨i, p⟩ : EventObj a) := by
    intro p
    rw [Equiv.symm_apply_eq]
    rfl
  change (evKey M ((eventEquiv f).symm
        (⟨blockIdx fᵂ i, faceEmb (blockFace fᵂ i) δ⟩ : EventObj b))
      < evKey M ((eventEquiv f).symm
        (⟨blockIdx fᵂ i, faceEmb (blockFace fᵂ i) δ'⟩ : EventObj b)))
    = (M i).lt δ δ'
  rw [key δ, key δ']
  exact propext (evKey_same_bead_lt_iff M i δ δ')

/-- **Every line of a refinement extends to the coarse chain.** -/
theorem linesRestrict_surjective {a b : Ch K} (f : a ⟶ b) :
    Function.Surjective (linesRestrict f) :=
  fun M => ⟨lineLift f M, linesRestrict_lineLift f M⟩

/-! ## Executions with a prescribed event count -/

/-- The execution `(a, L)`, as an object of the `n`-event part. -/
def execAt {a : Ch K} (L : LinesObj a) (h : Fintype.card (EventObj a) = n) : ConcCatN K n :=
  ⟨⟨op a, L⟩, h⟩

/-- The morphism of executions refining the chain along `g` and restricting the line. -/
noncomputable def restrictHom {c a : Ch K} (g : c ⟶ a) {L : LinesObj a} {M : LinesObj c}
    (hM : linesRestrict g L = M) (ha : Fintype.card (EventObj a) = n)
    (hc : Fintype.card (EventObj c) = n) : execAt L ha ⟶ execAt M hc :=
  ObjectProperty.homMk ⟨g.op, hM⟩

@[simp] theorem concRefine_restrictHom {c a : Ch K} (g : c ⟶ a) {L : LinesObj a} {M : LinesObj c}
    (hM : linesRestrict g L = M) (ha : Fintype.card (EventObj a) = n)
    (hc : Fintype.card (EventObj c) = n) :
    concRefine (restrictHom g hM ha hc) = g := rfl

/-! ## The event monodromy of an execution zigzag, on generators -/

theorem EvFrame.inv_eq {n : ℕ} {X Y : EvFrame n} (u : X ⟶ Y) :
    CategoryTheory.inv u = u.symm :=
  IsIso.inv_eq_of_hom_inv_id (u.self_trans_symm)

@[simp] theorem concRhoMap_homMk {x y : ConcCatN K n} (f : x ⟶ y) :
    concRhoMap (FreeGroupoid.homMk f) = (eventEquiv (concRefine f)).symm :=
  FreeGroupoid.lift_map_homMk (concFrameSystem K n) f

@[simp] theorem concRhoMap_id (x : ConcCatN K n) :
    concRhoMap (𝟙 (FreeGroupoid.mk x : ConcGrpdN K n)) = Equiv.refl (EventObj x.obj.chain) :=
  (concRho K n).map_id _

theorem concRhoMap_comp {x y z : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk y)
    (δ : (FreeGroupoid.mk y : ConcGrpdN K n) ⟶ FreeGroupoid.mk z) :
    concRhoMap (γ ≫ δ) = (concRhoMap γ).trans (concRhoMap δ) :=
  (concRho K n).map_comp γ δ

theorem concRhoMap_inv {x y : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk y) :
    concRhoMap (CategoryTheory.inv γ) = (concRhoMap γ).symm := by
  change (concRho K n).map (CategoryTheory.inv γ) = _
  rw [Functor.map_inv, EvFrame.inv_eq]
  rfl

/-! ## Changing the line of a chain moves no event -/

/-- The sequentialization of `L'`, as an `n`-event execution. -/
noncomputable def seqExecAt {a : Ch K} (L' : LinesObj a) (h : Fintype.card (EventObj a) = n) :
    ConcCatN K n :=
  execAt (runLine (seqChain L') (seqChain_isRun L'))
    ((card_eventObj_eq_of_hom (seqRefine L')).trans h)

/-- `(a, L)` sequentialized along a possibly *different* line `L'` (the target's line is forced: a
run has only one). -/
noncomputable def seqHomAt {a : Ch K} (L L' : LinesObj a) (h : Fintype.card (EventObj a) = n) :
    execAt L h ⟶ seqExecAt L' h :=
  restrictHom (seqRefine L')
    (@Subsingleton.elim _ (linesObj_subsingleton (seqChain_isRun L')) _ _) h _

@[simp] theorem concRefine_seqHomAt {a : Ch K} (L L' : LinesObj a)
    (h : Fintype.card (EventObj a) = n) :
    concRefine (seqHomAt L L' h) = seqRefine L' := rfl

/-- **Two lines of one chain are linked by an event-preserving zigzag.**  Both executions sequence
into the *same* run by the *same* refinement, so the two event bijections cancel. -/
theorem exists_lineShift {a : Ch K} (L L' : LinesObj a) (h : Fintype.card (EventObj a) = n) :
    ∃ ε : (FreeGroupoid.mk (execAt L h) : ConcGrpdN K n) ⟶ FreeGroupoid.mk (execAt L' h),
      concRhoMap ε = Equiv.refl (EventObj a) := by
  refine ⟨FreeGroupoid.homMk (seqHomAt L L' h)
    ≫ CategoryTheory.inv (FreeGroupoid.homMk (seqHomAt L' L' h)), ?_⟩
  rw [concRhoMap_comp, concRhoMap_inv, concRhoMap_homMk, concRhoMap_homMk,
    concRefine_seqHomAt, concRefine_seqHomAt, Equiv.symm_symm]
  exact Equiv.symm_trans_self _

/-! ## Lifting a chain zigzag to a zigzag of executions -/

/-- The event count is constant along a chain of `EventRel` steps. -/
theorem card_eventObj_eq_of_eqvGen {p q : Σ a : Ch K, EventObj a}
    (h : Relation.EqvGen (EventRel K) p q) :
    Fintype.card (EventObj p.1) = Fintype.card (EventObj q.1) := by
  induction h with
  | rel p q hpq => exact card_eventObj_eq_of_hom hpq.choose
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Every `EventRel` chain is realised by a zigzag of executions**, with a line prescribed at
*either* end (the two-sided form is what makes the `symm` step go through): the line at the far end
is chosen by `linesRestrict_surjective`, and the events are carried along by the zigzag's event
monodromy. -/
theorem exists_conc_zigzag {p q : Σ a : Ch K, EventObj a} (n : ℕ)
    (h : Relation.EqvGen (EventRel K) p q) :
    ∀ (hp : Fintype.card (EventObj p.1) = n) (hq : Fintype.card (EventObj q.1) = n),
      (∀ L : LinesObj p.1, ∃ (M : LinesObj q.1)
          (γ : (FreeGroupoid.mk (execAt L hp) : ConcGrpdN K n)
            ⟶ FreeGroupoid.mk (execAt M hq)), concRhoMap γ p.2 = q.2)
        ∧ (∀ M : LinesObj q.1, ∃ (L : LinesObj p.1)
          (γ : (FreeGroupoid.mk (execAt L hp) : ConcGrpdN K n)
            ⟶ FreeGroupoid.mk (execAt M hq)), concRhoMap γ p.2 = q.2) := by
  induction h with
  | rel p q hpq =>
      obtain ⟨f, hf⟩ := hpq
      intro hp hq
      constructor
      · intro L
        refine ⟨lineLift f L, CategoryTheory.inv (FreeGroupoid.homMk
          (restrictHom f (linesRestrict_lineLift f L) hq hp)), ?_⟩
        rw [concRhoMap_inv, concRhoMap_homMk, concRefine_restrictHom, Equiv.symm_symm]
        exact hf
      · intro M
        refine ⟨linesRestrict f M, CategoryTheory.inv (FreeGroupoid.homMk
          (restrictHom f rfl hq hp)), ?_⟩
        rw [concRhoMap_inv, concRhoMap_homMk, concRefine_restrictHom, Equiv.symm_symm]
        exact hf
  | refl p =>
      intro hp hq
      constructor
      · exact fun L => ⟨L, 𝟙 _, by rw [concRhoMap_id]; rfl⟩
      · exact fun M => ⟨M, 𝟙 _, by rw [concRhoMap_id]; rfl⟩
  | symm p q _ ih =>
      intro hq hp
      constructor
      · intro L
        obtain ⟨L', γ, hγ⟩ := (ih hp hq).2 L
        refine ⟨L', CategoryTheory.inv γ, ?_⟩
        rw [concRhoMap_inv, ← hγ]
        exact (concRhoMap γ).symm_apply_apply p.2
      · intro M
        obtain ⟨M', γ, hγ⟩ := (ih hp hq).1 M
        refine ⟨M', CategoryTheory.inv γ, ?_⟩
        rw [concRhoMap_inv, ← hγ]
        exact (concRhoMap γ).symm_apply_apply p.2
  | trans p q r h₁ _ ih₁ ih₂ =>
      intro hp hr
      have hq : Fintype.card (EventObj q.1) = n :=
        (card_eventObj_eq_of_eqvGen h₁).symm.trans hp
      constructor
      · intro L
        obtain ⟨M, γ₁, hγ₁⟩ := (ih₁ hp hq).1 L
        obtain ⟨N, γ₂, hγ₂⟩ := (ih₂ hq hr).1 M
        exact ⟨N, γ₁ ≫ γ₂, by rw [concRhoMap_comp, Equiv.trans_apply, hγ₁, hγ₂]⟩
      · intro N
        obtain ⟨M, γ₂, hγ₂⟩ := (ih₂ hq hr).2 N
        obtain ⟨L, γ₁, hγ₁⟩ := (ih₁ hp hq).2 M
        exact ⟨L, γ₁ ≫ γ₂, by rw [concRhoMap_comp, Equiv.trans_apply, hγ₁, hγ₂]⟩

/-! ## Purity ⟺ the naming property -/

/-- **Purity of the braid functor**: every vertex-group braid of `Φ = braidFunctor K n` has trivial
underlying permutation (`braidFunctor_pure`'s conclusion, as a property of `K`). -/
def BraidPure (K : BPSet) : Prop :=
  ∀ (n : ℕ) (x : ConcCatN K n) (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x),
    (FreeGroupoid.lift (braidPermFunctor n)).map ((braidFunctor K n).map γ) = 𝟙 _

/-- Purity, read frame-free: a loop of executions permutes the events of its chain trivially. -/
theorem concRhoMap_loop_eq_refl (h : BraidPure K) (x : ConcCatN K n)
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x) :
    concRhoMap γ = Equiv.refl (EventObj x.obj.chain) := by
  refine (evMonodromy_loop_eq_one_iff x γ).mp ?_
  have h2 : (braidFunctor K n ⋙ FreeGroupoid.lift (braidPermFunctor n)).map γ = 𝟙 _ := h n x γ
  rwa [braidFunctor_comp_braidPerm] at h2

/-- **The converse of `braidFunctor_pure`.**  Two events of a chain identified by the canonical
naming are joined by a zigzag of refinements; lift it to a zigzag of executions
(`exists_conc_zigzag`) and close it up without moving any event (`exists_lineShift`).  Purity of the
resulting loop says the two events were the same. -/
theorem hasGlobalEventNaming_of_pure (h : BraidPure K) : HasGlobalEventNaming K := by
  refine (hasGlobalEventNaming_iff K).mpr fun a e e' he => ?_
  have hgen : Relation.EqvGen (EventRel K) ⟨a, e⟩ ⟨a, e'⟩ :=
    Quot.eqvGen_exact (show canonicalName (⟨a, e⟩ : Σ a : Ch K, EventObj a)
      = canonicalName ⟨a, e'⟩ from he)
  have hcard : Fintype.card (EventObj a) = Fintype.card (EventObj a) := rfl
  obtain ⟨M, γ, hγ⟩ :=
    (exists_conc_zigzag (Fintype.card (EventObj a)) hgen hcard hcard).1
      (fun i => Chamber.std (ChainCat.beadDim a i))
  obtain ⟨ε, hε⟩ := exists_lineShift M (fun i => Chamber.std (ChainCat.beadDim a i)) hcard
  have hloop := concRhoMap_loop_eq_refl h
    (execAt (fun i => Chamber.std (ChainCat.beadDim a i)) hcard) (γ ≫ ε)
  have hcomp : concRhoMap (γ ≫ ε) e = e := by rw [hloop]; rfl
  rw [concRhoMap_comp, Equiv.trans_apply, hγ, hε] at hcomp
  exact hcomp.symm

/-- **Purity ⟺ HDA.**  `K` has a globally coherent event naming **iff** every vertex-group braid of
its braid functor is pure. -/
theorem hasGlobalEventNaming_iff_braidPure (K : BPSet) :
    HasGlobalEventNaming K ↔ BraidPure K :=
  ⟨fun h _ x γ => braidFunctor_pure h x γ, hasGlobalEventNaming_of_pure⟩

/-- The three faces of the naming property: a coherent naming, trivial event monodromy on chain
zigzags, and purity of the braid functor. -/
theorem eventMonodromyTrivial_iff_braidPure (K : BPSet) :
    EventMonodromyTrivial K ↔ BraidPure K :=
  (hasGlobalEventNaming_iff_monodromyTrivial K).symm.trans (hasGlobalEventNaming_iff_braidPure K)

end CubeChains
