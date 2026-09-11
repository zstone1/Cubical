import CubeChains.Concurrency.Presentation.Retraction

/-!
# Concurrency/Presentation/CrossLength — what the crossings grade on `Ch(Z)[W⁻¹]`

`posGrade` sends a refinement to the simple of its crossing permutation, so the two homomorphisms
out of `PosBraid` read a class of the localized base: `posLen` counts the pairs it crosses
(`locLen`), `posPermHom` names the permutation it performs (`locPerm`).  The count is blind to the
strand count and so is defined on every arrow; the permutation is not, and is read at the run.

Being gradings they are *constant* on a codimension-two cell, two factorisations of one refinement,
so they orient nothing.  They make the atoms' cover of the loops at the run length-preserving, and
they pin the classes of refinements out of the rest (`not_conj_eq_atomLoop_sq`).
-/

open CategoryTheory Equiv Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## The crossing count

`posLen` lands in `ℕ`, which has forgotten the strand count, so the degree transport carried by a
composite is invisible to it (`Graded.hom_congrDeg`) and no count has to be named. -/

/-- **The pairs an arrow of the localized base crosses.** -/
noncomputable def locLen {X Y : ((W Zbp).op).Localization} (g : X ⟶ Y) : ℕ :=
  Multiplicative.toAdd (posLen _ (posGradeLoc.map g).unop.val)

@[simp] theorem locLen_id (X : ((W Zbp).op).Localization) : locLen (𝟙 X) = 0 := by
  unfold locLen
  rw [CategoryTheory.Functor.map_id]
  exact congrArg Multiplicative.toAdd (map_one (posLen _))

theorem locLen_comp {X Y Z : ((W Zbp).op).Localization} (u : X ⟶ Y) (v : Y ⟶ Z) :
    locLen (u ≫ v) = locLen u + locLen v := by
  unfold locLen
  rw [CategoryTheory.Functor.map_comp, unop_comp, Graded.val_comp, map_mul,
    Graded.hom_congrDeg posLen, toAdd_mul]

@[simp] theorem locLen_Q {a b : Ch Zbp} (f : a ⟶ b) :
    locLen (((W Zbp).op).Q.map f.op) = permLen (crossPerm rfl f) := by
  unfold locLen
  rw [posGradeLoc_map_Q]
  rfl

/-- **A cut generator is not an atom** — one codimension-one step can cross two pairs, so a letter
of the cut presentation costs its own crossings and not one.  `[1,2] ⟶ [3]` is the least witness:
the lone event overtakes both of the other bead's. -/
theorem exists_codim_one_locLen_two :
    ∃ (a b : Ch Zbp) (f : a ⟶ b), codim f = 1 ∧ locLen (((W Zbp).op).Q.map f.op) = 2 := by
  obtain ⟨f, hf⟩ := exists_crossPerm_single (dimSum_atomComp 3 1) (m := atomTop 3 1)
    (atomTop_coe 3 1) (τ := adjT (1 : Fin 2) * adjT (0 : Fin 2))
    (fun x y hxy hlt => by
      obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq 3 1 hxy hlt
      decide)
  refine ⟨_, _, f, ?_, ?_⟩
  · rw [codim, degree_atomComp, degree, BPSet.degree]
    decide
  · rw [locLen_Q, permLen_crossPerm (dimSum_atomComp 3 1) rfl f, hf]
    decide

/-! ## …and the braid, at the run

`runGrade` is the same grading read in `PosBraid N`, so a loop at the run crosses that braid's
length and performs its permutation. -/

/-- **The crossings a loop at the run makes** — `ᵐᵒᵖ` is what makes composition multiplication. -/
noncomputable def runLen (N : ℕ) : RunLoops N →* Multiplicative ℕ := (posLen N).comp (runGrade N)

@[simp] theorem runLen_op {N : ℕ}
    (x : @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N))))) :
    runLen N (MulOpposite.op x) = Multiplicative.ofAdd (locLen x) := by
  change posLen N (Graded.congrDeg (dimSum_replicate N) (posGradeLoc.map x).unop.val) = _
  rw [Graded.hom_congrDeg posLen]
  exact (ofAdd_toAdd _).symm

@[simp] theorem locLen_runLoop (N : ℕ) (σ : Perm (Fin N)) : locLen (runLoop N σ) = permLen σ :=
  Multiplicative.ofAdd.injective <| by
    rw [← runLen_op]
    change posLen N (runGrade N (MulOpposite.op (runLoop N σ))) = _
    rw [runGrade_runLoop, posLen_posPerm]

/-- **A refinement's braid is reduced**: its class crosses exactly the pairs the refinement
crosses. -/
theorem locLen_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    locLen (conj ha f) = permLen (crossPerm ha f) := by
  rw [conj_eq_runLoop ha f, locLen_runLoop]

@[simp] theorem locLen_atomLoop (N : ℕ) (k : Fin (N - 1)) : locLen (atomLoop N k) = 1 := by
  rw [← runLoop_adjT, locLen_runLoop, permLen_adjT]

/-- **The permutation a loop at the run performs** — `Perm (Fin N)` moves with the strand count, so
this reading is pinned to the run, where the count is `N`. -/
noncomputable def locPerm (N : ℕ)
    (x : @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N))))) :
    Perm (Fin N) :=
  posPermHom N (runGrade N (MulOpposite.op x))

/-- **A refinement's class performs its own crossing permutation.** -/
theorem locPerm_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    locPerm N (conj ha f) = crossPerm ha f := by
  change posPermHom N (runGrade N (MulOpposite.op (conj ha f))) = _
  rw [runGrade_conj, posPermHom_posPerm]

@[simp] theorem locPerm_atomLoop (N : ℕ) (k : Fin (N - 1)) : locPerm N (atomLoop N k) = adjT k := by
  rw [atomLoop, locPerm_conj, crossPerm_atomOnes]

/-! ## The atoms cover the loops at the run

Length-preservingly, and onto.  The relations asked of the atoms are the two codimension-two
species; that they are the *only* ones is `runArtinEquiv`, Matsumoto's comparison read at the
run. -/

theorem isArtinFamily_atomLoop (N : ℕ) : IsArtinFamily (atomLoop N) where
  comm _ _ h := (atomLoop_comm h).symm
  braid _ _ h := atomLoop_braid h

/-- **The Artin monoid maps to the loops at the run** — the atoms satisfy the two relations and
nothing else is asked of them. -/
noncomputable def artinRun (N : ℕ) : ArtinPosBraid N →* RunLoops N :=
  ArtinPosBraid.lift _ (isArtinFamily_atomLoop N).op

@[simp] theorem artinRun_gen (N : ℕ) (k : Fin (N - 1)) :
    artinRun N (artinPosGen k) = MulOpposite.op (atomLoop N k) := rfl

/-- **A letter costs one crossing.** -/
theorem runLen_comp_artinRun (N : ℕ) : (runLen N).comp (artinRun N) = artinLen N :=
  artinPosGen_ext fun k => by
    rw [MonoidHom.comp_apply, artinRun_gen, runLen_op, locLen_atomLoop, artinLen_gen]

/-- **Every Artin braid naming a refinement's loop is reduced** — one letter per crossing, with no
minimising over spellings: the length is a value, not an infimum. -/
theorem artinLen_of_artinRun_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b)
    {β : ArtinPosBraid N} (hβ : artinRun N β = MulOpposite.op (conj ha f)) :
    artinLen N β = Multiplicative.ofAdd (permLen (crossPerm ha f)) := by
  rw [← runLen_comp_artinRun, MonoidHom.comp_apply, hβ, runLen_op, locLen_conj]

/-- **The cover is the Artin comparison itself** — both send a generator to its atom. -/
theorem artinRun_eq (N : ℕ) : artinRun N = (runArtinEquiv N).toMonoidHom :=
  artinPosGen_ext fun k => by
    rw [artinRun_gen]
    change _ = runBraid N ((posBraid_equiv_artinPos N).symm (artinPosGen k))
    rw [← posBraid_equiv_artinPos_adjT k, MulEquiv.symm_apply_apply, runBraid_posPerm,
      runLoop_adjT]

/-- **The atoms exhaust the loops at the run.** -/
theorem artinRun_surjective (N : ℕ) : Function.Surjective (artinRun N) := by
  rw [artinRun_eq]
  exact (runArtinEquiv N).surjective

/-- **A refinement's loop is a word in the atoms.** -/
theorem conj_mem_mrange_artinRun {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    MulOpposite.op (conj ha f) ∈ MonoidHom.mrange (artinRun N) :=
  MonoidHom.mem_mrange.mpr (artinRun_surjective N _)

/-! ## …but the refinements do not

The count alone tells the powers of one atom apart, so the loops at a run are infinite, while the
classes of refinements are the simples — at most `N!` of them.  A class named by an arrow carries
that arrow's braid, which pins the square of an atom out of that image. -/

theorem runLen_atomLoop_pow (N : ℕ) (k : Fin (N - 1)) (m : ℕ) :
    runLen N (MulOpposite.op (atomLoop N k) ^ m) = Multiplicative.ofAdd m := by
  rw [map_pow, runLen_op, locLen_atomLoop, ← ofAdd_nsmul, smul_eq_mul, mul_one]

/-- **The loops at a run of at least two events are infinite** — by the crossing count alone, with
no braid monoid in sight: the `m`-th power of an atom crosses `m` times. -/
theorem infinite_end_run {N : ℕ} (k : Fin (N - 1)) :
    Infinite (@End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N))))) := by
  refine Infinite.of_injective (fun m : ℕ => (MulOpposite.op (atomLoop N k) ^ m).unop) ?_
  intro m m' h
  have hm := congrArg (runLen N) (MulOpposite.unop_inj.mp h)
  rw [runLen_atomLoop_pow, runLen_atomLoop_pow] at hm
  exact Multiplicative.ofAdd.injective hm

/-- **No refinement's loop is an atom's square** — a refinement's loop grades to the *simple* of its
crossing, and `σₖ²` is no simple (`posPerm_ne_adjT_sq`).  So "the word of a class spells its
permutation" is a statement about *arrows*: the loops the localization adds are not reduced, and
Matsumoto's theorem does not reach them. -/
theorem not_conj_eq_atomLoop_sq {N : ℕ} (k : Fin (N - 1)) {a b : Ch Zbp}
    (ha : dimSum a.dims = N) (f : a ⟶ b) :
    conj ha f ≠ atomLoop N k ≫ atomLoop N k := fun h =>
  posPerm_ne_adjT_sq (crossPerm ha f) k <| by
    have hatom : runGrade N (MulOpposite.op (atomLoop N k)) = posPerm (adjT k) := by
      rw [← runLoop_adjT, runGrade_runLoop]
    rw [← runGrade_conj ha f, h]
    change runGrade N (MulOpposite.op (atomLoop N k) * MulOpposite.op (atomLoop N k)) = _
    rw [map_mul, hatom]

end ChainCat
