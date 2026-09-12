import CubeChains.Concurrency.Presentation.RunAtoms
import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Machinery.Braid.MatsumotoCat

/-!
# Concurrency/Presentation/RunCells — the degree-zero cells suffice, at every `K`

Over a chain `z` of `Ch K` the runs form a down-closed set of permutations (`runDescents`), an
adjacent ascent is an atom out of a run (`ascAtom`), and a climb is a word of such atoms.  Reading
the codimension-two cuts out of a run in that word gives Artin's two relations — the square and the
hexagon of the pair chain `z`'s blocks admit — so category-valued Matsumoto applies:

    run r ──atom k──▸ ▪ ◂──atom l── run r'        two climbs, one arrow
       └─────────────── z ───────────┘

`chCellPresentation` is then `Ch(K)[W⁻¹]` on the atoms out of the runs, relations the
codimension-two cuts out of a run.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat

variable {K : BPSet}

/-! ## A chain whose shape is a run is its own run -/

theorem eltRestrict_id (c : (chCutPoly K).V) : eltRestrict c (𝟙 (shOf c)) = c :=
  congrArg (fun t => (⟨shOf c, t⟩ : (chCutPoly K).V))
    (by rw [op_id, Functor.map_id_apply])

/-- **A chain is its own run exactly when its shape is one** — the merge onto it is an
endomorphism, and a reindexing that leaves the shape alone therefore reflects the condition. -/
theorem eltRep_eq_self_iff (c : (chCutPoly K).V) : eltRep c = c ↔ zRep (shOf c) = shOf c :=
  ⟨fun h => congrArg (fun z : (chCutPoly K).V => shOf z) h, fun hz =>
    (eltRestrict_eq_of_W c hz (W_zRunMerge (shOf c)) (MorphismProperty.id_mem _ _)).trans
      (eltRestrict_id c)⟩

/-- …read at a named strand count. -/
theorem eltRep_eq_self {N : ℕ} {c : (chCutPoly K).V} (h : shOf c = zObj (𝟙^N)) : eltRep c = c := by
  have hd : dimSum (shOf c).dims = N := by rw [h]; exact dimSum_replicate N
  refine (eltRep_eq_self_iff c).mpr ?_
  change zObj (𝟙^(dimSum (shOf c).dims)) = shOf c
  rw [hd, h]

/-! ## The runs over a chain

A run-arrow into `shOf z` is pinned by its crossing permutation, so the permutations it realises are
a faithful index set — `Descents`' hypothesis — and the arrow is recovered from the permutation. -/

/-- A crossing permutation some run-arrow into a chain realises. -/
def RunPerm (N : ℕ) (z : (chCutPoly K).V) : Type :=
  {σ : Perm (Fin N) // ∃ r : zObj (𝟙^N) ⟶ shOf z, crossPerm (dimSum_replicate N) r = σ}

namespace RunPerm

variable {N : ℕ} {z : (chCutPoly K).V}

/-- The run-arrow a realised permutation names. -/
noncomputable def arr (σ : RunPerm N z) : zObj (𝟙^N) ⟶ shOf z := σ.2.choose

@[simp] theorem crossPerm_arr (σ : RunPerm N z) :
    crossPerm (dimSum_replicate N) σ.arr = σ.1 := σ.2.choose_spec

/-- **A run-arrow is pinned by its crossing permutation.** -/
theorem eq_arr (σ : RunPerm N z) {r : zObj (𝟙^N) ⟶ shOf z}
    (hr : crossPerm (dimSum_replicate N) r = σ.1) : r = σ.arr :=
  hom_ext_of_crossPerm (hr.trans (σ.crossPerm_arr).symm)

theorem strands (σ : RunPerm N z) : dimSum (shOf z).dims = N :=
  (dimSum_eq_of_hom σ.arr).symm.trans (dimSum_replicate N)

end RunPerm

/-- The run a map out of a run names. -/
def runOf {N : ℕ} {z : (chCutPoly K).V} (r : zObj (𝟙^N) ⟶ shOf z) : RunPerm N z :=
  ⟨crossPerm (dimSum_replicate N) r, ⟨r, rfl⟩⟩

@[simp] theorem runOf_val {N : ℕ} {z : (chCutPoly K).V} (r : zObj (𝟙^N) ⟶ shOf z) :
    (runOf r).1 = crossPerm (dimSum_replicate N) r := rfl

@[simp] theorem arr_runOf {N : ℕ} {z : (chCutPoly K).V} (r : zObj (𝟙^N) ⟶ shOf z) :
    (runOf r).arr = r := ((runOf r).eq_arr rfl).symm

/-- **The runs over a chain are a down-closed set of permutations** — `exists_run_mul_adjT` is the
exchange, and a run-arrow is its permutation. -/
noncomputable def runDescents (N : ℕ) (z : (chCutPoly K).V) : Descents N (RunPerm N z) where
  perm := Subtype.val
  perm_inj := Subtype.val_injective
  exists_desc σ k hd := by
    obtain ⟨r, hr⟩ := exists_run_mul_adjT σ.strands σ.arr (by simpa using hd)
    exact ⟨runOf r, by rw [runOf_val, hr, σ.crossPerm_arr]⟩

@[simp] theorem runDescents_perm (N : ℕ) (z : (chCutPoly K).V) (σ : RunPerm N z) :
    (runDescents N z).perm σ = σ.1 := rfl

/-- The run a chain is merged into from. -/
noncomputable def runBot {N : ℕ} (z : (chCutPoly K).V) (hz : dimSum (shOf z).dims = N) :
    RunPerm N z := runOf (runMerge (shOf z) hz)

@[simp] theorem runBot_val {N : ℕ} (z : (chCutPoly K).V) (hz : dimSum (shOf z).dims = N) :
    (runBot z hz).1 = 1 := crossPerm_eq_one_of_W _ (W_runMerge _ _)

/-- **Every run is climbed to from the merge run.** -/
theorem runBot_le {N : ℕ} {z : (chCutPoly K).V} (hz : dimSum (shOf z).dims = N)
    (σ : RunPerm N z) : WeakOrder.of ((runDescents N z).perm (runBot z hz))
      ≤ WeakOrder.of ((runDescents N z).perm σ) := by
  rw [runDescents_perm, runDescents_perm, runBot_val]
  exact WeakOrder.le_of_mul_eq (one_mul σ.1) (by rw [permLen_one, Nat.add_zero])

/-! ## The 0-cell a run names -/

/-- The 0-cell of the contracted polygraph a run over a chain names. -/
noncomputable def runObj {N : ℕ} {z : (chCutPoly K).V} (σ : RunPerm N z) :
    (chContraction K).V := ⟨eltRestrict z σ.arr, eltRep_eq_self rfl⟩

theorem runObj_runBot {N : ℕ} (z : (chCutPoly K).V) (hz : dimSum (shOf z).dims = N) :
    (runObj (runBot z hz)).1 = eltRep z := by
  refine Eq.trans (congrArg (eltRestrict z) (arr_runOf (runMerge (shOf z) hz))) ?_
  exact eltRestrict_eq_of_W z (congrArg (fun n => zObj (𝟙^n)) hz.symm)
    (W_runMerge _ _) (W_zRunMerge (shOf z))

/-- The refinement a leg into a chain is, carrying the restricted element. -/
noncomputable def legLift {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    vChain (eltRestrict z w) ⟶ vChain z := liftOf w rfl

@[simp] theorem baseHom_legLift {z : (chCutPoly K).V} {p : Ch Zbp} (w : p ⟶ shOf z) :
    baseHom (legLift w) = w := rfl

theorem W_legLift {z : (chCutPoly K).V} {p : Ch Zbp} {w : p ⟶ shOf z} (hw : W Zbp w) :
    W K (legLift w) := (W_baseHom_iff _).mp hw

/-! ## A bead cut out of a run, as a 1-cell of the contraction -/

/-- A bead cut, acting on the element its source carries. -/
def cutGen {c c' : (chCutPoly K).V} (f : shOf c' ⟶ shOf c) (hf : codim f = 1)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) : (chCutPoly K).Gen c c' :=
  ⟨⟨f, hf⟩, (congrArg (fun g => (wedgeHoms K).map g c.2) (zCutPresentation_arrow _)).trans hres⟩

/-- **A bead cut out of a run**, as a 1-cell of the contraction: the cut merges nothing, and its
target is the run on its own events. -/
noncomputable def runGen {c c' : (chCutPoly K).V} {N : ℕ} (hc' : shOf c' = zObj (𝟙^N))
    (f : shOf c' ⟶ shOf c) (hf : codim f = 1) (hnW : ¬ W Zbp f)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) {X Y : (chContraction K).V}
    (hX : eltRep c = X.1) (hY : c' = Y.1) : (chContraction K).Gen X Y where
  dom := c
  cod := c'
  gen := Sum.inl (cutGen f hf hres)
  not_mem := fun hm => hnW ((merge_iff f).mp hm).1
  rep_dom := hX
  rep_cod := (eltRep_eq_self hc').trans hY

theorem runCut_runGen {c c' : (chCutPoly K).V} {N : ℕ} (hc' : shOf c' = zObj (𝟙^N))
    (f : shOf c' ⟶ shOf c) (hf : codim f = 1) (hnW : ¬ W Zbp f)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) {X Y : (chContraction K).V}
    (hX : eltRep c = X.1) (hY : c' = Y.1) :
    RunCut (runGen hc' f hf hnW hres hX hY) := eltRep_eq_self hc'

/-- **The refinement a cut out of a run performs.** -/
theorem chCutHom_runGen {c c' : (chCutPoly K).V} {N : ℕ} (hc' : shOf c' = zObj (𝟙^N))
    (f : shOf c' ⟶ shOf c) (hf : codim f = 1) (hnW : ¬ W Zbp f)
    (hres : (wedgeHoms K).map f.op c.2 = c'.2) {X Y : (chContraction K).V}
    (hX : eltRep c = X.1) (hY : c' = Y.1) :
    chCutHom (runGen hc' f hf hnW hres hX hY).gen
        (runGen hc' f hf hnW hres hX hY).not_mem
      = liftOf f hres := rfl

/-! ## An ascent is an atom out of a run

At an ascent the run-arrow below factors through the `k`-th atom shape and the one above crosses it
(`exists_atom_step`), so the leg is a chain of atom shape over the base and the atom's cut is
`atomOnes` — with no transport, the shapes being what `eltRestrict` records. -/

/-- **The run of a chain of atom shape** — the atom's own merge reaches it. -/
theorem eltRep_eltRestrict_atom {N : ℕ} {k : Fin (N - 1)} {z : (chCutPoly K).V}
    (w : zObj (atomComp N k) ⟶ shOf z) :
    eltRep (eltRestrict z w) = eltRestrict z (mergeOnes N k ≫ w) :=
  (eltRestrict_eq_of_W (eltRestrict z w)
      (congrArg (fun n => zObj (𝟙^n)) (dimSum_atomComp N k)) (W_zRunMerge _)
      (W_mergeOnes N k)).trans (eltRestrict_comp z w (mergeOnes N k))

variable {N : ℕ} {z : (chCutPoly K).V}

/-- The leg an ascent crosses: the atom shape at its index, over the base. -/
noncomputable def ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    zObj (atomComp N e.idx) ⟶ shOf z :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose

theorem mergeOnes_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    mergeOnes N e.idx ≫ ascLeg e = a.arr :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.1

theorem crossPerm_atomOnes_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    crossPerm (dimSum_replicate N) (atomOnes N e.idx ≫ ascLeg e) = a.1 * adjT e.idx :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.2

theorem atomOnes_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    atomOnes N e.idx ≫ ascLeg e = b.arr :=
  b.eq_arr ((crossPerm_atomOnes_ascLeg e).trans e.perm_eq.symm)

/-- **The `k`-th atom over a leg into a chain** — restricting twice is restricting along the
composite, so this is also the atom over the same leg read into anything the chain refines. -/
noncomputable def legAtom {k : Fin (N - 1)} (w : zObj (atomComp N k) ⟶ shOf z)
    {X Y : (chContraction K).V} (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRestrict z (atomOnes N k ≫ w) = Y.1) : (chContraction K).Gen X Y :=
  runGen rfl (atomOnes N k) (codim_atomOnes N k) (not_W_atomOnes N k)
    (map_op_comp w (atomOnes N k) z.2) hX hY

theorem runCut_legAtom {k : Fin (N - 1)} (w : zObj (atomComp N k) ⟶ shOf z)
    {X Y : (chContraction K).V} (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRestrict z (atomOnes N k ≫ w) = Y.1) : RunCut (legAtom w hX hY) :=
  eltRep_eq_self rfl

theorem map_mergeOnes_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    (wedgeHoms K).map (mergeOnes N e.idx).op (eltRestrict z (ascLeg e)).2
      = (eltRestrict z a.arr).2 :=
  (map_op_comp (ascLeg e) (mergeOnes N e.idx) z.2).trans
    (congrArg (fun t : zObj (𝟙^N) ⟶ shOf z => (wedgeHoms K).map t.op z.2) (mergeOnes_ascLeg e))

theorem eltRep_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    eltRep (eltRestrict z (ascLeg e)) = (runObj a).1 :=
  (eltRep_eltRestrict_atom (ascLeg e)).trans (congrArg (eltRestrict z) (mergeOnes_ascLeg e))

/-- **The atom an ascent names** — the `k`-th cut out of the run below it. -/
noncomputable def ascAtom {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    (chContraction K).Gen (runObj a) (runObj b) :=
  legAtom (ascLeg e) (eltRep_ascLeg e) (congrArg (eltRestrict z) (atomOnes_ascLeg e))

theorem runCut_ascAtom {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    RunCut (ascAtom e) := eltRep_eq_self rfl

/-- The word of atoms a climb spells. -/
noncomputable def climbPath {a : RunPerm N z} : ∀ {b : RunPerm N z},
    Climb (runDescents N z).perm a b →
      Quiver.Path ((chContraction K).poly.pt (runObj a)) ((chContraction K).poly.pt (runObj b))
  | _, .nil => Quiver.Path.nil
  | _, .cons R e => (climbPath R).cons (Polygraph.cell (P := (chContraction K).poly) (ascAtom e))

theorem all_climbPath {a : RunPerm N z} : ∀ {b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b),
    Quiver.Path.All (fun ⦃_ _⦄ g => RunCut g) (climbPath R)
  | _, .nil => Quiver.Path.all_nil _
  | _, .cons R e => (Quiver.Path.all_cons_iff _ _).mpr ⟨all_climbPath R, runCut_ascAtom e⟩

/-! ## A climb is the refinement it performs

The two legs out of an ascent's atom shape are a merge and the atom itself, and both land on the
base, so `runConj`'s contravariance telescopes a climb into one conjugated refinement. -/

/-- The atom's own cut, as a refinement of `Ch K`. -/
noncomputable def ascCut {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    vChain (eltRestrict z (atomOnes N e.idx ≫ ascLeg e)) ⟶ vChain (eltRestrict z (ascLeg e)) :=
  liftOf (atomOnes N e.idx) (map_op_comp (ascLeg e) (atomOnes N e.idx) z.2)

/-- …and its merge leg. -/
noncomputable def ascMerge {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    vChain (eltRestrict z a.arr) ⟶ vChain (eltRestrict z (ascLeg e)) :=
  liftOf (mergeOnes N e.idx) (map_mergeOnes_ascLeg e)

theorem W_ascMerge {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    W K (ascMerge e) :=
  (W_baseHom_iff _).mp (by rw [ascMerge, baseHom_liftOf]; exact W_mergeOnes N e.idx)

theorem chCutHom_ascAtom {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    chCutHom (ascAtom e).gen (ascAtom e).not_mem = ascCut e := rfl

/-- The arrow a run over a chain names, out of the chain's own run. -/
noncomputable def runConjAt (hz : dimSum (shOf z).dims = N) (σ : RunPerm N z) :
    chPt (runObj (runBot z hz)).1 ⟶ chPt (runObj σ).1 :=
  eqToHom (congrArg chPt (runObj_runBot z hz)) ≫ runConj (legLift σ.arr)
    ≫ eqToHom (congrArg chPt (eltRep_eq_self (N := N) (c := eltRestrict z σ.arr) rfl))

/-- Inserting a cancelling triple of renamings.  Stated for `exact`: the object slots of `≫` carry
two spellings of one object here, which defeats `simp`'s matching. -/
private theorem insert_cancel {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (s : X₃ ⟶ X₄) (q : X₄ ⟶ X₅) {s' : X₃ ⟶ X₅}
    (hs : s ≫ q = s') (m₁ : X₂ ⟶ Y₁) (m₂ : Y₁ ⟶ Y₂) (m₃ : Y₂ ⟶ X₂)
    (h : m₁ ≫ m₂ ≫ m₃ = 𝟙 X₂) :
    p ≫ (f ≫ g ≫ s) ≫ q = (p ≫ (f ≫ m₁) ≫ m₂) ≫ (m₃ ≫ g ≫ s') := by
  subst hs
  have key : (m₁ ≫ m₂ ≫ m₃) ≫ g ≫ s ≫ q = g ≫ s ≫ q := by rw [h, Category.id_comp]
  simp only [Category.assoc] at key ⊢
  rw [key]

/-- A renaming on either side of an arrow that is itself one. -/
private theorem eqToHom_sandwich {C : Type*} [Category C] {A B D E : C} (h₁ : A = B)
    {f : B ⟶ D} {h : B = D} (hf : f = eqToHom h) (h₂ : D = E) (hAE : A = E) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom hAE := by
  subst h₁; subst h; subst h₂; rw [hf]; simp

/-- Renaming both sides of an arrow does not see which arrow it is. -/
private theorem sandwich_congr {C : Type*} [Category C] {A B D E : C} (h₁ : A = B) (h₂ : D = E)
    {f g : B ⟶ D} (h : f = g) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by rw [h]

/-- **Two refinements of one shape, out of chains that agree, name one arrow.** -/
theorem runConj_eq_of_eq {c b₁ b₂ : (chCutPoly K).V} (h : b₁ = b₂) {u : vChain b₁ ⟶ vChain c}
    {u' : vChain b₂ ⟶ vChain c}
    (hbase : baseHom u = eqToHom (congrArg shOf h) ≫ baseHom u') :
    runConj u ≫ eqToHom (congrArg chPt (congrArg eltRep h)) = runConj u' := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hbase
  rw [hom_ext_baseHom hbase, eqToHom_refl, Category.comp_id]

theorem W_runBot_arr (hz : dimSum (shOf z).dims = N) : W Zbp ((runBot z hz).arr) := by
  have h : (runBot z hz).arr = runMerge (shOf z) hz := arr_runOf _
  rw [h]
  exact W_runMerge _ _

theorem runConjAt_bot (hz : dimSum (shOf z).dims = N) :
    runConjAt hz (runBot z hz) = 𝟙 (chPt (runObj (runBot z hz)).1) :=
  (eqToHom_sandwich _ (runConj_of_W _ (W_legLift (W_runBot_arr hz))) _ rfl).trans
    (eqToHom_refl _ _)

/-- **One atom appends to the conjugated refinement below it.** -/
theorem runConjAt_cons (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (e : Ascent (runDescents N z).perm a b) :
    runConjAt hz b = runConjAt hz a ≫ (chContraction K).backQuot.map
      (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath := by
  have hb : runConj (legLift (ascLeg e)) ≫ runConj (ascCut e)
      ≫ eqToHom (congrArg chPt (congrArg eltRep
        (congrArg (eltRestrict z) (atomOnes_ascLeg e)))) = runConj (legLift b.arr) := by
    rw [← Category.assoc, ← runConj_comp]
    refine runConj_eq_of_eq (congrArg (eltRestrict z) (atomOnes_ascLeg e)) ?_
    rw [baseHom_comp, baseHom_legLift, ascCut, baseHom_liftOf, baseHom_legLift]
    exact atomOnes_ascLeg e
  have ha : runConj (legLift a.arr) = runConj (legLift (ascLeg e))
      ≫ eqToHom (congrArg chPt (eltRep_eq_of_W (ascMerge e) (W_ascMerge e)).symm) := by
    rw [show legLift a.arr = ascMerge e ≫ legLift (ascLeg e) from
      hom_ext_baseHom (by
        rw [baseHom_comp, baseHom_legLift, baseHom_legLift, ascMerge, baseHom_liftOf]
        exact (mergeOnes_ascLeg e).symm), runConj_comp, runConj_of_W (ascMerge e) (W_ascMerge e)]
  have hgen : (chContraction K).backQuot.map
        (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath
      = eqToHom (congrArg chPt (ascAtom e).rep_dom).symm ≫ runConj (ascCut e)
        ≫ eqToHom (congrArg chPt (ascAtom e).rep_cod) := backQuot_gen (ascAtom e)
  refine Eq.trans ?_ (congrArg (fun t => runConjAt hz a ≫ t) hgen).symm
  refine Eq.trans (sandwich_congr _ _ hb.symm) (Eq.trans ?_ (congrArg (fun t => t
    ≫ (eqToHom (congrArg chPt (ascAtom e).rep_dom).symm ≫ runConj (ascCut e)
      ≫ eqToHom (congrArg chPt (ascAtom e).rep_cod))) (sandwich_congr _ _ ha)).symm)
  refine insert_cancel _ _ _ _ _ (eqToHom_trans _ _) _ _ _ ?_
  exact (congrArg (fun t => eqToHom (congrArg chPt
      (eltRep_eq_of_W (ascMerge e) (W_ascMerge e)).symm) ≫ t) (eqToHom_trans _ _)).trans
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- **A climb is the refinement it performs**, conjugated onto the chain's own run. -/
theorem backQuot_climbPath (hz : dimSum (shOf z).dims = N) : ∀ {σ : RunPerm N z}
    (R : Climb (runDescents N z).perm (runBot z hz) σ),
    (chContraction K).backQuot.map (climbPath R) = runConjAt hz σ
  | _, .nil => ((chContraction K).backQuot.map_id _).trans (runConjAt_bot hz).symm
  | _, .cons R e =>
      (((chContraction K).backQuot.map_comp (climbPath R)
          (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath).trans
        (congrArg (fun t => t ≫ (chContraction K).backQuot.map
          (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath)
          (backQuot_climbPath hz R))).trans (runConjAt_cons hz e).symm

/-! ## The word a 1-cell spells

The climb from the source's own run to the run of the target is a word of atoms performing the same
refinement, so the contraction's equivalence equates the two. -/

variable {X Y : (chContraction K).V}

/-- The bead cut a 1-cell of the contraction performs. -/
def genCut (g : (chContraction K).Gen X Y) : shOf g.cod ⟶ shOf g.dom :=
  Cut.genHom (chFwdOf g.gen g.not_mem).1

theorem map_genCut (g : (chContraction K).Gen X Y) :
    (wedgeHoms K).map (genCut g).op g.dom.2 = g.cod.2 :=
  (congrArg (fun q => (wedgeHoms K).map q g.dom.2)
    (zCutPresentation_arrow (chFwdOf g.gen g.not_mem).1)).symm.trans (chFwdOf g.gen g.not_mem).2

theorem chCutHom_eq (g : (chContraction K).Gen X Y) :
    chCutHom g.gen g.not_mem = liftOf (genCut g) (map_genCut g) := rfl

theorem eltRestrict_genCut (g : (chContraction K).Gen X Y) :
    eltRestrict g.dom (genCut g) = g.cod :=
  congrArg (fun t => (⟨shOf g.cod, t⟩ : (chCutPoly K).V)) (map_genCut g)

/-- The run of a 1-cell's target, read over its source. -/
noncomputable def genTop (g : (chContraction K).Gen X Y) : RunPerm (vCount g.dom) g.dom :=
  runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)

/-- **Restricting along a merge prefix sees only its shape** — `eq_of_W` pins the merge. -/
theorem eltRestrict_merge_comp {z : (chCutPoly K).V} {c : Ch Zbp} (f : c ⟶ shOf z) {N : ℕ}
    {m : zObj (𝟙^N) ⟶ c} (hm : W Zbp m) {m' : zRep c ⟶ c} (hm' : W Zbp m')
    (hs : zObj (𝟙^N) = zRep c) : eltRestrict z (m ≫ f) = eltRestrict z (m' ≫ f) :=
  (eltRestrict_comp z f m).symm.trans
    ((eltRestrict_eq_of_W (eltRestrict z f) hs hm hm').trans (eltRestrict_comp z f m'))

theorem runObj_genTop (g : (chContraction K).Gen X Y) : (runObj (genTop g)).1 = Y.1 :=
  (congrArg (eltRestrict g.dom) (arr_runOf _)).trans
    ((eltRestrict_merge_comp (genCut g) (W_runMerge _ _) (W_zRunMerge _)
        (congrArg (fun n => zObj (𝟙^n)) (dimSum_eq_of_hom (genCut g)).symm)).trans
      ((eltRep_eq_eltRestrict (chFwdOf g.gen g.not_mem)).symm.trans g.rep_cod))

theorem runObj_runBot_gen (g : (chContraction K).Gen X Y) :
    (runObj (runBot g.dom rfl)).1 = X.1 := (runObj_runBot g.dom rfl).trans g.rep_dom

/-- The climb a 1-cell's word reads. -/
noncomputable def genClimb (g : (chContraction K).Gen X Y) :
    Climb (runDescents (vCount g.dom) g.dom).perm (runBot g.dom rfl) (genTop g) :=
  ((runDescents (vCount g.dom) g.dom).nonempty_climb' (runBot_le rfl (genTop g))).some

/-- **The atom word a 1-cell spells**: itself when its cut starts at a run, and the climb out of the
source's own run otherwise. -/
noncomputable def runCellWord (g : (chContraction K).Gen X Y) :
    Quiver.Path ((chContraction K).poly.pt X) ((chContraction K).poly.pt Y) :=
  @dite _ (RunCut g) (Classical.propDecidable _)
    (fun _ => (Polygraph.cell (P := (chContraction K).poly) g).toPath)
    (fun _ => cellCongr Quiver.Path
      (congrArg (chContraction K).poly.pt (Subtype.ext (runObj_runBot_gen g)))
      (congrArg (chContraction K).poly.pt (Subtype.ext (runObj_genTop g)))
      (climbPath (genClimb g)))

theorem all_runCellWord (g : (chContraction K).Gen X Y) :
    Quiver.Path.All (fun ⦃_ _⦄ e => RunCut e) (runCellWord g) := by
  by_cases h : RunCut g
  · rw [runCellWord, dif_pos h]
    exact Quiver.Path.all_toPath.mpr h
  · rw [runCellWord, dif_neg h]
    exact (Quiver.Path.all_cellCongr _ _ _).mpr (all_climbPath (genClimb g))

/-- **A kept 1-cell spells itself.** -/
theorem runCellWord_self (g : (chContraction K).Gen X Y) (h : RunCut g) :
    runCellWord g = (Polygraph.cell (P := (chContraction K).poly) g).toPath := by
  rw [runCellWord, dif_pos h]

theorem map_genTopMerge (g : (chContraction K).Gen X Y) :
    (wedgeHoms K).map (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))).op g.cod.2
      = (eltRestrict g.dom (genTop g).arr).2 := by
  refine Eq.trans (congrArg
    ((wedgeHoms K).map (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))).op)
    (map_genCut g).symm) ?_
  refine Eq.trans (map_op_comp (genCut g)
    (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))) g.dom.2) ?_
  exact congrArg (fun t : zObj (𝟙^(vCount g.dom)) ⟶ shOf g.dom =>
    (wedgeHoms K).map t.op g.dom.2)
    (arr_runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)).symm

/-- The merge onto the target's run, read over the source. -/
noncomputable def genTopMerge (g : (chContraction K).Gen X Y) :
    vChain (eltRestrict g.dom (genTop g).arr) ⟶ vChain g.cod :=
  liftOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g))) (map_genTopMerge g)

theorem W_genTopMerge (g : (chContraction K).Gen X Y) : W K (genTopMerge g) :=
  (W_baseHom_iff _).mp (by rw [genTopMerge, baseHom_liftOf]; exact W_runMerge _ _)

/-- **The top of a 1-cell's climb is its own cut**, the merge onto the target's run contributing
nothing. -/
theorem runConj_genTop (g : (chContraction K).Gen X Y) :
    runConj (legLift ((genTop g).arr)) = runConj (liftOf (genCut g) (map_genCut g))
      ≫ eqToHom (congrArg chPt (eltRep_eq_of_W (genTopMerge g) (W_genTopMerge g)).symm) := by
  rw [show legLift ((genTop g).arr) = genTopMerge g ≫ liftOf (genCut g) (map_genCut g) from
    hom_ext_baseHom (by
      rw [baseHom_comp, baseHom_legLift, genTopMerge, baseHom_liftOf, baseHom_liftOf]
      exact arr_runOf (runMerge (shOf g.cod) (dimSum_eq_of_hom (genCut g)) ≫ genCut g)),
    runConj_comp, runConj_of_W (genTopMerge g) (W_genTopMerge g)]

/-- Collapsing a sandwich of renamings onto the arrow inside it. -/
private theorem sandwich_collapse {C : Type*} [Category C] {A A₁ A₂ B₀ B₁ B₂ B₃ : C}
    (p : A = A₁) (q : A₁ = A₂) {f : A₂ ⟶ B₀} (v : B₀ = B₁) (r : B₁ = B₂) (s : B₂ = B₃)
    (hA : A = A₂) (hB : B₀ = B₃) :
    eqToHom p ≫ (eqToHom q ≫ (f ≫ eqToHom v) ≫ eqToHom r) ≫ eqToHom s
      = eqToHom hA ≫ f ≫ eqToHom hB := by
  subst p; subst q; subst v; subst r; subst s; simp

/-- **Each 1-cell and its atom word name one arrow** — the dimension-one half of `Spans`. -/
theorem quot_runCellWord (g : (chContraction K).Gen X Y) :
    (chContraction K).poly.quot.map (runCellWord g)
      = (chContraction K).poly.quot.map
        (Polygraph.cell (P := (chContraction K).poly) g).toPath := by
  by_cases h : RunCut g
  · rw [runCellWord_self g h]
  · refine poly_quot_congr ?_
    rw [runCellWord, dif_neg h]
    refine Eq.trans (Paths.map_cellCongr₂ (chContraction K).backQuot _ _ _) ?_
    refine Eq.trans (sandwich_congr _ _ (((backQuot_climbPath rfl (genClimb g)).trans
      (sandwich_congr _ _ (runConj_genTop g))))) ?_
    exact (sandwich_collapse _ _ _ _ _ (congrArg chPt g.rep_dom).symm
      (congrArg chPt g.rep_cod)).trans (backQuot_gen g).symm

/-! ## The sub-polygraph at degree zero -/

/-- **The 2-cells to keep**: the codimension-two cuts out of a run. -/
def RunCutCell {u v : GenObj (chContraction K).poly.Gen} (α : (chContraction K).poly.Rel u v) :
    Prop := eltRep α.cod.as = α.cod.as

/-- **The atoms out of the runs, with the degree-zero codimension-two cells.** -/
noncomputable def runAtomPoly (K : BPSet) : Polygraph :=
  Polygraph.sub (P := (chContraction K).poly) RunCut RunCutCell runCellWord all_runCellWord

/-- Reading a word of the contracted polygraph in the sub-polygraph. -/
noncomputable def runSubF (K : BPSet) : (chContraction K).poly.Word ⥤ (runAtomPoly K).presented :=
  Paths.lift (subPre (P := (chContraction K).poly) RunCut runCellWord all_runCellWord)
    ⋙ (runAtomPoly K).quot

/-- The object a run names in the sub-polygraph. -/
noncomputable def subObj {N : ℕ} {z : (chCutPoly K).V} (σ : RunPerm N z) :
    (runAtomPoly K).presented := (runSubF K).obj ((chContraction K).poly.pt (runObj σ))

/-- The arrow a 1-cell names there. -/
noncomputable def subArr (g : (chContraction K).Gen X Y) :
    (runSubF K).obj ((chContraction K).poly.pt X) ⟶ (runSubF K).obj ((chContraction K).poly.pt Y) :=
  (runSubF K).map (Polygraph.cell (P := (chContraction K).poly) g).toPath

/-- …and the arrow a climb names. -/
noncomputable def climbArr {N : ℕ} {z : (chCutPoly K).V} {a : RunPerm N z} :
    ∀ {b : RunPerm N z}, Climb (runDescents N z).perm a b → (subObj a ⟶ subObj b)
  | _, .nil => 𝟙 _
  | _, .cons R e => climbArr R ≫ subArr (ascAtom e)

theorem subF_climbPath {N : ℕ} {z : (chCutPoly K).V} {a : RunPerm N z} : ∀ {b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b), (runSubF K).map (climbPath R) = climbArr R
  | _, .nil => (runSubF K).map_id _
  | _, .cons R e => ((runSubF K).map_comp (climbPath R)
      (Polygraph.cell (P := (chContraction K).poly) (ascAtom e)).toPath).trans
    (congrArg (fun t => t ≫ subArr (ascAtom e)) (subF_climbPath R))

theorem subArr_eq_map (g : (chContraction K).Gen X Y) :
    subArr g = (runSubF K).map (runCellWord g) := by
  have h0 : keptWord (P := (chContraction K).poly) RunCut (runCellWord g) (all_runCellWord g)
      = (Paths.lift (subPre (P := (chContraction K).poly) RunCut runCellWord
        all_runCellWord)).map (runCellWord g) :=
    (subWords_of_all RunCut (word_all := all_runCellWord) runCellWord_self
      (runCellWord g) (all_runCellWord g)).symm
  have h : (Paths.lift (subPre (P := (chContraction K).poly) RunCut runCellWord
        all_runCellWord)).map (Polygraph.cell (P := (chContraction K).poly) g).toPath
      = (Paths.lift (subPre (P := (chContraction K).poly) RunCut runCellWord
        all_runCellWord)).map (runCellWord g) :=
    (Paths.lift_toPath _ _).trans h0
  exact congrArg (runAtomPoly K).quot.map h

/-- **A 1-cell reads in the sub-polygraph as the climb its word spells.** -/
theorem subArr_eq_climbArr (g : (chContraction K).Gen X Y) (hg : ¬ RunCut g) :
    subArr g = eqToHom (congrArg (runSubF K).obj (congrArg (chContraction K).poly.pt
          (Subtype.ext (runObj_runBot_gen g)))).symm
      ≫ climbArr (genClimb g) ≫ eqToHom (congrArg (runSubF K).obj
        (congrArg (chContraction K).poly.pt (Subtype.ext (runObj_genTop g)))) := by
  rw [subArr_eq_map g, runCellWord, dif_neg hg]
  refine Eq.trans (Paths.map_cellCongr₂ (runSubF K) _ _ _) ?_
  exact sandwich_congr _ _ (subF_climbPath (genClimb g))

/-- **A climb that crosses one pair is its single atom** — `Climb.eq_cons_nil`, since a `RunPerm` is
pinned by its permutation.  So the climb a word *chose* is canonical at length one. -/
theorem climbArr_of_permLen_succ {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) (h : permLen b.1 = permLen a.1 + 1) :
    ∃ e : Ascent (runDescents N z).perm a b, climbArr R = subArr (ascAtom e) := by
  obtain ⟨e, rfl⟩ := Climb.eq_cons_nil (runDescents N z).perm_inj R h
  exact ⟨e, Category.id_comp _⟩

/-- **An atom is pinned by its leg**, read at any naming of the two runs it joins. -/
theorem subArr_legAtom_eq {M : ℕ} {y : (chCutPoly K).V} {k : Fin (M - 1)}
    {w w' : zObj (atomComp M k) ⟶ shOf y} (hww : w = w')
    {X Y X' Y' : (chContraction K).V}
    (hX : eltRep (eltRestrict y w) = X.1) (hY : eltRestrict y (atomOnes M k ≫ w) = Y.1)
    (hX' : eltRep (eltRestrict y w') = X'.1) (hY' : eltRestrict y (atomOnes M k ≫ w') = Y'.1)
    (p : (runSubF K).obj ((chContraction K).poly.pt X)
      = (runSubF K).obj ((chContraction K).poly.pt X'))
    (q : (runSubF K).obj ((chContraction K).poly.pt Y')
      = (runSubF K).obj ((chContraction K).poly.pt Y)) :
    subArr (legAtom w hX hY) = eqToHom p ≫ subArr (legAtom w' hX' hY') ≫ eqToHom q := by
  subst hww
  obtain rfl : X = X' := Subtype.ext (hX.symm.trans hX')
  obtain rfl : Y = Y' := Subtype.ext (hY.symm.trans hY')
  simp

/-! ## Reading the bead cuts in the sub-polygraph

A letter of the lifted cut polygraph contracts to the empty word when it is a merge and to its own
1-cell otherwise; `cutArr` is what it names either way. -/

/-- Reading a word of the lifted cut polygraph in the sub-polygraph. -/
noncomputable def cutSubF (K : BPSet) : (chCutPoly K).Word ⥤ (runAtomPoly K).presented :=
  (Polygraph.fwdPre (chCutPoly K) (chCutPicked K)).pathsFunctor ⋙ (chContraction K).words
    ⋙ runSubF K

/-- **A 2-cell of the contracted polygraph out of a run holds in the sub-polygraph** — that is what
its 2-cells are. -/
theorem runSubF_cell {u v : GenObj (chCutLocFunctor.obj K).Gen}
    (α : (chCutLocFunctor.obj K).Rel u v) (hv : eltRep v.as = v.as) :
    (runSubF K).map ((chContraction K).words.map ((chCutLocFunctor.obj K).src α))
      = (runSubF K).map ((chContraction K).words.map ((chCutLocFunctor.obj K).tgt α)) :=
  (runAtomPoly K).quot_src_tgt (x := ⟨((chContraction K).repObj u).as⟩)
    (y := ⟨((chContraction K).repObj v).as⟩) ⟨⟨u, v, α, rfl, rfl⟩, hv⟩

/-- …and so does one of the lifted cut polygraph. -/
theorem cutSubF_cell {u v : (chCutPoly K).V} (α : (chCutPoly K).Rel ⟨u⟩ ⟨v⟩)
    (hv : eltRep v = v) :
    (cutSubF K).map ((chCutPoly K).src α) = (cutSubF K).map ((chCutPoly K).tgt α) :=
  runSubF_cell (Polygraph.InvRel.keep (P := chCutPoly K) (S := chCutPicked K) α) hv

/-- The arrow a bead cut names there. -/
noncomputable def cutArr {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') :
    (cutSubF K).obj ((chCutPoly K).pt z) ⟶ (cutSubF K).obj ((chCutPoly K).pt z') :=
  (cutSubF K).map (Polygraph.cell e).toPath

theorem cutArr_eq {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') :
    cutArr e = (runSubF K).map ((chContraction K).cell
      (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e)) := by
  change (runSubF K).map ((chContraction K).words.map
    ((Polygraph.fwdPre (chCutPoly K) (chCutPicked K)).mapPath (Polygraph.cell e).toPath)) = _
  rw [Prefunctor.mapPath_toPath]
  exact congrArg (runSubF K).map (Paths.lift_toPath (chContraction K).pre
    (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e))

/-- **A merge names a renaming.** -/
theorem cutArr_merge {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z') (he : chCutPicked K e)
    (h : (cutSubF K).obj ((chCutPoly K).pt z) = (cutSubF K).obj ((chCutPoly K).pt z')) :
    cutArr e = eqToHom h := by
  rw [cutArr_eq, (chContraction K).cell_of_S
    (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e) he]
  refine Eq.trans (Paths.map_cellCongr₂ (runSubF K) _ _ _) ?_
  exact eqToHom_sandwich _ (((runSubF K).map_id _).trans (eqToHom_refl _ rfl).symm) _ h

/-- **…and any other cut is its own 1-cell of the contraction.** -/
theorem cutArr_gen {z z' : (chCutPoly K).V} (e : (chCutPoly K).Gen z z')
    (he : ¬ chCutPicked K e) :
    cutArr e = subArr ((chContraction K).genCell
      (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e) he) := by
  rw [cutArr_eq, (chContraction K).cell_of_not_S
    (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e) he]
  rfl

private theorem cutSubF_two {a b c : (chCutPoly K).V} (f : (chCutPoly K).Gen a b)
    (g : (chCutPoly K).Gen b c) :
    (cutSubF K).map ((Quiver.Path.nil.cons (Polygraph.cell f)).cons (Polygraph.cell g))
      = cutArr f ≫ cutArr g := by
  refine Eq.trans ((cutSubF K).map_comp (Quiver.Path.nil.cons (Polygraph.cell f))
    (Polygraph.cell g).toPath) ?_
  refine congrArg (fun t => t ≫ cutArr g) ?_
  refine Eq.trans ((cutSubF K).map_comp
    (Quiver.Path.nil : Quiver.Path ((chCutPoly K).pt a) ((chCutPoly K).pt a))
    (Polygraph.cell f).toPath) ?_
  rw [show (cutSubF K).map (Quiver.Path.nil : Quiver.Path ((chCutPoly K).pt a)
    ((chCutPoly K).pt a)) = 𝟙 _ from (cutSubF K).map_id _, Category.id_comp]
  rfl

/-- **Two two-step factorisations of one codimension-two cut out of a run spell one word.** -/
theorem cutArr_pair {z zm zm' zd : (chCutPoly K).V} (hz : eltRep z = z)
    (e₁ : (chCutPoly K).Gen zd zm) (e₂ : (chCutPoly K).Gen zm z)
    (e₁' : (chCutPoly K).Gen zd zm') (e₂' : (chCutPoly K).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1) :
    cutArr e₁ ≫ cutArr e₂ = cutArr e₁' ≫ cutArr e₂' :=
  (cutSubF_two e₁ e₂).symm.trans
    ((cutSubF_cell (pairCell e₁ e₂ e₁' e₂' hev) hz).trans (cutSubF_two e₁' e₂'))

/-! ## A cut over a base, read at the runs of its two ends -/

/-- The object a 0-cell of the contraction names in the sub-polygraph. -/
noncomputable abbrev subPt (X : (chContraction K).V) : (runAtomPoly K).presented :=
  (runSubF K).obj ((chContraction K).poly.pt X)

theorem subPt_eq {z : (chCutPoly K).V} {X : (chContraction K).V} (hX : eltRep z = X.1) :
    (cutSubF K).obj ((chCutPoly K).pt z) = subPt X :=
  congrArg subPt (Subtype.ext hX : (⟨eltRep z, eltRep_idem z⟩ : (chContraction K).V) = X)

/-- The arrow a cut over a base names between two named runs. -/
noncomputable def atRun {X Y : (chContraction K).V} {z₁ z₂ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1)
    (f : (cutSubF K).obj ((chCutPoly K).pt z₁) ⟶ (cutSubF K).obj ((chCutPoly K).pt z₂)) :
    subPt X ⟶ subPt Y :=
  eqToHom (subPt_eq hX).symm ≫ f ≫ eqToHom (subPt_eq hY)

private theorem eqToHom_sandwich_comp {C : Type*} [Category C] {A B D A' B' D' : C} (h₁ : A = A')
    (h₂ : B = B') (h₃ : D = D') (f : A ⟶ B) (g : B ⟶ D) :
    eqToHom h₁.symm ≫ (f ≫ g) ≫ eqToHom h₃
      = (eqToHom h₁.symm ≫ f ≫ eqToHom h₂) ≫ (eqToHom h₂.symm ≫ g ≫ eqToHom h₃) := by
  subst h₁; subst h₂; subst h₃; simp

theorem atRun_comp {X Y Z : (chContraction K).V} {z₁ z₂ z₃ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1) (hZ : eltRep z₃ = Z.1)
    (f : (cutSubF K).obj ((chCutPoly K).pt z₁) ⟶ (cutSubF K).obj ((chCutPoly K).pt z₂))
    (g : (cutSubF K).obj ((chCutPoly K).pt z₂) ⟶ (cutSubF K).obj ((chCutPoly K).pt z₃)) :
    atRun hX hZ (f ≫ g) = atRun hX hY f ≫ atRun hY hZ g :=
  eqToHom_sandwich_comp (subPt_eq hX) (subPt_eq hY) (subPt_eq hZ) f g

private theorem eqToHom_sandwich_id {C : Type*} [Category C] {A B A' B' : C} (h₁ : A = A')
    (h₂ : B = B') (h : A = B) (h' : A' = B') :
    eqToHom h₁.symm ≫ eqToHom h ≫ eqToHom h₂ = eqToHom h' := by
  subst h₁; subst h₂; subst h; simp

theorem atRun_eqToHom {X Y : (chContraction K).V} {z₁ z₂ : (chCutPoly K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1)
    (h : (cutSubF K).obj ((chCutPoly K).pt z₁) = (cutSubF K).obj ((chCutPoly K).pt z₂))
    (hXY : X = Y) : atRun hX hY (eqToHom h) = eqToHom (congrArg subPt hXY) :=
  eqToHom_sandwich_id (subPt_eq hX) (subPt_eq hY) h _

/-- **An atom's cut, read at the runs it joins, is that atom.** -/
theorem atRun_topCut {N : ℕ} {k : Fin (N - 1)} {z : (chCutPoly K).V}
    (w : zObj (atomComp N k) ⟶ shOf z) {X Y : (chContraction K).V}
    (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRep (eltRestrict z (atomOnes N k ≫ w)) = Y.1) :
    atRun hX hY (cutArr (cutGen (c := eltRestrict z w)
        (c' := eltRestrict z (atomOnes N k ≫ w)) (atomOnes N k) (codim_atomOnes N k) rfl))
      = subArr (legAtom w hX ((eltRep_eq_self rfl).symm.trans hY)) := by
  rw [cutArr_gen _ (fun hm => not_W_atomOnes N k ((merge_iff _).mp hm).1)]
  exact (subArr_legAtom_eq (w' := w) rfl hX ((eltRep_eq_self rfl).symm.trans hY)
    (X' := ⟨eltRep (eltRestrict z w), eltRep_idem _⟩)
    (Y' := ⟨eltRep (eltRestrict z (atomOnes N k ≫ w)), eltRep_idem _⟩) rfl
    (eltRep_eq_self rfl).symm _ _).symm

/-! ## The square and the hexagon over a pair chain

The degree-two chain two parabolic cuts share (`pairChain`) sits over the base carrying the foot's
own crossing permutation (`exists_pairLeg`), and the legs out of it realise the words Artin's two
relations compare.  A merge leg reads as a renaming, so the cells below the square pin the
intermediate cuts as single atoms. -/

theorem crossPerm_ascLeg {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b) :
    crossPerm (dimSum_atomComp N e.idx) (ascLeg e) = a.1 := by
  have h := crossPerm_comp (dimSum_replicate N) (mergeOnes N e.idx) (ascLeg e)
  rw [mergeOnes_ascLeg e, a.crossPerm_arr, crossPerm_eq_one_of_W _ (W_mergeOnes N e.idx),
    mul_one] at h
  exact h.symm

theorem eltRep_legChain {k : Fin (N - 1)} {σ : RunPerm N z} (w : zObj (atomComp N k) ⟶ shOf z)
    (hσ : mergeOnes N k ≫ w = σ.arr) : eltRep (eltRestrict z w) = (runObj σ).1 :=
  (eltRep_eltRestrict_atom w).trans (congrArg (eltRestrict z) hσ)

theorem eltRep_runChain {σ : RunPerm N z} {r : zObj (𝟙^N) ⟶ shOf z} (hσ : r = σ.arr) :
    eltRep (eltRestrict z r) = (runObj σ).1 :=
  (eltRep_eq_self rfl).trans (congrArg (eltRestrict z) hσ)

theorem eltRep_pairChain {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z)
    {σ : RunPerm N z} (hσ : runMerge E hE ≫ Q = σ.arr) :
    eltRep (eltRestrict z Q) = (runObj σ).1 :=
  (eltRestrict_merge_comp Q (W_runMerge E hE) (W_zRunMerge E)
      (congrArg (fun n => zObj (𝟙^n)) hE.symm)).symm.trans (congrArg (eltRestrict z) hσ)

/-- A cut over a base into the chain a leg names. -/
noncomputable def midCut {E : Ch Zbp} (Q : E ⟶ shOf z) {k : Fin (N - 1)}
    (v : zObj (atomComp N k) ⟶ E) (hv : codim v = 1) :
    (chCutPoly K).Gen (eltRestrict z Q) (eltRestrict z (v ≫ Q)) := cutGen v hv rfl

/-- …and the cut out of a run above it, named at the run-arrow it reaches. -/
noncomputable def topCut {E : Ch Zbp} (Q : E ⟶ shOf z) {k : Fin (N - 1)}
    (v : zObj (atomComp N k) ⟶ E) {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)} (hf : codim f = 1)
    {r : zObj (𝟙^N) ⟶ E} (hfv : f ≫ v = r) :
    (chCutPoly K).Gen (eltRestrict z (v ≫ Q)) (eltRestrict z (r ≫ Q)) :=
  cutGen f hf (congrArg (fun t : zObj (𝟙^N) ⟶ shOf z => (wedgeHoms K).map t.op z.2)
    (congrArg (fun t : zObj (𝟙^N) ⟶ E => t ≫ Q) hfv))

theorem atRun_topCut' {k : Fin (N - 1)} {E : Ch Zbp} (Q : E ⟶ shOf z)
    (v : zObj (atomComp N k) ⟶ E) {r : zObj (𝟙^N) ⟶ E} (hfv : atomOnes N k ≫ v = r)
    {X Y : (chContraction K).V} (hX : eltRep (eltRestrict z (v ≫ Q)) = X.1)
    (hY : eltRep (eltRestrict z (r ≫ Q)) = Y.1) (hY' : eltRestrict z (r ≫ Q) = Y.1) :
    atRun hX hY (cutArr (topCut Q v (codim_atomOnes N k) hfv))
      = subArr (legAtom (v ≫ Q) hX
        ((congrArg (fun t : zObj (𝟙^N) ⟶ E => eltRestrict z (t ≫ Q)) hfv).trans hY')) := by
  subst hfv
  exact atRun_topCut (v ≫ Q) hX hY

theorem atRun_merge {z₁ z₂ : (chCutPoly K).V} (e : (chCutPoly K).Gen z₁ z₂)
    (he : chCutPicked K e) {X Y : (chContraction K).V}
    (hX : eltRep z₁ = X.1) (hY : eltRep z₂ = Y.1) (hXY : X = Y) :
    atRun hX hY (cutArr e) = eqToHom (congrArg subPt hXY) :=
  (congrArg (atRun hX hY) (cutArr_merge e he
    ((subPt_eq hX).trans ((congrArg subPt hXY).trans (subPt_eq hY).symm)))).trans
    (atRun_eqToHom hX hY _ hXY)

/-- **Two two-step factorisations over one chain spell one word**, read at the runs of their
ends. -/
theorem legPair {E : Ch Zbp} (Q : E ⟶ shOf z) {k l : Fin (N - 1)}
    {v : zObj (atomComp N k) ⟶ E} (hv : codim v = 1)
    {v' : zObj (atomComp N l) ⟶ E} (hv' : codim v' = 1)
    {f : zObj (𝟙^N) ⟶ zObj (atomComp N k)} (hf : codim f = 1)
    {f' : zObj (𝟙^N) ⟶ zObj (atomComp N l)} (hf' : codim f' = 1)
    {r : zObj (𝟙^N) ⟶ E} (hfv : f ≫ v = r) (hfv' : f' ≫ v' = r)
    {X M M' Y : (chContraction K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hM : eltRep (eltRestrict z (v ≫ Q)) = M.1) (hM' : eltRep (eltRestrict z (v' ≫ Q)) = M'.1)
    (hY : eltRep (eltRestrict z (r ≫ Q)) = Y.1) :
    atRun hX hM (cutArr (midCut Q v hv)) ≫ atRun hM hY (cutArr (topCut Q v hf hfv))
      = atRun hX hM' (cutArr (midCut Q v' hv')) ≫ atRun hM' hY (cutArr (topCut Q v' hf' hfv')) := by
  rw [← atRun_comp hX hM hY, ← atRun_comp hX hM' hY]
  exact congrArg (atRun hX hY)
    (cutArr_pair (eltRep_eq_self rfl) _ _ _ _ (hfv.trans hfv'.symm))


theorem subArr_ascAtom_eq_legAtom {a b : RunPerm N z} (e : Ascent (runDescents N z).perm a b)
    {w : zObj (atomComp N e.idx) ⟶ shOf z} (hw : ascLeg e = w)
    {X Y : (chContraction K).V} (hX : eltRep (eltRestrict z w) = X.1)
    (hY : eltRestrict z (atomOnes N e.idx ≫ w) = Y.1)
    (p : subPt (runObj a) = subPt X) (q : subPt Y = subPt (runObj b)) :
    subArr (ascAtom e) = eqToHom p ≫ subArr (legAtom w hX hY) ≫ eqToHom q :=
  subArr_legAtom_eq hw _ _ hX hY p q


/-! ## A 1-cell read at an explicit strand count

`genTop` and `runBot` are taken at `vCount`; the cells below the square need them at the count the
pair chain names, so both come with an explicit `hM` and `subst` moves between them. -/

/-- **A chain its own run merges onto has an all-ones shape.** -/
theorem shOf_eq_ones_of_eltRep {M : ℕ} {c : (chCutPoly K).V} (h : eltRep c = c)
    (hM : dimSum (shOf c).dims = M) : shOf c = zObj (𝟙^M) :=
  (congrArg (fun s : (chCutPoly K).V => shOf s) h).symm.trans
    (congrArg (fun n => zObj (𝟙^n)) hM)

noncomputable def genTopAt {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : RunPerm M g.dom :=
  runOf (runMerge (shOf g.cod) ((dimSum_eq_of_hom (genCut g)).trans hM) ≫ genCut g)

theorem arr_genTopAt {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) :
    (genTopAt g hM).arr
      = runMerge (shOf g.cod) ((dimSum_eq_of_hom (genCut g)).trans hM) ≫ genCut g := arr_runOf _

theorem runObj_genTopAt {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : (runObj (genTopAt g hM)).1 = B.1 := by
  subst hM; exact runObj_genTop g

theorem subObj_runBot_gen {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : subPt A = subObj (runBot g.dom hM) :=
  (congrArg subPt (Subtype.ext ((runObj_runBot g.dom hM).trans g.rep_dom))).symm

theorem subObj_genTopAt {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) : subObj (genTopAt g hM) = subPt B :=
  congrArg subPt (Subtype.ext (runObj_genTopAt g hM))

/-- **A 1-cell whose cut crosses one pair is a single atom**, at any naming of the strand count. -/
theorem subArr_of_permLen_eq_one {A B : (chContraction K).V} (g : (chContraction K).Gen A B)
    {M : ℕ} (hM : dimSum (shOf g.dom).dims = M) (hg : ¬ RunCut g)
    (h : permLen (genTopAt g hM).1 = 1)
    (p : subPt A = subObj (runBot g.dom hM)) (q : subObj (genTopAt g hM) = subPt B) :
    ∃ e : Ascent (runDescents M g.dom).perm (runBot g.dom hM) (genTopAt g hM),
      subArr g = eqToHom p ≫ subArr (ascAtom e) ≫ eqToHom q := by
  subst hM
  obtain ⟨e, he⟩ := climbArr_of_permLen_succ (genClimb g)
    (by rw [runBot_val, permLen_one, Nat.zero_add]; exact h)
  exact ⟨e, (subArr_eq_climbArr g hg).trans (by rw [he]; rfl)⟩

/-! ## A run over a refinement, read over the chain it refines

`eltRestrict` is functorial on the nose, so a cut out of a run over `eltRestrict u t` *is* the cut
over `u` along the composite: only the 0-cells' names change, and the crossings add.  This sits
before the pair chain because the cells below the square are read at a leg's own base. -/

/-- A run over a chain's refinement, read over the chain. -/
noncomputable def pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : RunPerm M u := runOf (σ.arr ≫ t)

theorem arr_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : (pushPerm t σ).arr = σ.arr ≫ t := arr_runOf _

theorem val_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) (σ : RunPerm M (eltRestrict u t)) :
    (pushPerm t σ).1 = crossPerm hd t * σ.1 :=
  (runOf_val (σ.arr ≫ t)).trans ((crossPerm_comp (dimSum_replicate M) σ.arr t).trans
    (congrArg (fun p => crossPerm hd t * p) σ.crossPerm_arr))

theorem permLen_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) (σ : RunPerm M (eltRestrict u t)) :
    permLen (pushPerm t σ).1 = permLen σ.1 + permLen (crossPerm hd t) :=
  ((congrArg permLen (runOf_val (σ.arr ≫ t))).trans
      (permLen_crossPerm_comp (dimSum_replicate M) σ.arr t)).trans
    (congrArg (fun n => n + permLen (crossPerm hd t)) (congrArg permLen σ.crossPerm_arr))

theorem runObj_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : (runObj (pushPerm t σ)).1 = (runObj σ).1 :=
  congrArg (eltRestrict u) (arr_pushPerm t σ)

theorem subObj_pushPerm {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (σ : RunPerm M (eltRestrict u t)) : subObj (pushPerm t σ) = subObj σ :=
  congrArg subPt (Subtype.ext (runObj_pushPerm t σ))

/-- **Pushing an ascent onto a coarser base** — crossings add, so the length still goes up by one
and `ascent_of_permLen_succ` reads the ascent back off it. -/
noncomputable def pushAscent {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (e : Ascent (runDescents M (eltRestrict u t)).perm a b) :
    Ascent (runDescents M u).perm (pushPerm t a) (pushPerm t b) where
  idx := e.idx
  asc := by
    have hlb : permLen b.1 = permLen a.1 + 1 := e.permLen_eq
    have hperm : (pushPerm t b).1 = (pushPerm t a).1 * adjT e.idx := by
      rw [val_pushPerm t hd b, val_pushPerm t hd a, mul_assoc]
      exact congrArg (fun p => crossPerm hd t * p) e.perm_eq
    refine ascent_of_permLen_succ ?_
    rw [runDescents_perm, ← hperm, permLen_pushPerm t hd b, permLen_pushPerm t hd a]
    omega
  perm_eq := by
    rw [runDescents_perm, runDescents_perm, val_pushPerm t hd b, val_pushPerm t hd a, mul_assoc]
    exact congrArg (fun p => crossPerm hd t * p) e.perm_eq

/-- …and a whole climb. -/
noncomputable def pushClimb {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a : RunPerm M (eltRestrict u t)} :
    ∀ {b : RunPerm M (eltRestrict u t)}, Climb (runDescents M (eltRestrict u t)).perm a b →
      Climb (runDescents M u).perm (pushPerm t a) (pushPerm t b)
  | _, .nil => .nil
  | _, .cons R e => (pushClimb t hd R).cons (pushAscent t hd e)

/-- **A pushed atom is that atom** — the leg composes with the refinement, and the chain it cuts is
the same one. -/
theorem subArr_ascAtom_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (e : Ascent (runDescents M (eltRestrict u t)).perm a b)
    (p : subObj (pushPerm t a) = subObj a) (q : subObj b = subObj (pushPerm t b)) :
    subArr (ascAtom (pushAscent t hd e)) = eqToHom p ≫ subArr (ascAtom e) ≫ eqToHom q := by
  have hleg : ascLeg (pushAscent t hd e) = ascLeg e ≫ t :=
    hom_ext_of_crossPerm (h := dimSum_atomComp M e.idx)
      (((crossPerm_ascLeg (pushAscent t hd e)).trans (val_pushPerm t hd a)).trans
        ((congrArg (fun p => crossPerm hd t * p) (crossPerm_ascLeg e).symm).trans
          (crossPerm_comp (dimSum_atomComp M e.idx) (ascLeg e) t).symm))
  exact subArr_ascAtom_eq_legAtom (pushAscent t hd e) hleg (X := runObj a) (Y := runObj b)
    (eltRep_ascLeg e) (congrArg (eltRestrict (eltRestrict u t)) (atomOnes_ascLeg e)) p q

/-- **A mid cut above a merge leg is the atom at that leg** — the cell below it has a merge on
top. -/
theorem atRun_midCut_merge {E : Ch Zbp} (Q : E ⟶ shOf z) (hdeg : degree E = 2)
    {k l : Fin (N - 1)} {m : zObj (atomComp N k) ⟶ E} (hWm : W Zbp m)
    {w : zObj (atomComp N l) ⟶ E} (hsq : mergeOnes N l ≫ w = atomOnes N k ≫ m)
    {X M : (chContraction K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hm : eltRep (eltRestrict z (m ≫ Q)) = X.1) (hw : eltRep (eltRestrict z (w ≫ Q)) = M.1)
    (hMt : eltRestrict z ((atomOnes N k ≫ m) ≫ Q) = M.1) :
    subArr (legAtom (m ≫ Q) hm hMt) = atRun hX hw (cutArr (midCut Q w (codim_leg hdeg w))) := by
  have c1 := legPair Q (codim_leg hdeg m) (codim_leg hdeg w) (codim_atomOnes N k)
    (codim_mergeOnes N l) (r := atomOnes N k ≫ m) rfl hsq hX hm hw
    ((eltRep_eq_self rfl).trans hMt)
  rw [atRun_merge (midCut Q m (codim_leg hdeg m))
      ((merge_iff m).mpr ⟨hWm, codim_leg hdeg m⟩) _ _ (rfl : X = X),
    atRun_topCut' Q m (r := atomOnes N k ≫ m) rfl (X := X) (Y := M) hm
      ((eltRep_eq_self rfl).trans hMt) hMt,
    atRun_merge (topCut Q w (codim_mergeOnes N l) hsq)
      ((merge_iff _).mpr ⟨W_mergeOnes N l, codim_mergeOnes N l⟩) _ _ (rfl : M = M)] at c1
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using c1

/-- **A mid cut is the shorter one below it followed by an atom** — the cell between them has a
merge on top. -/
theorem atRun_midCut_step {E : Ch Zbp} (Q : E ⟶ shOf z) (hdeg : degree E = 2)
    {k l : Fin (N - 1)} {w₂ : zObj (atomComp N k) ⟶ E} {w₁ : zObj (atomComp N l) ⟶ E}
    (hsq : atomOnes N l ≫ w₁ = mergeOnes N k ≫ w₂)
    {X M₂ M₁ : (chContraction K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hw₂ : eltRep (eltRestrict z (w₂ ≫ Q)) = M₂.1)
    (hw₁ : eltRep (eltRestrict z (w₁ ≫ Q)) = M₁.1)
    (hMt : eltRestrict z ((mergeOnes N k ≫ w₂) ≫ Q) = M₂.1) :
    atRun hX hw₂ (cutArr (midCut Q w₂ (codim_leg hdeg w₂)))
      = atRun hX hw₁ (cutArr (midCut Q w₁ (codim_leg hdeg w₁)))
        ≫ subArr (legAtom (w₁ ≫ Q) hw₁
          ((congrArg (fun t : zObj (𝟙^N) ⟶ E => eltRestrict z (t ≫ Q)) hsq).trans hMt)) := by
  have c1 := legPair Q (codim_leg hdeg w₂) (codim_leg hdeg w₁) (codim_mergeOnes N k)
    (codim_atomOnes N l) (r := mergeOnes N k ≫ w₂) rfl hsq hX hw₂ hw₁
    ((eltRep_eq_self rfl).trans hMt)
  rw [atRun_merge (topCut Q w₂ (codim_mergeOnes N k) rfl)
      ((merge_iff _).mpr ⟨W_mergeOnes N k, codim_mergeOnes N k⟩) _ _ (rfl : M₂ = M₂),
    atRun_topCut' Q w₁ (r := mergeOnes N k ≫ w₂) hsq (X := M₁) (Y := M₂) hw₁
      ((eltRep_eq_self rfl).trans hMt) hMt] at c1
  simpa only [eqToHom_refl, Category.comp_id] using c1

/-- **Two mid cuts with a common atom above them spell one word.** -/
theorem atRun_midCut_pair {E : Ch Zbp} (Q : E ⟶ shOf z) (hdeg : degree E = 2)
    {k l : Fin (N - 1)} {w : zObj (atomComp N k) ⟶ E} {w' : zObj (atomComp N l) ⟶ E}
    (hsq : atomOnes N l ≫ w' = atomOnes N k ≫ w)
    {X M M' Y : (chContraction K).V} (hX : eltRep (eltRestrict z Q) = X.1)
    (hw : eltRep (eltRestrict z (w ≫ Q)) = M.1) (hw' : eltRep (eltRestrict z (w' ≫ Q)) = M'.1)
    (hY : eltRestrict z ((atomOnes N k ≫ w) ≫ Q) = Y.1) :
    atRun hX hw (cutArr (midCut Q w (codim_leg hdeg w))) ≫ subArr (legAtom (w ≫ Q) hw hY)
      = atRun hX hw' (cutArr (midCut Q w' (codim_leg hdeg w')))
        ≫ subArr (legAtom (w' ≫ Q) hw'
          ((congrArg (fun t : zObj (𝟙^N) ⟶ E => eltRestrict z (t ≫ Q)) hsq).trans hY)) := by
  have c1 := legPair Q (codim_leg hdeg w) (codim_leg hdeg w') (codim_atomOnes N k)
    (codim_atomOnes N l) (r := atomOnes N k ≫ w) rfl hsq hX hw hw'
    ((eltRep_eq_self rfl).trans hY)
  rw [atRun_topCut' Q w (r := atomOnes N k ≫ w) rfl (X := M) (Y := Y) hw
      ((eltRep_eq_self rfl).trans hY) hY,
    atRun_topCut' Q w' (r := atomOnes N k ≫ w) hsq (X := M') (Y := Y) hw'
      ((eltRep_eq_self rfl).trans hY) hY] at c1
  exact c1

/-- **The crossing permutation of a leg into a placed chain.** -/
theorem crossPerm_leg_comp {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z)
    {σ : Perm (Fin N)} (hQ : crossPerm hE Q = σ) {k : Fin (N - 1)}
    (w : zObj (atomComp N k) ⟶ E) {s : Perm (Fin N)}
    (hw : crossPerm (dimSum_atomComp N k) w = s) :
    crossPerm (dimSum_atomComp N k) (w ≫ Q) = σ * s := by
  rw [crossPerm_comp (dimSum_atomComp N k) w Q, hQ, hw]

/-- **The run a cut out of a leg into a placed chain reaches.** -/
theorem leg_run {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z) {σ : Perm (Fin N)}
    (hQ : crossPerm hE Q = σ) {k : Fin (N - 1)} (w : zObj (atomComp N k) ⟶ E)
    {s : Perm (Fin N)} (hw : crossPerm (dimSum_atomComp N k) w = s)
    (g : zObj (𝟙^N) ⟶ zObj (atomComp N k)) {t : Perm (Fin N)}
    (hg : crossPerm (dimSum_replicate N) g = t) {τ : RunPerm N z} (hτ : σ * s * t = τ.1) :
    g ≫ w ≫ Q = τ.arr := by
  refine τ.eq_arr ?_
  rw [crossPerm_comp (dimSum_replicate N) g (w ≫ Q), crossPerm_leg_comp hE Q hQ w hw, hg]
  exact hτ

/-- …and the run the placed chain's own merge reaches. -/
theorem base_run {E : Ch Zbp} (hE : dimSum E.dims = N) (Q : E ⟶ shOf z) {c : RunPerm N z}
    (hQ : crossPerm hE Q = c.1) : runMerge E hE ≫ Q = c.arr := by
  refine c.eq_arr ?_
  rw [crossPerm_comp (dimSum_replicate N) (runMerge E hE) Q, hQ,
    crossPerm_eq_one_of_W _ (W_runMerge E hE), mul_one]

/-- **The degree-two chain of two parabolic cuts, placed over a run** — its own run is that run. -/
theorem exists_pairQ (hz : dimSum (shOf z).dims = N) {i j : Fin (N - 1)}
    (hij' : (i : ℕ) ≠ (j : ℕ)) {c : RunPerm N z}
    (hci : c.1 (adjLo i) < c.1 (adjHi i)) (hcj : c.1 (adjLo j) < c.1 (adjHi j))
    (hi : ∃ σ : RunPerm N z, σ.1 = c.1 * adjT i) (hj : ∃ σ : RunPerm N z, σ.1 = c.1 * adjT j) :
    ∃ Q : pairChain N i j hij' ⟶ shOf z, crossPerm (dimSum_pairChain hij') Q = c.1 := by
  refine exists_pairLeg hij' hz ?_ ?_ c.crossPerm_arr
  · rintro k (hk | hk)
    · obtain rfl : k = i := Fin.ext hk
      obtain ⟨σ, hσ⟩ := hi
      refine index_adj_eq_of_descent hz σ.arr ?_
      simp only [RunPerm.crossPerm_arr, hσ, Equiv.Perm.mul_apply, adjT_lo, adjT_hi]
      exact hci
    · obtain rfl : k = j := Fin.ext hk
      obtain ⟨σ, hσ⟩ := hj
      refine index_adj_eq_of_descent hz σ.arr ?_
      simp only [RunPerm.crossPerm_arr, hσ, Equiv.Perm.mul_apply, adjT_lo, adjT_hi]
      exact hcj
  · rintro k (hk | hk)
    · obtain rfl : k = i := Fin.ext hk; exact hci
    · obtain rfl : k = j := Fin.ext hk; exact hcj

/-- **Two far-apart atoms commute** — the square of the pair chain, placed over the foot. -/
theorem subArr_ascAtom_comm (hz : dimSum (shOf z).dims = N) {c vi vj v : RunPerm N z}
    (a : Ascent (runDescents N z).perm vi v) (b : Ascent (runDescents N z).perm c vi)
    (a' : Ascent (runDescents N z).perm vj v) (b' : Ascent (runDescents N z).perm c vj)
    (hij : (a.idx : ℕ) + 1 < (a'.idx : ℕ)) (hb : b.idx = a'.idx) (hb' : b'.idx = a.idx) :
    subArr (ascAtom b) ≫ subArr (ascAtom a) = subArr (ascAtom b') ≫ subArr (ascAtom a') := by
  obtain ⟨bj, basc, bperm⟩ := b
  obtain ⟨bi, b'asc, b'perm⟩ := b'
  subst hb
  subst hb'
  have hij' : (a.idx : ℕ) ≠ (a'.idx : ℕ) := by omega
  have hE : dimSum (pairChain N a.idx a'.idx hij').dims = N := dimSum_pairChain hij'
  have hdeg : degree (pairChain N a.idx a'.idx hij') = 2 := degree_pairChain hij'
  obtain ⟨Q, hQ⟩ := exists_pairQ hz hij' b'asc basc ⟨vj, b'perm⟩ ⟨vi, bperm⟩
  obtain ⟨mi, hWmi, hui⟩ := exists_merge_leg a.idx (nonempty_left_pairChain hij')
  obtain ⟨mj, hWmj, huj⟩ := exists_merge_leg a'.idx (nonempty_right_pairChain hij')
  obtain ⟨wj, hwj⟩ := exists_leg a'.idx hE (nonempty_right_pairChain hij') (σ := adjT a.idx)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi, hwi⟩ := exists_leg a.idx hE (nonempty_left_pairChain hij') (σ := adjT a'.idx)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  have hcmi : crossPerm (dimSum_atomComp N a.idx) mi = 1 := (W_iff_crossPerm_eq_one _ mi).mp hWmi
  have hcmj : crossPerm (dimSum_atomComp N a'.idx) mj = 1 := (W_iff_crossPerm_eq_one _ mj).mp hWmj
  have hcone : ∀ k : Fin (N - 1), crossPerm (dimSum_replicate N) (mergeOnes N k) = 1 :=
    fun k => crossPerm_eq_one_of_W _ (W_mergeOnes N k)
  have hsq1 : mergeOnes N a.idx ≫ wi = atomOnes N a'.idx ≫ mj :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [huj, crossPerm_comp, hwi, hcone, mul_one])
  have hsq2 : mergeOnes N a'.idx ≫ wj = atomOnes N a.idx ≫ mi :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [hui, crossPerm_comp, hwj, hcone, mul_one])
  have hsq3 : atomOnes N a'.idx ≫ wj = atomOnes N a.idx ≫ wi :=
    atom_pair_eq (by rw [hwi, hwj]; exact adjT_comm a.idx a'.idx hij)
  have hmjc := leg_run hE Q hQ mj hcmj (mergeOnes N a'.idx) (hcone _) (by rw [mul_one, mul_one])
  have hmic := leg_run hE Q hQ mi hcmi (mergeOnes N a.idx) (hcone _) (by rw [mul_one, mul_one])
  have hmjvi := leg_run hE Q hQ mj hcmj (atomOnes N a'.idx) (crossPerm_atomOnes N a'.idx)
    (by rw [mul_one]; exact bperm.symm)
  have hmivj := leg_run hE Q hQ mi hcmi (atomOnes N a.idx) (crossPerm_atomOnes N a.idx)
    (by rw [mul_one]; exact b'perm.symm)
  have hwivi := leg_run hE Q hQ wi hwi (mergeOnes N a.idx) (hcone _) (by
    rw [mul_one]; exact bperm.symm)
  have hwjvj := leg_run hE Q hQ wj hwj (mergeOnes N a'.idx) (hcone _) (by
    rw [mul_one]; exact b'perm.symm)
  have hwiv := leg_run hE Q hQ wi hwi (atomOnes N a.idx) (crossPerm_atomOnes N a.idx)
    ((congrArg (fun s => s * adjT a.idx) bperm.symm).trans a.perm_eq.symm)
  have hwjv := leg_run hE Q hQ wj hwj (atomOnes N a'.idx) (crossPerm_atomOnes N a'.idx)
    ((congrArg (fun s => s * adjT a'.idx) b'perm.symm).trans a'.perm_eq.symm)
  have cA := atRun_midCut_merge Q hdeg hWmj hsq1 (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (mj ≫ Q) hmjc) (eltRep_legChain (wi ≫ Q) hwivi)
    (congrArg (eltRestrict z) hmjvi)
  have cB := atRun_midCut_merge Q hdeg hWmi hsq2 (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (mi ≫ Q) hmic) (eltRep_legChain (wj ≫ Q) hwjvj)
    (congrArg (eltRestrict z) hmivj)
  have cC := atRun_midCut_pair Q hdeg hsq3 (Y := runObj v)
    (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (wi ≫ Q) hwivi) (eltRep_legChain (wj ≫ Q) hwjvj)
    (congrArg (eltRestrict z) hwiv)
  have hlegb : ascLeg (⟨a'.idx, basc, bperm⟩ : Ascent (runDescents N z).perm c vi) = mj ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a'.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ mj hcmj, mul_one])
  have hlegb' : ascLeg (⟨a.idx, b'asc, b'perm⟩ : Ascent (runDescents N z).perm c vj) = mi ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ mi hcmi, mul_one])
  have hlega : ascLeg a = wi ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wi hwi]; exact bperm)
  have hlega' : ascLeg a' = wj ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a'.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wj hwj]; exact b'perm)
  rw [subArr_ascAtom_eq_legAtom _ hlegb (X := runObj c) (Y := runObj vi)
      (eltRep_legChain (mj ≫ Q) hmjc) (congrArg (eltRestrict z) hmjvi) rfl rfl,
    subArr_ascAtom_eq_legAtom a hlega (X := runObj vi) (Y := runObj v)
      (eltRep_legChain (wi ≫ Q) hwivi) (congrArg (eltRestrict z) hwiv) rfl rfl,
    subArr_ascAtom_eq_legAtom _ hlegb' (X := runObj c) (Y := runObj vj)
      (eltRep_legChain (mi ≫ Q) hmic) (congrArg (eltRestrict z) hmivj) rfl rfl,
    subArr_ascAtom_eq_legAtom a' hlega' (X := runObj vj) (Y := runObj v)
      (eltRep_legChain (wj ≫ Q) hwjvj) (congrArg (eltRestrict z) hwjv) rfl rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [cA, cB]
  exact cC

/-- **Two adjacent atoms braid** — the hexagon of the pair chain, its merge legs pinning the two
intermediate cuts. -/
theorem subArr_ascAtom_braid (hz : dimSum (shOf z).dims = N) {c vij vi v vji vj : RunPerm N z}
    (a₁ : Ascent (runDescents N z).perm vi v) (a₂ : Ascent (runDescents N z).perm vij vi)
    (a₃ : Ascent (runDescents N z).perm c vij) (b₁ : Ascent (runDescents N z).perm vj v)
    (b₂ : Ascent (runDescents N z).perm vji vj) (b₃ : Ascent (runDescents N z).perm c vji)
    (hij : (b₁.idx : ℕ) = (a₁.idx : ℕ) + 1) (h₂ : a₂.idx = b₁.idx) (h₃ : a₃.idx = a₁.idx)
    (h₂' : b₂.idx = a₁.idx) (h₃' : b₃.idx = b₁.idx) :
    subArr (ascAtom a₃) ≫ subArr (ascAtom a₂) ≫ subArr (ascAtom a₁)
      = subArr (ascAtom b₃) ≫ subArr (ascAtom b₂) ≫ subArr (ascAtom b₁) := by
  obtain ⟨x₂, a₂asc, a₂perm⟩ := a₂
  obtain ⟨x₃, a₃asc, a₃perm⟩ := a₃
  obtain ⟨y₂, b₂asc, b₂perm⟩ := b₂
  obtain ⟨y₃, b₃asc, b₃perm⟩ := b₃
  subst h₂
  subst h₃
  subst h₂'
  subst h₃'
  have hij' : (a₁.idx : ℕ) ≠ (b₁.idx : ℕ) := by omega
  have hE : dimSum (pairChain N a₁.idx b₁.idx hij').dims = N := dimSum_pairChain hij'
  have hdeg : degree (pairChain N a₁.idx b₁.idx hij') = 2 := degree_pairChain hij'
  obtain ⟨Q, hQ⟩ := exists_pairQ hz hij' a₃asc b₃asc ⟨vij, a₃perm⟩ ⟨vji, b₃perm⟩
  obtain ⟨mi, hWmi, hui⟩ := exists_merge_leg a₁.idx (nonempty_left_pairChain hij')
  obtain ⟨mj, hWmj, huj⟩ := exists_merge_leg b₁.idx (nonempty_right_pairChain hij')
  obtain ⟨wj₁, hwj₁⟩ := exists_leg b₁.idx hE (nonempty_right_pairChain hij') (σ := adjT a₁.idx)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi₁, hwi₁⟩ := exists_leg a₁.idx hE (nonempty_left_pairChain hij') (σ := adjT b₁.idx)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  obtain ⟨wi₂, hwi₂⟩ := exists_leg a₁.idx hE (nonempty_left_pairChain hij')
    (σ := adjT a₁.idx * adjT b₁.idx)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes N b₁.idx ≫ wj₁) (by rw [crossPerm_comp, hwj₁, crossPerm_atomOnes])
  obtain ⟨wj₂, hwj₂⟩ := exists_leg b₁.idx hE (nonempty_right_pairChain hij')
    (σ := adjT b₁.idx * adjT a₁.idx)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes N a₁.idx ≫ wi₁) (by rw [crossPerm_comp, hwi₁, crossPerm_atomOnes])
  have hcmi : crossPerm (dimSum_atomComp N a₁.idx) mi = 1 := (W_iff_crossPerm_eq_one _ mi).mp hWmi
  have hcmj : crossPerm (dimSum_atomComp N b₁.idx) mj = 1 := (W_iff_crossPerm_eq_one _ mj).mp hWmj
  have hcone : ∀ k : Fin (N - 1), crossPerm (dimSum_replicate N) (mergeOnes N k) = 1 :=
    fun k => crossPerm_eq_one_of_W _ (W_mergeOnes N k)
  have hsqA3 : mergeOnes N b₁.idx ≫ wj₁ = atomOnes N a₁.idx ≫ mi :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [crossPerm_comp, hwj₁, hcone, mul_one, hui])
  have hsqB3 : mergeOnes N a₁.idx ≫ wi₁ = atomOnes N b₁.idx ≫ mj :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [crossPerm_comp, hwi₁, hcone, mul_one, huj])
  have hsqA : atomOnes N b₁.idx ≫ wj₁ = mergeOnes N a₁.idx ≫ wi₂ :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [crossPerm_comp, crossPerm_comp, hwj₁, hwi₂, crossPerm_atomOnes, hcone, mul_one])
  have hsqB : atomOnes N a₁.idx ≫ wi₁ = mergeOnes N b₁.idx ≫ wj₂ :=
    hom_ext_of_crossPerm (h := dimSum_replicate N) (by
      rw [crossPerm_comp, crossPerm_comp, hwi₁, hwj₂, crossPerm_atomOnes, hcone, mul_one])
  have hsqC : atomOnes N b₁.idx ≫ wj₂ = atomOnes N a₁.idx ≫ wi₂ :=
    atom_pair_eq (by rw [hwi₂, hwj₂]; exact (adjT_braid a₁.idx b₁.idx hij).symm)
  have hvi : c.1 * (adjT a₁.idx * adjT b₁.idx) = vi.1 :=
    (mul_assoc c.1 (adjT a₁.idx) (adjT b₁.idx)).symm.trans
      ((congrArg (fun s => s * adjT b₁.idx) a₃perm.symm).trans a₂perm.symm)
  have hvj : c.1 * (adjT b₁.idx * adjT a₁.idx) = vj.1 :=
    (mul_assoc c.1 (adjT b₁.idx) (adjT a₁.idx)).symm.trans
      ((congrArg (fun s => s * adjT a₁.idx) b₃perm.symm).trans b₂perm.symm)
  have hmic := leg_run hE Q hQ mi hcmi (mergeOnes N a₁.idx) (hcone _) (by rw [mul_one, mul_one])
  have hmjc := leg_run hE Q hQ mj hcmj (mergeOnes N b₁.idx) (hcone _) (by rw [mul_one, mul_one])
  have hmivij := leg_run hE Q hQ mi hcmi (atomOnes N a₁.idx) (crossPerm_atomOnes N a₁.idx)
    (by rw [mul_one]; exact a₃perm.symm)
  have hmjvji := leg_run hE Q hQ mj hcmj (atomOnes N b₁.idx) (crossPerm_atomOnes N b₁.idx)
    (by rw [mul_one]; exact b₃perm.symm)
  have hwj₁vij := leg_run hE Q hQ wj₁ hwj₁ (mergeOnes N b₁.idx) (hcone _) (by
    rw [mul_one]; exact a₃perm.symm)
  have hwi₁vji := leg_run hE Q hQ wi₁ hwi₁ (mergeOnes N a₁.idx) (hcone _) (by
    rw [mul_one]; exact b₃perm.symm)
  have hwj₁vi := leg_run hE Q hQ wj₁ hwj₁ (atomOnes N b₁.idx) (crossPerm_atomOnes N b₁.idx)
    ((congrArg (fun s => s * adjT b₁.idx) a₃perm.symm).trans a₂perm.symm)
  have hwi₁vj := leg_run hE Q hQ wi₁ hwi₁ (atomOnes N a₁.idx) (crossPerm_atomOnes N a₁.idx)
    ((congrArg (fun s => s * adjT a₁.idx) b₃perm.symm).trans b₂perm.symm)
  have hwi₂vi := leg_run hE Q hQ wi₂ hwi₂ (mergeOnes N a₁.idx) (hcone _) (by
    rw [mul_one]; exact hvi)
  have hwj₂vj := leg_run hE Q hQ wj₂ hwj₂ (mergeOnes N b₁.idx) (hcone _) (by
    rw [mul_one]; exact hvj)
  have hwi₂v := leg_run hE Q hQ wi₂ hwi₂ (atomOnes N a₁.idx) (crossPerm_atomOnes N a₁.idx)
    ((congrArg (fun s => s * adjT a₁.idx) hvi).trans a₁.perm_eq.symm)
  have hwj₂v := leg_run hE Q hQ wj₂ hwj₂ (atomOnes N b₁.idx) (crossPerm_atomOnes N b₁.idx)
    ((congrArg (fun s => s * adjT b₁.idx) hvj).trans b₁.perm_eq.symm)
  have cA3 := atRun_midCut_merge Q hdeg hWmi hsqA3 (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (mi ≫ Q) hmic) (eltRep_legChain (wj₁ ≫ Q) hwj₁vij)
    (congrArg (eltRestrict z) hmivij)
  have cB3 := atRun_midCut_merge Q hdeg hWmj hsqB3 (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (mj ≫ Q) hmjc) (eltRep_legChain (wi₁ ≫ Q) hwi₁vji)
    (congrArg (eltRestrict z) hmjvji)
  have cA := atRun_midCut_step Q hdeg hsqA (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (wi₂ ≫ Q) hwi₂vi) (eltRep_legChain (wj₁ ≫ Q) hwj₁vij)
    (congrArg (eltRestrict z) hwi₂vi)
  have cB := atRun_midCut_step Q hdeg hsqB (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (wj₂ ≫ Q) hwj₂vj) (eltRep_legChain (wi₁ ≫ Q) hwi₁vji)
    (congrArg (eltRestrict z) hwj₂vj)
  have cC := atRun_midCut_pair Q hdeg hsqC (Y := runObj v)
    (eltRep_pairChain hE Q (base_run hE Q hQ))
    (eltRep_legChain (wi₂ ≫ Q) hwi₂vi) (eltRep_legChain (wj₂ ≫ Q) hwj₂vj)
    (congrArg (eltRestrict z) hwi₂v)
  have hlega₃ : ascLeg (⟨a₁.idx, a₃asc, a₃perm⟩ : Ascent (runDescents N z).perm c vij)
      = mi ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ mi hcmi, mul_one])
  have hlegb₃ : ascLeg (⟨b₁.idx, b₃asc, b₃perm⟩ : Ascent (runDescents N z).perm c vji)
      = mj ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N b₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ mj hcmj, mul_one])
  have hlega₂ : ascLeg (⟨b₁.idx, a₂asc, a₂perm⟩ : Ascent (runDescents N z).perm vij vi)
      = wj₁ ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N b₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wj₁ hwj₁]; exact a₃perm)
  have hlegb₂ : ascLeg (⟨a₁.idx, b₂asc, b₂perm⟩ : Ascent (runDescents N z).perm vji vj)
      = wi₁ ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wi₁ hwi₁]; exact b₃perm)
  have hlega₁ : ascLeg a₁ = wi₂ ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N a₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wi₂ hwi₂]; exact hvi.symm)
  have hlegb₁ : ascLeg b₁ = wj₂ ≫ Q :=
    hom_ext_of_crossPerm (h := dimSum_atomComp N b₁.idx) (by
      rw [crossPerm_ascLeg, crossPerm_leg_comp hE Q hQ wj₂ hwj₂]; exact hvj.symm)
  rw [subArr_ascAtom_eq_legAtom _ hlega₃ (X := runObj c) (Y := runObj vij)
      (eltRep_legChain (mi ≫ Q) hmic) (congrArg (eltRestrict z) hmivij) rfl rfl,
    subArr_ascAtom_eq_legAtom _ hlega₂ (X := runObj vij) (Y := runObj vi)
      (eltRep_legChain (wj₁ ≫ Q) hwj₁vij) (congrArg (eltRestrict z) hwj₁vi) rfl rfl,
    subArr_ascAtom_eq_legAtom a₁ hlega₁ (X := runObj vi) (Y := runObj v)
      (eltRep_legChain (wi₂ ≫ Q) hwi₂vi) (congrArg (eltRestrict z) hwi₂v) rfl rfl,
    subArr_ascAtom_eq_legAtom _ hlegb₃ (X := runObj c) (Y := runObj vji)
      (eltRep_legChain (mj ≫ Q) hmjc) (congrArg (eltRestrict z) hmjvji) rfl rfl,
    subArr_ascAtom_eq_legAtom _ hlegb₂ (X := runObj vji) (Y := runObj vj)
      (eltRep_legChain (wi₁ ≫ Q) hwi₁vji) (congrArg (eltRestrict z) hwi₁vj) rfl rfl,
    subArr_ascAtom_eq_legAtom b₁ hlegb₁ (X := runObj vj) (Y := runObj v)
      (eltRep_legChain (wj₂ ≫ Q) hwj₂vj) (congrArg (eltRestrict z) hwj₂v) rfl rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← cA3] at cA
  rw [← cB3] at cB
  rw [cA, cB] at cC
  simpa only [Category.assoc] using cC

/-! ## The web of atoms over a chain

The runs over a chain index the arrows, the atoms are the ascents, and the square and the hexagon
are the cells of the pair chain — so category-valued Matsumoto applies and a climb names one arrow
independently of the climb. -/

/-- **The atoms out of the runs over a chain, as an Artin web.** -/
noncomputable def runWeb (hz : dimSum (shOf z).dims = N) :
    ArtinWeb N (RunPerm N z) ((runAtomPoly K).presented) where
  toDescents := runDescents N z
  obj := subObj
  arr e := subArr (ascAtom e)
  comm a b a' b' hij hb hb' := subArr_ascAtom_comm hz a b a' b' hij (Fin.ext hb) (Fin.ext hb')
  braid a₁ a₂ a₃ b₁ b₂ b₃ hij h₂ h₃ h₂' h₃' :=
    subArr_ascAtom_braid hz a₁ a₂ a₃ b₁ b₂ b₃ hij (Fin.ext h₂) (Fin.ext h₃) (Fin.ext h₂')
      (Fin.ext h₃')

theorem ev_eq_climbArr (hz : dimSum (shOf z).dims = N) {a : RunPerm N z} :
    ∀ {b : RunPerm N z} (R : Climb (runDescents N z).perm a b),
      (runWeb hz).ev R = climbArr R
  | _, .nil => rfl
  | _, .cons R e => congrArg (fun t => t ≫ subArr (ascAtom e)) (ev_eq_climbArr hz R)

/-- **The arrow a climb over a chain spells** — Matsumoto, so it does not see which climb. -/
noncomputable def webArrow (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (h : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm b)) :
    subObj a ⟶ subObj b := (runWeb hz).arrow h

theorem climbArr_eq_arrow (hz : dimSum (shOf z).dims = N) {a b : RunPerm N z}
    (R : Climb (runDescents N z).perm a b) : climbArr R = webArrow hz R.le :=
  (ev_eq_climbArr hz R).symm.trans ((runWeb hz).ev_eq_arrow R)

theorem runArrow_refl (hz : dimSum (shOf z).dims = N) {a : RunPerm N z}
    (h : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm a)) :
    webArrow hz h = 𝟙 (subObj a) := (runWeb hz).arrow_refl h

theorem runArrow_comp (hz : dimSum (shOf z).dims = N) {a b c : RunPerm N z}
    (h₁ : WeakOrder.of ((runDescents N z).perm a) ≤ WeakOrder.of ((runDescents N z).perm b))
    (h₂ : WeakOrder.of ((runDescents N z).perm b) ≤ WeakOrder.of ((runDescents N z).perm c)) :
    webArrow hz h₁ ≫ webArrow hz h₂ = webArrow hz (h₁.trans h₂) := (runWeb hz).arrow_comp h₁ h₂


/-! ## The 0-cell and the run a word of bead cuts reaches

A letter restricts the element its source carries, so a word restricts along the refinement it
performs — and the run over the word's coarse end that the fine end's own merge names is the run the
word climbs to. -/

/-- The element a bead cut restricts. -/
theorem map_cutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (wedgeHoms K).map (Cut.genHom e.1).op a.2 = b.2 :=
  (congrArg (fun q => (wedgeHoms K).map q a.2) (zCutPresentation_arrow e.1)).symm.trans e.2

/-- **A bead cut is the cut of its own base map** — the lift carries no extra data. -/
theorem eq_cutGen {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    e = cutGen (Cut.genHom e.1) (Cut.codim_genHom e.1) (map_cutHom e) :=
  Subtype.ext (Subtype.ext rfl)

/-- **The element a word of bead cuts restricts.** -/
theorem map_ev {u : (chCutPoly K).V} : ∀ {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v),
    (wedgeHoms K).map (Cut.ev ((chProj K).mapPath w)).op u.2 = v.as.2
  | _, .nil => by rw [Prefunctor.mapPath_nil, Cut.ev_nil, op_id, Functor.map_id_apply]
  | _, .cons w e =>
      (congrArg ((wedgeHoms K).map (Cut.genHom e.1).op) (map_ev w)).trans (map_cutHom e)

theorem eltRestrict_ev {u : (chCutPoly K).V} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) :
    eltRestrict u (Cut.ev ((chProj K).mapPath w)) = v.as :=
  congrArg (fun s => (⟨shOf v.as, s⟩ : (chCutPoly K).V)) (map_ev w)

/-- A run-arrow read at itself is the run it names. -/
@[simp] theorem runOf_arr {M : ℕ} {c : (chCutPoly K).V} (σ : RunPerm M c) : runOf σ.arr = σ :=
  Subtype.ext σ.crossPerm_arr

theorem arr_runBot {M : ℕ} (c : (chCutPoly K).V) (hc : dimSum (shOf c).dims = M) :
    (runBot c hc).arr = runMerge (shOf c) hc := arr_runOf _

/-- The run a word of bead cuts reaches, read over its coarse end. -/
noncomputable def wordPerm {u : (chCutPoly K).V} {M : ℕ} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) (hv : dimSum (shOf v.as).dims = M) : RunPerm M u :=
  runOf (runMerge (shOf v.as) hv ≫ Cut.ev ((chProj K).mapPath w))

theorem eltRep_wordPerm {u : (chCutPoly K).V} {M : ℕ} {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt u) v) (hv : dimSum (shOf v.as).dims = M) :
    eltRep v.as = (runObj (wordPerm w hv)).1 :=
  (congrArg eltRep (eltRestrict_ev w)).symm.trans
    (eltRep_pairChain hv (Cut.ev ((chProj K).mapPath w)) (arr_runOf _).symm)

/-- **A run reached through a base performs the base's crossing permutation** — the merge onto the
base makes no crossing. -/
theorem val_eq_crossPerm {u : (chCutPoly K).V} {M : ℕ} {d : Ch Zbp} (t : d ⟶ shOf u)
    (hd : dimSum d.dims = M) {σ : RunPerm M u} (hσ : runMerge d hd ≫ t = σ.arr) :
    σ.1 = crossPerm hd t := by
  rw [← σ.crossPerm_arr, ← hσ, crossPerm_comp (dimSum_replicate M) (runMerge d hd) t,
    crossPerm_eq_one_of_W _ (W_runMerge d hd), mul_one]

/-- **A cut lengthens the run it reaches by its own crossings** — so the run below it is climbed
to. -/
theorem runPerm_le_of_cut {u : (chCutPoly K).V} {M : ℕ} {d b : Ch Zbp} (t : d ⟶ shOf u)
    (hd : dimSum d.dims = M) (hb : dimSum b.dims = M) (f : b ⟶ d) {σ₀ σ : RunPerm M u}
    (hσ₀ : runMerge d hd ≫ t = σ₀.arr) (hσ : runMerge b hb ≫ f ≫ t = σ.arr) :
    WeakOrder.of ((runDescents M u).perm σ₀) ≤ WeakOrder.of ((runDescents M u).perm σ) := by
  have h₀ := val_eq_crossPerm t hd hσ₀
  have h₁ := val_eq_crossPerm (f ≫ t) hb hσ
  rw [runDescents_perm, runDescents_perm]
  refine WeakOrder.le_of_mul_eq (π := crossPerm hb f) ?_ ?_
  · rw [h₁, crossPerm_comp hb f t, h₀]
  · rw [h₁, permLen_crossPerm_comp hb f t, h₀]

theorem climbArr_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hd : dimSum d.dims = M) {a b : RunPerm M (eltRestrict u t)}
    (R : Climb (runDescents M (eltRestrict u t)).perm a b) :
    climbArr (pushClimb t hd R)
      = eqToHom (subObj_pushPerm t a) ≫ climbArr R ≫ eqToHom (subObj_pushPerm t b).symm := by
  induction R with
  | nil =>
      change 𝟙 (subObj (pushPerm t a)) = eqToHom (subObj_pushPerm t a) ≫ 𝟙 (subObj a)
        ≫ eqToHom (subObj_pushPerm t a).symm
      simp
  | cons R e ih =>
      change climbArr (pushClimb t hd R) ≫ subArr (ascAtom (pushAscent t hd e))
        = eqToHom _ ≫ (climbArr R ≫ subArr (ascAtom e)) ≫ eqToHom _
      rw [ih, subArr_ascAtom_push t hd e (subObj_pushPerm t _) (subObj_pushPerm t _).symm]
      exact (eqToHom_sandwich_comp (subObj_pushPerm t a).symm _ _ _ _).symm

/-- **The web arrow over a chain is the one over anything it refines.** -/
theorem webArrow_push {u : (chCutPoly K).V} {d : Ch Zbp} (t : d ⟶ shOf u) {M : ℕ}
    (hu : dimSum (shOf u).dims = M) (hd : dimSum d.dims = M)
    {a b : RunPerm M (eltRestrict u t)}
    (h : WeakOrder.of ((runDescents M (eltRestrict u t)).perm a)
      ≤ WeakOrder.of ((runDescents M (eltRestrict u t)).perm b))
    (h' : WeakOrder.of ((runDescents M u).perm (pushPerm t a))
      ≤ WeakOrder.of ((runDescents M u).perm (pushPerm t b))) :
    webArrow hu h'
      = eqToHom (subObj_pushPerm t a) ≫ webArrow hd h ≫ eqToHom (subObj_pushPerm t b).symm := by
  obtain ⟨R⟩ := (runDescents M (eltRestrict u t)).nonempty_climb' h
  refine Eq.trans (climbArr_eq_arrow hu (pushClimb t hd R)).symm ?_
  exact (climbArr_push t hd R).trans (sandwich_congr _ _ (climbArr_eq_arrow hd R))

/-! ## A 1-cell is the web arrow to the run of its target

`subArr_eq_climbArr` reads a 1-cell whose cut does not start at a run as its own climb; a 1-cell
whose cut *does* start at a run cuts an atom's cell (`exists_atomComp`) and is the atom there
(`eq_atomOnes`), so its climb is the single ascent across that atom. -/

/-- **A 1-cell whose cut does not start at a run is the web arrow its climb spells.** -/
theorem subArr_eq_arrow {A B : (chContraction K).V} (g : (chContraction K).Gen A B) {M : ℕ}
    (hM : dimSum (shOf g.dom).dims = M) (hg : ¬ RunCut g)
    (p : subPt A = subObj (runBot g.dom hM)) (q : subObj (genTopAt g hM) = subPt B) :
    subArr g = eqToHom p ≫ webArrow hM (runBot_le hM (genTopAt g hM)) ≫ eqToHom q := by
  subst hM
  exact (subArr_eq_climbArr g hg).trans
    (sandwich_congr _ _ (climbArr_eq_arrow rfl (genClimb g)))

/-! ## A bead cut over a base, read at the runs of its two ends -/

/-- Collapsing two renamings onto one, on either side of an arrow. -/
private theorem sandwich_eq {C : Type*} [Category C] {A₀ A A' B' B B₀ : C} (p : A₀ = A)
    (p' : A = A') (q' : B' = B) (q : B = B₀) (r : A₀ = A') (s : B' = B₀) (f : A' ⟶ B') :
    eqToHom p ≫ (eqToHom p' ≫ f ≫ eqToHom q') ≫ eqToHom q = eqToHom r ≫ f ≫ eqToHom s := by
  subst p'; subst q'; subst p; subst q; simp

/-- The 1-cell of the contraction a non-merge bead cut over a base becomes. -/
noncomputable def cutCell {u : (chCutPoly K).V} {d b : Ch Zbp} (t : d ⟶ shOf u) {f : b ⟶ d}
    (hf : codim f = 1) (hnW : ¬ W Zbp f) :
    (chContraction K).Gen ⟨eltRep (eltRestrict u t), eltRep_idem _⟩
      ⟨eltRep (eltRestrict u (f ≫ t)), eltRep_idem _⟩ :=
  (chContraction K).genCell (Polygraph.fwdCell (chCutPoly K) (chCutPicked K)
      (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl))
    (fun hm => hnW ((merge_iff f).mp hm).1)

theorem cutArr_cutCell {u : (chCutPoly K).V} {d b : Ch Zbp} (t : d ⟶ shOf u) {f : b ⟶ d}
    (hf : codim f = 1) (hnW : ¬ W Zbp f) :
    cutArr (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl)
      = subArr (cutCell t hf hnW) :=
  cutArr_gen (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl)
    (fun hm => hnW ((merge_iff f).mp hm).1)

/-- **A bead cut over a base, read at the runs of its two ends, is the web arrow between them** — a
merge names a renaming, an atom out of a run names itself, and any other cut its own climb pushed
onto the base. -/
theorem atRun_cutRestrict {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {d : Ch Zbp} (t : d ⟶ shOf u) (hd : dimSum d.dims = M)
    {b : Ch Zbp} (hb : dimSum b.dims = M) {f : b ⟶ d} (hf : codim f = 1)
    {σ₀ σ : RunPerm M u} (hσ₀ : runMerge d hd ≫ t = σ₀.arr)
    (hσ : runMerge b hb ≫ f ≫ t = σ.arr)
    (hA : eltRep (eltRestrict u t) = (runObj σ₀).1)
    (hB : eltRep (eltRestrict u (f ≫ t)) = (runObj σ).1)
    (hle : WeakOrder.of ((runDescents M u).perm σ₀)
      ≤ WeakOrder.of ((runDescents M u).perm σ)) :
    atRun hA hB (cutArr (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl))
      = webArrow hu hle := by
  by_cases hW : W Zbp f
  · -- a merge: the two runs agree, and the cut names a renaming
    have hpick : chCutPicked K
        (cutGen (c := eltRestrict u t) (c' := eltRestrict u (f ≫ t)) f hf rfl) :=
      (merge_iff f).mpr ⟨hW, hf⟩
    have harr : σ₀.arr = σ.arr :=
      hσ₀.symm.trans ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
        (eq_of_W ((W Zbp).comp_mem _ _ (W_runMerge b hb) hW) (W_runMerge d hd))).symm.trans hσ)
    obtain rfl : σ₀ = σ := Subtype.ext (σ₀.crossPerm_arr.symm.trans
      ((congrArg (crossPerm (dimSum_replicate M)) harr).trans σ.crossPerm_arr))
    rw [cutArr_merge _ hpick ((subPt_eq hA).trans (subPt_eq hB).symm),
      atRun_eqToHom hA hB _ (rfl : runObj σ₀ = runObj σ₀), runArrow_refl hu hle]
    exact eqToHom_refl _ _
  · by_cases hg : eltRep (eltRestrict u (f ≫ t)) = eltRestrict u (f ≫ t)
    · -- the cut starts at a run: it is the atom at the cell its source names
      obtain rfl : b = zObj (𝟙^M) := shOf_eq_ones_of_eltRep hg hb
      obtain ⟨k, rfl⟩ := exists_atomComp f hf
      obtain rfl : f = atomOnes M k := eq_atomOnes hW
      have hval₀ := val_eq_crossPerm t hd hσ₀
      have hcomp := val_eq_crossPerm (atomOnes M k ≫ t) hb hσ
      have hval : σ.1 = σ₀.1 * adjT k := by
        rw [hcomp, crossPerm_comp hb (atomOnes M k) t, crossPerm_atomOnes, hval₀]
      have hlen : permLen (σ₀.1 * adjT k) = permLen σ₀.1 + 1 := by
        rw [← hval, hcomp, permLen_crossPerm_comp hb (atomOnes M k) t,
          crossPerm_atomOnes, permLen_adjT, hval₀]
        omega
      have hleg : ascLeg (⟨k, ascent_of_permLen_succ hlen, hval⟩ :
          Ascent (runDescents M u).perm σ₀ σ) = t :=
        hom_ext_of_crossPerm (h := dimSum_atomComp M k) (by
          rw [crossPerm_ascLeg]; exact hval₀)
      have hsand := subArr_ascAtom_eq_legAtom
        (⟨k, ascent_of_permLen_succ hlen, hval⟩ : Ascent (runDescents M u).perm σ₀ σ) hleg
        (X := runObj σ₀) (Y := runObj σ) hA ((eltRep_eq_self rfl).symm.trans hB) rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsand
      refine Eq.trans (atRun_topCut t hA hB) ?_
      refine Eq.trans hsand.symm ?_
      exact (Category.id_comp _).symm.trans (climbArr_eq_arrow hu (Climb.nil.cons
        (⟨k, ascent_of_permLen_succ hlen, hval⟩ : Ascent (runDescents M u).perm σ₀ σ)))
    · -- any other cut: its own climb over its source, pushed onto the base
      have h₀ : pushPerm t (runBot (eltRestrict u t) hd) = σ₀ :=
        (congrArg runOf ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
          (arr_runBot (eltRestrict u t) hd)).trans hσ₀)).trans (runOf_arr σ₀)
      have h₁ : pushPerm t (genTopAt (cutCell t hf hW) hd) = σ :=
        (congrArg runOf ((congrArg (fun s : zObj (𝟙^M) ⟶ d => s ≫ t)
          (arr_genTopAt (cutCell t hf hW) hd)).trans hσ)).trans (runOf_arr σ)
      subst h₀
      subst h₁
      refine Eq.trans (congrArg (atRun hA hB) ((cutArr_cutCell t hf hW).trans
        (subArr_eq_arrow (cutCell t hf hW) hd hg
          (subObj_runBot_gen (cutCell t hf hW) hd) (subObj_genTopAt (cutCell t hf hW) hd)))) ?_
      refine Eq.trans ?_ (webArrow_push t hu hd
        (runBot_le (z := eltRestrict u t) hd (genTopAt (cutCell t hf hW) hd)) hle).symm
      exact sandwich_eq _ _ _ _ _ _ _

/-- …and at any naming of the element its source carries. -/
theorem atRun_cutGen {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {d : Ch Zbp} (t : d ⟶ shOf u) (hd : dimSum d.dims = M)
    {x : (wedgeHoms K).obj (op d)} (hx : (wedgeHoms K).map t.op u.2 = x)
    {b : Ch Zbp} (hb : dimSum b.dims = M) {f : b ⟶ d} (hf : codim f = 1)
    {y : (wedgeHoms K).obj (op b)} (hy : (wedgeHoms K).map f.op x = y)
    {σ₀ σ : RunPerm M u} (hσ₀ : runMerge d hd ≫ t = σ₀.arr)
    (hσ : runMerge b hb ≫ f ≫ t = σ.arr)
    (hA : eltRep (⟨d, x⟩ : (chCutPoly K).V) = (runObj σ₀).1)
    (hB : eltRep (⟨b, y⟩ : (chCutPoly K).V) = (runObj σ).1)
    (hle : WeakOrder.of ((runDescents M u).perm σ₀)
      ≤ WeakOrder.of ((runDescents M u).perm σ)) :
    atRun hA hB (cutArr (cutGen f hf hy)) = webArrow hu hle := by
  subst hx
  subst hy
  exact atRun_cutRestrict hu t hd hb hf hσ₀ hσ hA hB hle

/-! ## The word a refinement spells, independent of the word

`atRun_cutGen` makes each letter a web arrow, so a word is the web arrow to the run its refinement
reaches — and that run sees only the refinement. -/

theorem cutSubF_cons {a m v : GenObj (chCutPoly K).Gen} (w : Quiver.Path a m) (e : m ⟶ v) :
    (cutSubF K).map (w.cons e) = (cutSubF K).map w ≫ cutArr e :=
  (cutSubF K).map_comp w e.toPath

/-- **A word of bead cuts is the web arrow to the run its refinement reaches.** -/
theorem atRun_cutSubF {u : (chCutPoly K).V} {M : ℕ} (hu : dimSum (shOf u).dims = M)
    {v : GenObj (chCutPoly K).Gen} (w : Quiver.Path ((chCutPoly K).pt u) v) :
    ∀ (hv : dimSum (shOf v.as).dims = M) {σ : RunPerm M u}
      (_hσ : runMerge (shOf v.as) hv ≫ Cut.ev ((chProj K).mapPath w) = σ.arr)
      (hA : eltRep u = (runObj (runBot u hu)).1) (hB : eltRep v.as = (runObj σ).1),
      atRun hA hB ((cutSubF K).map w) = webArrow hu (runBot_le hu σ) := by
  induction w with
  | nil =>
      intro hv σ hσ hA hB
      have hWσ : W Zbp σ.arr := by
        rw [← hσ]
        exact (W Zbp).comp_mem _ _ (W_runMerge (shOf u) hv) (MorphismProperty.id_mem _ _)
      obtain rfl : σ = runBot u hu := Subtype.ext (σ.crossPerm_arr.symm.trans
        ((crossPerm_eq_one_of_W _ hWσ).trans (runBot_val u hu).symm))
      rw [runArrow_refl hu (runBot_le hu (runBot u hu)),
        show (cutSubF K).map (Quiver.Path.nil :
            Quiver.Path ((chCutPoly K).pt u) ((chCutPoly K).pt u)) = 𝟙 _ from
          (cutSubF K).map_id _]
      exact (atRun_eqToHom hA hB rfl rfl).trans (eqToHom_refl _ _)
  | @cons m v w e ih =>
      intro hv σ hσ hA hB
      have hm : dimSum (shOf m.as).dims = M :=
        (dimSum_eq_of_hom (Cut.genHom e.1)).symm.trans hv
      have hσ₀ : runMerge (shOf m.as) hm ≫ Cut.ev ((chProj K).mapPath w)
          = (wordPerm w hm).arr := (arr_runOf _).symm
      have hstep := runPerm_le_of_cut (Cut.ev ((chProj K).mapPath w)) hm hv
        (Cut.genHom e.1) hσ₀ hσ
      rw [cutSubF_cons w e, atRun_comp hA (eltRep_wordPerm w hm) hB,
        ih hm hσ₀ hA (eltRep_wordPerm w hm),
        show atRun (eltRep_wordPerm w hm) hB (cutArr e) = webArrow hu hstep from
          Eq.trans (congrArg (atRun (eltRep_wordPerm w hm) hB) (congrArg cutArr (eq_cutGen e)))
            (atRun_cutGen hu (Cut.ev ((chProj K).mapPath w)) hm (map_ev w) hv
              (Cut.codim_genHom e.1) (map_cutHom e) hσ₀ hσ (eltRep_wordPerm w hm) hB hstep)]
      exact runArrow_comp hu (runBot_le hu (wordPerm w hm)) hstep

/-- Cancelling a renaming against its inverse, on either side of an arrow. -/
private theorem sandwich_cancel {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    (f : A ⟶ B) : eqToHom p ≫ (eqToHom p.symm ≫ f ≫ eqToHom q) ≫ eqToHom q.symm = f := by
  subst p; subst q; simp

theorem atRun_injective {A B : (chContraction K).V} {z₁ z₂ : (chCutPoly K).V}
    (hA : eltRep z₁ = A.1) (hB : eltRep z₂ = B.1)
    {f f' : (cutSubF K).obj ((chCutPoly K).pt z₁) ⟶ (cutSubF K).obj ((chCutPoly K).pt z₂)}
    (h : atRun hA hB f = atRun hA hB f') : f = f' :=
  (sandwich_cancel (subPt_eq hA) (subPt_eq hB) f).symm.trans
    ((congrArg (fun s => eqToHom (subPt_eq hA) ≫ s ≫ eqToHom (subPt_eq hB).symm) h).trans
      (sandwich_cancel (subPt_eq hA) (subPt_eq hB) f'))

/-- **Two words of bead cuts with the same value read alike** — they climb to one run, and
Matsumoto does not see which climb. -/
theorem cutSubF_congr {u : (chCutPoly K).V} {v : GenObj (chCutPoly K).Gen}
    {w w' : Quiver.Path ((chCutPoly K).pt u) v}
    (h : Cut.ev ((chProj K).mapPath w) = Cut.ev ((chProj K).mapPath w')) :
    (cutSubF K).map w = (cutSubF K).map w' := by
  have hu : dimSum (shOf u).dims = dimSum (shOf u).dims := rfl
  have hv : dimSum (shOf v.as).dims = dimSum (shOf u).dims :=
    dimSum_eq_of_hom (Cut.ev ((chProj K).mapPath w))
  refine atRun_injective ((runObj_runBot u hu).symm) (eltRep_wordPerm w hv) ?_
  refine Eq.trans (atRun_cutSubF hu w hv (arr_runOf _).symm _ (eltRep_wordPerm w hv)) ?_
  exact (atRun_cutSubF hu w' hv (by rw [← h]; exact (arr_runOf _).symm) _
    (eltRep_wordPerm w hv)).symm

/-! ## The degree-zero presentation -/

theorem all_merged_fwd {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b)
    (he : chCutPicked K e) :
    Quiver.Path.All (fun ⦃_ _⦄ g => Cut.merged g)
      (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath :=
  Quiver.Path.all_toPath.mpr he

theorem all_merged_bwd {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b)
    (he : chCutPicked K e) :
    Quiver.Path.All (fun ⦃_ _⦄ g => Cut.merged g)
      (Polygraph.bwdCell (chCutPoly K) (chCutPicked K) e he).toPath :=
  Quiver.Path.all_toPath.mpr trivial

/-- **Every 2-cell of the localized cut polygraph holds in the sub-polygraph** — a cancellation is
two merges, and a kept cell is two words with one value. -/
theorem runSubF_invRel {U V : GenObj (Polygraph.InvGen (chCutPoly K) (chCutPicked K))}
    (β : Polygraph.InvRel (chCutPoly K) (chCutPicked K) U V) :
    (runSubF K).map ((chContraction K).words.map ((cutLocPoly K).src β))
      = (runSubF K).map ((chContraction K).words.map ((cutLocPoly K).tgt β)) := by
  cases β with
  | keep α =>
      exact cutSubF_congr ((congrArg Cut.ev α.src_eq).trans
        (α.cell.ev_eq.trans (congrArg Cut.ev α.tgt_eq).symm))
  | cancel e he =>
      exact ((chContraction K).map_words_of_all_S (runSubF K)
          ((Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath.comp
            (Polygraph.bwdCell (chCutPoly K) (chCutPicked K) e he).toPath)
          ((all_merged_fwd e he).comp (all_merged_bwd e he)) rfl).trans
        ((chContraction K).map_words_of_all_S (runSubF K) Quiver.Path.nil
          (Quiver.Path.all_nil _) rfl).symm
  | cancel' e he =>
      exact ((chContraction K).map_words_of_all_S (runSubF K)
          ((Polygraph.bwdCell (chCutPoly K) (chCutPicked K) e he).toPath.comp
            (Polygraph.fwdCell (chCutPoly K) (chCutPicked K) e).toPath)
          ((all_merged_bwd e he).comp (all_merged_fwd e he)) rfl).trans
        ((chContraction K).map_words_of_all_S (runSubF K) Quiver.Path.nil
          (Quiver.Path.all_nil _) rfl).symm

/-- **…and so does every 2-cell of the contraction** — the conjugation only renames its ends. -/
theorem chCell_derivable {x y : GenObj (chContraction K).poly.Gen}
    (α : (chContraction K).poly.Rel x y) :
    (runSubF K).map ((chContraction K).poly.src α)
      = (runSubF K).map ((chContraction K).poly.tgt α) :=
  (Paths.map_cellCongr₂ (runSubF K) _ _ _).trans
    ((sandwich_congr _ _ (runSubF_invRel α.cell)).trans
      (Paths.map_cellCongr₂ (runSubF K) _ _ _).symm)

/-- **The atoms out of the runs with the codimension-two cuts out of a run span the contraction**,
for every `K` and with no hypothesis on `K`. -/
noncomputable def chRunCutSpans (K : BPSet) :
    Spans (chContraction K).poly RunCut RunCutCell where
  word := runCellWord
  word_all := all_runCellWord
  word_eq := quot_runCellWord
  word_self := runCellWord_self
  cell_derivable α := chCell_derivable α

/-- **`Ch(K)[W⁻¹]` presented by the atoms out of the runs, with the codimension-two cuts out of a
run as the only relations** — for every `K` and with no hypothesis on `K`. -/
noncomputable def chCellPresentation (K : BPSet) :
    Presents (chRunCutSpans K).poly (((W K).op).Localization) :=
  (chRunPresentation K).restrictCells (chRunCutSpans K)

end ChainCat
