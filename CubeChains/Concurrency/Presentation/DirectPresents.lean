import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.LocFunctor

/-!
# Concurrency/Presentation/DirectPresents — the paper's cells, read straight in the localization

`Rconj u` is the refinement `u` conjugated by the two merges the localization inverts, built out of
`Q` alone with no model of `Ch(K)[W⁻¹]` in between:

    run(c) ──bottomHom──▸ c ──u──▸ d ◂──bottomHom── run(d)

The geometric input is `lift_cutWord`: the word a codimension-one cut spells reads as its conjugate.
Then `paperE` interprets the cells, `Theta` reads the chains back on them, and the two are inverse —
so `Theta` is a localization functor and `paperE` the presentation.

`Q ⋙ chLocOpMap f = (pushforward f).op ⋙ Q` is an *equality*, so this reading is natural in `K` on
the nose, where a reading through a model of the localization is natural only up to isomorphism.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-- The localization functor. -/
noncomputable abbrev Lc (K : BPSet) : (Ch K)ᵒᵖ ⥤ ((W K).op).Localization := ((W K).op).Q

/-- The object a chain names. -/
noncomputable abbrev rho (c : Ch K) : ((W K).op).Localization := (Lc K).obj (op c)

/-- The arrow a refinement names. -/
noncomputable def arr {c d : Ch K} (u : c ⟶ d) : rho d ⟶ rho c := (Lc K).map u.op

theorem arr_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) : arr (v ≫ u) = arr u ≫ arr v :=
  (Lc K).map_comp u.op v.op

@[simp] theorem arr_id (c : Ch K) : arr (𝟙 c) = 𝟙 (rho c) := (Lc K).map_id _

theorem arr_eqToHom {c d : Ch K} (h : c = d) :
    arr (eqToHom h) = eqToHom (congrArg rho h).symm := by
  subst h; simp [arr]

noncomputable instance isIso_arr {c d : Ch K} (u : c ⟶ d) (hu : W K u) : IsIso (arr u) :=
  Localization.inverts (Lc K) ((W K).op) u.op hu

/-- The isomorphism a merge names. -/
noncomputable def mergeIso {c d : Ch K} {m : c ⟶ d} (hm : W K m) : rho d ≅ rho c :=
  @asIso _ _ _ _ (arr m) (isIso_arr m hm)

@[simp] theorem mergeIso_hom {c d : Ch K} {m : c ⟶ d} (hm : W K m) :
    (mergeIso hm).hom = arr m := rfl

/-- **The arrow a refinement names between the runs of its two ends.** -/
noncomputable def Rconj {c d : Ch K} (u : c ⟶ d) :
    rho (bottomRun d).chain ⟶ rho (bottomRun c).chain :=
  (mergeIso (W_bottomHom d)).inv ≫ arr u ≫ arr (bottomHom c)

theorem Rconj_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) :
    Rconj (v ≫ u) = Rconj u ≫ Rconj v := by
  rw [Rconj, Rconj, Rconj, arr_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (arr (bottomHom c)) _ _, ← mergeIso_hom (W_bottomHom c),
    Iso.hom_inv_id, Category.id_comp]

theorem Rconj_of_W {c d : Ch K} (u : c ⟶ d) (hu : W K u) :
    Rconj u = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_of_W u hu)) := by
  set h := bottomRun_eq_of_W u hu with hh
  have key : eqToHom (congrArg Run.chain h) ≫ (bottomHom c ≫ u) = bottomHom d :=
    eq_of_W ((W K).comp_mem _ _ (W_eqToHom _) ((W K).comp_mem _ _ (W_bottomHom c) hu))
      (W_bottomHom d)
  have harr : arr (bottomHom d)
      = (arr u ≫ arr (bottomHom c)) ≫ eqToHom (congrArg rho (congrArg Run.chain h)).symm := by
    rw [← key, arr_comp, arr_comp, arr_eqToHom]
  rw [Rconj, Iso.inv_comp_eq, mergeIso_hom, harr]
  simp

/-- **The merge below the target carries the conjugate to the refinement.** -/
theorem arr_bottomHom_comp_Rconj {c d : Ch K} (u : c ⟶ d) :
    arr (bottomHom d) ≫ Rconj u = arr u ≫ arr (bottomHom c) := by
  rw [Rconj, ← Category.assoc, ← mergeIso_hom (W_bottomHom d), Iso.hom_inv_id, Category.id_comp]

/-- **…and pins it.** -/
theorem Rconj_eq_of {c d : Ch K} (u : c ⟶ d)
    {t : rho (bottomRun d).chain ⟶ rho (bottomRun c).chain}
    (h : arr (bottomHom d) ≫ t = arr u ≫ arr (bottomHom c)) : t = Rconj u := by
  rw [Rconj, Iso.eq_inv_comp, mergeIso_hom]; exact h

private theorem eqToHom_move {C : Type*} [Category C] {A A' B B' : C} (p : A = A') (q : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : eqToHom p.symm ≫ f ≫ eqToHom q = g) :
    f = eqToHom p ≫ g ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h

/-- **Two merges into one chain name one arrow**, up to the renaming of their sources. -/
theorem arr_eq_of_W {a r r' : Ch K} {m : r ⟶ a} {m' : r' ⟶ a} (hm : W K m) (hm' : W K m')
    (h : r = r') : arr m = arr m' ≫ eqToHom (congrArg rho h).symm := by
  subst h
  rw [eq_of_W hm hm']
  simp

/-! ## The interpretation -/

/-- The arrow a cell names. -/
noncomputable def cellRconj {n : ℕ} {X Y : Run K} (α : Cell n X Y) : rho X.chain ⟶ rho Y.chain :=
  eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj α.hom
    ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y))

/-- **The interpretation of the paper's cells** in the localization. -/
noncomputable def paperPre' : GenObj (Gen (K := K)) ⥤q ((W K).op).Localization where
  obj X := rho X.as.chain
  map α := cellRconj α

/-! ## Essential surjectivity -/

theorem essSurj_paperPre' : (Paths.lift (paperPre' (K := K))).EssSurj where
  mem_essImage c :=
    ⟨runPt (bottomRun ((Lc K).objPreimage c).unop),
      ⟨(mergeIso (W_bottomHom ((Lc K).objPreimage c).unop)).symm
        ≪≫ (Lc K).objObjPreimageIso c⟩⟩

/-! ## A cut, read in the localization

`runPre` reads a kept cut as the degree-one object it lands on, so a kept cut reads as its own
conjugate.  That, and the telescoping of a climb below, is the whole geometric input: every other
reading of a word of cuts is this one, read through `(poly K).quot`. -/

/-- A renaming on either side of an arrow that is itself one. -/
private theorem eqToHom_sandwich {C : Type*} [Category C] {A B D E : C} (h₁ : A = B)
    {f : B ⟶ D} {h : B = D} (hf : f = eqToHom h) (h₂ : D = E) (hAE : A = E) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom hAE := by
  subst hf; rw [eqToHom_trans, eqToHom_trans]

/-- Renaming both sides of an arrow does not see which arrow it is. -/
private theorem sandwich_congr {C : Type*} [Category C] {A B D E : C} (h₁ : A = B) (h₂ : D = E)
    {f g : B ⟶ D} (h : f = g) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = eqToHom h₁ ≫ g ≫ eqToHom h₂ := by rw [h]

/-- Three nested renamings are one. -/
private theorem nest3 {C : Type*} [Category C] {A₀ A₁ A₂ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) {f : A₂ ⟶ B₂} (b₁ : B₂ = B₁) (b₀ : B₁ = B₀)
    (p : A₀ = A₂) (q : B₂ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ f ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ f ≫ eqToHom q := by
  subst a₀; subst a₁; subst b₁; subst b₀; simp

/-- …and four. -/
private theorem nest4 {C : Type*} [Category C] {A₀ A₁ A₂ B₃ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) {f : A₂ ⟶ B₃} (b₂ : B₃ = B₂) (b₁ : B₂ = B₁) (b₀ : B₁ = B₀)
    (p : A₀ = A₂) (q : B₃ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ (f ≫ eqToHom b₂) ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ f ≫ eqToHom q := by
  subst a₀; subst a₁; subst b₂; subst b₁; subst b₀; simp

/-- **A cell's arrow, at other names for its two runs.** -/
theorem cellRconj_cellCongr {n : ℕ} {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (β : Cell n X Y) :
    cellRconj (cellCongr (Cell n) hx hy β)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) hx).symm ≫ cellRconj β
        ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) hy) := by
  subst hx; subst hy
  rw [cellCongr_self]
  simp

/-- **A 1-cell's arrow is any crossing refinement out of its far end, conjugated.** -/
theorem cellRconj_of_hom {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    cellRconj α = eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj f
      ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y)) := by
  rw [cellRconj, Cell.hom_eq α hf]

/-! ## A climb, read in the localization

The two legs out of an ascent's atom are a merge and the atom's own cut, and both land on the chain,
so `Rconj`'s contravariance telescopes a climb into one conjugated refinement. -/

/-- The arrow a run over a chain names, out of the chain's own run. -/
noncomputable def runAt {e : Ch K} (σ : ChPerm e) :
    rho (shapeRun e (shapeBot (zObj e.dims) rfl)).chain ⟶ rho (shapeRun e σ).chain :=
  eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_shapeRun e)).symm
    ≫ Rconj (shapeHom e σ)
    ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self (shapeRun e σ)))

theorem runAt_bot (e : Ch K) :
    runAt (shapeBot (zObj e.dims) rfl)
      = 𝟙 (rho (shapeRun e (shapeBot (zObj e.dims) rfl)).chain) :=
  (eqToHom_sandwich _ (Rconj_of_W _ (W_shapeHom_shapeBot e)) _ rfl).trans (eqToHom_refl _ _)

/-- **One atom appends to the conjugated refinement below it** — the ascent's two legs are a merge
and the atom's own cut, and both land on the chain. -/
theorem runAt_cons {e : Ch K} {a b : ChPerm e} (ε : ChAsc e a b) :
    runAt b = runAt a ≫ cellRconj (ascGen e ε) := by
  rw [runAt, runAt, cellRconj_of_hom (ascGen e ε) (f := ascTop e ε) (not_W_ascTop e ε),
    ← ascTop_comp e ε, ← ascBot_comp e ε, Rconj_comp, Rconj_comp,
    Rconj_of_W (ascBot e ε) (W_ascBot e ε)]
  simp

/-- **A climb is the refinement it performs**, conjugated onto the chain's own run. -/
theorem lift_climbWord (e : Ch K) : ∀ {σ : ChPerm e}
    (R : Climb (shapeDescents (dimSum e.dims) (zObj e.dims)).perm
      (shapeBot (zObj e.dims) rfl) σ),
      (Paths.lift (paperPre' (K := K))).map ((ascPre e).mapPath R) = runAt σ
  | _, .nil => ((Paths.lift (paperPre' (K := K))).map_id _).trans (runAt_bot e).symm
  | _, .cons R ε =>
      ((Paths.lift_map_comp (paperPre' (K := K)) ((ascPre e).mapPath R)
            (Quiver.Hom.toPath (V := GenObj (Gen (K := K))) (ascGen e ε))).trans
        ((congrArg (fun t => t ≫ (Paths.lift (paperPre' (K := K))).map
              (Quiver.Hom.toPath (V := GenObj (Gen (K := K))) (ascGen e ε)))
            (lift_climbWord e R)).trans
          (congrArg (fun t => runAt _ ≫ t)
            (Paths.lift_toPath (paperPre' (K := K)) (ascGen e ε))))).trans
      (runAt_cons ε).symm

/-! ## The word a cut reads is its conjugate -/

/-- A renaming that renames nothing. -/
private theorem sandwich_refl {C : Type*} [Category C] {A B : C} (p : A = A) (q : B = B)
    (f : A ⟶ B) : eqToHom p ≫ f ≫ eqToHom q = f := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A renaming cancelled against its inverse. -/
private theorem cancel_eqToHom {C : Type*} [Category C] {A A' B : C} (p : A = A') (f : A ⟶ B) :
    eqToHom p ≫ eqToHom p.symm ≫ f = f := by subst p; simp

/-- An arrow inverse to a renaming is the renaming back. -/
private theorem eq_eqToHom_symm {C : Type*} [Category C] {A B : C} (p : A = B) {f : B ⟶ A}
    (h : eqToHom p ≫ f = 𝟙 A) : f = eqToHom p.symm := by subst p; simpa using h

/-- Four nested renamings are one. -/
private theorem collapse4 {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₄ B₃ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) (a₂ : A₂ = A₃) (a₃ : A₃ = A₄) {f : A₄ ⟶ B₄}
    (b₃ : B₄ = B₃) (b₂ : B₃ = B₂) (b₁ : B₂ = B₁) (b₀ : B₁ = B₀)
    (p : A₀ = A₄) (q : B₄ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ (eqToHom a₂ ≫ (eqToHom a₃ ≫ f ≫ eqToHom b₃)
        ≫ eqToHom b₂) ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ f ≫ eqToHom q := by
  subst a₀; subst a₁; subst a₂; subst a₃; subst b₃; subst b₂; subst b₁; subst b₀; simp

/-- **The word a codimension-one refinement reads is its conjugate** — the empty word at a merge,
its own letter at a cut that starts at a run, and the climb its conjugate spells otherwise. -/
theorem lift_cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    (Paths.lift (paperPre' (K := K))).map (cutWord u hu) = Rconj u := by
  by_cases hW : W K u
  · have hc : cutWord u hu = readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil := dif_pos hW
    rw [hc, Rconj_of_W u hW, readAt]
    refine Eq.trans (Paths.map_cellCongr₂ (Paths.lift (paperPre' (K := K))) _ _ _) ?_
    exact eqToHom_sandwich _ (((Paths.lift (paperPre' (K := K))).map_id _).trans
      (eqToHom_refl _ rfl).symm) _ _
  · by_cases hc : IsRun K c
    · rw [cutWord_of_run (degree_eq_one_of_isRun hc hu) (X := ⟨c, hc⟩) hu hW, readAt]
      refine Eq.trans (Paths.map_cellCongr₂ (Paths.lift (paperPre' (K := K))) _ _ _) ?_
      refine Eq.trans (sandwich_congr _ _ (Paths.lift_toPath (paperPre' (K := K)) _)) ?_
      refine Eq.trans (sandwich_congr _ _
        (cellRconj_of_hom (genOfHom (degree_eq_one_of_isRun hc hu) (X := ⟨c, hc⟩) hW)
          (f := u) hW)) ?_
      refine Eq.trans (nest3 _ _ _ _ rfl rfl) ?_
      exact sandwich_refl _ _ _
    · rw [cutWord_eq_climbWord hu hW hc, readAt]
      refine Eq.trans (Paths.map_cellCongr₂ (Paths.lift (paperPre' (K := K))) _ _ _) ?_
      refine Eq.trans (sandwich_congr _ _ (lift_climbWord d (cutClimb u))) ?_
      rw [runAt, ← cutTopHom_comp u, Rconj_comp, Rconj_of_W (cutTopHom u) (W_cutTopHom u)]
      refine Eq.trans (nest4 _ _ _ _ _ rfl rfl) ?_
      exact sandwich_refl _ _ _

/-! ## Soundness -/

/-- **A factorisation's word names the refinement**, whichever factorisation it is. -/
theorem lift_factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2) (ε : Bool) :
    (Paths.lift (paperPre' (K := K))).map (factorWords f hf ε)
      = Rconj f ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self X)) := by
  set F := (oneCutEquivBool f hf).symm ε with hF
  change (Paths.lift (paperPre' (K := K))).map
      (readAt rfl (bottomRun_self X)
        ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))) = _
  rw [readAt, Paths.map_cellCongr, Paths.lift_map_comp, lift_cutWord, lift_cutWord]
  exact congrArg (fun t => t ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain)
      (bottomRun_self X)))
    ((Rconj_comp F.1.fst F.1.snd).symm.trans (congrArg (fun u : X.chain ⟶ b => Rconj u) F.1.comp))

/-- **The paper's 2-cells are sound** — both sides name the object's own greatest refinement. -/
theorem sound_paperPre {x y : GenObj (Gen (K := K))} (α : (poly K).Rel x y) :
    (Paths.lift (paperPre' (K := K))).map ((poly K).src α)
      = (Paths.lift (paperPre' (K := K))).map ((poly K).tgt α) := by
  change (Paths.lift (paperPre' (K := K))).map (cellWords α false)
    = (Paths.lift (paperPre' (K := K))).map (cellWords α true)
  rw [cellWords, cellWords, readAt, readAt, Paths.map_cellCongr₂, Paths.map_cellCongr₂,
    lift_factorWords, lift_factorWords]

/-- **The paper's polygraph, interpreted in `Ch(K)[W⁻¹]`** — the comparison itself, with no model
of the localization in between. -/
noncomputable def paperE (K : BPSet) : (poly K).presented ⥤ ((W K).op).Localization :=
  Polygraph.desc (paperPre' (K := K)) sound_paperPre

theorem paperE_quot {x y : GenObj (Gen (K := K))} (w : Quiver.Path x y) :
    (paperE K).map ((poly K).quot.map w) = (Paths.lift (paperPre' (K := K))).map w := rfl

/-! ## A refinement, read on the paper's cells

`readCut_congr` says a word of bead cuts is pinned by the refinement it performs, so every
refinement names one arrow, contravariantly. -/

/-- The object a chain names on the paper's cells. -/
noncomputable abbrev subPt' (c : Ch K) : (poly K).presented :=
  (readCut K).obj ((chCutPoly K).pt (chV c))

/-- **The arrow a refinement names there.** -/
noncomputable def cutArrow {c d : Ch K} (f : c ⟶ d) : subPt' d ⟶ subPt' c :=
  (readCut K).map (chPath (a := chV c) (b := chV d) f)

theorem cutArrow_comp {c d e : Ch K} (f : c ⟶ d) (g : d ⟶ e) :
    cutArrow (f ≫ g) = cutArrow g ≫ cutArrow f := by
  have h1 : cutArrow (f ≫ g) = (readCut K).map
      ((chPath (a := chV d) (b := chV e) g).comp (chPath (a := chV c) (b := chV d) f)) := by
    refine readCut_congr ?_
    rw [ev_chPath, Prefunctor.mapPath_comp, Cut.ev_comp, ev_chPath, ev_chPath]
    rfl
  rw [h1]
  exact (readCut K).map_comp _ _

theorem cutArrow_id (c : Ch K) : cutArrow (𝟙 c) = 𝟙 (subPt' c) := by
  have h1 : cutArrow (𝟙 c) = (readCut K).map
      (Quiver.Path.nil : Quiver.Path ((chCutPoly K).pt (chV c)) ((chCutPoly K).pt (chV c))) := by
    refine readCut_congr ?_
    rw [ev_chPath, Prefunctor.mapPath_nil, Cut.ev_nil]
    rfl
  rw [h1]
  exact (readCut K).map_id _

/-- **The paper's polygraph, receiving the chains**, contravariantly: a chain names the run below it
and a refinement the word its cuts spell. -/
noncomputable def Theta (K : BPSet) : (Ch K)ᵒᵖ ⥤ (poly K).presented where
  obj c := subPt' c.unop
  map u := cutArrow u.unop
  map_id c := cutArrow_id c.unop
  map_comp u v := cutArrow_comp v.unop u.unop

/-! ## …read in the localization

The reading on the paper's cells, interpreted, is the conjugate of the refinement the word performs
— one letter at a time, `lift_cutWord` at each. -/

/-- **A letter, interpreted, is its own cut conjugated.** -/
theorem paperE_readCut_letter {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    (paperE K).map ((readCut K).map (Polygraph.cell e).toPath) = Rconj (chCutHom e) :=
  (congrArg (paperE K).map ((readCut_letter e).trans (sandwich_refl _ _ _))).trans
    ((paperE_quot _).trans (lift_cutWord (chCutHom e) (codim_chCutHom e)))

/-- **A word of bead cuts, interpreted, is the conjugate of the refinement it performs.** -/
theorem paperE_readCut {z : (chCutPoly K).V} : ∀ {v : GenObj (chCutPoly K).Gen}
    (w : Quiver.Path ((chCutPoly K).pt z) v) {f : vChain v.as ⟶ vChain z}
    (_hf : baseHom f = Cut.ev ((chProj K).mapPath w)),
    (paperE K).map ((readCut K).map w) = Rconj f := by
  intro v w
  induction w with
  | nil =>
      intro f hf
      obtain rfl : f = 𝟙 (vChain z) := hom_ext_baseHom (by
        rw [hf, Prefunctor.mapPath_nil, Cut.ev_nil]; rfl)
      refine Eq.trans (congrArg (paperE K).map ((readCut K).map_id ((chCutPoly K).pt z))) ?_
      rw [(paperE K).map_id, Rconj_of_W _ (MorphismProperty.id_mem _ _)]
      exact (eqToHom_refl _ _).symm
  | @cons m v w e ih =>
      intro f hf
      obtain rfl : f = chCutHom e ≫ liftOf (Cut.ev ((chProj K).mapPath w)) (map_ev w) :=
        hom_ext_baseHom (by
          rw [hf, baseHom_comp, baseHom_liftOf, Prefunctor.mapPath_cons, Cut.ev_cons]
          rfl)
      refine Eq.trans (congrArg (paperE K).map
        ((readCut K).map_comp w (Polygraph.cell e).toPath)) ?_
      rw [(paperE K).map_comp, ih (f := liftOf (Cut.ev ((chProj K).mapPath w)) (map_ev w)) rfl,
        paperE_readCut_letter e, Rconj_comp]
      rfl

/-- **…so the paper reads a refinement as its conjugate.** -/
theorem paperE_Theta {c d : Ch K} (u : c ⟶ d) :
    (paperE K).map ((Theta K).map u.op) = Rconj u :=
  paperE_readCut (chPath (a := chV c) (b := chV d) u)
    (ev_chPath (a := chV c) (b := chV d) u).symm

/-! ## The merges become isomorphisms

A merge's cut word is spelled out of the picked letters, and each of those reads as a renaming. -/

/-- **A word of picked letters reads as a renaming.** -/
theorem readCut_of_all_picked : ∀ {x y : GenObj (chCutPoly K).Gen} (w : Quiver.Path x y)
    (_hw : Quiver.Path.All (fun ⦃_ _⦄ e => chCutPicked K e) w),
    ∃ h : (readCut K).obj x = (readCut K).obj y, (readCut K).map w = eqToHom h := by
  intro x y w
  induction w with
  | nil => intro _; exact ⟨rfl, ((readCut K).map_id _).trans (eqToHom_refl _ rfl).symm⟩
  | @cons m v w e ih =>
      intro hw
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff w (Polygraph.cell e)).mp hw
      obtain ⟨hx, hxw⟩ := ih h₀
      have hobj : (readCut K).obj m = (readCut K).obj v :=
        congrArg (readColl K).obj ((chCollapse K).repObj_eq_of_S (Polygraph.cell e) he)
      refine ⟨hx.trans hobj, ?_⟩
      refine Eq.trans ((readCut K).map_comp w (Polygraph.cell e).toPath) ?_
      rw [hxw]
      refine Eq.trans (congrArg (fun t => eqToHom hx ≫ t) (cutArr_merge e he hobj)) ?_
      exact eqToHom_trans _ _

/-- **A merge names a renaming.** -/
theorem cutArrow_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    ∃ h : subPt' d = subPt' c, cutArrow m = eqToHom h :=
  readCut_of_all_picked _ (all_chPath_of_W (a := chV c) (b := chV d) m hm)

/-- **…and the paper's polygraph inverts them.** -/
theorem Theta_inverts : ((W K).op).IsInvertedBy (Theta K) := by
  rintro ⟨d⟩ ⟨c⟩ u hu
  obtain ⟨h, hu'⟩ := cutArrow_of_W u.unop hu
  rw [show (Theta K).map u = eqToHom h from hu']
  exact ⟨⟨eqToHom h.symm, (eqToHom_trans _ _).trans (eqToHom_refl _ _),
    (eqToHom_trans _ _).trans (eqToHom_refl _ _)⟩⟩

/-! ## …so the paper's reading is a localization

`Theta ⋙ paperE ≅ Q` is the merge below each chain, so the descent of `Theta` along `Q` and the
paper's reading are mutually inverse. -/

/-- **The paper reads a chain as the run below it.** -/
noncomputable def ThetaIso (K : BPSet) : Theta K ⋙ paperE K ≅ ((W K).op).Q :=
  NatIso.ofComponents (fun c => (mergeIso (W_bottomHom c.unop)).symm) (by
    rintro ⟨d⟩ ⟨c⟩ u
    change (paperE K).map ((Theta K).map u.unop.op) ≫ (mergeIso (W_bottomHom c)).inv
      = (mergeIso (W_bottomHom d)).inv ≫ arr u.unop
    rw [paperE_Theta u.unop, Iso.comp_inv_eq, Rconj, mergeIso_hom]
    exact (Category.assoc _ _ _).symm)

/-- The descent of the paper's reading of the chains along the localization. -/
noncomputable abbrev Phi (K : BPSet) : ((W K).op).Localization ⥤ (poly K).presented :=
  Localization.Construction.lift (Theta K) Theta_inverts

theorem Q_comp_Phi (K : BPSet) : ((W K).op).Q ⋙ Phi K = Theta K :=
  Localization.Construction.fac _ _

/-- **Reading back, then reading, is the identity on `Ch(K)[W⁻¹]`.** -/
noncomputable def PhiPaperIso (K : BPSet) : Phi K ⋙ paperE K ≅ 𝟭 (((W K).op).Localization) :=
  Localization.liftNatIso ((W K).op).Q ((W K).op) (Theta K ⋙ paperE K) (((W K).op).Q)
    (Phi K ⋙ paperE K) (𝟭 _) (ThetaIso K)

/-! ## …and the other way round

A 1-cell of the paper's polygraph is a crossing codimension-one cut, so its word is its own letter;
that is what makes reading and reading back the identity on the presented category. -/

/-- **A codimension-one refinement's cut word is its own letter.** -/
theorem cutArrow_eq_cutArr {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    cutArrow u = cutArr (cutGenOf u hu) := by
  refine readCut_congr ?_
  rw [ev_chPath, Prefunctor.mapPath_toPath]
  exact (Category.comp_id _).symm

/-- **…so the paper reads it as the word that cut spells.** -/
theorem cutArrow_eq_cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    cutArrow u = (poly K).quot.map (cutWord u hu) :=
  (cutArrow_eq_cutArr u hu).trans (congrArg (poly K).quot.map (readWords_toPath u hu))

/-- **A 1-cell's own refinement spells that 1-cell.** -/
theorem cutWord_hom {X Y : Run K} (α : Gen X Y) :
    cutWord α.hom α.codim_hom
      = readAt α.below.symm (bottomRun_self Y).symm (Polygraph.cell (P := poly K) α).toPath := by
  have hW : ¬ W K α.hom := α.not_W_hom one_ne_zero
  have hβ : (cellCongr (Cell 1) α.below.symm (bottomRun_self Y).symm α).obj = α.obj :=
    cellCongr_const (F := Cell 1) Cell.obj _ _ α
  refine (cutWord_of_run α.degree_obj α.codim_hom hW).trans ?_
  refine Eq.trans (genWord_congr rfl (bottomRun_self Y).symm
    (β := cellCongr (Cell 1) α.below.symm (bottomRun_self Y).symm α) hβ.symm) ?_
  exact (genWord_congr α.below.symm (bottomRun_self Y).symm hβ.symm).symm

/-! ## Reading a 1-cell back -/

/-- The object a chain names, read back. -/
theorem Phi_obj (c : Ch K) : (Phi K).obj (rho c) = (Theta K).obj (op c) :=
  Functor.congr_obj (Q_comp_Phi K) (op c)

theorem Phi_arr {c d : Ch K} (v : c ⟶ d) :
    (Phi K).map (arr v)
      = eqToHom (Phi_obj d) ≫ (Theta K).map v.op ≫ eqToHom (Phi_obj c).symm :=
  Functor.congr_hom (Q_comp_Phi K) v.op

/-- **A merge is read back as a renaming.** -/
theorem Phi_arr_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    ∃ h : (Phi K).obj (rho d) = (Phi K).obj (rho c), (Phi K).map (arr m) = eqToHom h := by
  obtain ⟨h, hm'⟩ := cutArrow_of_W m hm
  refine ⟨((Phi_obj d).trans h).trans (Phi_obj c).symm, ?_⟩
  rw [Phi_arr m, show (Theta K).map m.op = eqToHom h from hm']
  exact (congrArg (fun t => eqToHom (Phi_obj d) ≫ t) (eqToHom_trans _ _)).trans
    (eqToHom_trans _ _)

/-- **…so the conjugate of a refinement is read back as the refinement.** -/
theorem Phi_Rconj {c d : Ch K} (v : c ⟶ d) :
    ∃ (p : (Phi K).obj (rho (bottomRun d).chain) = (Phi K).obj (rho d))
      (q : (Phi K).obj (rho c) = (Phi K).obj (rho (bottomRun c).chain)),
      (Phi K).map (Rconj v) = eqToHom p ≫ (Phi K).map (arr v) ≫ eqToHom q := by
  obtain ⟨hd, hd'⟩ := Phi_arr_of_W (bottomHom d) (W_bottomHom d)
  obtain ⟨hc, hc'⟩ := Phi_arr_of_W (bottomHom c) (W_bottomHom c)
  refine ⟨hd.symm, hc, ?_⟩
  have hinv : (Phi K).map ((mergeIso (W_bottomHom d)).inv) = eqToHom hd.symm := by
    refine eq_eqToHom_symm hd ?_
    rw [← hd', ← (Phi K).map_comp]
    exact (congrArg (Phi K).map (mergeIso (W_bottomHom d)).hom_inv_id).trans ((Phi K).map_id _)
  rw [Rconj, (Phi K).map_comp, (Phi K).map_comp, hinv, hc']

/-! ## Reading, then reading back, is the identity -/

/-- **The run below a run is that run.** -/
theorem Theta_obj_run (X : Run K) : (Theta K).obj (op X.chain) = (poly K).quot.obj (runPt X) :=
  congrArg (fun Z : Run K => (poly K).quot.obj (runPt Z)) (bottomRun_self X)

theorem paperPhi_obj (X : Run K) :
    (poly K).quot.obj (runPt X) = (Phi K).obj (rho X.chain) :=
  (Theta_obj_run X).symm.trans (Phi_obj X.chain).symm

/-- **A 1-cell is read, then read back, as itself.** -/
theorem Phi_cellRconj {X Y : Run K} (α : Gen X Y) :
    (Phi K).map (cellRconj α)
      = eqToHom (paperPhi_obj X).symm
        ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (paperPhi_obj Y) := by
  obtain ⟨p, q, hR⟩ := Phi_Rconj α.hom
  have hArr : (Phi K).map (arr α.hom)
      = eqToHom (Phi_obj α.obj) ≫ (poly K).quot.map (cutWord α.hom α.codim_hom)
        ≫ eqToHom (Phi_obj Y.chain).symm :=
    (Phi_arr α.hom).trans (sandwich_congr _ _ (cutArrow_eq_cutWord α.hom α.codim_hom))
  have hWd : (poly K).quot.map (cutWord α.hom α.codim_hom)
      = eqToHom (congrArg (poly K).quot.obj (congrArg runPt α.below.symm)).symm
        ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (congrArg (poly K).quot.obj (congrArg runPt (bottomRun_self Y).symm)) := by
    rw [cutWord_hom α, readAt]
    exact Paths.map_cellCongr₂ (poly K).quot _ _ _
  rw [cellRconj, (Phi K).map_comp, (Phi K).map_comp, eqToHom_map, eqToHom_map, hR,
    hArr.trans (sandwich_congr _ _ hWd)]
  exact collapse4 _ _ _ _ _ _ _ _ _ _

/-- **Reading, then reading back, is the identity on the presented category.** -/
noncomputable def paperPhiIso (K : BPSet) :
    𝟭 ((poly K).presented) ≅ paperE K ⋙ Phi K := by
  refine NatIso.ofComponents (fun x => eqToIso (paperPhi_obj x.as.as)) ?_
  rintro ⟨x⟩ ⟨y⟩ f
  obtain ⟨w, rfl⟩ := (poly K).quot.map_surjective f
  refine Polygraph.naturality_of_gen (P := poly K) (fun z => eqToHom (paperPhi_obj z.as))
    (fun {a b} e => ?_) w
  have hp : (paperE K ⋙ Phi K).map ((poly K).quot.map e.toPath)
      = (Phi K).map (cellRconj e) :=
    congrArg (Phi K).map ((paperE_quot _).trans (Paths.lift_toPath (paperPre' (K := K)) e))
  exact Eq.trans (cancel_eqToHom (paperPhi_obj a.as) _).symm
    (congrArg (fun t => eqToHom (paperPhi_obj a.as) ≫ t) (hp.trans (Phi_cellRconj e))).symm

/-- **The interpretation of the paper's cells is an equivalence**, with the reading of the chains
as its inverse. -/
noncomputable instance isEquivalence_paperE (K : BPSet) : (paperE K).IsEquivalence :=
  Functor.IsEquivalence.mk' (Phi K) (paperPhiIso K) (PhiPaperIso K)

/-- **The paper's polygraph presents `Ch(K)[W⁻¹]`** — 0-cells the runs, 1- and 2-cells the objects
of degree one and two — for every `K` and with no hypothesis on `K`. -/
noncomputable def paperPresents (K : BPSet) :
    Presents (poly K) (((W K).op).Localization) := ⟨paperE K, inferInstance⟩

@[simp] theorem paperPresents_E (K : BPSet) : (paperPresents K).E = paperE K := rfl

/-- **A 1-cell names the arrow its object's refinement conjugates to.** -/
theorem paperE_map_gen {x y : GenObj (Gen (K := K))} (e : x ⟶ y) :
    (paperE K).map ((poly K).quot.map e.toPath) = cellRconj e :=
  (paperE_quot _).trans (Paths.lift_toPath (paperPre' (K := K)) e)

/-- **…so the chains, read on the paper's cells, are a localization.** -/
instance isLocalization_Theta (K : BPSet) : (Theta K).IsLocalization ((W K).op) where
  inverts := Theta_inverts
  isEquivalence := by
    have h : Localization.Construction.lift (Theta K) Theta_inverts = Phi K := rfl
    rw [h]
    exact Functor.IsEquivalence.mk' (paperE K) (PhiPaperIso K).symm (paperPhiIso K).symm

/-! ## Strict naturality of the interpretation -/

section Natural

variable {K' : BPSet} (f : K ⟶ K')

/-- **The run below a chain is carried along.** -/
theorem bottomRun_pushforward (c : Ch K) :
    bottomRun ((pushforward f).obj c) = (Run.pushforward f).obj (bottomRun c) :=
  eq_bottomRun_of_W ((pushforward f).map (bottomHom c))
    ((W_pushforward_iff f (bottomHom c)).mpr (W_bottomHom c))

/-- **…and so is the object a chain names.** -/
theorem chLocOpMap_obj (c : Ch K) :
    (chLocOpMap f).obj (rho c) = rho ((pushforward f).obj c) :=
  Functor.congr_obj (Q_comp_chLocOpMap f) (op c)

theorem chLocOpMap_arr {c d : Ch K} (u : c ⟶ d) :
    (chLocOpMap f).map (arr u)
      = eqToHom (chLocOpMap_obj f d) ≫ arr ((pushforward f).map u)
        ≫ eqToHom (chLocOpMap_obj f c).symm :=
  Functor.congr_hom (Q_comp_chLocOpMap f) u.op

theorem arr_pushforward {c d : Ch K} (u : c ⟶ d) :
    arr ((pushforward f).map u)
      = eqToHom (chLocOpMap_obj f d).symm ≫ (chLocOpMap f).map (arr u)
        ≫ eqToHom (chLocOpMap_obj f c) := by
  rw [chLocOpMap_arr]; simp

/-- …spelled at the chain, where the merge below lives. -/
theorem bottomRun_chain_pushforward (c : Ch K) :
    (bottomRun ((pushforward f).obj c)).chain = (pushforward f).obj (bottomRun c).chain :=
  congrArg Run.chain (bottomRun_pushforward f c)

/-- The object a run names, carried along. -/
theorem locObj_bottom (c : Ch K) :
    (chLocOpMap f).obj (rho (bottomRun c).chain) = rho (bottomRun ((pushforward f).obj c)).chain :=
  (chLocOpMap_obj f (bottomRun c).chain).trans
    (congrArg rho (bottomRun_chain_pushforward f c).symm)

/-- **The merge below a chain is carried to the merge below its image** — both are merges. -/
theorem pushforward_bottomHom (c : Ch K) :
    (pushforward f).map (bottomHom c)
      = eqToHom (bottomRun_chain_pushforward f c).symm ≫ bottomHom ((pushforward f).obj c) :=
  eq_of_W ((W_pushforward_iff f _).mpr (W_bottomHom c))
    ((W K').comp_mem _ _ (W_eqToHom _) (W_bottomHom _))

/-- The merge below the image, read through the image of the merge below. -/
theorem arr_bottomHom_pushforward (a : Ch K) :
    arr (bottomHom ((pushforward f).obj a))
      = arr ((pushforward f).map (bottomHom a))
        ≫ eqToHom (congrArg rho (bottomRun_chain_pushforward f a)) := by
  rw [pushforward_bottomHom f a, arr_comp, arr_eqToHom, Category.assoc, eqToHom_trans]
  exact (Category.comp_id _).symm

/-- Two renamings after an arrow are one. -/
private theorem sandwich_merge {C : Type*} [Category C] {A B X Y Z : C} (p : A = B) {g : B ⟶ X}
    (r : X = Y) (s : Y = Z) (q : X = Z) :
    eqToHom p ≫ (g ≫ eqToHom r) ≫ eqToHom s = eqToHom p ≫ g ≫ eqToHom q := by
  subst p; subst r; subst s; simp

/-- Two conjugates spliced at a renaming and its inverse. -/
private theorem splice {C : Type*} [Category C] {P Q R M S T : C} (a : P ⟶ Q) (g : Q ⟶ R)
    (p : R = M) (k : R ⟶ S) (c : S ⟶ T) :
    (a ≫ g ≫ eqToHom p) ≫ (eqToHom p.symm ≫ k ≫ c) = (a ≫ g ≫ k) ≫ c := by
  subst p; simp

/-- **The merge below a chain, carried along.** -/
theorem chLocOpMap_arr_bottomHom (a : Ch K) :
    (chLocOpMap f).map (arr (bottomHom a))
      = eqToHom (chLocOpMap_obj f a) ≫ arr (bottomHom ((pushforward f).obj a))
        ≫ eqToHom (locObj_bottom f a).symm := by
  rw [chLocOpMap_arr f (bottomHom a), arr_bottomHom_pushforward f a]
  exact (sandwich_merge _ _ _ _).symm

/-- **…and so is the conjugate of a refinement**, the only transports being the two runs' names. -/
theorem chLocOpMap_Rconj {c d : Ch K} (u : c ⟶ d) :
    eqToHom (locObj_bottom f d).symm ≫ (chLocOpMap f).map (Rconj u)
        ≫ eqToHom (locObj_bottom f c) = Rconj ((pushforward f).map u) := by
  refine Rconj_eq_of _ ?_
  have hd : arr (bottomHom ((pushforward f).obj d))
      = eqToHom (chLocOpMap_obj f d).symm ≫ (chLocOpMap f).map (arr (bottomHom d))
        ≫ eqToHom (locObj_bottom f d) := by
    rw [chLocOpMap_arr_bottomHom f d]; simp
  have key : (chLocOpMap f).map (arr (bottomHom d)) ≫ (chLocOpMap f).map (Rconj u)
      = (chLocOpMap f).map (arr u) ≫ (chLocOpMap f).map (arr (bottomHom c)) :=
    ((chLocOpMap f).map_comp _ _).symm.trans
      ((congrArg (chLocOpMap f).map (arr_bottomHom_comp_Rconj u)).trans
        ((chLocOpMap f).map_comp _ _))
  have hc : arr (bottomHom ((pushforward f).obj c))
      = eqToHom (chLocOpMap_obj f c).symm ≫ (chLocOpMap f).map (arr (bottomHom c))
        ≫ eqToHom (locObj_bottom f c) := by
    rw [chLocOpMap_arr_bottomHom f c]; simp
  rw [hd, hc, arr_pushforward f u]
  refine Eq.trans (splice _ _ _ _ _) (Eq.trans ?_ (splice _ _ _ _ _).symm)
  exact congrArg
    (fun t => (eqToHom (chLocOpMap_obj f d).symm ≫ t) ≫ eqToHom (locObj_bottom f c)) key

end Natural

end ChainCat.Paper
