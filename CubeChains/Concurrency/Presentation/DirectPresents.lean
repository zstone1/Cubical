import CubeChains.Concurrency.Presentation.ChainWeb
import CubeChains.Concurrency.Presentation.LocFunctor

/-!
# Concurrency/Presentation/DirectPresents — the paper's cells, read straight in the localization

`Rconj u` is the refinement `u` conjugated by the two merges the localization inverts:

    run(c) ──bottomHom──▸ c ──u──▸ d ◂──bottomHom── run(d)

A climb telescopes into the conjugate of the refinement it performs (`runAt_climb`), so `paperE`
reads `Theta`'s arrows as conjugates and the two are inverse.  `Q ⋙ chLocOpMap f` is an equality,
so the reading is natural in `K` on the nose. -/

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

/-! ## The interpretation -/

/-- The arrow a cell names. -/
noncomputable def cellRconj {n : ℕ} {X Y : Run K} (α : Cell n X Y) : rho X.chain ⟶ rho Y.chain :=
  eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj α.hom
    ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y))

/-- **The interpretation of the paper's 1-cells** in the localization. -/
noncomputable def paperPre' : GenObj (Gen (K := K)) ⥤q ((W K).op).Localization where
  obj X := rho X.as.chain
  map α := cellRconj α

/-- **A 1-cell's arrow is any crossing refinement out of its far end, conjugated.** -/
theorem cellRconj_of_hom {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    cellRconj α = eqToHom (congrArg (fun Z : Run K => rho Z.chain) α.below.symm) ≫ Rconj f
      ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self Y)) := by
  rw [cellRconj, Cell.hom_eq α hf]

/-! ## Renamings

Every transport below is an `eqToHom` between two spellings of one object; these collapse them
whatever their proofs, which a rewrite cannot, the spellings differing. -/

/-- A renaming on either side of an arrow that renames nothing. -/
private theorem sandwich_self {C : Type*} [Category C] {A B : C} (p : A = A) (q : B = B)
    (f : A ⟶ B) : eqToHom p ≫ f ≫ eqToHom q = f := by simp

/-- Three renamings are one. -/
private theorem eqToHom_comp3 {C : Type*} [Category C] {A B D E : C} (p : A = B) (q : B = D)
    (r : D = E) : eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom (p.trans (q.trans r)) := by simp

/-- An arrow renamed on the left, moved across. -/
private theorem eq_eqToHom_comp {C : Type*} [Category C] {A B D : C} (p : A = B) {f : B ⟶ D}
    {g : A ⟶ D} (h : g = eqToHom p ≫ f) (p' : B = A) : f = eqToHom p' ≫ g := by
  subst p; simpa using h.symm

/-- Nested renamings around an arrow, and a renaming after it, collapse. -/
private theorem collapse {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ B₂ B₃ : C} (a : A₀ = A₁)
    (p : A₁ = A₂) (f : A₂ ⟶ B₀) (q : B₀ = B₁) (r : B₁ = B₂) (b : B₂ = B₃) :
    eqToHom a ≫ (eqToHom p ≫ ((f ≫ eqToHom q) ≫ eqToHom r)) ≫ eqToHom b
      = eqToHom (a.trans p) ≫ f ≫ eqToHom (q.trans (r.trans b)) := by
  subst a p q r b; simp

/-- Two nested renamings around an arrow are one. -/
private theorem nest {C : Type*} [Category C] {A₀ A₁ A₂ B₂ B₁ B₀ : C} (a₀ : A₀ = A₁)
    (a₁ : A₁ = A₂) (f : A₂ ⟶ B₂) (b₁ : B₂ = B₁) (b₀ : B₁ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ f ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom (a₀.trans a₁) ≫ f ≫ eqToHom (b₁.trans b₀) := by
  subst a₀ a₁ b₁ b₀; simp

/-- …and four. -/
private theorem collapse4 {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₄ B₃ B₂ B₁ B₀ : C}
    (a₀ : A₀ = A₁) (a₁ : A₁ = A₂) (a₂ : A₂ = A₃) (a₃ : A₃ = A₄) {f : A₄ ⟶ B₄}
    (b₃ : B₄ = B₃) (b₂ : B₃ = B₂) (b₁ : B₂ = B₁) (b₀ : B₁ = B₀)
    (p : A₀ = A₄) (q : B₄ = B₀) :
    eqToHom a₀ ≫ (eqToHom a₁ ≫ (eqToHom a₂ ≫ (eqToHom a₃ ≫ f ≫ eqToHom b₃)
        ≫ eqToHom b₂) ≫ eqToHom b₁) ≫ eqToHom b₀
      = eqToHom p ≫ f ≫ eqToHom q := by
  subst a₀; subst a₁; subst a₂; subst a₃; subst b₃; subst b₂; subst b₁; subst b₀; simp

/-- A renaming cancelled against its inverse. -/
private theorem cancel_eqToHom {C : Type*} [Category C] {A A' B : C} (p : A = A') (f : A ⟶ B) :
    eqToHom p ≫ eqToHom p.symm ≫ f = f := by subst p; simp

/-! ## A climb, read in the localization

The two legs out of an ascent's atom are a merge and the atom's own cut, and both land on the chain,
so `Rconj`'s contravariance telescopes a climb into one conjugated refinement. -/

/-- The arrow a run over a chain names, out of the chain's own run. -/
noncomputable def runAt (e : Ch K) {N : ℕ} (σ : ChPerm e N) :
    rho (bottomRun e).chain ⟶ rho (shapeRun e σ).chain :=
  Rconj (shapeHom e σ) ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self _))

/-- **One atom appends to the conjugated refinement below it.** -/
theorem runAt_cons (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    runAt e b = runAt e a ≫ cellRconj (ascGen e ε) := by
  rw [runAt, runAt, cellRconj_of_hom (ascGen e ε) (f := ascTop e ε) (not_W_ascTop e ε),
    ← ascTop_comp e ε, ← ascBot_comp e ε, Rconj_comp, Rconj_comp,
    Rconj_of_W (ascBot e ε) (W_ascBot e ε)]
  dsimp only [obj_ascGen]
  simp

/-- **A climb is the refinement it performs**, conjugated. -/
theorem runAt_climb (e : Ch K) {N : ℕ} {a : ChPerm e N} :
    ∀ {b : ChPerm e N} (R : Climb (shapeLower N (zObj e.dims)).perm a b),
      runAt e b = runAt e a ≫ (Paths.lift (paperPre' (K := K))).map ((ascPre e N).mapPath R)
  | _, .nil => (Category.comp_id _).symm
  | _, .cons R ε => (runAt_cons e ε).trans
      (congrArg (· ≫ cellRconj (ascGen e ε)) (runAt_climb e R) |>.trans (Category.assoc _ _ _))

/-- …starting from the chain's own run, where it is a renaming. -/
theorem runAt_shapeBot (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    runAt e (shapeBot (zObj e.dims) hN)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_shapeRun e hN)) :=
  (congrArg (· ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self _)))
    (Rconj_of_W (shapeHom e (shapeBot (zObj e.dims) hN))
      ((W_iff_of_φ (f := shapeHom e (shapeBot (zObj e.dims) hN))
        (f' := (shapeBot (zObj e.dims) hN).arr) rfl).mpr (W_shapeBot_arr hN)))).trans
    (eqToHom_trans _ _)

/-- **A climb out of the chain's merge run is the conjugate of the run it reaches.** -/
theorem lift_climb (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) {σ : ChPerm e N}
    (R : Climb (shapeLower N (zObj e.dims)).perm (shapeBot (zObj e.dims) hN) σ) :
    (Paths.lift (paperPre' (K := K))).map ((ascPre e N).mapPath R)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_shapeRun e hN)).symm
        ≫ runAt e σ :=
  eq_eqToHom_comp _ ((runAt_climb e R).trans (congrArg (· ≫ _) (runAt_shapeBot e hN))) _

/-! ## Soundness -/

/-- **Two climbs to one run read alike**, at any naming of their ends. -/
private theorem lift_readAt_congr (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N)
    {σ₁ σ₂ : ChPerm e N} (h : σ₁ = σ₂)
    (R₁ : Climb (shapeLower N (zObj e.dims)).perm (shapeBot (zObj e.dims) hN) σ₁)
    (R₂ : Climb (shapeLower N (zObj e.dims)).perm (shapeBot (zObj e.dims) hN) σ₂) {X Y : Run K}
    (hx : shapeRun e (shapeBot (zObj e.dims) hN) = X) (hy₁ : shapeRun e σ₁ = Y)
    (hy₂ : shapeRun e σ₂ = Y) :
    (Paths.lift (paperPre' (K := K))).map (readAt hx hy₁ ((ascPre e N).mapPath R₁))
      = (Paths.lift (paperPre' (K := K))).map (readAt hx hy₂ ((ascPre e N).mapPath R₂)) := by
  subst h
  exact (Paths.map_cellCongr₂ _ _ _ _).trans
    ((congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
      ((lift_climb e hN R₁).trans (lift_climb e hN R₂).symm)).trans
        (Paths.map_cellCongr₂ _ _ _ _).symm)

/-- **The paper's 2-cells are sound** — both climbs of a degree-two object's polygon reach its
top. -/
theorem sound_paperPre {x y : GenObj (Gen (K := K))} (α : (poly K).Rel x y) :
    (Paths.lift (paperPre' (K := K))).map ((poly K).src α)
      = (Paths.lift (paperPre' (K := K))).map ((poly K).tgt α) := by
  have hN : dimSum α.obj.dims = dimSum α.obj.dims := rfl
  have hlo := nonempty_atomComp_lo (s := zObj α.obj.dims) hN α.degree_obj
  have hhi := nonempty_atomComp_hi (s := zObj α.obj.dims) hN α.degree_obj
  have hne := (shapePair (zObj α.obj.dims) hN α.degree_obj).ne
  change (Paths.lift (paperPre' (K := K))).map
      (readAt α.below α.top (riseWord α.obj hN α.degree_obj hne hlo hhi))
    = (Paths.lift (paperPre' (K := K))).map
      (readAt α.below α.top (riseWord α.obj hN α.degree_obj hne.symm hhi hlo))
  rw [riseWord, riseWord, readAt_trans, readAt_trans]
  exact lift_readAt_congr α.obj hN ((riseElem_cox hN α.degree_obj hne hlo hhi).trans
    (riseElem_cox hN α.degree_obj hne.symm hhi hlo).symm) _ _ _ _ _

/-- **The paper's polygraph, interpreted in `Ch(K)[W⁻¹]`.** -/
noncomputable def paperE (K : BPSet) : (poly K).presented ⥤ ((W K).op).Localization :=
  Polygraph.desc (paperPre' (K := K)) sound_paperPre

theorem paperE_quot {x y : GenObj (Gen (K := K))} (w : Quiver.Path x y) :
    (paperE K).map ((poly K).quot.map w) = (Paths.lift (paperPre' (K := K))).map w := rfl

/-- **A 1-cell names the arrow its object's refinement conjugates to.** -/
theorem paperE_map_gen {x y : GenObj (Gen (K := K))} (e : x ⟶ y) :
    (paperE K).map ((poly K).quot.map e.toPath) = cellRconj e :=
  (paperE_quot _).trans (Paths.lift_toPath (paperPre' (K := K)) e)

/-! ## The chains, read on the paper's cells -/

/-- The merge out of the run a refinement's source names over its target. -/
noncomputable def cutTopHom {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    (shapeRun d (cutTop u hN)).chain ⟶ c :=
  ⟨zPhi (runMerge (zObj c.dims) hN), by
    change zPhi (runMerge (zObj c.dims) hN) ≫ c.map = zPhi (cutTop u hN).arr ≫ d.map
    rw [arr_pushPerm, arr_shapeBot]
    exact ((Category.assoc (zPhi (runMerge (zObj c.dims) hN)) (zPhi (baseMap u)) d.map).trans
      (congrArg (zPhi (runMerge (zObj c.dims) hN) ≫ ·) u.w)).symm⟩

theorem W_cutTopHom {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    W K (cutTopHom u hN) :=
  (W_iff_of_φ (f := cutTopHom u hN) (f' := runMerge (zObj c.dims) hN) rfl).mpr (W_runMerge _ _)

/-- **…followed by the refinement, it is the run's own.** -/
theorem cutTopHom_comp {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    cutTopHom u hN ≫ u = shapeHom d (cutTop u hN) :=
  hom_ext' (show zPhi (runMerge (zObj c.dims) hN) ≫ Hom.φ u = zPhi (cutTop u hN).arr by
    rw [arr_pushPerm, arr_shapeBot]; rfl)

/-- **A merge is read as a renaming** — its source is merged from the bottom run of its target. -/
theorem thetaAt_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    thetaAt m (rfl : dimSum c.dims = dimSum c.dims)
      = eqToHom (congrArg pt (bottomRun_eq_of_W m hm)) := by
  have hc : cutTop m (rfl : dimSum c.dims = dimSum c.dims)
      = shapeBot (zObj d.dims) ((dimSum_eq_of_hom m).symm.trans rfl) := Subtype.ext (by
    simp only [val_pushPerm (baseMap m) (rfl : dimSum c.dims = dimSum c.dims), shapeBot_val,
      mul_one]
    exact crossPerm_eq_one_of_W _ ((W_zHom_iff m).mpr hm))
  rw [thetaAt, (chWeb d _).arrow_of_eq hc.symm]
  dsimp only [chWeb]
  simp

/-- **The paper's polygraph, receiving the chains**, contravariantly: a chain names the run below it
and a refinement Matsumoto's arrow over its target. -/
noncomputable def Theta (K : BPSet) : (Ch K)ᵒᵖ ⥤ (poly K).presented where
  obj c := pt (bottomRun c.unop)
  map u := thetaAt u.unop rfl
  map_id c := (thetaAt_of_W (𝟙 c.unop) (MorphismProperty.id_mem _ _)).trans (eqToHom_refl _ _)
  map_comp u v := (thetaAt_comp v.unop u.unop rfl).trans
    (congrArg (· ≫ thetaAt v.unop rfl) (thetaAt_eq u.unop _))

/-- **The paper reads a refinement as its conjugate.** -/
theorem paperE_Theta {c d : Ch K} (u : c ⟶ d) :
    (paperE K).map ((Theta K).map u.op) = Rconj u := by
  have hT : runAt d (cutTop u (rfl : dimSum c.dims = dimSum c.dims))
      = (Rconj u ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain)
          (bottomRun_eq_of_W _ (W_cutTopHom u rfl))))
        ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_self _)) := by
    rw [runAt, ← cutTopHom_comp u rfl, Rconj_comp, Rconj_of_W _ (W_cutTopHom u rfl)]
  change (paperE K).map (thetaAt u rfl) = Rconj u
  rw [thetaAt, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  refine Eq.trans (congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
    ((congrArg (paperE K).map (chWeb_eval d _ _)).trans
      ((lift_climb d _ _).trans (congrArg (_ ≫ ·) hT)))) ?_
  exact (collapse _ _ _ _ _ _).trans (sandwich_self _ _ _)

/-- **…so the paper's polygraph inverts the merges.** -/
theorem Theta_inverts : ((W K).op).IsInvertedBy (Theta K) := by
  rintro ⟨d⟩ ⟨c⟩ u hu
  rw [show (Theta K).map u = eqToHom _ from thetaAt_of_W u.unop hu]
  infer_instance

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

A 1-cell's own refinement climbs one ascent over its object, and that ascent's atom is the
object. -/

/-- The object a chain names, read back. -/
theorem Phi_obj (c : Ch K) : (Phi K).obj (rho c) = (Theta K).obj (op c) :=
  Functor.congr_obj (Q_comp_Phi K) (op c)

theorem Phi_arr {c d : Ch K} (v : c ⟶ d) :
    (Phi K).map (arr v)
      = eqToHom (Phi_obj d) ≫ (Theta K).map v.op ≫ eqToHom (Phi_obj c).symm :=
  Functor.congr_hom (Q_comp_Phi K) v.op

/-- **A merge is read back as a renaming.** -/
theorem Phi_arr_of_W {c d : Ch K} (m : c ⟶ d) (hm : W K m) :
    ∃ h : (Phi K).obj (rho d) = (Phi K).obj (rho c), (Phi K).map (arr m) = eqToHom h :=
  ⟨_, (Phi_arr m).trans ((congrArg (fun t => eqToHom (Phi_obj d) ≫ t ≫ eqToHom (Phi_obj c).symm)
    (thetaAt_of_W m hm)).trans (eqToHom_comp3 _ _ _))⟩

/-- An arrow inverse to a renaming is the renaming back. -/
private theorem eq_eqToHom_symm {C : Type*} [Category C] {A B : C} (p : A = B) {f : B ⟶ A}
    (h : eqToHom p ≫ f = 𝟙 A) : f = eqToHom p.symm := by subst p; simpa using h

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

/-- **A degree-one object's refinement climbs one ascent, and that ascent is the object.** -/
theorem Theta_map_hom {X Y : Run K} (α : Gen X Y) :
    (Theta K).map α.hom.op
      = eqToHom (congrArg pt α.below) ≫ (poly K).quot.map (genWord α)
        ≫ eqToHom (congrArg pt (bottomRun_self Y)).symm := by
  have hN : dimSum Y.chain.dims = dimSum Y.chain.dims := rfl
  obtain ⟨ε, hR⟩ := Climb.eq_cons_nil (chWeb α.obj (dimSum Y.chain.dims)).perm_inj
    ((chWeb α.obj _).nonempty_climb (shapeBot_le _ (cutTop α.hom hN))).some (by
      change permLen (pushPerm (baseMap α.hom) (shapeBot (zObj Y.chain.dims) hN)).1
        = permLen (shapeBot (zObj α.obj.dims) ((dimSum_eq_of_hom α.hom).symm.trans hN)).1 + 1
      simp only [val_pushPerm (baseMap α.hom) hN, shapeBot_val, mul_one, permLen_one,
        Nat.zero_add]
      exact (congrArg permLen (crossPerm_eq_of_φ hN (g := baseMap α.hom) (g' := α.hom) rfl)).trans
        (α.permLen_crossPerm_hom hN))
  have hobj : (ascGen α.obj ε).obj = α.obj :=
    (codim_eq_zero_iff (ascLegHom α.obj ε)).mp (by rw [codim, degree_ascObj, α.degree_obj])
  have hA : (chWeb α.obj (dimSum Y.chain.dims)).arrow (shapeBot_le _ (cutTop α.hom hN))
      = (poly K).quot.map (genWord (ascGen α.obj ε)) := by
    change (chWeb α.obj _).eval.map
      ((chWeb α.obj _).nonempty_climb (shapeBot_le _ (cutTop α.hom hN))).some = _
    rw [hR]
    exact Category.id_comp _
  change thetaAt α.hom hN = _
  rw [thetaAt, hA, ← genWord_congr (α := ascGen α.obj ε) (β := α)
    ((bottomRun_eq_shapeRun α.obj _).symm.trans α.below)
    ((shapeRun_cutTop α.hom hN).trans (bottomRun_self Y)) hobj, quot_readAt]
  exact (nest _ _ _ _ _).symm

theorem paperPhi_obj (X : Run K) : (poly K).quot.obj (runPt X) = (Phi K).obj (rho X.chain) :=
  (congrArg pt (bottomRun_self X)).symm.trans (Phi_obj X.chain).symm

/-- **A 1-cell is read, then read back, as itself.** -/
theorem Phi_cellRconj {X Y : Run K} (α : Gen X Y) :
    (Phi K).map (cellRconj α)
      = eqToHom (paperPhi_obj X).symm ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (paperPhi_obj Y) := by
  obtain ⟨p, q, hR⟩ := Phi_Rconj α.hom
  rw [cellRconj, (Phi K).map_comp, (Phi K).map_comp, eqToHom_map, eqToHom_map, hR, Phi_arr,
    Theta_map_hom α]
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
    congrArg (Phi K).map (paperE_map_gen e)
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

/-- **The merge below the target carries the conjugate to the refinement.** -/
theorem arr_bottomHom_comp_Rconj {c d : Ch K} (u : c ⟶ d) :
    arr (bottomHom d) ≫ Rconj u = arr u ≫ arr (bottomHom c) := by
  rw [Rconj, ← Category.assoc, ← mergeIso_hom (W_bottomHom d), Iso.hom_inv_id, Category.id_comp]

/-- **…and pins it.** -/
theorem Rconj_eq_of {c d : Ch K} (u : c ⟶ d)
    {t : rho (bottomRun d).chain ⟶ rho (bottomRun c).chain}
    (h : arr (bottomHom d) ≫ t = arr u ≫ arr (bottomHom c)) : t = Rconj u := by
  rw [Rconj, Iso.eq_inv_comp, mergeIso_hom]; exact h

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
