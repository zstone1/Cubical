import CubeChains.Concurrency.Presentation.ChainWeb
import CubeChains.Concurrency.Presentation.LocFunctor

/-!
# Concurrency/Presentation/DirectPresents — the paper's cells, read straight in the localization

A cospan whose first leg is a merge names an arrow of the localization (`conj`):

    a ──m (merge)──▸ e ◂──f── b          conj m f : a ⟶ b, back along m, forward along f

A cell is the cospan of its two legs, a climb telescopes into the cospan of the run it reaches
(`runAt_climb`), so `paperE` reads `Theta`'s arrows as cospans and the two are inverse. -/

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

/-! ## The arrow a cospan names -/

/-- **The arrow a cospan names** — back along its merge, forward along its other leg. -/
noncomputable def conj {a b e : Ch K} {m : a ⟶ e} (hm : W K m) (f : b ⟶ e) : rho a ⟶ rho b :=
  (mergeIso hm).inv ≫ arr f

theorem conj_congr {a b e : Ch K} {m m' : a ⟶ e} (hm : W K m) (hm' : W K m') (h : m = m')
    {f f' : b ⟶ e} (h' : f = f') : conj hm f = conj hm' f' := by
  subst h h'; rfl

/-- **Refining the far end composes.** -/
theorem conj_comp {a b b' e : Ch K} {m : a ⟶ e} (hm : W K m) (g : b' ⟶ b) (f : b ⟶ e) :
    conj hm (g ≫ f) = conj hm f ≫ arr g := by
  rw [conj, conj, arr_comp, Category.assoc]

/-- **A merge names nothing.** -/
theorem conj_self {a e : Ch K} {m : a ⟶ e} (hm : W K m) : conj hm m = 𝟙 (rho a) :=
  (mergeIso hm).inv_hom_id

/-- **Two cospans glued along a leg** — the second one's merge cancels. -/
theorem conj_comp_conj {a b c e e₀ : Ch K} {m : a ⟶ e} (hm : W K m) (l : e₀ ⟶ e) {m₀ : b ⟶ e₀}
    (hm₀ : W K m₀) (f₀ : c ⟶ e₀) : conj hm (m₀ ≫ l) ≫ conj hm₀ f₀ = conj hm (f₀ ≫ l) := by
  rw [conj_comp, conj_comp, Category.assoc]
  exact congrArg (conj hm l ≫ ·) ((mergeIso hm₀).hom_inv_id_assoc (arr f₀))

/-! ## The interpretation -/

/-- **The arrow a cell names**: the cospan of its two legs. -/
noncomputable def cellRconj {n : ℕ} {X Y : Run K} (α : Cell n X Y) : rho X.chain ⟶ rho Y.chain :=
  conj α.W_bot α.hom

/-- **The interpretation of the paper's 1-cells** in the localization. -/
noncomputable def paperPre' : GenObj (Gen (K := K)) ⥤q ((W K).op).Localization where
  obj X := rho X.as.chain
  map α := cellRconj α

/-- **A 1-cell names the cospan of any merge and any crossing refinement onto its object.** -/
theorem cellRconj_eq {X Y : Run K} (α : Gen X Y) {m : X.chain ⟶ α.obj} (hm : W K m)
    {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) : cellRconj α = conj hm f :=
  conj_congr _ _ (eq_of_W α.W_bot hm) (Cell.hom_eq α hf)

/-! ## A climb, read in the localization

The two legs out of an ascent's atom are a merge and the atom's own cut, and both land on the chain,
so gluing cospans telescopes a climb into the cospan of the run it reaches. -/

/-- The arrow a run over a chain names, out of the chain's own run. -/
noncomputable def runAt (e : Ch K) {N : ℕ} (σ : ChPerm e N) :
    rho (bottomRun e).chain ⟶ rho (shapeRun e σ).chain :=
  conj (W_bottomHom e) (shapeHom e σ)

/-- **One atom appends to the cospan below it.** -/
theorem runAt_cons (e : Ch K) {N : ℕ} {a b : ChPerm e N} (ε : ChAsc e a b) :
    runAt e b = runAt e a ≫ cellRconj (ascGen e ε) := by
  rw [cellRconj_eq (ascGen e ε) (W_ascBot e ε) (not_W_ascTop e ε), runAt, runAt,
    ← ascBot_comp e ε, ← ascTop_comp e ε]
  exact (conj_comp_conj _ _ _ _).symm

/-- **A climb is the refinement it performs.** -/
theorem runAt_climb (e : Ch K) {N : ℕ} {a : ChPerm e N} :
    ∀ {b : ChPerm e N} (R : Climb (shapeLower N (zObj e.dims)).perm a b),
      runAt e b = runAt e a ≫ (Paths.lift (paperPre' (K := K))).map ((ascPre e N).mapPath R)
  | _, .nil => (Category.comp_id _).symm
  | _, .cons R ε => (runAt_cons e ε).trans
      (congrArg (· ≫ cellRconj (ascGen e ε)) (runAt_climb e R) |>.trans (Category.assoc _ _ _))

/-- …starting from the chain's own run, where it is a renaming. -/
theorem runAt_shapeBot (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) :
    runAt e (shapeBot (zObj e.dims) hN)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_shapeRun e hN)) := by
  have hm : shapeHom e (shapeBot (zObj e.dims) hN)
      = eqToHom (congrArg Run.chain (bottomRun_eq_shapeRun e hN)).symm ≫ bottomHom e :=
    eq_of_W ((W_iff_of_φ (f := shapeHom e (shapeBot (zObj e.dims) hN))
        (f' := (shapeBot (zObj e.dims) hN).arr) rfl).mpr (W_shapeBot_arr hN))
      ((W K).comp_mem _ _ (W_eqToHom _) (W_bottomHom e))
  rw [runAt, hm, conj_comp, conj_self, Category.id_comp, arr_eqToHom]

/-- **A climb out of the chain's merge run is the cospan of the run it reaches.** -/
theorem lift_climb (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) {σ : ChPerm e N}
    (R : Climb (shapeLower N (zObj e.dims)).perm (shapeBot (zObj e.dims) hN) σ) :
    (Paths.lift (paperPre' (K := K))).map ((ascPre e N).mapPath R)
      = eqToHom (congrArg (fun Z : Run K => rho Z.chain) (bottomRun_eq_shapeRun e hN)).symm
        ≫ runAt e σ :=
  (eqToHom_comp_iff _ _ _).mp
    ((runAt_climb e R).trans (congrArg (· ≫ _) (runAt_shapeBot e hN))).symm

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

/-- **A 1-cell names the cospan of its legs.** -/
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

/-- **The paper reads a refinement as the cospan of the merge below its target.** -/
theorem paperE_Theta {c d : Ch K} (u : c ⟶ d) :
    (paperE K).map ((Theta K).map u.op) = conj (W_bottomHom d) (bottomHom c ≫ u) := by
  have hm : cutTopHom u rfl
      = eqToHom (congrArg Run.chain (shapeRun_cutTop u rfl)) ≫ bottomHom c :=
    eq_of_W (W_cutTopHom u rfl) ((W K).comp_mem _ _ (W_eqToHom _) (W_bottomHom c))
  have hR : runAt d (cutTop u rfl)
      = conj (W_bottomHom d) (bottomHom c ≫ u)
        ≫ eqToHom (congrArg (fun Z : Run K => rho Z.chain) (shapeRun_cutTop u rfl)).symm := by
    rw [runAt, ← cutTopHom_comp u rfl, conj_comp, hm, arr_comp, arr_eqToHom, ← Category.assoc,
      ← conj_comp]
  change (paperE K).map (thetaAt u rfl) = _
  rw [thetaAt, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  refine (congrArg (fun t => eqToHom _ ≫ t ≫ eqToHom _)
    ((congrArg (paperE K).map (chWeb_eval d _ _)).trans
      ((lift_climb d _ _).trans (congrArg (_ ≫ ·) hR)))).trans ?_
  exact (eqToHom_nest _ _ _ _ rfl rfl).trans ((conj_eqToHom_iff_heq' _ _ rfl rfl).mpr HEq.rfl).symm

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
    rw [paperE_Theta u.unop, conj_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (conj (W_bottomHom d) u.unop ≫ ·)
      (mergeIso (W_bottomHom c)).hom_inv_id).trans (Category.comp_id _)))

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

/-- **A cospan is read back as its far leg**, the merge being read as a renaming. -/
theorem Phi_conj {a b e : Ch K} {m : a ⟶ e} (hm : W K m) (f : b ⟶ e) :
    ∃ (p : (Phi K).obj (rho a) = (Theta K).obj (op e))
      (q : (Theta K).obj (op b) = (Phi K).obj (rho b)),
      (Phi K).map (conj hm f) = eqToHom p ≫ (Theta K).map f.op ≫ eqToHom q := by
  have h : (Phi K).obj (rho e) = (Phi K).obj (rho a) :=
    (Phi_obj e).trans ((congrArg pt (bottomRun_eq_of_W m hm)).trans (Phi_obj a).symm)
  have hW : (Phi K).mapIso (mergeIso hm) = eqToIso h :=
    Iso.ext ((Phi_arr m).trans (by
      change eqToHom _ ≫ thetaAt m rfl ≫ eqToHom _ = _
      rw [thetaAt_of_W m hm]
      simp))
  refine ⟨h.symm.trans (Phi_obj e), (Phi_obj b).symm, ?_⟩
  rw [conj, Functor.map_comp, ← Functor.mapIso_inv, hW, eqToIso.inv, Phi_arr]
  exact eqToHom_trans_assoc _ _ _

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
  exact (eqToHom_nest _ _ _ _ _ _).symm

theorem paperPhi_obj (X : Run K) : (poly K).quot.obj (runPt X) = (Phi K).obj (rho X.chain) :=
  (congrArg pt (bottomRun_self X)).symm.trans (Phi_obj X.chain).symm

/-- **A 1-cell is read, then read back, as itself.** -/
theorem Phi_cellRconj {X Y : Run K} (α : Gen X Y) :
    (Phi K).map (cellRconj α)
      = eqToHom (paperPhi_obj X).symm ≫ (poly K).quot.map (Polygraph.cell (P := poly K) α).toPath
        ≫ eqToHom (paperPhi_obj Y) := by
  obtain ⟨p, q, hR⟩ := Phi_conj α.W_bot α.hom
  rw [cellRconj, hR, Theta_map_hom α]
  exact eqToHom_nest _ _ _ _ _ _

/-- **Reading, then reading back, is the identity on the presented category.** -/
noncomputable def paperPhiIso (K : BPSet) :
    𝟭 ((poly K).presented) ≅ paperE K ⋙ Phi K := by
  refine NatIso.ofComponents (fun x => eqToIso (paperPhi_obj x.as.as)) ?_
  rintro ⟨x⟩ ⟨y⟩ f
  obtain ⟨w, rfl⟩ := (poly K).quot.map_surjective f
  refine Polygraph.naturality_of_gen (P := poly K) (fun z => eqToHom (paperPhi_obj z.as))
    (fun {a b} e => ?_) w
  exact ((congrArg (eqToHom (paperPhi_obj a.as) ≫ ·)
    ((congrArg (Phi K).map (paperE_map_gen e)).trans (Phi_cellRconj e))).trans
      ((eqToHom_comp_iff _ _ _).mpr rfl)).symm

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

/-! ## The interpretation, carried along a map of `K` -/

section Natural

variable {K' : BPSet} (f : K ⟶ K')

/-- **The object a chain names is carried along.** -/
theorem chLocOpMap_obj (c : Ch K) :
    (chLocOpMap f).obj (rho c) = rho ((pushforward f).obj c) :=
  Functor.congr_obj (Q_comp_chLocOpMap f) (op c)

theorem chLocOpMap_arr {c d : Ch K} (u : c ⟶ d) :
    (chLocOpMap f).map (arr u)
      = eqToHom (chLocOpMap_obj f d) ≫ arr ((pushforward f).map u)
        ≫ eqToHom (chLocOpMap_obj f c).symm :=
  Functor.congr_hom (Q_comp_chLocOpMap f) u.op

/-- **…and so is the arrow a cospan names** — the localized pushforward is strict. -/
theorem chLocOpMap_conj {a b e : Ch K} {m : a ⟶ e} (hm : W K m) (u : b ⟶ e) :
    (chLocOpMap f).map (conj hm u)
      = eqToHom (chLocOpMap_obj f a)
        ≫ conj ((W_pushforward_iff f m).mpr hm) ((pushforward f).map u)
        ≫ eqToHom (chLocOpMap_obj f b).symm := by
  have hW : (chLocOpMap f).mapIso (mergeIso hm)
      = eqToIso (chLocOpMap_obj f e) ≪≫ mergeIso ((W_pushforward_iff f m).mpr hm)
        ≪≫ eqToIso (chLocOpMap_obj f a).symm :=
    Iso.ext (chLocOpMap_arr f m)
  rw [conj, Functor.map_comp, ← Functor.mapIso_inv, hW, chLocOpMap_arr]
  simp [conj]

end Natural

end ChainCat.Paper
