import CubeChains.Concurrency.Presentation.PaperPoly

/-!
# Concurrency/Presentation/ChainWeb — the runs over a chain carry Matsumoto's functor

The runs over a chain are a web on the paper's cells (`chWeb`), and a refinement is a map of webs —
left translation on runs — along which climbs evaluate alike (`Web.eval_mapPath`):

    runs over o ──chPush q──▸ runs over d        o the pair chain, placed under a foot of d

So the 2-cell of `o` closes every polygon of `d` (`isArtin_chWeb`), and a refinement reads,
functorially, as the web arrow from its target's bottom run to its source's (`thetaAt`). -/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

/-! ## Maps of webs -/

namespace CubeChains.Web

variable {n : ℕ} {V V' : Type*} {C : Type*} [Category C] {W : Web n V C} {W' : Web n V' C}

/-- Two renamed arrows, composed at a shared renaming. -/
private theorem sandwich_comp {A A' B B' D D' : C} (p : A = A') (q : B = B') (r : D = D')
    (f : A' ⟶ B') (g : B' ⟶ D') :
    (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm)
      = eqToHom p ≫ (f ≫ g) ≫ eqToHom r.symm := by
  subst p; subst q; subst r; simp

/-- **A climb evaluates alike along a map of webs** — a prefunctor of ascent quivers carrying each
object and cover to its own, up to renaming the objects. -/
theorem eval_mapPath (φ : Ascents W.perm ⥤q Ascents W'.perm)
    (hobj : ∀ v, W'.pre.obj (φ.obj v) = W.pre.obj v)
    (hmap : ∀ {v w : V} (e : Ascent W.perm v w),
      W'.pre.map (φ.map e) = eqToHom (hobj v) ≫ W.pre.map e ≫ eqToHom (hobj w).symm)
    {v : V} : ∀ {w : V} (R : Climb W.perm v w),
      W'.eval.map (φ.mapPath R) = eqToHom (hobj v) ≫ W.eval.map R ≫ eqToHom (hobj w).symm
  | _, .nil => by
      change 𝟙 _ = eqToHom (hobj v) ≫ 𝟙 _ ≫ eqToHom (hobj v).symm
      rw [Category.id_comp]
      exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm
  | _, .cons R e => by
      change W'.eval.map (φ.mapPath R) ≫ W'.pre.map (φ.map e)
        = eqToHom (hobj v) ≫ (W.eval.map R ≫ W.pre.map e) ≫ eqToHom (hobj _).symm
      rw [eval_mapPath φ hobj hmap R, hmap e]
      exact sandwich_comp (hobj v) (hobj _) (hobj _) _ _

/-- **…so does Matsumoto's arrow**, once the target web satisfies Artin's relation. -/
theorem arrow_map (hW' : W'.IsArtin) (φ : Ascents W.perm ⥤q Ascents W'.perm)
    (hobj : ∀ v, W'.pre.obj (φ.obj v) = W.pre.obj v)
    (hmap : ∀ {v w : V} (e : Ascent W.perm v w),
      W'.pre.map (φ.map e) = eqToHom (hobj v) ≫ W.pre.map e ≫ eqToHom (hobj w).symm)
    {v w : V} (h : WeakOrder.of (W.perm v) ≤ WeakOrder.of (W.perm w))
    (h' : WeakOrder.of (W'.perm (φ.obj v)) ≤ WeakOrder.of (W'.perm (φ.obj w))) :
    W'.arrow h' = eqToHom (hobj v) ≫ W.arrow h ≫ eqToHom (hobj w).symm :=
  (eval_eq_arrow hW' (φ.mapPath (W.nonempty_climb h).some)).symm.trans
    (eval_mapPath φ hobj hmap _)

/-- An arrow between renamed ends. -/
theorem arrow_congr (W : Web n V C) {a a' b b' : V} (ha : a = a') (hb : b = b')
    (h : WeakOrder.of (W.perm a) ≤ WeakOrder.of (W.perm b))
    (h' : WeakOrder.of (W.perm a') ≤ WeakOrder.of (W.perm b')) :
    W.arrow h
      = eqToHom (congrArg W.pre.obj ha) ≫ W.arrow h' ≫ eqToHom (congrArg W.pre.obj hb).symm := by
  subst ha; subst hb
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- **An arrow between equal ends is a renaming.** -/
theorem arrow_of_eq (W : Web n V C) {a b : V} (hab : a = b)
    (h : WeakOrder.of (W.perm a) ≤ WeakOrder.of (W.perm b)) :
    W.arrow h = eqToHom (congrArg W.pre.obj hab) := by
  subst hab; exact (arrow_refl h).trans (eqToHom_refl _ _).symm

/-- A climb re-ended at renamed ends, with the last cover it forces. -/
theorem exists_eval_cons (W : Web n V C) {a x x' y y' : V} (R : Climb W.perm a x)
    (f : Ascent W.perm x y) (hx : x = x') (hy : y = y') (e : Ascent W.perm x' y') :
    ∃ R' : Climb W.perm a x',
      W.eval.map (R'.cons e) = W.eval.map (R.cons f) ≫ eqToHom (congrArg W.pre.obj hy) := by
  subst hx; subst hy
  exact ⟨R, by
    rw [Subsingleton.elim e f]
    exact (Category.comp_id _).symm.trans (congrArg _ (eqToHom_refl _ _).symm)⟩

end CubeChains.Web

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The web over a chain -/

/-- The object of the presented category a run names. -/
noncomputable abbrev pt (X : Run K) : (poly K).presented := (poly K).quot.obj (runPt X)

/-- **The runs over a chain, as a web on the paper's cells.** -/
noncomputable abbrev chWeb (e : Ch K) (N : ℕ) : Web N (ChPerm e N) (poly K).presented where
  toLower := shapeLower N (zObj e.dims)
  pre :=
    { obj := fun σ => pt (shapeRun e σ)
      map := fun ε => (poly K).quot.map (genWord (ascGen e ε)) }

/-- **A climb evaluates to the word it spells.** -/
theorem chWeb_eval (e : Ch K) (N : ℕ) {a : ChPerm e N} :
    ∀ {b : ChPerm e N} (R : Climb (shapeLower N (zObj e.dims)).perm a b),
      (chWeb e N).eval.map R = (poly K).quot.map ((ascPre e N).mapPath R)
  | _, .nil => rfl
  | _, .cons R ε =>
      (congrArg (· ≫ (poly K).quot.map (genWord (ascGen e ε))) (chWeb_eval e N R)).trans
        ((poly K).quot_map_cons _ _).symm

/-! ## A refinement is a map of webs -/

section Push

variable {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hc : dimSum c.dims = N)

/-- **A run over a refinement's source, read over its target, is the same run.** -/
theorem shapeRun_pushPerm (σ : ChPerm c N) :
    shapeRun d (pushPerm (baseMap u) σ) = shapeRun c σ :=
  Run.ext (congrArg (fun m => (⟨𝟙^N, m⟩ : Ch K)) (by
    rw [pushPerm, arr_runOf]
    exact (Category.assoc (zPhi σ.arr) (zPhi (baseMap u)) d.map).trans
      (congrArg (zPhi σ.arr ≫ ·) u.w)))

/-- **…and an atom over the source, pushed, is the same atom.** -/
theorem ascObj_pushAscent {a b : ChPerm c N} (ε : ChAsc c a b) :
    ascObj d (pushAscent (baseMap u) hc ε) = ascObj c ε :=
  congrArg (fun m => (⟨atomComp N ε.idx, m⟩ : Ch K)) (by
    rw [ascLeg_pushAscent]
    exact (Category.assoc (zPhi (ascLeg ε)) (zPhi (baseMap u)) d.map).trans
      (congrArg (zPhi (ascLeg ε) ≫ ·) u.w))

/-- The runs over a refinement's source, pushed onto its target. -/
noncomputable abbrev chPush : Ascents (chWeb c N).perm ⥤q Ascents (chWeb d N).perm :=
  pushPre (baseMap u) hc

theorem chPush_obj (σ : ChPerm c N) :
    (chWeb d N).pre.obj ((chPush u hc).obj σ) = (chWeb c N).pre.obj σ :=
  congrArg pt (shapeRun_pushPerm u σ)

theorem chPush_map {a b : ChPerm c N} (ε : Ascent (chWeb c N).perm a b) :
    (chWeb d N).pre.map ((chPush u hc).map ε)
      = eqToHom (chPush_obj u hc a) ≫ (chWeb c N).pre.map ε
        ≫ eqToHom (chPush_obj u hc b).symm := by
  change (poly K).quot.map (genWord (ascGen d (pushAscent (baseMap u) hc ε))) = _
  rw [← genWord_congr (α := ascGen c ε) (β := ascGen d (pushAscent (baseMap u) hc ε))
    (shapeRun_pushPerm u a).symm (shapeRun_pushPerm u b).symm (ascObj_pushAscent u hc ε).symm]
  exact Paths.map_cellCongr₂ (poly K).quot _ _ _

theorem chWeb_eval_push {a b : ChPerm c N} (R : Climb (chWeb c N).perm a b) :
    (chWeb d N).eval.map ((chPush u hc).mapPath R)
      = eqToHom (chPush_obj u hc a) ≫ (chWeb c N).eval.map R
        ≫ eqToHom (chPush_obj u hc b).symm :=
  Web.eval_mapPath (chPush u hc) (chPush_obj u hc) (chPush_map u hc) R

end Push

/-! ## Artin's relation over every chain

Two covers into a run span a polygon whose foot ascends through both (`ascent_polyFoot`), so the
pair chain sits under the foot (`exists_pairLeg`); its 2-cell equates the two maximal climbs of its
runs, and pushed onto the chain those are two climbs from the foot through the two covers. -/

/-- A relation renamed on the left cancels the renaming. -/
private theorem eqToHom_cancel_left {C : Type*} [Category C] {A A' B₁ B₂ Z : C} {f : A ⟶ B₁}
    {g : A ⟶ B₂} (p p' : A' = A) (q₁ : B₁ = Z) (q₂ : B₂ = Z)
    (h : eqToHom p ≫ f ≫ eqToHom q₁ = eqToHom p' ≫ g ≫ eqToHom q₂) :
    f ≫ eqToHom q₁ = g ≫ eqToHom q₂ := by
  subst p; simpa using h

/-- A relation between two arrows out of one object, carried along renamings of all three ends. -/
private theorem eqToHom_push {C : Type*} [Category C] {A B₁ B₂ Z : C} {f : A ⟶ B₁}
    {g : A ⟶ B₂} (q₁ : B₁ = Z) (q₂ : B₂ = Z) (h : f ≫ eqToHom q₁ = g ≫ eqToHom q₂)
    {A' B₁' B₂' Z' : C} {f' : A' ⟶ B₁'} {g' : A' ⟶ B₂'} (s : A' = A) (r₁ : B₁' = B₁)
    (r₂ : B₂' = B₂) (hf : f' = eqToHom s ≫ f ≫ eqToHom r₁.symm)
    (hg : g' = eqToHom s ≫ g ≫ eqToHom r₂.symm) (t₁ : B₁' = Z') (t₂ : B₂' = Z') :
    f' ≫ eqToHom t₁ = g' ≫ eqToHom t₂ := by
  subst s hf hg r₁ r₂ q₁ t₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  rw [h]

/-- **The relation a degree-two object imposes, read on its web**: its two maximal climbs, however
spelled, name one arrow up to the object's greatest run. -/
theorem chWeb_rel (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) (h2 : degree (zObj e.dims) = 2)
    {P₁ : Climb (chWeb e N).perm (shapeBot (zObj e.dims) hN)
      (riseElem hN (shapePair (zObj e.dims) hN h2).ne (nonempty_atomComp_lo hN h2)
        (nonempty_atomComp_hi hN h2) _ le_rfl)}
    {P₂ : Climb (chWeb e N).perm (shapeBot (zObj e.dims) hN)
      (riseElem hN (shapePair (zObj e.dims) hN h2).ne.symm (nonempty_atomComp_hi hN h2)
        (nonempty_atomComp_lo hN h2) _ le_rfl)}
    (h₁ : riseClimb hN _ _ _ _ le_rfl = P₁) (h₂ : riseClimb hN _ _ _ _ le_rfl = P₂) :
    (chWeb e N).eval.map P₁ ≫ eqToHom (congrArg pt (topOf_fst_eq_riseElem e hN h2 _ _ _).symm)
      = (chWeb e N).eval.map P₂
        ≫ eqToHom (congrArg pt (topOf_fst_eq_riseElem e hN h2 _ _ _).symm) := by
  subst h₁; subst h₂
  have h := quot_loWord e hN h2
  rw [loWord, hiWord, riseWord, riseWord, quot_readAt, quot_readAt] at h
  rw [chWeb_eval, chWeb_eval]
  exact eqToHom_cancel_left _ _ _ _ h

/-- **Artin's relation holds over every chain.** -/
theorem isArtin_chWeb (d : Ch K) (N : ℕ) : (chWeb d N).IsArtin := by
  intro v b b' e e' hbb'
  have hij : (e.idx : ℕ) ≠ (e'.idx : ℕ) := (e.idx_ne_iff (chWeb d N).perm_inj e').mpr hbb'
  have hd : dimSum d.dims = N := v.strands
  have hvi : v.1 (adjHi e.idx) < v.1 (adjLo e.idx) := e.descent
  have hvj : v.1 (adjHi e'.idx) < v.1 (adjLo e'.idx) := e'.descent
  -- the pair chain, placed under the foot
  obtain ⟨Q, hQ⟩ : ∃ Q : pairChain N e.idx e'.idx hij ⟶ zObj d.dims,
      crossPerm (dimSum_pairChain hij) Q = polyFoot v.1 e.idx e'.idx := by
    refine exists_pairLeg hij hd (fun k hk => ?_) (fun k hk => ascent_polyFoot hij hvi hvj ?_)
      (((chWeb d N).foot e e' hbb').crossPerm_arr.trans ((chWeb d N).perm_foot e e' hbb'))
    · refine index_adj_eq_of_descent hd v.arr ?_
      rw [v.crossPerm_arr]
      rcases hk with hk | hk
      · rw [show k = e.idx from Fin.ext hk]; exact hvi
      · rw [show k = e'.idx from Fin.ext hk]; exact hvj
    · rcases hk with hk | hk
      · exact Or.inl (Fin.ext hk)
      · exact Or.inr (Fin.ext hk)
  -- the degree-two object it names over `d`, and its two junctions
  let o : Ch K := ⟨(pairChain N e.idx e'.idx hij).dims, zPhi Q ≫ d.map⟩
  let q : o ⟶ d := ⟨zPhi Q, rfl⟩
  have hN : dimSum o.dims = N := dimSum_pairChain hij
  have h2 : degree (zObj o.dims) = 2 := degree_pairChain hij
  have hlo := nonempty_atomComp_lo hN h2
  have hhi := nonempty_atomComp_hi hN h2
  have hne := (shapePair (zObj o.dims) hN h2).ne
  have hi : e.idx = (shapePair (zObj o.dims) hN h2).lo
      ∨ e.idx = (shapePair (zObj o.dims) hN h2).hi :=
    (nonempty_atomComp_iff hN h2 _).mp (nonempty_left_pairChain hij)
  have hj : e'.idx = (shapePair (zObj o.dims) hN h2).lo
      ∨ e'.idx = (shapePair (zObj o.dims) hN h2).hi :=
    (nonempty_atomComp_iff hN h2 _).mp (nonempty_right_pairChain hij)
  -- its two maximal climbs, each ending in its last letter
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = cox (shapePair (zObj o.dims) hN h2).lo
      (shapePair (zObj o.dims) hN h2).hi :=
    ⟨_, Nat.sub_add_cancel (by have := two_le_cox hne; omega)⟩
  obtain ⟨x₁, R₁, f₁, hR₁, hf₁⟩ := riseClimb_eq_cons hN hne hlo hhi _ le_rfl m hm
  obtain ⟨x₂, R₂, f₂, hR₂, hf₂⟩ :=
    riseClimb_eq_cons hN hne.symm hhi hlo _ le_rfl m (hm.trans (cox_comm _ _))
  -- the relation, read on the web over `o`
  have hrel := chWeb_rel o hN h2 hR₁ hR₂
  -- the top of `o`, pushed, is the run the two covers enter
  have hW : altWord e.idx e'.idx (cox e.idx e'.idx)
      = altWord (shapePair (zObj o.dims) hN h2).lo (shapePair (zObj o.dims) hN h2).hi
        (cox (shapePair (zObj o.dims) hN h2).lo (shapePair (zObj o.dims) hN h2).hi) :=
    altWord_cox_of_pair hne hi hj hij
  have hinv : altWord e.idx e'.idx (cox e.idx e'.idx) * altWord e.idx e'.idx (cox e.idx e'.idx)
      = 1 := by
    nth_rewrite 1 [← altWord_cox_inv hij]
    exact inv_mul_cancel _
  have hQv : ∀ σ : ChPerm o N, σ.1 = altWord (shapePair (zObj o.dims) hN h2).lo
      (shapePair (zObj o.dims) hN h2).hi
        (cox (shapePair (zObj o.dims) hN h2).lo (shapePair (zObj o.dims) hN h2).hi) →
      (chPush q hN).obj σ = v := by
    intro σ hσ
    refine Subtype.ext ?_
    change (pushPerm (baseMap q) σ).1 = v.1
    rw [val_pushPerm (baseMap q) hN σ, show @crossPerm Zbp (zObj o.dims) (zObj d.dims) N hN
      (baseMap q) = polyFoot v.1 e.idx e'.idx from hQ, hσ, ← hW, polyFoot, mul_assoc, hinv,
      mul_one]
  have hend₁ := hQv _ (riseElem_val hN hne hlo hhi _ le_rfl)
  have hend₂ := hQv _ ((riseElem_val hN hne.symm hhi hlo _ le_rfl).trans
    (altWord_cox_of_pair hne (Or.inr rfl) (Or.inl rfl) hne.symm))
  have hpushed := eqToHom_push _ _ hrel (chPush_obj q hN _) (chPush_obj q hN _)
    (chPush_obj q hN _) (chWeb_eval_push q hN (R₁.cons f₁))
    (chWeb_eval_push q hN (R₂.cons f₂)) (congrArg (chWeb d N).pre.obj hend₁)
    (congrArg (chWeb d N).pre.obj hend₂)
  -- the foot of `d`, and the two last covers
  have hfoot : (chPush q hN).obj (shapeBot (zObj o.dims) hN) = (chWeb d N).foot e e' hbb' :=
    Subtype.ext (by
      change (pushPerm (baseMap q) _).1 = _
      rw [val_pushPerm (baseMap q) hN, shapeBot_val, mul_one]
      exact (show @crossPerm Zbp (zObj o.dims) (zObj d.dims) N hN (baseMap q)
        = polyFoot v.1 e.idx e'.idx from hQ).trans ((chWeb d N).perm_foot e e' hbb').symm)
  have key : ∀ {c₁ c₂ : ChPerm d N} (g₁ : Ascent (chWeb d N).perm c₁ v)
      (g₂ : Ascent (chWeb d N).perm c₂ v),
      g₁.idx = altIdx (shapePair (zObj o.dims) hN h2).lo (shapePair (zObj o.dims) hN h2).hi m →
      g₂.idx = altIdx (shapePair (zObj o.dims) hN h2).hi (shapePair (zObj o.dims) hN h2).lo m →
      ∃ (R : Climb (chWeb d N).perm ((chPush q hN).obj (shapeBot (zObj o.dims) hN)) c₁)
        (R' : Climb (chWeb d N).perm ((chPush q hN).obj (shapeBot (zObj o.dims) hN)) c₂),
        (chWeb d N).eval.map (R.cons g₁) = (chWeb d N).eval.map (R'.cons g₂) := by
    intro c₁ c₂ g₁ g₂ hg₁ hg₂
    have hx : ∀ {x : ChPerm o N} {y : ChPerm o N} (f : Ascent (chWeb o N).perm x y)
        {c : ChPerm d N} (g : Ascent (chWeb d N).perm c v), (chPush q hN).obj y = v →
        f.idx = g.idx → (chPush q hN).obj x = c := by
      intro x y f c g hy hfg
      refine Subtype.ext ?_
      have h1 : ((chPush q hN).obj x).1 = ((chPush q hN).obj y).1 * adjT ((chPush q hN).map f).idx :=
        ((chPush q hN).map f).perm_eq'
      rw [h1, congrArg Subtype.val hy, show ((chPush q hN).map f).idx = g.idx from hfg]
      exact g.perm_eq'.symm
    obtain ⟨S₁, hS₁⟩ := (chWeb d N).exists_eval_cons ((chPush q hN).mapPath R₁)
      ((chPush q hN).map f₁) (hx f₁ g₁ hend₁ (hf₁.trans hg₁.symm)) hend₁ g₁
    obtain ⟨S₂, hS₂⟩ := (chWeb d N).exists_eval_cons ((chPush q hN).mapPath R₂)
      ((chPush q hN).map f₂) (hx f₂ g₂ hend₂ (hf₂.trans hg₂.symm)) hend₂ g₂
    exact ⟨S₁, S₂, hS₁.trans (hpushed.trans hS₂.symm)⟩
  rw [← hfoot]
  rcases altIdx_cases hne hi hj hij m with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key e e' h₁ h₂
  · obtain ⟨R, R', h⟩ := key e' e h₂ h₁
    exact ⟨R', R, h.symm⟩

/-! ## A refinement, read on the paper's cells

A refinement names the run over its target that its source is merged from (`cutTop`), and the web
over the target has an arrow up to it from the target's own merge run.  That run, for a composite,
is the first factor's pushed along the second — so the reading is a functor. -/

/-- The run over a refinement's target that its source is merged from. -/
noncomputable abbrev cutTop {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    ChPerm d N :=
  pushPerm (baseMap u) (shapeBot (zObj c.dims) hN)

theorem shapeRun_cutTop {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    shapeRun d (cutTop u hN) = bottomRun c :=
  (shapeRun_pushPerm u _).trans (bottomRun_eq_shapeRun c hN).symm

/-- **The arrow a refinement names**, from the run below its target to the run below its source. -/
noncomputable def thetaAt {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    pt (bottomRun d) ⟶ pt (bottomRun c) :=
  eqToHom (congrArg pt (bottomRun_eq_shapeRun d ((dimSum_eq_of_hom u).symm.trans hN)))
    ≫ (chWeb d N).arrow (shapeBot_le _ (cutTop u hN))
    ≫ eqToHom (congrArg pt (shapeRun_cutTop u hN))

/-- …read at any count of the events. -/
theorem thetaAt_eq {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    thetaAt u hN = thetaAt u rfl := by
  subst hN; rfl

/-- **The reading is functorial** — a composite's run is the first factor's, pushed along the second,
and Matsumoto's arrow is natural along the push. -/
theorem thetaAt_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) {N : ℕ} (hb : dimSum b.dims = N) :
    thetaAt (v ≫ u) hb = thetaAt u ((dimSum_eq_of_hom v).symm.trans hb) ≫ thetaAt v hb := by
  have hc : dimSum c.dims = N := (dimSum_eq_of_hom v).symm.trans hb
  have hp : (chPush u hc).obj (cutTop v hb) = cutTop (v ≫ u) hb := pushPerm_comp _ _ _
  obtain ⟨R⟩ := (chWeb c N).nonempty_climb (shapeBot_le hc (cutTop v hb))
  have hle := Climb.le ((chPush u hc).mapPath R)
  have hA := Web.arrow_map (isArtin_chWeb d N) (chPush u hc) (chPush_obj u hc) (chPush_map u hc)
    (shapeBot_le hc (cutTop v hb)) hle
  have hle' : WeakOrder.of ((chWeb d N).perm (cutTop u hc))
      ≤ WeakOrder.of ((chWeb d N).perm (cutTop (v ≫ u) hb)) := hp ▸ hle
  have hB := (chWeb d N).arrow_congr rfl hp hle hle'
  have hC := (chWeb d N).arrow_comp (isArtin_chWeb d N)
    (shapeBot_le (s := zObj d.dims) ((dimSum_eq_of_hom u).symm.trans hc) (cutTop u hc)) hle'
  rw [hB] at hA
  have hA' : (chWeb c N).arrow (shapeBot_le hc (cutTop v hb))
      = eqToHom (chPush_obj u hc _).symm ≫ (eqToHom (congrArg (chWeb d N).pre.obj rfl)
        ≫ (chWeb d N).arrow hle' ≫ eqToHom (congrArg (chWeb d N).pre.obj hp).symm)
        ≫ eqToHom (chPush_obj u hc _) := by
    rw [hA]; simp
  rw [thetaAt, thetaAt, thetaAt, hA', ← hC]
  dsimp only [chWeb, cutTop, chPush, pushPre]
  simp

end ChainCat.Paper
