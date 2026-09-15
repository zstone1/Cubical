import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Concurrency.Presentation.PairChain

/-!
# Concurrency/Presentation/ChainWeb — the runs over a chain carry Matsumoto's functor

The runs over a chain are a web on the paper's cells (`chWeb`), and a refinement is a map of webs —
composition of runs with its shape — along which climbs evaluate alike (`Web.eval_mapPath`):

    runs over o ──chPush q──▸ runs over d        o the pair chain, placed under a foot of d

So the 2-cell of `o` closes every polygon of `d` (`isArtin_chWeb`), and a refinement reads,
functorially, as the web arrow from its target's bottom run to its source's (`thetaAt`). -/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The web over a chain -/

/-- The object of the presented category a run names. -/
noncomputable abbrev pt (X : Run K) : (poly K).presented := (poly K).quot.obj (runPt X)

/-- **The runs over a chain, as a web on the paper's cells.** -/
noncomputable abbrev chWeb (e : Ch K) (N : ℕ) :
    Web N (zObj (𝟙^N) ⟶ zObj e.dims) (poly K).presented where
  toLower := shapeLower N (zObj e.dims)
  pre :=
    { obj := fun σ => pt (shapeRun e σ)
      map := fun ε => (poly K).quot.map (genWord (ascGen e ε)) }

/-- **A climb evaluates to the word it spells.** -/
theorem chWeb_eval (e : Ch K) (N : ℕ) {a : zObj (𝟙^N) ⟶ zObj e.dims} :
    ∀ {b : zObj (𝟙^N) ⟶ zObj e.dims} (R : Climb (shapeLower N (zObj e.dims)).perm a b),
      (chWeb e N).eval.map R = (poly K).quot.map ((ascPre e N).mapPath R)
  | _, .nil => rfl
  | _, .cons R ε =>
      (congrArg (· ≫ (poly K).quot.map (genWord (ascGen e ε))) (chWeb_eval e N R)).trans
        ((poly K).quot_map_cons _ _).symm

/-! ## A refinement is a map of webs -/

section Push

variable {c d : Ch K} (u : c ⟶ d) {N : ℕ}

/-- **An atom over the source, pushed, is the same atom.** -/
theorem ascObj_pushAscent {a b : zObj (𝟙^N) ⟶ zObj c.dims} (ε : ChAsc c a b) :
    ascObj d (pushAscent (baseMap u) ε) = ascObj c ε :=
  congrArg (fun m => (⟨atomComp N ε.idx, m⟩ : Ch K)) (by
    rw [ascLeg_pushAscent]
    exact (Category.assoc (zPhi (ascLeg ε)) (zPhi (baseMap u)) d.map).trans
      (congrArg (zPhi (ascLeg ε) ≫ ·) u.w))

/-- The runs over a refinement's source, pushed onto its target. -/
noncomputable abbrev chPush : Ascents (chWeb c N).perm ⥤q Ascents (chWeb d N).perm :=
  pushPre (baseMap u)

theorem chPush_obj (σ : zObj (𝟙^N) ⟶ zObj c.dims) :
    (chWeb d N).pre.obj ((chPush u).obj σ) = (chWeb c N).pre.obj σ :=
  congrArg pt (shapeRun_comp u σ)

theorem chPush_map {a b : zObj (𝟙^N) ⟶ zObj c.dims} (ε : Ascent (chWeb c N).perm a b) :
    (chWeb d N).pre.map ((chPush u).map ε)
      = eqToHom (chPush_obj u a) ≫ (chWeb c N).pre.map ε ≫ eqToHom (chPush_obj u b).symm := by
  change (poly K).quot.map (genWord (ascGen d (pushAscent (baseMap u) ε))) = _
  rw [← genWord_congr (α := ascGen c ε) (β := ascGen d (pushAscent (baseMap u) ε))
    (shapeRun_comp u a).symm (shapeRun_comp u b).symm (ascObj_pushAscent u ε).symm]
  exact Paths.map_cellCongr₂ (poly K).quot _ _ _

end Push

/-! ## Artin's relation over every chain

Two covers into a run span a polygon whose foot ascends through both (`ascent_polyFoot`), so the
pair chain sits under the foot (`exists_pairLeg`); its 2-cell equates the two maximal climbs of its
runs, and pushed onto the chain those are two climbs from the foot through the two covers. -/

/-- **The relation a degree-two object imposes, read on its web**: its two maximal climbs, however
spelled, name one arrow up to its longest run. -/
theorem chWeb_rel (e : Ch K) {N : ℕ} (hN : dimSum e.dims = N) (h2 : degree (zObj e.dims) = 2)
    {i k : Fin (N - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : Nonempty (zObj (atomComp N i) ⟶ zObj e.dims))
    (hk : Nonempty (zObj (atomComp N k) ⟶ zObj e.dims))
    {P₁ : Climb (chWeb e N).perm (runMerge (zObj e.dims) hN) (riseElem hN hik hi hk _ le_rfl)}
    {P₂ : Climb (chWeb e N).perm (runMerge (zObj e.dims) hN)
      (riseElem hN (Ne.symm hik) hk hi _ le_rfl)}
    (h₁ : riseClimb hN _ _ _ _ le_rfl = P₁) (h₂ : riseClimb hN _ _ _ _ le_rfl = P₂) :
    (chWeb e N).eval.map P₁ ≫ eqToHom (congrArg (chWeb e N).pre.obj (riseElem_cox hN h2 _ _ _))
      = (chWeb e N).eval.map P₂
        ≫ eqToHom (congrArg (chWeb e N).pre.obj (riseElem_cox hN h2 _ _ _)) := by
  subst h₁; subst h₂
  have h := quot_riseWord e hN h2 hik hi hk
  rw [riseWord, riseWord, quot_readAt, quot_readAt] at h
  rw [chWeb_eval, chWeb_eval]
  have h' := congrArg (· ≫ eqToHom (congrArg pt (topRun_eq_shapeRun e hN))) ((cancel_epi _).mp h)
  simpa only [Category.assoc, eqToHom_trans] using h'

/-- **Artin's relation holds over every chain.** -/
theorem isArtin_chWeb (d : Ch K) (N : ℕ) : (chWeb d N).IsArtin := by
  intro v b b' e e' hbb'
  have hij : (e.idx : ℕ) ≠ (e'.idx : ℕ) := (e.idx_ne_iff (chWeb d N).perm_inj e').mpr hbb'
  have hd : dimSum d.dims = N := dimSum_eq_of_onesHom v
  have hvi := e.descent
  have hvj := e'.descent
  -- the pair chain, placed under the foot
  obtain ⟨Q, hQ⟩ : ∃ Q : pairChain N e.idx e'.idx ⟶ zObj d.dims,
      crossPerm (dimSum_pairChain _ _) Q = polyFoot ((chWeb d N).perm v) e.idx e'.idx :=
    exists_pairLeg (nonempty_atomComp_of_descent hd v hvi)
      (nonempty_atomComp_of_descent hd v hvj)
      (fun k hk => ascent_polyFoot hij hvi hvj (hk.imp Fin.ext Fin.ext))
      ((chWeb d N).perm_foot e e' hbb')
  -- the degree-two object it names over `d`
  let o : Ch K := ⟨(pairChain N e.idx e'.idx).dims, zPhi Q ≫ d.map⟩
  let q : o ⟶ d := ⟨zPhi Q, rfl⟩
  have hN : dimSum (zObj o.dims).dims = N := dimSum_pairChain _ _
  have h2 : degree (zObj o.dims) = 2 := degree_pairChain hij
  have hi : Nonempty (zObj (atomComp N e.idx) ⟶ zObj o.dims) := nonempty_left_pairChain
  have hj : Nonempty (zObj (atomComp N e'.idx) ⟶ zObj o.dims) := nonempty_right_pairChain
  have hQq : crossPerm (tgtStrands (runMerge (zObj o.dims) hN) (dimSum_replicate N)) (baseMap q)
      = polyFoot ((chWeb d N).perm v) e.idx e'.idx := hQ
  -- its two maximal climbs, through the two covers' crossings, each ending in its last letter
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = cox e.idx e'.idx :=
    ⟨_, Nat.sub_add_cancel (by have := two_le_cox hij; omega)⟩
  obtain ⟨x₁, R₁, f₁, hR₁, hf₁⟩ := riseClimb_eq_cons hN hij hi hj _ le_rfl m hm
  obtain ⟨x₂, R₂, f₂, hR₂, hf₂⟩ :=
    riseClimb_eq_cons hN (Ne.symm hij) hj hi _ le_rfl m (hm.trans (cox_comm _ _))
  -- the relation, read on the web over `o`
  have hrel := chWeb_rel o hN h2 hij hi hj hR₁ hR₂
  -- the top of `o`, pushed, is the run the two covers enter
  have hinv : altWord e.idx e'.idx (cox e.idx e'.idx) * altWord e.idx e'.idx (cox e.idx e'.idx)
      = 1 := by
    nth_rewrite 1 [← altWord_cox_inv hij]
    exact inv_mul_cancel _
  have hT : (chPush q).obj (shapeTop (zObj o.dims) hN) = v := (chWeb d N).perm_inj (by
    change crossPerm (dimSum_replicate N) (shapeTop (zObj o.dims) hN ≫ baseMap q) = _
    rw [crossPerm_comp, hQq, ← riseElem_cox hN h2 hij hi hj, riseElem_val, polyFoot, mul_assoc,
      hinv, mul_one])
  have hend₁ := (congrArg (chPush q).obj (riseElem_cox hN h2 hij hi hj)).trans hT
  have hend₂ := (congrArg (chPush q).obj (riseElem_cox hN h2 (Ne.symm hij) hj hi)).trans hT
  have hpushed := congrArg (· ≫ eqToHom (congrArg (chWeb d N).pre.obj hT))
    (Web.eval_mapPath_eq (chPush q) (chPush_obj q) (chPush_map q) _ _
      (riseElem_cox hN h2 hij hi hj) (riseElem_cox hN h2 (Ne.symm hij) hj hi) hrel)
  simp only [Category.assoc, eqToHom_trans] at hpushed
  -- the foot of `d`, and the two last covers
  have hfoot : (chPush q).obj (runMerge (zObj o.dims) hN) = (chWeb d N).foot e e' hbb' :=
    (chWeb d N).perm_inj (by
      change crossPerm (dimSum_replicate N) (runMerge (zObj o.dims) hN ≫ baseMap q) = _
      rw [crossPerm_comp, crossPerm_runMerge, mul_one, hQq]
      exact ((chWeb d N).perm_foot e e' hbb').symm)
  have key : ∀ {c₁ c₂ : zObj (𝟙^N) ⟶ zObj d.dims} (g₁ : Ascent (chWeb d N).perm c₁ v)
      (g₂ : Ascent (chWeb d N).perm c₂ v),
      g₁.idx = altIdx e.idx e'.idx m → g₂.idx = altIdx e'.idx e.idx m →
      ∃ (R : Climb (chWeb d N).perm ((chPush q).obj (runMerge (zObj o.dims) hN)) c₁)
        (R' : Climb (chWeb d N).perm ((chPush q).obj (runMerge (zObj o.dims) hN)) c₂),
        (chWeb d N).eval.map (R.cons g₁) = (chWeb d N).eval.map (R'.cons g₂) := by
    intro c₁ c₂ g₁ g₂ hg₁ hg₂
    have hx : ∀ {x y : zObj (𝟙^N) ⟶ zObj o.dims} (f : Ascent (chWeb o N).perm x y)
        {c : zObj (𝟙^N) ⟶ zObj d.dims} (g : Ascent (chWeb d N).perm c v),
        (chPush q).obj y = v → f.idx = g.idx → (chPush q).obj x = c := by
      intro x y f c g hy hfg
      refine (chWeb d N).perm_inj (((chPush q).map f).perm_eq'.trans ?_)
      rw [show ((chPush q).map f).idx = g.idx from hfg, hy]
      exact g.perm_eq'.symm
    obtain ⟨S₁, hS₁⟩ := (chWeb d N).exists_eval_cons ((chPush q).mapPath R₁)
      ((chPush q).map f₁) (hx f₁ g₁ hend₁ (hf₁.trans hg₁.symm)) hend₁ g₁
    obtain ⟨S₂, hS₂⟩ := (chWeb d N).exists_eval_cons ((chPush q).mapPath R₂)
      ((chPush q).map f₂) (hx f₂ g₂ hend₂ (hf₂.trans hg₂.symm)) hend₂ g₂
    exact ⟨S₁, S₂, hS₁.trans (hpushed.trans hS₂.symm)⟩
  rw [← hfoot]
  rcases altIdx_cases e.idx e'.idx m with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact key e e' h₁.symm h₂.symm
  · obtain ⟨R, R', h⟩ := key e' e h₁.symm h₂.symm
    exact ⟨R', R, h.symm⟩

/-! ## A refinement, read on the paper's cells

A refinement names the run over its target that its source is merged from (`cutTop`), and the web
over the target has an arrow up to it from the target's own merge run.  That run, for a composite,
is the first factor's pushed along the second — so the reading is a functor. -/

/-- The run over a refinement's target that its source is merged from. -/
noncomputable abbrev cutTop {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    zObj (𝟙^N) ⟶ zObj d.dims :=
  runMerge (zObj c.dims) hN ≫ baseMap u

theorem shapeRun_cutTop {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    shapeRun d (cutTop u hN) = bottomRun c :=
  (shapeRun_comp u _).trans (bottomRun_eq_shapeRun c hN).symm

/-- **The arrow a refinement names**, from the run below its target to the run below its source. -/
noncomputable def thetaAt {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    pt (bottomRun d) ⟶ pt (bottomRun c) :=
  eqToHom (congrArg pt (bottomRun_eq_shapeRun d ((dimSum_eq_of_hom u).symm.trans hN)))
    ≫ (chWeb d N).arrow (runMerge_le _ (cutTop u hN))
    ≫ eqToHom (congrArg pt (shapeRun_cutTop u hN))

/-- …read at any count of the events. -/
theorem thetaAt_eq {c d : Ch K} (u : c ⟶ d) {N : ℕ} (hN : dimSum c.dims = N) :
    thetaAt u hN = thetaAt u rfl := by
  subst hN; rfl

/-- **The reading is functorial** — a composite's run is the first factor's, pushed along the
second, and Matsumoto's arrow is natural along the push. -/
theorem thetaAt_comp {b c d : Ch K} (v : b ⟶ c) (u : c ⟶ d) {N : ℕ} (hb : dimSum b.dims = N) :
    thetaAt (v ≫ u) hb = thetaAt u ((dimSum_eq_of_hom v).symm.trans hb) ≫ thetaAt v hb := by
  have hc : dimSum c.dims = N := (dimSum_eq_of_hom v).symm.trans hb
  have hp : (chPush u).obj (cutTop v hb) = cutTop (v ≫ u) hb := Category.assoc _ _ _
  obtain ⟨R⟩ := (chWeb c N).nonempty_climb (runMerge_le hc (cutTop v hb))
  have hle := Climb.le ((chPush u).mapPath R)
  have hA := Web.arrow_map (isArtin_chWeb d N) (chPush u) (chPush_obj u) (chPush_map u)
    (runMerge_le hc (cutTop v hb)) hle
  have hle' : WeakOrder.of ((chWeb d N).perm (cutTop u hc))
      ≤ WeakOrder.of ((chWeb d N).perm (cutTop (v ≫ u) hb)) := hp ▸ hle
  have hB := (chWeb d N).arrow_congr rfl hp hle hle'
  have hC := (chWeb d N).arrow_comp (isArtin_chWeb d N)
    (runMerge_le (s := zObj d.dims) ((dimSum_eq_of_hom u).symm.trans hc) (cutTop u hc)) hle'
  rw [hB] at hA
  have hA' : (chWeb c N).arrow (runMerge_le hc (cutTop v hb))
      = eqToHom (chPush_obj u _).symm ≫ (eqToHom (congrArg (chWeb d N).pre.obj rfl)
        ≫ (chWeb d N).arrow hle' ≫ eqToHom (congrArg (chWeb d N).pre.obj hp).symm)
        ≫ eqToHom (chPush_obj u _) := by
    rw [hA]; simp
  rw [thetaAt, thetaAt, thetaAt, hA', ← hC]
  dsimp only [chWeb, cutTop, chPush, pushPre]
  simp

end ChainCat.Paper
