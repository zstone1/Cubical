import CubeChains.Concurrency.Presentation.RunContract
import CubeChains.Concurrency.Presentation.Retraction
import CubeChains.Machinery.Presentation.Reduce

/-!
# Concurrency/Presentation/RunReduce — a bead cut at a run is a braid loop

    ⟨bead cuts | codim-2 cells⟩ ──invert merges──▸ ──contract──▸ ⟨cuts at a run | those cells⟩

A 0-cell of the contraction *is* the run on its own events (`shOf_eq_ones`), so a bead cut out of it
is a loop, and `zRun_arrow_runLoop` reads that loop off its crossing permutation alone.  The cuts
that start at a run are exactly the `N−1` atoms (`keptEquiv`), each naming `atomLoop`.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

set_option quotPrecheck false in
/-- The localization functor of the base, the only one this file names. -/
local notation "Qz" => ((W Zbp).op).Q

/-- The bead cuts of `Ch Zbp` acting on an element. -/
local notation "ZP" => chCutPoly Zbp

/-! ## The fibre is a point

`Zbp` is terminal, so a serial wedge maps into it in exactly one way: a 0-cell of the lifted
polygraph is its shape, and the element a 1-cell carries is no condition at all. -/

/-- The fibre over a shape is a point — `Zbp` is terminal.  Stated at the type `zEltV` sees:
`Cut.poly.V` does not unfold at instance transparency. -/
instance zFibreUnique (d : Ch Zbp) :
    Unique ((wedgeHoms Zbp).obj (zCutPresentation.at' (Cut.poly.pt d))) :=
  inferInstanceAs (Unique (⋁d.dims ⟶ Zbp))

/-- The shape a 0-cell of the lifted polygraph names.  `Cut.poly.V` does not unfold at instance
transparency, so the projection is wrapped at the type callers see. -/
abbrev shOf {K : BPSet} (z : (chCutPoly K).V) : Ch Zbp := z.1

/-- The merges among the lifted bead cuts. -/
noncomputable abbrev chCutPicked (K : BPSet) :
    ∀ {a b : (chCutPoly K).V}, (chCutPoly K).Gen a b → Prop :=
  chPicked zCutPresentation Cut.mergeGen K

/-- The lifted bead cuts with a formal inverse adjoined to each merge. -/
noncomputable abbrev cutLocPoly (K : BPSet) : Polygraph := chCutLocFunctor.obj K

/-- The merges of `ZP`, and `ZP` with a formal inverse adjoined to each of them. -/
local notation "ZS" => chCutPicked Zbp

local notation "ZL" => invPoly (ZP) (ZS)

/-- The bead cut an unmerged 1-cell of the extension is. -/
def chFwdOf {K : BPSet} {a b : (chCutPoly K).V} :
    ∀ g : InvGen (chCutPoly K) (chCutPicked K) a b, ¬ Cut.merged g → (chCutPoly K).Gen a b
  | .inl e, _ => e
  | .inr _, h => absurd trivial h

/-- A 0-cell of the lifted polygraph is its shape. -/
theorem zEltV_ext {z z' : (ZP).V} (h : shOf z = shOf z') : z = z' := by
  obtain ⟨d, m⟩ := z
  obtain ⟨d', m'⟩ := z'
  subst h
  exact congrArg _ (Subsingleton.elim m m')

/-- The 0-cell a shape names. -/
def zEltV (d : Ch Zbp) : (ZP).V := ⟨d, default⟩

/-- A bead cut, acting on the unique element over its shape. -/
def zEltGen {z z' : (ZP).V} (e : Cut.Refine (shOf z) (shOf z')) :
    (ZP).Gen z z' := ⟨e, Subsingleton.elim _ _⟩

/-- A leg out of an atom's cell into a degree-two chain cuts once. -/
theorem codim_leg {d : Ch Zbp} (hdeg : degree d = 2) {N : ℕ} {k : Fin (N - 1)}
    (w : zObj (atomComp N k) ⟶ d) : codim w = 1 := by rw [codim, hdeg, degree_atomComp]

/-- **Two two-step factorisations of one codimension-two refinement, as a 2-cell** — a word of
length two *is* a two-step factorisation, so the 2-cell carries no more data than its value. -/
noncomputable def pairCell {K : BPSet} {z zm zm' zd : (chCutPoly K).V}
    (e₁ : (chCutPoly K).Gen zd zm) (e₂ : (chCutPoly K).Gen zm z)
    (e₁' : (chCutPoly K).Gen zd zm') (e₂' : (chCutPoly K).Gen zm' z)
    (hev : Cut.genHom e₂.1 ≫ Cut.genHom e₁.1 = Cut.genHom e₂'.1 ≫ Cut.genHom e₁'.1) :
    (chCutPoly K).Rel ⟨zd⟩ ⟨z⟩ where
  src := (Quiver.Path.nil.cons (Polygraph.cell e₁)).cons (Polygraph.cell e₂)
  tgt := (Quiver.Path.nil.cons (Polygraph.cell e₁')).cons (Polygraph.cell e₂')
  cell :=
    { src := (Quiver.Path.nil.cons e₁.1).cons e₂.1
      tgt := (Quiver.Path.nil.cons e₁'.1).cons e₂'.1
      src_length := rfl
      tgt_length := rfl
      ev_eq := by simpa using hev }
  src_eq := rfl
  tgt_eq := rfl

/-! ## The localized cut presentation, named -/

/-- The presentation of `(Ch Zbp)ᵒᵖ` the localized one is built on. -/
noncomputable abbrev zEltPres : Presents (ZP) ((Ch Zbp)ᵒᵖ) :=
  chPresentation Zbp zCutPresentation

theorem W_op_eq_chCutPicked :
    (W Zbp).op = (zEltPres.pickedArrows (ZS)).multiplicativeClosure :=
  multiplicativeClosure_chPicked zCutPresentation Cut.mergeGen
    (by rw [pickedArrows_mergeGen, ← MorphismProperty.multiplicativeClosure_op]; rfl) Zbp

/-- The generating quiver of the lifted polygraph, over the bead cuts. -/
abbrev zEltProj : GenObj (zCutPresentation.elementsGen (wedgeHoms Zbp)) ⥤q GenObj Cut.Refine :=
  zCutPresentation.elementsProj (wedgeHoms Zbp)

/-- **The refinement a word of the lifted polygraph performs** — the bead cuts it projects to,
evaluated. -/
noncomputable def zEltHom {z z' : (ZP).V} (u : Quiver.Path ((ZP).pt z) ((ZP).pt z')) :
    shOf z' ⟶ shOf z := Cut.ev (zEltProj.mapPath u)

@[simp] theorem zEltHom_toPath {z z' : (ZP).V} (e : (ZP).Gen z z') :
    zEltHom (Polygraph.cell e).toPath = Cut.genHom e.1 := Category.comp_id _

/-! ## A 0-cell is the shape it names

The element a 0-cell carries *is* the classifying map of its shape, so the comparison is the
identity wedge map — no transport survives into the reading of a word. -/

/-- The shape a 0-cell names, in the opposite where the cut presentation lives. -/
def zEltObjIso (z : (ZP).V) : zEltPres.at' ((ZP).pt z) ≅ op (shOf z) :=
  Iso.op (X := shOf z) (Y := (⟨(shOf z).dims, z.2⟩ : Ch Zbp))
    { hom := ⟨𝟙 _, Subsingleton.elim _ _⟩
      inv := ⟨𝟙 _, Subsingleton.elim _ _⟩
      hom_inv_id := hom_ext' (Category.comp_id _)
      inv_hom_id := hom_ext' (Category.comp_id _) }

/-- **A word of the lifted polygraph performs the refinement it projects to** — the fibre being a
point, the only comparison is the renaming of its two ends. -/
theorem zEltPres_eval_map {z z' : (ZP).V} (u : Quiver.Path ((ZP).pt z) ((ZP).pt z')) :
    zEltPres.eval.map u = (zEltObjIso z).hom ≫ (zEltHom u).op ≫ (zEltObjIso z').inv := by
  have hr : Hom.φ (((zEltObjIso z).hom ≫ (zEltHom u).op ≫ (zEltObjIso z').inv).unop)
      = Hom.φ (zEltHom u) := by
    change 𝟙 _ ≫ Hom.φ (zEltHom u) ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  have hl : Hom.φ ((zEltPres.eval.map u).unop) = Hom.φ (zEltHom u) := by
    change Hom.φ (homOfRestrict ((zCutPresentation.elements (wedgeHoms Zbp)).eval.map u).val.unop
      ((zCutPresentation.elements (wedgeHoms Zbp)).eval.map u).property) = _
    rw [homOfRestrict_φ, zCutPresentation.elements_eval_val (wedgeHoms Zbp) u]
    rfl
  exact Quiver.Hom.unop_inj (hom_ext' (hl.trans hr.symm))

/-! ## …with the merges inverted

`locComparison` reads the extension by formal inverses through `Q`, so a forward word still
performs the refinement it projects to — now in `Ch(Z)[W⁻¹]`. -/

/-- Re-bracketing a five-fold composite.  Stated for `exact`: the object slots of `≫` carry two
spellings of one object here, which defeats `simp`'s matching. -/
private theorem comp_assoc₅ {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) :
    a ≫ (b ≫ c ≫ d) ≫ e = (a ≫ b) ≫ c ≫ (d ≫ e) := by simp

/-- Cancelling the two inner isomorphisms of a conjugate.  Stated for `exact`, for the same
reason. -/
private theorem conj_cancel {C : Type*} [Category C] {X₀ X₁ Y Z A B X₂ X₃ : C} (p : X₀ ⟶ X₁)
    (q : X₁ ⟶ Y) (I : Z ≅ Y) (f : Y ⟶ B) (J : A ≅ B) (m : B ⟶ X₂) (n : X₂ ⟶ X₃) :
    (p ≫ q ≫ I.inv) ≫ (I.hom ≫ f ≫ J.inv) ≫ (J.hom ≫ m ≫ n) = p ≫ q ≫ f ≫ m ≫ n := by simp

/-- `Ch(Z)[W⁻¹]` presented by the bead cuts plus a formal inverse for each merge. -/
noncomputable abbrev zLocPres : Presents (ZL) (((W Zbp).op).Localization) :=
  zEltPres.presentsLocalization (ZS) W_op_eq_chCutPicked

local notation "ZCmp" => zEltPres.locComparison (ZS) W_op_eq_chCutPicked

/-- The shape a 0-cell names, in `Ch(Z)[W⁻¹]`. -/
noncomputable def zLocIso (z : (ZP).V) :
    zLocPres.at' ((ZL).pt z) ≅ (Qz).obj (op (shOf z)) :=
  (ZCmp).app ⟨(ZP).pt z⟩ ≪≫ (Qz).mapIso (zEltObjIso z)

/-- **A forward word performs the refinement it projects to.** -/
theorem zLoc_eval_fwd {z z' : (ZP).V} (u : Quiver.Path ((ZP).pt z) ((ZP).pt z')) :
    zLocPres.eval.map ((fwdPre (ZP) (ZS)).mapPath u)
      = (zLocIso z).hom ≫ (Qz).map (zEltHom u).op ≫ (zLocIso z').inv := by
  have hQ : (Qz).map (zEltPres.eval.map u) = (Qz).map (zEltObjIso z).hom
      ≫ ((Qz).map (zEltHom u).op ≫ (Qz).map (zEltObjIso z').inv) :=
    (congrArg (Qz).map (zEltPres_eval_map u)).trans
      (((Qz).map_comp _ _).trans (congrArg (fun t => (Qz).map (zEltObjIso z).hom ≫ t)
        ((Qz).map_comp _ _)))
  refine Eq.trans (zEltPres.eval_fwd_mapPath (ZS) W_op_eq_chCutPicked u) ?_
  refine Eq.trans (congrArg (fun t => ((ZCmp).app (⟨(ZP).pt z⟩ : (ZP).presented)).hom ≫ t
    ≫ ((ZCmp).app (⟨(ZP).pt z'⟩ : (ZP).presented)).inv) hQ) ?_
  exact comp_assoc₅ _ _ _ _ _

/-! ## The merge onto the run

`Machinery/Presentation/Localize`'s cancellation 2-cells make the merge word invertible, and
`zLoc_eval_fwd` says which arrow it is. -/

/-- A renaming of chains is a merge — `W K` contains the identities. -/
theorem W_eqToHom {K : BPSet} {a b : Ch K} (h : a = b) : W K (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact MorphismProperty.id_mem _ _

/-- **The conjugated loop, from any pair of merges onto the run** — `eq_of_W` pins both, so no
choice of merge is involved. -/
theorem conj_eq_of_merges {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b)
    {ma : zObj (𝟙^N) ⟶ a} (hma : W Zbp ma) {mb : zObj (𝟙^N) ⟶ b} (hmb : W Zbp mb) :
    conj ha f = @inv _ _ _ _ _ (isIso_Q_op_of_W hmb) ≫ (Qz).map f.op ≫ (Qz).map ma.op := by
  obtain rfl : ma = runMerge a ha := eq_runMerge ha hma
  obtain rfl : mb = runMerge b (tgtStrands f ha) := eq_runMerge (tgtStrands f ha) hmb
  rfl

/-- **The merge word onto a 0-cell's run performs that merge.** -/
theorem zEltHom_eltRunWord (z : (ZP).V) : zEltHom (eltRunWord z) = zRunMerge (shOf z) :=
  (congrArg (fun p => Cut.ev p) (elementsProj_eltRunWord z)).trans (ev_runCutWord (shOf z))

/-- …conjugated onto the 0-cells of the presentation. -/
noncomputable def zRunIso (z : (ZP).V) :
    zLocPres.at' ((ZL).pt z) ≅ zLocPres.at' ((ZL).pt (eltRep z)) :=
  zLocIso z ≪≫ mergeIso (W_zRunMerge (shOf z)) ≪≫ (zLocIso (eltRep z)).symm

/-- **The contraction's merge word is that merge.** -/
theorem eval_word_eq (z : (ZP).V) :
    zLocPres.eval.map (zCutContraction.word z) = (zRunIso z).hom :=
  (zLoc_eval_fwd (eltRunWord z)).trans
    (congrArg (fun t : shOf (eltRep z) ⟶ shOf z => (zLocIso z).hom
      ≫ (Qz).map (Quiver.Hom.op t) ≫ (zLocIso (eltRep z)).inv)
      (zEltHom_eltRunWord z))

/-- **…and its inverse word is the inverse** — the cancellation 2-cells, read in the
localization. -/
theorem eval_invWord_eq (z : (ZP).V) :
    zLocPres.eval.map (zCutContraction.invWord z) = (zRunIso z).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← eval_word_eq]
  exact zEltPres.eval_fwd_comp_invWord (ZS) W_op_eq_chCutPicked (eltRunWord z)
    (all_eltRunWord z)

/-! ## A 1-cell of the contraction, read in `Ch(Z)[W⁻¹]`

A 1-cell is a *forward* bead cut — a formal inverse is merged, hence contracted away — and the
contraction reads it conjugated by the merges onto the runs of its two ends. -/

/-- The bead cut a 1-cell of the contraction performs, as a refinement of `Ch Zbp`. -/
def zRunHom {x y : zCutContraction.V} (g : zCutContraction.Gen x y) : shOf g.cod ⟶ shOf g.dom :=
  Cut.genHom (chFwdOf g.gen g.not_mem).1

/-- **A 1-cell is the word the contraction conjugates it to.** -/
theorem zRun_arrow_eq_eval {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    zRunPresentation.arrow g = zLocPres.eval.map (zCutContraction.backPre.map g) :=
  congrArg (fun t => zLocPres.eval.map t) (Paths.lift_toPath zCutContraction.backPre g)

/-- **…which is the merge down, the cut, and the merge back up.** -/
theorem zRun_arrow_genCell {u v : GenObj (ZL).Gen} (g : u ⟶ v) (hg : ¬ Cut.merged g) :
    zRunPresentation.arrow (zCutContraction.genCell g hg)
      = zLocPres.eval.map (zCutContraction.invWord u.as)
        ≫ zLocPres.eval.map g.toPath ≫ zLocPres.eval.map (zCutContraction.word v.as) := by
  have h1 : zLocPres.E.map (zCutContraction.backQuot.map (zCutContraction.cell g))
      = zRunPresentation.arrow (zCutContraction.genCell g hg) :=
    (congrArg (fun t => zLocPres.E.map (zCutContraction.backQuot.map t))
        (zCutContraction.cell_of_not_S g hg)).trans
      ((congrArg (fun t => zLocPres.eval.map t)
          (Paths.lift_toPath zCutContraction.backPre
            (zCutContraction.genCell g hg))).trans (zRun_arrow_eq_eval _).symm)
  refine Eq.trans h1.symm (Eq.trans (congrArg (fun t => zLocPres.E.map t)
    (zCutContraction.backQuot_cell_of_not_S g hg)) ?_)
  exact (zLocPres.E.map_comp _ _).trans
    (congrArg (fun t => zLocPres.eval.map (zCutContraction.invWord u.as) ≫ t)
      (zLocPres.E.map_comp _ _))

/-- **A 1-cell of the contraction is its bead cut, conjugated by merges onto the runs of its two
ends** — any merges, since `eq_of_W` pins them. -/
theorem zRun_arrow_mk {vx vy : (ZL).V} (hvx : zCutContraction.rep vx = vx)
    (hvy : zCutContraction.rep vy = vy) {dm cd : (ZL).V} (gen : (ZL).Gen dm cd)
    (hnm : ¬ Cut.merged gen) (hrd : zCutContraction.rep dm = vx)
    (hrc : zCutContraction.rep cd = vy)
    {ma : shOf vx ⟶ shOf dm} (hma : W Zbp ma) {mb : shOf vy ⟶ shOf cd} (hmb : W Zbp mb) :
    zRunPresentation.arrow
        (⟨dm, cd, gen, hnm, hrd, hrc⟩ : zCutContraction.Gen ⟨vx, hvx⟩ ⟨vy, hvy⟩)
      = (zLocIso vx).hom ≫ (@inv _ _ _ _ _ (isIso_Q_op_of_W hma)
          ≫ (Qz).map (Cut.genHom (chFwdOf gen hnm).1).op ≫ (Qz).map mb.op)
        ≫ (zLocIso vy).inv := by
  subst hrd
  subst hrc
  rcases gen with e | ⟨e, he⟩
  case inr => exact absurd trivial hnm
  obtain rfl : ma = zRunMerge (shOf dm) := eq_of_W hma (W_zRunMerge (shOf dm))
  obtain rfl : mb = zRunMerge (shOf cd) := eq_of_W hmb (W_zRunMerge (shOf cd))
  have hmid : zLocPres.eval.map (Quiver.Hom.toPath (Polygraph.cell (P := ZL) (Sum.inl e)))
      = (zLocIso dm).hom ≫ (Qz).map (Cut.genHom e.1).op ≫ (zLocIso cd).inv :=
    (zLoc_eval_fwd (Polygraph.cell e).toPath).trans
      (congrArg (fun t : shOf cd ⟶ shOf dm => (zLocIso dm).hom
        ≫ (Qz).map (Quiver.Hom.op t) ≫ (zLocIso cd).inv) (zEltHom_toPath e))
  refine Eq.trans (zRun_arrow_genCell (Polygraph.cell (P := ZL) (Sum.inl e)) hnm) ?_
  refine Eq.trans (congrArg (fun t => zLocPres.eval.map (zCutContraction.invWord dm) ≫ t
    ≫ zLocPres.eval.map (zCutContraction.word cd)) hmid) ?_
  rw [eval_invWord_eq, eval_word_eq, zRunIso, zRunIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, mergeIso_hom, Category.assoc]
  exact conj_cancel _ _ _ _ _ _ _

/-- …stated at a 1-cell.  `zRun_arrow_mk` takes the `Gen` fields apart because `subst hrd` needs
them free: destructuring `g` first leaves `ma`'s type depending on the equation. -/
theorem zRun_arrow {x y : zCutContraction.V} (g : zCutContraction.Gen x y)
    {ma : shOf x.1 ⟶ shOf g.dom} (hma : W Zbp ma) {mb : shOf y.1 ⟶ shOf g.cod} (hmb : W Zbp mb) :
    zRunPresentation.arrow g = (zLocIso x.1).hom ≫ (@inv _ _ _ _ _ (isIso_Q_op_of_W hma)
        ≫ (Qz).map (zRunHom g).op ≫ (Qz).map mb.op) ≫ (zLocIso y.1).inv :=
  zRun_arrow_mk x.2 y.2 g.gen g.not_mem g.rep_dom g.rep_cod hma hmb

/-! ## The 0-cells are the runs

`rep x = x` says a 0-cell *is* the run on its own events, so it carries only a strand count; a
bead cut preserves that count, so every 1-cell is a loop. -/

/-- The strand count a 0-cell carries. -/
def vStrands (x : zCutContraction.V) : ℕ := dimSum (shOf x.1).dims

/-- **A 0-cell is the run on its own events.** -/
theorem shOf_eq_ones (x : zCutContraction.V) : shOf x.1 = zObj (𝟙^(vStrands x)) :=
  (congrArg (fun z : (ZP).V => shOf z) x.2).symm

/-- **A 1-cell's two ends carry the strand counts of their 0-cells.** -/
theorem vStrands_of_rep {z : (ZP).V} {x : zCutContraction.V} (h : zCutContraction.rep z = x.1) :
    dimSum (shOf z).dims = vStrands x :=
  (dimSum_replicate _).symm.trans (congrArg (fun w : (ZP).V => dimSum (shOf w).dims) h)

theorem vStrands_dom {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    dimSum (shOf g.dom).dims = vStrands x := vStrands_of_rep g.rep_dom

theorem vStrands_cod {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    dimSum (shOf g.cod).dims = vStrands y := vStrands_of_rep g.rep_cod

/-- **A 1-cell is a loop** — its bead cut preserves the strand count, so both ends have the same
run. -/
theorem eq_of_gen {x y : zCutContraction.V} (g : zCutContraction.Gen x y) : x = y := by
  have hN : vStrands x = vStrands y :=
    (vStrands_dom g).symm.trans ((dimSum_eq_of_hom (zRunHom g)).symm.trans (vStrands_cod g))
  exact Subtype.ext (zEltV_ext ((shOf_eq_ones x).trans
    ((congrArg (fun n => zObj (𝟙^n)) hN).trans (shOf_eq_ones y).symm)))

/-- The renaming of a 0-cell's shape as the run on its events. -/
noncomputable def vRunIso (x : zCutContraction.V) :
    (Qz).obj (op (zObj (𝟙^(vStrands x)))) ≅ (Qz).obj (op (shOf x.1)) :=
  mergeIso (W_eqToHom (shOf_eq_ones x))

/-- **A 0-cell names the run on its events, in `Ch(Z)[W⁻¹]`.** -/
noncomputable def runIsoAt (x : zCutContraction.V) :
    zRunPresentation.at' (zCutContraction.poly.pt x) ≅ (Qz).obj (op (zObj (𝟙^(vStrands x)))) :=
  zLocIso x.1 ≪≫ (vRunIso x).symm

/-- **A 1-cell of the contraction is the loop its crossing permutation spells at the run** — the
merges the contraction inverts are the ones `conj` inverts. -/
theorem zRun_arrow_runLoop {x : zCutContraction.V} (g : zCutContraction.Gen x x) :
    zRunPresentation.arrow g
      = (runIsoAt x).hom ≫ runLoop (vStrands x) (crossPerm (vStrands_cod g) (zRunHom g))
        ≫ (runIsoAt x).inv := by
  have hWd : W Zbp (eqToHom (shOf_eq_ones x) ≫ runMerge (shOf g.dom) (vStrands_dom g)) :=
    (W Zbp).comp_mem _ _ (W_eqToHom _) (W_runMerge _ _)
  have hWc : W Zbp (eqToHom (shOf_eq_ones x) ≫ runMerge (shOf g.cod) (vStrands_cod g)) :=
    (W Zbp).comp_mem _ _ (W_eqToHom _) (W_runMerge _ _)
  have hinvd : @inv _ _ _ _ _ (isIso_Q_op_of_W hWd) = (vRunIso x).inv
      ≫ @inv _ _ _ _ _ (isIso_Q_op_of_W (W_runMerge (shOf g.dom) (vStrands_dom g))) :=
    congrArg Iso.inv (Iso.ext ((Qz).map_comp (runMerge (shOf g.dom) (vStrands_dom g)).op
      (eqToHom (shOf_eq_ones x)).op) : mergeIso hWd
        = mergeIso (W_runMerge (shOf g.dom) (vStrands_dom g)) ≪≫ vRunIso x)
  have hfwdc : (Qz).map (eqToHom (shOf_eq_ones x) ≫ runMerge (shOf g.cod) (vStrands_cod g)).op
      = (Qz).map (runMerge (shOf g.cod) (vStrands_cod g)).op ≫ (vRunIso x).hom :=
    (Qz).map_comp (runMerge (shOf g.cod) (vStrands_cod g)).op (eqToHom (shOf_eq_ones x)).op
  have hconj : conj (vStrands_cod g) (zRunHom g)
      = @inv _ _ _ _ _ (isIso_Q_op_of_W (W_runMerge (shOf g.dom) (vStrands_dom g)))
        ≫ (Qz).map (zRunHom g).op ≫ (Qz).map (runMerge (shOf g.cod) (vStrands_cod g)).op :=
    conj_eq_of_merges (vStrands_cod g) (zRunHom g) (W_runMerge _ _) (W_runMerge _ _)
  have hmiddle : @inv _ _ _ _ _ (isIso_Q_op_of_W hWd) ≫ (Qz).map (zRunHom g).op
        ≫ (Qz).map (eqToHom (shOf_eq_ones x) ≫ runMerge (shOf g.cod) (vStrands_cod g)).op
      = (vRunIso x).inv ≫ runLoop (vStrands x) (crossPerm (vStrands_cod g) (zRunHom g))
        ≫ (vRunIso x).hom := by
    rw [hinvd, hfwdc]
    refine Eq.trans (comp_assoc₅ _ _ _ _ _).symm ?_
    exact congrArg (fun t => (vRunIso x).inv ≫ t ≫ (vRunIso x).hom)
      (hconj.symm.trans (conj_eq_runLoop (vStrands_cod g) (zRunHom g)))
  refine Eq.trans (zRun_arrow g hWd hWc) ?_
  refine Eq.trans (congrArg (fun t => (zLocIso x.1).hom ≫ t ≫ (zLocIso x.1).inv) hmiddle) ?_
  exact comp_assoc₅ _ _ _ _ _

/-! ## The atoms out of a run

A 1-cell whose bead cut *starts* at a run is an atom: `exists_atomComp` names the cell it cuts, and
only the merge and that atom land there (`eq_atomOnes`). -/

/-- Cancelling a renaming against its inverse. -/
private theorem eqToHom_cancel {C : Type*} [Category C] {X Y Z : C} (h : X = Y) (f : X ⟶ Z) :
    eqToHom h ≫ eqToHom h.symm ≫ f = f := by subst h; simp

/-- A renaming does not change the codimension — `codim` sees only the two shapes. -/
theorem codim_eqToHom_comp {K : BPSet} {a a' b : Ch K} (h : a = a') (f : a' ⟶ b) :
    codim (eqToHom h ≫ f) = codim f := by subst h; rfl

/-- **The 1-cells to keep**: those whose bead cut starts at a run. -/
def OutOfRun {x y : zCutContraction.V} (g : zCutContraction.Gen x y) : Prop :=
  zCutContraction.rep g.cod = g.cod

/-- The `k`-th atom out of the run a 0-cell names. -/
noncomputable def atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    zCutContraction.Gen x x where
  dom := zEltV (zObj (atomComp (vStrands x) k))
  cod := x.1
  gen := Sum.inl (zEltGen ⟨eqToHom (shOf_eq_ones x) ≫ atomOnes (vStrands x) k,
    (codim_eqToHom_comp _ _).trans (codim_atomOnes (vStrands x) k)⟩)
  not_mem := fun hm => not_W_atomOnes (vStrands x) k
    (W_of_comp_right _ _ ((merge_iff _).mp hm).1)
  rep_dom := zEltV_ext ((congrArg (fun n => zObj (𝟙^n)) (dimSum_atomComp (vStrands x) k)).trans
    (shOf_eq_ones x).symm)
  rep_cod := x.2

theorem outOfRun_atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    OutOfRun (atomCell x k) := x.2

/-- **The `k`-th atom crosses the `k`-th pair.** -/
theorem crossPerm_atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    crossPerm (vStrands_cod (atomCell x k)) (zRunHom (atomCell x k)) = adjT k := by
  refine Eq.trans (crossPerm_comp _ (eqToHom (shOf_eq_ones x)) (atomOnes (vStrands x) k)) ?_
  rw [crossPerm_eq_one_of_W _ (W_eqToHom (shOf_eq_ones x)), mul_one]
  exact crossPerm_atomOnes (vStrands x) k

/-- **A kept 1-cell names the atom loop it cuts.** -/
theorem arrow_atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    zRunPresentation.arrow (atomCell x k)
      = (runIsoAt x).hom ≫ atomLoop (vStrands x) k ≫ (runIsoAt x).inv := by
  rw [zRun_arrow_runLoop, crossPerm_atomCell, runLoop_adjT]

/-- **A kept 1-cell is one of the `N−1` atoms** — the cut lands on an atom's cell
(`exists_atomComp`) and is not the merge there (`eq_atomOnes`). -/
theorem exists_atomCell {x : zCutContraction.V} (g : zCutContraction.Gen x x)
    (hg : OutOfRun g) : ∃ k : Fin (vStrands x - 1), atomCell x k = g := by
  obtain ⟨vx, hvx⟩ := x
  obtain ⟨dm, cd, gen, hnm, hrd, hrc⟩ := g
  obtain rfl : cd = vx := hg.symm.trans hrc
  rcases gen with e | ⟨e, he⟩
  case inr => exact absurd trivial hnm
  set N := vStrands (⟨cd, hvx⟩ : zCutContraction.V) with hN
  have hsh : shOf cd = zObj (𝟙^N) := shOf_eq_ones ⟨cd, hvx⟩
  obtain ⟨k, hk⟩ := _root_.ChainCat.exists_atomComp (eqToHom hsh.symm ≫ e.1.1)
    ((codim_eqToHom_comp _ _).trans e.1.2)
  obtain rfl : dm = zEltV (zObj (atomComp N k)) := zEltV_ext hk
  have hatom : eqToHom hsh.symm ≫ e.1.1 = atomOnes N k :=
    eq_atomOnes fun hW => hnm ((merge_iff _).mpr ⟨W_of_comp_right _ _ hW, e.1.2⟩)
  have hc1 : codim (eqToHom hsh ≫ atomOnes N k) = 1 :=
    (codim_eqToHom_comp _ _).trans (codim_atomOnes _ _)
  have hval : eqToHom hsh ≫ atomOnes N k = e.1.1 :=
    (congrArg (fun t => eqToHom hsh ≫ t) hatom).symm.trans (eqToHom_cancel hsh e.1.1)
  refine ⟨k, ?_⟩
  obtain rfl : e = zEltGen (⟨eqToHom hsh ≫ atomOnes N k, hc1⟩ : Cut.Refine _ _) :=
    Subtype.ext (Subtype.ext hval.symm)
  rfl

/-- **The kept 1-cells at a 0-cell are its `N−1` atoms.** -/
noncomputable def keptEquiv (x : zCutContraction.V) :
    Fin (vStrands x - 1) ≃ keptGen (P := zCutContraction.poly) OutOfRun x x :=
  Equiv.ofBijective (fun k => ⟨atomCell x k, outOfRun_atomCell x k⟩)
    ⟨fun i j hij => Fin.ext (by
        by_contra hne
        have hdom : zObj (atomComp (vStrands x) i) = zObj (atomComp (vStrands x) j) :=
          congrArg (fun g : keptGen (P := zCutContraction.poly) OutOfRun x x => shOf g.1.dom) hij
        exact atomComp_ne hne hdom),
      fun g => by
        obtain ⟨k, hk⟩ := exists_atomCell g.1 g.2
        exact ⟨k, Subtype.ext hk⟩⟩

/-- The `k`-th atom, as a kept 1-cell. -/
noncomputable def atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    (⟨x⟩ : GenObj (keptGen (P := zCutContraction.poly) OutOfRun)) ⟶ ⟨x⟩ := keptEquiv x k

@[simp] theorem keptPre_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    (keptPre (P := zCutContraction.poly) OutOfRun).map (atomGen x k) = atomCell x k := rfl

end ChainCat
