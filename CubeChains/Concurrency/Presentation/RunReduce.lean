import CubeChains.Concurrency.Presentation.RunContract
import CubeChains.Concurrency.Presentation.Retraction
import CubeChains.Machinery.Presentation.Reduce

/-!
# Concurrency/Presentation/RunReduce — a bead cut at a run is a braid loop

    ⟨bead cuts | codim-2 cells⟩ ──invert merges──▸ ──contract──▸ ⟨cuts at a run | those cells⟩

A 0-cell of the contraction *is* the run on its own events (`zSh_eq_ones`), so a bead cut out of it
is a loop, and `zRun_arrow_runLoop` reads that loop off its crossing permutation alone.  The cuts
that start at a run are exactly the `N−1` atoms (`keptEquiv`), each naming `atomLoop`.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

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
abbrev zSh (z : (chCutPoly Zbp).V) : Ch Zbp := z.1

/-- A 0-cell of the lifted polygraph is its shape. -/
theorem zEltV_ext {z z' : (chCutPoly Zbp).V} (h : zSh z = zSh z') : z = z' := by
  obtain ⟨d, m⟩ := z
  obtain ⟨d', m'⟩ := z'
  subst h
  exact congrArg _ (Subsingleton.elim m m')

/-- The 0-cell a shape names. -/
def zEltV (d : Ch Zbp) : (chCutPoly Zbp).V := ⟨d, default⟩

/-- A bead cut, acting on the unique element over its shape. -/
def zEltGen {z z' : (chCutPoly Zbp).V} (e : Cut.Refine (zSh z) (zSh z')) :
    (chCutPoly Zbp).Gen z z' := ⟨e, Subsingleton.elim _ _⟩

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
noncomputable abbrev zEltPres : Presents (chCutPoly Zbp) ((Ch Zbp)ᵒᵖ) :=
  chPresentation Zbp zCutPresentation

/-- …and the merges among its 1-cells. -/
abbrev zEltPicked : ∀ {a b : (chCutPoly Zbp).V}, (chCutPoly Zbp).Gen a b → Prop :=
  chPicked zCutPresentation Cut.mergeGen Zbp

theorem W_op_eq_zEltPicked :
    (W Zbp).op = (zEltPres.pickedArrows zEltPicked).multiplicativeClosure :=
  multiplicativeClosure_chPicked zCutPresentation Cut.mergeGen
    (by rw [pickedArrows_mergeGen, ← MorphismProperty.multiplicativeClosure_op]; rfl) Zbp

/-- The generating quiver of the lifted polygraph, over the bead cuts. -/
abbrev zEltProj : GenObj (zCutPresentation.elementsGen (wedgeHoms Zbp)) ⥤q GenObj Cut.Refine :=
  zCutPresentation.elementsProj (wedgeHoms Zbp)

/-- **The refinement a word of the lifted polygraph performs** — the bead cuts it projects to,
evaluated. -/
noncomputable def zEltHom {z z' : (chCutPoly Zbp).V}
    (u : Quiver.Path ((chCutPoly Zbp).pt z) ((chCutPoly Zbp).pt z')) : zSh z' ⟶ zSh z :=
  Cut.ev (zEltProj.mapPath u)

@[simp] theorem zEltHom_toPath {z z' : (chCutPoly Zbp).V} (e : (chCutPoly Zbp).Gen z z') :
    zEltHom (Polygraph.cell e).toPath = Cut.genHom e.1 := Category.comp_id _

/-! ## A 0-cell is the shape it names

The element a 0-cell carries *is* the classifying map of its shape, so the comparison is the
identity wedge map — no transport survives into the reading of a word. -/

/-- The shape a 0-cell names, in the opposite where the cut presentation lives. -/
def zEltObjIso (z : (chCutPoly Zbp).V) : zEltPres.at' ((chCutPoly Zbp).pt z) ≅ op (zSh z) :=
  Iso.op (X := zSh z) (Y := (⟨(zSh z).dims, z.2⟩ : Ch Zbp))
    { hom := ⟨𝟙 _, Subsingleton.elim _ _⟩
      inv := ⟨𝟙 _, Subsingleton.elim _ _⟩
      hom_inv_id := hom_ext' (Category.comp_id _)
      inv_hom_id := hom_ext' (Category.comp_id _) }

/-- **A word of the lifted polygraph performs the refinement it projects to** — the fibre being a
point, the only comparison is the renaming of its two ends. -/
theorem zEltPres_eval_map {z z' : (chCutPoly Zbp).V}
    (u : Quiver.Path ((chCutPoly Zbp).pt z) ((chCutPoly Zbp).pt z')) :
    zEltPres.eval.map u = (zEltObjIso z).hom ≫ (zEltHom u).op ≫ (zEltObjIso z').inv := by
  have hval : ((zCutPresentation.elements (wedgeHoms Zbp)).eval.map u).val = (zEltHom u).op :=
    zCutPresentation.elements_eval_val (wedgeHoms Zbp) u
  have hr : Hom.φ (((zEltObjIso z).hom ≫ (zEltHom u).op ≫ (zEltObjIso z').inv).unop)
      = Hom.φ (zEltHom u) := by
    change 𝟙 _ ≫ Hom.φ (zEltHom u) ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
  have hl : Hom.φ ((zEltPres.eval.map u).unop) = Hom.φ (zEltHom u) := by
    change Hom.φ (homOfRestrict ((zCutPresentation.elements (wedgeHoms Zbp)).eval.map u).val.unop
      ((zCutPresentation.elements (wedgeHoms Zbp)).eval.map u).property) = _
    rw [homOfRestrict_φ, hval]
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
noncomputable abbrev zLocPres :
    Presents (invPoly (chCutPoly Zbp) zEltPicked) (((W Zbp).op).Localization) :=
  zEltPres.presentsLocalization zEltPicked W_op_eq_zEltPicked

/-- The shape a 0-cell names, in `Ch(Z)[W⁻¹]`. -/
noncomputable def zLocIso (z : (chCutPoly Zbp).V) :
    zLocPres.at' ((invPoly (chCutPoly Zbp) zEltPicked).pt z)
      ≅ ((W Zbp).op).Q.obj (op (zSh z)) :=
  (zEltPres.locComparison zEltPicked W_op_eq_zEltPicked).app ⟨(chCutPoly Zbp).pt z⟩
    ≪≫ ((W Zbp).op).Q.mapIso (zEltObjIso z)

/-- **A forward word performs the refinement it projects to.** -/
theorem zLoc_eval_fwd {z z' : (chCutPoly Zbp).V}
    (u : Quiver.Path ((chCutPoly Zbp).pt z) ((chCutPoly Zbp).pt z')) :
    zLocPres.eval.map ((fwdPre (chCutPoly Zbp) zEltPicked).mapPath u)
      = (zLocIso z).hom ≫ ((W Zbp).op).Q.map (zEltHom u).op ≫ (zLocIso z').inv := by
  have hQ : ((W Zbp).op).Q.map (zEltPres.eval.map u)
      = ((W Zbp).op).Q.map (zEltObjIso z).hom
        ≫ (((W Zbp).op).Q.map (zEltHom u).op ≫ ((W Zbp).op).Q.map (zEltObjIso z').inv) :=
    (congrArg ((W Zbp).op).Q.map (zEltPres_eval_map u)).trans
      ((((W Zbp).op).Q.map_comp _ _).trans
        (congrArg (fun t => ((W Zbp).op).Q.map (zEltObjIso z).hom ≫ t)
          (((W Zbp).op).Q.map_comp _ _)))
  refine Eq.trans (zEltPres.eval_fwd_mapPath zEltPicked W_op_eq_zEltPicked u) ?_
  refine Eq.trans (congrArg (fun t =>
      ((zEltPres.locComparison zEltPicked W_op_eq_zEltPicked).app
          (⟨(chCutPoly Zbp).pt z⟩ : (chCutPoly Zbp).presented)).hom ≫ t
        ≫ ((zEltPres.locComparison zEltPicked W_op_eq_zEltPicked).app
          (⟨(chCutPoly Zbp).pt z'⟩ : (chCutPoly Zbp).presented)).inv) hQ) ?_
  exact comp_assoc₅ _ _ _ _ _

/-! ## The merge onto the run

`Machinery/Presentation/Localize`'s cancellation 2-cells make the merge word invertible, and
`zLoc_eval_fwd` says which arrow it is. -/

/-- A renaming of chains is a merge — `W K` contains the identities. -/
theorem W_eqToHom {K : BPSet} {a b : Ch K} (h : a = b) : W K (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact MorphismProperty.id_mem _ _

/-- **A merge is invertible in `Ch(Z)[W⁻¹]`** — the only comparison the reading of a word needs. -/
noncomputable def mergeIso {a b : Ch Zbp} {m : a ⟶ b} (hm : W Zbp m) :
    ((W Zbp).op).Q.obj (op b) ≅ ((W Zbp).op).Q.obj (op a) :=
  @asIso _ _ _ _ (((W Zbp).op).Q.map m.op) (isIso_Q_op_of_W hm)

@[simp] theorem mergeIso_hom {a b : Ch Zbp} {m : a ⟶ b} (hm : W Zbp m) :
    (mergeIso hm).hom = ((W Zbp).op).Q.map m.op := rfl

/-- **The conjugated loop, from any pair of merges onto the run** — `eq_of_W` pins both, so no
choice of merge is involved. -/
theorem conj_eq_of_merges {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b)
    {ma : zObj (𝟙^N) ⟶ a} (hma : W Zbp ma) {mb : zObj (𝟙^N) ⟶ b} (hmb : W Zbp mb) :
    conj ha f = @inv _ _ _ _ _ (isIso_Q_op_of_W hmb) ≫ ((W Zbp).op).Q.map f.op
      ≫ ((W Zbp).op).Q.map ma.op := by
  obtain rfl : ma = runMerge a ha := eq_runMerge ha hma
  obtain rfl : mb = runMerge b (tgtStrands f ha) := eq_runMerge (tgtStrands f ha) hmb
  rfl

/-- **The merge word onto a 0-cell's run performs that merge.** -/
theorem zEltHom_eltRunWord (z : (chCutPoly Zbp).V) :
    zEltHom (eltRunWord z) = zRunMerge (zSh z) := by
  have h : zEltHom (eltRunWord z) = Cut.ev (runCutWord (zSh z)) :=
    congrArg (fun p => Cut.ev p) (elementsProj_eltRunWord z)
  exact h.trans (ev_runCutWord (zSh z))

/-- …conjugated onto the 0-cells of the presentation. -/
noncomputable def zRunIso (z : (chCutPoly Zbp).V) :
    zLocPres.at' ((invPoly (chCutPoly Zbp) zEltPicked).pt z)
      ≅ zLocPres.at' ((invPoly (chCutPoly Zbp) zEltPicked).pt (eltRep z)) :=
  zLocIso z ≪≫ mergeIso (W_zRunMerge (zSh z)) ≪≫ (zLocIso (eltRep z)).symm

/-- **The contraction's merge word is that merge.** -/
theorem eval_word_eq (z : (chCutPoly Zbp).V) :
    zLocPres.eval.map (zCutContraction.word z) = (zRunIso z).hom :=
  (zLoc_eval_fwd (eltRunWord z)).trans
    (congrArg (fun t : zSh (eltRep z) ⟶ zSh z => (zLocIso z).hom
      ≫ ((W Zbp).op).Q.map (Quiver.Hom.op t) ≫ (zLocIso (eltRep z)).inv)
      (zEltHom_eltRunWord z))

/-- **…and its inverse word is the inverse** — the cancellation 2-cells, read in the
localization. -/
theorem eval_invWord_eq (z : (chCutPoly Zbp).V) :
    zLocPres.eval.map (zCutContraction.invWord z) = (zRunIso z).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← eval_word_eq]
  exact zEltPres.eval_fwd_comp_invWord zEltPicked W_op_eq_zEltPicked (eltRunWord z)
    (all_eltRunWord z)

/-! ## A 1-cell of the contraction, read in `Ch(Z)[W⁻¹]`

A 1-cell is a *forward* bead cut — a formal inverse is merged, hence contracted away — and the
contraction reads it conjugated by the merges onto the runs of its two ends. -/

/-- The bead cut an unmerged 1-cell of the extension is. -/
def Cut.fwdOf {a b : (chCutPoly Zbp).V} :
    ∀ g : InvGen (chCutPoly Zbp) zEltPicked a b, ¬ Cut.merged g → (chCutPoly Zbp).Gen a b
  | .inl e, _ => e
  | .inr _, h => absurd trivial h

/-- The bead cut a 1-cell of the contraction performs, as a refinement of `Ch Zbp`. -/
def zRunHom {x y : zCutContraction.V} (g : zCutContraction.Gen x y) : zSh g.cod ⟶ zSh g.dom :=
  Cut.genHom (Cut.fwdOf g.gen g.not_mem).1

/-- **A 1-cell is the word the contraction conjugates it to.** -/
theorem zRun_arrow_eq_eval {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    zRunPresentation.arrow g = zLocPres.eval.map (zCutContraction.backPre.map g) :=
  congrArg (fun t => zLocPres.eval.map t) (Paths.lift_toPath zCutContraction.backPre g)

/-- **…which is the merge down, the cut, and the merge back up.** -/
theorem zRun_arrow_genCell {u v : GenObj (chCutLocFunctor.obj Zbp).Gen} (g : u ⟶ v)
    (hg : ¬ Cut.merged g) :
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
theorem zRun_arrow_mk {vx vy : (chCutLocFunctor.obj Zbp).V}
    (hvx : zCutContraction.rep vx = vx) (hvy : zCutContraction.rep vy = vy)
    {dm cd : (chCutLocFunctor.obj Zbp).V} (gen : (chCutLocFunctor.obj Zbp).Gen dm cd)
    (hnm : ¬ Cut.merged gen) (hrd : zCutContraction.rep dm = vx)
    (hrc : zCutContraction.rep cd = vy)
    {ma : zSh vx ⟶ zSh dm} (hma : W Zbp ma) {mb : zSh vy ⟶ zSh cd} (hmb : W Zbp mb) :
    zRunPresentation.arrow
        (⟨dm, cd, gen, hnm, hrd, hrc⟩ : zCutContraction.Gen ⟨vx, hvx⟩ ⟨vy, hvy⟩)
      = (zLocIso vx).hom ≫ (@inv _ _ _ _ _ (isIso_Q_op_of_W hma)
          ≫ ((W Zbp).op).Q.map (Cut.genHom (Cut.fwdOf gen hnm).1).op
          ≫ ((W Zbp).op).Q.map mb.op) ≫ (zLocIso vy).inv := by
  subst hrd
  subst hrc
  rcases gen with e | ⟨e, he⟩
  case inr => exact absurd trivial hnm
  obtain rfl : ma = zRunMerge (zSh dm) := eq_of_W hma (W_zRunMerge (zSh dm))
  obtain rfl : mb = zRunMerge (zSh cd) := eq_of_W hmb (W_zRunMerge (zSh cd))
  have hmid : zLocPres.eval.map
        (Quiver.Hom.toPath (Polygraph.cell (P := chCutLocFunctor.obj Zbp) (Sum.inl e)))
      = (zLocIso dm).hom ≫ ((W Zbp).op).Q.map (Cut.genHom e.1).op ≫ (zLocIso cd).inv :=
    (zLoc_eval_fwd (Polygraph.cell e).toPath).trans
      (congrArg (fun t : zSh cd ⟶ zSh dm => (zLocIso dm).hom
        ≫ ((W Zbp).op).Q.map (Quiver.Hom.op t) ≫ (zLocIso cd).inv) (zEltHom_toPath e))
  refine Eq.trans (zRun_arrow_genCell
    (Polygraph.cell (P := chCutLocFunctor.obj Zbp) (Sum.inl e)) hnm) ?_
  refine Eq.trans (congrArg (fun t => zLocPres.eval.map (zCutContraction.invWord dm) ≫ t
    ≫ zLocPres.eval.map (zCutContraction.word cd)) hmid) ?_
  rw [eval_invWord_eq, eval_word_eq, zRunIso, zRunIso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, mergeIso_hom,
    Category.assoc]
  exact conj_cancel _ _ _ _ _ _ _

/-- …stated at a 1-cell.  `zRun_arrow_mk` takes the `Gen` fields apart because `subst hrd` needs
them free: destructuring `g` first leaves `ma`'s type depending on the equation. -/
theorem zRun_arrow {x y : zCutContraction.V} (g : zCutContraction.Gen x y)
    {ma : zSh x.1 ⟶ zSh g.dom} (hma : W Zbp ma) {mb : zSh y.1 ⟶ zSh g.cod} (hmb : W Zbp mb) :
    zRunPresentation.arrow g
      = (zLocIso x.1).hom ≫ (@inv _ _ _ _ _ (isIso_Q_op_of_W hma)
          ≫ ((W Zbp).op).Q.map (zRunHom g).op ≫ ((W Zbp).op).Q.map mb.op)
        ≫ (zLocIso y.1).inv :=
  zRun_arrow_mk x.2 y.2 g.gen g.not_mem g.rep_dom g.rep_cod hma hmb

/-! ## The 0-cells are the runs

`rep x = x` says a 0-cell *is* the run on its own events, so it carries only a strand count; a
bead cut preserves that count, so every 1-cell is a loop. -/

/-- The strand count a 0-cell carries. -/
def vStrands (x : zCutContraction.V) : ℕ := dimSum (zSh x.1).dims

/-- **A 0-cell is the run on its own events.** -/
theorem zSh_eq_ones (x : zCutContraction.V) : zSh x.1 = zObj (𝟙^(vStrands x)) :=
  (congrArg (fun z : (chCutPoly Zbp).V => zSh z) x.2).symm

/-- **A 1-cell's source carries the strand count of its 0-cell.** -/
theorem vStrands_dom {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    dimSum (zSh g.dom).dims = vStrands x :=
  (dimSum_replicate _).symm.trans
    (congrArg (fun z : (chCutPoly Zbp).V => dimSum (zSh z).dims) g.rep_dom)

/-- …and so does its target. -/
theorem vStrands_cod {x y : zCutContraction.V} (g : zCutContraction.Gen x y) :
    dimSum (zSh g.cod).dims = vStrands y :=
  (dimSum_replicate _).symm.trans
    (congrArg (fun z : (chCutPoly Zbp).V => dimSum (zSh z).dims) g.rep_cod)

/-- **A 1-cell is a loop** — its bead cut preserves the strand count, so both ends have the same
run. -/
theorem eq_of_gen {x y : zCutContraction.V} (g : zCutContraction.Gen x y) : x = y := by
  have hN : vStrands x = vStrands y :=
    (vStrands_dom g).symm.trans ((dimSum_eq_of_hom (zRunHom g)).symm.trans (vStrands_cod g))
  exact Subtype.ext (zEltV_ext ((zSh_eq_ones x).trans
    ((congrArg (fun n => zObj (𝟙^n)) hN).trans (zSh_eq_ones y).symm)))

/-- The renaming of a 0-cell's shape as the run on its events. -/
noncomputable def vRunIso (x : zCutContraction.V) :
    ((W Zbp).op).Q.obj (op (zObj (𝟙^(vStrands x)))) ≅ ((W Zbp).op).Q.obj (op (zSh x.1)) :=
  mergeIso (W_eqToHom (zSh_eq_ones x))

/-- **A 0-cell names the run on its events, in `Ch(Z)[W⁻¹]`.** -/
noncomputable def runIsoAt (x : zCutContraction.V) :
    zRunPresentation.at' (zCutContraction.poly.pt x)
      ≅ ((W Zbp).op).Q.obj (op (zObj (𝟙^(vStrands x)))) :=
  zLocIso x.1 ≪≫ (vRunIso x).symm

/-- **A 1-cell of the contraction is the loop its crossing permutation spells at the run** — the
merges the contraction inverts are the ones `conj` inverts. -/
theorem zRun_arrow_runLoop {x : zCutContraction.V} (g : zCutContraction.Gen x x) :
    zRunPresentation.arrow g
      = (runIsoAt x).hom ≫ runLoop (vStrands x) (crossPerm (vStrands_cod g) (zRunHom g))
        ≫ (runIsoAt x).inv := by
  have hWd : W Zbp (eqToHom (zSh_eq_ones x) ≫ runMerge (zSh g.dom) (vStrands_dom g)) :=
    (W Zbp).comp_mem _ _ (W_eqToHom _) (W_runMerge _ _)
  have hWc : W Zbp (eqToHom (zSh_eq_ones x) ≫ runMerge (zSh g.cod) (vStrands_cod g)) :=
    (W Zbp).comp_mem _ _ (W_eqToHom _) (W_runMerge _ _)
  have hmd : mergeIso hWd
      = mergeIso (W_runMerge (zSh g.dom) (vStrands_dom g)) ≪≫ vRunIso x :=
    Iso.ext (((W Zbp).op).Q.map_comp (runMerge (zSh g.dom) (vStrands_dom g)).op
      (eqToHom (zSh_eq_ones x)).op)
  have hinvd : @inv _ _ _ _ _ (isIso_Q_op_of_W hWd)
      = (vRunIso x).inv
        ≫ @inv _ _ _ _ _ (isIso_Q_op_of_W (W_runMerge (zSh g.dom) (vStrands_dom g))) :=
    congrArg Iso.inv hmd
  have hfwdc : ((W Zbp).op).Q.map
        (eqToHom (zSh_eq_ones x) ≫ runMerge (zSh g.cod) (vStrands_cod g)).op
      = ((W Zbp).op).Q.map (runMerge (zSh g.cod) (vStrands_cod g)).op ≫ (vRunIso x).hom :=
    ((W Zbp).op).Q.map_comp (runMerge (zSh g.cod) (vStrands_cod g)).op
      (eqToHom (zSh_eq_ones x)).op
  have hconj : conj (vStrands_cod g) (zRunHom g)
      = @inv _ _ _ _ _ (isIso_Q_op_of_W (W_runMerge (zSh g.dom) (vStrands_dom g)))
        ≫ ((W Zbp).op).Q.map (zRunHom g).op
        ≫ ((W Zbp).op).Q.map (runMerge (zSh g.cod) (vStrands_cod g)).op :=
    conj_eq_of_merges (vStrands_cod g) (zRunHom g) (W_runMerge _ _) (W_runMerge _ _)
  have hmiddle : @inv _ _ _ _ _ (isIso_Q_op_of_W hWd) ≫ ((W Zbp).op).Q.map (zRunHom g).op
        ≫ ((W Zbp).op).Q.map
            (eqToHom (zSh_eq_ones x) ≫ runMerge (zSh g.cod) (vStrands_cod g)).op
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
  gen := Sum.inl (zEltGen ⟨eqToHom (zSh_eq_ones x) ≫ atomOnes (vStrands x) k,
    (codim_eqToHom_comp _ _).trans (codim_atomOnes (vStrands x) k)⟩)
  not_mem := fun hm => not_W_atomOnes (vStrands x) k
    (W_of_comp_right _ _ ((merge_iff _).mp hm).1)
  rep_dom := zEltV_ext ((congrArg (fun n => zObj (𝟙^n)) (dimSum_atomComp (vStrands x) k)).trans
    (zSh_eq_ones x).symm)
  rep_cod := x.2

theorem outOfRun_atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    OutOfRun (atomCell x k) := x.2

/-- **The `k`-th atom crosses the `k`-th pair.** -/
theorem crossPerm_atomCell (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    crossPerm (vStrands_cod (atomCell x k)) (zRunHom (atomCell x k)) = adjT k := by
  refine Eq.trans (crossPerm_comp _ (eqToHom (zSh_eq_ones x)) (atomOnes (vStrands x) k)) ?_
  rw [crossPerm_eq_one_of_W _ (W_eqToHom (zSh_eq_ones x)), mul_one]
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
  have hsh : zSh cd = zObj (𝟙^(vStrands (⟨cd, hvx⟩ : zCutContraction.V))) :=
    zSh_eq_ones ⟨cd, hvx⟩
  obtain ⟨k, hk⟩ := _root_.ChainCat.exists_atomComp (eqToHom hsh.symm ≫ e.1.1)
    ((codim_eqToHom_comp _ _).trans e.1.2)
  obtain rfl : dm = zEltV (zObj (atomComp (vStrands (⟨cd, hvx⟩ : zCutContraction.V)) k)) :=
    zEltV_ext hk
  have hnotW : ¬ W Zbp (eqToHom hsh.symm ≫ e.1.1) := fun hW =>
    hnm ((merge_iff _).mpr ⟨W_of_comp_right _ _ hW, e.1.2⟩)
  have hatom : eqToHom hsh.symm ≫ e.1.1
      = atomOnes (vStrands (⟨cd, hvx⟩ : zCutContraction.V)) k := eq_atomOnes hnotW
  have hc1 : codim (eqToHom hsh ≫ atomOnes (vStrands (⟨cd, hvx⟩ : zCutContraction.V)) k) = 1 :=
    (codim_eqToHom_comp _ _).trans (codim_atomOnes _ _)
  have hval : eqToHom hsh ≫ atomOnes (vStrands (⟨cd, hvx⟩ : zCutContraction.V)) k = e.1.1 :=
    (congrArg (fun t => eqToHom hsh ≫ t) hatom).symm.trans (eqToHom_cancel hsh e.1.1)
  refine ⟨k, ?_⟩
  have hr : e = zEltGen (⟨eqToHom hsh
      ≫ atomOnes (vStrands (⟨cd, hvx⟩ : zCutContraction.V)) k, hc1⟩ : Cut.Refine _ _) :=
    Subtype.ext (Subtype.ext hval.symm)
  subst hr
  rfl

/-- **The kept 1-cells at a 0-cell are its `N−1` atoms.** -/
noncomputable def keptEquiv (x : zCutContraction.V) :
    Fin (vStrands x - 1) ≃ keptGen (P := zCutContraction.poly) OutOfRun x x :=
  Equiv.ofBijective (fun k => ⟨atomCell x k, outOfRun_atomCell x k⟩)
    ⟨fun i j hij => Fin.ext (by
        by_contra hne
        have hdom : zObj (atomComp (vStrands x) i) = zObj (atomComp (vStrands x) j) :=
          congrArg (fun g : keptGen (P := zCutContraction.poly) OutOfRun x x => zSh g.1.dom) hij
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
