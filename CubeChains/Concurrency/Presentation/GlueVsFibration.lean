import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/GlueVsFibration — the two presentations of `Ch(K)[W⁻¹]`, compared

The glue route names one 0-cell per **run of `K`** (`covered_iff_isRun`) and one 1-cell per
*witnessed* crossing — a run-step read inside a chain.  The fibration route names one 0-cell
per element of the fibre over the run and one 1-cell per base generator acting on it.  At
`K = Hbp □ⁿ` the fibre is the runs, so the 0-cells agree (`coveredVEquivPerm`).

What a 1-cell *does* is read by `chBraid`, the positive braid an arrow performs in the localized
base.  The projection there is **faithful** (`faithful_chLocBase`, `eq_of_chBraid_eq`), so a
parallel pair performing one braid is one arrow — which is how a generator dictionary gets
checked.  Both routes' generators perform the same atom: `chBraid_glueSliceEval_runStep` on the
glue side, `chBraid_hLocArtinPresentation_arrow` on the fibration side.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

/-- **The objects of `Ch K` the copies name are exactly the runs.**  A copy contributes only runs,
and a run is a run over itself. -/
theorem covered_iff_isRun (K : BPSet) (v : GlueV (wedgeHoms K)) :
    Covered (wedgeHoms K) runLabels v ↔ IsRun Zbp v.1 := by
  constructor
  · rintro ⟨s, a, rfl⟩
    exact a.2
  · intro hv
    refine ⟨v, ⟨Over.mk (𝟙 v.1), hv⟩, ?_⟩
    simp only [gluePt, runLabels, Over.mk_left, Over.mk_hom, CategoryStruct.id]
    rfl

/-! ## The braid an arrow performs

`posGrade` reads a refinement's crossing permutation as a Garside simple and inverts the merges, so
it descends to `Ch(K)[W⁻¹]` along the projection to the base — with no hypothesis on `K`, and with
its value on a `Q`-image forced.  It is what says a 1-cell names an *atom*. -/

section Braid

variable (K : BPSet)

theorem eltBraid_inverts :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).IsInvertedBy
      ((CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ posGrade) :=
  fun _ _ _ hf => posGrade_inverts _ hf

/-- **The positive braid an arrow of `Ch(K)[W⁻¹]` performs** — `posGrade`, descended along the
projection to the base. -/
noncomputable def eltBraid :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization ⥤
      FullPosBraid :=
  Localization.Construction.lift _ (eltBraid_inverts K)

theorem eltBraid_fac :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q ⋙ eltBraid K
      = (CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ posGrade :=
  Localization.Construction.fac _ _

/-- The braid a slice performs. -/
noncomputable def overBraid (d : Ch Zbp) : ((W Zbp).over (X := d)).Localization ⥤ FullPosBraid :=
  Localization.Construction.lift (Over.forget d ⋙ posGrade) fun _ _ _ hf => posGrade_inverts _ hf

/-- **A slice's braid is the ambient one.**  The cartesian lift is a section of the projection
(`elementsLift_comp_π`, an equality on the nose), so the two descents agree — no comparison iso, and
in particular a 1-cell's braid may be read in its own slice. -/
theorem glueSliceEval_comp_eltBraid (d : Ch Zbp) (x : (wedgeHoms K).obj (op d)) :
    glueSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltBraid K = overBraid d :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, eltBraid_fac, ← Functor.assoc,
      elementsLift_comp_π]
    exact (Localization.Construction.fac _ _).symm)

end Braid

/-! ## At the decorated cube: the 0-cells are the fibre

`Hbp □ⁿ` puts every chain at `n` strands, so a covered 0-cell is *the* run shape and its data is a
map out of `⋁1ⁿ` — the fibre over the run, which is what the fibration route's 0-cells are. -/

/-- **Every 0-cell of the glued polygraph of `Hbp □ⁿ` sits at the run.** -/
theorem covered_eq_run (n : ℕ) {v : GlueV (wedgeHoms (Hbp.obj (□n)))}
    (hv : Covered (wedgeHoms (Hbp.obj (□n))) runLabels v) : v.1 = zObj (𝟙^n) := by
  have hrun := (covered_iff_isRun (Hbp.obj (□n)) v).mp hv
  refine Obj.eq_of_dims ?_
  rw [zObj_dims, eq_replicate_of_ones hrun,
    ← dimSum_eq_length_of_ones hrun, hbpCubeStrands v.2]

/-- The 0-cell a map out of the run names. -/
def runToCoveredV (n : ℕ) (x : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    CoveredV (wedgeHoms (Hbp.obj (□n))) runLabels :=
  ⟨⟨zObj (𝟙^n), x⟩, (covered_iff_isRun _ _).mpr fun _ hd => List.eq_of_mem_replicate hd⟩

theorem bijective_runToCoveredV (n : ℕ) : Function.Bijective (runToCoveredV n) := by
  constructor
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
  · rintro ⟨⟨d, x⟩, hv⟩
    obtain rfl : d = zObj (𝟙^n) := covered_eq_run n hv
    exact ⟨x, rfl⟩

/-- **The 0-cells of the two presentations agree**: the glued polygraph's are the runs of `Hbp □ⁿ`,
which are the `n!` orderings of the axes — the fibre the fibration route indexes its 0-cells by. -/
noncomputable def coveredVEquivPerm (n : ℕ) :
    CoveredV (wedgeHoms (Hbp.obj (□n))) runLabels ≃ Equiv.Perm (Fin n) :=
  (Equiv.ofBijective _ (bijective_runToCoveredV n)).symm.trans (runFibreEquiv n)

/-! ## The 1-cells

A 1-cell of the glued polygraph is a `RunStep` inside a chain.  Two readings of it: what it
*is* — an adjacent transposition of the source run, absorbed by a merge from the target — and what
it *names* in the localized slice, which thinness pins with nothing chosen. -/

/-- **A 1-cell of the glued polygraph is an adjacent transposition.**  `RunStep` asks for one
crossing; a permutation with one inversion is an `adjT`. -/
theorem runStep_exists_adjT {d : Ch Zbp} {a b : RunOver d} (h : RunStep a b) :
    ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d)
      (k : Fin (dimSum a.1.left.dims - 1)),
      crossPerm rfl t = adjT k ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom := by
  obtain ⟨e, t, m, z, ht, hm, hta, hmb⟩ := h
  obtain ⟨k, hk⟩ := eq_adjT_of_permLen_eq_one ht
  exact ⟨e, t, m, z, k, hk, hm, hta, hmb⟩

/-- **What a 1-cell names**: cross the pair, then undo the merge.  The localized slice is a poset,
so this is *the* arrow, not a choice of one. -/
theorem runSlicePresentation_arrow {d : Ch Zbp} {a b : RunOver d} (h : PLift (RunStep a b))
    {e : Ch Zbp} {t : a.1.left ⟶ e} {m : b.1.left ⟶ e} {z : e ⟶ d}
    (hm : W Zbp m) (hta : t ≫ z = a.1.hom) (hmb : m ≫ z = b.1.hom) :
    haveI : IsIso (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
      Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _ hm
    (runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z) ≫
        inv (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
  Subsingleton.elim _ _

theorem overBraid_Q {d : Ch Zbp} {y y' : Over d} (f : y ⟶ y') :
    (overBraid d).map (((W Zbp).over (X := d)).Q.map f) = posGrade.map f.left :=
  Category.id_comp _

/-- **The braid a 1-cell performs**: cross the one pair, then undo the merge.  With
`runStep_exists_adjT` — the crossing is an `adjT` — this says a 1-cell of the glued polygraph names
an **atom** of the braid monoid, which is what the fibration route's generators are. -/
theorem overBraid_runStep {d : Ch Zbp} {a b : RunOver d} (h : PLift (RunStep a b))
    {e : Ch Zbp} {t : a.1.left ⟶ e} {m : b.1.left ⟶ e} {z : e ⟶ d}
    (hm : W Zbp m) (hta : t ≫ z = a.1.hom) (hmb : m ≫ z = b.1.hom) :
    (overBraid d).map ((runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩))
        ≫ posGrade.map m = posGrade.map t := by
  haveI : IsIso (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
    Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _ hm
  have h1 : (overBraid d).map
      (((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z)) = posGrade.map t :=
    overBraid_Q _
  have h2 : (overBraid d).map
      (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) = posGrade.map m :=
    overBraid_Q _
  have key : (runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)
        ≫ ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z) := by
    rw [runSlicePresentation_arrow h hm hta hmb]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun w => ((W Zbp).over (X := d)).Q.map
      (Over.homMk t hta : a.1 ⟶ Over.mk z) ≫ w)
      (IsIso.inv_hom_id (((W Zbp).over (X := d)).Q.map
        (Over.homMk m hmb : b.1 ⟶ Over.mk z)))).trans ?_
    exact Category.comp_id _
  have step : (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)) ≫ posGrade.map m
      = (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩) ≫
        ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
    (congrArg (fun w => (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)) ≫ w) h2.symm).trans
      ((overBraid d).map_comp _ _).symm
  rw [step, key]
  exact h1


/-! ## The base a localized chain lies over

`Ch K` is the category of elements of `wedgeHoms K`, so a localized chain still remembers the
localized base it lies over, and it remembers it *faithfully*: the projection of a category of
elements is faithful, and localizing `Ch K` only localizes the base
(`isLocalization_chDescent`). -/

section BaseProjection

open CategoryTheory.Localization

/-- The descent of a presheaf's elements projects to the base — `pre`, transported. -/
theorem preOf_comp_π {B : Type*} [Category B] (W : MorphismProperty B) {P : B ⥤ Type}
    {Pd : W.Localization ⥤ Type} (h : W.Q ⋙ Pd = P) :
    Localization.preOf W h ⋙ CategoryOfElements.π Pd = CategoryOfElements.π P ⋙ W.Q := by
  subst h; rfl

/-- **An isomorphism of the localized base performs nothing** — `PosBraid N` has no non-trivial
units. -/
theorem homEquivPosBraid_eq_one_of_isIso {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (f : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op b))
    (hf : IsIso f) : homEquivPosBraid ha hb f = 1 := by
  haveI := hf
  have h : homEquivPosBraid ha hb f * homEquivPosBraid hb ha (inv f) = 1 := by
    rw [← homEquivPosBraid_comp ha hb ha, IsIso.hom_inv_id, homEquivPosBraid_id]
  exact eq_one_of_mul_eq_one h

/-- **Conjugating by isomorphisms does not change the braid**, in the shape the comparison
functors produce: a pair of isomorphisms outside and a pair inside.  The `IsIso` witnesses are
explicit — the object spellings a comparison functor produces are not the ones instance search
matches. -/
theorem homEquivPosBraid_conj5 {N : ℕ} {a b a' b' a'' b'' : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (ha' : dimSum a'.dims = N) (hb' : dimSum b'.dims = N)
    (ha'' : dimSum a''.dims = N) (hb'' : dimSum b''.dims = N)
    (c₁ : ((W Zbp).op).Q.obj (op a) ⟶ ((W Zbp).op).Q.obj (op a')) (hc₁ : IsIso c₁)
    (d₁ : ((W Zbp).op).Q.obj (op a') ⟶ ((W Zbp).op).Q.obj (op a'')) (hd₁ : IsIso d₁)
    (f : ((W Zbp).op).Q.obj (op a'') ⟶ ((W Zbp).op).Q.obj (op b''))
    (d₂ : ((W Zbp).op).Q.obj (op b'') ⟶ ((W Zbp).op).Q.obj (op b')) (hd₂ : IsIso d₂)
    (c₂ : ((W Zbp).op).Q.obj (op b') ⟶ ((W Zbp).op).Q.obj (op b)) (hc₂ : IsIso c₂) :
    homEquivPosBraid ha hb (c₁ ≫ (d₁ ≫ f ≫ d₂) ≫ c₂) = homEquivPosBraid ha'' hb'' f := by
  haveI := hc₁; haveI := hd₁; haveI := hd₂; haveI := hc₂
  rw [homEquivPosBraid_comp ha ha' hb, homEquivPosBraid_comp ha' hb' hb,
    homEquivPosBraid_comp ha' ha'' hb', homEquivPosBraid_comp ha'' hb'' hb',
    homEquivPosBraid_eq_one_of_isIso ha ha' c₁ hc₁,
    homEquivPosBraid_eq_one_of_isIso ha' ha'' d₁ hd₁,
    homEquivPosBraid_eq_one_of_isIso hb'' hb' d₂ hd₂,
    homEquivPosBraid_eq_one_of_isIso hb' hb c₂ hc₂,
    mul_one, one_mul, mul_one, one_mul]

variable (K : BPSet)

/-- A chain of `K`, read in the localized base. -/
noncomputable abbrev chBaseRaw : Ch K ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  toElements K ⋙ (CategoryOfElements.π (wedgeHoms K) ⋙ ((W Zbp).op).Q).op

theorem chBaseRaw_inverts : (W K).IsInvertedBy (chBaseRaw K) := by
  intro a b f hf
  rw [W_eq_inverseImage_toElements K] at hf
  haveI : IsIso ((((W Zbp).op).Q).map ((CategoryOfElements.π (wedgeHoms K)).map
      ((toElements K).map f).unop)) :=
    Localization.inverts ((W Zbp).op).Q ((W Zbp).op) _ hf
  exact inferInstanceAs (IsIso (Quiver.Hom.op ((((W Zbp).op).Q).map
    ((CategoryOfElements.π (wedgeHoms K)).map ((toElements K).map f).unop))))

/-- **The localized chains, projected to the localized base.** -/
noncomputable def chLocBase : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  Localization.Construction.lift (chBaseRaw K) (chBaseRaw_inverts K)

theorem chLocBase_fac : (W K).Q ⋙ chLocBase K = chBaseRaw K :=
  Localization.Construction.fac _ _

theorem chLocBase_map_Q {a b : Ch K} (f : a ⟶ b) :
    (chLocBase K).map ((W K).Q.map f) = (chBaseRaw K).map f :=
  Category.id_comp _

variable (hS : IsSegal K.toPsh)

/-- The descent of `Ch K` to the localized base is the projection it already was. -/
theorem chDescent_comp_π :
    chDescent K hS ⋙ (CategoryOfElements.π (wedgeHomsDescend K hS)).op = chBaseRaw K :=
  congrArg (fun F : (wedgeHoms K).Elements ⥤ ((W Zbp).op).Localization => toElements K ⋙ F.op)
    (preOf_comp_π ((W Zbp).op)
      (Localization.Construction.fac (wedgeHoms K) (invertsMerges_of_isSegal K hS)))

/-- The base projection, read through the descent equivalence — where it is manifestly
faithful. -/
noncomputable def chLocBaseModel : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent K hS
  (Localization.equivalenceFromModel (chDescent K hS) (W K)).functor ⋙
    (CategoryOfElements.π (wedgeHomsDescend K hS)).op

/-- **The two readings of the projection agree** — both lift `chBaseRaw` through the
localization. -/
noncomputable def chLocBaseModelIso : chLocBase K ≅ chLocBaseModel K hS :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent K hS
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K) (chLocBaseModel K hS) :=
    ⟨Functor.isoWhiskerRight
      (Localization.qCompEquivalenceFromModelFunctorIso (chDescent K hS) (W K))
      ((CategoryOfElements.π (wedgeHomsDescend K hS)).op) ≪≫
      eqToIso (chDescent_comp_π K hS)⟩
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K) (chLocBase K) :=
    ⟨eqToIso (chLocBase_fac K)⟩
  Localization.liftNatIso (W K).Q (W K) (chBaseRaw K) (chBaseRaw K) _ _ (Iso.refl _)

include hS in
/-- **A localized chain remembers its base faithfully** — `Ch K` is a category of elements and
localizing it only localizes the base, so the projection stays faithful. -/
theorem faithful_chLocBase : (chLocBase K).Faithful :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent K hS
  haveI : (chLocBaseModel K hS).Faithful :=
    inferInstanceAs ((Localization.equivalenceFromModel (chDescent K hS) (W K)).functor ⋙
      (CategoryOfElements.π (wedgeHomsDescend K hS)).op).Faithful
  Functor.Faithful.of_iso (chLocBaseModelIso K hS).symm

/-! ### The braid an arrow performs, read in the base

Every hom-set of the localized base is `PosBraid N` (`homEquivPosBraid`), so the faithful
projection turns an arrow of `Ch(K)[W⁻¹]` into a positive braid — and two parallel arrows
performing the same braid are equal. -/

variable {K}

/-- The chain a localized object is — the localization construction keeps the objects. -/
noncomputable abbrev chOf {K : BPSet} (X : (W K).Localization) : Ch K :=
  (Localization.Construction.objEquiv (W K)).symm X

/-- The base chain a localized-base object is. -/
noncomputable abbrev zOf (X : ((W Zbp).op).Localization) : Ch Zbp :=
  ((Localization.Construction.objEquiv ((W Zbp).op)).symm X).unop

/-- **The positive braid an arrow of `Ch(K)[W⁻¹]` performs.**  The arrow comes first: it pins the
two objects, and the strand counts are then checked against them. -/
noncomputable def chBraid {N : ℕ} {X Y : (W K).Localization} (f : X ⟶ Y)
    (hX : dimSum (chOf X).dims = N) (hY : dimSum (chOf Y).dims = N) : PosBraid N :=
  homEquivPosBraid (a := zObj (chOf Y).dims) (b := zObj (chOf X).dims) hY hX
    ((chLocBase K).map f).unop

/-- **A refinement performs its crossing permutation.** -/
theorem chBraid_Q {N : ℕ} {a b : Ch K} (f : a ⟶ b) (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) : chBraid ((W K).Q.map f) ha hb = posPerm (crossPerm ha f) := by
  rw [chBraid, chLocBase_map_Q]
  exact (homEquivPosBraid_Q (a := zObj a.dims) (b := zObj b.dims) ha hb (zHom f.φ)).trans
    (congrArg posPerm (crossPerm_zHom ha f))

/-- **Composition multiplies, in the concurrency order** — the later arrow's braid first. -/
theorem chBraid_comp {N : ℕ} {X Y Z : (W K).Localization} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : dimSum (chOf X).dims = N) (hY : dimSum (chOf Y).dims = N)
    (hZ : dimSum (chOf Z).dims = N) :
    chBraid (f ≫ g) hX hZ = chBraid g hY hZ * chBraid f hX hY := by
  rw [chBraid, chBraid, chBraid, (chLocBase K).map_comp]
  exact homEquivPosBraid_comp hZ hY hX _ _

@[simp] theorem chBraid_id {N : ℕ} {X : (W K).Localization} (hX : dimSum (chOf X).dims = N) :
    chBraid (𝟙 X) hX hX = 1 := by
  rw [chBraid, CategoryTheory.Functor.map_id]
  exact homEquivPosBraid_id hX

/-- **An isomorphism performs nothing** — `PosBraid N` has no non-trivial units. -/
theorem chBraid_eq_one_of_isIso {N : ℕ} {X Y : (W K).Localization} (f : X ⟶ Y) [IsIso f]
    (hX : dimSum (chOf X).dims = N) (hY : dimSum (chOf Y).dims = N) : chBraid f hX hY = 1 := by
  have h : chBraid f hX hY * chBraid (inv f) hY hX = 1 := by
    rw [← chBraid_comp (inv f) f hY hX hY, IsIso.inv_hom_id, chBraid_id]
  exact eq_one_of_mul_eq_one h

include hS in
/-- **A parallel pair performing the same braid is one arrow** — faithfulness of the projection,
read through `homEquivPosBraid`. -/
theorem eq_of_chBraid_eq {N : ℕ} {X Y : (W K).Localization} {f g : X ⟶ Y}
    (hX : dimSum (chOf X).dims = N) (hY : dimSum (chOf Y).dims = N)
    (h : chBraid f hX hY = chBraid g hX hY) : f = g :=
  haveI := faithful_chLocBase K hS
  (chLocBase K).map_injective (Quiver.Hom.unop_inj
    ((homEquivPosBraid (a := zObj (chOf Y).dims) (b := zObj (chOf X).dims) hY hX).injective h))

/-! ### The projection, read through the fibre over the run

`chLocEquivElements` reads `Ch K[W⁻¹]` as the elements of the fibre over the run; projecting those
back to the base is the very same functor, so a *fibration-route* arrow's braid may be read off the
base generator it carries. -/

section Fibre

variable (K : BPSet) (N : ℕ) (hS : IsSegal K.toPsh)
  (hK : ∀ {d : List ℕ+}, (⋁d ⟶ K) → dimSum d = N)

/-- The base projection, read through the fibre over the run. -/
noncomputable def chLocBaseElt : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  (chLocEquivElements K N hS hK).functor ⋙
    (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
      CategoryOfElements.π (wedgeHomsDescend K hS)).op

/-- **…and it is the projection.**  `pre` is inverted and re-applied, so only its counit is
left. -/
noncomputable def chLocBaseEltIso : chLocBase K ≅ chLocBaseElt K N hS hK :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (cover_of_strands K N hS hK)
  chLocBaseModelIso K hS ≪≫
    Functor.isoWhiskerLeft (Localization.equivalenceFromModel (chDescent K hS) (W K)).functor
      (NatIso.op (Functor.isoWhiskerRight
        (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).asEquivalence.counitIso
        (CategoryOfElements.π (wedgeHomsDescend K hS))))

/-- **The two readings of an arrow, conjugated** — the naturality of a comparison, read on the
base rather than on its opposite. -/
theorem chLocBase_map_unop {K : BPSet}
    {G : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ} (α : chLocBase K ≅ G)
    {X Y : (W K).Localization} (g : X ⟶ Y) :
    ((chLocBase K).map g).unop
      = (α.inv.app Y).unop ≫ (G.map g).unop ≫ (α.hom.app X).unop := by
  conv_lhs => rw [← NatIso.naturality_2 α g]
  rw [unop_comp, unop_comp, Category.assoc]

/-- **The braid a fibration-route arrow performs is the base generator it carries.**  An arrow of
the fibre's category of elements is a braid acting on a run; read back in `Ch(K)[W⁻¹]` it performs
exactly that braid, the two comparison isomorphisms contributing nothing
(`homEquivPosBraid_eq_one_of_isIso`). -/
theorem chBraid_chLocEquivElements_inverse_map
    {A B : (runBase N ⋙ wedgeHomsDescend K hS).Elements} (ψ : A ⟶ B)
    (hB : dimSum (chOf ((chLocEquivElements K N hS hK).inverse.obj (op B))).dims = N)
    (hA : dimSum (chOf ((chLocEquivElements K N hS hK).inverse.obj (op A))).dims = N) :
    chBraid ((chLocEquivElements K N hS hK).inverse.map ψ.op) hB hA
      = homEquivPosBraid (dimSum_replicate N) (dimSum_replicate N) ((runBase N).map ψ.val) := by
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (cover_of_strands K N hS hK)
  haveI hinv : ∀ Z, IsIso ((chLocBaseEltIso K N hS hK).inv.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocBaseEltIso K N hS hK).app Z).unop).inv)
  haveI hhom : ∀ Z, IsIso ((chLocBaseEltIso K N hS hK).hom.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocBaseEltIso K N hS hK).app Z).unop).hom)
  haveI hcinv : ∀ Z, IsIso ((chLocEquivElements K N hS hK).counitIso.inv.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocEquivElements K N hS hK).counitIso.app Z).unop).inv)
  haveI hchom : ∀ Z, IsIso ((chLocEquivElements K N hS hK).counitIso.hom.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocEquivElements K N hS hK).counitIso.app Z).unop).hom)
  have hcounit : (chLocEquivElements K N hS hK).functor.map
        ((chLocEquivElements K N hS hK).inverse.map ψ.op)
      = (chLocEquivElements K N hS hK).counitIso.hom.app (op B) ≫ ψ.op ≫
        (chLocEquivElements K N hS hK).counitIso.inv.app (op A) :=
    (NatIso.naturality_2 (chLocEquivElements K N hS hK).counitIso ψ.op).symm
  have hmain : ((chLocBaseElt K N hS hK).map
        ((chLocEquivElements K N hS hK).inverse.map ψ.op)).unop
      = (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
            CategoryOfElements.π (wedgeHomsDescend K hS)).map
          ((chLocEquivElements K N hS hK).counitIso.inv.app (op A)).unop ≫
        (runBase N).map ψ.val ≫
        (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
            CategoryOfElements.π (wedgeHomsDescend K hS)).map
          ((chLocEquivElements K N hS hK).counitIso.hom.app (op B)).unop := by
    have h1 : ((chLocEquivElements K N hS hK).functor.map
          ((chLocEquivElements K N hS hK).inverse.map ψ.op)).unop
        = ((chLocEquivElements K N hS hK).counitIso.inv.app (op A)).unop ≫ ψ ≫
          ((chLocEquivElements K N hS hK).counitIso.hom.app (op B)).unop := by
      rw [hcounit]; simp
    have h2 := (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
        CategoryOfElements.π (wedgeHomsDescend K hS)).map_comp
      ((chLocEquivElements K N hS hK).counitIso.inv.app (op A)).unop
      (ψ ≫ ((chLocEquivElements K N hS hK).counitIso.hom.app (op B)).unop)
    have h3 := (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
        CategoryOfElements.π (wedgeHomsDescend K hS)).map_comp
      ψ ((chLocEquivElements K N hS hK).counitIso.hom.app (op B)).unop
    change (CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
      CategoryOfElements.π (wedgeHomsDescend K hS)).map
      (((chLocEquivElements K N hS hK).functor.map
        ((chLocEquivElements K N hS hK).inverse.map ψ.op)).unop) = _
    rw [h1]
    exact h2.trans (congrArg (CategoryStruct.comp _) h3)
  haveI := hcinv (op A)
  haveI := hchom (op B)
  have hd₁ : IsIso ((CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
      CategoryOfElements.π (wedgeHomsDescend K hS)).map
      ((chLocEquivElements K N hS hK).counitIso.inv.app (op A)).unop) := inferInstance
  have hd₂ : IsIso ((CategoryOfElements.pre (wedgeHomsDescend K hS) (runBase N) ⋙
      CategoryOfElements.π (wedgeHomsDescend K hS)).map
      ((chLocEquivElements K N hS hK).counitIso.hom.app (op B)).unop) := inferInstance
  rw [chBraid, chLocBase_map_unop (chLocBaseEltIso K N hS hK), hmain]
  exact homEquivPosBraid_conj5 hA hB (dimSum_replicate N) (dimSum_replicate N)
    (dimSum_replicate N) (dimSum_replicate N) _ (hinv _) _ hd₁ _ _ hd₂ _ (hhom _)

end Fibre

/-! ### At the decorated cube: a fibration-route generator names its atom -/

section ArtinGenerator

/-- The merge out of the run into itself is the identity. -/
theorem runArrow_ones (N : ℕ) : runArrow (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ := by
  rw [runArrow, show runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ from endo_eq_id _, op_id]
  exact CategoryTheory.Functor.map_id _ _

theorem inv_runArrow_ones (N : ℕ) :
    inv (runArrow (zObj (𝟙^N)) (dimSum_replicate N)) = 𝟙 _ :=
  IsIso.inv_eq_of_hom_inv_id (by rw [Category.comp_id, runArrow_ones])

/-- **A loop at the run performs its own crossing permutation** — nothing to conjugate. -/
theorem homEquivPosBraid_runLoop (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    homEquivPosBraid (dimSum_replicate N) (dimSum_replicate N) (runLoop N σ) = posPerm σ := by
  rw [homEquivPosBraid_apply, inv_runArrow_ones, runArrow_ones, Category.id_comp, Category.comp_id]
  exact runGrade_runLoop N σ

/-- Every chain of the decorated cube has `n` strands. -/
theorem hbpStrands {n : ℕ} (c : Ch (Hbp.obj (□n))) : dimSum c.dims = n := hbpCubeStrands c.map

/-- **The braid the `k`-th Artin generator names is the `k`-th atom.**  The fibration route's
1-cells are the base's generators acting on the fibre, and the base generator `k` is `posPerm
(adjT k)` on the nose; nothing in the transport to `Ch(Hbp □ⁿ)[W⁻¹]` disturbs it. -/
theorem chBraid_hLocArtinPresentation_arrow (n : ℕ) {x y : GenObj (hLocArtinPoly n).Gen}
    (e : x ⟶ y) :
    chBraid ((hLocArtinPresentation n).arrow e).unop
        (hbpStrands (chOf ((hLocArtinPresentation n).at' y).unop))
        (hbpStrands (chOf ((hLocArtinPresentation n).at' x).unop))
      = posPerm (adjT e.1) :=
  (chBraid_chLocEquivElements_inverse_map (Hbp.obj (□n)) n
      (isSegal_H_of_symFree_repr (symFreeCube n)) (fun {_} α => hbpCubeStrands α)
      (((artinComponent n).elements
        (runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
          (isSegal_H_of_symFree_repr (symFreeCube n)))).arrow e)
      (hbpStrands _) (hbpStrands _)).trans
    (homEquivPosBraid_runLoop n (adjT e.1))

end ArtinGenerator

/-! ### The projection, read through the glued slices

The glue route reads `Ch(K)[W⁻¹]` as the localized category of elements and each 1-cell inside a
localized slice.  Both steps project to the localized base on the nose — `elementsLift_comp_π` is
an equality — so a *glue-route* arrow's braid is read in its own slice. -/

section GlueSide

variable (K : BPSet)

/-- A chain of the base, read in the localized base. -/
noncomputable abbrev zBase : Ch Zbp ⥤ (((W Zbp).op).Localization)ᵒᵖ := ((W Zbp).op).Q.rightOp

/-- The elements of `wedgeHoms K`, read in the localized base. -/
noncomputable abbrev eltBaseRaw : ((wedgeHoms K).Elements)ᵒᵖ ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  (CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ zBase

theorem eltBaseRaw_inverts :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).IsInvertedBy
      (eltBaseRaw K) := by
  intro a b f hf
  haveI : IsIso ((((W Zbp).op).Q).map
      (((CategoryOfElements.π (wedgeHoms K)).leftOp.map f).op)) :=
    Localization.inverts ((W Zbp).op).Q ((W Zbp).op) _ hf
  exact inferInstanceAs (IsIso (Quiver.Hom.op ((((W Zbp).op).Q).map
    (((CategoryOfElements.π (wedgeHoms K)).leftOp.map f).op))))

/-- The localized elements, projected to the localized base. -/
noncomputable def eltLocBase :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization ⥤
      (((W Zbp).op).Localization)ᵒᵖ :=
  Localization.Construction.lift (eltBaseRaw K) (eltBaseRaw_inverts K)

theorem eltLocBase_fac :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q ⋙ eltLocBase K
      = eltBaseRaw K :=
  Localization.Construction.fac _ _

/-- The localized slice over a chain of the base, projected to the localized base. -/
noncomputable def overLocBase (d : Ch Zbp) :
    ((W Zbp).over (X := d)).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ :=
  Localization.Construction.lift (Over.forget d ⋙ zBase) (by
    intro y y' f hf
    haveI : IsIso ((((W Zbp).op).Q).map (f.left.op)) :=
      Localization.inverts ((W Zbp).op).Q ((W Zbp).op) _ hf
    exact inferInstanceAs (IsIso (Quiver.Hom.op ((((W Zbp).op).Q).map (f.left.op)))))

theorem overLocBase_map_Q {d : Ch Zbp} {y y' : Over d} (f : y ⟶ y') :
    (overLocBase d).map (((W Zbp).over (X := d)).Q.map f) = zBase.map f.left :=
  Category.id_comp _

/-- **A slice's projection is the ambient one.**  The cartesian lift is a section of the projection
(`elementsLift_comp_π`), so the two descents agree on the nose. -/
theorem glueSliceEval_comp_eltLocBase (d : Ch Zbp) (x : (wedgeHoms K).obj (op d)) :
    glueSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltLocBase K = overLocBase d :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, eltLocBase_fac, ← Functor.assoc,
      elementsLift_comp_π]
    exact (Localization.Construction.fac _ _).symm)

/-- **The two readings of the projection agree** — both lift `chBaseRaw` through the
localization. -/
noncomputable def chLocBaseGlueIso :
    chLocBase K ≅ (locEquivElements K).functor ⋙ eltLocBase K :=
  haveI : (toElements K ⋙
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q).IsLocalization (W K) :=
    Functor.IsLocalization.of_inverseImage (toElements K) _ _ (W K)
      (W_eq_inverseImage_elements K)
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K)
      ((locEquivElements K).functor ⋙ eltLocBase K) :=
    ⟨Functor.isoWhiskerRight
      (Localization.compUniqFunctor (W K).Q
        (toElements K ⋙ ((W Zbp).inverseImage
          (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)) (eltLocBase K) ≪≫
      eqToIso (congrArg (fun F => toElements K ⋙ F) (eltLocBase_fac K))⟩
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K) (chLocBase K) :=
    ⟨eqToIso (chLocBase_fac K)⟩
  Localization.liftNatIso (W K).Q (W K) (chBaseRaw K) (chBaseRaw K) _ _ (Iso.refl _)

/-- **The braid a glue-route arrow performs is the one it performs on the elements.**  The
comparison with the localized category of elements is invisible to the braid. -/
theorem chBraid_locEquivElements_inverse_map {N : ℕ}
    {A B : ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization}
    (φ : A ⟶ B)
    (hA : dimSum (chOf ((locEquivElements K).inverse.obj A)).dims = N)
    (hB : dimSum (chOf ((locEquivElements K).inverse.obj B)).dims = N)
    (hA' : dimSum (zOf ((eltLocBase K).obj A).unop).dims = N)
    (hB' : dimSum (zOf ((eltLocBase K).obj B).unop).dims = N) :
    chBraid ((locEquivElements K).inverse.map φ) hA hB
      = homEquivPosBraid hB' hA' (((eltLocBase K).map φ).unop) := by
  haveI hinv : ∀ Z, IsIso ((chLocBaseGlueIso K).inv.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocBaseGlueIso K).app Z).unop).inv)
  haveI hhom : ∀ Z, IsIso ((chLocBaseGlueIso K).hom.app Z).unop := fun Z =>
    inferInstanceAs (IsIso (((chLocBaseGlueIso K).app Z).unop).hom)
  haveI hcinv : ∀ Z, IsIso ((locEquivElements K).counitIso.inv.app Z) := fun Z =>
    inferInstanceAs (IsIso ((locEquivElements K).counitIso.app Z).inv)
  haveI hchom : ∀ Z, IsIso ((locEquivElements K).counitIso.hom.app Z) := fun Z =>
    inferInstanceAs (IsIso ((locEquivElements K).counitIso.app Z).hom)
  have hcounit : (locEquivElements K).functor.map ((locEquivElements K).inverse.map φ)
      = (locEquivElements K).counitIso.hom.app A ≫ φ ≫
        (locEquivElements K).counitIso.inv.app B :=
    (NatIso.naturality_2 (locEquivElements K).counitIso φ).symm
  have hmain : (((locEquivElements K).functor ⋙ eltLocBase K).map
        ((locEquivElements K).inverse.map φ)).unop
      = ((eltLocBase K).map ((locEquivElements K).counitIso.inv.app B)).unop ≫
        ((eltLocBase K).map φ).unop ≫
        ((eltLocBase K).map ((locEquivElements K).counitIso.hom.app A)).unop := by
    have h2 := (eltLocBase K).map_comp ((locEquivElements K).counitIso.hom.app A)
      (φ ≫ (locEquivElements K).counitIso.inv.app B)
    have h3 := (eltLocBase K).map_comp φ ((locEquivElements K).counitIso.inv.app B)
    have h5 : ((locEquivElements K).functor ⋙ eltLocBase K).map
          ((locEquivElements K).inverse.map φ)
        = (eltLocBase K).map ((locEquivElements K).counitIso.hom.app A) ≫
          (eltLocBase K).map φ ≫
          (eltLocBase K).map ((locEquivElements K).counitIso.inv.app B) := by
      change (eltLocBase K).map ((locEquivElements K).functor.map
        ((locEquivElements K).inverse.map φ)) = _
      rw [hcounit]
      exact h2.trans (congrArg (CategoryStruct.comp _) h3)
    rw [h5]
    refine unop_comp.trans ?_
    refine (congrArg (fun s => s ≫ ((eltLocBase K).map
      ((locEquivElements K).counitIso.hom.app A)).unop) unop_comp).trans ?_
    exact Category.assoc _ _ _
  have hd₁ : IsIso (((eltLocBase K).map
      ((locEquivElements K).counitIso.inv.app B)).unop) := inferInstance
  have hd₂ : IsIso (((eltLocBase K).map
      ((locEquivElements K).counitIso.hom.app A)).unop) := inferInstance
  rw [chBraid, chLocBase_map_unop (chLocBaseGlueIso K), hmain]
  exact homEquivPosBraid_conj5 hB hA
    (strandsEq_loc (((chLocBaseGlueIso K).inv.app
      ((locEquivElements K).inverse.obj B)).unop) |>.trans hB)
    ((strandsEq_loc (((chLocBaseGlueIso K).hom.app
      ((locEquivElements K).inverse.obj A)).unop)).symm.trans hA)
    hB' hA' _ (hinv _) _ hd₁ _ _ hd₂ _ (hhom _)

/-- A slice 1-cell, projected: the cartesian lift is a section of the projection, so both descents
read a `Q`-image off the arrow underneath. -/
theorem glueSliceEval_eltLocBase_map_Q (d : Ch Zbp) (x : (wedgeHoms K).obj (op d))
    {y y' : Over d} (f : y ⟶ y') :
    (eltLocBase K).map ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map
      (((W Zbp).over (X := d)).Q.map f)) = zBase.map f.left := by
  have h1 : (glueSliceEval (wedgeHoms K) (W Zbp) d x).map (((W Zbp).over (X := d)).Q.map f)
      = ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.map
        ((elementsLift (wedgeHoms K) d x).map f) := Category.id_comp _
  have h2 : (eltLocBase K).map (((W Zbp).inverseImage
        (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.map
        ((elementsLift (wedgeHoms K) d x).map f))
      = (eltBaseRaw K).map ((elementsLift (wedgeHoms K) d x).map f) := Category.id_comp _
  exact (congrArg (eltLocBase K).map h1).trans h2

/-- **The braid a glue-route 1-cell performs in `Ch(K)[W⁻¹]` is the atom it crosses**: cross the
pair, then undo the merge, which performs nothing.  Both comparisons — the localized elements and
the cartesian lift of the slice — are invisible to the braid, so a 1-cell's braid may be read in
its own slice. -/
theorem chBraid_glueSliceEval_runStep {N : ℕ} (d : Ch Zbp) (x : (wedgeHoms K).obj (op d))
    {a b : RunOver d} (h : PLift (RunStep a b)) {e : Ch Zbp} {t : a.1.left ⟶ e}
    {m : b.1.left ⟶ e} {z : e ⟶ d} (hm : W Zbp m) (hta : t ≫ z = a.1.hom)
    (hmb : m ≫ z = b.1.hom)
    (ha : dimSum a.1.left.dims = N) (hb : dimSum b.1.left.dims = N) (he : dimSum e.dims = N)
    (hA : dimSum (chOf ((locEquivElements K).inverse.obj
      ((glueSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (Localization.Construction.objEquiv ((W Zbp).over (X := d)) a.1)))).dims = N)
    (hB : dimSum (chOf ((locEquivElements K).inverse.obj
      ((glueSliceEval (wedgeHoms K) (W Zbp) d x).obj
        (Localization.Construction.objEquiv ((W Zbp).over (X := d)) b.1)))).dims = N) :
    chBraid ((locEquivElements K).inverse.map ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map
        ((runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))) hA hB
      = posPerm (crossPerm ha t) := by
  refine (chBraid_locEquivElements_inverse_map K _ hA hB ha hb).trans ?_
  have hkey : (runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩) ≫
      ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z) :=
    Subsingleton.elim _ _
  have hstep : (eltLocBase K).map ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map
        ((runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))
        ≫ zBase.map m = zBase.map t :=
    (congrArg (fun s => (eltLocBase K).map ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map
        ((runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩))) ≫ s)
      (glueSliceEval_eltLocBase_map_Q K d x (Over.homMk m hmb : b.1 ⟶ Over.mk z)).symm).trans
      ((((glueSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltLocBase K).map_comp _ _).symm.trans
        (congrArg (fun s => (eltLocBase K).map
          ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map s)) hkey)).trans
        (glueSliceEval_eltLocBase_map_Q K d x (Over.homMk t hta : a.1 ⟶ Over.mk z)))
  have hu : (zBase.map m).unop ≫ ((eltLocBase K).map
        ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map ((runSlicePresentation d).arrow
          (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))).unop = (zBase.map t).unop :=
    unop_comp.symm.trans (congrArg Quiver.Hom.unop hstep)
  have h3 : homEquivPosBraid he hb ((zBase.map m).unop) = 1 :=
    (homEquivPosBraid_Q hb he m).trans
      (by rw [crossPerm_eq_one_of_W hb hm, posPerm_one])
  calc homEquivPosBraid hb ha (((eltLocBase K).map
          ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map ((runSlicePresentation d).arrow
            (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))).unop)
      = 1 * homEquivPosBraid hb ha (((eltLocBase K).map
          ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map ((runSlicePresentation d).arrow
            (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))).unop) := (one_mul _).symm
    _ = homEquivPosBraid he hb ((zBase.map m).unop) *
          homEquivPosBraid hb ha (((eltLocBase K).map
            ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map ((runSlicePresentation d).arrow
              (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))).unop) := by rw [h3]
    _ = homEquivPosBraid he ha ((zBase.map m).unop ≫ ((eltLocBase K).map
          ((glueSliceEval (wedgeHoms K) (W Zbp) d x).map ((runSlicePresentation d).arrow
            (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)))).unop) :=
        (homEquivPosBraid_comp he hb ha _ _).symm
    _ = posPerm (crossPerm ha t) :=
        (congrArg (homEquivPosBraid he ha) hu).trans (homEquivPosBraid_Q ha he t)

end GlueSide

end BaseProjection

end ChainCat
