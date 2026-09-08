import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Merge.TotalMerge
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Machinery/Localization/ElementsKan — the elements of a Kan extension are not the localization

`elementsKan α : ∫F ⥤ ∫G` compares the elements of a presheaf with those of an extension of it
along `L`, and it inverts whatever `L` inverts.  It is not a localization.  At a representable
`F = よc` — where `∫F` is the slice `C/c` and `∫(Lan よc)` is `D/(L c)` — essential surjectivity
says every arrow into `L c` is an arrow of `C` up to isomorphism, a calculus-of-fractions demand.
`Ch Zbp` fails it at the square: the atom loop `σ` of `PosBraid 2` is an endomorphism of `[2]` that
no refinement performs, because a refinement of two strands crosses at most once.  What sees this
is `crossGrading`, the Coxeter length of `crossPerm` — additive, and vanishing exactly on `W`, so
unlike `codim` it survives the localization.
-/

universe w v u u'

open CategoryTheory Opposite

namespace CategoryTheory

section Comparison

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D] {L : C ⥤ D}
  {F : Cᵒᵖ ⥤ Type w} {G : Dᵒᵖ ⥤ Type w}

/-- The comparison over `L`: an element of `F` becomes an element of `G` at the image object. -/
def elementsKan (α : F ⟶ L.op ⋙ G) : F.Elements ⥤ G.Elements :=
  CategoryOfElements.map α ⋙ CategoryOfElements.pre G L.op

@[simp] theorem elementsKan_obj (α : F ⟶ L.op ⋙ G) (p : F.Elements) :
    (elementsKan α).obj p = ⟨op (L.obj p.1.unop), α.app p.1 p.2⟩ := rfl

@[simp] theorem elementsKan_map_val (α : F ⟶ L.op ⋙ G) {p q : F.Elements} (f : p ⟶ q) :
    ((elementsKan α).map f).val = (L.map f.val.unop).op := rfl

/-- **The comparison inverts whatever the base does**: a morphism of a category of elements is
invertible as soon as the morphism it lies over is. -/
theorem elementsKan_inverts (α : F ⟶ L.op ⋙ G) (W : MorphismProperty C)
    (hL : W.IsInvertedBy L) :
    (W.op.inverseImage (CategoryOfElements.π F)).IsInvertedBy (elementsKan α) := by
  intro p q f hf
  have h1 : IsIso (L.map f.val.unop) := hL _ hf
  have h2 : IsIso ((elementsKan α).map f).val := by
    rw [elementsKan_map_val]
    exact @isIso_op _ _ _ _ _ h1
  exact @CategoryOfElements.isIso_of_isIso_val _ _ _ _ _ _ h2

end Comparison

section Slice

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]

/-- **Every arrow into `L c` is an arrow of `C` up to an isomorphism of its source** — essential
surjectivity of `Over.post L : Over c ⥤ Over (L.obj c)`, written out. -/
def SliceEssSurj (L : C ⥤ D) (c : C) : Prop :=
  ∀ ⦃d : D⦄ (ψ : d ⟶ L.obj c),
    ∃ (a : C) (v : d ⟶ L.obj a) (u : a ⟶ c), IsIso v ∧ v ≫ L.map u = ψ

variable {L : C ⥤ D} {F : Cᵒᵖ ⥤ Type v} {G : Dᵒᵖ ⥤ Type v}

/-- **At a representable the comparison is the slice comparison.**  `Lan` of a representable is a
representable (mathlib's `yonedaMap` instance), so an object of `∫(Lan よc)` over `d` is an arrow
`d ⟶ L c`, and it is hit only by the arrows of `C` into `c`. -/
theorem sliceEssSurj_of_essSurj {c : C} (i : F ≅ yoneda.obj c) (α : F ⟶ L.op ⋙ G)
    [G.IsLeftKanExtension α] (h : (elementsKan α).EssSurj) : SliceEssSurj L c := by
  intro d ψ
  let e : G ≅ yoneda.obj (L.obj c) :=
    G.leftKanExtensionUniqueOfIso α i (yoneda.obj (L.obj c)) (yonedaMap L c)
  obtain ⟨p, ⟨iso⟩⟩ := h.mem_essImage (⟨op d, e.inv.app (op d) ψ⟩ : G.Elements)
  haveI : IsIso iso.hom.val :=
    inferInstanceAs (IsIso ((CategoryOfElements.π G).map iso.hom))
  refine ⟨p.1.unop, iso.hom.val.unop, i.hom.app p.1 p.2, isIso_unop _, ?_⟩
  have hfac : e.hom.app ((elementsKan α).obj p).1 (α.app p.1 p.2)
      = L.map (i.hom.app p.1 p.2) := by
    have h0 := ConcreteCategory.congr_hom (G.descOfIsLeftKanExtension_fac_app α
      (yoneda.obj (L.obj c)) (i.hom ≫ yonedaMap L c) p.1) p.2
    simpa using h0
  calc iso.hom.val.unop ≫ L.map (i.hom.app p.1 p.2)
      = e.hom.app (op d) (G.map iso.hom.val (α.app p.1 p.2)) := by
        rw [e.hom.naturality_apply iso.hom.val (α.app p.1 p.2), hfac]
        rfl
    _ = e.hom.app (op d) (e.inv.app (op d) ψ) := congrArg _ iso.hom.property
    _ = ψ := by
        rw [← types_comp_apply (e.inv.app (op d)) (e.hom.app (op d)), ← NatTrans.comp_app,
          e.inv_hom_id, NatTrans.id_app, types_id_apply]

/-- **A localization is essentially surjective**, so the slice comparison must be too. -/
theorem sliceEssSurj_of_isLocalization {c : C} (i : F ≅ yoneda.obj c) (α : F ⟶ L.op ⋙ G)
    [G.IsLeftKanExtension α] (W' : MorphismProperty F.Elements)
    [(elementsKan α).IsLocalization W'] : SliceEssSurj L c :=
  sliceEssSurj_of_essSurj i α (Localization.essSurj _ W')

end Slice

section EssSurj

variable {A : Type*} [Category A] {B : Type*} [Category B] {E : Type*} [Category E]

theorem essSurj_of_comp (F : A ⥤ B) (Ψ : B ⥤ E) (h : (F ⋙ Ψ).EssSurj) : Ψ.EssSurj :=
  ⟨fun Y => ((h.mem_essImage Y).elim fun X e => ⟨F.obj X, e⟩)⟩

theorem essSurj_of_op (Ψ : A ⥤ B) (h : Ψ.op.EssSurj) : Ψ.EssSurj :=
  ⟨fun Y => ((h.mem_essImage (op Y)).elim fun X e => ⟨X.unop, ⟨(e.some.unop).symm⟩⟩)⟩

end EssSurj

/-- A functor into `Grade` is a grading — the converse of `Grading.functor`. -/
def Grading.ofFunctor {D : Type u} [Category.{v} D] (F : D ⥤ Grade) : Grading D where
  codim f := Multiplicative.toAdd (F.map f)
  codim_id a := congrArg Multiplicative.toAdd (F.map_id a)
  codim_comp f g := by rw [F.map_comp]; exact Nat.add_comm _ _

end CategoryTheory

open CubeChains BPSet

namespace ChainCat

/-! ## The crossing number of a chain morphism -/

/-- **The crossing number**: the Coxeter length of the crossing permutation.  It is additive
because a crossing made is never undone (`permLen_crossPerm_comp`), and it vanishes exactly on the
merges — so, unlike `codim`, it survives inverting them. -/
noncomputable def crossGrading (K : BPSet) : Grading (Ch K) where
  codim f := permLen (crossPerm rfl f)
  codim_id a := by rw [crossPerm_id, permLen_one]
  codim_comp f g := by
    rw [permLen_crossPerm_comp rfl f g, permLen_crossPerm rfl (tgtStrands f rfl) g]

theorem crossGrading_codim {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    (crossGrading K).codim f = permLen (crossPerm rfl f) := rfl

theorem crossGrading_codim_eq_zero_iff {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    (crossGrading K).codim f = 0 ↔ W K f :=
  ⟨fun h => (W_iff_crossPerm_eq_one rfl f).mpr (eq_one_of_permLen_eq_zero _ h),
    fun h => by rw [crossGrading_codim, (W_iff_crossPerm_eq_one rfl f).mp h, permLen_one]⟩

theorem crossGrading_inverts (K : BPSet) : (W K).IsInvertedBy (crossGrading K).functor := by
  intro a b f hf
  have h : (crossGrading K).functor.map f = 𝟙 _ :=
    congrArg Multiplicative.ofAdd ((crossGrading_codim_eq_zero_iff f).mpr hf)
  rw [h]
  exact IsIso.id _

/-- **The crossing number of a localized arrow.** -/
noncomputable def crossLoc (K : BPSet) : (W K).Localization ⥤ Grade :=
  Localization.Construction.lift _ (crossGrading_inverts K)

/-- …as a grading, so that it vanishes on isomorphisms and adds along composition. -/
noncomputable def crossGradingLoc (K : BPSet) : Grading ((W K).Localization) :=
  Grading.ofFunctor (crossLoc K)

theorem crossGradingLoc_Q {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    (crossGradingLoc K).codim ((W K).Q.map f) = permLen (crossPerm rfl f) := rfl

/-! ## The square, and the atom loop it creates -/

theorem not_merge_atomHom (l r : List ℕ+) : ¬ merge Zbp (atomHom l r) := by
  rintro ⟨d, hd⟩
  rw [Subsingleton.elim d (spliceCut l r 1 1 (cubeReorder 1 1))] at hd
  exact cubeMerge_ne_cubeReorder hd.symm

theorem not_W_atomHom (l r : List ℕ+) : ¬ W Zbp (atomHom l r) := fun h =>
  not_merge_atomHom l r
    ((merge_iff _).mpr ⟨h, (spliceCut l r 1 1 (cubeReorder 1 1)).codim_eq_one⟩)

/-- The straight staircase of the square. -/
def sqMerge : zObj [1, 1] ⟶ zObj [2] := mergeHom [] [] 1 1

/-- The crossed staircase of the square — same source and target, one crossing more. -/
def sqAtom : zObj [1, 1] ⟶ zObj [2] := atomHom [] []

theorem W_sqMerge : W Zbp sqMerge := W_mergeHom [] [] 1 1

theorem not_W_sqAtom : ¬ W Zbp sqAtom := not_W_atomHom [] []

theorem crossGrading_sqAtom_pos : 0 < (crossGrading Zbp).codim sqAtom :=
  Nat.pos_of_ne_zero fun h => not_W_sqAtom ((crossGrading_codim_eq_zero_iff _).mp h)

/-- **Nothing is longer than the reversal**, as a bound. -/
theorem permLen_le_revPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLen σ ≤ permLen (Fin.revPerm : Equiv.Perm (Fin n)) :=
  Nat.le.intro (permLen_add_inv_mul_revPerm σ)

/-- **A refinement performs a simple braid**: it crosses no pair twice, so it crosses at most as
much as the reversal.  This is the bound the localized base breaks — `PosBraid N` is not simple. -/
theorem crossGrading_le_revPerm {K : BPSet} {a b : Ch K} {N : ℕ} (f : a ⟶ b)
    (h : dimSum a.dims = N) :
    (crossGrading K).codim f ≤ permLen (Fin.revPerm : Equiv.Perm (Fin N)) := by
  rw [crossGrading_codim, permLen_crossPerm h rfl f]
  exact permLen_le_revPerm _

theorem crossGrading_le_one {a b : Ch Zbp} (f : a ⟶ b) (h : dimSum a.dims = 2) :
    (crossGrading Zbp).codim f ≤ 1 :=
  (crossGrading_le_revPerm f h).trans (by decide)

instance isIso_Q_sqMerge : IsIso ((W Zbp).Q.map sqMerge) :=
  Localization.inverts (W Zbp).Q (W Zbp) _ W_sqMerge

/-- **The atom loop**: the crossed staircase of the square read over the straight one.  It is the
generator `σ` of `PosBraid 2`, and it is not invertible — `Ch Zbp[W⁻¹]` has arrows that no single
refinement performs. -/
noncomputable def atomLoop : (W Zbp).Q.obj (zObj [2]) ⟶ (W Zbp).Q.obj (zObj [2]) :=
  inv ((W Zbp).Q.map sqMerge) ≫ (W Zbp).Q.map sqAtom

theorem crossGradingLoc_atomLoop :
    (crossGradingLoc Zbp).codim atomLoop = (crossGrading Zbp).codim sqAtom := by
  rw [atomLoop, (crossGradingLoc Zbp).codim_comp,
    (crossGradingLoc Zbp).codim_eq_zero_of_isIso, crossGradingLoc_Q]
  exact Nat.zero_add _

/-- **The square breaks the slice comparison.**  `σ²` crosses twice, while a refinement of two
strands crosses at most once and an isomorphism crosses nothing — so `σ²` is not `Q u` for any
refinement `u` into `[2]`, however its source is transported. -/
theorem not_sliceEssSurj_sq : ¬ SliceEssSurj (W Zbp).Q (zObj [2]) := by
  intro hs
  obtain ⟨a, v, u, hv, hvu⟩ := hs (atomLoop ≫ atomLoop)
  haveI := hv
  have h2 : 2 ≤ (crossGradingLoc Zbp).codim (atomLoop ≫ atomLoop) := by
    rw [(crossGradingLoc Zbp).codim_comp, crossGradingLoc_atomLoop]
    have := crossGrading_sqAtom_pos
    omega
  have hdim : dimSum a.dims = 2 := (dimSum_eq_of_hom u).trans rfl
  have h1 : (crossGradingLoc Zbp).codim (v ≫ (W Zbp).Q.map u) ≤ 1 := by
    rw [(crossGradingLoc Zbp).codim_comp, (crossGradingLoc Zbp).codim_eq_zero_of_isIso,
      crossGradingLoc_Q]
    have hu := crossGrading_le_one u hdim
    rw [crossGrading_codim] at hu
    omega
  rw [hvu] at h1
  omega

/-! ## The refutation

`Ch (⋁c)` is the slice `Ch Zbp / c`, so the claim at `K = ⋁c` is that localizing a slice is
slicing the localization.  It is not: the atom loop lives over `[2]` in `Ch Zbp[W⁻¹]` and no
refinement of the square performs it. -/

/-- **The fibre presheaf of a serial wedge is representable** — the inclusion of the serial wedges
into `BPSet` is fully faithful, so `Ch (⋁c) ≌ Ch Zbp / c`. -/
def wedgeHomsSerial (c : List ℕ+) : wedgeHoms (⋁c) ≅ yoneda.obj (zObj c) :=
  NatIso.ofComponents
    (fun a => Equiv.toIso
      { toFun := fun φ => (⟨φ, Subsingleton.elim _ _⟩ : a.unop ⟶ zObj c)
        invFun := Hom.φ
        left_inv := fun _ => rfl
        right_inv := fun _ => hom_ext' rfl })
    (fun f => by ext φ; exact hom_ext' rfl)

/-- **Refutation, at the comparison.**  For `K = ⋁[2]` — the square — the comparison from `Ch K`
to the elements of *any* left Kan extension of `wedgeHoms K` along the localized base is not
essentially surjective, so it cannot be a localization. -/
theorem not_essSurj_elementsKan_square {G : ((W Zbp).Localization)ᵒᵖ ⥤ Type}
    (α : wedgeHoms (⋁[2]) ⟶ (W Zbp).Q.op ⋙ G) [G.IsLeftKanExtension α] :
    ¬ (elementsKan α).EssSurj := fun h =>
  not_sliceEssSurj_sq (sliceEssSurj_of_essSurj (wedgeHomsSerial [2]) α h)

theorem not_isLocalization_elementsKan_square {G : ((W Zbp).Localization)ᵒᵖ ⥤ Type}
    (α : wedgeHoms (⋁[2]) ⟶ (W Zbp).Q.op ⋙ G) [G.IsLeftKanExtension α]
    (W' : MorphismProperty (wedgeHoms (⋁[2])).Elements) :
    ¬ (elementsKan α).IsLocalization W' := fun _ =>
  not_sliceEssSurj_sq (sliceEssSurj_of_isLocalization (wedgeHomsSerial [2]) α W')

/-! ### …read on `Ch K` itself -/

/-- The comparison, read on `Ch K` — `chEquivElements` puts `Ch K` on the opposite side. -/
noncomputable def chKan {K : BPSet} {G : ((W Zbp).Localization)ᵒᵖ ⥤ Type}
    (α : wedgeHoms K ⟶ (W Zbp).Q.op ⋙ G) : Ch K ⥤ (G.Elements)ᵒᵖ :=
  (chEquivElements K).functor ⋙ (elementsKan α).op

/-- **`Ch(K)[W⁻¹]` is not the elements of a Kan-extended presheaf.**  The square is the
counterexample, and it is the first slice: `Ch(□²)[W⁻¹]` is the weak order on two strands, while
the slice of the localized base over `[2]` is all of `PosBraid 2`. -/
theorem not_isLocalization_chKan {G : ((W Zbp).Localization)ᵒᵖ ⥤ Type}
    (α : wedgeHoms (⋁[2]) ⟶ (W Zbp).Q.op ⋙ G) [G.IsLeftKanExtension α] :
    ¬ (chKan α).IsLocalization (W (⋁[2])) := by
  intro hloc
  exact not_essSurj_elementsKan_square α
    (essSurj_of_op _ (essSurj_of_comp _ _ (Localization.essSurj (chKan α) (W (⋁[2])))))

/-- **…at the Kan extension itself** — `Type` has the colimits, so the counterexample is not
vacuous for want of an extension. -/
theorem not_isLocalization_chKan_lan :
    ¬ (chKan ((W Zbp).Q.op.leftKanExtensionUnit (wedgeHoms (⋁[2])))).IsLocalization (W (⋁[2])) :=
  not_isLocalization_chKan _

end ChainCat
