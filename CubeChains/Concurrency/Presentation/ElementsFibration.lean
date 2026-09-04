import CubeChains.Concurrency.Merge.MergeGenerate
import CubeChains.Concurrency.Grading.Degree
import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Machinery.Localization.ElementsAction
import CubeChains.Machinery.Localization.FibrationLocalize
import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Concurrency/Presentation/ElementsFibration — `Ch K` is a category of elements over `Ch Zbp`

`toChZ : Ch K ⥤ Ch Zbp` is a discrete fibration whose fibre over `a` is `⋁a ⟶ K`, so `Ch K` is
the category of elements of `wedgeHoms K = ⋁- ⟶ K` — with an `ᵒᵖ`, mathlib's `Elements` being the
opfibration convention.  `W K` is the inverse image of `W Zbp`, so
`Machinery/Localization/FibrationLocalize` applies: localizing `Ch K` only localizes the base.

A discrete fibration over `Ch Zbp` *is* a presheaf on it, and a presheaf descends along
`Ch Zbp ⟶ Ch Zbp[W⁻¹]` exactly when it inverts `W`.  `InvertsMerges K` is that condition verbatim,
and it is `IsSegal` with `K`'s own base points fixed (`isSegal_iff_invertsMerges_repoint`) — hence
strictly weaker, which is why the refutations state it while the descent takes `IsSegal`.  It buys
the *fibre*, not the presentation: lifting a presentation through the localization needs nothing
of `K` (`Presentation.elements` plus `merge_iff`).
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite CubeChains BPSet

universe w

namespace ChainCat

variable (K : BPSet)

/-! ### The fibre presheaf -/

/-- The fibre of `toChZ` over a serial wedge: the maps of that wedge into `K`. -/
def wedgeHoms : (Ch Zbp)ᵒᵖ ⥤ Type := serialWedgeInclusion.op ⋙ yoneda.obj K

@[simp] theorem wedgeHoms_map {a b : Ch Zbp} (f : a ⟶ b) (m : (wedgeHoms K).obj (op b)) :
    (wedgeHoms K).map f.op m = f.φ ≫ m := rfl

/-! ### `Ch K` is its category of elements -/

/-- A chain is its dimension sequence together with its classifying map. -/
@[simps] def toElements : Ch K ⥤ ((wedgeHoms K).Elements)ᵒᵖ where
  obj a := op ⟨op (zObj a.dims), a.map⟩
  map {a b} f := (CategoryOfElements.homMk _ _ (zHom f.φ).op f.w).op
  map_id a := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _
    (Quiver.Hom.unop_inj (hom_ext' (by simp [zHom_φ]))))
  map_comp f g := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _
    (Quiver.Hom.unop_inj (hom_ext' (by simp [zHom_φ]))))

instance : (toElements K).Faithful where
  map_injective h := hom_ext' (by
    have := congrArg (fun u => (Subtype.val (Quiver.Hom.unop u)).unop.φ) h
    simpa [zHom_φ] using this)

instance : (toElements K).Full where
  map_surjective {a b} h :=
    ⟨⟨(h.unop.val).unop.φ, h.unop.property⟩,
      Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _
        (Quiver.Hom.unop_inj (hom_ext' (by simp [zHom_φ]))))⟩

private theorem wedgeHoms_map_eqToHom {a b : Ch Zbp} (e : a = b) (t : (wedgeHoms K).obj (op a)) :
    (wedgeHoms K).map (eqToHom (congrArg op e)) t
      = eqToHom (congrArg BPSet.serialWedge (congrArg Obj.dims e).symm) ≫ t := by
  subst e; simp

instance : (toElements K).EssSurj where
  mem_essImage x := by
    have e : zObj (unop (unop x).1).dims = unop (unop x).1 := Obj.eq_of_dims rfl
    refine ⟨⟨(unop (unop x).1).dims, (unop x).2⟩, ⟨eqToIso (Opposite.unop_injective ?_)⟩⟩
    refine Functor.Elements.ext _ _ (congrArg op ?_) ?_
    · exact e
    · exact (wedgeHoms_map_eqToHom K e _).trans (Category.id_comp _)

instance : (toElements K).IsEquivalence where

/-- **`Ch K` is the category of elements of `⋁- ⟶ K`.** -/
noncomputable def chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ :=
  (toElements K).asEquivalence

/-- …read on the opposite, where `wedgeHoms K` is covariant and the cut presentation lives. -/
noncomputable def chOpEquivElements : (Ch K)ᵒᵖ ≌ (wedgeHoms K).Elements :=
  (chEquivElements K).op.trans (opOpEquivalence _)

/-! ### The merges are pulled back from the base -/

/-- `W K` read on the category of elements. -/
theorem W_eq_inverseImage_toElements :
    W K = ((W Zbp).op.inverseImage (CategoryOfElements.π (wedgeHoms K))).op.inverseImage
      (toElements K) := by
  ext a b f
  rw [W_eq_inverseImage_toChZ]
  rfl

/-! ### The bead merges act bijectively

A merge *is* `𝟙 ∨ cubeMerge ∨ 𝟙` up to isomorphism (`CutData`), which is what makes the reduction
to the cubes cheap: the whiskering lemmas run along the flanking beads and the unitors strip them
off again.  `isLocal_iff_bijective_repoint` is the base points, free in one direction and
recovered in the other. -/

/-- A bead merge acts bijectively on the maps of a serial wedge into `K`. -/
def InvertsMerges (K : BPSet) : Prop := ((W Zbp).op).IsInvertedBy (wedgeHoms K)

/-- **Only the wedge-to-tensor comparison needs checking**: "acts invertibly" is multiplicative,
and `W` is what one merge at a time reaches (`W_le_iff`). -/
theorem invertsMerges_of_merge
    (h : ∀ {a b : Ch Zbp} (u : a ⟶ b), merge Zbp u → IsIso ((wedgeHoms K).map u.op)) :
    InvertsMerges K := by
  have key : W Zbp
      ≤ ((MorphismProperty.isomorphisms Type).inverseImage (wedgeHoms K)).unop := by
    rw [W_le_iff]
    exact fun _ _ u hu => h u hu
  exact fun _ _ f hf => key f.unop hf

/-- **Locality at the positive blocks makes every bead merge act bijectively** — the whiskering
lemmas carry the cube statement along the flanking beads of a cut. -/
theorem invertsMerges_of_isLocal_cubeMerge
    (h : ∀ p q : ℕ+, IsLocal K.toPsh (cubeMerge (p : ℕ) (q : ℕ))) : InvertsMerges K := by
  refine invertsMerges_of_merge K ?_
  rintro a b u ⟨d, hd⟩
  have hw : IsLocal K.toPsh d.w := hd ▸ h d.p d.q
  have hu : IsLocal K.toPsh (Hom.φ u) :=
    IsLocal.congr d.e₁ d.e₂.symm
      (by rw [Iso.symm_hom, ← Category.assoc, d.sq, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])
      ((hw.tensor_id (⋁d.r)).id_tensor (⋁d.l))
  rw [isIso_iff_bijective]
  exact bijective_of_isLocal hu

/-- **The Segal condition makes every bead merge act bijectively.** -/
theorem invertsMerges_of_isSegal (h : IsSegal K.toPsh) : InvertsMerges K :=
  invertsMerges_of_isLocal_cubeMerge K ((isSegal_iff_isLocal_cubeMerge_pos K.toPsh).mp h)

/-! ### The injective half alone

Bijectivity is what makes the localized fibration have *all* lifts; **injectivity** is what makes it
have *at most one*, which is what a presentation transfers along.  The two are independent, and
only the second is available for a bare cube. -/

/-- Arrows of `Ch Zbp` along which restriction into `K` is injective. -/
def separating (K : BPSet) : MorphismProperty (Ch Zbp) :=
  fun _ _ u => Function.Injective ((wedgeHoms K).map u.op)

instance : (separating K).IsMultiplicative where
  id_mem _ := by intro m m' h; simpa using h
  comp_mem u v hu hv := by
    intro m m' h
    refine hv (hu ?_)
    rwa [show ((u ≫ v).op : op _ ⟶ op _) = v.op ≫ u.op from rfl,
      Functor.map_comp_apply] at h

/-- **A bead merge acts injectively** on the maps of a serial wedge into `K`: a chain of `K` has at
most one `W`-preimage of each shape.  Strictly weaker than `InvertsMerges`, and it is what
`Machinery/Presentation/Partial` consumes. -/
def SeparatesMerges (K : BPSet) : Prop := W Zbp ≤ separating K

/-- **Separation at the positive blocks makes every bead merge act injectively** — the whiskering
lemmas carry the cube statement along the flanking beads of a cut, exactly as for `IsLocal`. -/
theorem separatesMerges_of_isSegalSep (h : IsSegalSep K.toPsh) : SeparatesMerges K := by
  rw [SeparatesMerges, W_le_iff]
  rintro a b u ⟨d, hd⟩
  have hw : IsSeparated K.toPsh d.w := hd ▸ h d.p d.q
  have hu : IsSeparated K.toPsh (Hom.φ u) :=
    IsSeparated.congr d.e₁ d.e₂.symm
      (by rw [Iso.symm_hom, ← Category.assoc, d.sq, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])
      ((hw.tensor_id (⋁d.r)).id_tensor (⋁d.l))
  exact injective_of_isSeparated hu

/-- **Inverting implies separating** — the half of `IsSegal` that survives on a bare cube. -/
theorem separatesMerges_of_invertsMerges (h : InvertsMerges K) : SeparatesMerges K :=
  fun _ _ u hu => (isIso_iff_bijective _).mp (h u.op hu) |>.1

/-- **The bare cube separates its merges**, though it does not invert them
(`not_isSegal_cube_two`) — the instance that makes `SeparatesMerges` a weaker hypothesis than
`InvertsMerges` in fact and not only on paper. -/
theorem separatesMerges_cube (n : ℕ) : SeparatesMerges (□n) :=
  separatesMerges_of_isSegalSep _ (isSegalSep_cube n)

/-! ## Lifting a chart, partially

Inverting a merge would make restriction bijective; separating it makes restriction *injective*,
which is enough for the inverse to be a partial function.  That is the whole difference between the
descent route and the partial one. -/

section Lift

variable {K} {a b : Ch Zbp} {w : a ⟶ b}

/-- **Lifting a chart along a separating arrow is a partial function**: restriction along it is
injective, so a chart of the coarse shape extends in at most one way.  `SeparatesMerges K` supplies
the hypothesis at every merge. -/
noncomputable def mergeLift (_hw : separating K w) :
    (wedgeHoms K).obj (op a) → Option ((wedgeHoms K).obj (op b)) :=
  Function.partialInv ((wedgeHoms K).map w.op)

/-- **…and it is the lift it looks like.** -/
theorem mergeLift_eq_some_iff (hw : separating K w) (x : (wedgeHoms K).obj (op a))
    (y : (wedgeHoms K).obj (op b)) :
    mergeLift hw x = some y ↔ (wedgeHoms K).map w.op y = x :=
  hw.isPartialInv y x

/-- A chart of the fine shape restricts and lifts back to itself. -/
@[simp] theorem mergeLift_map (hw : separating K w) (y : (wedgeHoms K).obj (op b)) :
    mergeLift hw ((wedgeHoms K).map w.op y) = some y :=
  (mergeLift_eq_some_iff hw _ y).mpr rfl



/-- The chain of `K` a chart names. -/
abbrev chartChain (s : List ℕ+) (x : ⋁s ⟶ K) : Ch K := ⟨s, x⟩

/-- **Cartesian lift**: a chart of the fine shape restricting to `x` is a refinement of `x` in
`Ch K`, lying over `w`.  `Ch K` is a discrete fibration over `Ch Zbp` (`chEquivElements`), so this
asks nothing of `K` — in particular not separation, which is why the atom leg gets one too. -/
def homOfRestrict (w : a ⟶ b) {x : (wedgeHoms K).obj (op a)} {y : (wedgeHoms K).obj (op b)}
    (h : (wedgeHoms K).map w.op y = x) : chartChain a.dims x ⟶ chartChain b.dims y :=
  ⟨w.φ, h⟩

@[simp] theorem homOfRestrict_φ (w : a ⟶ b) {x : (wedgeHoms K).obj (op a)}
    {y : (wedgeHoms K).obj (op b)} (h : (wedgeHoms K).map w.op y = x) :
    (homOfRestrict w h).φ = w.φ := rfl

/-- **…and conversely**: a morphism of `Ch K` lying over `w` is a lift. -/
theorem mergeLift_eq_some_of_hom (hw : separating K w) {x : (wedgeHoms K).obj (op a)}
    {y : (wedgeHoms K).obj (op b)} (u : chartChain a.dims x ⟶ chartChain b.dims y)
    (hu : u.φ = w.φ) : mergeLift hw x = some y :=
  (mergeLift_eq_some_iff hw x y).mpr (by
    change w.φ ≫ y = x
    rw [← hu]
    exact u.w)

/-- A lift refines by the codimension of the arrow it lies over — `degree` sees only the shape, so
the `codim = 1` side condition `HasDiamonds` wants is free. -/
@[simp] theorem codim_homOfRestrict (w : a ⟶ b) {x : (wedgeHoms K).obj (op a)}
    {y : (wedgeHoms K).obj (op b)} (h : (wedgeHoms K).map w.op y = x) :
    codim (homOfRestrict w h) = codim w := rfl

/-- **The bridge**: a chart lifts along `w` exactly when the chain it names has a refinement lying
over `w` — the form `HasDiamonds` consumes. -/
theorem isSome_mergeLift_iff (hw : separating K w) (x : (wedgeHoms K).obj (op a)) :
    (mergeLift hw x).isSome ↔
      ∃ (y : (wedgeHoms K).obj (op b)) (u : chartChain a.dims x ⟶ chartChain b.dims y),
        u.φ = w.φ := by
  constructor
  · intro hs
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨y, homOfRestrict w ((mergeLift_eq_some_iff hw x y).mp hy), rfl⟩
  · rintro ⟨y, u, hu⟩
    exact Option.isSome_iff_exists.mpr ⟨y, mergeLift_eq_some_of_hom hw u hu⟩

end Lift

/-- **…and conversely**: a bead merge is the wedge-tensor comparison at a pair of cubes, spliced
between two stretches of beads that the unitors strip off again. -/
theorem isLocal_cubeMerge_of_invertsMerges (p q : ℕ+)
    (h : ∀ u v : K.cells 0, InvertsMerges (K.repoint u v)) :
    IsLocal K.toPsh (cubeMerge (p : ℕ) (q : ℕ)) := by
  have hm : IsLocal K.toPsh (Hom.φ (mergeHom [] [] p q)) :=
    (isLocal_iff_bijective_repoint _ K).mpr fun u v =>
      (isIso_iff_bijective _).mp (h u v _ (W_mergeHom [] [] p q))
  exact IsLocal.of_tensor_unit (IsLocal.of_unit_tensor
    ((isLocal_congr (w := 𝟙 (⋁([] : List ℕ+)) ⊗ₘ (cubeMerge (p : ℕ) (q : ℕ) ⊗ₘ 𝟙 (⋁([] : List ℕ+))))
      (cutSrcIso ([] : List ℕ+) [] p q).symm
      (serialWedgeAppend ([] : List ℕ+) [p + q]) rfl).mp hm))

/-- **`K` is Segal exactly when its chains' bead merges act bijectively**, at every choice of base
points — the two readings of "`K` inverts the wedge-to-tensor comparison". -/
theorem isSegal_iff_invertsMerges_repoint :
    IsSegal K.toPsh ↔ ∀ u v : K.cells 0, InvertsMerges (K.repoint u v) :=
  (isSegal_iff_isLocal_cubeMerge_pos K.toPsh).trans
    ⟨fun h u v => invertsMerges_of_isLocal_cubeMerge (K.repoint u v) h,
      fun h p q => isLocal_cubeMerge_of_invertsMerges K p q h⟩

/-! ### Descent along the merges

`Ch K` localized at `W K` is the category of elements of the descended presheaf: all of the
`K`-dependence sits in `wedgeHoms K`. -/

section Descent

open CategoryTheory.Localization

variable (hS : IsSegal K.toPsh)

/-- The merges of `Ch K` read on the category of elements. -/
abbrev elementsW : MorphismProperty (wedgeHoms K).Elements :=
  (W Zbp).op.inverseImage (CategoryOfElements.π (wedgeHoms K))

/-- `⋁- ⟶ K` descended through the merges of the base. -/
noncomputable abbrev wedgeHomsDescend : ((W Zbp).op).Localization ⥤ Type :=
  descend (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS)

/-- `Ch K` compared with the category of elements of the descended presheaf. -/
noncomputable def chDescent : Ch K ⥤ ((wedgeHomsDescend K hS).Elements)ᵒᵖ :=
  toElements K ⋙ (elementsDescent (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS)).op

/-- **Localizing `Ch K` at the merges only localizes the base**, once the wedge of two cubes is
their tensor. -/
theorem isLocalization_chDescent : (chDescent K hS).IsLocalization (W K) :=
  haveI : Functor.IsLocalization
      (elementsDescent (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS))
      (elementsW K) := isLocalization_elementsDescent _ _ _
  Functor.IsLocalization.of_inverseImage (toElements K) _ (elementsW K).op _
    (W_eq_inverseImage_toElements K)

end Descent

end ChainCat
