import CubeChains.Concurrency.Presentation.PosLocalization
import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Machinery.Localization.FibrationLocalize

/-!
# Concurrency/Presentation/ElementsFibration — `Ch K` is a category of elements over `Ch Zbp`

`toChZ : Ch K ⥤ Ch Zbp` is a discrete fibration whose fibre over `a` is `⋁a ⟶ K`, so `Ch K` is
the category of elements of `wedgeHoms K = ⋁- ⟶ K` — with an `ᵒᵖ`, mathlib's `Elements` being the
opfibration convention.  `W K` is the inverse image of `W Zbp`, so
`Machinery/Localization/FibrationLocalize` applies: localizing `Ch K` only localizes the base.

What that needs is `InvertsMerges K`, which is `IsSegal` with `K`'s own base points fixed
(`isSegal_iff_invertsMerges_repoint`) — hence strictly weaker, which is why the refutations state
it while the descent takes `IsSegal`.
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
off again, with no bead computation for `splicePhi`.  `isLocal_iff_bijective_repoint` is the base
points, free in one direction and recovered in the other. -/

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

/-- **Only the canonical merges need checking**: a merge *is* a `mergeHom` (`eq_splicePhi_of_sq`),
so this is one condition per cut position — a chain with two adjacent beads has exactly one filler
merging them. -/
theorem invertsMerges_iff_bijective_mergeHom :
    InvertsMerges K ↔ ∀ (l r : List ℕ+) (p q : ℕ+),
      Function.Bijective ((wedgeHoms K).map (mergeHom l r p q).op) := by
  refine ⟨fun hK l r p q =>
    (isIso_iff_bijective _).mp (hK (mergeHom l r p q).op (W_mergeHom l r p q)),
    fun h => invertsMerges_of_merge K ?_⟩
  rintro a b u ⟨d, hw⟩
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  have hmap : ∀ m, (wedgeHoms K).map u.op m = (wedgeHoms K).map (mergeHom l r p q).op m := by
    intro m
    change Hom.φ u ≫ m = Hom.φ (mergeHom l r p q) ≫ m
    rw [eq_splicePhi_of_sq sq, hw, mergeHom, spliceHom, zHom_φ]
    rfl
  refine (isIso_iff_bijective _).mpr ⟨fun x y hxy => (h l r p q).1 ?_, fun y => ?_⟩
  · rw [← hmap, ← hmap]; exact hxy
  · obtain ⟨x, hx⟩ := (h l r p q).2 y
    exact ⟨x, (hmap x).trans hx⟩

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
theorem isLocalization_chDescent : (chDescent K hS).IsLocalization (W K) := by
  haveI : Functor.IsLocalization
      (elementsDescent (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS))
      (elementsW K) := isLocalization_elementsDescent _ _ _
  refine Functor.IsLocalization.of_equivalence_source
    ((elementsDescent (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS)).op)
    (elementsW K).op
    (chDescent K hS) (W K) (chEquivElements K).symm ?_ ?_ ?_
  · intro X Y f hf
    refine MorphismProperty.le_isoClosure _ _ ?_
    rw [W_eq_inverseImage_toElements]
    change (elementsW K).op
      ((chEquivElements K).functor.map ((chEquivElements K).inverse.map f))
    rw [Equivalence.fun_inv_map]
    exact MorphismProperty.RespectsIso.precomp _ ((chEquivElements K).counitIso.app X).hom _
      (MorphismProperty.RespectsIso.postcomp _ ((chEquivElements K).counitIso.app Y).inv _ hf)
  · intro a b f hf
    rw [W_eq_inverseImage_toElements] at hf
    exact Localization.inverts
      ((elementsDescent (W Zbp).op (wedgeHoms K) (invertsMerges_of_isSegal K hS)).op)
      (elementsW K).op _ hf
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (chEquivElements K).counitIso _ ≪≫ Functor.leftUnitor _

end Descent

end ChainCat
