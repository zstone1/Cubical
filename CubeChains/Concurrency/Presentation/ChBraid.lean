import CubeChains.Concurrency.Presentation.Retraction
import CubeChains.Concurrency.Presentation.ElementsFibration

/-!
# Concurrency/Presentation/ChBraid — the positive braid an arrow of `Ch(K)[W⁻¹]` performs

`Ch K` is a category of elements over `Ch Zbp`, so it projects to the localized base, where every
hom-set is `PosBraid N` (`homEquivPosBraid`).  That composite is `chBraid`.

Under `IsSegal` the projection is **faithful** (`faithful_chLocBase`): localizing `Ch K` only
localizes the base.  Hence `eq_of_chBraid_eq` — a parallel pair performing one positive braid is
one arrow — which is what makes `chBraid` decisive rather than merely invariant.

`chBraid_equiv_map` reads the braid through *any* equivalence modelling `Ch(K)[W⁻¹]`, so a route
that names its 1-cells in its own model never has to be transported by hand.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

open CategoryTheory.Localization

/-- The descent of a presheaf's elements projects to the base — `pre`, transported. -/
theorem preOf_comp_π {B : Type*} [Category B] (W : MorphismProperty B) {P : B ⥤ Type}
    {Pd : W.Localization ⥤ Type} (h : W.Q ⋙ Pd = P) :
    Localization.preOf W h ⋙ CategoryOfElements.π Pd = CategoryOfElements.π P ⋙ W.Q := by
  subst h; rfl

variable (K : BPSet)

/-! ## The projection to the localized base -/

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

/-- **Any lift of `chBaseRaw` through the localization is the projection** — the universal property,
so a route only has to exhibit its own reading as a lift. -/
noncomputable def chLocBaseIso (G : (W K).Localization ⥤ (((W Zbp).op).Localization)ᵒᵖ)
    [Localization.Lifting (W K).Q (W K) (chBaseRaw K) G] : chLocBase K ≅ G :=
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K) (chLocBase K) :=
    ⟨eqToIso (chLocBase_fac K)⟩
  Localization.liftNatIso (W K).Q (W K) (chBaseRaw K) (chBaseRaw K) _ _ (Iso.refl _)

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

/-- **The two readings of the projection agree** — both lift `chBaseRaw`. -/
noncomputable def chLocBaseModelIso : chLocBase K ≅ chLocBaseModel K hS :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent K hS
  haveI : Localization.Lifting (W K).Q (W K) (chBaseRaw K) (chLocBaseModel K hS) :=
    ⟨Functor.isoWhiskerRight
      (Localization.qCompEquivalenceFromModelFunctorIso (chDescent K hS) (W K))
      ((CategoryOfElements.π (wedgeHomsDescend K hS)).op) ≪≫
      eqToIso (chDescent_comp_π K hS)⟩
  chLocBaseIso K _

include hS in
/-- **A localized chain remembers its base faithfully** — `Ch K` is a category of elements and
localizing it only localizes the base, so the projection stays faithful. -/
theorem faithful_chLocBase : (chLocBase K).Faithful :=
  haveI : (chDescent K hS).IsLocalization (W K) := isLocalization_chDescent K hS
  haveI : (chLocBaseModel K hS).Faithful :=
    inferInstanceAs ((Localization.equivalenceFromModel (chDescent K hS) (W K)).functor ⋙
      (CategoryOfElements.π (wedgeHomsDescend K hS)).op).Faithful
  Functor.Faithful.of_iso (chLocBaseModelIso K hS).symm

/-! ## The braid an arrow performs

Every hom-set of the localized base is `PosBraid N` (`homEquivPosBraid`), so the projection turns
an arrow of `Ch(K)[W⁻¹]` into a positive braid — faithfully, under `IsSegal`. -/

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
  refine eq_one_of_mul_eq_one (b := chBraid (inv f) hY hX) ?_
  rw [← chBraid_comp (inv f) f hY hX hY, IsIso.inv_hom_id, chBraid_id]

/-- **Isomorphisms on either side do not change the braid** — the shape every comparison of two
presentations produces.  The `IsIso` witnesses are explicit: the object spellings a comparison
produces are not the ones instance search matches. -/
theorem chBraid_sandwich {N : ℕ} {X X' Y Y' : (W K).Localization} (u : X ⟶ X') (hu : IsIso u)
    (f : X' ⟶ Y') (v : Y' ⟶ Y) (hv : IsIso v)
    (hX : dimSum (chOf X).dims = N) (hX' : dimSum (chOf X').dims = N)
    (hY' : dimSum (chOf Y').dims = N) (hY : dimSum (chOf Y).dims = N) :
    chBraid (u ≫ f ≫ v) hX hY = chBraid f hX' hY' := by
  haveI := hu; haveI := hv
  rw [chBraid_comp u (f ≫ v) hX hX' hY, chBraid_comp f v hX' hY' hY,
    chBraid_eq_one_of_isIso u hX hX', chBraid_eq_one_of_isIso v hY' hY, mul_one, one_mul]

/-- **…and in particular transports do not** — the shape a comparison of two *polygraphs*
produces, where the isomorphisms are equalities of 0-cells. -/
theorem chBraid_eqToHom_sandwich {N : ℕ} {X X' Y Y' : (W K).Localization} (hx : X = X')
    (f : X' ⟶ Y') (hy : Y' = Y)
    (hX : dimSum (chOf X).dims = N) (hX' : dimSum (chOf X').dims = N)
    (hY' : dimSum (chOf Y').dims = N) (hY : dimSum (chOf Y).dims = N) :
    chBraid (eqToHom hx ≫ f ≫ eqToHom hy) hX hY = chBraid f hX' hY' :=
  chBraid_sandwich _ inferInstance f _ inferInstance hX hX' hY' hY

include hS in
/-- **A parallel pair performing the same braid is one arrow** — faithfulness of the projection,
read through `homEquivPosBraid`. -/
theorem eq_of_chBraid_eq {N : ℕ} {X Y : (W K).Localization} {f g : X ⟶ Y}
    (hX : dimSum (chOf X).dims = N) (hY : dimSum (chOf Y).dims = N)
    (h : chBraid f hX hY = chBraid g hX hY) : f = g :=
  haveI := faithful_chLocBase K hS
  (chLocBase K).map_injective (Quiver.Hom.unop_inj
    ((homEquivPosBraid (a := zObj (chOf Y).dims) (b := zObj (chOf X).dims) hY hX).injective h))

/-- **The braid may be read in any model of `Ch(K)[W⁻¹]`.**  Given an equivalence `E` onto a model
and a reading `G` of that model in the localized base lifting the projection, an arrow of the model
performs the braid its `G`-image is: the comparison and the counit are isomorphisms, and an
isomorphism performs nothing.  This is what lets each route read its own generators' braids without
transporting anything by hand. -/
theorem chBraid_equiv_map {N : ℕ} {D : Type*} [Category D] (E : (W K).Localization ≌ D)
    {G : D ⥤ (((W Zbp).op).Localization)ᵒᵖ} (α : chLocBase K ≅ E.functor ⋙ G)
    {A B : D} (ψ : A ⟶ B)
    (hA : dimSum (chOf (E.inverse.obj A)).dims = N)
    (hB : dimSum (chOf (E.inverse.obj B)).dims = N)
    (hA' : dimSum (zOf (G.obj A).unop).dims = N)
    (hB' : dimSum (zOf (G.obj B).unop).dims = N) :
    chBraid (E.inverse.map ψ) hA hB = homEquivPosBraid hB' hA' ((G.map ψ).unop) := by
  obtain ⟨γ⟩ : Nonempty (E.inverse ⋙ chLocBase K ≅ G) :=
    ⟨Functor.isoWhiskerLeft E.inverse α ≪≫ Functor.isoWhiskerRight E.counitIso G ≪≫
      G.leftUnitor⟩
  have hnat : ((chLocBase K).map (E.inverse.map ψ)).unop
      = (γ.inv.app B).unop ≫ (G.map ψ).unop ≫ (γ.hom.app A).unop :=
    (congrArg Quiver.Hom.unop (NatIso.naturality_2 γ ψ).symm).trans
      (unop_comp.trans ((congrArg (fun s => s ≫ (γ.hom.app A).unop) unop_comp).trans
        (Category.assoc _ _ _)))
  rw [chBraid, hnat]
  exact homEquivPosBraid_sandwich hB hA hB' hA' _
    (inferInstanceAs (IsIso ((γ.app B).unop).inv)) _ _
    (inferInstanceAs (IsIso ((γ.app A).unop).hom))

end ChainCat
