import CubeChains.Machinery.Bicolimit
import CubeChains.Machinery.Localization.SliceFamily
import Mathlib.CategoryTheory.Category.Cat.Colimit

/-!
# Machinery/Localization/SliceBicolimit — `C[W⁻¹]` is the bicolimit of its localized slices

The diagram `overLocFunctor W` is strict, so its cocones commute on the nose and
`isColimitOverLocCocone` reads `overCoconeLocEquiv` in `Cat`.  A *pseudo*-cocone commutes only up
to isomorphism, and the terminal object `𝟙 c` of each slice absorbs that isomorphism: reading a
pseudo-cocone at the tops (`descTop`) descends it, so the same legs are a bicolimit.
-/

universe u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

/-! ## The diagram of localized slices -/

/-- The localized slices as a diagram of categories. -/
noncomputable def overLocFunctor : C ⥤ Cat.{u, u} where
  obj c := Cat.of ((W.over (X := c)).Localization)
  map u := (overMapLoc W u).toCatHom
  map_id c := Cat.ext (overMapLoc_id W c)
  map_comp u v := Cat.ext (overMapLoc_comp W u v)

/-- The localization functor, restricted to the slice over `c`. -/
noncomputable def overLocLeg (c : C) : (W.over (X := c)).Localization ⥤ W.Localization :=
  (overCoconeLocEquiv W (𝟭 W.Localization)).obj c

/-- **A functor on `C[W⁻¹]` postcomposes the legs** — `overCoconeLocEquiv` is natural in its
target, which is what makes the legs a *colimiting* cocone and not merely a cocone. -/
theorem overLocLeg_comp {E : Type u} [Category.{u} E] (Φ : W.Localization ⥤ E) (c : C) :
    overLocLeg W c ⋙ Φ = (overCoconeLocEquiv W Φ).obj c :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overLocLeg, overCoconeLocEquiv_apply W (𝟭 W.Localization) c,
      overCoconeLocEquiv_apply W Φ c, Functor.comp_id, Functor.assoc])

/-- The legs, as a cocone on the localized slices. -/
noncomputable def overLocCocone : Cocone (overLocFunctor W) where
  pt := Cat.of W.Localization
  ι :=
    { app := fun c => (overLocLeg W c).toCatHom
      naturality := fun _ _ u =>
        Cat.ext (((overCoconeLocEquiv W (𝟭 W.Localization)).w u).trans
          (Functor.comp_id _).symm) }

/-- **`C[W⁻¹]` is the colimit of its localized slices.** -/
noncomputable def isColimitOverLocCocone : IsColimit (overLocCocone W) where
  desc s := Cat.Hom.ofFunctor ((overCoconeLocEquiv W).symm
    { obj := fun c => (s.ι.app c).toFunctor
      w := fun {_ _} u => congrArg Cat.Hom.toFunctor (s.w u) })
  fac s c := Cat.ext ((overLocLeg_comp W _ c).trans
    (congrArg (fun G : OverCoconeLoc W ↥s.pt => G.obj c)
      ((overCoconeLocEquiv W).apply_symm_apply _)))
  uniq _s m h := Cat.ext ((Equiv.eq_symm_apply _).2 (OverCoconeLoc.ext W fun c =>
    (overLocLeg_comp W m.toFunctor c).symm.trans (congrArg Cat.Hom.toFunctor (h c))))

/-! ## The tops of the slices, as a section

Everything the pseudo-cocone contributes is packed into `Grothendieck.functorFrom`, so the two
lemmas below — the only geometry there is — are equations between arrows of
`Grothendieck (overLocFunctor W)`, where `Grothendieck.ext` reads them off base and fibre. -/

/-- The terminal object of the slice, in the localization. -/
noncomputable def sliceTop (c : C) : (W.over (X := c)).Localization :=
  (W.over (X := c)).Q.obj (Over.mk (𝟙 c))

/-- The diagram acts on a localized slice arrow as `Over.map` acts on the arrow. -/
theorem overLocFunctor_map_Q_map {X Y : C} (u : X ⟶ Y) {A B : Over X} (g : A ⟶ B) :
    ((overLocFunctor W).map u).toFunctor.map ((W.over (X := X)).Q.map g)
      = (W.over (X := Y)).Q.map ((Over.map u).map g) := rfl

/-- **The tops are a section of the slice diagram**: `𝟙 c` is terminal in `Over c`, and `toTop`
carries a pushed-forward top to the top. -/
noncomputable def sliceTopSection : C ⥤ Grothendieck (overLocFunctor W) where
  obj c := ⟨c, sliceTop W c⟩
  map {_ c} u := ⟨u, (W.over (X := c)).Q.map (OverCocone.toTop u)⟩
  map_id c := Grothendieck.ext _ _ rfl (by
    refine (Category.id_comp _).trans ?_
    rw [OverCocone.toTop_id]
    exact eqToHom_map (W.over (X := c)).Q _)
  map_comp {a b c} u v := Grothendieck.ext _ _ rfl (by
    have key : (W.over (X := c)).Q.map (OverCocone.toTop (u ≫ v))
        = eqToHom (congrArg (W.over (X := c)).Q.obj
            (Functor.congr_obj (Over.mapComp_eq u v) (Over.mk (𝟙 a))))
          ≫ (W.over (X := c)).Q.map ((Over.map v).map (OverCocone.toTop u))
          ≫ (W.over (X := c)).Q.map (OverCocone.toTop v) := by
      rw [OverCocone.toTop_comp, Functor.map_comp, Functor.map_comp, eqToHom_map]
    exact (Category.id_comp _).trans key)

/-- **Every slice object is a top pushed forward** — the arrow to it is a fibrewise isomorphism, so
the bicolimit inverts it. -/
noncomputable def sliceTopArrow {c : C} (x : Over c) :
    (sliceTopSection W).obj x.left
      ⟶ (Grothendieck.ι (overLocFunctor W) c).obj ((W.over (X := c)).Q.obj x) where
  base := x.hom
  fiber := eqToHom (congrArg (W.over (X := c)).Q.obj (OverCocone.map_obj_top x.hom))

instance isIso_sliceTopArrow_fiber {c : C} (x : Over c) : IsIso (sliceTopArrow W x).fiber :=
  inferInstanceAs (IsIso (eqToHom
    (congrArg (W.over (X := c)).Q.obj (OverCocone.map_obj_top x.hom))))

variable {W}

/-- **The arrow to a slice object is natural in it.** -/
theorem sliceTopArrow_naturality {c : C} {x y : Over c} (f : x ⟶ y) :
    (sliceTopSection W).map f.left ≫ sliceTopArrow W y
      = sliceTopArrow W x ≫ (Grothendieck.ι (overLocFunctor W) c).map
        ((W.over (X := c)).Q.map f) := by
  have key : (W.over (X := c)).Q.map ((Over.map y.hom).map (OverCocone.toTop f.left))
      = eqToHom (congrArg (W.over (X := c)).Q.obj (OverCocone.map_obj_map_obj_top f))
        ≫ (W.over (X := c)).Q.map f
        ≫ eqToHom (congrArg (W.over (X := c)).Q.obj
            (OverCocone.map_obj_top y.hom).symm) := by
    rw [OverCocone.map_toTop f, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  refine Grothendieck.ext _ _ (by simp [sliceTopArrow, sliceTopSection, Over.w f]) ?_
  simp only [Grothendieck.comp_fiber, sliceTopArrow, sliceTopSection, Grothendieck.ι_map]
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ z ≫ _) key) ?_
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z ≫ _ ≫ _) (eqToHom_map _ _)).symm
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (comp_eqToHom₂ ((W.over (X := c)).Q.map f) _ _)) ?_
  exact eqToHom_comp₃_comp_eq _ _ _ _ _ _ _

variable (W)

/-- The tops, as a transformation into the fibre inclusion. -/
noncomputable def sliceTopNat (c : C) :
    Over.forget c ⋙ sliceTopSection W
      ⟶ (W.over (X := c)).Q ⋙ Grothendieck.ι (overLocFunctor W) c where
  app x := sliceTopArrow W x
  naturality _ _ f := sliceTopArrow_naturality f

variable {W}

/-- **…and compatible with the transitions of the Grothendieck construction.** -/
theorem sliceTopArrow_ιNatTrans {c c' : C} (u : c ⟶ c') (x : Over c) :
    sliceTopArrow W x ≫ (Grothendieck.ιNatTrans (F := overLocFunctor W) u).app
        ((W.over (X := c)).Q.obj x)
      = sliceTopArrow W ((Over.map u).obj x) := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [Grothendieck.comp_fiber, sliceTopArrow, Grothendieck.ιNatTrans_app_fiber,
    eqToHom_map]
  exact (eqToHom_comp₃_comp _ _ _ _ _).trans (Category.comp_id _)

/-! ## The legs, as a pseudo-cocone -/

variable (W)

/-- The legs of `overCoconeLocEquiv`: the diagram is strict, so the transitions are transports. -/
noncomputable def slicePseudoCocone : PseudoCocone (overLocFunctor W) W.Localization where
  ι c := overLocLeg W c
  κ u := eqToIso ((overCoconeLocEquiv W (𝟭 W.Localization)).w u).symm
  κ_id _ := rfl
  κ_comp u v := by
    refine NatTrans.ext (funext fun x => ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
    symm
    exact eqToHom_comp₃ _ _ _ _

/-- The transitions are transports between functors that agree on objects, so they are
componentwise identities. -/
theorem slicePseudoCocone_κ_app {c c' : C} (u : c ⟶ c')
    (z : (W.over (X := c)).Localization) : ((slicePseudoCocone W).κ u).hom.app z = 𝟙 _ :=
  eqToHom_app ((overCoconeLocEquiv W (𝟭 W.Localization)).w u).symm z

/-- Reading the leg at the top of the slice is reading the localization functor. -/
theorem overLocLeg_sliceTop (c : C) : (overLocLeg W c).obj (sliceTop W c) = W.Q.obj c := rfl

/-- Every object of a localized slice is a slice object. -/
theorem Q_objEquiv_symm {c : C} (z : (W.over (X := c)).Localization) :
    (W.over (X := c)).Q.obj ((Localization.Construction.objEquiv (W.over (X := c))).symm z) = z :=
  rfl

/-! ## A pseudo-cocone, read at the tops -/

variable {W} {E : Type u} [Category.{u} E]

/-- A leg precomposed with a functor carries the same identity transitions. -/
theorem precompose_κ_app (Φ : W.Localization ⥤ E) {c c' : C} (u : c ⟶ c')
    (z : (W.over (X := c)).Localization) :
    ((((slicePseudoCocone W).precompose E).obj Φ).κ u).hom.app z = 𝟙 _ :=
  (congrArg Φ.map (slicePseudoCocone_κ_app W u z)).trans (Φ.map_id _)

variable (s : PseudoCocone (overLocFunctor W) E)

/-- **A pseudo-cocone, read at the tops of the slices** — the transitions are absorbed by
`functorFrom`, so no coherence is checked twice. -/
noncomputable def descTop : C ⥤ E := sliceTopSection W ⋙ s.functorFrom

theorem descTop_inverts : W.IsInvertedBy (descTop s) := fun _ Y w hw =>
  s.functorFrom_inverts _ (Localization.inverts (W.over (X := Y)).Q (W.over (X := Y))
    (OverCocone.toTop w) hw)

/-- **The functor on `C[W⁻¹]` a pseudo-cocone descends to.** -/
noncomputable def descLoc : W.Localization ⥤ E :=
  Localization.Construction.lift (descTop s) (descTop_inverts s)

instance isIso_functorFrom_sliceTopNat (c : C) :
    IsIso (Functor.whiskerRight (sliceTopNat W c) s.functorFrom) := by
  haveI : ∀ x : Over c, IsIso ((Functor.whiskerRight (sliceTopNat W c) s.functorFrom).app x) :=
    fun x => s.functorFrom_inverts (sliceTopArrow W x) (isIso_sliceTopArrow_fiber W x)
  exact NatIso.isIso_of_isIso_app _

/-- **The descent, read on a slice**: the arrow to a slice object, which the pseudo-cocone
inverts. -/
noncomputable def descSlice (c : C) :
    Over.forget c ⋙ descTop s ≅ (W.over (X := c)).Q ⋙ s.ι c :=
  @asIso _ _ _ _ _ (isIso_functorFrom_sliceTopNat s c) ≪≫
    Functor.isoWhiskerLeft _ (s.ιCompFunctorFrom c)

theorem descSlice_hom_app (c : C) (x : Over c) :
    (descSlice s c).hom.app x = s.functorFrom.map (sliceTopArrow W x) :=
  Category.comp_id (s.functorFrom.map (sliceTopArrow W x))

/-! ## …and descends to `C[W⁻¹]` -/

theorem Q_comp_overLocLeg (c : C) :
    (W.over (X := c)).Q ⋙ overLocLeg W c = Over.forget c ⋙ W.Q :=
  overCoconeLocEquiv_apply W (𝟭 W.Localization) c

theorem Q_comp_descLocLeg (c : C) :
    (W.over (X := c)).Q ⋙ (overLocLeg W c ⋙ descLoc s) = Over.forget c ⋙ descTop s := by
  rw [← Functor.assoc, Q_comp_overLocLeg, Functor.assoc, descLoc, Localization.Construction.fac]

noncomputable instance liftingDescLoc (c : C) :
    Localization.Lifting (W.over (X := c)).Q (W.over (X := c)) (Over.forget c ⋙ descTop s)
      (overLocLeg W c ⋙ descLoc s) :=
  ⟨eqToIso (Q_comp_descLocLeg s c)⟩

/-- **The descent reads a leg back to that leg.** -/
noncomputable def descLocLeg (c : C) : overLocLeg W c ⋙ descLoc s ≅ s.ι c :=
  Localization.liftNatIso (W.over (X := c)).Q (W.over (X := c)) (Over.forget c ⋙ descTop s)
    ((W.over (X := c)).Q ⋙ s.ι c) (overLocLeg W c ⋙ descLoc s) (s.ι c) (descSlice s c)

theorem descLocLeg_hom_app (c : C) (x : Over c) :
    (descLocLeg s c).hom.app ((W.over (X := c)).Q.obj x)
      = s.functorFrom.map (sliceTopArrow W x) := by
  have h0 : (Localization.Lifting.iso (W.over (X := c)).Q (W.over (X := c))
        (Over.forget c ⋙ descTop s) (overLocLeg W c ⋙ descLoc s)).hom.app x
      = eqToHom (Functor.congr_obj (Q_comp_descLocLeg s c) x) :=
    eqToHom_app (Q_comp_descLocLeg s c) x
  rw [descLocLeg, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    descSlice_hom_app, h0]
  exact Eq.trans (Category.id_comp (s.functorFrom.map (sliceTopArrow W x) ≫ 𝟙 _))
    (Category.comp_id (s.functorFrom.map (sliceTopArrow W x)))

/-- The transition of a pseudo-cocone, read on the Grothendieck construction. -/
theorem functorFrom_ιNatTrans {c c' : C} (u : c ⟶ c') (z : (W.over (X := c)).Localization) :
    s.functorFrom.map ((Grothendieck.ιNatTrans u).app z) = (s.κ u).hom.app z :=
  (congrArg ((s.κ u).hom.app z ≫ ·) ((s.ι c').map_id _)).trans (Category.comp_id _)

/-- **Every pseudo-cocone is its own descent, read back through the legs.** -/
noncomputable def precomposeDescLocIso :
    ((slicePseudoCocone W).precompose E).obj (descLoc s) ≅ s :=
  PseudoCocone.isoMk (descLocLeg s) fun {c c'} u =>
    Localization.natTrans_ext (W.over (X := c)).Q (W.over (X := c)) fun x => by
      have hA := precompose_κ_app (descLoc s) u
      have hB : (descLocLeg s c').hom.app
            (((overLocFunctor W).map u).toFunctor.obj ((W.over (X := c)).Q.obj x))
          = s.functorFrom.map (sliceTopArrow W ((Over.map u).obj x)) :=
        descLocLeg_hom_app s c' ((Over.map u).obj x)
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [hA, hB, ← sliceTopArrow_ιNatTrans u x]
      refine (Category.id_comp _).trans ((s.functorFrom.map_comp _ _).trans ?_)
      exact (congrArg (s.functorFrom.map (sliceTopArrow W x) ≫ ·)
          (functorFrom_ιNatTrans s u ((W.over (X := c)).Q.obj x))).trans
        (congrArg (· ≫ (s.κ u).hom.app ((W.over (X := c)).Q.obj x))
          (descLocLeg_hom_app s c x).symm)

/-! ## The universal property -/

instance essSurj_precompose_slicePseudoCocone :
    ((slicePseudoCocone W).precompose E).EssSurj where
  mem_essImage s := ⟨descLoc s, ⟨precomposeDescLocIso s⟩⟩

instance faithful_precompose_slicePseudoCocone :
    ((slicePseudoCocone W).precompose E).Faithful where
  map_injective {_ _ _ _} h :=
    Localization.natTrans_ext W.Q W fun c =>
      congr_app (congrArg (PseudoCocone.Hom.app · c) h) (sliceTop W c)

variable {Φ Ψ : W.Localization ⥤ E}
  (θ : ((slicePseudoCocone W).precompose E).obj Φ
    ⟶ ((slicePseudoCocone W).precompose E).obj Ψ)

/-- **A modification is pinned at the tops**: its law along `u`, read at the top of the slice. -/
theorem mod_app_top {c c' : C} (u : c ⟶ c') :
    (θ.app c').app (((overLocFunctor W).map u).toFunctor.obj (sliceTop W c))
      = (θ.app c).app (sliceTop W c) := by
  have hmod := congr_app (θ.naturality u) (sliceTop W c)
  rw [NatTrans.comp_app, NatTrans.comp_app, precompose_κ_app Φ u, precompose_κ_app Ψ u] at hmod
  exact (Category.id_comp _).symm.trans (hmod.trans (Category.comp_id _))

/-- A modification of the legs, read at the tops. -/
noncomputable def modTop : W.Q ⋙ Φ ⟶ W.Q ⋙ Ψ where
  app c := (θ.app c).app (sliceTop W c)
  naturality {_ c'} u :=
    ((θ.app c').naturality ((W.over (X := c')).Q.map (OverCocone.toTop u))).trans
      (congrArg (· ≫ Ψ.map (W.Q.map u)) (mod_app_top θ u))

instance full_precompose_slicePseudoCocone : ((slicePseudoCocone W).precompose E).Full where
  map_surjective {Φ' Ψ'} θ' :=
    ⟨Localization.Construction.natTransExtension (modTop θ'), PseudoCocone.hom_ext fun c =>
      NatTrans.ext (funext fun z => by
        obtain ⟨x, rfl⟩ : ∃ x : Over c, (W.over (X := c)).Q.obj x = z :=
          ⟨_, Q_objEquiv_symm W z⟩
        have hQ : (W.over (X := c)).Q.obj ((Over.map x.hom).obj (Over.mk (𝟙 x.left)))
            = (W.over (X := c)).Q.obj x :=
          congrArg (W.over (X := c)).Q.obj (OverCocone.map_obj_top x.hom)
        have h3 : ((((slicePseudoCocone W).precompose E).obj Φ').ι c).map (eqToHom hQ) = 𝟙 _ :=
          (congrArg Φ'.map (eqToHom_map (overLocLeg W c) hQ)).trans (Φ'.map_id _)
        have h4 : ((((slicePseudoCocone W).precompose E).obj Ψ').ι c).map (eqToHom hQ) = 𝟙 _ :=
          (congrArg Ψ'.map (eqToHom_map (overLocLeg W c) hQ)).trans (Ψ'.map_id _)
        have hnat := (θ'.app c).naturality (eqToHom hQ)
        rw [h3, h4] at hnat
        have key : (θ'.app c).app ((W.over (X := c)).Q.obj x)
            = (θ'.app c).app ((W.over (X := c)).Q.obj
                ((Over.map x.hom).obj (Over.mk (𝟙 x.left)))) :=
          (Category.id_comp _).symm.trans (hnat.trans (Category.comp_id _))
        exact (Localization.Construction.NatTransExtension.app_eq (modTop θ') x.left).trans
          ((mod_app_top θ' x.hom).symm.trans key.symm))⟩

/-- **`C[W⁻¹]` is the bicolimit of its localized slices** — the terminal object of each slice
normalises a pseudo-cocone's transitions away. -/
theorem isBicolimit_slicePseudoCocone : IsBicolimit (slicePseudoCocone W) := fun _ _ =>
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-! ## The slice diagram of a discrete fibration -/

/-- **The localized slices of a discrete fibration, against those of its base** — a comparison of
diagrams, where `sliceLocEquiv` is only a comparison of categories. -/
noncomputable def postLocNat {D : Type u} [Category.{u} D] (F : C ⥤ D)
    (V : MorphismProperty D) : overLocFunctor (V.inverseImage F) ⟶ F ⋙ overLocFunctor V where
  app c := (postLoc F V c).toCatHom
  naturality _ _ u := Cat.ext (postLoc_naturality F V u)

end CategoryTheory
