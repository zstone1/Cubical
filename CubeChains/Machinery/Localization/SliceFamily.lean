import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Machinery/Localization/SliceFamily — a functor on `C` is a cocone on its slices

`c ↦ Over c` is a *strict* functor to `Cat` (`Over.mapId_eq`, `Over.mapComp_eq`), and so is its
localization (`overMapLoc_id`, `overMapLoc_comp`), so a compatible family is an honest cocone: the
compatibility is an equality of functors and the correspondence is an `Equiv` of types.
`Over.forget c ⋙ Φ` is one such cocone, and every cocone comes from a unique `Φ` — read it at the
terminal object `𝟙 c` of each slice.

Localizing changes nothing, because `W.over c` is inverted for every `c` exactly when `W` is.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]

/-! ## Cocones on the slices -/

/-- A functor on each slice of `C`, constant along postcomposition. -/
structure OverCocone (C : Type u₁) [Category.{v₁} C] (E : Type u₂) [Category.{v₂} E] where
  /-- the functor on the slice over `c` -/
  obj (c : C) : Over c ⥤ E
  /-- reading at `c` after postcomposing along `u : c' ⟶ c` is reading at `c'` -/
  w {c' c : C} (u : c' ⟶ c) : Over.map u ⋙ obj c = obj c'

namespace OverCocone

@[ext] theorem ext {G G' : OverCocone C E} (h : ∀ c, G.obj c = G'.obj c) : G = G' := by
  cases G; cases G'; congr 1; exact funext h

/-- The slices of a functor. -/
@[simps] def ofFunctor (Φ : C ⥤ E) : OverCocone C E where
  obj c := Over.forget c ⋙ Φ
  w _ := rfl

variable (G : OverCocone C E)

/-- `G.w` read on morphisms. -/
theorem map_eq {c' c : C} (u : c' ⟶ c) {X Y : Over c'} (f : X ⟶ Y) :
    (G.obj c').map f =
      eqToHom (Functor.congr_obj (G.w u).symm X) ≫ (G.obj c).map ((Over.map u).map f) ≫
        eqToHom (Functor.congr_obj (G.w u).symm Y).symm :=
  Functor.congr_hom (G.w u).symm f

/-- The arrow of `Over c` from `u` to the terminal object.  A `def`, not an `abbrev`: in term
position an `abbrev` is unfolded and `rw` can no longer match on it. -/
def toTop {c' c : C} (u : c' ⟶ c) :
    (Over.map u).obj (Over.mk (𝟙 c')) ⟶ Over.mk (𝟙 c) :=
  Over.homMk u (by simp)

@[simp] theorem toTop_left {c' c : C} (u : c' ⟶ c) : (toTop u).left = u := rfl

/-- The functor a cocone descends to: read each slice at its terminal object. -/
def desc : C ⥤ E where
  obj c := (G.obj c).obj (Over.mk (𝟙 c))
  map {c' c} u :=
    eqToHom (Functor.congr_obj (G.w u).symm (Over.mk (𝟙 c'))) ≫ (G.obj c).map (toTop u)
  map_id c := by
    have h : toTop (𝟙 c) = eqToHom (Functor.congr_obj (Over.mapId_eq c) (Over.mk (𝟙 c))) := by
      ext; simp
    rw [h]; simp [eqToHom_map]
  map_comp {a b c} u v := by
    have hs : toTop (u ≫ v) =
        eqToHom (Functor.congr_obj (Over.mapComp_eq u v) (Over.mk (𝟙 a))) ≫
          ((Over.map v).map (toTop u) ≫ toTop v) := by
      ext; simp
    rw [hs, G.map_eq v (toTop u)]
    simp [eqToHom_map]

@[simp] theorem desc_obj (c : C) : G.desc.obj c = (G.obj c).obj (Over.mk (𝟙 c)) := rfl

theorem desc_map {c' c : C} (u : c' ⟶ c) :
    G.desc.map u =
      eqToHom (Functor.congr_obj (G.w u).symm (Over.mk (𝟙 c'))) ≫ (G.obj c).map (toTop u) :=
  rfl

theorem desc_ofFunctor (Φ : C ⥤ E) : (ofFunctor Φ).desc = Φ :=
  Functor.ext (fun _ => rfl) fun _ _ _ => by simp [desc_map]

/-- The terminal object of `Over c'`, pushed along `u : c' ⟶ c`, is `u` itself. -/
theorem map_obj_top {c' c : C} (u : c' ⟶ c) :
    (Over.map u).obj (Over.mk (𝟙 c')) = Over.mk u := by
  change Over.mk (𝟙 c' ≫ u) = Over.mk u
  rw [Category.id_comp]

theorem ofFunctor_desc : ofFunctor G.desc = G := by
  ext c
  refine Functor.ext (fun Y => ?_) (fun Y Z f => ?_)
  · exact (Functor.congr_obj (G.w Y.hom) (Over.mk (𝟙 Y.left))).symm.trans
      (congrArg (G.obj c).obj (map_obj_top Y.hom))
  · have hY : (Over.map Z.hom).obj ((Over.map f.left).obj (Over.mk (𝟙 Y.left))) = Y := by
      change Over.mk ((𝟙 Y.left ≫ f.left) ≫ Z.hom) = Over.mk Y.hom
      rw [Category.id_comp, Over.w]
    have hf : (Over.map Z.hom).map (toTop f.left) =
        eqToHom hY ≫ f ≫ eqToHom (map_obj_top Z.hom).symm := by ext; simp
    change G.desc.map f.left = _
    rw [desc_map, G.map_eq Z.hom (toTop f.left), hf]
    simp [eqToHom_map]

end OverCocone

/-- **A functor on `C` is a cocone on its slices.** -/
@[simps] def overCoconeEquiv : (C ⥤ E) ≃ OverCocone C E where
  toFun := OverCocone.ofFunctor
  invFun := OverCocone.desc
  left_inv := OverCocone.desc_ofFunctor
  right_inv := OverCocone.ofFunctor_desc

/-! ## Cocones whose compatibility is only an isomorphism

Reach for `OverCocone` when the compatibility really is an equality: that is the stronger statement
and it is a genuine `Equiv`.  Reach for `OverPseudoCocone` when the components come from **inverting
an equivalence** — inverting a `Presents` is a choice (`Functor.inv` is non-constructive), so such a
comparison is compatible only up to isomorphism and never strictly.  `Functor.ext` does not repair
this: a `Presents` gives an essentially surjective comparison, not a bijective-on-objects one, so
the objects are only isomorphic and the object half of `Functor.ext` fails. -/

/-- A functor on each slice of `C`, constant along postcomposition up to isomorphism. -/
structure OverPseudoCocone (C : Type u₁) [Category.{v₁} C] (E : Type u₂) [Category.{v₂} E] where
  /-- the functor on the slice over `c` -/
  obj (c : C) : Over c ⥤ E
  /-- reading at `c` after postcomposing along `u : c' ⟶ c` is reading at `c'`, up to iso -/
  iso {c' c : C} (u : c' ⟶ c) : Over.map u ⋙ obj c ≅ obj c'
  /-- the identity acts trivially -/
  iso_id (c : C) : iso (𝟙 c) = eqToIso (by rw [Over.mapId_eq, Functor.id_comp])
  /-- and composites compose -/
  iso_comp {a b c : C} (u : a ⟶ b) (v : b ⟶ c) :
    iso (u ≫ v) = eqToIso (by rw [Over.mapComp_eq, Functor.assoc]) ≪≫
      Functor.isoWhiskerLeft (Over.map u) (iso v) ≪≫ iso u

namespace OverPseudoCocone

variable (G : OverPseudoCocone C E)

/-- The functor a pseudo-cocone descends to: read each slice at its terminal object, and use the
comparison isomorphism where `OverCocone.desc` uses an `eqToHom`. -/
def desc : C ⥤ E where
  obj c := (G.obj c).obj (Over.mk (𝟙 c))
  map {c' c} u := (G.iso u).inv.app (Over.mk (𝟙 c')) ≫ (G.obj c).map (OverCocone.toTop u)
  map_id c := by
    have h : OverCocone.toTop (𝟙 c)
        = eqToHom (Functor.congr_obj (Over.mapId_eq c) (Over.mk (𝟙 c))) := by ext; simp
    rw [h, G.iso_id c]
    simp [eqToHom_map]
  map_comp {a b c} u v := by
    have hs : OverCocone.toTop (u ≫ v) =
        eqToHom (Functor.congr_obj (Over.mapComp_eq u v) (Over.mk (𝟙 a))) ≫
          ((Over.map v).map (OverCocone.toTop u) ≫ OverCocone.toTop v) := by ext; simp
    -- stated in the goal's spelling: `(G.obj c).map ((Over.map v).map _)`, not `(_ ⋙ _).map _`
    have hnat : (G.obj b).map (OverCocone.toTop u) ≫ (G.iso v).inv.app (Over.mk (𝟙 b))
        = (G.iso v).inv.app ((Over.map u).obj (Over.mk (𝟙 a))) ≫
          (G.obj c).map ((Over.map v).map (OverCocone.toTop u)) :=
      (G.iso v).inv.naturality (OverCocone.toTop u)
    have hnat' : ∀ {Z : E} (k : (Over.map v ⋙ G.obj c).obj (Over.mk (𝟙 b)) ⟶ Z),
        (G.obj b).map (OverCocone.toTop u) ≫ (G.iso v).inv.app (Over.mk (𝟙 b)) ≫ k
          = (G.iso v).inv.app ((Over.map u).obj (Over.mk (𝟙 a))) ≫
            (G.obj c).map ((Over.map v).map (OverCocone.toTop u)) ≫ k := fun k => by
      rw [← Category.assoc, hnat]
      exact Category.assoc _ _ _
    rw [hs, G.iso_comp u v]
    simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, eqToIso.inv, eqToHom_app, Functor.map_comp, Category.assoc,
      eqToHom_map]
    refine congrArg ((G.iso u).inv.app (Over.mk (𝟙 a)) ≫ ·) ?_
    refine Eq.trans ?_ (hnat' _).symm
    refine congrArg ((G.iso v).inv.app ((Over.map u).obj (Over.mk (𝟙 a))) ≫ ·) ?_
    exact (eqToHom_trans_assoc _ _ _).trans
      ((congrArg (· ≫ (G.obj c).map ((Over.map v).map (OverCocone.toTop u)) ≫
        (G.obj c).map (OverCocone.toTop v)) (eqToHom_refl _ _)).trans (Category.id_comp _))

theorem desc_map {c' c : C} (u : c' ⟶ c) :
    G.desc.map u = (G.iso u).inv.app (Over.mk (𝟙 c')) ≫ (G.obj c).map (OverCocone.toTop u) :=
  rfl

section Map

variable {G₁ G₂ : OverPseudoCocone C E}

/-- A map of pseudo-cocones: a family of legs commuting with the comparison isos. -/
def descMap (τ : ∀ c, G₁.obj c ⟶ G₂.obj c)
    (hτ : ∀ {c' c : C} (u : c' ⟶ c),
      Functor.whiskerLeft (Over.map u) (τ c) ≫ (G₂.iso u).hom = (G₁.iso u).hom ≫ τ c') :
    G₁.desc ⟶ G₂.desc where
  app c := (τ c).app (Over.mk (𝟙 c))
  naturality {c' c} u := by
    have hinv : (G₁.iso u).inv ≫ Functor.whiskerLeft (Over.map u) (τ c)
        = τ c' ≫ (G₂.iso u).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hτ u, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h := congrArg (fun σ => NatTrans.app σ (Over.mk (𝟙 c'))) hinv
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    -- `Category.assoc` will not match across `desc.map`'s spelling, so this runs through `exact`
    change ((G₁.iso u).inv.app _ ≫ (G₁.obj c).map _) ≫ _ = _ ≫ ((G₂.iso u).inv.app _ ≫ _)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((G₁.iso u).inv.app (Over.mk (𝟙 c')) ≫ ·)
      ((τ c).naturality (OverCocone.toTop u))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (G₂.obj c).map (OverCocone.toTop u)) h).trans ?_
    exact Category.assoc _ _ _

/-- **Descending is functorial**: leg isomorphisms commuting with the comparison isos descend to
an isomorphism of the descended functors. -/
def descIso (e : ∀ c, G₁.obj c ≅ G₂.obj c)
    (he : ∀ {c' c : C} (u : c' ⟶ c),
      Functor.whiskerLeft (Over.map u) (e c).hom ≫ (G₂.iso u).hom
        = (G₁.iso u).hom ≫ (e c').hom) :
    G₁.desc ≅ G₂.desc where
  hom := descMap (fun c => (e c).hom) he
  inv := descMap (fun c => (e c).inv) (by
    intro c' c u
    rw [show Functor.whiskerLeft (Over.map u) (e c).inv
        = (Functor.isoWhiskerLeft (Over.map u) (e c)).inv from rfl, Iso.inv_comp_eq,
      Functor.isoWhiskerLeft_hom, ← Category.assoc, he u, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  hom_inv_id := by ext c; exact (e c).hom_inv_id_app _
  inv_hom_id := by ext c; exact (e c).inv_hom_id_app _

end Map

end OverPseudoCocone

/-! ## The same, localized -/

/-- A strict universal property is a bijection on functors. -/
def Localization.StrictUniversalPropertyFixedTarget.functorEquiv {D : Type u₃} [Category.{v₃} D]
    {L : C ⥤ D} {W : MorphismProperty C}
    (h : Localization.StrictUniversalPropertyFixedTarget L W E) :
    (D ⥤ E) ≃ { F : C ⥤ E // W.IsInvertedBy F } where
  toFun Ψ := ⟨L ⋙ Ψ, fun _ _ f hf => by
    haveI := h.inverts f hf
    exact inferInstanceAs (IsIso (Ψ.map (L.map f)))⟩
  invFun F := h.lift F.1 F.2
  left_inv _ := h.uniq _ _ (h.fac _ _)
  right_inv _ := Subtype.ext (h.fac _ _)

variable (W : MorphismProperty C)

/-- A functor on each localized slice, constant along postcomposition. -/
structure OverCoconeLoc (W : MorphismProperty C) (E : Type u₂) [Category.{v₂} E] where
  /-- the functor on the localized slice over `c` -/
  obj (c : C) : (W.over (X := c)).Localization ⥤ E
  /-- reading at `c` after postcomposing along `u : c' ⟶ c` is reading at `c'` -/
  w {c' c : C} (u : c' ⟶ c) : overMapLoc W u ⋙ obj c = obj c'

namespace OverCoconeLoc

@[ext] theorem ext {G G' : OverCoconeLoc W E} (h : ∀ c, G.obj c = G'.obj c) : G = G' := by
  cases G; cases G'; congr 1; exact funext h

end OverCoconeLoc

/-- Inverting `W` and inverting every `W.over c` are the same condition. -/
theorem isInvertedBy_iff_over (Φ : C ⥤ E) :
    W.IsInvertedBy Φ ↔
      ∀ c : C, (W.over (X := c)).IsInvertedBy ((OverCocone.ofFunctor Φ).obj c) := by
  constructor
  · exact fun h _ _ _ f hf => h f.left hf
  · exact fun h _ b w hw =>
      h b (Over.homMk (U := Over.mk w) (V := Over.mk (𝟙 b)) w (by simp)) hw

/-- A `W`-inverting cocone on the slices is a cocone on the localized slices. -/
noncomputable def coconeLocEquiv :
    { G : OverCocone C E // ∀ c, (W.over (X := c)).IsInvertedBy (G.obj c) } ≃
      OverCoconeLoc W E where
  toFun G :=
    { obj := fun c => Localization.Construction.lift (G.1.obj c) (G.2 c)
      w := fun {c' c} u => Localization.Construction.uniq _ _ (by
        rw [← Functor.assoc, overMapLocFac, Functor.assoc, Localization.Construction.fac,
          Localization.Construction.fac, G.1.w u]) }
  invFun G :=
    ⟨{ obj := fun c => (W.over (X := c)).Q ⋙ G.obj c
       w := fun {c' c} u => by rw [← Functor.assoc, ← overMapLocFac, Functor.assoc, G.w u] },
     fun c _ _ f hf => by
       haveI : IsIso ((W.over (X := c)).Q.map f) := Localization.inverts _ _ f hf
       exact inferInstanceAs (IsIso ((G.obj c).map ((W.over (X := c)).Q.map f)))⟩
  left_inv _ := Subtype.ext (OverCocone.ext fun _ => Localization.Construction.fac _ _)
  right_inv _ :=
    OverCoconeLoc.ext _ fun _ => Localization.Construction.uniq _ _
      (Localization.Construction.fac _ _)

/-- A functor on each localized slice, constant along postcomposition up to isomorphism. -/
structure OverPseudoCoconeLoc (W : MorphismProperty C) (E : Type u₂) [Category.{v₂} E] where
  /-- the functor on the localized slice over `c` -/
  obj (c : C) : (W.over (X := c)).Localization ⥤ E
  /-- reading at `c` after postcomposing along `u : c' ⟶ c` is reading at `c'`, up to iso -/
  iso {c' c : C} (u : c' ⟶ c) : overMapLoc W u ⋙ obj c ≅ obj c'
  /-- the identity acts trivially -/
  iso_id (c : C) : iso (𝟙 c) = eqToIso (by rw [overMapLoc_id, Functor.id_comp])
  /-- and composites compose -/
  iso_comp {a b c : C} (u : a ⟶ b) (v : b ⟶ c) :
    iso (u ≫ v) = eqToIso (by rw [overMapLoc_comp, Functor.assoc]) ≪≫
      Functor.isoWhiskerLeft (overMapLoc W u) (iso v) ≪≫ iso u

namespace OverPseudoCoconeLoc

variable {W} (G : OverPseudoCoconeLoc W E)

theorem obj_eq {c' c : C} (u : c' ⟶ c) :
    Over.map u ⋙ (W.over (X := c)).Q ⋙ G.obj c
      = (W.over (X := c')).Q ⋙ overMapLoc W u ⋙ G.obj c := by
  rw [← Functor.assoc, ← overMapLocFac, Functor.assoc]

/-- Restricting along the localization functors. -/
noncomputable def toPseudoCocone : OverPseudoCocone C E where
  obj c := (W.over (X := c)).Q ⋙ G.obj c
  iso u := eqToIso (G.obj_eq u) ≪≫ Functor.isoWhiskerLeft _ (G.iso u)
  iso_id c := by rw [G.iso_id]; ext; simp
  iso_comp {a b _} u v := by
    rw [G.iso_comp]
    ext x
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
    -- in the goal's spelling: `(overMapLoc W u).obj (Q.obj x)`, not `(Q ⋙ overMapLoc W u).obj x`
    have ho : (overMapLoc W u).obj ((W.over (X := a)).Q.obj x)
        = (W.over (X := b)).Q.obj ((Over.map u).obj x) :=
      Functor.congr_obj (overMapLocFac W u) x
    rw [natTrans_app_congr (G.iso v).hom ho]
    simp

/-- The descended functor inverts `W`. -/
theorem toPseudoCocone_inverts : W.IsInvertedBy G.toPseudoCocone.desc := by
  intro a b w hw
  haveI : IsIso ((W.over (X := b)).Q.map (OverCocone.toTop w)) :=
    Localization.inverts (W.over (X := b)).Q (W.over (X := b)) (OverCocone.toTop w) hw
  exact (((G.toPseudoCocone.iso w).app (Over.mk (𝟙 a))).symm ≪≫
    (G.obj b).mapIso (asIso ((W.over (X := b)).Q.map (OverCocone.toTop w)))).isIso_hom

/-- **A pseudo-cocone on the localized slices induces a functor on `C[W⁻¹]`.** -/
noncomputable def descLoc : W.Localization ⥤ E :=
  Localization.Construction.lift _ G.toPseudoCocone_inverts

theorem descLoc_fac : W.Q ⋙ G.descLoc = G.toPseudoCocone.desc :=
  Localization.Construction.fac _ _

noncomputable instance liftingDescLoc :
    Localization.Lifting W.Q W G.toPseudoCocone.desc G.descLoc :=
  ⟨eqToIso G.descLoc_fac⟩

section Map

variable {G₁ G₂ : OverPseudoCoconeLoc W E}

/-- **`descLoc` is functorial in the pseudo-cocone**: a family of leg isomorphisms commuting with
the comparison isos descends.  Both `Ψ ⋙ Φ ≅ 𝟭` and `Φ ⋙ Ψ ≅ 𝟭` are instances, which is why this
is stated once here rather than twice at the use site. -/
noncomputable def descLocIso (e : ∀ c, G₁.obj c ≅ G₂.obj c)
    (he : ∀ {c' c : C} (u : c' ⟶ c),
      Functor.whiskerLeft (overMapLoc W u) (e c).hom ≫ (G₂.iso u).hom
        = (G₁.iso u).hom ≫ (e c').hom) :
    G₁.descLoc ≅ G₂.descLoc :=
  Localization.liftNatIso W.Q W G₁.toPseudoCocone.desc G₂.toPseudoCocone.desc
    G₁.descLoc G₂.descLoc
    (OverPseudoCocone.descIso (fun c => Functor.isoWhiskerLeft (W.over (X := c)).Q (e c))
      (by
        intro c' c u
        ext Y
        -- the goal spells it `Q.obj ((Over.map u).obj Y)`, not `(overMapLoc W u).obj (Q.obj Y)`
        have ho : (overMapLoc W u).obj ((W.over (X := c')).Q.obj Y)
            = (W.over (X := c)).Q.obj ((Over.map u).obj Y) :=
          Functor.congr_obj (overMapLocFac W u) Y
        have h := congrArg (fun σ => NatTrans.app σ ((W.over (X := c')).Q.obj Y)) (he u)
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
        simp only [toPseudoCocone, Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.isoWhiskerLeft_hom, eqToIso.hom, eqToHom_app, Category.assoc]
        rw [natTrans_app_congr (e c).hom ho] at h
        rw [← eqToHom_comp_iff]
        simpa using h))

end Map

/-- Reading a pseudo-cocone through a further functor. -/
noncomputable def postcomp {E' : Type u₃} [Category.{v₃} E'] (Φ : E ⥤ E') :
    OverPseudoCoconeLoc W E' where
  obj c := G.obj c ⋙ Φ
  iso u := Functor.isoWhiskerRight (G.iso u) Φ
  iso_id c := by rw [G.iso_id]; ext; simp [eqToHom_map]
  iso_comp u v := by rw [G.iso_comp]; ext; simp [eqToHom_map]

theorem descLoc_postcomp {E' : Type u₃} [Category.{v₃} E'] (Φ : E ⥤ E') :
    (G.postcomp Φ).descLoc = G.descLoc ⋙ Φ :=
  Localization.Construction.uniq _ _ (by
    rw [descLoc_fac, ← Functor.assoc, descLoc_fac]
    refine Functor.ext (fun _ => rfl) (fun c' c u => ?_)
    simp [postcomp, toPseudoCocone, OverPseudoCocone.desc, eqToHom_map])

end OverPseudoCoconeLoc

/-- A strict cocone on the localized slices is a pseudo-cocone. -/
noncomputable def OverCoconeLoc.toPseudo {W : MorphismProperty C} (G : OverCoconeLoc W E) :
    OverPseudoCoconeLoc W E where
  obj := G.obj
  iso u := eqToIso (G.w u)
  iso_id _ := rfl
  iso_comp u v := by ext; simp

/-- **A functor on `C[W⁻¹]` is a cocone on the localized slices.** -/
noncomputable def overCoconeLocEquiv : (W.Localization ⥤ E) ≃ OverCoconeLoc W E :=
  ((Localization.strictUniversalPropertyFixedTargetQ W E).functorEquiv).trans <|
    (Equiv.subtypeEquiv overCoconeEquiv (isInvertedBy_iff_over W)).trans (coconeLocEquiv W)

/-- Each leg of the cocone of `Φ` is `Φ` restricted to the slice. -/
theorem overCoconeLocEquiv_apply (Φ : W.Localization ⥤ E) (c : C) :
    (W.over (X := c)).Q ⋙ (overCoconeLocEquiv W Φ).obj c = Over.forget c ⋙ W.Q ⋙ Φ :=
  Localization.Construction.fac _ _

/-- …so a cocone is recovered from the functor it descends to. -/
theorem overCoconeLocEquiv_symm_apply (G : OverCoconeLoc W E) (c : C) :
    (W.over (X := c)).Q ⋙ G.obj c = Over.forget c ⋙ W.Q ⋙ (overCoconeLocEquiv W).symm G := by
  have h := overCoconeLocEquiv_apply W ((overCoconeLocEquiv W).symm G) c
  rwa [Equiv.apply_symm_apply] at h

/-- The pseudo-cocone of a functor on `C[W⁻¹]`, so that `𝟭` is a `descLoc` like any other. -/
noncomputable def OverPseudoCoconeLoc.ofFunctor {W : MorphismProperty C}
    (Φ : W.Localization ⥤ E) : OverPseudoCoconeLoc W E :=
  (overCoconeLocEquiv W Φ).toPseudo

theorem OverPseudoCoconeLoc.descLoc_ofFunctor {W : MorphismProperty C}
    (Φ : W.Localization ⥤ E) :
    (OverPseudoCoconeLoc.ofFunctor Φ).descLoc = Φ :=
  Localization.Construction.uniq _ _ (by
    rw [OverPseudoCoconeLoc.descLoc_fac]
    refine Functor.ext
      (fun c => Functor.congr_obj (overCoconeLocEquiv_apply W Φ c) (Over.mk (𝟙 c)))
      (fun c' c u => ?_)
    simp only [OverPseudoCocone.desc_map, OverPseudoCoconeLoc.toPseudoCocone,
      OverPseudoCoconeLoc.ofFunctor, OverCoconeLoc.toPseudo]
    rw [Functor.congr_hom (overCoconeLocEquiv_apply W Φ c) (OverCocone.toTop u)]
    simp
    rfl)

end CategoryTheory
