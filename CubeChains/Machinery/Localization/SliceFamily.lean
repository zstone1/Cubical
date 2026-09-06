import CubeChains.Machinery.Localization.SliceLocalize
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Machinery/Localization/SliceFamily — a functor on `C` is a cocone on its slices

`c ↦ Over c` is a *strict* functor to `Cat` (`Over.mapId_eq`, `Over.mapComp_eq`), and so is its
localization (`overMapLoc_id`, `overMapLoc_comp`), so a compatible family is an honest cocone: the
compatibility is an equality of functors and the correspondence is an `Equiv` of types.
`Over.forget c ⋙ Φ` is one such cocone, and every cocone comes from a unique `Φ` — read it at the
terminal object `𝟙 c` of each slice.

A comparison that is only an *isomorphism* still needs no weaker notion of cocone: read the
isomorphism as a cocone valued in `Arrow E` (`NatTrans.toArrow`), whose two projections are the
functors being compared.  A 2-cell carried as a 1-cell keeps every compatibility an equality.

Localizing changes nothing, because `W.over c` is inverted for every `c` exactly when `W` is.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]

/-! ## A natural transformation, read as a functor into the arrow category -/

instance Arrow.isThin [Quiver.IsThin E] : Quiver.IsThin (Arrow E) :=
  fun _ _ => ⟨fun a b => Arrow.hom_ext a b (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- In a thin category an arrow is pinned by its endpoints, so `Arrow.ext`'s filling obligation is
discharged without ever transporting the morphism. -/
theorem Arrow.mk_eq_mk_of_thin [Quiver.IsThin E] {A B A' B' : E} (f : A ⟶ B) (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') : Arrow.mk f = Arrow.mk g :=
  Arrow.ext hA hB (Subsingleton.elim _ _)

/-- **A natural transformation, read as a functor into the arrow category**: a 2-cell carried as a
1-cell.  Its projections along `Arrow.leftFunc` and `Arrow.rightFunc` are `F` and `G` by
definition, which is what lets a comparison be checked with `Functor.ext` and no `eqToHom`. -/
@[simps] def NatTrans.toArrow {A : Type u₃} [Category.{v₃} A] {F G : A ⥤ E} (α : F ⟶ G) :
    A ⥤ Arrow E where
  obj a := Arrow.mk (α.app a)
  map f := Arrow.homMk (F.map f) (G.map f) (α.naturality f)
  map_id _ := Arrow.hom_ext _ _ (F.map_id _) (G.map_id _)
  map_comp _ _ := Arrow.hom_ext _ _ (F.map_comp _ _) (G.map_comp _ _)

theorem Functor.mapArrow_comp {E' : Type u₃} [Category.{v₃} E'] (Φ : C ⥤ E) (Ψ : E ⥤ E') :
    (Φ ⋙ Ψ).mapArrow = Φ.mapArrow ⋙ Ψ.mapArrow := rfl

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

/-- **Two functors agreeing on every slice are equal** — the injectivity half of
`overCoconeEquiv`, read on functors. -/
theorem functor_ext {Φ Φ' : C ⥤ E} (h : ∀ c, Over.forget c ⋙ Φ = Over.forget c ⋙ Φ') : Φ = Φ' := by
  rw [← desc_ofFunctor Φ, ← desc_ofFunctor Φ']
  exact congrArg desc (ext h)

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

/-- Reading a cocone through a further functor. -/
def postcomp {E' : Type u₃} [Category.{v₃} E'] (Φ : E ⥤ E') : OverCocone C E' where
  obj c := G.obj c ⋙ Φ
  w u := congrArg (· ⋙ Φ) (G.w u)

/-- A sandwich whose crusts are identities up to defeq.  `eqToHom_refl` cannot see them — the two
spellings of each object are equal, not syntactically equal — so reach this through `exact`. -/
theorem eqToHom_conj_id {A B : E} (h₁ : A = A) (h₂ : B = B) (f : A ⟶ B) :
    eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by simp

theorem desc_postcomp {E' : Type u₃} [Category.{v₃} E'] (Φ : E ⥤ E') :
    (G.postcomp Φ).desc = G.desc ⋙ Φ := by
  refine Functor.ext (fun _ => rfl) fun _ _ u => ?_
  refine Eq.trans ?_ (eqToHom_conj_id _ _ _).symm
  simp [desc_map, postcomp, eqToHom_map]

end OverCocone

/-- **A functor on `C` is a cocone on its slices.** -/
@[simps] def overCoconeEquiv : (C ⥤ E) ≃ OverCocone C E where
  toFun := OverCocone.ofFunctor
  invFun := OverCocone.desc
  left_inv := OverCocone.desc_ofFunctor
  right_inv := OverCocone.ofFunctor_desc

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

/-- **A functor on `C[W⁻¹]` is a cocone on the localized slices.** -/
noncomputable def overCoconeLocEquiv : (W.Localization ⥤ E) ≃ OverCoconeLoc W E :=
  ((Localization.strictUniversalPropertyFixedTargetQ W E).functorEquiv).trans <|
    (Equiv.subtypeEquiv overCoconeEquiv (isInvertedBy_iff_over W)).trans (coconeLocEquiv W)

/-- Each leg of the cocone of `Φ` is `Φ` restricted to the slice. -/
theorem overCoconeLocEquiv_apply (Φ : W.Localization ⥤ E) (c : C) :
    (W.over (X := c)).Q ⋙ (overCoconeLocEquiv W Φ).obj c = Over.forget c ⋙ W.Q ⋙ Φ :=
  Localization.Construction.fac _ _

end CategoryTheory
