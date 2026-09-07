import CubeChains.Machinery.Localization.SliceFamily

/-!
# Machinery/Presentation/ChosenInverse — inverting a fully faithful functor by hand

`F.invOfPreimage r θ` inverts a fully faithful `F` from a **chosen** preimage `r Y` of each object
together with `θ Y : F.obj (r Y) ≅ Y`: a morphism goes to the `F`-preimage of its conjugate, so
functoriality and both comparisons with `𝟭` are `F.map_preimage` and nothing else.

`Functor.inv` cannot do this job — its object map is `objPreimage`, so a *family* of inverses is
natural in a parameter only up to isomorphism.  Here naturality of the choice (`hr`, `hθ`) buys
strict squares, and the two comparisons — only isomorphisms, since `r` need not be injective —
travel as `Arrow`-valued functors, which keeps their squares equalities as well.
-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

/-- **Two 2-cells with equal endpoints and equal components are one 1-cell.**  `Arrow` inherits no
thinness, so this is what compares two `NatTrans.toArrow`s. -/
theorem NatTrans.toArrow_congr {A : Type u₁} [Category.{v₁} A] {E : Type u₂} [Category.{v₂} E]
    {F G F' G' : A ⥤ E} (α : F ⟶ G) (β : F' ⟶ G') (hF : F = F') (hG : G = G')
    (h : ∀ a, α.app a = eqToHom (Functor.congr_obj hF a) ≫ β.app a ≫
      eqToHom (Functor.congr_obj hG a).symm) :
    α.toArrow = β.toArrow := by
  subst hF; subst hG
  exact congrArg NatTrans.toArrow (NatTrans.ext (funext fun a => by simpa using h a))

/-! ## `eqToIso` bookkeeping

An `eqToIso`-conjugate of an iso is pinned by its endpoints, whatever objects the bookkeeping
routes through.  Two shapes, stated at the bracketings a chain of rewrites leaves behind: inside a
localized category `simp` will not reassociate `≪≫` — the instance argument defeats
`Iso.trans_assoc`'s matching — so the normal form has to be reached in one step. -/

theorem eqToIso_conj_ext {C : Type u₁} [Category.{v₁} C] {X Y A M N M' N' B : C} (α : X ≅ Y)
    (a : A = M) (a' : M = X) (b : Y = N) (b' : N = B)
    (c : A = M') (c' : M' = X) (d : Y = N') (d' : N' = B) :
    eqToIso a ≪≫ (eqToIso a' ≪≫ α ≪≫ eqToIso b) ≪≫ eqToIso b'
      = eqToIso c ≪≫ (eqToIso c' ≪≫ α ≪≫ eqToIso d) ≪≫ eqToIso d' := by
  subst a'; subst c'; subst a; subst b; subst d; subst b'; simp

theorem eqToIso_conj_collapse {C : Type u₁} [Category.{v₁} C] {X Y A₀ A₁ B₀ B₁ B₂ : C} (α : X ≅ Y)
    (a₀ : A₀ = A₁) (a₁ : A₁ = X) (b₀ : Y = B₀) (b₁ : B₀ = B₁) (b₂ : B₁ = B₂)
    (a : A₀ = X) (b : Y = B₂) :
    (eqToIso a₀ ≪≫ (eqToIso a₁ ≪≫ α ≪≫ eqToIso b₀) ≪≫ eqToIso b₁) ≪≫ eqToIso b₂
      = eqToIso a ≪≫ α ≪≫ eqToIso b := by
  subst a₁; subst a₀; subst b₀; subst b₁; subst b₂; simp

namespace Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **A faithful functor detects an equality of functors into its source**, given the equality on
objects: what stands in for `Subsingleton.elim` on `Functor.ext`'s morphism half. -/
theorem ext_of_faithful (F : A ⥤ B) [F.Faithful] {A' : Type u₃} [Category.{v₃} A']
    {G₁ G₂ : A' ⥤ A} (hobj : ∀ a, G₁.obj a = G₂.obj a) (h : G₁ ⋙ F = G₂ ⋙ F) : G₁ = G₂ :=
  Functor.ext hobj fun _ _ g => F.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact Functor.congr_hom h g)

theorem comp_mapIso {C : Type u₃} [Category.{v₃} C] (F : A ⥤ B) (G : B ⥤ C) {X Y : A} (α : X ≅ Y) :
    (F ⋙ G).mapIso α = G.mapIso (F.mapIso α) := rfl

/-- `Functor.congr_hom`, on isomorphisms. -/
theorem congr_mapIso {F G : A ⥤ B} (h : F = G) {X Y : A} (α : X ≅ Y) :
    F.mapIso α = eqToIso (Functor.congr_obj h X) ≪≫ G.mapIso α
      ≪≫ eqToIso (Functor.congr_obj h Y).symm := by
  subst h; simp

variable (F : A ⥤ B) [F.Full] [F.Faithful] (r : B → A) (θ : ∀ Y : B, F.obj (r Y) ≅ Y)

/-- **The inverse of `F` determined by a chosen preimage of every object.** -/
noncomputable def invOfPreimage : B ⥤ A where
  obj := r
  map {Y Y'} g := F.preimage ((θ Y).hom ≫ g ≫ (θ Y').inv)
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

@[simp] theorem invOfPreimage_obj (Y : B) : (F.invOfPreimage r θ).obj Y = r Y := rfl

omit [F.Full] [F.Faithful] in
/-- **The naming, transported along an equality of objects.** -/
theorem invOfPreimage_iso_congr {Y Y' : B} (h : Y = Y') :
    θ Y = eqToIso (congrArg (fun Z => F.obj (r Z)) h) ≪≫ θ Y' ≪≫ eqToIso h.symm := by
  subst h; ext; simp

/-- **The chosen inverse is a section of `F`, up to the chosen isos.** -/
noncomputable def invOfPreimageCounit : F.invOfPreimage r θ ⋙ F ≅ 𝟭 B :=
  NatIso.ofComponents θ fun _ => by simp [invOfPreimage]

@[simp] theorem invOfPreimageCounit_hom_app (Y : B) :
    (F.invOfPreimageCounit r θ).hom.app Y = (θ Y).hom := rfl

/-- **…and a retraction of it, only up to isomorphism**: `r` need not be injective, so two objects
may be entered from one 0-cell. -/
noncomputable def invOfPreimageUnit : 𝟭 A ≅ F ⋙ F.invOfPreimage r θ :=
  NatIso.ofComponents (fun Z => (F.preimageIso (θ (F.obj Z))).symm)
    fun _ => F.map_injective (by simp [invOfPreimage])

@[simp] theorem invOfPreimageUnit_hom_app (Z : A) :
    (F.invOfPreimageUnit r θ).hom.app Z = F.preimage (θ (F.obj Z)).inv := rfl

/-! ## Naturality in a parameter

Two chosen inverses, one over the other along `G` below and `H` above.  The choices are asked to
agree (`hr`, `hθ`); everything else is `F.map_preimage`. -/

section Square

variable {A' : Type u₃} [Category.{v₃} A'] {B' : Type u₄} [Category.{v₄} B']
  (F' : A' ⥤ B') [F'.Full] [F'.Faithful] (r' : B' → A') (θ' : ∀ Y : B', F'.obj (r' Y) ≅ Y)
  (G : A ⥤ A') (H : B ⥤ B')

/-- **The two chosen inverses agree after `F'`** — the square whose components are the chosen
isos. -/
theorem invOfPreimage_comp_square
    (e : ∀ Y : B, F'.obj (r' (H.obj Y)) = H.obj (F.obj (r Y)))
    (hθ : ∀ Y : B, θ' (H.obj Y) = eqToIso (e Y) ≪≫ H.mapIso (θ Y)) :
    H ⋙ F'.invOfPreimage r' θ' ⋙ F' = (F.invOfPreimage r θ ⋙ F) ⋙ H :=
  Functor.ext e fun _ _ _ => by simp [invOfPreimage, hθ]

/-- **…and therefore before it**, `F'` being faithful. -/
theorem invOfPreimage_square (hGH : G ⋙ F' = F ⋙ H)
    (hr : ∀ Y : B, r' (H.obj Y) = G.obj (r Y))
    (e : ∀ Y : B, F'.obj (r' (H.obj Y)) = H.obj (F.obj (r Y)))
    (hθ : ∀ Y : B, θ' (H.obj Y) = eqToIso (e Y) ≪≫ H.mapIso (θ Y)) :
    H ⋙ F'.invOfPreimage r' θ' = F.invOfPreimage r θ ⋙ G :=
  F'.ext_of_faithful hr (by
    change H ⋙ F'.invOfPreimage r' θ' ⋙ F' = F.invOfPreimage r θ ⋙ G ⋙ F'
    rw [invOfPreimage_comp_square F r θ F' r' θ' H e hθ, hGH]
    rfl)

/-- **The counit comparison travels along the square** — an equality of `Arrow`-valued functors,
which is what descends through a colimit. -/
theorem invOfPreimageCounit_arrow_square
    (e : ∀ Y : B, F'.obj (r' (H.obj Y)) = H.obj (F.obj (r Y)))
    (hθ : ∀ Y : B, θ' (H.obj Y) = eqToIso (e Y) ≪≫ H.mapIso (θ Y)) :
    H ⋙ (F'.invOfPreimageCounit r' θ').hom.toArrow
      = (F.invOfPreimageCounit r θ).hom.toArrow ⋙ H.mapArrow :=
  NatTrans.toArrow_congr (Functor.whiskerLeft H (F'.invOfPreimageCounit r' θ').hom)
    (Functor.whiskerRight (F.invOfPreimageCounit r θ).hom H)
    (invOfPreimage_comp_square F r θ F' r' θ' H e hθ) rfl fun _ => by simp [hθ]

/-- The unit's square, one level below the counit's. -/
theorem invOfPreimageUnit_square (hGH : G ⋙ F' = F ⋙ H)
    (hr : ∀ Y : B, r' (H.obj Y) = G.obj (r Y))
    (e : ∀ Y : B, F'.obj (r' (H.obj Y)) = H.obj (F.obj (r Y)))
    (hθ : ∀ Y : B, θ' (H.obj Y) = eqToIso (e Y) ≪≫ H.mapIso (θ Y)) :
    G ⋙ F' ⋙ F'.invOfPreimage r' θ' = (F ⋙ F.invOfPreimage r θ) ⋙ G :=
  calc G ⋙ F' ⋙ F'.invOfPreimage r' θ' = (G ⋙ F') ⋙ F'.invOfPreimage r' θ' := rfl
    _ = (F ⋙ H) ⋙ F'.invOfPreimage r' θ' := by rw [hGH]
    _ = F ⋙ H ⋙ F'.invOfPreimage r' θ' := rfl
    _ = F ⋙ F.invOfPreimage r θ ⋙ G := by
        rw [invOfPreimage_square F r θ F' r' θ' G H hGH hr e hθ]
    _ = (F ⋙ F.invOfPreimage r θ) ⋙ G := rfl

/-- **…and so does the unit comparison.** -/
theorem invOfPreimageUnit_arrow_square (hGH : G ⋙ F' = F ⋙ H)
    (hr : ∀ Y : B, r' (H.obj Y) = G.obj (r Y))
    (e : ∀ Y : B, F'.obj (r' (H.obj Y)) = H.obj (F.obj (r Y)))
    (hθ : ∀ Y : B, θ' (H.obj Y) = eqToIso (e Y) ≪≫ H.mapIso (θ Y)) :
    G ⋙ (F'.invOfPreimageUnit r' θ').hom.toArrow
      = (F.invOfPreimageUnit r θ).hom.toArrow ⋙ G.mapArrow :=
  have key : ∀ {a b : A} (u : a ⟶ b), F'.map (G.map u)
      = eqToHom (Functor.congr_obj hGH a) ≫ H.map (F.map u)
        ≫ eqToHom (Functor.congr_obj hGH b).symm := fun u => Functor.congr_hom hGH u
  NatTrans.toArrow_congr (Functor.whiskerLeft G (F'.invOfPreimageUnit r' θ').hom)
    (Functor.whiskerRight (F.invOfPreimageUnit r θ).hom G) rfl
    (invOfPreimageUnit_square F r θ F' r' θ' G H hGH hr e hθ)
    fun Z => F'.map_injective (by
      simp only [comp_obj, id_obj, invOfPreimage_obj, whiskerLeft_app, invOfPreimageUnit_hom_app,
        map_preimage, eqToHom_refl, whiskerRight_app, Category.id_comp, map_comp, key,
        eqToHom_map]
      rw [invOfPreimage_iso_congr F' r' θ'
        (show F'.obj (G.obj Z) = H.obj (F.obj Z) from Functor.congr_obj hGH Z), hθ (F.obj Z)]
      simp)

end Square

end Functor

end CategoryTheory
