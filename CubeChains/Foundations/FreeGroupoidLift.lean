import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Foundations/FreeGroupoidLift — the free groupoid's universal property, with parameters

`FreeGroupoid.lift` is **strict**: `lift_spec` and `lift_unique` are equalities.  That strictness is
lost if a functor out of a *product* of free groupoids goes through
`freeGroupoidProdEquiv = Localization.uniq`, which is pinned only up to natural iso.

The fix is to lift one variable at a time, keeping the other as a parameter.  A functor category
into a groupoid is a groupoid, so `lift` applies there too, and currying is *strictly* invertible
(`curryingEquiv` is an `Equiv`).  Hence `lift₂`, whose universal property is again an equality.

    lift₂ F : FreeGroupoid C × FreeGroupoid D ⥤ G      (of C).prod (of D) ⋙ lift₂ F = F
-/

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₂} [Category.{v₂} E] {G : Type u₃} [Groupoid.{v₃} G]

/-- Natural transformations into a groupoid are invertible, so a functor category into a groupoid
is a groupoid.  This is what lets `lift` be applied *with parameters*. -/
noncomputable instance functorGroupoid : Groupoid (D ⥤ G) :=
  Groupoid.ofIsIso fun α => NatIso.isIso_of_isIso_app α

namespace FreeGroupoid

/-- Two functors out of a free groupoid agreeing on the generators are **equal**. -/
theorem lift_ext {Φ Ψ : FreeGroupoid C ⥤ G} (h : of C ⋙ Φ = of C ⋙ Ψ) : Φ = Ψ :=
  (lift_unique _ Φ h).trans (lift_unique _ Ψ rfl).symm

/-- A natural transformation out of a free groupoid is pinned by its generator components
(`eq_mk` is `rfl`, so every object *is* a generator). -/
theorem natTrans_ext {Φ Ψ : FreeGroupoid D ⥤ G} {α β : Φ ⟶ Ψ}
    (h : ∀ X : D, α.app (mk X) = β.app (mk X)) : α = β := by
  ext Y
  exact h Y.as.as

/-- `lift`, as a functor of its input. -/
noncomputable def liftFunctor : (D ⥤ G) ⥤ (FreeGroupoid D ⥤ G) where
  obj F := lift F
  map {F₁ F₂} α := (liftNatIso (lift F₁) (lift F₂)
    (eqToIso (lift_spec F₁) ≪≫ asIso α ≪≫ eqToIso (lift_spec F₂).symm)).hom
  map_id F := by
    refine natTrans_ext fun X => ?_
    simp
  map_comp α β := by
    refine natTrans_ext fun X => ?_
    simp

@[simp] theorem liftFunctor_obj (F : D ⥤ G) : (liftFunctor (D := D) (G := G)).obj F = lift F := rfl

@[simp] theorem liftFunctor_map_app {F₁ F₂ : D ⥤ G} (α : F₁ ⟶ F₂) (X : D) :
    ((liftFunctor (D := D) (G := G)).map α).app (mk X) = α.app X := by
  simp [liftFunctor]

/-! ## Lifting out of a product -/

/-- **The product universal property, strictly**: lift the second variable with the first as a
parameter, then the first.  No `Localization.uniq`, so no loss of strictness. -/
noncomputable def lift₂ (F : C × D ⥤ G) : FreeGroupoid C × FreeGroupoid D ⥤ G :=
  Functor.uncurry.obj (lift (Functor.curry.obj F ⋙ liftFunctor))

@[simp] theorem lift₂_obj (F : C × D ⥤ G) (X : C) (Y : D) :
    (lift₂ F).obj (mk X, mk Y) = F.obj (X, Y) := rfl

@[simp] theorem lift₂_map_homMk (F : C × D ⥤ G) {X₁ X₂ : C} {Y₁ Y₂ : D}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (lift₂ F).map ((homMk f, homMk g) : (mk X₁, mk Y₁) ⟶ (mk X₂, mk Y₂))
      = F.map ((f, g) : (X₁, Y₁) ⟶ (X₂, Y₂)) := by
  have hsplit : ((f, g) : ((X₁, Y₁) : C × D) ⟶ (X₂, Y₂))
      = (show ((X₁, Y₁) : C × D) ⟶ (X₂, Y₁) from (f, 𝟙 Y₁))
        ≫ (show ((X₂, Y₁) : C × D) ⟶ (X₂, Y₂) from (𝟙 X₂, g)) := by
    rw [prod_comp]
    simp
  rw [hsplit, F.map_comp]
  simp [lift₂, Functor.uncurry, liftFunctor]

/-- **The universal property, and it is an equality** — unlike `Localization.uniq`. -/
theorem lift₂_spec (F : C × D ⥤ G) : (of C).prod (of D) ⋙ lift₂ F = F := by
  refine Functor.ext (fun X => rfl) fun X₁ X₂ f => ?_
  obtain ⟨c₁, d₁⟩ := X₁
  obtain ⟨c₂, d₂⟩ := X₂
  obtain ⟨u, v⟩ := f
  simp

/-- `lift₂` on a generator paired with an identity — the shape a whiskering produces. -/
@[simp] theorem lift₂_map_id_homMk (F : C × D ⥤ G) (X : C) {Y₁ Y₂ : D} (g : Y₁ ⟶ Y₂) :
    (lift₂ F).map ((𝟙 (mk X), homMk g) : (mk X, mk Y₁) ⟶ (mk X, mk Y₂))
      = F.map ((𝟙 X, g) : (X, Y₁) ⟶ (X, Y₂)) := by
  rw [show (𝟙 (mk X) : mk X ⟶ mk X) = homMk (𝟙 X) from ((of C).map_id X).symm,
    lift₂_map_homMk]

@[simp] theorem lift₂_map_homMk_id (F : C × D ⥤ G) {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : D) :
    (lift₂ F).map ((homMk f, 𝟙 (mk Y)) : (mk X₁, mk Y) ⟶ (mk X₂, mk Y))
      = F.map ((f, 𝟙 Y) : (X₁, Y) ⟶ (X₂, Y)) := by
  rw [show (𝟙 (mk Y) : mk Y ⟶ mk Y) = homMk (𝟙 Y) from ((of D).map_id Y).symm,
    lift₂_map_homMk]

/-- **Two functors out of a product of free groupoids agreeing on the generators are equal.** -/
theorem lift₂_ext {Φ Ψ : FreeGroupoid C × FreeGroupoid D ⥤ G}
    (h : (of C).prod (of D) ⋙ Φ = (of C).prod (of D) ⋙ Ψ) : Φ = Ψ := by
  -- agree on the generators of one variable, with the other held fixed
  have hfix : ∀ (X : C), (Functor.curry.obj Φ).obj (mk X) = (Functor.curry.obj Ψ).obj (mk X) := by
    intro X
    refine lift_ext (C := D) (G := G)
      (Functor.ext (fun Y => Functor.congr_obj h (X, Y)) fun Y₁ Y₂ g => ?_)
    simpa using Functor.congr_hom h (show ((X, Y₁) : C × D) ⟶ (X, Y₂) from (𝟙 X, g))
  refine Functor.curryingEquiv.symm.injective (lift_ext (C := C) (G := FreeGroupoid D ⥤ G) ?_)
  refine Functor.ext hfix fun X₁ X₂ f => ?_
  refine natTrans_ext fun Y => ?_
  simpa [eqToHom_app] using
    Functor.congr_hom h (show ((X₁, Y) : C × D) ⟶ (X₂, Y) from (f, 𝟙 Y))

theorem lift₂_unique (F : C × D ⥤ G) (Φ : FreeGroupoid C × FreeGroupoid D ⥤ G)
    (hΦ : (of C).prod (of D) ⋙ Φ = F) : Φ = lift₂ F :=
  lift₂_ext (Φ := Φ) (Ψ := lift₂ F) (hΦ.trans (lift₂_spec F).symm)

/-- A natural transformation out of a product of free groupoids is pinned by its components at the
generators. -/
theorem natTrans₂_ext {Φ Ψ : FreeGroupoid C × FreeGroupoid D ⥤ G} {α β : Φ ⟶ Ψ}
    (h : ∀ (X : C) (Y : D), α.app (mk X, mk Y) = β.app (mk X, mk Y)) : α = β := by
  ext ⟨X, Y⟩
  exact h X.as.as Y.as.as

/-- **Ext for a triple product** — what the enrichment's associativity axiom needs. -/
theorem lift₃_ext {E' : Type u₂} [Category.{v₂} E']
    {Φ Ψ : FreeGroupoid C × (FreeGroupoid D × FreeGroupoid E') ⥤ G}
    (h : (of C).prod ((of D).prod (of E')) ⋙ Φ
      = (of C).prod ((of D).prod (of E')) ⋙ Ψ) : Φ = Ψ := by
  have hfix : ∀ (X : C), (Functor.curry.obj Φ).obj (mk X) = (Functor.curry.obj Ψ).obj (mk X) := by
    intro X
    refine lift₂_ext (C := D) (D := E') (G := G) (Functor.ext (fun Y => ?_) fun Y₁ Y₂ g => ?_)
    · exact Functor.congr_obj h (X, Y)
    · simpa using Functor.congr_hom h
        (show ((X, Y₁) : C × (D × E')) ⟶ (X, Y₂) from (𝟙 X, g))
  refine Functor.curryingEquiv.symm.injective
    (lift_ext (C := C) (G := FreeGroupoid D × FreeGroupoid E' ⥤ G) ?_)
  refine Functor.ext hfix fun X₁ X₂ f => ?_
  refine natTrans₂_ext fun Y Z => ?_
  simpa [eqToHom_app] using
    Functor.congr_hom h (show ((X₁, Y, Z) : C × (D × E')) ⟶ (X₂, Y, Z) from (f, 𝟙 Y, 𝟙 Z))

/-! ## A terminal object collapses the free groupoid

If `C` has a terminal object `t` then every generator `f : X ⟶ Y` satisfies `f ≫ t_Y = t_X`, so in
the free groupoid `homMk f = τ X ≫ (τ Y)⁻¹`.  Packaging that as a natural iso `𝟭 ≅ const (mk t)` —
which `liftNatIso` builds from its generator components alone — makes *every* hom a singleton.

No nerve, no Gabriel–Zisman: the free groupoid on a category with a terminal object is codiscrete. -/

section Terminal

/-- The generator components of the collapse: `mk X ≅ mk t`, natural by terminality. -/
noncomputable def terminalIso {C : Type u₁} [Category.{v₁} C] (t : C)
    (ht : Limits.IsTerminal t) :
    of C ⋙ 𝟭 (FreeGroupoid C)
      ≅ of C ⋙ (Functor.const (FreeGroupoid C)).obj (mk t) :=
  NatIso.ofComponents (fun X => asIso (homMk (ht.from X)))
    (fun {X Y} f => by
      have h : f ≫ ht.from Y = ht.from X := ht.hom_ext _ _
      have h2 : (of C).map f ≫ (of C).map (ht.from Y) = (of C).map (ht.from X) := by
        rw [← CategoryTheory.Functor.map_comp, h]
      simpa [homMk] using h2)

/-- **A terminal object collapses the free groupoid**: `𝟭 ≅ const (mk t)`. -/
noncomputable def terminalNatIso {C : Type u₁} [Category.{v₁} C] (t : C)
    (ht : Limits.IsTerminal t) :
    𝟭 (FreeGroupoid C) ≅ (Functor.const (FreeGroupoid C)).obj (mk t) :=
  liftNatIso _ _ (terminalIso t ht)

/-- **The free groupoid on a category with a terminal object is codiscrete.**  Every hom is a
singleton — so it has *no loops at all*.  This is what makes a Ch-side invariant vanish over a
serial wedge. -/
theorem subsingleton_hom_of_isTerminal {C : Type u₁} [Category.{v₁} C] (t : C)
    (ht : Limits.IsTerminal t) (X Y : FreeGroupoid C) : Subsingleton (X ⟶ Y) := by
  have η := terminalNatIso t ht
  refine ⟨fun u v => ?_⟩
  have hu : u ≫ η.hom.app Y = η.hom.app X := by simpa using η.hom.naturality u
  have hv : v ≫ η.hom.app Y = η.hom.app X := by simpa using η.hom.naturality v
  exact (cancel_mono (η.hom.app Y)).mp (hu.trans hv.symm)

end Terminal

section Initial

/-- The generator components of the collapse: `mk i ≅ mk X`, natural by initiality. -/
noncomputable def initialIso {C : Type u₁} [Category.{v₁} C] (i : C) (hi : Limits.IsInitial i) :
    of C ⋙ (Functor.const (FreeGroupoid C)).obj (mk i) ≅ of C ⋙ 𝟭 (FreeGroupoid C) :=
  NatIso.ofComponents (fun X => asIso (homMk (hi.to X))) fun {X Y} f => by
    have h : (of C).map (hi.to X) ≫ (of C).map f = (of C).map (hi.to Y) := by
      rw [← Functor.map_comp, hi.hom_ext (hi.to X ≫ f) (hi.to Y)]
    simpa [homMk] using h.symm

/-- **An initial object collapses the free groupoid**: `const (mk i) ≅ 𝟭`. -/
noncomputable def initialNatIso {C : Type u₁} [Category.{v₁} C] (i : C)
    (hi : Limits.IsInitial i) :
    (Functor.const (FreeGroupoid C)).obj (mk i) ≅ 𝟭 (FreeGroupoid C) :=
  liftNatIso _ _ (initialIso i hi)

/-- **The free groupoid on a category with an initial object is codiscrete** — the dual of
`subsingleton_hom_of_isTerminal`, and what makes a principal up-set kill the loops inside it. -/
theorem subsingleton_hom_of_isInitial {C : Type u₁} [Category.{v₁} C] (i : C)
    (hi : Limits.IsInitial i) (X Y : FreeGroupoid C) : Subsingleton (X ⟶ Y) := by
  have η := initialNatIso i hi
  refine ⟨fun u v => ?_⟩
  have hu : η.hom.app X ≫ u = η.hom.app Y := by simpa using (η.hom.naturality u).symm
  have hv : η.hom.app X ≫ v = η.hom.app Y := by simpa using (η.hom.naturality v).symm
  exact (cancel_epi (η.hom.app X)).mp (hu.trans hv.symm)

end Initial

end FreeGroupoid

/-! ## The principal up-set

`↑b` has minimum `b`, so in a thin category it is a full subcategory with an *initial* object, and
the free groupoid on it is codiscrete: a loop staying in `↑b` is the identity — no nerve, no
asphericity. -/

section UpSet

variable {C : Type u₁} [Category.{v₁} C]

/-- The objects `b` maps to. -/
def upSet (b : C) : ObjectProperty C := fun X => Nonempty (b ⟶ X)

instance fullSubcategory_isThin (P : ObjectProperty C) [Quiver.IsThin C] :
    Quiver.IsThin P.FullSubcategory :=
  fun _ _ => ⟨fun _ _ => ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩

/-- `b`, viewed as the least element of `↑b`. -/
def upSetBot (b : C) : (upSet b).FullSubcategory := ⟨b, ⟨𝟙 b⟩⟩

/-- Thinness turns the minimum of `↑b` into an initial object. -/
noncomputable def isInitial_upSetBot [Quiver.IsThin C] (b : C) :
    Limits.IsInitial (upSetBot b) :=
  Limits.IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk X.property.some)
    fun _ _ => Subsingleton.elim _ _

/-- The inclusion `↑b ⥤ C`, on free groupoids. -/
noncomputable def upSetToFree (b : C) :
    FreeGroupoid (upSet b).FullSubcategory ⥤ FreeGroupoid C :=
  FreeGroupoid.map (upSet b).ι

/-- **A loop lying in `↑b` is trivial.** -/
theorem loop_trivial_of_mem_upSet [Quiver.IsThin C] (b : C)
    {x : (upSet b).FullSubcategory} (γ : FreeGroupoid.mk x ⟶ FreeGroupoid.mk x) :
    (upSetToFree b).map γ = 𝟙 _ := by
  haveI := FreeGroupoid.subsingleton_hom_of_isInitial _ (isInitial_upSetBot b)
    (FreeGroupoid.mk x) (FreeGroupoid.mk x)
  rw [Subsingleton.elim γ (𝟙 _), Functor.map_id]

/-! ### The cone map, for loops written out as words

A caller holds a *term* `homMk f₁ ≫ inv (homMk f₂) ≫ ⋯`, not an element of a subcategory.  For
those, rewrite with `cone_comp`/`cone_inv_comp` until the loop is absorbed, then cancel. -/

/-- A generator step out of `↑b` reroots the cone map. -/
theorem cone_comp [Quiver.IsThin C] {b x y : C} (hx : b ⟶ x) (f : x ⟶ y) (hy : b ⟶ y) :
    FreeGroupoid.homMk hx ≫ FreeGroupoid.homMk f = FreeGroupoid.homMk hy := by
  rw [← (FreeGroupoid.of C).map_comp, Subsingleton.elim (hx ≫ f) hy]

/-- The same step run backwards. -/
theorem cone_inv_comp [Quiver.IsThin C] {b x y : C} (hy : b ⟶ y) (f : x ⟶ y) (hx : b ⟶ x) :
    FreeGroupoid.homMk hy ≫ inv (FreeGroupoid.homMk f) = FreeGroupoid.homMk hx := by
  rw [← cone_comp hx f hy, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- A loop fixing the cone map at `b` is trivial. -/
theorem eq_id_of_cone_comp {b x : C} (h : b ⟶ x)
    {γ : FreeGroupoid.mk x ⟶ FreeGroupoid.mk x}
    (hγ : FreeGroupoid.homMk h ≫ γ = FreeGroupoid.homMk h) : γ = 𝟙 _ :=
  (cancel_epi (FreeGroupoid.homMk h)).mp (by simpa using hγ)

end UpSet

end CategoryTheory
