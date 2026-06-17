import CubeChains.Operations.Deformation
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# The groupoid reflection is the weakest target, and what produces `𝟭 ⟹ Φ`

Two results behind the operations theory.

## Part 1 — the groupoid reflection `M = Ch(K)[Ch(K)⁻¹]` is the weakest target

A homotopy invariant is a functor `H : Cat ⥤ 𝒯`, and an operation's leg `ℓ` is a
weak equivalence when `H(Ch ℓ)` is invertible in `𝒯`.  Three rungs:

```
Cat  ⟶  Grpd  ⟶  Type
        (𝑟)        (π₀)
```

* `Cat`-equivalence ⟹ `Grpd`-equivalence (`freeGroupoid_map_isEquivalence`): the
  reflection is *coarser* than equivalence of categories.
* `Grpd`-equivalence ⟹ `π₀`-bijection, because **π₀ factors through the reflection**
  (`connectedComponentsFreeGroupoidEquiv`): so the reflection is *finer* than `π₀`.
* `M = FreeGroupoid (Ch K)` is the localization at **all** morphisms
  (`(FreeGroupoid.of _).IsLocalization ⊤`, from mathlib) — the *universal* functor
  inverting every morphism.  Its hom-sets are exactly the zigzags of `Ch K`.

So the reflection is the **initial** invariant that inverts the morphisms of `Ch K`
(hence retains the zigzags as actual arrows of `M`); `π₀` is a further truncation
that keeps only whether a zigzag exists.  That is the precise sense of "weakest".

## Part 2 — a span alone does not give `𝟭 ⟹ Φ`; a homotopy between the legs does

A span `K ←ℓ E →r K` lifts to the transport `Φ = (Ch ℓ)⁻¹ ⋙ (Ch r)`, a self-map of
`Ch K`, but to turn a fixed chain `p` into an actual *zigzag* `p ⇝ Φ p` you need a
natural transformation `𝟭 ⟹ Φ`.  `transportTransf` shows the exact extra datum that
suffices: **a natural transformation `η : Ch ℓ ⟹ Ch r` between the two legs** —
geometrically a (directed) cubical homotopy between `ℓ` and `r` (a cylinder
`E ⊗ □¹ → K`).  From `η` we build `𝟭 ⟹ Φ`, hence for each chain `p` a morphism
`p ⟶ Φ p` in `Ch K` (an arrow of `M`).
-/

open CategoryTheory

namespace Operations

/-! ## Part 2: the extra datum producing `𝟭 ⟹ Φ` -/

section Transport

variable {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]

/-- **What a span lacks.**  Given the left leg `L` (an equivalence) and *any* natural
transformation `η : L ⟶ R` to the right leg, the transport `Φ = L⁻¹ ⋙ R` receives a
natural transformation from the identity: `𝟭 ⟹ Φ`.

(`η` is exactly the data a bare span omits; geometrically it is a homotopy `ℓ ≃ r`
between the legs — a cylinder `E ⊗ □¹ → K`.) -/
noncomputable def transportTransf (L R : 𝒜 ⥤ ℬ) [L.IsEquivalence] (η : L ⟶ R) :
    𝟭 ℬ ⟶ L.inv ⋙ R :=
  L.asEquivalence.counitIso.inv ≫ Functor.whiskerLeft L.inv η

/-- **The lifted zigzag at a fixed chain.**  For each chain `p`, `η : L ⟶ R` yields a
genuine morphism `p ⟶ Φ p` in `Ch K` — i.e. an arrow of `M = Ch(K)[Ch(K)⁻¹]`, the
homotopy of d-paths the operation realizes at `p`. -/
noncomputable def transportMor (L R : 𝒜 ⥤ ℬ) [L.IsEquivalence] (η : L ⟶ R) (p : ℬ) :
    p ⟶ (L.inv ⋙ R).obj p :=
  (transportTransf L R η).app p

end Transport

/-! ## Part 1: the groupoid reflection is the weakest target -/

section Weakest

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- `FreeGroupoid.map` preserves natural isomorphisms. -/
noncomputable def freeGroupoidMapNatIso {F G : C ⥤ D} (α : F ≅ G) :
    FreeGroupoid.map F ≅ FreeGroupoid.map G :=
  FreeGroupoid.liftNatIso _ _ (Functor.isoWhiskerRight α (FreeGroupoid.of D))

/-- **`Cat`-equivalence ⟹ `Grpd`-equivalence.**  The groupoid reflection sends an
equivalence of categories to an equivalence of groupoids, so its class of weak
equivalences contains `Homotopical`'s — the reflection is *coarser* than `Cat`. -/
theorem freeGroupoid_map_isEquivalence (F : C ⥤ D) [F.IsEquivalence] :
    (FreeGroupoid.map F).IsEquivalence := by
  let e := F.asEquivalence
  refine Functor.IsEquivalence.mk' (FreeGroupoid.map e.inverse) ?_ ?_
  · exact (FreeGroupoid.mapId C).symm ≪≫ freeGroupoidMapNatIso e.unitIso ≪≫
      FreeGroupoid.mapComp e.functor e.inverse
  · exact (FreeGroupoid.mapComp e.inverse e.functor).symm ≪≫
      freeGroupoidMapNatIso e.counitIso ≪≫ FreeGroupoid.mapId D

/-- Zigzag-connected objects in a discrete category are equal. -/
theorem zigzag_discrete_as {X : Type*} {a b : Discrete X} (h : Zigzag a b) : a.as = b.as := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rcases hbc with hf | hf
      · exact ih.trans (Discrete.eq_of_hom hf.some)
      · exact ih.trans (Discrete.eq_of_hom hf.some).symm

/-- **π₀ factors through the groupoid reflection.**  The localization
`of C : C ⥤ FreeGroupoid C` induces a *bijection* on connected components: passing to
the free groupoid adds inverses but neither merges nor splits components.  Hence a
`Grpd`-equivalence is in particular a `π₀`-bijection — the reflection is *finer* than
`π₀`, and `π₀` is a strict further truncation that forgets the morphisms (= zigzags). -/
theorem of_mapConnectedComponents_bijective (C : Type*) [Category C] :
    Function.Bijective (FreeGroupoid.of C).mapConnectedComponents := by
  constructor
  · -- injective, via the factorization through `Discrete (π₀ C)`
    intro a b hab
    obtain ⟨X, rfl⟩ := a.exists_rep
    obtain ⟨Y, rfl⟩ := b.exists_rep
    rw [Functor.mapConnectedComponents_mk, Functor.mapConnectedComponents_mk] at hab
    have hz : Zigzag ((FreeGroupoid.of C).obj X) ((FreeGroupoid.of C).obj Y) := Quotient.exact hab
    let D₀ : C ⥤ Discrete (ConnectedComponents C) :=
      ConnectedComponents.functorToDiscrete (ConnectedComponents C) id
    let L : FreeGroupoid C ⥤ Discrete (ConnectedComponents C) := FreeGroupoid.lift D₀
    have hspec : FreeGroupoid.of C ⋙ L = D₀ := FreeGroupoid.lift_spec D₀
    have hz2 : Zigzag (D₀.obj X) (D₀.obj Y) := by
      have h := zigzag_obj_of_zigzag L hz
      simpa only [← Functor.comp_obj, hspec] using h
    exact zigzag_discrete_as hz2
  · -- surjective: every object of `FreeGroupoid C` is `of`-of something
    intro y
    obtain ⟨Y, rfl⟩ := y.exists_rep
    refine ⟨Quotient.mk _ (Y.as.as), ?_⟩
    rw [Functor.mapConnectedComponents_mk]
    congr 1

/-- `π₀` packaged as a bijection `ConnectedComponents C ≃ ConnectedComponents (FreeGroupoid C)`. -/
noncomputable def connectedComponentsFreeGroupoidEquiv (C : Type*) [Category C] :
    ConnectedComponents C ≃ ConnectedComponents (FreeGroupoid C) :=
  Equiv.ofBijective _ (of_mapConnectedComponents_bijective C)

/-- **The reflection is the universal inverter — the weakest target.**  For any chain
category `𝒞 = Ch K`, the groupoid reflection `M = FreeGroupoid 𝒞` is the localization
of `𝒞` at *all* its morphisms.  So `M = 𝒞[𝒞⁻¹]`, its hom-sets are exactly the zigzags
of `𝒞`, and (universal property) any groupoid-valued functor inverting the morphisms
of `𝒞` factors uniquely through `M`: `M` is **initial** among such targets, hence the
weakest one that still retains the zigzags as actual arrows. -/
theorem groupoidReflection_isLocalization (𝒞 : Type*) [Category 𝒞] :
    (FreeGroupoid.of 𝒞).IsLocalization ⊤ := inferInstance

end Weakest

end Operations
