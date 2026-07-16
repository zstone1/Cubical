import CubeChains.Foundations.DeckSequence
import CubeChains.Foundations.NerveQuot
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Foundations/DeckExact — the full short exact sequence of a regular groupoid covering

Builds on `DeckSequence` (monodromy endpoint `endpt`, middle exactness, injectivity) to package the
**deck transformation homomorphism** `deck : Aut(mk ⟦x⟧) →* G` and its surjectivity, giving the
short exact sequence

```
1 → π₁(FreeGroupoid P, x) → π₁(FreeGroupoid (QuotCat P G), ⟦x⟧) → G → 1.
```

The engine is `G`-equivariance of unique lifting: `smulFunctor g` commutes with `quotFunctor`
(`smulFunctor_comp_quotFunctor`), so applying `g` to a lift is again a lift, and the lift endpoint
transforms by `g`.  Composition of loops multiplies monodromy (`liftPS_comp` + equivariance);
surjectivity is connectivity of the fibre.
-/

open CategoryTheory CategoryTheory.FreeGroupoid Quiver Relation

namespace OrderQuotient

open MulAction QuotCat

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-! ## `G`-equivariance of the covering

`smulFunctor g` is a deck transformation: it commutes with `quotFunctor`, so its symmetrification
composes with `φ = quotFunctor.symmetrify` back to `φ`. -/

/-- Symmetrification is functorial: it commutes with prefunctor composition. -/
theorem symmetrify_comp_gen {U V W : Type*} [Quiver U] [Quiver V] [Quiver W]
    (F : U ⥤q V) (H : V ⥤q W) :
    F.symmetrify ⋙q H.symmetrify = (F ⋙q H).symmetrify := by
  refine Prefunctor.ext (fun _ => rfl) (fun X Y e => ?_)
  cases e <;> rfl

/-- The symmetrified deck transformation composed with `φ` is `φ` again. -/
theorem symmetrify_smul_comp (g : G) :
    (smulFunctor g).toPrefunctor.symmetrify ⋙q
        (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify
      = (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify := by
  rw [symmetrify_comp_gen]
  exact congrArg (fun F : P ⥤ QuotCat P G => F.toPrefunctor.symmetrify)
    (smulFunctor_comp_quotFunctor g)

/-- **Equivariance of `φ.mapPath`.**  Translating a path upstairs by `g` and projecting is the same
downstairs word as projecting directly (heterogeneously in the shifted endpoints). -/
theorem phi_mapPath_smul_heq (g : G) {a b : Quiver.Symmetrify P}
    (p : Quiver.Path a b) :
    HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
          ((smulFunctor g).toPrefunctor.symmetrify.mapPath p))
        ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath p) := by
  rw [← Prefunctor.mapPath_comp_apply]
  exact congr_arg_heq (fun ψ : (Quiver.Symmetrify P) ⥤q (Quiver.Symmetrify (QuotCat P G)) =>
    ψ.mapPath p) (symmetrify_smul_comp g)

/-- The `φ`-image of a lift is (heterogeneously) the word it lifts. -/
theorem phi_mapPath_lift_heq (x : P)
    (w : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)) :
    HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath (liftPS x ⟨_, w⟩).2)
      w := by
  have hsym : pathLiftEquiv (G := G) (P := P) x (liftPS x ⟨_, w⟩) = ⟨_, w⟩ :=
    (pathLiftEquiv (G := G) (P := P) x).apply_symm_apply _
  rw [pathLiftEquiv_apply] at hsym
  exact (Sigma.ext_iff.mp hsym).2

/-- HEq congruence for `mapPath` under an endpoint move. -/
theorem mapPath_heq_congr {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V)
    {a b b' : U} (hb : b = b') {p : Quiver.Path a b} {p' : Quiver.Path a b'} (h : HEq p p') :
    HEq (F.mapPath p) (F.mapPath p') := by
  subst hb; rw [eq_of_heq h]

/-! ## The monodromy homomorphism `deck` -/

/-- The monodromy of a loop `γ` at `⟦x⟧`, on morphisms: the deck element carrying `x` to the lift
endpoint. -/
noncomputable def deckM (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) : G :=
  align (endpt x γ) x (mk_endpt x γ)

@[simp] theorem deckM_smul (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    deckM x γ • x = endpt x γ :=
  align_smul _ _ _

/-- The monodromy of the identity loop is trivial. -/
theorem deckM_one (x : P) :
    deckM x (𝟙 (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))) = 1 := by
  have h : endpt x (𝟙 (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))) = x :=
    (mem_range_mapAut_iff x _).mp ⟨𝟙 _, CategoryTheory.Functor.map_id _ _⟩
  exact (align_eq (endpt x _) x (mk_endpt x _) 1 (by rw [one_smul, h])).symm

/-- **Composite endpoint.**  `endpt x (γ ≫ δ) = deckM x γ • endpt x δ`.  The lift of `γ ≫ δ` is the
lift of `γ` then the `deckM γ`-translate of the lift of `δ` (`liftPS_comp` + equivariance). -/
theorem endpt_comp (x : P)
    (γ δ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    endpt x (γ ≫ δ) = deckM x γ • endpt x δ := by
  have hcomp : (wordFunctor (QuotCat P G)).map
      (((wordFunctor (QuotCat P G)).preimage γ).comp ((wordFunctor (QuotCat P G)).preimage δ))
      = γ ≫ δ := by
    rw [show ((wordFunctor (QuotCat P G)).preimage γ).comp ((wordFunctor (QuotCat P G)).preimage δ)
        = ((wordFunctor (QuotCat P G)).preimage γ) ≫ ((wordFunctor (QuotCat P G)).preimage δ)
        from rfl, Functor.map_comp]
    congr 1 <;> exact (wordFunctor (QuotCat P G)).map_preimage _
  have hgg : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
        (((liftPS x ⟨_, (wordFunctor (QuotCat P G)).preimage γ⟩).2).cast rfl (deckM_smul x γ).symm))
      ((wordFunctor (QuotCat P G)).preimage γ) := by
    rw [mapPath_cast]
    exact (Quiver.Path.cast_heq rfl _ _).trans (phi_mapPath_lift_heq x _)
  have hdd : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
        ((smulFunctor (deckM x γ)).toPrefunctor.symmetrify.mapPath
          (liftPS x ⟨_, (wordFunctor (QuotCat P G)).preimage δ⟩).2))
      ((wordFunctor (QuotCat P G)).preimage δ) :=
    (phi_mapPath_smul_heq (deckM x γ) _).trans (phi_mapPath_lift_heq x _)
  have hlc := liftPS_comp x (mk_smul_eq (deckM x γ) x)
    ((mk_smul_eq (deckM x γ) (endpt x δ)).trans (mk_endpt x δ)) hgg hdd
  rw [endpt_spec x (γ ≫ δ) hcomp]
  change (liftPS x ⟨_, ((wordFunctor (QuotCat P G)).preimage γ).comp
    ((wordFunctor (QuotCat P G)).preimage δ)⟩).1 = deckM x γ • endpt x δ
  exact congrArg Sigma.fst hlc

/-- **Monodromy is multiplicative** for composition of loops. -/
theorem deckM_comp (x : P)
    (γ δ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    deckM x (γ ≫ δ) = deckM x γ * deckM x δ :=
  (align_eq (endpt x (γ ≫ δ)) x (mk_endpt x (γ ≫ δ)) (deckM x γ * deckM x δ)
    (by rw [mul_smul, deckM_smul x δ, ← endpt_comp])).symm

/-- Trivial monodromy is exactly a lift that returns to base. -/
theorem deckM_eq_one_iff (x : P)
    (γ : (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) ⟶ mk (Quotient.mk'' x)) :
    deckM x γ = 1 ↔ endpt x γ = x := by
  constructor
  · intro h
    have := deckM_smul x γ
    rw [h, one_smul] at this
    exact this.symm
  · intro h
    exact (align_eq (endpt x γ) x (mk_endpt x γ) 1 (by rw [one_smul]; exact h.symm)).symm

/-! ## The deck homomorphism `Aut(mk ⟦x⟧) →* G`

`Aut` multiplies by `≪≫` (reverse composition), while `deckM` is covariant for `≫`; reading the
monodromy off the **inverse** iso absorbs the reversal, giving a genuine homomorphism. -/

/-- **The deck-transformation homomorphism.** -/
noncomputable def deck (x : P) :
    Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)) →* G where
  toFun a := deckM x a.inv
  map_one' := by
    change deckM x (1 : Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))).inv = 1
    rw [show (1 : Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))).inv = 𝟙 _ from rfl]
    exact deckM_one x
  map_mul' a b := by
    show deckM x (a * b).inv = deckM x a.inv * deckM x b.inv
    rw [show (a * b).inv = a.inv ≫ b.inv from by rw [Aut.Aut_mul_def, Iso.trans_inv], deckM_comp]

@[simp] theorem deck_apply (x : P)
    (a : Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))) :
    deck x a = deckM x a.inv := rfl

/-! ## Surjectivity of the monodromy

Given a path from `x` to `g • x` upstairs (connectivity of the fibre), its projection is a loop at
`⟦x⟧` whose monodromy is `g`. -/

/-- Re-casting a word's endpoint does not move the lift endpoint. -/
theorem endptW_cast_target (x : P) {D D' : Quiver.Symmetrify (QuotCat P G)} (h : D = D')
    (p : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x) D) :
    endptW x (p.cast rfl h) = endptW x p := by
  subst h
  rw [Quiver.Path.cast_rfl_rfl]

/-- **Surjectivity of `deck`.**  If the fibre `G • x` is connected upstairs (a path `x ⟶ g • x` for
every `g`), the monodromy hits every `g`. -/
theorem deck_surjective (x : P)
    (hconn : ∀ g : G, Nonempty ((mk x : FreeGroupoid P) ⟶ mk (g • x))) :
    Function.Surjective (deck (G := G) x) := by
  intro g
  obtain ⟨a⟩ := hconn g
  set w := @Quiver.Path.cast (Quiver.Symmetrify (QuotCat P G))
      (Quiver.symmetrifyQuiver (QuotCat P G))
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj (g • x))
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj x)
      rfl (mk_smul_eq g x)
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
        ((wordFunctor P).preimage a)) with hw
  have hendβ : endpt x ((wordFunctor (QuotCat P G)).map w) = g • x := by
    rw [show endpt x ((wordFunctor (QuotCat P G)).map w) = endptW x w from endpt_spec x _ rfl,
      hw, endptW_cast_target, endptW_mapPath]
  have hdeckβ : deckM x ((wordFunctor (QuotCat P G)).map w) = g :=
    (align_eq (endpt x _) x (mk_endpt x _) g (by rw [hendβ])).symm
  refine ⟨(CategoryTheory.Groupoid.isoEquivHom
    (X := (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G)))
    (Y := mk (Quotient.mk'' x))).symm ((wordFunctor (QuotCat P G)).map w) |>.symm, ?_⟩
  rw [deck_apply]
  exact hdeckβ

/-! ## Exactness at the middle: `ker(deck) = range(FreeGroupoid.map quotFunctor)` -/

/-- Loop and its inverse have simultaneously trivial monodromy. -/
theorem endpt_inv_iff (x : P)
    (a : Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))) :
    endpt x a.inv = x ↔ endpt x a.hom = x := by
  rw [← deckM_eq_one_iff, ← deckM_eq_one_iff]
  have hkey : deckM x a.hom * deckM x a.inv = 1 := by
    rw [← deckM_comp, show a.hom ≫ a.inv = 𝟙 _ from a.hom_inv_id, deckM_one]
  constructor
  · intro h; rw [h, mul_one] at hkey; exact hkey
  · intro h; rw [h, one_mul] at hkey; exact hkey

/-- Vertex-group form of middle exactness: `a` is in the image iff its lift is a loop. -/
theorem mem_range_mapAut_aut_iff (x : P)
    (a : Aut (mk (Quotient.mk'' x) : FreeGroupoid (QuotCat P G))) :
    a ∈ ((CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).mapAut (mk x)).range
      ↔ endpt x a.hom = x := by
  constructor
  · intro ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
    exact (mem_range_mapAut_iff x _).mp ⟨b.hom, rfl⟩
  · intro h
    obtain ⟨f, hf⟩ := (mem_range_mapAut_iff x a.hom).mpr h
    exact MonoidHom.mem_range.mpr ⟨(CategoryTheory.Groupoid.isoEquivHom
      (X := (mk x : FreeGroupoid P)) (Y := mk x)).symm f, Iso.ext hf⟩

/-- **Middle exactness of the deck sequence.**  The kernel of the monodromy is exactly the image of
`FreeGroupoid.map quotFunctor` on the vertex group. -/
theorem deck_ker_eq_range (x : P) :
    (deck x).ker
      = ((FreeGroupoid.map (quotFunctor (G := G) (P := P))).mapAut (mk x)).range := by
  ext a
  rw [MonoidHom.mem_ker, deck_apply, deckM_eq_one_iff, endpt_inv_iff]
  exact (mem_range_mapAut_aut_iff x a).symm

end OrderQuotient
