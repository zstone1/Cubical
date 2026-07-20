import CubeChains.Foundations.Box
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Foundations/GluePushout

A **computable** pushout of presheaves.  Mathlib's `pushout f g = colimit (span f g)`
is `Classical.choice`-opaque (so `noncomputable`, and its cells never `#eval`).  Here we
assemble the pushout pointwise from the explicit `Types.Pushout` (a plain `Quot`, with
`inl/inr = Quot.mk` and `desc = Quot.lift`) via `combineCocones`, so the object, its
inclusions, and `desc` all reduce.

`Glue.isPushout f g : IsPushout f g (Glue.inl f g) (Glue.inr f g)` is the whole point:
everything downstream is phrased through the pushout *universal property*, and transfers
verbatim.  The API mirrors mathlib's `pushout.inl`/`inr`/`desc`/`condition`/`hom_ext`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Glue

variable {S A B : PrecubicalSet} (f : S ⟶ A) (g : S ⟶ B)

/-- Pointwise computable colimit cocone (the explicit `Types.Pushout`), transported onto
the flip diagram `(span f g).flip.obj k` via `diagramIsoSpan`. -/
def ptCocone (k : Boxᵒᵖ) : ColimitCocone ((span f g).flip.obj k) where
  cocone := (Cocone.precompose (diagramIsoSpan ((span f g).flip.obj k)).hom).obj
    (Types.Pushout.cocone (((span f g).flip.obj k).map WalkingSpan.Hom.fst)
      (((span f g).flip.obj k).map WalkingSpan.Hom.snd))
  isColimit := (IsColimit.precomposeHomEquiv (diagramIsoSpan ((span f g).flip.obj k)) _).symm
    (Types.Pushout.isColimitCocone _ _)

/-- The assembled pushout cocone in the presheaf category. -/
def cocone : Cocone (span f g) := combineCocones (span f g) (ptCocone f g)

/-- The computable glued presheaf `A ⊔_S B`. -/
def gluePsh : PrecubicalSet := (cocone f g).pt

/-- The assembled cocone is a colimit (pointwise it is `Types.Pushout.isColimitCocone`). -/
def isColimit : IsColimit (cocone f g) := combinedIsColimit (span f g) (ptCocone f g)

/-- Left inclusion `A ⟶ A ⊔_S B` (computable: pointwise `Quot.mk ∘ Sum.inl`). -/
def inl : A ⟶ gluePsh f g := (cocone f g).ι.app WalkingSpan.left

/-- Right inclusion `B ⟶ A ⊔_S B`. -/
def inr : B ⟶ gluePsh f g := (cocone f g).ι.app WalkingSpan.right

/-- **The universal property.**  Every consumer downstream is phrased through this. -/
theorem isPushout : IsPushout f g (inl f g) (inr f g) := by
  have h := IsPushout.of_isColimit_cocone (isColimit f g)
  simpa only [inl, inr] using h

/-- The gluing square commutes. -/
theorem condition : f ≫ inl f g = g ≫ inr f g := (isPushout f g).w

/-- The computable descent map (a map *out* of the glue), `f ≫ h = g ≫ k ⟹ A ⊔_S B ⟶ W`.
`f`, `g` are implicit (pinned by `w`), so call sites read like `pushout.desc h k w`. -/
def desc {W : PrecubicalSet} {f : S ⟶ A} {g : S ⟶ B} (h : A ⟶ W) (k : B ⟶ W)
    (w : f ≫ h = g ≫ k) : gluePsh f g ⟶ W :=
  (isColimit f g).desc (PushoutCocone.mk h k w)

@[reassoc (attr := simp)]
theorem inl_desc {f : S ⟶ A} {g : S ⟶ B} {W : PrecubicalSet}
    (h : A ⟶ W) (k : B ⟶ W) (w : f ≫ h = g ≫ k) :
    inl f g ≫ desc h k w = h :=
  (isColimit f g).fac (PushoutCocone.mk h k w) WalkingSpan.left

@[reassoc (attr := simp)]
theorem inr_desc {f : S ⟶ A} {g : S ⟶ B} {W : PrecubicalSet}
    (h : A ⟶ W) (k : B ⟶ W) (w : f ≫ h = g ≫ k) :
    inr f g ≫ desc h k w = k :=
  (isColimit f g).fac (PushoutCocone.mk h k w) WalkingSpan.right

/-- Maps out of the glue are pinned by their restrictions to `A` and `B`. -/
theorem hom_ext {f : S ⟶ A} {g : S ⟶ B} {W : PrecubicalSet} {a b : gluePsh f g ⟶ W}
    (hl : inl f g ≫ a = inl f g ≫ b) (hr : inr f g ≫ a = inr f g ≫ b) : a = b :=
  (isPushout f g).hom_ext hl hr

-- Seal the heavy internals: like the opaque `Classical.choice` inside mathlib's `pushout`,
-- this stops `isDefEq`/`whnf` from unfolding the `combineCocones` tower during elaboration
-- (proofs go through the API lemmas above).  The compiler ignores `irreducible`, so the
-- object still `#eval`s.
attribute [irreducible] gluePsh inl inr desc

-- `inl` is pointwise `Quot.mk ∘ Sum.inl` (exposes the `Quot` for computable readback).
unseal gluePsh inl in
theorem inl_app {f : S ⟶ A} {g : S ⟶ B} (o : Boxᵒᵖ) (x : A.obj o) :
    (inl f g).app o x = Quot.mk _ (Sum.inl x) := rfl

-- `inr` is pointwise `Quot.mk ∘ Sum.inr`.
unseal gluePsh inr in
theorem inr_app {f : S ⟶ A} {g : S ⟶ B} (o : Boxᵒᵖ) (y : B.obj o) :
    (inr f g).app o y = Quot.mk _ (Sum.inr y) := rfl

-- **Computable cell-level descent.**  `desc` descends into a *presheaf*; when the target is a
-- bare type (an altitude `… → ℤ`, say) you need this instead — the pointwise `Quot.lift`.  Using
-- mathlib's `IsPushout.desc` here would silently make the caller `noncomputable`.
unseal gluePsh in
def descCell {W : Type} {f : S ⟶ A} {g : S ⟶ B} (o : Boxᵒᵖ)
    (h : A.obj o → W) (k : B.obj o → W)
    (w : ∀ s : S.obj o, h (f.app o s) = k (g.app o s)) :
    (gluePsh f g).obj o → W :=
  Quot.lift (fun x => match x with | Sum.inl a => h a | Sum.inr b => k b)
    (by rintro _ _ ⟨t⟩; exact w t)

unseal gluePsh inl in
@[simp] theorem descCell_inl {W : Type} {f : S ⟶ A} {g : S ⟶ B} (o : Boxᵒᵖ)
    {h : A.obj o → W} {k : B.obj o → W} {w} (x : A.obj o) :
    descCell o h k w ((inl f g).app o x) = h x := rfl

unseal gluePsh inr in
@[simp] theorem descCell_inr {W : Type} {f : S ⟶ A} {g : S ⟶ B} (o : Boxᵒᵖ)
    {h : A.obj o → W} {k : B.obj o → W} {w} (y : B.obj o) :
    descCell o h k w ((inr f g).app o y) = k y := rfl

end Glue
