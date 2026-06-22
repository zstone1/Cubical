import CubeChains.Cobordisms.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Extensive

/-!
# Cobordisms/Union — disjoint union `⊔` of cospans (M4, the `⊔` operation)

The **disjoint union** of two cospans, built on the binary coproduct of
`PrecubicalSet`.  Given `C₁ : Cospan X Y` and `C₂ : Cospan X' Y'`, their union is a
cospan `X ⨿ X' ⇒ Y ⨿ Y'` whose middle is `C₁.mid ⨿ C₂.mid` and whose legs are the
levelwise-disjoint `coprod.map`s of the two pairs of legs.  This is pure category
theory on coproducts — **independent of the tensor/cylinder**.

The two facts that make it work both come from `PrecubicalSet` being a presheaf
topos (`Boxᵒᵖ ⥤ Type`), hence **finitary extensive**:

* `coprod.map` of two monos is again mono — reduced to the cell level
  (`NatTrans.mono_iff_mono_app` + `mono_iff_injective`) and transported through the
  levelwise coproduct bijection `FunctorToTypes.binaryCoproductEquiv`, under which
  `coprod.map f g` acts as `Sum.map (f.app _) (g.app _)`; `Sum.map` of injectives is
  injective.
* The legs of the union are disjoint — at the cell level, `inl` lands in the `X`/`X'`
  summands (`Sum.inl`) and `inr` in the `Y`/`Y'` summands (`Sum.inr`).  A collision
  forces matching summands, where the componentwise `LegsDisjoint` hypotheses for
  `C₁` and `C₂` apply.  (`Sum.inl x ≠ Sum.inr y` rules out the cross terms.)

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Cospan`, mathlib
`BinaryProducts`/`FunctorToTypes`/`Extensive`.

Commutativity/associativity of `union` (up to the coproduct iso) is genuine
coherence and is **deferred to M4/M5**; it is not developed here.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace PrecubicalSet

universe u

variable {X Y X' Y' : PrecubicalSet}

/-! ### `coprod.map` of monos is mono

`PrecubicalSet = Boxᵒᵖ ⥤ Type` is finitary extensive (a functor category into the
extensive category `Type`), so coproduct injections are mono and coproducts are
levelwise the `Type`-coproduct.  A cell of `(A ⨿ B).cells n` is, up to the canonical
bijection `FunctorToTypes.binaryCoproductEquiv`, an element of the `Type`-coproduct
`A.cells n ⊕ B.cells n`; the inclusions `coprodInl`/`coprodInr` correspond to
`Sum.inl`/`Sum.inr`.  We use this to:
* enumerate cells of `A ⨿ B` (every cell is a `coprodInl` or a `coprodInr`);
* see `coprodInl`/`coprodInr` are injective with disjoint images;
* compute the action of `coprod.map f g` on each inclusion via naturality;

and conclude `coprod.map f g` mono by injectivity at the cell level. -/

/-- `coprodInl` is the cell-level action of the categorical left injection `coprod.inl`. -/
theorem coprodInl_eq_inl_app {A B : PrecubicalSet} {n : ℕ} (a : A.cells n) :
    (FunctorToTypes.coprodInl a : (A ⨿ B).cells n)
      = (coprod.inl : A ⟶ A ⨿ B).app (op (Box.ob n)) a := by
  have h := NatTrans.congr_app
    (FunctorToTypes.inl_comp_binaryCoproductIso_inv (F := A) (G := B)) (op (Box.ob n))
  apply_fun (fun φ => φ a) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h.symm

/-- `coprodInr` is the cell-level action of the categorical right injection `coprod.inr`. -/
theorem coprodInr_eq_inr_app {A B : PrecubicalSet} {n : ℕ} (b : B.cells n) :
    (FunctorToTypes.coprodInr b : (A ⨿ B).cells n)
      = (coprod.inr : B ⟶ A ⨿ B).app (op (Box.ob n)) b := by
  have h := NatTrans.congr_app
    (FunctorToTypes.inr_comp_binaryCoproductIso_inv (F := A) (G := B)) (op (Box.ob n))
  apply_fun (fun φ => φ b) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h.symm

/-- Every `n`-cell of `A ⨿ B` is either `coprodInl a` or `coprodInr b`. -/
theorem coprod_cell_cases {A B : PrecubicalSet} {n : ℕ} (z : (A ⨿ B).cells n) :
    (∃ a, z = FunctorToTypes.coprodInl a) ∨ (∃ b, z = FunctorToTypes.coprodInr b) := by
  rcases h : FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n)) z with a | b
  · refine Or.inl ⟨a, ?_⟩
    apply (FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n))).injective
    simpa [FunctorToTypes.coprodInl] using h
  · refine Or.inr ⟨b, ?_⟩
    apply (FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n))).injective
    simpa [FunctorToTypes.coprodInr] using h

/-- `coprodInl` is injective on `n`-cells (it is `binaryCoproductEquiv.symm ∘ Sum.inl`). -/
theorem coprodInl_injective {A B : PrecubicalSet} {n : ℕ} :
    Function.Injective (fun a : A.cells n => (FunctorToTypes.coprodInl a : (A ⨿ B).cells n)) := by
  intro a a' h
  have := congrArg (FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n))) h
  simpa [FunctorToTypes.coprodInl] using this

/-- `coprodInr` is injective on `n`-cells. -/
theorem coprodInr_injective {A B : PrecubicalSet} {n : ℕ} :
    Function.Injective (fun b : B.cells n => (FunctorToTypes.coprodInr b : (A ⨿ B).cells n)) := by
  intro b b' h
  have := congrArg (FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n))) h
  simpa [FunctorToTypes.coprodInr] using this

/-- `coprodInl` and `coprodInr` have disjoint images on `n`-cells. -/
theorem coprodInl_ne_coprodInr {A B : PrecubicalSet} {n : ℕ}
    (a : A.cells n) (b : B.cells n) :
    (FunctorToTypes.coprodInl a : (A ⨿ B).cells n) ≠ FunctorToTypes.coprodInr b := by
  intro h
  have := congrArg (FunctorToTypes.binaryCoproductEquiv A B (op (Box.ob n))) h
  simp only [FunctorToTypes.coprodInl, FunctorToTypes.coprodInr] at this
  simp at this

/-- The action of `coprod.map f g` on a left inclusion: it commutes with `coprodInl`. -/
theorem coprodMap_coprodInl {A B A' B' : PrecubicalSet} (f : A ⟶ B) (g : A' ⟶ B')
    {n : ℕ} (a : A.cells n) :
    (coprod.map f g).app (op (Box.ob n)) (FunctorToTypes.coprodInl a)
      = FunctorToTypes.coprodInl (f.app (op (Box.ob n)) a) := by
  rw [coprodInl_eq_inl_app, coprodInl_eq_inl_app]
  have h := NatTrans.congr_app (coprod.inl_map f g) (op (Box.ob n))
  apply_fun (fun φ => φ a) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h

/-- The action of `coprod.map f g` on a right inclusion: it commutes with `coprodInr`. -/
theorem coprodMap_coprodInr {A B A' B' : PrecubicalSet} (f : A ⟶ B) (g : A' ⟶ B')
    {n : ℕ} (b : A'.cells n) :
    (coprod.map f g).app (op (Box.ob n)) (FunctorToTypes.coprodInr b)
      = FunctorToTypes.coprodInr (g.app (op (Box.ob n)) b) := by
  rw [coprodInr_eq_inr_app, coprodInr_eq_inr_app]
  have h := NatTrans.congr_app (coprod.inr_map f g) (op (Box.ob n))
  apply_fun (fun φ => φ b) at h
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h

/-- `coprod.map f g` of two monos is a mono.  (`PrecubicalSet` is finitary extensive;
proved at the cell level by injectivity through the coproduct bijection.) -/
instance coprodMap_mono {A B A' B' : PrecubicalSet} (f : A ⟶ B) (g : A' ⟶ B')
    [Mono f] [Mono g] : Mono (coprod.map f g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  obtain ⟨⟨n⟩⟩ := k
  rw [mono_iff_injective]
  have hf : Function.Injective (f.app (op (Box.ob n))) := by
    rw [← mono_iff_injective]; exact (NatTrans.mono_iff_mono_app f).1 ‹_› _
  have hg : Function.Injective (g.app (op (Box.ob n))) := by
    rw [← mono_iff_injective]; exact (NatTrans.mono_iff_mono_app g).1 ‹_› _
  intro a b hab
  rcases coprod_cell_cases a with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases coprod_cell_cases b with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · -- inl, inl
    rw [coprodMap_coprodInl, coprodMap_coprodInl] at hab
    exact congrArg _ (hf (coprodInl_injective hab))
  · -- inl, inr: images disjoint, contradiction
    rw [coprodMap_coprodInl, coprodMap_coprodInr] at hab
    exact absurd hab (coprodInl_ne_coprodInr _ _)
  · -- inr, inl: images disjoint, contradiction
    rw [coprodMap_coprodInr, coprodMap_coprodInl] at hab
    exact absurd hab.symm (coprodInl_ne_coprodInr _ _)
  · -- inr, inr
    rw [coprodMap_coprodInr, coprodMap_coprodInr] at hab
    exact congrArg _ (hg (coprodInr_injective hab))

/-! ### The disjoint union of cospans -/

namespace Cospan

/-- **Disjoint union `⊔` of cospans** (M4).  Given `C₁ : Cospan X Y` and
`C₂ : Cospan X' Y'`, their union is a cospan `X ⨿ X' ⇒ Y ⨿ Y'` with middle
`C₁.mid ⨿ C₂.mid` and legs the `coprod.map`s of the legs of `C₁` and `C₂`.  Both new
legs are mono (`coprodMap_mono`). -/
noncomputable def union (C₁ : Cospan X Y) (C₂ : Cospan X' Y') :
    Cospan (X ⨿ X') (Y ⨿ Y') where
  mid := C₁.mid ⨿ C₂.mid
  inl := coprod.map C₁.inl C₂.inl
  inr := coprod.map C₁.inr C₂.inr
  mono_inl := coprodMap_mono _ _
  mono_inr := coprodMap_mono _ _

@[inherit_doc] scoped infixr:65 " ⊔ᶜ " => Cospan.union

@[simp] theorem union_mid (C₁ : Cospan X Y) (C₂ : Cospan X' Y') :
    (C₁.union C₂).mid = (C₁.mid ⨿ C₂.mid) := rfl

@[simp] theorem union_inl (C₁ : Cospan X Y) (C₂ : Cospan X' Y') :
    (C₁.union C₂).inl = coprod.map C₁.inl C₂.inl := rfl

@[simp] theorem union_inr (C₁ : Cospan X Y) (C₂ : Cospan X' Y') :
    (C₁.union C₂).inr = coprod.map C₁.inr C₂.inr := rfl

/-- **Leg-disjointness is preserved by `⊔`.**  At the cell level the `inl` leg lands
in the `mid₁`/`mid₂` summands of the source according to which summand of `X ⨿ X'` the
cell sits in, and likewise for `inr` and `Y ⨿ Y'`.  A collision therefore forces
*matching* summands of `C₁.mid ⨿ C₂.mid` (`coprodInl_ne_coprodInr` rules out the cross
terms), and within a summand the componentwise disjointness of `C₁` resp. `C₂`
applies. -/
theorem LegsDisjoint.union {C₁ : Cospan X Y} {C₂ : Cospan X' Y'}
    (h₁ : C₁.LegsDisjoint) (h₂ : C₂.LegsDisjoint) : (C₁.union C₂).LegsDisjoint := by
  intro n z w hcollide
  rw [union_inl, union_inr] at hcollide
  -- Split both source cells into their `X`/`X'` resp. `Y`/`Y'` summands.
  rcases coprod_cell_cases z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases coprod_cell_cases w with ⟨y, rfl⟩ | ⟨y, rfl⟩
  -- In each case, rewrite the legs back through `coprodMap_coprod{In{l,r}}` so that
  -- the collision becomes an equation between `coprodInl`/`coprodInr` cells.
  -- We turn `hcollide` into an equation between `coprodInl`/`coprodInr` cells by
  -- composing with the `coprodMap_coprod{In{l,r}}` equations on each side.  (`Eq.trans`
  -- unifies up to defeq, sidestepping `rw`'s keyed `cells`/`obj` matching.)
  · -- both in the left summand `mid₁`: reduce to `C₁`'s leg-disjointness.
    exact h₁ x y (coprodInl_injective
      ((coprodMap_coprodInl C₁.inl C₂.inl x).symm.trans
        (hcollide.trans (coprodMap_coprodInl C₁.inr C₂.inr y))))
  · -- `inl` lands in `mid₁`, `inr` in `mid₂`: disjoint summands, no collision.
    exact coprodInl_ne_coprodInr _ _
      ((coprodMap_coprodInl C₁.inl C₂.inl x).symm.trans
        (hcollide.trans (coprodMap_coprodInr C₁.inr C₂.inr y)))
  · -- `inl` lands in `mid₂`, `inr` in `mid₁`: disjoint summands, no collision.
    exact coprodInl_ne_coprodInr _ _
      ((coprodMap_coprodInl C₁.inr C₂.inr y).symm.trans
        (hcollide.symm.trans (coprodMap_coprodInr C₁.inl C₂.inl x)))
  · -- both in the right summand `mid₂`: reduce to `C₂`'s leg-disjointness.
    exact h₂ x y (coprodInr_injective
      ((coprodMap_coprodInr C₁.inl C₂.inl x).symm.trans
        (hcollide.trans (coprodMap_coprodInr C₁.inr C₂.inr y))))

end Cospan

end PrecubicalSet
