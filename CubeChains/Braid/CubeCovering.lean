import CubeChains.Braid.CubeViaZ

/-!
# Braid/CubeCovering — injectivity of the cube→terminal comparison map `φ_x`

`concToZAut n x` (`φ_x`, `CubeViaZ`) is the vertex-group map of the forgetful push
`FreeGroupoid.map (concToZ (□n))`.  Injectivity of `φ_x` is the categorical model of
`Pₙ ↪ Bₙ`: the ordered→unordered covering induces an injection on `π₁`.

`φ_x` injective ⟺ `FreeGroupoid.map (concToZ (□n))` is faithful on the vertex homs
`mk x ⟶ mk x`; and this property transports along any iso of `mk x` inside the groupoid
(conjugation), so it suffices to check one basepoint per connected component.
-/

open CategoryTheory

namespace CubeChains

/-! ## `mapAut` injectivity is vertex-faithfulness -/

variable {C : Type*} [Groupoid C] {D : Type*} [Groupoid D]

/-- `F.mapAut X` is injective as soon as `F.map` is injective on the vertex endos `X ⟶ X`. -/
theorem mapAut_injective_of_map_injective (F : C ⥤ D) (X : C)
    (h : Function.Injective (fun g : X ⟶ X => F.map g)) :
    Function.Injective (F.mapAut X) := by
  intro a b hab
  apply Aut.ext
  apply h
  exact congrArg Iso.hom hab

/-- Conversely, `F.mapAut X` injective forces `F.map` injective on vertex endos:
in a groupoid every endo is the `.hom` of an `Aut`. -/
theorem map_injective_of_mapAut_injective (F : C ⥤ D) (X : C)
    (h : Function.Injective (F.mapAut X)) :
    Function.Injective (fun g : X ⟶ X => F.map g) := by
  intro g g' hgg
  have hg : (Groupoid.isoEquivHom X X).symm g = (Groupoid.isoEquivHom X X).symm g' := by
    apply h
    apply Aut.ext
    exact hgg
  simpa using congrArg (Groupoid.isoEquivHom X X) hg

/-! ## Conjugation transports vertex-faithfulness across a connecting iso -/

/-- Conjugating automorphisms of `X` by an iso `p : X ≅ Y` — a group isomorphism `Aut X ≃* Aut Y`. -/
@[simps]
def autConj {X Y : C} (p : X ≅ Y) : Aut X ≃* Aut Y where
  toFun a := p.symm ≪≫ a ≪≫ p
  invFun b := p ≪≫ b ≪≫ p.symm
  left_inv a := by ext; simp
  right_inv b := by ext; simp
  map_mul' a b := by
    apply Aut.ext
    simp only [Aut.Aut_mul_def, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]

/-- **Naturality of `mapAut` under conjugation.**  Pushing a conjugated automorphism and conjugating
a pushed automorphism agree: `F` preserves `≪≫`. -/
theorem mapAut_autConj (F : C ⥤ D) {X Y : C} (p : X ≅ Y) (a : Aut X) :
    F.mapAut Y (autConj p a) = autConj (F.mapIso p) (F.mapAut X a) := by
  apply Aut.ext
  change F.map ((p.symm ≪≫ a ≪≫ p).hom) = _
  simp only [autConj_apply, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp]
  rfl

/-- **Transport of `mapAut` injectivity across a connecting iso.**  If `mapAut` is injective at `X`
and `p : X ≅ Y`, then it is injective at `Y`. -/
theorem mapAut_injective_of_iso (F : C ⥤ D) {X Y : C} (p : X ≅ Y)
    (h : Function.Injective (F.mapAut X)) :
    Function.Injective (F.mapAut Y) := by
  intro a b hab
  -- pull `a, b` back to `Aut X`
  have ha : F.mapAut Y a = F.mapAut Y (autConj p ((autConj p).symm a)) := by
    rw [MulEquiv.apply_symm_apply]
  have hb : F.mapAut Y b = F.mapAut Y (autConj p ((autConj p).symm b)) := by
    rw [MulEquiv.apply_symm_apply]
  rw [ha, hb, mapAut_autConj, mapAut_autConj] at hab
  have hab' := (autConj (F.mapIso p)).injective hab
  have := h hab'
  have := (autConj p).symm.injective this
  simpa using this

end CubeChains
