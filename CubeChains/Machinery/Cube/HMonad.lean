import CubeChains.Machinery.Cube.SymRepresentable
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Machinery/Cube/HMonad — the natural maps between powers of `H`

`H = symFree ⋙ symRestrict` is the monad of `symFreeAdj`, and its multiplication is the *only*
natural `H² ⟶ H` (`Hmul_unique`): the bar construction's degree `1` carries a single face.  Degree
`2` carries two, `μ_{HK}` and `H μ_K`, and they differ (`HmulOuter_ne_HmulInner`).

The argument is naturality twice: in `K` the cell cannot move (`nat_app`), and along the edge
freeing `i` the surviving order is read off the axis (`natOrd_eq`).
-/

open CategoryTheory Opposite StdCube

namespace CubeChains

/-! ## The counit, and the multiplication -/

/-- The counit is the descent of the identity — `symFree_hom_ext` plus the triangle law. -/
theorem symFreeAdj_counit_app (G : SymPrecubicalSet) :
    symFreeAdj.counit.app G = symDesc G (𝟙 (symRestrict.obj G)) :=
  symFree_hom_ext <|
    (symFreeAdj_unit_app (symRestrict.obj G) ▸ symFreeAdj.right_triangle_components G).trans
      (symUnit_symDesc G (𝟙 (symRestrict.obj G))).symm

/-- The multiplication of the monad `H`. -/
noncomputable def Hmul : H ⋙ H ⟶ H := symFreeAdj.toMonad.μ

/-- **The multiplication composes the two orders**: the outer order `τ` is performed first. -/
theorem Hmul_app {K : PrecubicalSet} {m : ℕ} (τ σ : Equiv.Perm (Fin m)) (y : K.obj (op ▫m)) :
    (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = ((σ * τ, y) : (H.obj K).obj (op ▫m)) := by
  have h : (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = (symFree.obj K).map (symHom τ).op ((σ, y) : (symFree.obj K).obj (op ▪m)) := by
    change (symFreeAdj.counit.app (symFree.obj K)).app (op ▪m) _ = _
    rw [symFreeAdj_counit_app]
    rfl
  rw [h, symFree_obj_map_symHom]
  rfl

/-! ## Edges see every axis

An edge carries no order (`Perm (Fin 1)` is trivial), so sorting one through `ρ` *is*
post-composition with `symHom ρ`, and the axis it performs moves by `ρ`. -/

/-- **Sorting an edge through `ρ` is post-composition with `ρ`** — there is no order to sort. -/
theorem J_sortFace_edge {n : ℕ} (g : ▫1 ⟶ ▫n) (ρ : Equiv.Perm (Fin n)) :
    (J.map (SHom.sortFace (J.map g) ρ) : ▪1 ⟶ ▪n) = J.map g ≫ symHom ρ := by
  have h := SHom.symm_sortPerm_sortFace (J.map g) ρ
  rwa [sHomEquiv_symm_apply, Subsingleton.elim (SHom.sortPerm (J.map g) ρ) 1, symHom_one,
    Category.id_comp] at h

/-- …so the axis the edge performs moves by `ρ`. -/
theorem faceEmb_sortFace_edge {n : ℕ} (g : ▫1 ⟶ ▫n) (ρ : Equiv.Perm (Fin n)) :
    faceEmb (SHom.sortFace (J.map g) ρ) 0 = ρ (faceEmb g 0) := by
  have h := congrArg (fun u : ▪1 ⟶ ▪n => SHom.pos u 0) (J_sortFace_edge g ρ)
  simpa using h

/-! ## There is only one natural map `H² ⟶ H` -/

/-- The order a natural `H² ⟶ H` returns, read on the representable's top cell.  `nat_app` says
this is all of it. -/
noncomputable def natOrd (θ : H ⋙ H ⟶ H) (m : ℕ) (τ σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) :=
  ((θ.app (yoneda.obj ▫m)).app (op ▫m)
    ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))).1

/-- **A natural `H² ⟶ H` cannot touch the cell**: naturality in `K` reduces it to the cube, whose
top cell is rigid, so only the order can move. -/
theorem nat_app (θ : H ⋙ H ⟶ H) {K : PrecubicalSet} {m : ℕ}
    (τ σ : Equiv.Perm (Fin m)) (y : K.obj (op ▫m)) :
    (θ.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))
      = ((natOrd θ m τ σ, y) : (H.obj K).obj (op ▫m)) := by
  have hy : (yonedaEquiv.symm y).app (op ▫m) (𝟙 ▫m) = y :=
    (yonedaEquiv_apply _).symm.trans (yonedaEquiv.apply_symm_apply y)
  have hL : ((H ⋙ H).map (yonedaEquiv.symm y)).app (op ▫m)
      ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m))
      = ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m)) := Prod.ext rfl (Prod.ext rfl hy)
  have hR : (H.map (yonedaEquiv.symm y)).app (op ▫m)
      ((θ.app (yoneda.obj ▫m)).app (op ▫m)
        ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m)))
      = ((natOrd θ m τ σ, y) : (H.obj K).obj (op ▫m)) :=
    Prod.ext rfl ((congrArg ((yonedaEquiv.symm y).app (op ▫m)) (Box.endo_eq_id _)).trans hy)
  exact ((congrArg ((θ.app K).app (op ▫m)) hL).symm.trans
    (comp_app_cell₂ (θ.naturality (yonedaEquiv.symm y)) m
      ((τ, σ, 𝟙 ▫m) : ((H ⋙ H).obj (yoneda.obj ▫m)).obj (op ▫m)))).trans hR

/-- **The order is forced to be the product** — naturality along the edge freeing `i` reads the
composite `σ ∘ τ` off the axis `i`. -/
theorem natOrd_eq (θ : H ⋙ H ⟶ H) {n : ℕ} (τ σ : Equiv.Perm (Fin n)) :
    natOrd θ n τ σ = σ * τ := by
  refine Equiv.ext fun i => ?_
  set F := natOrd θ n τ σ
  set g : ▫1 ⟶ ▫n := edge n i with hg
  set g₁ : ▫1 ⟶ ▫n := SHom.sortFace (J.map g) τ with hg₁
  have hnat := NatTrans.naturality_apply (θ.app (yoneda.obj ▫n)) g.op
    ((τ, σ, 𝟙 ▫n) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫n))
  have hL : (((H ⋙ H).obj (yoneda.obj ▫n)).map g.op
      ((τ, σ, 𝟙 ▫n) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫n)))
      = ((SHom.sortPerm (J.map g) τ, SHom.sortPerm (J.map g₁) σ,
          SHom.sortFace (J.map g₁) σ) : ((H ⋙ H).obj (yoneda.obj ▫n)).obj (op ▫1)) :=
    Prod.ext rfl (Prod.ext rfl (Category.comp_id (SHom.sortFace (J.map g₁) σ)))
  have hR : (H.obj (yoneda.obj ▫n)).map g.op
      ((F, 𝟙 ▫n) : (H.obj (yoneda.obj ▫n)).obj (op ▫n))
      = ((SHom.sortPerm (J.map g) F, SHom.sortFace (J.map g) F) :
          (H.obj (yoneda.obj ▫n)).obj (op ▫1)) :=
    Prod.ext rfl (Category.comp_id (SHom.sortFace (J.map g) F))
  rw [hL, nat_app, nat_app, hR] at hnat
  have h2 : SHom.sortFace (J.map g₁) σ = SHom.sortFace (J.map g) F := congrArg Prod.snd hnat
  have e0 : faceEmb g 0 = i := by rw [hg]; exact faceEmb_edge n i
  have e1 : faceEmb g₁ 0 = τ i := by
    rw [hg₁]
    exact (faceEmb_sortFace_edge g τ).trans (congrArg (fun j : Fin n => τ j) e0)
  have h3 := congrArg (fun ψ : ▫1 ⟶ ▫n => faceEmb ψ 0) h2
  rw [Equiv.Perm.mul_apply]
  calc F i = F (faceEmb g 0) := by rw [e0]
    _ = faceEmb (SHom.sortFace (J.map g) F) 0 := (faceEmb_sortFace_edge g F).symm
    _ = faceEmb (SHom.sortFace (J.map g₁) σ) 0 := h3.symm
    _ = σ (faceEmb g₁ 0) := faceEmb_sortFace_edge g₁ σ
    _ = σ (τ i) := by rw [e1]

/-- **`Hmul` is the only natural transformation `H² ⟶ H`** — degree `1` of the bar construction
has a single face. -/
theorem Hmul_unique (θ : H ⋙ H ⟶ H) : θ = Hmul := by
  refine NatTrans.ext (funext fun K => ?_)
  refine NatTrans.ext_apply fun B p => ?_
  obtain ⟨τ, σ, y⟩ := p
  exact (nat_app θ (m := B.unop.dim) τ σ y).trans
    ((congrArg (fun ρ => ((ρ, y) : (H.obj K).obj B)) (natOrd_eq θ τ σ)).trans
      (Hmul_app τ σ y).symm)

instance : Subsingleton (H ⋙ H ⟶ H) :=
  ⟨fun θ θ' => (Hmul_unique θ).trans (Hmul_unique θ').symm⟩

theorem swap_ne_one : Equiv.swap (0 : Fin 2) 1 ≠ 1 := fun h =>
  absurd (Equiv.swap_eq_refl_iff.mp h) (by decide)

/-- **Forgetting either order is not natural**: at a transposition every natural map returns it,
not the other factor. -/
theorem natOrd_forget (θ : H ⋙ H ⟶ H) :
    natOrd θ 2 (Equiv.swap 0 1) 1 ≠ 1 ∧ natOrd θ 2 1 (Equiv.swap 0 1) ≠ 1 :=
  ⟨by rw [natOrd_eq, one_mul]; exact swap_ne_one,
   by rw [natOrd_eq, mul_one]; exact swap_ne_one⟩

/-! ## Degree `2`: the two faces are different

`μ_{HK}` multiplies the two *outer* orders and `H μ_K` the two *inner* ones; the monad law only
makes them agree after a further `μ`. -/

/-- `μ_{HK}` — the bar face that multiplies the outer pair. -/
noncomputable def HmulOuter : H ⋙ H ⋙ H ⟶ H ⋙ H := Functor.whiskerLeft H Hmul

/-- `H μ_K` — the bar face that multiplies the inner pair. -/
noncomputable def HmulInner : H ⋙ H ⋙ H ⟶ H ⋙ H := Functor.whiskerRight Hmul H

theorem HmulOuter_app {K : PrecubicalSet} {m : ℕ} (ρ τ σ : Equiv.Perm (Fin m))
    (y : K.obj (op ▫m)) :
    (HmulOuter.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((τ * ρ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m)) :=
  Hmul_app (K := H.obj K) ρ τ ((σ, y) : (H.obj K).obj (op ▫m))

theorem HmulInner_app {K : PrecubicalSet} {m : ℕ} (ρ τ σ : Equiv.Perm (Fin m))
    (y : K.obj (op ▫m)) :
    (HmulInner.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((ρ, σ * τ, y) : ((H ⋙ H).obj K).obj (op ▫m)) := by
  have h0 : (HmulInner.app K).app (op ▫m) ((ρ, τ, σ, y) : ((H ⋙ H ⋙ H).obj K).obj (op ▫m))
      = ((ρ, (Hmul.app K).app (op ▫m) ((τ, σ, y) : ((H ⋙ H).obj K).obj (op ▫m))) :
          ((H ⋙ H).obj K).obj (op ▫m)) := rfl
  rw [h0, Hmul_app]
  rfl

/-- **The two degree-`2` faces differ** — already on the `2`-cube, at a transposition. -/
theorem HmulOuter_ne_HmulInner : HmulOuter ≠ HmulInner := by
  intro h
  have key : (HmulOuter.app (yoneda.obj ▫2)).app (op ▫2)
        (((1 : Equiv.Perm (Fin 2)), Equiv.swap (0 : Fin 2) (1 : Fin 2),
            (1 : Equiv.Perm (Fin 2)), 𝟙 ▫2) :
          ((H ⋙ H ⋙ H).obj (yoneda.obj ▫2)).obj (op ▫2))
      = (HmulInner.app (yoneda.obj ▫2)).app (op ▫2)
        (((1 : Equiv.Perm (Fin 2)), Equiv.swap (0 : Fin 2) (1 : Fin 2),
            (1 : Equiv.Perm (Fin 2)), 𝟙 ▫2) :
          ((H ⋙ H ⋙ H).obj (yoneda.obj ▫2)).obj (op ▫2)) := by
    rw [h]
  rw [HmulOuter_app, HmulInner_app] at key
  refine swap_ne_one ?_
  have h1 := congrArg Prod.fst key
  rwa [mul_one] at h1

end CubeChains
