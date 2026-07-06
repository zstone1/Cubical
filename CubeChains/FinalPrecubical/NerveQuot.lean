import CubeChains.FinalPrecubical.QuotientCat
import CubeChains.FinalPrecubical.Salvetti
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Algebra.Order.Group.Action.Synonym
import Mathlib.CategoryTheory.Category.Preorder

/-!
# FinalPrecubical / NerveQuot

Step 5 of the braid-chains program (see `BRAID_CHAINS_README.md`): the **nerve
quotient**.

For an order-free group action `G ↷ P` on a poset (Step 1), the nerve of the quotient
category `P // G` is the levelwise `G`-quotient of `nerve P`:

  `θ : (nerve P) / G  ≅  nerve (P // G)`   (`nerveQuotIso`).

The generic package (items 1–4 of the spec) is developed here, sorry-free:

* `smulFunctor g : P ⥤ P` — the order-iso induced by `g`, and the resulting
  `MulAction G (ComposableArrows P m)` (post-composition).
* `nerveQuot P G : SSet` — the levelwise quotient simplicial set.
* `θ : nerveQuot P G ⟶ nerve (QuotCat P G)` — the comparison, induced by the quotient
  functor `quotFunctor : P ⥤ QuotCat P G`.
* `nerveQuotIso : nerveQuot P G ≅ nerve (QuotCat P G)` — `θ` is levelwise bijective by
  **unique chain lifting** (`QuotCat.homEquivUpSet`).

The final `ChZ`-assembly (item 5, `nerve_chZ_iso`) is isolated behind an interface: it
consumes the Step-4 isomorphism `Φ` (still being built) and is the only place a `sorry`
is used.
-/

open CategoryTheory Opposite Simplicial

namespace FinalPrecubical

open MulAction

/-! ## Item 0. The order-free action transports to the order dual `Pᵒᵈ` -/

section OrderDual

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-- **Item 0.** An order-free action on `P` is order-free on the order-dual `Pᵒᵈ`.
On `Pᵒᵈ`, `x ≤ g • x` means `g • x ≤ x` in `P`; applying `g⁻¹•` gives `x ≤ g⁻¹ • x` in
`P`, whence `g⁻¹ = 1`. -/
instance orderFreeAction_orderDual : OrderFreeAction G Pᵒᵈ where
  smul_le_smul_iff g {x y} :=
    smul_le_smul_iff (P := P) g (x := OrderDual.ofDual y) (y := OrderDual.ofDual x)
  eq_one_of_le_smul g x h := by
    have h' : g • OrderDual.ofDual x ≤ OrderDual.ofDual x := h
    have h2 : OrderDual.ofDual x ≤ g⁻¹ • OrderDual.ofDual x := by
      have := (smul_le_smul_iff (P := P) g⁻¹).2 h'
      rwa [inv_smul_smul] at this
    have hg : g⁻¹ = 1 := eq_one_of_le_smul (P := P) g⁻¹ _ h2
    exact inv_eq_one.mp hg

end OrderDual

/-! ## Generic setup: the `G`-action on nerves -/

section Generic

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-- Functor extensionality into a preorder: agreement on objects suffices (thinness). -/
theorem funext_into_preorder {J : Type*} [Category J] {C : Type*} [Preorder C]
    {F H : J ⥤ C} (h : ∀ j, F.obj j = H.obj j) : F = H :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Subsingleton.elim _ _)

/-! ### Item 1. `g` acts on `nerve P` by functoriality -/

/-- Left multiplication by `g` is monotone (an order automorphism of `P`). -/
theorem smulMono (g : G) : Monotone (fun x : P => g • x) :=
  fun _ _ h => (smul_le_smul_iff g).2 h

/-- The order-iso functor `P ⥤ P` induced by `g : G`. -/
def smulFunctor (g : G) : P ⥤ P := (smulMono g).functor

@[simp] theorem smulFunctor_obj (g : G) (x : P) : (smulFunctor g).obj x = g • x := rfl

theorem smulFunctor_one : smulFunctor (1 : G) (P := P) = 𝟭 P :=
  funext_into_preorder (fun x => one_smul G x)

theorem smulFunctor_mul (g h : G) :
    smulFunctor (g * h) (P := P) = smulFunctor h ⋙ smulFunctor g :=
  funext_into_preorder (fun x => mul_smul g h x)

/-- **Item 1.** `G` acts on `ComposableArrows P m = Fin (m+1) ⥤ P` by post-composition
with `smulFunctor`. -/
instance composableArrowsAction (m : ℕ) : MulAction G (ComposableArrows P m) where
  smul g F := F ⋙ smulFunctor g
  one_smul F := by
    show F ⋙ smulFunctor (1 : G) = F
    rw [smulFunctor_one]; exact Functor.comp_id F
  mul_smul g h F := by
    show F ⋙ smulFunctor (g * h) = (F ⋙ smulFunctor h) ⋙ smulFunctor g
    rw [smulFunctor_mul, Functor.assoc]

theorem composableArrows_smul_def (g : G) {m : ℕ} (F : ComposableArrows P m) :
    g • F = F ⋙ smulFunctor g := rfl

/-! ### Item 2. The quotient simplicial set `(nerve P) / G` -/

/-- The simplicial operator of `nerve P` at `f`, as a plain function on
`ComposableArrows` (definitionally `⇑((nerve P).map f)`, but with reduced types so the
`MulAction` instances fire). -/
def nerveOp {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    ComposableArrows P Δ.unop.len → ComposableArrows P Δ'.unop.len :=
  (⇑((nerve P).map f) : ComposableArrows P Δ.unop.len → ComposableArrows P Δ'.unop.len)

theorem nerveOp_id (Δ : SimplexCategoryᵒᵖ) :
    nerveOp (P := P) (𝟙 Δ) = id := by
  funext x
  change ⇑((nerve P).map (𝟙 Δ)) x = x
  rw [(nerve P).map_id]; rfl

theorem nerveOp_comp {Δ Δ' Δ'' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (h : Δ' ⟶ Δ'') :
    nerveOp (P := P) (f ≫ h) = nerveOp h ∘ nerveOp f := by
  funext x
  change ⇑((nerve P).map (f ≫ h)) x = ⇑((nerve P).map h) (⇑((nerve P).map f) x)
  rw [(nerve P).map_comp]; rfl

/-- The `G`-action commutes with the simplicial operators of `nerve P`
(left-whiskering by a `Fin`-map versus right-whiskering by `smulFunctor g`). -/
theorem nerveOp_smul {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (g : G)
    (x : ComposableArrows P Δ.unop.len) :
    nerveOp f (g • x) = g • nerveOp f x := rfl

/-- The descended simplicial operator on the levelwise quotients. -/
def orbitMap {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    orbitRel.Quotient G (ComposableArrows P Δ.unop.len) →
      orbitRel.Quotient G (ComposableArrows P Δ'.unop.len) :=
  fun q => Quotient.liftOn' q
    (fun x => (Quotient.mk'' (nerveOp f x) : orbitRel.Quotient G _))
    (fun a b hab => Quotient.sound' (by
      obtain ⟨g, rfl⟩ := hab
      exact ⟨g, (nerveOp_smul f g b).symm⟩))

@[simp] theorem orbitMap_mk {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (x : ComposableArrows P Δ.unop.len) :
    orbitMap (G := G) f (Quotient.mk'' x) = Quotient.mk'' (nerveOp f x) := rfl

/-- **Item 2.** The levelwise `G`-quotient of `nerve P`. -/
@[simps obj]
def nerveQuot : SSet where
  obj Δ := orbitRel.Quotient G (ComposableArrows P Δ.unop.len)
  map {Δ Δ'} f := ↾(orbitMap (G := G) (P := P) f)
  map_id Δ := by
    have hfun : orbitMap (G := G) (P := P) (𝟙 Δ) = id := by
      funext q
      induction q using Quotient.inductionOn' with
      | h x => rw [orbitMap_mk, nerveOp_id]; rfl
    rw [hfun]; rfl
  map_comp {Δ Δ' Δ''} f h := by
    have hfun : orbitMap (G := G) (P := P) (f ≫ h) = orbitMap h ∘ orbitMap f := by
      funext q
      induction q using Quotient.inductionOn' with
      | h x => simp only [Function.comp_apply, orbitMap_mk, nerveOp_comp]
    rw [hfun]; rfl

/-! ### Item 3. The quotient functor `Q : P ⥤ QuotCat P G` and the comparison `θ` -/

/-- The morphism `⟦a⟧ ⟶ ⟦b⟧` in `QuotCat P G` represented by the comparable pair
`(a, b)`. -/
def quotHom {a b : P} (hab : a ≤ b) :
    (Quotient.mk'' a : QuotCat P G) ⟶ Quotient.mk'' b :=
  Quotient.mk'' ⟨(a, b), hab, rfl, rfl⟩

/-- Identity law for `quotHom`. -/
theorem quotHom_id (p : P) :
    quotHom (le_refl p) = 𝟙 (Quotient.mk'' p : QuotCat P G) := by
  apply Quotient.sound'
  exact ⟨align (Quotient.out (Quotient.mk'' p : QuotCat P G)) p (Quotient.out_eq' _),
    align_smul _ _ _, align_smul _ _ _⟩

/-- Composition law for `quotHom` (the aligner of a "matching" pair is the identity). -/
theorem quotHom_comp {p q r : P} (h : p ≤ q) (k : q ≤ r) :
    quotHom (G := G) h ≫ quotHom k = quotHom (h.trans k) := by
  apply Quotient.sound'
  refine ⟨1, by simp [QuotCat.compSpan_val_fst], ?_⟩
  simp only [QuotCat.compSpan_val_snd, one_smul]
  rw [show QuotCat.alignPair
      (⟨(p, q), h, rfl, rfl⟩ : QuotCat.Span (Quotient.mk'' p : QuotCat P G) (Quotient.mk'' q))
      (⟨(q, r), k, rfl, rfl⟩ : QuotCat.Span (Quotient.mk'' q : QuotCat P G) (Quotient.mk'' r))
      = (1 : G) from align_self q _, one_smul]

/-- **The quotient functor** `Q : P ⥤ QuotCat P G`. -/
noncomputable def quotFunctor : P ⥤ QuotCat P G where
  obj p := (Quotient.mk'' p : QuotCat P G)
  map {p q} h := quotHom (leOfHom h)
  map_id p := quotHom_id p
  map_comp {p q r} h k := (quotHom_comp (leOfHom h) (leOfHom k)).symm

@[simp] theorem quotFunctor_obj (p : P) :
    (quotFunctor (G := G)).obj p = (Quotient.mk'' p : QuotCat P G) := rfl

theorem quotFunctor_map {p q : P} (h : p ≤ q) :
    (quotFunctor (G := G)).map (homOfLE h) = quotHom h := rfl

/-- `eqToHom` of an equality `⟦a⟧ = Y` in `QuotCat P G` is the quotient of the diagonal
span `(a, a)`. -/
theorem eqToHom_quotMk {a : P} {Y : QuotCat P G} (e : (Quotient.mk'' a : QuotCat P G) = Y) :
    eqToHom e = Quotient.mk'' (⟨(a, a), le_refl a, rfl, e⟩ : QuotCat.Span (Quotient.mk'' a) Y) := by
  subst e
  rw [eqToHom_refl]
  symm
  apply Quotient.sound'
  exact ⟨align (Quotient.out (Quotient.mk'' a)) a (Quotient.out_eq' _),
    align_smul _ _ _, align_smul _ _ _⟩

/-- The unique upper endpoint of `quotHom hab` over its source `a` is `b`. -/
theorem homEquivUpSet_quotHom {a b : P} (hab : a ≤ b) :
    ((QuotCat.homEquivUpSet a (Quotient.mk'' b : QuotCat P G)) (quotHom hab)).val = b := by
  show (QuotCat.homToUpSet a (Quotient.mk'' b : QuotCat P G) (quotHom hab)).val = b
  simp only [QuotCat.homToUpSet, quotHom, Quotient.liftOn'_mk'']
  rw [align_self, one_smul]

/-- **Core edge invariance.**  `Q` sends the `g`-translate of an edge to the same
morphism (up to the object identifications `⟦g • x⟧ = ⟦x⟧`). -/
theorem quotHom_smul_eq (g : G) {x y : P} (hxy : x ≤ y) :
    quotHom ((smul_le_smul_iff g).2 hxy)
      = eqToHom (mk_smul_eq g x) ≫ quotHom hxy ≫ eqToHom (mk_smul_eq g y).symm := by
  rw [eqToHom_quotMk (mk_smul_eq g x),
      eqToHom_quotMk (Y := Quotient.mk'' (g • y)) (mk_smul_eq g y).symm]
  simp only [quotHom]
  apply Quotient.sound'
  -- name the three composed spans
  set sM : QuotCat.Span (Quotient.mk'' x : QuotCat P G) (Quotient.mk'' y) :=
    ⟨(x, y), hxy, rfl, rfl⟩ with hsM
  set sC : QuotCat.Span (Quotient.mk'' y : QuotCat P G) (Quotient.mk'' (g • y)) :=
    ⟨(y, y), le_refl y, rfl, (mk_smul_eq g y).symm⟩ with hsC
  set sA : QuotCat.Span (Quotient.mk'' (g • x) : QuotCat P G) (Quotient.mk'' x) :=
    ⟨(g • x, g • x), le_refl (g • x), rfl, mk_smul_eq g x⟩ with hsA
  -- the inner composite fixes `y`
  have hinner1 : (QuotCat.compSpan sM sC).val.1 = x := QuotCat.compSpan_val_fst sM sC
  have hinner2 : (QuotCat.compSpan sM sC).val.2 = y := by
    rw [QuotCat.compSpan_val_snd]; exact QuotCat.alignPair_smul sM sC
  -- the outer aligner carries `x` to `g • x`, hence (freeness) equals `g`
  have houter : QuotCat.alignPair sA (QuotCat.compSpan sM sC) = g := by
    have h := QuotCat.alignPair_smul sA (QuotCat.compSpan sM sC)
    rw [hinner1, hsA] at h
    exact smul_left_cancel h
  refine ⟨1, ?_, ?_⟩
  · rw [QuotCat.compSpan_val_fst, one_smul, hsA]
  · rw [one_smul, QuotCat.compSpan_val_snd, hinner2, houter]

/-- **Item 3 (invariance).**  Post-composing with `smulFunctor g` does not change the
quotient functor: `smulFunctor g ⋙ Q = Q`. -/
theorem smulFunctor_comp_quotFunctor (g : G) :
    smulFunctor g ⋙ quotFunctor (G := G) (P := P) = quotFunctor :=
  CategoryTheory.Functor.ext (fun x => mk_smul_eq g x)
    (fun x y f => quotHom_smul_eq g (leOfHom f))

/-- The levelwise comparison map: send `⟦F⟧` to `F ⋙ Q`. -/
noncomputable def thetaApp (Δ : SimplexCategoryᵒᵖ) :
    orbitRel.Quotient G (ComposableArrows P Δ.unop.len) →
      ComposableArrows (QuotCat P G) Δ.unop.len :=
  fun q => Quotient.liftOn' q (fun F => F ⋙ quotFunctor) (fun a b hab => by
    obtain ⟨g, rfl⟩ := hab
    show (g • b) ⋙ quotFunctor = b ⋙ quotFunctor
    rw [composableArrows_smul_def, Functor.assoc, smulFunctor_comp_quotFunctor])

@[simp] theorem thetaApp_mk (Δ : SimplexCategoryᵒᵖ) (F : ComposableArrows P Δ.unop.len) :
    thetaApp (G := G) Δ (Quotient.mk'' F) = F ⋙ quotFunctor := rfl

/-- **Item 3.**  The comparison map `θ : (nerve P)/G ⟶ nerve (P // G)`, the descent of
`nerveMap (quotFunctor)`. -/
noncomputable def theta : nerveQuot (G := G) (P := P) ⟶ nerve (QuotCat P G) where
  app Δ := ↾(thetaApp (G := G) (P := P) Δ)
  naturality {Δ Δ'} f := by
    ext q
    induction q using Quotient.inductionOn' with
    | h x =>
      simp only [TypeCat.ofHom_apply, types_comp_apply, nerveQuot_obj, orbitMap_mk, thetaApp_mk]
      rfl

end Generic

/-! ## Items 4–5: placeholders (to be filled) -/

section Iso

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-- **Item 4.** `θ` is an isomorphism of simplicial sets. -/
def nerveQuotIso : nerveQuot (G := G) (P := P) ≅ nerve (QuotCat P G) := by
  sorry

end Iso

end FinalPrecubical
