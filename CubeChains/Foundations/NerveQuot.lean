import CubeChains.Foundations.QuotientCat
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Algebra.Order.Group.Action.Synonym
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.Cat

/-!
# Foundations/NerveQuot — the nerve of a quotient category

For an order-free group action `G ↷ P` on a poset, the nerve of the quotient category `P // G`
is the levelwise `G`-quotient of `nerve P`:

  `nerveQuotIso : (nerve P) / G  ≅  nerve (P // G)`.

* `smulFunctor g : P ⥤ P` — the order-iso induced by `g`, and the resulting
  `MulAction G (ComposableArrows P m)`;
* `nerveQuot P G : SSet` — the levelwise quotient simplicial set;
* `theta : nerveQuot P G ⟶ nerve (QuotCat P G)` — the comparison from `quotFunctor`;
* `nerveQuotIso` — `theta` is levelwise bijective by **unique chain lifting**
  (`QuotCat.homEquivUpSet`).

`nerveQuotIso_of_catIso` adds the order-dual/opposite transport, so any category isomorphic to
`(P // G)ᵒᵖ` has its nerve identified with `(nerve Pᵒᵈ) / G`.
-/

open CategoryTheory Opposite Simplicial

namespace OrderQuotient

open MulAction

/-! ## The order-free action transports to the order dual `Pᵒᵈ` -/

section OrderDual

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-- An order-free action on `P` is order-free on the order-dual `Pᵒᵈ`.
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

/-! ### `g` acts on `nerve P` by functoriality -/

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

/-- `G` acts on `ComposableArrows P m = Fin (m+1) ⥤ P` by post-composition
with `smulFunctor`. -/
instance composableArrowsAction (m : ℕ) : MulAction G (ComposableArrows P m) where
  smul g F := F ⋙ smulFunctor g
  one_smul F := by
    change F ⋙ smulFunctor (1 : G) = F
    rw [smulFunctor_one]; exact Functor.comp_id F
  mul_smul g h F := by
    change F ⋙ smulFunctor (g * h) = (F ⋙ smulFunctor h) ⋙ smulFunctor g
    rw [smulFunctor_mul, Functor.assoc]

theorem composableArrows_smul_def (g : G) {m : ℕ} (F : ComposableArrows P m) :
    g • F = F ⋙ smulFunctor g := rfl

/-! ### The quotient simplicial set `(nerve P) / G` -/

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

/-- The levelwise `G`-quotient of `nerve P`. -/
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

/-! ### The quotient functor `Q : P ⥤ QuotCat P G` and the comparison `θ` -/

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
  change (QuotCat.homToUpSet a (Quotient.mk'' b : QuotCat P G) (quotHom hab)).val = b
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

/-- Post-composing with `smulFunctor g` does not change the quotient functor:
`smulFunctor g ⋙ Q = Q`. -/
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
    change (g • b) ⋙ quotFunctor = b ⋙ quotFunctor
    rw [composableArrows_smul_def, Functor.assoc, smulFunctor_comp_quotFunctor])

@[simp] theorem thetaApp_mk (Δ : SimplexCategoryᵒᵖ) (F : ComposableArrows P Δ.unop.len) :
    thetaApp (G := G) Δ (Quotient.mk'' F) = F ⋙ quotFunctor := rfl

/-- The comparison map `θ : (nerve P)/G ⟶ nerve (P // G)`, the descent of
`nerveMap (quotFunctor)`. -/
noncomputable def theta : nerveQuot (G := G) (P := P) ⟶ nerve (QuotCat P G) where
  app Δ := ↾(thetaApp (G := G) (P := P) Δ)
  naturality {Δ Δ'} f := by
    ext q
    induction q using Quotient.inductionOn' with
    | h x =>
      simp only [nerveQuot_obj]
      rfl

/-! ### `θ` is a levelwise bijection (unique chain lifting) -/

/-- The inverse of `homEquivUpSet`, as a `quotHom` composed with an `eqToHom`. -/
theorem homEquivUpSet_symm_eq {a : P} {Y : QuotCat P G}
    (s : {b : P // a ≤ b ∧ (Quotient.mk'' b : QuotCat P G) = Y}) :
    (QuotCat.homEquivUpSet a Y).symm s = quotHom s.property.1 ≫ eqToHom s.property.2 := by
  obtain ⟨b, hab, hbY⟩ := s
  change Quotient.mk'' (⟨(a, b), hab, rfl, hbY⟩ : QuotCat.Span (Quotient.mk'' a) Y)
      = quotHom hab ≫ eqToHom hbY
  rw [eqToHom_quotMk hbY, quotHom]
  apply Quotient.sound'
  refine ⟨1, by simp [QuotCat.compSpan_val_fst], ?_⟩
  rw [one_smul, QuotCat.compSpan_val_snd]
  exact (QuotCat.alignPair_smul
    (⟨(a, b), hab, rfl, rfl⟩ : QuotCat.Span (Quotient.mk'' a : QuotCat P G) (Quotient.mk'' b))
    (⟨(b, b), le_refl b, rfl, hbY⟩ : QuotCat.Span (Quotient.mk'' b : QuotCat P G) Y)).symm

variable {m : ℕ}

/-- The recursive lift of a `QuotCat`-chain `F` to a `P`-chain, starting from a chosen
representative `p0` of the initial vertex. -/
noncomputable def liftPt (F : ComposableArrows (QuotCat P G) m) (p0 : P)
    (hp0 : (Quotient.mk'' p0 : QuotCat P G) = F.obj 0) :
    ∀ i : Fin (m + 1), {p : P // (Quotient.mk'' p : QuotCat P G) = F.obj i} :=
  Fin.induction ⟨p0, hp0⟩ (fun i prev =>
    ⟨(QuotCat.homEquivUpSet prev.val (F.obj i.succ)
        (eqToHom prev.property ≫ F.map (homOfLE (Fin.castSucc_le_succ i)))).val,
     (QuotCat.homEquivUpSet prev.val (F.obj i.succ)
        (eqToHom prev.property ≫ F.map (homOfLE (Fin.castSucc_le_succ i)))).property.2⟩)

variable (F : ComposableArrows (QuotCat P G) m) (p0 : P)
    (hp0 : (Quotient.mk'' p0 : QuotCat P G) = F.obj 0)

@[simp] theorem liftPt_zero : liftPt F p0 hp0 0 = ⟨p0, hp0⟩ := rfl

/-- Unfolding of the lift at a successor index. -/
theorem liftPt_succ (i : Fin m) :
    liftPt F p0 hp0 i.succ =
      ⟨(QuotCat.homEquivUpSet (liftPt F p0 hp0 i.castSucc).val (F.obj i.succ)
          (eqToHom (liftPt F p0 hp0 i.castSucc).property
            ≫ F.map (homOfLE (Fin.castSucc_le_succ i)))).val,
       (QuotCat.homEquivUpSet (liftPt F p0 hp0 i.castSucc).val (F.obj i.succ)
          (eqToHom (liftPt F p0 hp0 i.castSucc).property
            ≫ F.map (homOfLE (Fin.castSucc_le_succ i)))).property.2⟩ := rfl

/-- Consecutive lift points are comparable. -/
theorem liftPt_le (i : Fin m) :
    (liftPt F p0 hp0 i.castSucc).val ≤ (liftPt F p0 hp0 i.succ).val := by
  rw [liftPt_succ]
  exact (QuotCat.homEquivUpSet _ _ _).property.1

/-- The lifted `P`-chain. -/
noncomputable def liftChain : ComposableArrows P m :=
  ComposableArrows.mkOfObjOfMapSucc (fun i => (liftPt F p0 hp0 i).val)
    (fun i => homOfLE (liftPt_le F p0 hp0 i))

@[simp] theorem liftChain_obj (i : Fin (m + 1)) :
    (liftChain F p0 hp0).obj i = (liftPt F p0 hp0 i).val := rfl

/-- The lifted edge, computed via `homEquivUpSet_symm_eq`. -/
theorem liftPt_quotHom (i : Fin m) :
    quotHom (liftPt_le F p0 hp0 i)
      = eqToHom (liftPt F p0 hp0 i.castSucc).property
        ≫ F.map (homOfLE (Fin.castSucc_le_succ i))
        ≫ eqToHom (liftPt F p0 hp0 i.succ).property.symm := by
  have key : (eqToHom (liftPt F p0 hp0 i.castSucc).property
        ≫ F.map (homOfLE (Fin.castSucc_le_succ i)) :
        (Quotient.mk'' (liftPt F p0 hp0 i.castSucc).val : QuotCat P G) ⟶ F.obj i.succ)
      = quotHom (liftPt_le F p0 hp0 i) ≫ eqToHom (liftPt F p0 hp0 i.succ).property := by
    have h1 := (Equiv.symm_apply_apply
        (QuotCat.homEquivUpSet (liftPt F p0 hp0 i.castSucc).val (F.obj i.succ))
        (eqToHom (liftPt F p0 hp0 i.castSucc).property
          ≫ F.map (homOfLE (Fin.castSucc_le_succ i)))).symm
    rw [h1]
    exact homEquivUpSet_symm_eq _
  rw [← Category.assoc, key, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **Surjectivity.**  The lift is a genuine preimage: `liftChain F p0 ⋙ Q = F`. -/
theorem liftChain_comp_quotFunctor :
    liftChain F p0 hp0 ⋙ quotFunctor (G := G) = F := by
  refine ComposableArrows.ext (fun i => (liftPt F p0 hp0 i).property) (fun i hi => ?_)
  change quotFunctor.map (ComposableArrows.map'
    (ComposableArrows.mkOfObjOfMapSucc (fun i => (liftPt F p0 hp0 i).val)
      (fun i => homOfLE (liftPt_le F p0 hp0 i))) i (i + 1)) = _
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  change quotHom (liftPt_le F p0 hp0 ⟨i, hi⟩) = _
  rw [liftPt_quotHom]
  rfl

theorem thetaApp_surjective (Δ : SimplexCategoryᵒᵖ) :
    Function.Surjective (thetaApp (G := G) (P := P) Δ) := by
  intro F
  refine ⟨Quotient.mk'' (liftChain F (Quotient.out (F.obj 0)) (Quotient.out_eq' _)), ?_⟩
  rw [thetaApp_mk]
  exact liftChain_comp_quotFunctor F _ _

/-- The recovery identity: `L.obj i.succ` is the unique upper endpoint of the `Q`-image
edge above `L.obj i.castSucc`. -/
theorem recover (L : ComposableArrows P m) (i : Fin m) :
    L.obj i.succ = (QuotCat.homEquivUpSet (L.obj i.castSucc)
      (Quotient.mk'' (L.obj i.succ) : QuotCat P G)
      (quotHom (leOfHom (L.map (homOfLE (Fin.castSucc_le_succ i)))))).val :=
  (homEquivUpSet_quotHom (G := G) (leOfHom (L.map (homOfLE (Fin.castSucc_le_succ i))))).symm

/-- Congruence for the upper-endpoint map. -/
theorem homEquivUpSet_val_congr {a a' : P} {Y Y' : QuotCat P G}
    (φ : (Quotient.mk'' a : QuotCat P G) ⟶ Y) (φ' : (Quotient.mk'' a' : QuotCat P G) ⟶ Y')
    (ha : a = a') (hY : Y = Y') (hφ : HEq φ φ') :
    (QuotCat.homEquivUpSet a Y φ).val = (QuotCat.homEquivUpSet a' Y' φ').val := by
  subst ha; subst hY
  rw [eq_of_heq hφ]

/-- **Lift uniqueness (object level).**  Two `P`-chains with the same `Q`-image and the same
initial vertex agree pointwise. -/
theorem obj_eq_of_comp_eq {L L' : ComposableArrows P m}
    (hQ : L ⋙ quotFunctor (G := G) = L' ⋙ quotFunctor (G := G)) (h0 : L.obj 0 = L'.obj 0) :
    ∀ i : Fin (m + 1), L.obj i = L'.obj i := by
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i IH =>
    rw [recover (G := G) L i, recover (G := G) L' i]
    refine homEquivUpSet_val_congr _ _ IH (congrArg (fun D => D.obj i.succ) hQ) ?_
    show HEq (ComposableArrows.map' (L ⋙ quotFunctor (G := G)) i.val (i.val + 1))
      (ComposableArrows.map' (L' ⋙ quotFunctor (G := G)) i.val (i.val + 1))
    rw [hQ]

/-- **Injectivity.** -/
theorem thetaApp_injective (Δ : SimplexCategoryᵒᵖ) :
    Function.Injective (thetaApp (G := G) (P := P) Δ) := by
  intro a b hab
  induction a using Quotient.inductionOn' with
  | h L =>
    induction b using Quotient.inductionOn' with
    | h L' =>
      rw [thetaApp_mk, thetaApp_mk] at hab
      -- align the two initial vertices
      have h0orbit : (Quotient.mk'' (L.obj 0) : QuotCat P G) = Quotient.mk'' (L'.obj 0) :=
        congrArg (fun D => D.obj 0) hab
      obtain ⟨g, hg⟩ := Quotient.exact' h0orbit
      -- replace L' by `g • L'`
      have hQ : L ⋙ quotFunctor (G := G) = (g • L') ⋙ quotFunctor (G := G) := by
        rw [composableArrows_smul_def, Functor.assoc, smulFunctor_comp_quotFunctor]; exact hab
      have h0 : L.obj 0 = (g • L').obj 0 := hg.symm
      have hLL' : L = g • L' :=
        ComposableArrows.ext (obj_eq_of_comp_eq hQ h0) (fun _ _ => Subsingleton.elim _ _)
      apply Quotient.sound'
      exact ⟨g, hLL'.symm⟩

/-- `θ` is levelwise bijective, hence an isomorphism of simplicial sets. -/
noncomputable def nerveQuotIso : nerveQuot (G := G) (P := P) ≅ nerve (QuotCat P G) :=
  haveI : ∀ Δ, IsIso ((theta (G := G) (P := P)).app Δ) := fun Δ => by
    rw [CategoryTheory.isIso_iff_bijective]
    exact ⟨thetaApp_injective Δ, thetaApp_surjective Δ⟩
  haveI : IsIso (theta (G := G) (P := P)) := NatIso.isIso_of_isIso_app _
  asIso (theta (G := G) (P := P))

end Generic

/-! ## Opposite / order-dual transport

`OrderDual P` is a definitional synonym of `P` carrying the same `G`-action, giving a categorical
iso `opQuotCatIso : (P // G)ᵒᵖ ≅ Pᵒᵈ // G` (built from the span-swap machinery below).  Composed
with `nerveQuotIso` at `Pᵒᵈ`, this yields `nerveQuotIso_of_catIso`. -/

section Assembly

universe u

variable {G P : Type u} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-! ### Object casts and span swaps

`OrderDual P` is a *definitional* synonym of `P` on which the `G`-action agrees, so the two
quotient categories share objects.  The phantom `PartialOrder` parameter on `QuotCat`/`Span`
prevents Lean from silently reusing an object of one at the other in dependent positions, so we
route object casts through the two identity defs `toDualObj`/`toBaseObj`.  A `P`-span `(a, b)`
with `a ≤ b` becomes a `Pᵒᵈ`-span `(b, a)` (with the reversed inequality, which is *the same
proof* by `OrderDual`'s definitional `≤`). -/

/-- Identity cast of objects into the order-dual quotient category. -/
def toDualObj (X : QuotCat P G) : QuotCat (OrderDual P) G := X

/-- Identity cast of objects back from the order-dual quotient category. -/
def toBaseObj (X : QuotCat (OrderDual P) G) : QuotCat P G := X

@[simp] theorem toBaseObj_toDualObj (X : QuotCat P G) : toBaseObj (toDualObj X) = X := rfl

@[simp] theorem toDualObj_toBaseObj (X : QuotCat (OrderDual P) G) : toDualObj (toBaseObj X) = X :=
  rfl

/-- Swap the comparable pair of a `P`-span, reading it in the order-dual. -/
def swapSpanToDual {A B : QuotCat P G} (s : QuotCat.Span (P := P) A B) :
    QuotCat.Span (toDualObj B) (toDualObj A) := by
  refine ⟨(s.val.2, s.val.1), ?_, ?_, ?_⟩
  · exact s.property.1
  · exact s.property.2.2
  · exact s.property.2.1

/-- Swap the comparable pair of an order-dual span, reading it back in `P`. -/
def swapSpanToOp {A B : QuotCat (OrderDual P) G} (s : QuotCat.Span (P := OrderDual P) A B) :
    QuotCat.Span (toBaseObj B) (toBaseObj A) := by
  refine ⟨(s.val.2, s.val.1), ?_, ?_, ?_⟩
  · exact s.property.1
  · exact s.property.2.2
  · exact s.property.2.1

@[simp] theorem swapSpanToDual_val {A B : QuotCat P G} (s : QuotCat.Span (P := P) A B) :
    (swapSpanToDual s).val = (s.val.2, s.val.1) := rfl

@[simp] theorem swapSpanToOp_val {A B : QuotCat (OrderDual P) G}
    (s : QuotCat.Span (P := OrderDual P) A B) :
    (swapSpanToOp s).val = (s.val.2, s.val.1) := rfl

/-- The two span swaps are mutually inverse. -/
theorem swapSpanToOp_swapSpanToDual {A B : QuotCat P G} (s : QuotCat.Span (P := P) A B) :
    swapSpanToOp (swapSpanToDual s) = s := rfl

theorem swapSpanToDual_swapSpanToOp {A B : QuotCat (OrderDual P) G}
    (s : QuotCat.Span (P := OrderDual P) A B) :
    swapSpanToDual (swapSpanToOp s) = s := rfl

/-- The descended span-swap on morphisms: `Mor A B → Mor (Bᵒᵈ) (Aᵒᵈ)`. -/
def swapMorToDual {A B : QuotCat P G} (f : A ⟶ B) :
    toDualObj B ⟶ toDualObj A :=
  Quotient.liftOn' f
    (fun s => (Quotient.mk'' (swapSpanToDual s) : toDualObj B ⟶ toDualObj A))
    (by rintro s t ⟨g, hg1, hg2⟩; exact Quotient.sound' ⟨g, hg2, hg1⟩)

/-- The descended span-swap on morphisms, the other way. -/
def swapMorToOp {A B : QuotCat (OrderDual P) G} (f : A ⟶ B) :
    toBaseObj B ⟶ toBaseObj A :=
  Quotient.liftOn' f
    (fun s => (Quotient.mk'' (swapSpanToOp s) : toBaseObj B ⟶ toBaseObj A))
    (by rintro s t ⟨g, hg1, hg2⟩; exact Quotient.sound' ⟨g, hg2, hg1⟩)

@[simp] theorem swapMorToDual_mk {A B : QuotCat P G} (s : QuotCat.Span (P := P) A B) :
    swapMorToDual (Quotient.mk'' s) = Quotient.mk'' (swapSpanToDual s) := rfl

@[simp] theorem swapMorToOp_mk {A B : QuotCat (OrderDual P) G}
    (s : QuotCat.Span (P := OrderDual P) A B) :
    swapMorToOp (Quotient.mk'' s) = Quotient.mk'' (swapSpanToOp s) := rfl

/-- The two morphism swaps are mutually inverse. -/
theorem swapMorToOp_swapMorToDual {A B : QuotCat P G} (f : A ⟶ B) :
    swapMorToOp (swapMorToDual f) = f := by
  induction f using Quotient.inductionOn' with
  | h s => rfl

theorem swapMorToDual_swapMorToOp {A B : QuotCat (OrderDual P) G} (f : A ⟶ B) :
    swapMorToDual (swapMorToOp f) = f := by
  induction f using Quotient.inductionOn' with
  | h s => rfl

/-- `swapMorToDual` sends identities to identities. -/
theorem swapMorToDual_id (a : QuotCat P G) :
    swapMorToDual (𝟙 a) = 𝟙 (toDualObj a) := by
  change Quotient.mk'' (swapSpanToDual (QuotCat.idSpan a))
      = Quotient.mk'' (QuotCat.idSpan (toDualObj a))
  apply Quotient.sound'
  refine ⟨align (P := OrderDual P) (Quotient.out (toDualObj a)) (Quotient.out a) ?_, ?_, ?_⟩
  · exact (Quotient.out_eq' _).trans (Quotient.out_eq' a).symm
  · exact align_smul _ _ _
  · exact align_smul _ _ _

/-- `swapMorToOp` sends identities to identities. -/
theorem swapMorToOp_id (a : QuotCat (OrderDual P) G) :
    swapMorToOp (𝟙 a) = 𝟙 (toBaseObj a) := by
  change Quotient.mk'' (swapSpanToOp (QuotCat.idSpan a))
      = Quotient.mk'' (QuotCat.idSpan (toBaseObj a))
  apply Quotient.sound'
  refine ⟨align (P := P) (Quotient.out (toBaseObj a)) (Quotient.out a) ?_, ?_, ?_⟩
  · exact (Quotient.out_eq' _).trans (Quotient.out_eq' a).symm
  · exact align_smul _ _ _
  · exact align_smul _ _ _

/-- `swapMorToDual` reverses composition (the content of contravariance). -/
theorem swapMorToDual_comp {X Y Z : QuotCat P G}
    (p : X ⟶ Y) (q : Y ⟶ Z) :
    swapMorToDual (p ≫ q) = swapMorToDual q ≫ swapMorToDual p := by
  induction p using Quotient.inductionOn' with
  | h sp =>
    induction q using Quotient.inductionOn' with
    | h sq =>
      change Quotient.mk'' (swapSpanToDual (QuotCat.compSpan sp sq))
          = Quotient.mk'' (QuotCat.compSpan (swapSpanToDual sq) (swapSpanToDual sp))
      apply Quotient.sound'
      set g₀ := QuotCat.alignPair sp sq with hg₀
      set g₁ := QuotCat.alignPair (swapSpanToDual sq) (swapSpanToDual sp) with hg₁
      -- `g₀ • sq.1 = sp.2` and `g₁ • sp.2 = sq.1`, hence `g₁ = g₀⁻¹`
      have h0 : g₀ • sq.val.1 = sp.val.2 := QuotCat.alignPair_smul sp sq
      have h1 : g₁ • sp.val.2 = sq.val.1 := QuotCat.alignPair_smul (swapSpanToDual sq)
        (swapSpanToDual sp)
      have hinv : g₁ = g₀⁻¹ := by
        apply smul_left_cancel (x := sp.val.2)
        rw [h1, ← h0, inv_smul_smul]
      refine ⟨g₀⁻¹, ?_, ?_⟩
      · simp only [swapSpanToDual_val, QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd, ← hg₀]
        exact inv_smul_smul _ _
      · simp only [swapSpanToDual_val, QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd,
          ← hg₁, hinv]

/-- `swapMorToOp` reverses composition. -/
theorem swapMorToOp_comp {X Y Z : QuotCat (OrderDual P) G}
    (p : X ⟶ Y) (q : Y ⟶ Z) :
    swapMorToOp (p ≫ q) = swapMorToOp q ≫ swapMorToOp p := by
  induction p using Quotient.inductionOn' with
  | h sp =>
    induction q using Quotient.inductionOn' with
    | h sq =>
      change Quotient.mk'' (swapSpanToOp (QuotCat.compSpan sp sq))
          = Quotient.mk'' (QuotCat.compSpan (swapSpanToOp sq) (swapSpanToOp sp))
      apply Quotient.sound'
      set g₀ := QuotCat.alignPair sp sq with hg₀
      set g₁ := QuotCat.alignPair (swapSpanToOp sq) (swapSpanToOp sp) with hg₁
      have h0 : g₀ • sq.val.1 = sp.val.2 := QuotCat.alignPair_smul sp sq
      have h1 : g₁ • sp.val.2 = sq.val.1 := QuotCat.alignPair_smul (swapSpanToOp sq)
        (swapSpanToOp sp)
      have hinv : g₁ = g₀⁻¹ := by
        apply smul_left_cancel (x := sp.val.2)
        rw [h1, ← h0, inv_smul_smul]
      refine ⟨g₀⁻¹, ?_, ?_⟩
      · simp only [swapSpanToOp_val, QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd, ← hg₀]
        exact inv_smul_smul _ _
      · simp only [swapSpanToOp_val, QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd,
          ← hg₁, hinv]

/-- The forward comparison functor `(P // G)ᵒᵖ ⥤ Pᵒᵈ // G`: identity on objects, span-swap
(contravariant) on morphisms. -/
def opFunctorFwd : (QuotCat P G)ᵒᵖ ⥤ QuotCat (OrderDual P) G where
  obj X := toDualObj X.unop
  map {X Y} f := swapMorToDual f.unop
  map_id X := swapMorToDual_id X.unop
  map_comp {X Y Z} f g := swapMorToDual_comp g.unop f.unop

/-- The inverse comparison functor `Pᵒᵈ // G ⥤ (P // G)ᵒᵖ`. -/
def opFunctorInv : QuotCat (OrderDual P) G ⥤ (QuotCat P G)ᵒᵖ where
  obj Y := Opposite.op (toBaseObj Y)
  map {Y Z} h := (swapMorToOp h).op
  map_id Y := by rw [swapMorToOp_id]; rfl
  map_comp {Y Z W} h k := by rw [swapMorToOp_comp]; rfl

@[simp] theorem opFunctorFwd_obj (X : (QuotCat P G)ᵒᵖ) :
    opFunctorFwd.obj X = toDualObj X.unop := rfl

@[simp] theorem opFunctorInv_obj (Y : QuotCat (OrderDual P) G) :
    opFunctorInv.obj Y = Opposite.op (toBaseObj Y) := rfl

/-- The opposite of the quotient category is the quotient of the order-dual poset:
`(P // G)ᵒᵖ ≅ Pᵒᵈ // G` as categories ("op commutes with the quotient").  Both functors
are the identity on objects and the span-swap on morphisms, and the swap is involutive. -/
noncomputable def opQuotCatIso :
    Cat.of ((QuotCat P G)ᵒᵖ) ≅ Cat.of (QuotCat (OrderDual P) G) where
  hom := opFunctorFwd.toCatHom
  inv := opFunctorInv.toCatHom
  hom_inv_id := by
    apply Cat.ext
    change opFunctorFwd ⋙ opFunctorInv = 𝟭 ((QuotCat P G)ᵒᵖ)
    refine _root_.CategoryTheory.Functor.ext (fun X => rfl) (fun X Y f => ?_)
    have key : opFunctorInv.map (opFunctorFwd.map f) = f := by
      change (swapMorToOp (swapMorToDual f.unop)).op = f
      rw [swapMorToOp_swapMorToDual]
      exact Quiver.Hom.op_unop f
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
      opFunctorFwd_obj, opFunctorInv_obj, toBaseObj_toDualObj, Opposite.op_unop,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    exact key
  inv_hom_id := by
    apply Cat.ext
    change opFunctorInv ⋙ opFunctorFwd = 𝟭 (QuotCat (OrderDual P) G)
    refine _root_.CategoryTheory.Functor.ext (fun X => rfl) (fun X Y f => ?_)
    have key : opFunctorFwd.map (opFunctorInv.map f) = f := by
      change swapMorToDual (swapMorToOp f) = f
      rw [swapMorToDual_swapMorToOp]
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
      opFunctorFwd_obj, opFunctorInv_obj, toDualObj_toBaseObj, Opposite.unop_op,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    exact key

/-- Any category isomorphic to `(P // G)ᵒᵖ` has nerve isomorphic to the `G`-quotient of the
nerve of the order-dual poset `Pᵒᵈ`, i.e. to `(nerve Pᵒᵈ) / G`. -/
noncomputable def nerveQuotIso_of_catIso (𝒞 : Type u) [Category.{u} 𝒞]
    (Φiso : Cat.of 𝒞 ≅ Cat.of ((QuotCat P G)ᵒᵖ)) :
    nerve 𝒞 ≅ nerveQuot (G := G) (P := OrderDual P) :=
  nerveFunctor.mapIso Φiso ≪≫ nerveFunctor.mapIso opQuotCatIso ≪≫
    (nerveQuotIso (G := G) (P := OrderDual P)).symm

end Assembly

end OrderQuotient
