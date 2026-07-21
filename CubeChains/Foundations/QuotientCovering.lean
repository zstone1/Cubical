import CubeChains.Foundations.QuotientCat
import CubeChains.Foundations.NerveQuot
import Mathlib.Combinatorics.Quiver.Covering
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Foundations/QuotientCovering — the quotient functor is a covering of quivers

For an order-free group action `G ↷ P` on a poset, the quotient functor
`quotFunctor : P ⥤ QuotCat P G` is a **covering of quivers** (`quotFunctor_isCovering`): its
`star` and `costar` maps are bijections at every vertex.  This is the order-theoretic content of
"a free order action is a covering", read off the star bijection `QuotCat.homEquivUpSet` (upward)
and its downward mirror `homEquivDownSet` built here.

Covering + symmetrisation gives **unique lifting of zigzag words**
(`symmetrify_pathStar_bijective`), packaged as the equivalence `pathLiftEquiv`.  This is the
covering engine behind the classical "a covering is `π₁`-injective": faithfulness of
`FreeGroupoid.map quotFunctor` (`quotFunctor_freeMap_faithful`), got by reflecting the free-groupoid
spur/category-functoriality relations (collapsed to `totalRel`) through the lift.
-/

open CategoryTheory Quiver

namespace OrderQuotient

open MulAction QuotCat

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P] [OrderFreeAction G P]

/-! ## Downward fixed-target representatives (mirror of `homEquivUpSet`) -/

/-- The backward map: send a morphism `X ⟶ ⟦c⟧` to its unique lower endpoint below `c`. -/
noncomputable def homToDownSet (X : QuotCat P G) (c : P) (f : X ⟶ Quotient.mk'' c) :
    {a : P // a ≤ c ∧ (Quotient.mk'' a : orbitRel.Quotient G P) = X} :=
  Quotient.liftOn' f
    (fun p =>
      ⟨align c p.val.2 p.property.2.2.symm • p.val.1, by
        refine ⟨?_, ?_⟩
        · have h2 : align c p.val.2 p.property.2.2.symm • p.val.1
              ≤ align c p.val.2 p.property.2.2.symm • p.val.2 :=
            (smul_le_smul_iff _).2 p.property.1
          rw [align_smul] at h2
          exact h2
        · rw [mk_smul_eq]; exact p.property.2.1⟩)
    (by
      rintro p q ⟨g, hg1, hg2⟩
      apply Subtype.ext
      change align c p.val.2 p.property.2.2.symm • p.val.1
          = align c q.val.2 q.property.2.2.symm • q.val.1
      have hkey : align c q.val.2 q.property.2.2.symm * g
          = align c p.val.2 p.property.2.2.symm := by
        apply align_eq c p.val.2 p.property.2.2.symm
        rw [mul_smul, hg2, align_smul]
      rw [← hkey, mul_smul, hg1])

/-- **Fixed-target representatives**: `(X ⟶ ⟦c⟧) ≃ {a // a ≤ c ∧ ⟦a⟧ = X}`. -/
noncomputable def homEquivDownSet (X : QuotCat P G) (c : P) :
    (X ⟶ Quotient.mk'' c) ≃
      {a : P // a ≤ c ∧ (Quotient.mk'' a : orbitRel.Quotient G P) = X} where
  toFun := homToDownSet X c
  invFun a := Quotient.mk'' ⟨(a.val, c), a.property.1, a.property.2, rfl⟩
  left_inv := by
    intro f
    induction f using Quotient.inductionOn' with
    | h p =>
      apply Quotient.sound'
      refine ⟨(align c p.val.2 p.property.2.2.symm)⁻¹, ?_, ?_⟩
      · change (align c p.val.2 p.property.2.2.symm)⁻¹
            • (align c p.val.2 p.property.2.2.symm • p.val.1) = p.val.1
        exact inv_smul_smul _ _
      · change (align c p.val.2 p.property.2.2.symm)⁻¹ • c = p.val.2
        rw [inv_smul_eq_iff]
        exact (align_smul c p.val.2 p.property.2.2.symm).symm
  right_inv := by
    intro a
    apply Subtype.ext
    change align c c rfl • a.val = a.val
    rw [align_self, one_smul]

/-- The inverse of `homEquivDownSet`, as an `eqToHom` composed with a `quotHom`. -/
theorem homEquivDownSet_symm_eq {c : P} {X : QuotCat P G}
    (a : {a : P // a ≤ c ∧ (Quotient.mk'' a : QuotCat P G) = X}) :
    (homEquivDownSet X c).symm a = eqToHom a.property.2.symm ≫ quotHom a.property.1 := by
  obtain ⟨a0, hac, haX⟩ := a
  subst haX
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- The unique lower endpoint of `quotHom hab` under its target `b` is `a`. -/
theorem homEquivDownSet_quotHom {a b : P} (hab : a ≤ b) :
    ((homEquivDownSet (Quotient.mk'' a : QuotCat P G) b) (quotHom hab)).val = a := by
  change (homToDownSet (Quotient.mk'' a : QuotCat P G) b (quotHom hab)).val = a
  simp only [homToDownSet, quotHom, Quotient.liftOn'_mk'']
  rw [align_self, one_smul]

/-! ## `quotFunctor` is a quiver covering -/

/-- Congruence for the lower-endpoint map (mirror of `homEquivUpSet_val_congr`). -/
theorem homEquivDownSet_val_congr {c c' : P} {X X' : QuotCat P G}
    (φ : X ⟶ Quotient.mk'' c) (φ' : X' ⟶ Quotient.mk'' c')
    (hc : c = c') (hX : X = X') (hφ : HEq φ φ') :
    (homEquivDownSet X c φ).val = (homEquivDownSet X' c' φ').val := by
  subst hc; subst hX
  rw [eq_of_heq hφ]

/-- The star map computes to the `quotHom` of the arrow (definitional unfolding). -/
theorem star_apply_quotHom (p v : P) (e : p ⟶ v) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.star p ⟨v, e⟩
      = ⟨Quotient.mk'' v, quotHom (leOfHom e)⟩ := rfl

/-- The costar map computes to the `quotHom` of the arrow (definitional unfolding). -/
theorem costar_apply_quotHom (v u : P) (e : u ⟶ v) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.costar v ⟨u, e⟩
      = ⟨Quotient.mk'' u, quotHom (leOfHom e)⟩ := rfl

theorem star_bijective (p : P) :
    Function.Bijective ((quotFunctor (G := G) (P := P)).toPrefunctor.star p) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun s => ⟨(homEquivUpSet p s.1 s.2).val, homOfLE (homEquivUpSet p s.1 s.2).property.1⟩,
    ?_, ?_⟩
  · rintro ⟨v, e⟩
    rw [star_apply_quotHom]
    have hval : (homEquivUpSet p (Quotient.mk'' v : QuotCat P G) (quotHom (leOfHom e))).val = v :=
      homEquivUpSet_quotHom (leOfHom e)
    refine Sigma.ext hval ?_
    exact Subsingleton.helim (congrArg (fun x => (p ⟶ x)) hval) _ _
  · rintro ⟨Y, φ⟩
    have hφ : φ = quotHom (homEquivUpSet p Y φ).property.1
        ≫ eqToHom (homEquivUpSet p Y φ).property.2 := by
      conv_lhs => rw [← Equiv.symm_apply_apply (homEquivUpSet p Y) φ]
      exact homEquivUpSet_symm_eq _
    dsimp only
    rw [star_apply_quotHom]
    refine Sigma.ext (homEquivUpSet p Y φ).property.2 ?_
    conv_rhs => rw [hφ]
    exact (comp_eqToHom_heq (quotHom (homEquivUpSet p Y φ).property.1)
      (homEquivUpSet p Y φ).property.2).symm

theorem costar_bijective (v : P) :
    Function.Bijective ((quotFunctor (G := G) (P := P)).toPrefunctor.costar v) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun s =>
      ⟨(homEquivDownSet s.1 v s.2).val, homOfLE (homEquivDownSet s.1 v s.2).property.1⟩,
    ?_, ?_⟩
  · rintro ⟨u, e⟩
    rw [costar_apply_quotHom]
    have hval : (homEquivDownSet (Quotient.mk'' u : QuotCat P G) v (quotHom (leOfHom e))).val = u :=
      homEquivDownSet_quotHom (leOfHom e)
    refine Sigma.ext hval ?_
    exact Subsingleton.helim (congrArg (fun x => (x ⟶ v)) hval) _ _
  · rintro ⟨X, φ⟩
    have hφ : φ = eqToHom (homEquivDownSet X v φ).property.2.symm
        ≫ quotHom (homEquivDownSet X v φ).property.1 := by
      conv_lhs => rw [← Equiv.symm_apply_apply (homEquivDownSet X v) φ]
      exact homEquivDownSet_symm_eq _
    dsimp only
    rw [costar_apply_quotHom]
    refine Sigma.ext (homEquivDownSet X v φ).property.2 ?_
    conv_rhs => rw [hφ]
    exact (eqToHom_comp_heq (quotHom (homEquivDownSet X v φ).property.1)
      (homEquivDownSet X v φ).property.2.symm).symm

/-- `quotFunctor` is a covering of quivers: star and costar are bijections everywhere. -/
theorem quotFunctor_isCovering :
    (quotFunctor (G := G) (P := P)).toPrefunctor.IsCovering :=
  ⟨star_bijective, costar_bijective⟩

/-- The symmetrified quotient functor is a covering: `star` and `costar` on the symmetrified
quiver (which allow zigzag arrows) are bijections. -/
theorem symmetrify_isCovering :
    (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.IsCovering :=
  quotFunctor_isCovering.symmetrify

/-- **Unique lifting of zigzag words.**  For every base point `u : P`, the map on path-stars of
the symmetrified quiver is a bijection: every word (zigzag) out of `⟦u⟧` lifts uniquely to a word
out of `u`. -/
theorem symmetrify_pathStar_bijective (u : P) :
    Function.Bijective
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.pathStar
        (Quiver.Symmetrify.of.obj u)) :=
  symmetrify_isCovering.pathStar_bijective _

/-! ## Path lifting as an equivalence, and its compositional structure -/

/-- The unique-lifting bijection on path-stars, packaged as an equivalence. -/
noncomputable def pathLiftEquiv (u : P) :
    Quiver.PathStar (U := Quiver.Symmetrify P) u ≃
      Quiver.PathStar
        ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u) :=
  Equiv.ofBijective _ (symmetrify_pathStar_bijective u)

@[simp] theorem pathLiftEquiv_apply (u : P) (s : Quiver.PathStar (U := Quiver.Symmetrify P) u) :
    pathLiftEquiv u s = (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.pathStar u s := rfl

/-! ## Faithfulness of `FreeGroupoid.map quotFunctor`

The classical "a covering is `π₁`-injective": we reflect the free-groupoid word relations through
the unique lifting of zigzag words.  The plan is to collapse the two-level quotient defining
`FreeGroupoid C` (spurs `redStep` then category functoriality `homRel`) to a single relation
`totalRel` on zigzag words, then reflect a single `EqvGen` of it through the covering. -/

section FreeGroupoidFaithful

open CategoryTheory CategoryTheory.FreeGroupoid Quiver Relation

/-- The word-level functor from zigzag words in `Symmetrify C` to the free groupoid on `C`:
`Quotient.functor` by spurs, then by category functoriality. -/
def wordFunctor (C : Type*) [Category C] :
    CategoryTheory.Paths (Quiver.Symmetrify C) ⥤ CategoryTheory.FreeGroupoid C :=
  CategoryTheory.Quotient.functor (Quiver.FreeGroupoid.redStep (V := C)) ⋙
    CategoryTheory.Quotient.functor (CategoryTheory.FreeGroupoid.homRel C)

/-- The forward embedding of a category into zigzag words: a `C`-arrow becomes a length-one
forward word.  Routing through this prefunctor keeps objects genuinely typed in
`Paths (Symmetrify C)`, avoiding the `Symmetrify`/`Paths` synonym instance clash. -/
def posP (C : Type*) [Category C] : C ⥤q CategoryTheory.Paths (Quiver.Symmetrify C) :=
  (Quiver.Symmetrify.of).comp (CategoryTheory.Paths.of (Quiver.Symmetrify C))

theorem wordFunctor_map_posP {C : Type*} [Category C] {x y : C} (f : x ⟶ y) :
    (wordFunctor C).map ((posP C).map f) = homMk f := rfl

/-- The category-functoriality relation on zigzag words (the pullback of `homRel` to words):
a forward composite `f ≫ g` is the concatenation of its factors, and a forward identity is `nil`. -/
inductive funct (C : Type*) [Category C] :
    HomRel (CategoryTheory.Paths (Quiver.Symmetrify C))
  | idr (X : C) : funct C ((posP C).map (𝟙 X)) (𝟙 ((posP C).obj X))
  | compr {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
      funct C ((posP C).map (f ≫ g)) ((posP C).map f ≫ (posP C).map g)

/-- The combined word relation: spurs plus category functoriality. -/
def totalRel (C : Type*) [Category C] :
    HomRel (CategoryTheory.Paths (Quiver.Symmetrify C)) :=
  fun _ _ p q => Quiver.FreeGroupoid.redStep p q ∨ funct C p q

theorem totalRel_of_redStep {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {p q : X ⟶ Y}
    (h : Quiver.FreeGroupoid.redStep p q) : totalRel C p q := Or.inl h

theorem totalRel_of_funct {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {p q : X ⟶ Y}
    (h : funct C p q) : totalRel C p q := Or.inr h

/-- `wordFunctor` identifies both sides of any `totalRel` generator. -/
theorem wordFunctor_map_totalRel {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {p q : X ⟶ Y} (h : totalRel C p q) :
    (wordFunctor C).map p = (wordFunctor C).map q := by
  rcases h with hred | hf
  · exact congrArg (CategoryTheory.Quotient.functor (CategoryTheory.FreeGroupoid.homRel C)).map
      (CategoryTheory.Quotient.sound _ hred)
  · cases hf with
    | idr X =>
        rw [wordFunctor_map_posP]
        exact ((of C).map_id X).trans
          (CategoryTheory.Functor.map_id (wordFunctor C) _).symm
    | compr f g =>
        rw [wordFunctor_map_posP, Functor.map_comp, wordFunctor_map_posP, wordFunctor_map_posP]
        exact (of C).map_comp f g

/-- **Forward collapse.** `EqvGen` of `totalRel` steps implies equality of words in the free
groupoid. -/
theorem wordFunctor_map_eq_of_eqvGen {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {p q : X ⟶ Y}
    (h : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) p q) :
    (wordFunctor C).map p = (wordFunctor C).map q := by
  induction h with
  | rel s t hst =>
      obtain ⟨a, b, f, m1, m2, g, hm⟩ := hst
      simp only [Functor.map_comp]
      rw [wordFunctor_map_totalRel hm]
  | refl s => rfl
  | symm s t _ ih => exact ih.symm
  | trans s t u _ _ ih1 ih2 => exact ih1.trans ih2

/-- Spurs (the quotient defining `Quiver.FreeGroupoid`) refine to `totalRel`. -/
def redFunctor (C : Type*) [Category C] :
    CategoryTheory.Paths (Quiver.Symmetrify C) ⥤ Quiver.FreeGroupoid C :=
  CategoryTheory.Quotient.functor (Quiver.FreeGroupoid.redStep (V := C))

instance redFunctor_full (C : Type*) [Category C] : (redFunctor C).Full :=
  CategoryTheory.Quotient.full_functor _

theorem redFunctor_posP {C : Type*} [Category C] {x y : C} (f : x ⟶ y) :
    (redFunctor C).map ((posP C).map f) = (Quiver.FreeGroupoid.of C).map f := rfl

theorem wordFunctor_eq (C : Type*) [Category C] :
    wordFunctor C = redFunctor C ⋙ CategoryTheory.Quotient.functor
      (CategoryTheory.FreeGroupoid.homRel C) := rfl

/-- Equal `redFunctor`-images reflect to an `EqvGen` of `totalRel` (spurs alone suffice). -/
theorem eqvGen_totalRel_of_redFunctor_eq {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {pa pb : X ⟶ Y}
    (h : (redFunctor C).map pa = (redFunctor C).map pb) :
    Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) pa pb := by
  refine ((CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen
      (Quiver.FreeGroupoid.redStep (V := C)) pa pb).mp h).mono (fun a b hr => ?_)
  obtain ⟨s, t, f, m1, m2, g, hrr⟩ := hr
  exact HomRel.CompClosure.intro _ _ f m1 m2 g (Or.inl hrr)

/-- **Backward collapse.** Equality of words in the free groupoid reflects to an `EqvGen` of
`totalRel` steps.  We reflect the outer (category-functoriality) `EqvGen` step by step, choosing
zigzag-word representatives via fullness of `redFunctor`. -/
theorem eqvGen_totalRel_of_wordFunctor_map_eq {C : Type*} [Category C]
    {X Y : CategoryTheory.Paths (Quiver.Symmetrify C)} {p q : X ⟶ Y}
    (h : (wordFunctor C).map p = (wordFunctor C).map q) :
    Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) p q := by
  have hE : Relation.EqvGen
      (@HomRel.CompClosure _ _ (CategoryTheory.FreeGroupoid.homRel C) _ _)
      ((redFunctor C).map p) ((redFunctor C).map q) :=
    (CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen
      (CategoryTheory.FreeGroupoid.homRel C) ((redFunctor C).map p) ((redFunctor C).map q)).mp h
  suffices key : ∀ {A B : (redFunctor C).obj X ⟶ (redFunctor C).obj Y},
      Relation.EqvGen (@HomRel.CompClosure _ _ (CategoryTheory.FreeGroupoid.homRel C) _ _) A B →
      ∀ (pa pb : X ⟶ Y), (redFunctor C).map pa = A → (redFunctor C).map pb = B →
        Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) pa pb by
    exact key hE p q rfl rfl
  intro A B hAB
  induction hAB with
  | rel A B hAB =>
      intro pa pb hpa hpb
      obtain ⟨a', b', fa, m1, m2, ga, hm⟩ := hAB
      cases hm with
      | map_id X0 =>
          obtain ⟨pfa, hfa⟩ :=
            (redFunctor C).map_surjective (Y := (posP C).obj X0) fa
          obtain ⟨pga, hga⟩ :=
            (redFunctor C).map_surjective (X := (posP C).obj X0) ga
          have h1 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) pa
              (pfa ≫ (posP C).map (𝟙 X0) ≫ pga) :=
            eqvGen_totalRel_of_redFunctor_eq (by
              rw [hpa]
              simp only [CategoryTheory.Functor.map_comp, hfa, hga]
              rfl)
          have h2 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _)
              (pfa ≫ (posP C).map (𝟙 X0) ≫ pga) (pfa ≫ 𝟙 ((posP C).obj X0) ≫ pga) :=
            Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ pfa
              ((posP C).map (𝟙 X0)) (𝟙 ((posP C).obj X0)) pga (totalRel_of_funct (funct.idr X0)))
          have h3 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _)
              (pfa ≫ 𝟙 ((posP C).obj X0) ≫ pga) pb :=
            eqvGen_totalRel_of_redFunctor_eq (by
              rw [hpb]
              simp only [CategoryTheory.Functor.map_comp, hfa, hga]
              rfl)
          exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2 h3)
      | map_comp f g =>
          obtain ⟨pfa, hfa⟩ :=
            (redFunctor C).map_surjective (Y := (posP C).obj _) fa
          obtain ⟨pga, hga⟩ :=
            (redFunctor C).map_surjective (X := (posP C).obj _) ga
          have h1 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _) pa
              (pfa ≫ (posP C).map (f ≫ g) ≫ pga) :=
            eqvGen_totalRel_of_redFunctor_eq (by
              rw [hpa]
              simp only [CategoryTheory.Functor.map_comp, hfa, hga]
              rfl)
          have h2 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _)
              (pfa ≫ (posP C).map (f ≫ g) ≫ pga)
              (pfa ≫ ((posP C).map f ≫ (posP C).map g) ≫ pga) :=
            Relation.EqvGen.rel _ _ (HomRel.CompClosure.intro _ _ pfa
              ((posP C).map (f ≫ g)) ((posP C).map f ≫ (posP C).map g) pga
              (totalRel_of_funct (funct.compr f g)))
          have h3 : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel C) _ _)
              (pfa ≫ ((posP C).map f ≫ (posP C).map g) ≫ pga) pb :=
            eqvGen_totalRel_of_redFunctor_eq (by
              rw [hpb]
              simp only [CategoryTheory.Functor.map_comp, hfa, hga]
              rfl)
          exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2 h3)
  | refl A =>
      intro pa pb hpa hpb
      exact eqvGen_totalRel_of_redFunctor_eq (hpa.trans hpb.symm)
  | symm A B _ ih =>
      intro pa pb hpa hpb
      exact Relation.EqvGen.symm _ _ (ih pb pa hpb hpa)
  | trans A B D _ _ ih1 ih2 =>
      intro pa pb hpa hpb
      obtain ⟨pm, hpm⟩ := (redFunctor C).map_surjective B
      exact Relation.EqvGen.trans _ _ _ (ih1 pa pm hpa hpm) (ih2 pm pb hpm hpb)

/-- A single backward zigzag letter maps to the inverse of the forward generator. -/
theorem wordFunctor_map_neg {C : Type*} [Category C] {x y : C} (f : x ⟶ y) :
    (wordFunctor C).map (Quiver.Path.reverse ((posP C).map f)) = inv (homMk f) := by
  have hspur : homMk f ≫ (wordFunctor C).map (Quiver.Path.reverse ((posP C).map f)) = 𝟙 (mk x) := by
    have hword : (wordFunctor C).map ((posP C).map f ≫ Quiver.Path.reverse ((posP C).map f))
        = (wordFunctor C).map (𝟙 ((CategoryTheory.Paths.of (Quiver.Symmetrify C)).obj x)) :=
      (congrArg (CategoryTheory.Quotient.functor (CategoryTheory.FreeGroupoid.homRel C)).map
        (CategoryTheory.Quotient.sound (Quiver.FreeGroupoid.redStep (V := C))
          (Quiver.FreeGroupoid.redStep.step x y (Sum.inl f)))).symm
    rw [CategoryTheory.Functor.map_comp, wordFunctor_map_posP,
      CategoryTheory.Functor.map_id] at hword
    exact hword
  exact CategoryTheory.IsIso.eq_inv_of_hom_inv_id hspur

theorem wordFunctor_map_comp {C : Type*} [Category C] {a b c : Quiver.Symmetrify C}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (wordFunctor C).map (Quiver.Path.comp p q) = (wordFunctor C).map p ≫ (wordFunctor C).map q :=
  CategoryTheory.Functor.map_comp (wordFunctor C) p q

/-- On a single zigzag letter, `FreeGroupoid.map quotFunctor` intertwines the two word
functors through the symmetrified quotient prefunctor. -/
theorem map_quotFunctor_wordFunctor_letter
    {a b : Quiver.Symmetrify P} (e : a ⟶ b) :
    (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map
        ((wordFunctor P).map (Quiver.Hom.toPath e))
      = (wordFunctor (QuotCat P G)).map (Quiver.Hom.toPath
          ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.map e)) := by
  rcases e with f | f
  · change (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map
          ((wordFunctor P).map ((posP P).map f))
        = (wordFunctor (QuotCat P G)).map ((posP (QuotCat P G)).map (quotFunctor.map f))
    rw [wordFunctor_map_posP, wordFunctor_map_posP]
    exact CategoryTheory.FreeGroupoid.map_map_homMk quotFunctor f
  · change (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map
          ((wordFunctor P).map (Quiver.Path.reverse ((posP P).map f)))
        = (wordFunctor (QuotCat P G)).map
            (Quiver.Path.reverse ((posP (QuotCat P G)).map (quotFunctor.map f)))
    rw [wordFunctor_map_neg, wordFunctor_map_neg]
    exact CategoryTheory.Functor.map_inv _ _

/-! ### Reflection of the word relation through unique lifting -/

/-- The unique lift of a downstairs zigzag word to an upstairs one, out of a chosen base. -/
noncomputable def liftPS (u : P) :
    Quiver.PathStar ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u) →
      Quiver.PathStar (U := Quiver.Symmetrify P) u :=
  (pathLiftEquiv u).symm

/-- The lift inverts `pathStar`: the lift of the `φ`-image of an upstairs word is that word. -/
theorem liftPS_pathLiftEquiv (u : P) (S : Quiver.PathStar (U := Quiver.Symmetrify P) u) :
    liftPS u (pathLiftEquiv (G := G) u S) = S :=
  (pathLiftEquiv u).symm_apply_apply S

/-- `φ.obj` of the lift's endpoint recovers the downstairs endpoint. -/
theorem liftPS_obj (u : P)
    (S : Quiver.PathStar ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u)) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj (liftPS u S).1 = S.1 :=
  congrArg Sigma.fst ((pathLiftEquiv u).apply_symm_apply S)

/-- `φ.mapPath` of the lifted word recovers the downstairs word (heterogeneously in the endpoint). -/
theorem liftPS_mapPath_heq (u : P)
    (S : Quiver.PathStar ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u)) :
    HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath (liftPS u S).2) S.2 := by
  have h := (pathLiftEquiv u).apply_symm_apply S
  rw [pathLiftEquiv_apply] at h
  exact (Sigma.ext_iff.mp h).2

/-- Heterogeneous congruence for path composition along endpoint equalities. -/
theorem path_comp_heq {V : Type*} [Quiver V] {a b b' c c' : V} (hb : b = b') (hc : c = c')
    {γ : Quiver.Path a b} {δ : Quiver.Path b c} {γ' : Quiver.Path a b'} {δ' : Quiver.Path b' c'}
    (hγ : HEq γ γ') (hδ : HEq δ δ') : HEq (γ.comp δ) (γ'.comp δ') := by
  subst hb; subst hc
  rw [eq_of_heq hγ, eq_of_heq hδ]

/-- Recognising the lift by exhibiting its `pathStar` image. -/
theorem liftPS_eq (u : P)
    (D : Quiver.PathStar ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u))
    (T : Quiver.PathStar (U := Quiver.Symmetrify P) u)
    (h : pathLiftEquiv (G := G) u T = D) : liftPS u D = T := by
  rw [← h]; exact (pathLiftEquiv u).symm_apply_apply T

/-- The lift of a concatenation is the concatenation of the lifts (endpoints matched by the
covering-image equalities and the word `HEq`s). -/
theorem liftPS_comp (u : P) {w x : Quiver.Symmetrify (QuotCat P G)}
    {γ : Quiver.Path ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u) w}
    {δ : Quiver.Path w x}
    {v1 v2 : Quiver.Symmetrify P}
    {gg : Quiver.Path (Quiver.Symmetrify.of.obj u) v1} {dd : Quiver.Path v1 v2}
    (hv1 : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj v1 = w)
    (hv2 : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj v2 = x)
    (hgg : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath gg) γ)
    (hdd : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath dd) δ) :
    liftPS u ⟨x, γ.comp δ⟩ = ⟨v2, gg.comp dd⟩ := by
  refine liftPS_eq u _ ⟨v2, gg.comp dd⟩ ?_
  rw [pathLiftEquiv_apply, Prefunctor.pathStar_apply]
  refine Sigma.ext hv2 (?_ : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
    (gg.comp dd)) (γ.comp δ))
  rw [Prefunctor.mapPath_comp]
  exact path_comp_heq hv1 hv2 hgg hdd

/-- The unique lift of a single downstairs symmetrified arrow, out of a chosen base. -/
noncomputable def liftStar (w : Quiver.Symmetrify P) :
    Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj w) →
      Quiver.Star w :=
  (Equiv.ofBijective _ (symmetrify_isCovering.star_bijective w)).symm

theorem liftStar_obj (w : Quiver.Symmetrify P)
    (E : Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj w)) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj (liftStar w E).1 = E.1 :=
  congrArg Sigma.fst
    ((Equiv.ofBijective _ (symmetrify_isCovering.star_bijective w)).apply_symm_apply E)

theorem liftStar_map_heq (w : Quiver.Symmetrify P)
    (E : Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj w)) :
    HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.map (liftStar w E).2) E.2 := by
  have h := (Equiv.ofBijective _ (symmetrify_isCovering.star_bijective w)).apply_symm_apply E
  exact (Sigma.ext_iff.mp h).2

/-- **Naturality.**  `FreeGroupoid.map quotFunctor` sends the `P`-word of `p` to the
`QuotCat`-word of `φ p`, where `φ` is the symmetrified quotient prefunctor. -/
theorem map_quotFunctor_wordFunctor {x y : CategoryTheory.Paths (Quiver.Symmetrify P)}
    (p : x ⟶ y) :
    (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).map ((wordFunctor P).map p)
      = (wordFunctor (QuotCat P G)).map
          ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath p) := by
  induction p using CategoryTheory.Paths.induction with
  | id => exact CategoryTheory.Functor.map_id _ _
  | comp p q ih =>
      simp only [CategoryTheory.Paths.of_map, CategoryTheory.Functor.map_comp, ih,
        Prefunctor.mapPath_comp', wordFunctor_map_comp]
      exact congrArg _ (map_quotFunctor_wordFunctor_letter q)

/-! ### Generic heterogeneous congruence helpers -/

/-- Heterogeneous congruence for path composition when *all three* endpoints may differ. -/
theorem path_comp_heq' {V : Type*} [Quiver V] {a a' b b' c c' : V}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {γ : Quiver.Path a b} {δ : Quiver.Path b c} {γ' : Quiver.Path a' b'} {δ' : Quiver.Path b' c'}
    (hγ : HEq γ γ') (hδ : HEq δ δ') : HEq (γ.comp δ) (γ'.comp δ') := by
  subst ha; subst hb; subst hc
  obtain rfl := eq_of_heq hγ; obtain rfl := eq_of_heq hδ; exact HEq.rfl

/-- HEq congruence for a spur word `e.toPath ≫ (reverse e).toPath` under an endpoint move. -/
theorem redword_heq {V : Type*} [Quiver V] [Quiver.HasReverse V] {c d d' : V} (hd : d = d')
    {e1 : c ⟶ d} {e2 : c ⟶ d'} (h : HEq e1 e2) :
    HEq ((Quiver.Hom.toPath e1).comp (Quiver.reverse e1).toPath)
        ((Quiver.Hom.toPath e2).comp (Quiver.reverse e2).toPath) := by
  subst hd; obtain rfl := eq_of_heq h; exact HEq.rfl

/-! ### The word functor is full (so every free-groupoid arrow comes from a word). -/

instance wordFunctor_full (C : Type*) [Category C] : (wordFunctor C).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ :=
      (CategoryTheory.Quotient.functor (CategoryTheory.FreeGroupoid.homRel C)).map_surjective f
    obtain ⟨p, hp⟩ := (redFunctor C).map_surjective g
    refine ⟨p, ?_⟩
    change (CategoryTheory.Quotient.functor (CategoryTheory.FreeGroupoid.homRel C)).map
        ((redFunctor C).map p) = f
    rw [hp]; exact hg

/-! ### The forward (non-symmetrified) unique lift of a single arrow. -/

/-- The unique lift of a single downstairs (forward) arrow to an upstairs `P`-arrow. -/
noncomputable def liftStarFwd (w : P) :
    Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.obj w) → Quiver.Star w :=
  (Equiv.ofBijective _ (star_bijective w)).symm

theorem liftStarFwd_obj (w : P)
    (E : Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.obj w)) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.obj (liftStarFwd w E).1 = E.1 :=
  congrArg Sigma.fst ((Equiv.ofBijective _ (star_bijective w)).apply_symm_apply E)

theorem liftStarFwd_map_heq (w : P)
    (E : Quiver.Star ((quotFunctor (G := G) (P := P)).toPrefunctor.obj w)) :
    HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.map (liftStarFwd w E).2) E.2 :=
  (Sigma.ext_iff.mp ((Equiv.ofBijective _ (star_bijective w)).apply_symm_apply E)).2

/-- `φ.mapPath` of a forward `P`-word is the corresponding forward `QuotCat`-word. -/
theorem mapPath_posP {x y : P} (h : x ⟶ y) :
    (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath ((posP P).map h)
      = (posP (QuotCat P G)).map ((quotFunctor (G := G) (P := P)).map h) := rfl

/-- HEq congruence: the forward word of a composite `f ≫ g`, under endpoint moves. -/
theorem posQ_comp_heq {x : QuotCat P G} {yt zt : P} {Y Z : QuotCat P G}
    (hY : (quotFunctor (G := G) (P := P)).obj yt = Y)
    (hZ : (quotFunctor (G := G) (P := P)).obj zt = Z)
    {f1 : x ⟶ (quotFunctor (G := G) (P := P)).obj yt}
    {g1 : (quotFunctor (G := G) (P := P)).obj yt ⟶ (quotFunctor (G := G) (P := P)).obj zt}
    {f2 : x ⟶ Y} {g2 : Y ⟶ Z} (hf : HEq f1 f2) (hg : HEq g1 g2) :
    HEq ((posP (QuotCat P G)).map (f1 ≫ g1)) ((posP (QuotCat P G)).map (f2 ≫ g2)) := by
  subst hY; subst hZ; obtain rfl := eq_of_heq hf; obtain rfl := eq_of_heq hg; exact HEq.rfl

/-- HEq congruence: the concatenation of two forward words, under endpoint moves. -/
theorem posQ_pathcomp_heq {x : QuotCat P G} {yt zt : P} {Y Z : QuotCat P G}
    (hY : (quotFunctor (G := G) (P := P)).obj yt = Y)
    (hZ : (quotFunctor (G := G) (P := P)).obj zt = Z)
    {f1 : x ⟶ (quotFunctor (G := G) (P := P)).obj yt}
    {g1 : (quotFunctor (G := G) (P := P)).obj yt ⟶ (quotFunctor (G := G) (P := P)).obj zt}
    {f2 : x ⟶ Y} {g2 : Y ⟶ Z} (hf : HEq f1 f2) (hg : HEq g1 g2) :
    HEq (((posP (QuotCat P G)).map f1).comp ((posP (QuotCat P G)).map g1))
        (((posP (QuotCat P G)).map f2).comp ((posP (QuotCat P G)).map g2)) := by
  subst hY; subst hZ; obtain rfl := eq_of_heq hf; obtain rfl := eq_of_heq hg; exact HEq.rfl

/-! ### The `PathStar`-level equivalence carrying endpoint dependency -/

/-- Two upstairs words out of `u` with a shared endpoint `v`, related by
`EqvGen (CompClosure (totalRel P))`. -/
def PSEqvGen (u : P) (S T : Quiver.PathStar (U := Quiver.Symmetrify P) u) : Prop :=
  ∃ (v : Quiver.Symmetrify P) (p q : @Quiver.Path (Quiver.Symmetrify P) _ u v),
    S = ⟨v, p⟩ ∧ T = ⟨v, q⟩ ∧
    Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel P) _ _) p q

theorem PSEqvGen.refl (u : P) (S : Quiver.PathStar (U := Quiver.Symmetrify P) u) :
    PSEqvGen u S S :=
  ⟨S.1, S.2, S.2, rfl, rfl, Relation.EqvGen.refl _⟩

theorem PSEqvGen.symm {u : P} {S T : Quiver.PathStar (U := Quiver.Symmetrify P) u}
    (h : PSEqvGen u S T) : PSEqvGen u T S := by
  obtain ⟨v, p, q, hS, hT, hE⟩ := h
  exact ⟨v, q, p, hT, hS, Relation.EqvGen.symm _ _ hE⟩

theorem PSEqvGen.trans {u : P} {S T W : Quiver.PathStar (U := Quiver.Symmetrify P) u}
    (h1 : PSEqvGen u S T) (h2 : PSEqvGen u T W) : PSEqvGen u S W := by
  obtain ⟨v, p, q, hS, hT, hE1⟩ := h1
  obtain ⟨v', q', w, hT', hW, hE2⟩ := h2
  obtain ⟨rfl, hq⟩ := Sigma.ext_iff.mp (hT.symm.trans hT')
  obtain rfl := eq_of_heq hq
  exact ⟨v, p, w, hS, hW, Relation.EqvGen.trans _ _ _ hE1 hE2⟩

/-! ### Reflection of a single word-relation generator through the covering -/

/-- Reflect one `totalRel (QuotCat P G)` generator `m1 m2 : a' ⟶ b'`, given a chosen upstairs source
`d` over `a'`, to a matched `totalRel P` generator upstairs. -/
theorem gen_reflect (d : P) {a' b' : Quiver.Symmetrify (QuotCat P G)}
    (hae : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj d = a')
    {m1 m2 : @Quiver.Path (Quiver.Symmetrify (QuotCat P G)) _ a' b'}
    (hm : totalRel (QuotCat P G) m1 m2) :
    ∃ (bt : Quiver.Symmetrify P)
      (_ : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj bt = b')
      (mt1 mt2 : @Quiver.Path (Quiver.Symmetrify P) _ d bt),
      totalRel P mt1 mt2 ∧
      HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath mt1) m1 ∧
      HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath mt2) m2 := by
  subst hae
  rcases hm with hred | hf
  · -- spur generator
    cases hred with
    | step X0 Z0 f =>
      have hZ : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj
          (liftStar d ⟨Z0, f⟩).1 = Z0 := liftStar_obj d ⟨Z0, f⟩
      have hf' : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.map
          (liftStar d ⟨Z0, f⟩).2) f := liftStar_map_heq d ⟨Z0, f⟩
      refine ⟨d, rfl, Quiver.Path.nil,
        (liftStar d ⟨Z0, f⟩).2.toPath.comp (Quiver.reverse (liftStar d ⟨Z0, f⟩).2).toPath,
        totalRel_of_redStep
          (Quiver.FreeGroupoid.redStep.step d (liftStar d ⟨Z0, f⟩).1 (liftStar d ⟨Z0, f⟩).2),
        HEq.rfl, ?_⟩
      rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath,
        Prefunctor.map_reverse]
      exact redword_heq hZ hf'
  · cases hf with
    | idr X0 =>
      refine ⟨d, rfl, (posP P).map (𝟙 d), Quiver.Path.nil,
        totalRel_of_funct (funct.idr d), ?_, HEq.rfl⟩
      exact heq_of_eq (congrArg (posP (QuotCat P G)).map
        ((quotFunctor (G := G) (P := P)).map_id d))
    | compr f g =>
      have hY : (quotFunctor (G := G) (P := P)).toPrefunctor.obj (liftStarFwd d ⟨_, f⟩).1 = _ :=
        liftStarFwd_obj d ⟨_, f⟩
      have hf' : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.map
          (liftStarFwd d ⟨_, f⟩).2) f := liftStarFwd_map_heq d ⟨_, f⟩
      have hZ : (quotFunctor (G := G) (P := P)).toPrefunctor.obj
          (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).1 = _ :=
        liftStarFwd_obj (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩
      have hg' : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.map
          (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2) g :=
        (liftStarFwd_map_heq (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).trans
          (Quiver.Hom.cast_heq hY.symm rfl g)
      refine ⟨(liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).1, hZ,
        (posP P).map ((liftStarFwd d ⟨_, f⟩).2 ≫
          (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2),
        ((posP P).map (liftStarFwd d ⟨_, f⟩).2).comp
          ((posP P).map (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2),
        totalRel_of_funct (funct.compr (liftStarFwd d ⟨_, f⟩).2
          (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2), ?_, ?_⟩
      · exact (heq_of_eq (congrArg (posP (QuotCat P G)).map
          ((quotFunctor (G := G) (P := P)).map_comp (liftStarFwd d ⟨_, f⟩).2
            (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2))).trans
          (posQ_comp_heq hY hZ hf' hg')
      · exact (heq_of_eq (((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify).mapPath_comp
          ((posP P).map (liftStarFwd d ⟨_, f⟩).2)
          ((posP P).map (liftStarFwd (liftStarFwd d ⟨_, f⟩).1 ⟨_, g.cast hY.symm rfl⟩).2))).trans
          (posQ_pathcomp_heq hY hZ hf' hg')

/-- **Reflection of the word relation.**  An `EqvGen` of `totalRel (QuotCat P G)` steps downstairs
between the `φ`-images of two words lifts to an `EqvGen` of `totalRel P` steps upstairs. -/
theorem reflectPS (u : P) {D : Quiver.Symmetrify (QuotCat P G)}
    {a b : @Quiver.Path (Quiver.Symmetrify (QuotCat P G)) _
      ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj u) D}
    (h : Relation.EqvGen (@HomRel.CompClosure _ _ (totalRel (QuotCat P G)) _ _) a b) :
    PSEqvGen u (liftPS u ⟨D, a⟩) (liftPS u ⟨D, b⟩) := by
  induction h with
  | rel s t hst =>
      obtain ⟨a', b', pa, m1, m2, pb, hm⟩ := hst
      have hae : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj
          (liftPS u ⟨a', pa⟩).1 = a' := liftPS_obj u ⟨a', pa⟩
      have hpa : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
          (liftPS u ⟨a', pa⟩).2) pa := liftPS_mapPath_heq u ⟨a', pa⟩
      obtain ⟨bt, hbe, mt1, mt2, htot, hm1, hm2⟩ :=
        gen_reflect (G := G) (P := P) (liftPS u ⟨a', pa⟩).1 hae hm
      set pbc : @Quiver.Path (Quiver.Symmetrify (QuotCat P G)) _
          ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj bt) D :=
        Quiver.Path.cast hbe.symm rfl pb with hpbc
      have hYe : (quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.obj
          (liftPS (G := G) (P := P) bt ⟨D, pbc⟩).1 = D :=
        liftPS_obj (G := G) (P := P) bt ⟨D, pbc⟩
      have hpb : HEq ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath
          (liftPS (G := G) (P := P) bt ⟨D, pbc⟩).2) pb :=
        (liftPS_mapPath_heq (G := G) (P := P) bt ⟨D, pbc⟩).trans
          (hpbc ▸ Quiver.Path.cast_heq hbe.symm rfl pb : HEq pbc pb)
      have E1 : liftPS u ⟨D, pa ≫ m1 ≫ pb⟩ = (⟨(liftPS (G := G) (P := P) bt ⟨D, pbc⟩).1,
          (liftPS u ⟨a', pa⟩).2.comp (mt1.comp (liftPS (G := G) (P := P) bt ⟨D, pbc⟩).2)⟩ :
          Quiver.PathStar (U := Quiver.Symmetrify P) u) :=
        liftPS_comp u hae hYe hpa
          (by rw [Prefunctor.mapPath_comp]; exact path_comp_heq' hae hbe hYe hm1 hpb)
      have E2 : liftPS u ⟨D, pa ≫ m2 ≫ pb⟩ = (⟨(liftPS (G := G) (P := P) bt ⟨D, pbc⟩).1,
          (liftPS u ⟨a', pa⟩).2.comp (mt2.comp (liftPS (G := G) (P := P) bt ⟨D, pbc⟩).2)⟩ :
          Quiver.PathStar (U := Quiver.Symmetrify P) u) :=
        liftPS_comp u hae hYe hpa
          (by rw [Prefunctor.mapPath_comp]; exact path_comp_heq' hae hbe hYe hm2 hpb)
      refine ⟨_, _, _, E1, E2, ?_⟩
      have hcc := HomRel.CompClosure.intro (r := totalRel P) _ _ (liftPS u ⟨a', pa⟩).2 mt1 mt2
        (liftPS (G := G) (P := P) bt ⟨D, pbc⟩).2 htot
      exact Relation.EqvGen.rel _ _ hcc
  | refl s => exact PSEqvGen.refl u _
  | symm s t _ ih => exact PSEqvGen.symm ih
  | trans s t w _ _ ih1 ih2 => exact PSEqvGen.trans ih1 ih2

/-- **Faithfulness of the free-groupoid functor.**  The classical "a covering is `π₁`-injective". -/
theorem quotFunctor_freeMap_faithful :
    (CategoryTheory.FreeGroupoid.map (quotFunctor (G := G) (P := P))).Faithful := by
  constructor
  intro A B f g hfg
  obtain ⟨p, hp⟩ := (wordFunctor P).map_surjective (X := A.as.as) (Y := B.as.as) f
  obtain ⟨q, hq⟩ := (wordFunctor P).map_surjective (X := A.as.as) (Y := B.as.as) g
  rw [← hp, ← hq] at hfg
  have hfg2 : (wordFunctor (QuotCat P G)).map
        ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath p)
      = (wordFunctor (QuotCat P G)).map
        ((quotFunctor (G := G) (P := P)).toPrefunctor.symmetrify.mapPath q) :=
    (map_quotFunctor_wordFunctor p).symm.trans (hfg.trans (map_quotFunctor_wordFunctor q))
  have hEqv := eqvGen_totalRel_of_wordFunctor_map_eq hfg2
  have hPS := reflectPS (G := G) (P := P) A.as.as hEqv
  obtain ⟨v, p', q', hSp, hTq, hE⟩ := hPS
  have hSp' : (⟨B.as.as, p⟩ : Quiver.PathStar (U := Quiver.Symmetrify P) A.as.as) = ⟨v, p'⟩ :=
    (liftPS_pathLiftEquiv (G := G) (P := P) A.as.as ⟨B.as.as, p⟩).symm.trans hSp
  have hTq' : (⟨B.as.as, q⟩ : Quiver.PathStar (U := Quiver.Symmetrify P) A.as.as) = ⟨v, q'⟩ :=
    (liftPS_pathLiftEquiv (G := G) (P := P) A.as.as ⟨B.as.as, q⟩).symm.trans hTq
  obtain ⟨rfl, hpp⟩ := Sigma.ext_iff.mp hSp'
  obtain ⟨_, hqq⟩ := Sigma.ext_iff.mp hTq'
  obtain rfl := eq_of_heq hpp
  obtain rfl := eq_of_heq hqq
  rw [← hp, ← hq]
  exact wordFunctor_map_eq_of_eqvGen hE

end FreeGroupoidFaithful

end OrderQuotient
