import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Foundations/QuotientCat — the quotient category `P // G`

The quotient category of an order-free group action on a poset.  Given
`[Group G] [PartialOrder P] [MulAction G P]` with an `OrderFreeAction G P` instance:

* objects are orbits `Quotient (MulAction.orbitRel G P)`;
* morphisms `X ⟶ Y` are the diagonal-`G` quotient of comparable pairs
  `{p : P × P // p.1 ≤ p.2 ∧ ⟦p.1⟧ = X ∧ ⟦p.2⟧ = Y}`.

The workhorse is **alignment**: whenever `⟦b⟧ = ⟦c⟧` there is a *unique* `g` with `g • c = b`
(existence from same-orbit, uniqueness from freeness); composition and the category laws all
reduce to this uniqueness.
-/

namespace OrderQuotient

open MulAction CategoryTheory

/-- An action is *order-free* when it preserves and reflects `≤`, and the only
element that can weakly move a point *up* is the identity.  The second axiom
implies genuine freeness (`g • x = x → g = 1`), which we derive below. -/
class OrderFreeAction (G P : Type*) [Group G] [PartialOrder P] [MulAction G P] :
    Prop where
  smul_le_smul_iff  : ∀ (g : G) {x y : P}, g • x ≤ g • y ↔ x ≤ y
  eq_one_of_le_smul : ∀ (g : G) (x : P), x ≤ g • x → g = 1

variable {G P : Type*} [Group G] [PartialOrder P] [MulAction G P]

section Basics

variable [OrderFreeAction G P]

/-- The action preserves and reflects `≤`. -/
theorem smul_le_smul_iff (g : G) {x y : P} : g • x ≤ g • y ↔ x ≤ y :=
  OrderFreeAction.smul_le_smul_iff g

/-- Only the identity weakly moves a point up. -/
theorem eq_one_of_le_smul (g : G) (x : P) (h : x ≤ g • x) : g = 1 :=
  OrderFreeAction.eq_one_of_le_smul g x h

/-- **Freeness**, derived from the axioms: a group element fixing a point is `1`. -/
theorem eq_one_of_smul_eq (g : G) (x : P) (h : g • x = x) : g = 1 :=
  eq_one_of_le_smul g x h.ge

/-- **Left cancellation** for the action: the uniqueness engine.
If two group elements agree on a point, they are equal. -/
theorem smul_left_cancel {g g' : G} {x : P} (h : g • x = g' • x) : g = g' := by
  have hx : (g'⁻¹ * g) • x = x := by rw [mul_smul, h, inv_smul_smul]
  have h1 : g'⁻¹ * g = 1 := eq_one_of_smul_eq _ _ hx
  exact (inv_mul_eq_one.mp h1).symm

omit [PartialOrder P] [OrderFreeAction G P] in
/-- The quotient map is invariant under the action: `⟦g • x⟧ = ⟦x⟧`. -/
theorem mk_smul_eq (g : G) (x : P) :
    (Quotient.mk'' (g • x) : orbitRel.Quotient G P) = Quotient.mk'' x :=
  Quotient.sound' (mem_orbit x g)

end Basics

/-! ## Alignment -/

section Alignment

variable [OrderFreeAction G P]

/-- **Alignment (existence + uniqueness).**  If `b` and `c` are in the same orbit,
there is a *unique* group element carrying `c` to `b`. -/
theorem align_existsUnique (b c : P)
    (h : (Quotient.mk'' b : orbitRel.Quotient G P) = Quotient.mk'' c) :
    ∃! g : G, g • c = b := by
  have hmem : b ∈ orbit G c := Quotient.exact' h
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 hmem
  exact ⟨g, hg, fun g' hg' => smul_left_cancel (hg'.trans hg.symm)⟩

/-- The chosen aligner: the unique `g` with `g • c = b` when `⟦b⟧ = ⟦c⟧`. -/
noncomputable def align (b c : P)
    (h : (Quotient.mk'' b : orbitRel.Quotient G P) = Quotient.mk'' c) : G :=
  (align_existsUnique b c h).choose

@[simp]
theorem align_smul (b c : P)
    (h : (Quotient.mk'' b : orbitRel.Quotient G P) = Quotient.mk'' c) :
    align b c h • c = b :=
  (align_existsUnique b c h).choose_spec.1

/-- Uniqueness half of alignment, packaged for rewriting. -/
theorem align_eq (b c : P)
    (h : (Quotient.mk'' b : orbitRel.Quotient G P) = Quotient.mk'' c)
    (g : G) (hg : g • c = b) : g = align b c h :=
  smul_left_cancel (hg.trans (align_smul b c h).symm)

@[simp]
theorem align_self (a : P)
    (h : (Quotient.mk'' a : orbitRel.Quotient G P) = Quotient.mk'' a) :
    align a a h = 1 :=
  (align_eq a a h 1 (by rw [one_smul])).symm

end Alignment

/-! ## The quotient category `P // G` -/

/-- Objects of the quotient category: the orbits of the action. -/
abbrev QuotCat (P G : Type*) [Group G] [PartialOrder P] [MulAction G P] : Type _ :=
  orbitRel.Quotient G P

namespace QuotCat

variable [OrderFreeAction G P]

/-- A *span* from `X` to `Y`: a comparable pair whose endpoints have orbits `X`, `Y`. -/
abbrev Span (X Y : QuotCat P G) : Type _ :=
  {p : P × P // p.1 ≤ p.2 ∧ (Quotient.mk'' p.1 : orbitRel.Quotient G P) = X
    ∧ (Quotient.mk'' p.2 : orbitRel.Quotient G P) = Y}

/-- Two spans are identified when related by the diagonal `G`-action. -/
def homSetoid (X Y : QuotCat P G) : Setoid (Span X Y) where
  r p q := ∃ g : G, g • p.val.1 = q.val.1 ∧ g • p.val.2 = q.val.2
  iseqv :=
    ⟨fun p => ⟨1, by rw [one_smul], by rw [one_smul]⟩,
     fun {p q} => fun ⟨g, h1, h2⟩ =>
       ⟨g⁻¹, by rw [← h1, inv_smul_smul], by rw [← h2, inv_smul_smul]⟩,
     fun {p q r} => fun ⟨g, hg1, hg2⟩ ⟨g', hg1', hg2'⟩ =>
       ⟨g' * g, by rw [mul_smul, hg1, hg1'], by rw [mul_smul, hg2, hg2']⟩⟩

/-- Morphisms of the quotient category `X ⟶ Y`. -/
def Mor (X Y : QuotCat P G) : Type _ := Quotient (homSetoid X Y)

/-- The identity span `(a, a)` for the canonical representative `a` of `X`. -/
noncomputable def idSpan (X : QuotCat P G) : Span X X :=
  ⟨(Quotient.out X, Quotient.out X), le_refl _, Quotient.out_eq' X, Quotient.out_eq' X⟩

/-- The aligning element of a composable pair of spans: the unique `g` carrying
`q`'s lower endpoint to `p`'s upper endpoint. -/
noncomputable def alignPair {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) : G :=
  align p.val.2 q.val.1 (p.property.2.2.trans q.property.2.1.symm)

@[simp]
theorem alignPair_smul {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) :
    alignPair p q • q.val.1 = p.val.2 :=
  align_smul _ _ _

/-- The composite span `(a, b) · (c, d) := (a, align b c • d)`. -/
noncomputable def compSpan {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) : Span X Z :=
  ⟨(p.val.1, alignPair p q • q.val.2), by
    refine ⟨?_, p.property.2.1, ?_⟩
    · have h2 : alignPair p q • q.val.1 ≤ alignPair p q • q.val.2 :=
        (smul_le_smul_iff _).2 q.property.1
      rw [alignPair_smul] at h2
      exact le_trans p.property.1 h2
    · rw [mk_smul_eq]; exact q.property.2.2⟩

@[simp]
theorem compSpan_val_fst {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) :
    (compSpan p q).val.1 = p.val.1 := rfl

@[simp]
theorem compSpan_val_snd {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) :
    (compSpan p q).val.2 = alignPair p q • q.val.2 := rfl

/-- Composition of morphisms, descended from `compSpan`. -/
noncomputable def compMor {X Y Z : QuotCat P G} (f : Mor X Y) (g : Mor Y Z) : Mor X Z :=
  Quotient.liftOn₂' f g (fun p q => Quotient.mk'' (compSpan p q)) <| by
    rintro p₁ q₁ p₂ q₂ ⟨gg, hg1, hg2⟩ ⟨hh, hh1, hh2⟩
    apply Quotient.sound'
    refine ⟨gg, hg1, ?_⟩
    change gg • (alignPair p₁ q₁ • q₁.val.2) = alignPair p₂ q₂ • q₂.val.2
    have hkey : gg * alignPair p₁ q₁ = alignPair p₂ q₂ * hh := by
      apply smul_left_cancel (x := q₁.val.1)
      rw [mul_smul, mul_smul, alignPair_smul, hh1, alignPair_smul, hg2]
    rw [smul_smul, hkey, mul_smul, hh2]

theorem compMor_mk {X Y Z : QuotCat P G} (p : Span X Y) (q : Span Y Z) :
    compMor (Quotient.mk'' p) (Quotient.mk'' q) = Quotient.mk'' (compSpan p q) := rfl

noncomputable instance category : Category (QuotCat P G) where
  Hom := Mor
  id X := Quotient.mk'' (idSpan X)
  comp f g := compMor f g
  id_comp := by
    rintro X Y f
    induction f using Quotient.inductionOn' with
    | h p =>
      apply Quotient.sound'
      refine ⟨(alignPair (idSpan X) p)⁻¹, ?_, ?_⟩
      · change (alignPair (idSpan X) p)⁻¹ • (idSpan X).val.2 = p.val.1
        rw [inv_smul_eq_iff]
        exact (alignPair_smul (idSpan X) p).symm
      · change (alignPair (idSpan X) p)⁻¹ • (alignPair (idSpan X) p • p.val.2) = p.val.2
        exact inv_smul_smul _ _
  comp_id := by
    rintro X Y f
    induction f using Quotient.inductionOn' with
    | h p =>
      apply Quotient.sound'
      refine ⟨1, ?_, ?_⟩
      · simp only [one_smul, compSpan_val_fst]
      · change (1 : G) • (alignPair p (idSpan Y) • (idSpan Y).val.2) = p.val.2
        rw [one_smul]
        exact alignPair_smul p (idSpan Y)
  assoc := by
    rintro W X Y Z f g h
    induction f using Quotient.inductionOn' with
    | h p =>
      induction g using Quotient.inductionOn' with
      | h q =>
        induction h using Quotient.inductionOn' with
        | h r =>
          apply Quotient.sound'
          refine ⟨1, ?_, ?_⟩
          · simp only [one_smul, compSpan_val_fst]
          · rw [one_smul]
            change alignPair (compSpan p q) r • r.val.2
                = alignPair p (compSpan q r) • (alignPair q r • r.val.2)
            have hbr : alignPair p (compSpan q r) = alignPair p q := rfl
            have hkey : alignPair (compSpan p q) r
                = alignPair p (compSpan q r) * alignPair q r := by
              apply smul_left_cancel (x := r.val.1)
              rw [alignPair_smul, mul_smul, alignPair_smul, hbr, compSpan_val_snd]
            rw [hkey, mul_smul]

end QuotCat

/-! ## Fixed-source representatives (workhorse for Steps 4 & 5) -/

namespace QuotCat

variable [OrderFreeAction G P]

/-- The forward map: send a morphism `⟦a⟧ ⟶ Y` to its unique upper endpoint above `a`.
Choosing the representative with first coordinate exactly `a` pins it via the aligner. -/
noncomputable def homToUpSet (a : P) (Y : QuotCat P G) (f : Mor (Quotient.mk'' a) Y) :
    {b : P // a ≤ b ∧ (Quotient.mk'' b : orbitRel.Quotient G P) = Y} :=
  Quotient.liftOn' f
    (fun p =>
      ⟨align a p.val.1 p.property.2.1.symm • p.val.2, by
        refine ⟨?_, ?_⟩
        · have h2 : align a p.val.1 p.property.2.1.symm • p.val.1
              ≤ align a p.val.1 p.property.2.1.symm • p.val.2 :=
            (smul_le_smul_iff _).2 p.property.1
          rw [align_smul] at h2
          exact h2
        · rw [mk_smul_eq]; exact p.property.2.2⟩)
    (by
      rintro p q ⟨g, hg1, hg2⟩
      apply Subtype.ext
      change align a p.val.1 p.property.2.1.symm • p.val.2
          = align a q.val.1 q.property.2.1.symm • q.val.2
      have hkey : align a q.val.1 q.property.2.1.symm * g
          = align a p.val.1 p.property.2.1.symm := by
        apply align_eq a p.val.1 p.property.2.1.symm
        rw [mul_smul, hg1, align_smul]
      rw [← hkey, mul_smul, hg2])

/-- **Fixed-source representatives** (workhorse of Steps 4 & 5):
`(⟦a⟧ ⟶ Y) ≃ {b // a ≤ b ∧ ⟦b⟧ = Y}`.  Every hom out of `⟦a⟧` has a unique
representative whose first coordinate is exactly `a`. -/
noncomputable def homEquivUpSet (a : P) (Y : QuotCat P G) :
    (Quotient.mk'' a ⟶ Y) ≃
      {b : P // a ≤ b ∧ (Quotient.mk'' b : orbitRel.Quotient G P) = Y} where
  toFun := homToUpSet a Y
  invFun b := Quotient.mk'' ⟨(a, b.val), b.property.1, rfl, b.property.2⟩
  left_inv := by
    intro f
    induction f using Quotient.inductionOn' with
    | h p =>
      apply Quotient.sound'
      refine ⟨(align a p.val.1 p.property.2.1.symm)⁻¹, ?_, ?_⟩
      · change (align a p.val.1 p.property.2.1.symm)⁻¹ • a = p.val.1
        rw [inv_smul_eq_iff]
        exact (align_smul a p.val.1 p.property.2.1.symm).symm
      · change (align a p.val.1 p.property.2.1.symm)⁻¹
            • (align a p.val.1 p.property.2.1.symm • p.val.2) = p.val.2
        exact inv_smul_smul _ _
  right_inv := by
    intro b
    apply Subtype.ext
    change align a a rfl • b.val = b.val
    rw [align_self, one_smul]

end QuotCat

end OrderQuotient
