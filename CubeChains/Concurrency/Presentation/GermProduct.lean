import CubeChains.Concurrency.Presentation.GermWeakOrder
import CubeChains.Foundations.Polygraph.Presheaf

/-!
# Concurrency/Presentation/GermProduct — the germ of a product of charts

Two germ charts juxtapose: `GermChart.prod` names the block sums, and a germ step of a block sum is
a germ step in each block (`germStep_permSum_iff`), so `germPoly p (C₁.prod C₂)` reads the two
charts at once.

Whether that is the *categorical* product of the two germs — cellwise, since polygraphs are a
presheaf topos — depends on the presentation, and the dividing line is padding.  A 1-cell of a
product is a **pair** of 1-cells, so both blocks must advance at every letter.  The Garside germ
can: its generators are all the simples, the identity among them, which is what `PosGermRel.one`
is for.  Artin's cannot, and at `a = b = 2` the block sum already carries two 1-cells where the
product carries at most one.
-/

open CategoryTheory Opposite CubeChains Polygraph Limits

namespace ChainCat

namespace GermChart

variable {a b : ℕ}

/-- **The product of two germ charts**: the block sums of their points.  Down-closed because a
length-additive factorisation of a block sum is block-diagonal (`exists_permSum_of_permLen_add`)
and splits blockwise. -/
def prod (C₁ : GermChart a) (C₂ : GermChart b) : GermChart (a + b) where
  carrier := C₁.carrier × C₂.carrier
  perm x := permSum a b (C₁.perm x.1, C₂.perm x.2)
  perm_injective x y h := by
    have h' := permSum_injective h
    exact Prod.ext (C₁.perm_injective (congrArg Prod.fst h'))
      (C₂.perm_injective (congrArg Prod.snd h'))
  mem_of_le := by
    intro x τ h
    have hle : permLen τ + permLen (τ⁻¹ * permSum a b (C₁.perm x.1, C₂.perm x.2))
        = permLen (permSum a b (C₁.perm x.1, C₂.perm x.2)) := WeakOrder.le_def.mp h
    obtain ⟨⟨q₁, q₂⟩, rfl⟩ := exists_permSum_of_permLen_add (C₁.perm x.1, C₂.perm x.2) hle
    have hprod : ((q₁, q₂) * (q₁⁻¹ * C₁.perm x.1, q₂⁻¹ * C₂.perm x.2)
        : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) = (C₁.perm x.1, C₂.perm x.2) := by
      rw [Prod.mk_mul_mk, mul_inv_cancel_left, mul_inv_cancel_left]
    have hinv : ((q₁, q₂) : Equiv.Perm (Fin a) × Equiv.Perm (Fin b))⁻¹
        * (C₁.perm x.1, C₂.perm x.2) = (q₁⁻¹ * C₁.perm x.1, q₂⁻¹ * C₂.perm x.2) := rfl
    have hsplit : permLen (permSum a b ((q₁, q₂) * (q₁⁻¹ * C₁.perm x.1, q₂⁻¹ * C₂.perm x.2)))
        = permLen (permSum a b (q₁, q₂))
          + permLen (permSum a b (q₁⁻¹ * C₁.perm x.1, q₂⁻¹ * C₂.perm x.2)) := by
      rw [hprod, ← hinv, map_mul, map_inv]
      omega
    obtain ⟨h₁, h₂⟩ := (permLen_permSum_mul_iff q₁ _ q₂ _).mp hsplit
    rw [mul_inv_cancel_left] at h₁ h₂
    obtain ⟨y₁, hy₁⟩ := C₁.mem_of_le (x := x.1) (τ := q₁)
      (WeakOrder.le_def.mpr (by simp only [WeakOrder.perm_of]; omega))
    obtain ⟨y₂, hy₂⟩ := C₂.mem_of_le (x := x.2) (τ := q₂)
      (WeakOrder.le_def.mpr (by simp only [WeakOrder.perm_of]; omega))
    exact ⟨(y₁, y₂), by rw [show C₁.perm (y₁, y₂).1 = q₁ from hy₁,
      show C₂.perm (y₁, y₂).2 = q₂ from hy₂]⟩

@[simp] theorem prod_perm (C₁ : GermChart a) (C₂ : GermChart b) (x : (C₁.prod C₂).carrier) :
    (C₁.prod C₂).perm x = permSum a b (C₁.perm x.1, C₂.perm x.2) := rfl

end GermChart

/-! ## The refutation: Artin's germ is not closed under products

A cellwise product advances **both** blocks at every letter, and Artin's presentation has no idle
generator to pad with.  Already at `a = b = 2` the block-sum chart has a 1-cell moving the first
block alone, while every 1-cell of the product moves both. -/

namespace ArtinGermProduct

/-- The two-strand chart, and the four-strand chart of its block sums. -/
abbrev C2 : GermChart 2 := GermChart.top 2

/-- The block-sum chart on `2 + 2` strands. -/
abbrev C22 : GermChart (2 + 2) := C2.prod C2

/-- The one Artin generator on two strands. -/
def gen2 : artinBP.S 2 := ⟨0, by omega⟩

/-- …and the simple it crosses. -/
def swap2 : Equiv.Perm (Fin 2) := adjT gen2

theorem permLen_swap2 : permLen swap2 = 1 := permLen_adjT gen2

theorem swap2_ne_one : swap2 ≠ 1 := fun h => by
  have := permLen_swap2
  rw [h, permLen_one] at this
  exact absurd this (by omega)

/-- **Two strands admit at most one crossing** — there is one pair to cross. -/
theorem permLen_le_one (y : Equiv.Perm (Fin 2)) : permLen y ≤ 1 := by
  classical
  have hsub : inversions y ⊆ {((0 : Fin 2), (1 : Fin 2))} := by
    rintro ⟨p, q⟩ hp
    rw [mem_inversions] at hp
    have h1 : (p : ℕ) < (q : ℕ) := hp.1
    have h2 : (q : ℕ) < 2 := q.2
    refine Finset.mem_singleton.mpr (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      simp only [Fin.val_zero, Fin.val_one] <;> omega
  simpa [permLen] using Finset.card_le_card hsub

/-- **The Artin germ on two strands has exactly one 1-cell** — the generator crosses the one pair,
so its source can only be the identity. -/
instance subsingleton_edge_two :
    Subsingleton (Quiver.Total (GenObj (artinBP.germPoly C2).Gen)) := by
  haveI : Subsingleton (artinBP.S 2) := inferInstanceAs (Subsingleton (Fin 1))
  refine ⟨?_⟩
  rintro ⟨⟨x⟩, ⟨y⟩, ⟨k, hk⟩⟩ ⟨⟨x'⟩, ⟨y'⟩, ⟨k', hk'⟩⟩
  obtain ⟨hy, hlen⟩ := (artinBP_germStep_iff k x y).mp hk
  obtain ⟨hy', hlen'⟩ := (artinBP_germStep_iff k' x' y').mp hk'
  have hx := eq_one_of_permLen_eq_zero x (by have := permLen_le_one y; omega)
  have hx' := eq_one_of_permLen_eq_zero x' (by have := permLen_le_one y'; omega)
  obtain rfl : k' = k := Subsingleton.elim _ _
  subst hx; subst hx'; subst hy; subst hy'
  rfl

/-- The identity point of the block-sum chart. -/
def pt11 : C22.carrier := ((1 : Equiv.Perm (Fin 2)), (1 : Equiv.Perm (Fin 2)))

/-- …the point with the first block swapped. -/
def ptS1 : C22.carrier := (swap2, (1 : Equiv.Perm (Fin 2)))

/-- …and the point with the second block swapped. -/
def pt1S : C22.carrier := ((1 : Equiv.Perm (Fin 2)), swap2)

theorem germStep_left : artinBP.GermStep (⟨0, by omega⟩ : artinBP.S (2 + 2))
    (permSum 2 2 (1, 1)) (permSum 2 2 (swap2, 1)) := by
  refine (artinBP_germStep_iff _ _ _).mpr ⟨?_, ?_⟩
  · rw [permSum_one_one, one_mul,
      show ((swap2, (1 : Equiv.Perm (Fin 2)))) = (adjT gen2, 1) from rfl]
    exact permSum_adjT_left gen2 ⟨0, by omega⟩ rfl
  · rw [permSum_one_one, permLen_one, permLen_permSum, permLen_one, permLen_swap2]

theorem germStep_right : artinBP.GermStep (⟨2, by omega⟩ : artinBP.S (2 + 2))
    (permSum 2 2 (1, 1)) (permSum 2 2 (1, swap2)) := by
  refine (artinBP_germStep_iff _ _ _).mpr ⟨?_, ?_⟩
  · rw [permSum_one_one, one_mul,
      show (((1 : Equiv.Perm (Fin 2)), swap2)) = (1, adjT gen2) from rfl]
    exact permSum_adjT_right gen2 ⟨2, by omega⟩ rfl
  · rw [permSum_one_one, permLen_one, permLen_permSum, permLen_one, permLen_swap2]

/-- A 1-cell of the block-sum chart moving **only the first block**. -/
def edgeLeft : Quiver.Total (GenObj (artinBP.germPoly C22).Gen) :=
  ⟨⟨pt11⟩, ⟨ptS1⟩, ⟨⟨0, by omega⟩, germStep_left⟩⟩

/-- …and one moving only the second. -/
def edgeRight : Quiver.Total (GenObj (artinBP.germPoly C22).Gen) :=
  ⟨⟨pt11⟩, ⟨pt1S⟩, ⟨⟨2, by omega⟩, germStep_right⟩⟩

theorem edgeLeft_ne_edgeRight : edgeLeft ≠ edgeRight := by
  intro h
  have h' := congrArg (fun t : Quiver.Total (GenObj (artinBP.germPoly C22).Gen) =>
    (t.right.as : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)).1) h
  exact swap2_ne_one h'

/-- **The germ of a block sum is not the product of the germs, for Artin's presentation.**
`a = b = 2`: the block-sum chart carries a 1-cell moving the first block alone, and a product
carries none — every letter of a product moves both blocks at once. -/
theorem isEmpty_iso_prod_artin :
    IsEmpty (artinBP.germPoly C22 ≅ artinBP.germPoly C2 ⨯ artinBP.germPoly C2) := by
  refine ⟨fun i => ?_⟩
  haveI : Subsingleton (Quiver.Total (GenObj (artinBP.germPoly C2 ⨯ artinBP.germPoly C2).Gen)) :=
    (prodEdgeEquiv _ _).subsingleton
  haveI : Subsingleton (Quiver.Total (GenObj (artinBP.germPoly C22).Gen)) :=
    (edgeEquivOfIso i).subsingleton
  exact edgeLeft_ne_edgeRight (Subsingleton.elim _ _)

end ArtinGermProduct

/-! ## The Garside germ: the block-sum chart *is* the product

`germBP`'s generators are all the simples — the identity among them — so a pair of blocks is one
letter, and the lockstep a product forces costs nothing.  That idle generator is `PosGermRel.one`;
a presentation without one has no chance, which is the whole of `isEmpty_iso_prod_artin`. -/

namespace GarsideGerm

variable {n a b : ℕ}

/-! ### Reading a germ cell -/

/-- The simple a germ 1-cell names. -/
def germLetter {C : GermChart n} {x y : GenObj (germBP.GermGen C)} (e : x ⟶ y) :
    Equiv.Perm (Fin n) := e.1

theorem germStep_germLetter {C : GermChart n} {x y : GenObj (germBP.GermGen C)} (e : x ⟶ y) :
    CubeChains.GermStep (posPerm (germLetter e)) (C.perm x.as) (C.perm y.as) := e.2

theorem perm_eq_mul_germLetter {C : GermChart n} {x y : GenObj (germBP.GermGen C)} (e : x ⟶ y) :
    C.perm y.as = C.perm x.as * germLetter e := e.2.mul_eq

/-- **A germ 1-cell is pinned by its endpoints** — the simple it names is the gap between them. -/
theorem germGen_eq {C : GermChart n} {x y : GenObj (germBP.GermGen C)} (e e' : x ⟶ y) : e = e' :=
  Subtype.ext (mul_left_cancel (a := C.perm x.as)
    ((perm_eq_mul_germLetter e).symm.trans (perm_eq_mul_germLetter e')))

/-- The word of simples a path of `germBP`'s one-object polygraph spells. -/
noncomputable def simpleWord {x y : GenObj (germBP.P n).Gen} (w : Quiver.Path x y) :
    FreeMonoid (Equiv.Perm (Fin n)) := MonoidPoly.word (rels := PosGermRel n) w

/-- …read on a germ path. -/
noncomputable abbrev germSimples (C : GermChart n) {x y : GenObj (germBP.GermGen C)}
    (w : Quiver.Path x y) :
    FreeMonoid (Equiv.Perm (Fin n)) := simpleWord ((germBP.germProj C).mapPath w)

@[simp] theorem germSimples_nil (C : GermChart n) (x : GenObj (germBP.GermGen C)) :
    germSimples C (Quiver.Path.nil (a := x)) = 1 := rfl

@[simp] theorem germSimples_cons (C : GermChart n) {x y z : GenObj (germBP.GermGen C)}
    (w : Quiver.Path x y) (e : y ⟶ z) :
    germSimples C (w.cons e) = germSimples C w * FreeMonoid.of (germLetter e) := rfl

/-- **A 2-cell of the germ is a germ relation between the words its boundary spells.** -/
theorem posGermRel_of_rel {C : GermChart n} {x y : GenObj (germBP.GermGen C)}
    (α : (germBP.germPoly C).Rel x y) :
    PosGermRel n (germSimples C ((germBP.germPoly C).src α))
      (germSimples C ((germBP.germPoly C).tgt α)) := by
  rw [show germSimples C ((germBP.germPoly C).src α) = simpleWord ((germBP.P n).src α.cell) from
      congrArg simpleWord α.src_eq,
    show germSimples C ((germBP.germPoly C).tgt α) = simpleWord ((germBP.P n).tgt α.cell) from
      congrArg simpleWord α.tgt_eq]
  exact α.cell.2

/-- …and every such relation is a 2-cell. -/
noncomputable def relOfPosGermRel {C : GermChart n} {x y : GenObj (germBP.GermGen C)}
    (u v : Quiver.Path x y) (h : PosGermRel n (germSimples C u) (germSimples C v)) :
    (germBP.germPoly C).Rel x y := ⟨u, v, ⟨(_, _), h⟩, rfl, rfl⟩

/-! ### Free-monoid surgery

`PosGermRel` has two constructors, of shapes `(2, 1)` and `(1, 0)`; a word's length is what picks
between them, and blockwise reading preserves it. -/

private theorem posGermRel_cases {W W' : FreeMonoid (Equiv.Perm (Fin n))} (h : PosGermRel n W W') :
    (∃ σ τ, W = FreeMonoid.of σ * FreeMonoid.of τ ∧ W' = FreeMonoid.of (σ * τ) ∧
        permLen (σ * τ) = permLen σ + permLen τ)
      ∨ (W = FreeMonoid.of 1 ∧ W' = 1) := by
  cases h with
  | germ σ τ hl => exact Or.inl ⟨σ, τ, rfl, rfl, hl⟩
  | one => exact Or.inr ⟨rfl, rfl⟩

private theorem length_map {α β : Type} (f : α → β) (Z : FreeMonoid α) :
    (FreeMonoid.map f Z).length = Z.length := List.length_map _

private theorem of_mul_of_inj {α : Type} {x y u v : α}
    (h : FreeMonoid.of x * FreeMonoid.of y = FreeMonoid.of u * FreeMonoid.of v) :
    x = u ∧ y = v := by
  have h' := congrArg FreeMonoid.toList h
  simpa using h'

private theorem exists_two_of_map {α β : Type} (f : α → β) {Z : FreeMonoid α} {u v : β}
    (h : FreeMonoid.map f Z = FreeMonoid.of u * FreeMonoid.of v) :
    ∃ p q, Z = FreeMonoid.of p * FreeMonoid.of q ∧ f p = u ∧ f q = v := by
  have hlen : Z.length = 2 := by
    rw [← length_map f Z, h, FreeMonoid.length_mul, FreeMonoid.length_of, FreeMonoid.length_of]
  obtain ⟨p, q, rfl⟩ := FreeMonoid.length_eq_two.mp hlen
  rw [map_mul, FreeMonoid.map_of, FreeMonoid.map_of] at h
  exact ⟨p, q, rfl, (of_mul_of_inj h).1, (of_mul_of_inj h).2⟩

private theorem exists_one_of_map {α β : Type} (f : α → β) {Z : FreeMonoid α} {u : β}
    (h : FreeMonoid.map f Z = FreeMonoid.of u) : ∃ p, Z = FreeMonoid.of p ∧ f p = u := by
  have hlen : Z.length = 1 := by
    rw [← length_map f Z, h, FreeMonoid.length_of]
  obtain ⟨p, rfl⟩ := FreeMonoid.length_eq_one.mp hlen
  rw [FreeMonoid.map_of] at h
  exact ⟨p, rfl, FreeMonoid.of_injective h⟩

private theorem eq_one_of_map {α β : Type} (f : α → β) {Z : FreeMonoid α}
    (h : FreeMonoid.map f Z = 1) : Z = 1 :=
  FreeMonoid.length_eq_zero.mp (by rw [← length_map f Z, h, FreeMonoid.length_one])

/-- **A germ relation of block sums is a germ relation in each block, and conversely.**  The two
constructors are pinned by the word lengths, which the three readings share, so no case can pair
with the other; the germ relation itself then splits by `permLen_permSum_mul_iff`. -/
theorem posGermRel_permSum_iff
    {Z Z' : FreeMonoid (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))} :
    PosGermRel (a + b) (FreeMonoid.map (permSum a b) Z) (FreeMonoid.map (permSum a b) Z')
      ↔ PosGermRel a (FreeMonoid.map Prod.fst Z) (FreeMonoid.map Prod.fst Z') ∧
        PosGermRel b (FreeMonoid.map Prod.snd Z) (FreeMonoid.map Prod.snd Z') := by
  constructor
  · intro h
    rcases posGermRel_cases h with ⟨ρ, π, hs, ht, hl⟩ | ⟨hs, ht⟩
    · obtain ⟨p, q, rfl, hp, hq⟩ := exists_two_of_map _ hs
      obtain ⟨r, rfl, hr⟩ := exists_one_of_map _ ht
      have hrpq : r = p * q := permSum_injective (by rw [hr, ← hp, ← hq, map_mul])
      subst hrpq
      obtain ⟨h₁, h₂⟩ := (permLen_permSum_mul_iff' p q).mp (by rw [hr, hp, hq]; exact hl)
      refine ⟨?_, ?_⟩
      · simpa only [map_mul, FreeMonoid.map_of] using PosGermRel.germ p.1 q.1 h₁
      · simpa only [map_mul, FreeMonoid.map_of] using PosGermRel.germ p.2 q.2 h₂
    · obtain ⟨p, rfl, hp⟩ := exists_one_of_map _ hs
      obtain rfl : Z' = 1 := eq_one_of_map _ ht
      obtain rfl : p = 1 := permSum_injective (by rw [hp, map_one])
      exact ⟨PosGermRel.one, PosGermRel.one⟩
  · rintro ⟨h₁, h₂⟩
    rcases posGermRel_cases h₁ with ⟨σ, τ, hs, ht, hl⟩ | ⟨hs, ht⟩
    · obtain ⟨p, q, rfl, hp, hq⟩ := exists_two_of_map _ hs
      obtain ⟨r, rfl, hr⟩ := exists_one_of_map _ ht
      simp only [map_mul, FreeMonoid.map_of] at h₂ ⊢
      rcases posGermRel_cases h₂ with ⟨σ', τ', hs', ht', hl'⟩ | ⟨hs', ht'⟩
      · obtain ⟨e₁, e₂⟩ := of_mul_of_inj hs'
        have e₃ : r.2 = σ' * τ' := FreeMonoid.of_injective ht'
        obtain rfl : r = p * q := Prod.ext (by rw [hr, ← hp, ← hq]; rfl)
          (by rw [e₃, ← e₁, ← e₂]; rfl)
        have hadd : permLen (permSum a b (p * q))
            = permLen (permSum a b p) + permLen (permSum a b q) :=
          (permLen_permSum_mul_iff' p q).mpr
            ⟨by rw [hp, hq]; exact hl, by rw [e₁, e₂]; exact hl'⟩
        rw [map_mul]
        exact PosGermRel.germ _ _ (by rw [← map_mul]; exact hadd)
      · exact absurd (congrArg FreeMonoid.length hs') (by simp)
    · obtain ⟨p, rfl, hp⟩ := exists_one_of_map _ hs
      obtain rfl : Z' = 1 := eq_one_of_map _ ht
      simp only [FreeMonoid.map_of, map_one] at h₂ ⊢
      rcases posGermRel_cases h₂ with ⟨σ', τ', hs', -, -⟩ | ⟨hs', -⟩
      · exact absurd (congrArg FreeMonoid.length hs') (by simp)
      · obtain rfl : p = 1 := Prod.ext hp (FreeMonoid.of_injective hs')
        rw [map_one]
        exact PosGermRel.one

/-! ### The block projections -/

variable {C₁ : GermChart a} {C₂ : GermChart b}

/-- **A 1-cell of a block-sum chart is the block sum of the two gaps it spans.** -/
theorem germLetter_prod {x y : GenObj (germBP.GermGen (C₁.prod C₂))} (e : x ⟶ y) :
    germLetter e = permSum a b ((C₁.perm x.as.1)⁻¹ * C₁.perm y.as.1,
      (C₂.perm x.as.2)⁻¹ * C₂.perm y.as.2) := by
  have h : (C₁.prod C₂).perm x.as * germLetter e = (C₁.prod C₂).perm y.as :=
    (perm_eq_mul_germLetter e).symm
  have h2 : germLetter e
      = ((C₁.prod C₂).perm x.as)⁻¹ * (C₁.prod C₂).perm y.as := by
    rw [← h, inv_mul_cancel_left]
  rw [h2]
  change (permSum a b (C₁.perm x.as.1, C₂.perm x.as.2))⁻¹
      * permSum a b (C₁.perm y.as.1, C₂.perm y.as.2) = _
  rw [← map_inv, ← map_mul]
  rfl

/-- …and each gap is itself a germ step. -/
theorem germStep_prod_split {x y : GenObj (germBP.GermGen (C₁.prod C₂))} (e : x ⟶ y) :
    CubeChains.GermStep (posPerm ((C₁.perm x.as.1)⁻¹ * C₁.perm y.as.1))
        (C₁.perm x.as.1) (C₁.perm y.as.1) ∧
      CubeChains.GermStep (posPerm ((C₂.perm x.as.2)⁻¹ * C₂.perm y.as.2))
        (C₂.perm x.as.2) (C₂.perm y.as.2) := by
  have h := germStep_germLetter e
  rw [germLetter_prod e] at h
  exact (germStep_permSum_iff _ _ _ _ _ _).mp h

/-- The first block of a block-sum germ. -/
def germFstPre (C₁ : GermChart a) (C₂ : GermChart b) :
    GenObj (germBP.GermGen (C₁.prod C₂)) ⥤q GenObj (germBP.GermGen C₁) where
  obj x := ⟨x.as.1⟩
  map {_ _} e := ⟨_, (germStep_prod_split e).1⟩

/-- …and the second. -/
def germSndPre (C₁ : GermChart a) (C₂ : GermChart b) :
    GenObj (germBP.GermGen (C₁.prod C₂)) ⥤q GenObj (germBP.GermGen C₂) where
  obj x := ⟨x.as.2⟩
  map {_ _} e := ⟨_, (germStep_prod_split e).2⟩

theorem germLetter_eq_permSum {x y : GenObj (germBP.GermGen (C₁.prod C₂))} (e : x ⟶ y) :
    germLetter e = permSum a b (germLetter ((germFstPre C₁ C₂).map e),
      germLetter ((germSndPre C₁ C₂).map e)) := germLetter_prod e

/-! ### The word of pairs

A path read through two germ readings spells a word of *pairs*; its two projections are the two
germ words, and its block sums are the block-sum germ word. -/

/-- The word of pairs a path spells through two germ readings. -/
noncomputable def pairWord {V : Type} {Gen : V → V → Type}
    (F₁ : GenObj Gen ⥤q GenObj (germBP.GermGen C₁))
    (F₂ : GenObj Gen ⥤q GenObj (germBP.GermGen C₂)) {x : GenObj Gen} :
    {y : GenObj Gen} → Quiver.Path x y → FreeMonoid (Equiv.Perm (Fin a) × Equiv.Perm (Fin b))
  | _, Quiver.Path.nil => 1
  | _, Quiver.Path.cons w e =>
      pairWord F₁ F₂ w * FreeMonoid.of (germLetter (F₁.map e), germLetter (F₂.map e))

section PairWord

variable {V : Type} {Gen : V → V → Type}
  (F₁ : GenObj Gen ⥤q GenObj (germBP.GermGen C₁)) (F₂ : GenObj Gen ⥤q GenObj (germBP.GermGen C₂))

@[simp] theorem pairWord_nil (x : GenObj Gen) :
    pairWord F₁ F₂ (Quiver.Path.nil (a := x)) = 1 := rfl

@[simp] theorem pairWord_cons {x y z : GenObj Gen} (w : Quiver.Path x y) (e : y ⟶ z) :
    pairWord F₁ F₂ (w.cons e)
      = pairWord F₁ F₂ w * FreeMonoid.of (germLetter (F₁.map e), germLetter (F₂.map e)) := rfl

theorem map_fst_pairWord {x y : GenObj Gen} (w : Quiver.Path x y) :
    FreeMonoid.map Prod.fst (pairWord F₁ F₂ w) = germSimples C₁ (F₁.mapPath w) := by
  induction w with
  | nil => rfl
  | cons w e ih => rw [pairWord_cons, map_mul, ih]; rfl

theorem map_snd_pairWord {x y : GenObj Gen} (w : Quiver.Path x y) :
    FreeMonoid.map Prod.snd (pairWord F₁ F₂ w) = germSimples C₂ (F₂.mapPath w) := by
  induction w with
  | nil => rfl
  | cons w e ih => rw [pairWord_cons, map_mul, ih]; rfl

/-- **A reading whose letters are the block sums spells the block-sum word.** -/
theorem map_permSum_pairWord (F : GenObj Gen ⥤q GenObj (germBP.GermGen (C₁.prod C₂)))
    (hF : ∀ {x y : GenObj Gen} (e : x ⟶ y),
      germLetter (F.map e) = permSum a b (germLetter (F₁.map e), germLetter (F₂.map e)))
    {x y : GenObj Gen} (w : Quiver.Path x y) :
    FreeMonoid.map (permSum a b) (pairWord F₁ F₂ w) = germSimples (C₁.prod C₂) (F.mapPath w) := by
  induction w with
  | nil => rfl
  | cons w e ih =>
      rw [pairWord_cons, map_mul, ih]
      exact congrArg _ (congrArg FreeMonoid.of (hF e).symm)

end PairWord

/-! ### The two germs are the factors -/

theorem boundaryDetermined_germPoly (C : GermChart n) :
    (germBP.germPoly C).BoundaryDetermined :=
  Polygraph.boundaryDetermined_comap (fun _ _ hs ht => Subtype.ext (Prod.ext hs ht)) _ _

/-- **A map into a germ is pinned by its 0-cells** — the 1-cells are, and the 2-cells are their
boundary. -/
theorem germPoly_hom_ext {R : Polygraph.{0, 0, 0}} {C : GermChart n}
    {F G : R ⟶ germBP.germPoly C} (h : ∀ x, F.pre.obj x = G.pre.obj x) : F = G :=
  Polygraph.hom_ext_of_boundaryDetermined (boundaryDetermined_germPoly C)
    (Prefunctor.ext' h fun _ _ _ => germGen_eq _ _)

/-- **A germ relation of a block-sum path is one of its first-block reading.** -/
theorem posGermRel_fst_mapPath {x y : GenObj (germBP.GermGen (C₁.prod C₂))}
    {u v : Quiver.Path x y}
    (h : PosGermRel (a + b) (germSimples (C₁.prod C₂) u) (germSimples (C₁.prod C₂) v)) :
    PosGermRel a (germSimples C₁ ((germFstPre C₁ C₂).mapPath u))
      (germSimples C₁ ((germFstPre C₁ C₂).mapPath v)) := by
  rw [← map_fst_pairWord (germFstPre C₁ C₂) (germSndPre C₁ C₂),
    ← map_fst_pairWord (germFstPre C₁ C₂) (germSndPre C₁ C₂)]
  refine (posGermRel_permSum_iff.mp ?_).1
  rw [map_permSum_pairWord _ _ (Prefunctor.id _) (fun e => germLetter_eq_permSum e),
    map_permSum_pairWord _ _ (Prefunctor.id _) (fun e => germLetter_eq_permSum e),
    Prefunctor.mapPath_id, Prefunctor.mapPath_id]
  exact h

/-- …and of its second-block reading. -/
theorem posGermRel_snd_mapPath {x y : GenObj (germBP.GermGen (C₁.prod C₂))}
    {u v : Quiver.Path x y}
    (h : PosGermRel (a + b) (germSimples (C₁.prod C₂) u) (germSimples (C₁.prod C₂) v)) :
    PosGermRel b (germSimples C₂ ((germSndPre C₁ C₂).mapPath u))
      (germSimples C₂ ((germSndPre C₁ C₂).mapPath v)) := by
  rw [← map_snd_pairWord (germFstPre C₁ C₂) (germSndPre C₁ C₂),
    ← map_snd_pairWord (germFstPre C₁ C₂) (germSndPre C₁ C₂)]
  refine (posGermRel_permSum_iff.mp ?_).2
  rw [map_permSum_pairWord _ _ (Prefunctor.id _) (fun e => germLetter_eq_permSum e),
    map_permSum_pairWord _ _ (Prefunctor.id _) (fun e => germLetter_eq_permSum e),
    Prefunctor.mapPath_id, Prefunctor.mapPath_id]
  exact h

/-- The first block, as a map of germs. -/
noncomputable def germFst (C₁ : GermChart a) (C₂ : GermChart b) :
    germBP.germPoly (C₁.prod C₂) ⟶ germBP.germPoly C₁ where
  pre := germFstPre C₁ C₂
  two α := relOfPosGermRel _ _ (posGermRel_fst_mapPath (posGermRel_of_rel α))
  src_two _ := rfl
  tgt_two _ := rfl

/-- …and the second. -/
noncomputable def germSnd (C₁ : GermChart a) (C₂ : GermChart b) :
    germBP.germPoly (C₁.prod C₂) ⟶ germBP.germPoly C₂ where
  pre := germSndPre C₁ C₂
  two α := relOfPosGermRel _ _ (posGermRel_snd_mapPath (posGermRel_of_rel α))
  src_two _ := rfl
  tgt_two _ := rfl

/-! ### The lift -/

variable {R : Polygraph.{0, 0, 0}}

/-- A pair of germ readings, juxtaposed. -/
noncomputable def liftPre (f : R ⟶ germBP.germPoly C₁) (g : R ⟶ germBP.germPoly C₂) :
    GenObj R.Gen ⥤q GenObj (germBP.GermGen (C₁.prod C₂)) where
  obj x := ⟨((f.pre.obj x).as, (g.pre.obj x).as)⟩
  map {_ _} e := ⟨permSum a b (germLetter (f.pre.map e), germLetter (g.pre.map e)),
    (germStep_permSum_iff _ _ _ _ _ _).mpr ⟨germStep_germLetter _, germStep_germLetter _⟩⟩

theorem germLetter_liftPre (f : R ⟶ germBP.germPoly C₁) (g : R ⟶ germBP.germPoly C₂)
    {x y : GenObj R.Gen} (e : x ⟶ y) :
    germLetter ((liftPre f g).map e)
      = permSum a b (germLetter (f.pre.map e), germLetter (g.pre.map e)) := rfl

/-- **A germ relation in each block is one of the block sum.** -/
theorem posGermRel_liftPre (f : R ⟶ germBP.germPoly C₁) (g : R ⟶ germBP.germPoly C₂)
    {x y : GenObj R.Gen} {u v : Quiver.Path x y}
    (h₁ : PosGermRel a (germSimples C₁ (f.pre.mapPath u)) (germSimples C₁ (f.pre.mapPath v)))
    (h₂ : PosGermRel b (germSimples C₂ (g.pre.mapPath u)) (germSimples C₂ (g.pre.mapPath v))) :
    PosGermRel (a + b) (germSimples (C₁.prod C₂) ((liftPre f g).mapPath u))
      (germSimples (C₁.prod C₂) ((liftPre f g).mapPath v)) := by
  rw [← map_permSum_pairWord f.pre g.pre (liftPre f g) (germLetter_liftPre f g),
    ← map_permSum_pairWord f.pre g.pre (liftPre f g) (germLetter_liftPre f g)]
  refine posGermRel_permSum_iff.mpr ⟨?_, ?_⟩
  · rw [map_fst_pairWord, map_fst_pairWord]; exact h₁
  · rw [map_snd_pairWord, map_snd_pairWord]; exact h₂

/-- **A pair of germ readings is one reading of the block-sum germ.** -/
noncomputable def liftHom (f : R ⟶ germBP.germPoly C₁) (g : R ⟶ germBP.germPoly C₂) :
    R ⟶ germBP.germPoly (C₁.prod C₂) where
  pre := liftPre f g
  two α := relOfPosGermRel _ _ (posGermRel_liftPre f g
    (by rw [← f.src_two α, ← f.tgt_two α]; exact posGermRel_of_rel (f.two α))
    (by rw [← g.src_two α, ← g.tgt_two α]; exact posGermRel_of_rel (g.two α)))
  src_two _ := rfl
  tgt_two _ := rfl

/-- **The two block projections exhibit the block-sum germ as the product of the germs.**  This is
the Garside germ's own doing: a pair of simples is a simple, and the identity is a generator, so
the lockstep a cellwise product forces is free. -/
noncomputable def isLimitGermProd (C₁ : GermChart a) (C₂ : GermChart b) :
    IsLimit (BinaryFan.mk (germFst C₁ C₂) (germSnd C₁ C₂)) :=
  BinaryFan.isLimitMk (fun s => liftHom s.fst s.snd) (fun _ => germPoly_hom_ext fun _ => rfl)
    (fun _ => germPoly_hom_ext fun _ => rfl)
    fun s _m h₁ h₂ => germPoly_hom_ext fun x => GenObj.ext (Prod.ext
      (congrArg (fun H : s.pt ⟶ germBP.germPoly C₁ => (H.pre.obj x).as) h₁)
      (congrArg (fun H : s.pt ⟶ germBP.germPoly C₂ => (H.pre.obj x).as) h₂))

/-- **…so the germ of a product of charts is the categorical product of the germs.** -/
noncomputable def germProdIso (C₁ : GermChart a) (C₂ : GermChart b) :
    germBP.germPoly (C₁.prod C₂) ≅ germBP.germPoly C₁ ⨯ germBP.germPoly C₂ :=
  (isLimitGermProd C₁ C₂).conePointUniqueUpToIso (limit.isLimit (pair _ _))

end GarsideGerm

end ChainCat
