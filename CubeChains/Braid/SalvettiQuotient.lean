import CubeChains.Braid.SalvettiConstruction
import CubeChains.Braid.SalQuotZ

/-!
# Braid/SalvettiQuotient — the Salvetti braid grading descended to the `Sₙ`-quotient

`crossPerm` is invariant under the diagonal reorientation action (`crossPerm_reindex`): a global
relabeling by `σ` multiplies every tope order on the right by `σ⁻¹`, which cancels in the order
*change* of an edge.  So `salvettiGrading` factors through the quotient poset, giving

    salvettiGradingQuot n : QuotCat (Sal (braidCOM n)) Sₙ ⥤ SingleObj (Braid n)

and its free-groupoid lift `salvettiConstructionQuot n`.  This is the **middle vertical map** of the
braid five-lemma ladder; the **left square** is the strict functor equality

    quotCover n ⋙ salvettiConstructionQuot n = salvettiConstruction n.
-/

open CategoryTheory OrderQuotient

namespace CubeChains

variable {n : ℕ}

/-! ## `crossPerm` is `Sₙ`-invariant on the diagonal reorientation action -/

/-- The tope of a reoriented cell is the reorientation of its tope (definitional). -/
theorem smul_tope (τ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    (τ • a : Sal (braidCOM n)).tope = reorient τ a.tope := rfl

/-- Precomposing a `< c` predicate by a permutation does not change the cardinality of its fibre. -/
theorem card_filter_perm (τ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) (c : ℤ) :
    (Finset.univ.filter (fun j => x (τ j) < c)).card
      = (Finset.univ.filter (fun j => x j < c)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv τ (fun _ => Iff.rfl))

/-- **Reindexing the rank.**  Reorienting by `τ` sends the rank of `i` to the rank of `τ⁻¹ i`. -/
theorem topeRank_reindex (τ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) (i : Fin n) :
    topeRank ((τ • a : Sal (braidCOM n)).tope) i = topeRank a.tope (τ⁻¹ i) := by
  obtain ⟨x, -, hT⟩ := (braidCOM_isTope_iff_injective a.tope).mp a.2.2.1
  have hT' : (τ • a : Sal (braidCOM n)).tope = braidSign (fun i => x (τ⁻¹ i)) := by
    rw [smul_tope, hT, reorient_braidSign]
  apply Fin.ext
  rw [topeRank_eq_card hT' i, topeRank_eq_card hT (τ⁻¹ i)]
  exact card_filter_perm τ⁻¹ x (x (τ⁻¹ i))

/-- **Reindexing the tope permutation.**  `topePerm (τ • a) = topePerm a * τ⁻¹`. -/
theorem topePerm_reindex (τ : Equiv.Perm (Fin n)) (a : Sal (braidCOM n)) :
    topePerm (τ • a) = topePerm a * τ⁻¹ := by
  refine Equiv.ext (fun i => ?_)
  rw [topePerm_apply, Equiv.Perm.mul_apply, topePerm_apply]
  exact topeRank_reindex τ a i

/-- **`crossPerm` is `Sₙ`-invariant.**  The right `τ⁻¹` factors cancel in the order change of an
edge, so the crossing permutation is a function of the orbit alone. -/
theorem crossPerm_reindex (τ : Equiv.Perm (Fin n)) (a b : Sal (braidCOM n)) :
    crossPerm (τ • a) (τ • b) = crossPerm a b := by
  simp only [crossPerm, topePerm_reindex]
  group

/-! ## The descended crossing cocycle -/

/-- The crossing permutation of a quotient-category morphism: `crossPerm` of any representing span,
well-defined by `Sₙ`-invariance. -/
noncomputable def crossPermQuot {X Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (f : X ⟶ Y) : Equiv.Perm (Fin n) :=
  Quotient.liftOn' f (fun s => crossPerm s.val.1 s.val.2) <| by
    rintro s t ⟨g, hg1, hg2⟩
    change crossPerm s.val.1 s.val.2 = crossPerm t.val.1 t.val.2
    rw [← hg1, ← hg2, crossPerm_reindex]

@[simp] theorem crossPermQuot_quotHom {a b : Sal (braidCOM n)} (hab : a ≤ b) :
    crossPermQuot (quotHom hab) = crossPerm a b := rfl

theorem crossPermQuot_id (X : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) :
    crossPermQuot (𝟙 X) = 1 := by
  change crossPerm (QuotCat.idSpan X).val.1 (QuotCat.idSpan X).val.2 = 1
  exact crossPerm_self _

theorem crossPermQuot_comp {X Y Z : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    crossPermQuot (f ≫ g) = crossPermQuot g * crossPermQuot f := by
  induction f using Quotient.inductionOn' with | h p =>
  induction g using Quotient.inductionOn' with | h q =>
  change crossPerm (QuotCat.compSpan p q).val.1 (QuotCat.compSpan p q).val.2
      = crossPerm q.val.1 q.val.2 * crossPerm p.val.1 p.val.2
  rw [QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd,
    crossPerm_comp p.val.1 (QuotCat.alignPair p q • q.val.1) (QuotCat.alignPair p q • q.val.2),
    crossPerm_reindex, QuotCat.alignPair_smul]

theorem crossPermQuot_len {X Y Z : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    permLen (crossPermQuot (f ≫ g)) = permLen (crossPermQuot f) + permLen (crossPermQuot g) := by
  induction f using Quotient.inductionOn' with | h p =>
  induction g using Quotient.inductionOn' with | h q =>
  have hbc : QuotCat.alignPair p q • q.val.1 ≤ QuotCat.alignPair p q • q.val.2 :=
    (smul_le_smul_iff _).2 q.property.1
  have hab : p.val.1 ≤ QuotCat.alignPair p q • q.val.1 := by
    rw [QuotCat.alignPair_smul]; exact p.property.1
  change permLen (crossPerm (QuotCat.compSpan p q).val.1 (QuotCat.compSpan p q).val.2)
      = permLen (crossPerm p.val.1 p.val.2) + permLen (crossPerm q.val.1 q.val.2)
  rw [QuotCat.compSpan_val_fst, QuotCat.compSpan_val_snd, crossPerm_noDoubleCross hab hbc,
    crossPerm_reindex, QuotCat.alignPair_smul]

/-! ## The middle vertical arrow -/

/-- **The Salvetti braid grading, descended to the `Sₙ`-quotient.** -/
noncomputable def salvettiGradingQuot (n : ℕ) :
    QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)) ⥤ SingleObj (Braid n) :=
  permBraidFunctor n (p := fun {_ _} f => crossPermQuot f)
    (hp1 := crossPermQuot_id) (hpc := fun f g => crossPermQuot_comp f g)
    (hlen := fun f g => crossPermQuot_len f g)

@[simp] theorem salvettiGradingQuot_map {X Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))}
    (f : X ⟶ Y) : (salvettiGradingQuot n).map f = ofPerm (crossPermQuot f) := rfl

/-- **The middle vertical map of the braid five-lemma ladder**: the free-groupoid lift of the
descended grading. -/
noncomputable def salvettiConstructionQuot (n : ℕ) :
    FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) ⥤ SingleObj (Braid n) :=
  FreeGroupoid.lift (salvettiGradingQuot n)

/-! ## The left square commutes -/

/-- The descended grading precomposed with the quotient functor is the original grading — a strict
functor equality, both sending an edge `a ⟶ b` to the positive braid of `crossPerm a b`. -/
theorem quotFunctor_comp_salvettiGradingQuot (n : ℕ) :
    OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n))
        ⋙ salvettiGradingQuot n
      = salvettiGrading n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun a b f => ?_)
  rfl

/-- **The left square of the braid five-lemma ladder.**  The middle vertical map, restricted along
the covering `quotCover`, is the original Salvetti construction. -/
theorem quotCover_comp_salvettiConstructionQuot (n : ℕ) :
    quotCover n ⋙ salvettiConstructionQuot n = salvettiConstruction n := by
  rw [quotCover, salvettiConstructionQuot, salvettiConstruction,
    FreeGroupoid.map_comp_lift, quotFunctor_comp_salvettiGradingQuot]

end CubeChains
