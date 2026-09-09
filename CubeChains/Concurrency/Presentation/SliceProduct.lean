import CubeChains.Concurrency.Presentation.SliceGerm
import CubeChains.Machinery.Presentation.LengthGraded

/-!
# Concurrency/Presentation/SliceProduct — the slice over `d` is the beads' tensor

The runs over `d` are the parabolic `S_{d₁} × ⋯ × S_{d_k}` and the weak order of a parabolic is the
product of the blocks', so `⨂ᵢ dehornoy p dᵢ` presents the localized slice over `d`
(`beadSlicePresents`): the wedge's localization splits bead by bead (`locChConsEquiv`), and the
tensor presents the product.

The tensor does **not** carry the merges.  Its interchange square has the same two letters on both
sides, and no germ relation relates two words of one length (`PosGermRel.length_ne`), so two beads
merging into one have nowhere to send the square — `isEmpty_beadHom_pair_two`, already at
`[1,1] ⟶ [2]`.  Hence the family the colimit consumes reads its generators at the *whole* strand
count on the down-set of runs (`slicePoly`), where disjoint simples multiply into one letter.
-/

open CategoryTheory Opposite BPSet CubeChains Polygraph

namespace ChainCat

namespace BraidPresentation

variable (p : BraidPresentation)

/-! ## The beads' tensor -/

/-- **`⨂ᵢ p.germPoly dᵢ`**, right-nested along the list; the empty wedge is `□0`, so the empty
tensor is the zero-strand germ. -/
noncomputable def beadTensor : List ℕ+ → Polygraph.{0, 0, 0}
  | [] => (p.germPoly (WeakDownset.top 0)).op
  | c :: rest => Polygraph.prod (p.germPoly (WeakDownset.top (c : ℕ))).op (beadTensor rest)

/-- **`⨂ᵢ dehornoy p dᵢ` presents `Ch(⋁d)[W⁻¹]`.** -/
noncomputable def beadTensorPresents : (d : List ℕ+) →
    Presents (p.beadTensor d) ((W (⋁d)).Localization)
  | [] => p.germPresentsCube 0
  | c :: rest =>
      (Presents.prod (p.germPresentsCube (c : ℕ)) (beadTensorPresents rest)).transport
        (locChConsEquiv c rest)

/-- **…and hence the localized slice over `d`** — the paper's slice presentation. -/
noncomputable def beadSlicePresents (d : List ℕ+) :
    Presents (p.beadTensor d) (((W Zbp).over (X := zObj d)).Localization) :=
  (p.beadTensorPresents d).transport (locOverEquivWedge d).symm

end BraidPresentation

/-! ## The merges have no image

A `Polygraph.Hom` sends a 2-cell to a 2-cell with the pushed-forward boundary *on the nose*, so an
interchange square must land on a relation between two words of length two.  The germ has none;
`ArtinRel`'s commutation is one, so the Artin naming escapes *this* obstruction and the general
statement still does not, `germBP` being a `BraidPresentation` like any other. -/

/-- **The Garside germ's 2-cells never relate two words of the same length.** -/
theorem lengthGraded_germBP_P (n : ℕ) : LengthGraded (germBP.P n) := fun α hα =>
  PosGermRel.length_ne α.2
    (by rw [MonoidPoly.length_word, MonoidPoly.length_word]; exact hα)

theorem lengthGraded_germPoly {n : ℕ} (C : WeakDownset n) :
    LengthGraded (germBP.germPoly C).op :=
  LengthGraded.op (LengthGraded.comap (germBP.germProj C) (lengthGraded_germBP_P n))

/-! ### The merge `[1,1] ⟶ [2]` -/

private theorem perm_fin_one (a : Equiv.Perm (Fin 1)) : a = 1 :=
  Equiv.ext fun _ => Subsingleton.elim _ _

/-- The unique point of the one-strand down-set. -/
def pt1 : (WeakDownset.top 1).carrier := Equiv.refl (Fin 1)

/-- The germ loop there — the identity simple, which every down-set carries. -/
noncomputable def loop1 : germBP.GermGen (WeakDownset.top 1) pt1 pt1 :=
  ⟨Equiv.refl (Fin 1), by
    have hlen : ∀ a : Equiv.Perm (Fin 1), permLen a = 0 := fun a => by
      rw [perm_fin_one a]; exact permLen_one
    refine (germBP.germStep_iff (Equiv.refl (Fin 1)) _ _).mpr
      ⟨rfl, (perm_fin_one _).trans (perm_fin_one _).symm, ?_⟩
    simp only [hlen]⟩

/-- **A merge is not a map of the beads' tensors**: the two beads of `[1,1]` span an interchange
square, the one bead of `[2]` has no relation between two words of one length, so `[1,1] ⟶ [2]`
has no image at all and `d ↦ ⨂ᵢ p.germPoly dᵢ` carries no functor structure. -/
theorem isEmpty_beadHom_pair_two :
    IsEmpty (Polygraph.Hom
      (Polygraph.prod (germBP.germPoly (WeakDownset.top 1)).op
        (germBP.germPoly (WeakDownset.top 1)).op)
      (germBP.germPoly (WeakDownset.top 2)).op) :=
  ⟨fun F => not_lengthGraded_prod loop1 loop1
      (LengthGraded.of_hom F (lengthGraded_germPoly (WeakDownset.top 2)))⟩

end ChainCat
