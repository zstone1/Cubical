import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Concurrency.Presentation.Dehornoy
import CubeChains.Machinery.Presentation.LengthGraded

/-!
# Concurrency/Presentation/SliceProduct — why the beads' *tensor* carries no merge

The runs over `d` are the parabolic `S_{d₁} × ⋯ × S_{d_k}`, so the beads' Day tensor of germs has
the right cells over each chain.  It carries no **merge**: an interchange square has the same two
on both sides, and no germ relation relates two words of one length (`lengthGraded_taut`), so two
beads merging into one have nowhere to send the square — `isEmpty_beadHom_pair_two`, already at
`[1,1] ⟶ [2]`.

The **product** is what does carry it (`garsidePolyListCons`): there a 2-cell is a word, and the
identity relation pads the shorter side.  That is the whole difference between the two.
-/

open CategoryTheory Opposite BPSet CubeChains Polygraph

namespace ChainCat

/-! ## The merges have no image

A `Polygraph.Hom` sends a 2-cell to a 2-cell with the pushed-forward boundary *on the nose*, so an
interchange square must land on a relation between two words of length two.  The germ has none;
`ArtinRel`'s commutation is one, so the Artin naming escapes *this* obstruction.  What makes the
germ's product work instead is **padding** — the identity is among the simples, so both factors
advance at every letter (`tautProdIso`). -/

/-- **The Garside germ's 2-cells never relate two words of the same length.** -/
theorem lengthGraded_dehornoyPoly (n : ℕ) : LengthGraded (dehornoyPoly n).op :=
  LengthGraded.op (lengthGraded_taut (C := WeakOrder n))

/-- The germ loop at one strand — the identity simple, which every germ carries. -/
def loop1 : ((dehornoyPoly 1).op).Gen (WeakOrder.of 1) (WeakOrder.of 1) := 𝟙 _

/-- **A merge is not a map of the beads' tensors**: the two beads of `[1,1]` span an interchange
square, the one bead of `[2]` has no relation between two words of one length, so `[1,1] ⟶ [2]` has
no image at all and `d ↦ ⨂ᵢ dehornoyPoly dᵢ` carries no functor structure. -/
theorem isEmpty_beadHom_pair_two :
    IsEmpty (Polygraph.Hom (Polygraph.prod (dehornoyPoly 1).op (dehornoyPoly 1).op)
      (dehornoyPoly 2).op) :=
  ⟨fun F => not_lengthGraded_prod loop1 loop1
    (LengthGraded.of_hom F (lengthGraded_dehornoyPoly 2))⟩

/-! ## …and the base carries no multiplication at all

The same length argument one level down: a multiplication `p.poly ⊗ p.poly ⟶ p.poly` would have to
send the interchange square to a relation between two words of length two, which the Garside germ
has none of.  So the block sums of the graded braid monoid are not visible to any polygraph
structure on its presentation. -/

/-- The Garside germ's relations at one strand count also change the word length. -/
theorem lengthGraded_germBP_P (n : ℕ) : LengthGraded (germBP.P n) := fun α hα =>
  PosGermRel.length_ne α.2
    (by rw [MonoidPoly.length_word, MonoidPoly.length_word]; exact hα)

theorem lengthGraded_germBP_poly : LengthGraded germBP.poly :=
  LengthGraded.coprod lengthGraded_germBP_P

/-- **The Garside base is not a monoid in polygraphs** — it has no multiplication whatever. -/
theorem isEmpty_germ_mul :
    IsEmpty (Polygraph.Hom (Polygraph.prod germBP.poly germBP.poly) germBP.poly) :=
  ⟨fun F => not_lengthGraded_prod (germBP.gen (1 : Equiv.Perm (Fin 1)))
      (germBP.gen (1 : Equiv.Perm (Fin 1))) (LengthGraded.of_hom F lengthGraded_germBP_poly)⟩

end ChainCat
