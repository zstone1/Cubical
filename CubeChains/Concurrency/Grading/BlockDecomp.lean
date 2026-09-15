import CubeChains.Concurrency.Grading.Boundaries
import CubeChains.Concurrency.Grading.CoordFunctor

/-!
# Concurrency/Grading/BlockDecomp — where a block of a serial-wedge map sits

For a wedge map `φ : ⋁a ⟶ ⋁b` the block data `blockIdx`/`blockFace` is
`Precubical/Chains/WedgeMap`; here it is *located*.  Read in a chain of the target, the coordinates
before a bead are counted by its bead start (`card_beadOf_lt`) and `blockIdx` is monotone, so a
source bead lies inside its target block (`serialWedge_bead_sub_block`) and every junction of the
target is one of the source's (`boundaries_subset_of_wedgeHom`).
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

/-! ### The bead starts are the composition's prefix sums

`dimComp`'s `sizeUpTo` *is* `beadStart` (`dimComp_sizeUpTo`), so mathlib's sandwich for
`Composition.index` reads straight off the total-free bead starts. -/

/-- **A coordinate's block against the bead starts** — `Composition.index_lt_iff` at `beadStart`. -/
theorem index_lt_iff_beadStart {N : ℕ} {d : List ℕ+} (hd : BPSet.dimSum d = N) (p : Fin N)
    (j : ℕ) : ((dimComp d hd).index p : ℕ) < j ↔ (p : ℕ) < beadStart d j := by
  rw [Composition.index_lt_iff, dimComp_sizeUpTo]
  rfl

/-- **A coordinate's block, from the two bead starts bracketing it.** -/
theorem index_eq_of_beadStart {N : ℕ} {d : List ℕ+} (hd : BPSet.dimSum d = N) {j : ℕ} (p : Fin N)
    (h1 : beadStart d j ≤ (p : ℕ)) (h2 : (p : ℕ) < beadStart d (j + 1)) :
    ((dimComp d hd).index p : ℕ) = j :=
  Composition.index_eq_of_bracket _ p (by rw [dimComp_sizeUpTo]; exact h1)
    (by rw [dimComp_sizeUpTo]; exact h2)

/-- **An event's strand lies in its own bead's block.** -/
theorem index_strand {N : ℕ} (d : List ℕ+) (hd : BPSet.dimSum d = N) (e : beadEvent d) :
    ((dimComp d hd).index (strand d hd e) : ℕ) = e.1 := by
  have hs := beadStart_succ d e.1
  have hk := e.2.isLt
  exact index_eq_of_beadStart hd _ (by rw [strand_val, pos_val]; omega)
    (by rw [strand_val, pos_val]; omega)

/-- **The coordinates before a bead are the first `beadStart` many** — `coordFlip` matches them
with the events before it, which the flattening ranks first. -/
theorem card_beadOf_lt {n : ℕ} (A : Ch (□n)) (j : ℕ) :
    (Finset.univ.filter fun r : Fin n => (beadOf A r : ℕ) < j).card = beadStart A.dims j := by
  have hN := wedgeDimSum_eq A.map
  rw [Finset.card_equiv ((coordFlip A.map).symm.trans (strand A.dims hN))
      (t := Finset.univ.filter fun r : Fin n => (r : ℕ) < beadStart A.dims j) fun r => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply, strand_val,
      pos_lt_beadStart_iff, beadOf_eq], Fin.card_filter_val_lt]
  exact min_eq_right ((beadStart_le_dimSum _ _).trans_eq hN)

end CubeChains

namespace CubeChain

open CubeChains

/-- **A source bead lies inside its target block**: read in a chain of the target, the coordinates
before the block are among those before the bead, and those up to the bead among those up to the
block — `blockIdx` being monotone. -/
theorem serialWedge_bead_sub_block {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) (i : Fin ad.length) :
    beadStart cd (blockIdx φ.hom i).val ≤ beadStart ad i.val
      ∧ beadStart ad (i.val + 1) ≤ beadStart cd ((blockIdx φ.hom i).val + 1) := by
  obtain ⟨χ⟩ := nonempty_toCube cd
  let A : Ch (□(BPSet.dimSum cd)) := ⟨ad, φ ≫ χ⟩
  let B : Ch (□(BPSet.dimSum cd)) := ⟨cd, χ⟩
  have hcomp : ∀ u, beadFace A.map.hom u = blockFace φ.hom u ≫ beadFace χ.hom (blockIdx φ.hom u) :=
    fun u => beadFace_comp φ.hom χ.hom u
  have hAB : ∀ r, beadOf B r = blockIdx φ.hom (beadOf A r) := fun r => by
    obtain ⟨k, hk⟩ := (mem_range_iff_beadOf A (beadOf A r) r).mpr rfl
    refine (mem_range_iff_beadOf B _ r).mp ⟨faceEmb (blockFace φ.hom _) k, ?_⟩
    rw [← faceEmb_comp, ← hcomp]
    exact hk
  have hmono := serialWedge_blockIdx_monotone φ
  rw [← card_beadOf_lt A, ← card_beadOf_lt A, ← card_beadOf_lt B, ← card_beadOf_lt B]
  refine ⟨Finset.card_le_card fun r => ?_, Finset.card_le_card fun r => ?_⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hAB]
  · exact fun h => lt_of_not_ge fun hc => absurd (hmono (Fin.le_def.mpr hc)) (not_le.mpr h)
  · exact fun h => Nat.lt_succ_of_le (Fin.le_def.mp (hmono (Fin.le_def.mpr (Nat.le_of_lt_succ h))))

/-- **Every coordinate of a source bead lies in its target block**, read by `cd`'s composition. -/
theorem serialWedge_index_of_bead {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) {N : ℕ}
    (hc : BPSet.dimSum cd = N) (i : Fin ad.length) (p : Fin N) (h1 : beadStart ad i.val ≤ (p : ℕ))
    (h2 : (p : ℕ) < beadStart ad (i.val + 1)) :
    ((CubeChains.dimComp cd hc).index p : ℕ) = (blockIdx φ.hom i).val :=
  have hsub := serialWedge_bead_sub_block φ i
  CubeChains.index_eq_of_beadStart hc p (hsub.1.trans h1) (h2.trans_le hsub.2)

end CubeChain

namespace ChainCat

open CubeChains

/-- **A chain morphism preserves the strand count** — it is a serial-wedge map on the nose. -/
theorem dimSum_eq_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    BPSet.dimSum a.dims = BPSet.dimSum b.dims :=
  serialWedge_dimSum_eq f.φ

/-- **A wedge map only refines**: every junction of the target is one of the source's — the
target's blocks are unions of the source's (`serialWedge_index_of_bead`). -/
theorem boundaries_subset_of_wedgeHom {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    boundaries cd ⊆ boundaries ad := by
  have hd := serialWedge_dimSum_eq φ
  have hbead : ∀ p : Fin (BPSet.dimSum cd), ((dimComp cd rfl).index p : ℕ)
      = (blockIdx φ.hom ⟨(dimComp ad hd).index p, by
          simpa using ((dimComp ad hd).index p).isLt⟩).val := fun p =>
    serialWedge_index_of_bead φ rfl _ p
      (not_lt.mp fun h => absurd ((index_lt_iff_beadStart hd p _).mpr h) (lt_irrefl _))
      ((index_lt_iff_beadStart hd p _).mp (Nat.lt_succ_self _))
  refine boundaries_subset_of_index hd rfl fun p q hpq => Fin.ext ?_
  have hv : ((dimComp ad hd).index p : ℕ) = (dimComp ad hd).index q := congrArg Fin.val hpq
  rw [hbead p, hbead q]
  exact congrArg (fun i : Fin ad.length => (blockIdx φ.hom i).val) (Fin.ext hv)

/-- **A refinement inherits every boundary of its coarsening.** -/
theorem boundaries_subset_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    boundaries b.dims ⊆ boundaries a.dims :=
  boundaries_subset_of_wedgeHom f.φ

end ChainCat
