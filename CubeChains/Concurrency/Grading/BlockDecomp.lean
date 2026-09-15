import CubeChains.Concurrency.Grading.Boundaries
import CubeChains.Precubical.Chains.Category
import CubeChains.Precubical.Chains.Altitude
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Concurrency/Grading/BlockDecomp — where a block of a serial-wedge map sits

For a bi-pointed wedge map `φ : ⋁ad ⟶ ⋁cd`, the block data `blockIdx`/`blockFace` is
`Precubical/Chains/WedgeMap`; here it is *located*, by prefix sums of the dimension lists: a source
bead lies inside its target block (`serialWedge_bead_sub_block`), so `blockIdx` is monotone and the
target's junctions are among the source's (`boundaries_subset_of_wedgeHom`).
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

end CubeChains

namespace CubeChain

/-! ### Where a block sits: the prefix-sum sandwich

`blockIdx` is pinned numerically by dimension prefix sums, read in the grading every serial wedge
carries (`serialWedge_admitsAltitude`) — no hypothesis on any ambient `K`. -/

/-- The chain a wedge map into `⋁cd` pushes forward, for any map fixing the initial vertex. -/
theorem serialWedge_isCubeChain_push {ed cd : List ℕ+} (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (hinit : hom⟪0⟫ (⋁ed).init = (⋁cd).init) :
    IsCubeChain (⋁cd).init (beadCell hom).toList (hom⟪0⟫ (⋁ed).final) := by
  have h := beadCell_isCubeChain (K := ⋁cd) ed hom
  rwa [hinit] at h

/-- The altitude of bead `k` of a wedge map into `⋁cd` is where that bead starts.
A packaging of `isCubeChain_alt_get` through `Beads.toList_get`. -/
theorem serialWedge_bead_alt {ed cd : List ℕ+}
    (alt : ∀ n, (⋁cd).cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude (⋁cd).toPsh alt)
    (h0 : alt 0 (⋁cd).init = 0)
    (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (hinit : hom⟪0⟫ (⋁ed).init = (⋁cd).init)
    (k : Fin ed.length) :
    alt (ed.get k : ℕ) (beadCell hom k) = (beadStart ed k.val : ℤ) := by
  have hlt : k.val < (beadCell hom).toList.length := by
    rw [Beads.length_toList]; exact k.isLt
  have hcast : (⟨k.val, hlt⟩ : Fin (beadCell hom).toList.length).cast
      (Beads.length_toList (beadCell hom)) = k := Fin.ext rfl
  have hget := Beads.toList_get (beadCell hom) ⟨k.val, hlt⟩
  have hg := isCubeChain_alt_get alt hax (beadCell hom).toList (⋁cd).init _
    (serialWedge_isCubeChain_push hom hinit) k.val hlt
  rw [h0, zero_add, Beads.map_fst_toList] at hg
  rw [hget, hcast] at hg
  exact hg

/-- **A source bead sits inside its target block**, offset by the block face's `trueCount`:
bead `i` of `ad` starts `trueCount (Box.sign (blockFace φ i))` into block `blockIdx φ i` of `cd`.
Uses **only** `serialWedge_admitsAltitude cd`. -/
theorem serialWedge_beadStart_blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    beadStart ad i.val
      = beadStart cd (blockIdx φ i).val + trueCount (Box.sign (blockFace φ i)) := by
  obtain ⟨alt, hax, h0⟩ := BPSet.serialWedge_admitsAltitude cd
  have hP := serialWedge_bead_alt alt hax h0 φ hinit i
  have hT := serialWedge_bead_alt alt hax h0 (𝟙 (⋁cd).toPsh) (by simp) (blockIdx φ i)
  rw [beadCell_id] at hT
  have hc := PrecubicalSet.alt_cubeMap alt hax (tautBead cd (blockIdx φ i)) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  have hz : (beadStart ad i.val : ℤ)
      = (beadStart cd (blockIdx φ i).val : ℤ) + (trueCount (Box.sign (blockFace φ i)) : ℤ) := by
    rw [← hP, ← hT, blockFace_spec_cell φ i]; exact hc
  exact_mod_cast hz

/-- **A source bead lies inside its target block**: bead `i` of `ad` runs within the prefix sums of
`cd` bracketing block `blockIdx φ i` — it starts `trueCount` in, and is no longer than the block. -/
theorem serialWedge_bead_sub_block {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    beadStart cd (blockIdx φ i).val ≤ beadStart ad i.val
      ∧ beadStart ad (i.val + 1) ≤ beadStart cd ((blockIdx φ i).val + 1) := by
  have heq := serialWedge_beadStart_blockIdx φ hinit i
  have htle : trueCount (Box.sign (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) := trueCount_le _
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    cells_card_le (Box.sign (blockFace φ i))
  have hs := beadStart_succ ad i
  have hs' := beadStart_succ cd (blockIdx φ i)
  constructor <;> omega

/-- **Every coordinate of a source bead lies in its target block**, read by `cd`'s composition. -/
theorem serialWedge_index_of_bead {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init) {N : ℕ} (hc : BPSet.dimSum cd = N)
    (i : Fin ad.length) (p : Fin N) (h1 : beadStart ad i.val ≤ (p : ℕ))
    (h2 : (p : ℕ) < beadStart ad (i.val + 1)) :
    ((CubeChains.dimComp cd hc).index p : ℕ) = (blockIdx φ i).val :=
  have hsub := serialWedge_bead_sub_block φ hinit i
  CubeChains.index_eq_of_beadStart hc p (hsub.1.trans h1) (h2.trans_le hsub.2)

/-- **`blockIdx` of a bi-pointed wedge map is monotone** — it is `Composition.index` read at a bead
start, and both of those rise. -/
theorem serialWedge_blockIdx_monotone {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init) :
    Monotone (blockIdx φ) := by
  have hlt : ∀ i : Fin ad.length, beadStart ad i.val < beadStart ad (i.val + 1) := fun i => by
    have := (ad.get i).pos; have := beadStart_succ ad i; omega
  have hstart : ∀ i : Fin ad.length, beadStart ad i.val < BPSet.dimSum cd := fun i =>
    (hlt i).trans_le ((serialWedge_bead_sub_block φ hinit i).2.trans (beadStart_le_dimSum cd _))
  intro i i' hii
  rw [Fin.le_def, ← serialWedge_index_of_bead φ hinit rfl i ⟨_, hstart i⟩ le_rfl (hlt i),
    ← serialWedge_index_of_bead φ hinit rfl i' ⟨_, hstart i'⟩ le_rfl (hlt i')]
  exact (CubeChains.dimComp cd rfl).index_monotone
    (Fin.le_def.mpr (beadStart_mono ad (Fin.le_def.mp hii)))

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
    serialWedge_index_of_bead φ.hom φ.app_init rfl _ p
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
