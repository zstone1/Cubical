import CubeChains.Concurrency.Grading.Boundaries
import CubeChains.Precubical.Chains.Category
import CubeChains.Precubical.Segal.SegalAltitude
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Concurrency/Grading/BlockDecomp — where a block of a serial-wedge map sits

For a bi-pointed wedge map `φ : ⋁ad ⟶ ⋁cd`, the block data `blockIdx`/`blockFace` is
`Precubical/Chains/WedgeMap`; here it is *located*, by prefix sums of the dimension lists
(`serialWedge_beadStart_blockIdx`), whence `blockIdx` is monotone
(`serialWedge_blockIdx_monotone`) and `∑ ad = ∑ cd` (`serialWedge_dimSum_eq`).
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

`blockIdx` is pinned numerically by dimension prefix sums.  Everything here runs on the serial
wedge's *own* tautological altitude (`serialWedge_admitsAltitude`), which always exists — no
hypothesis on any ambient `K`. -/

/-- The tautBead chain of a serial wedge: its own beads, read off the identity. -/
theorem serialWedge_isCubeChain_id (cd : List ℕ+) :
    IsCubeChain (⋁cd).init (beadCell (𝟙 (⋁cd).toPsh)).toList (⋁cd).final := by
  simpa using beadCell_isCubeChain (K := ⋁cd) cd (𝟙 (⋁cd).toPsh)

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

/-- **A source bead's start names its target block**: `serialWedge_beadStart_blockIdx` brackets the
start between two prefix sums of `cd`, which is exactly what pins `dimComp cd`'s index. -/
theorem serialWedge_blockIdx_eq_index {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    ∃ hlt : beadStart ad i.val < BPSet.dimSum cd,
      ((CubeChains.dimComp cd rfl).index ⟨beadStart ad i.val, hlt⟩ : ℕ) = (blockIdx φ i).val := by
  have heq := serialWedge_beadStart_blockIdx φ hinit i
  have hsucc := beadStart_succ cd (blockIdx φ i)
  have hcpos : 0 < (cd.get (blockIdx φ i) : ℕ) := (cd.get (blockIdx φ i)).2
  have htle : trueCount (Box.sign (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    trueCount_le (Box.sign (blockFace φ i))
  have hipos : 0 < (ad.get i : ℕ) := (ad.get i).2
  have hub : beadStart ad i.val < beadStart cd ((blockIdx φ i).val + 1) := by omega
  exact ⟨hub.trans_le (beadStart_le_dimSum cd _), CubeChains.index_eq_of_beadStart rfl _
    (show beadStart cd (blockIdx φ i).val ≤ beadStart ad i.val by omega) hub⟩

/-- **`blockIdx` of a bi-pointed wedge map is monotone** — it is `Composition.index` read at a bead
start, and both of those rise. -/
theorem serialWedge_blockIdx_monotone {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init) :
    Monotone (blockIdx φ) := by
  intro i i' hii
  obtain ⟨h1, e⟩ := serialWedge_blockIdx_eq_index φ hinit i
  obtain ⟨h2, e'⟩ := serialWedge_blockIdx_eq_index φ hinit i'
  rw [Fin.le_def, ← e, ← e']
  exact (CubeChains.dimComp cd rfl).index_monotone
    (show (⟨beadStart ad i.val, h1⟩ : Fin (BPSet.dimSum cd)) ≤ ⟨beadStart ad i'.val, h2⟩ from
      Fin.le_def.mpr (beadStart_mono ad (Fin.le_def.mp hii)))

/-- **`∑ ad = ∑ cd` for a bi-pointed serial-wedge map**: the pushed chain has dimension list
`ad`, the tautBead chain has `cd`, and both span the same altitude gap in `⋁cd`. -/
theorem serialWedge_dimSum_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    BPSet.dimSum ad = BPSet.dimSum cd := by
  obtain ⟨alt, hax, _⟩ := BPSet.serialWedge_admitsAltitude cd
  have hT := isCubeChain_alt_final alt hax _ _ _ (serialWedge_isCubeChain_id cd)
  have hP := isCubeChain_alt_final alt hax _ _ _
    (serialWedge_isCubeChain_push φ.hom φ.app_init)
  rw [φ.app_final] at hP
  rw [Beads.map_fst_toList] at hT hP
  exact_mod_cast add_left_cancel (hP.symm.trans hT)

end CubeChain

namespace ChainCat

/-- **A chain morphism preserves the strand count** — it is a serial-wedge map on the nose. -/
theorem dimSum_eq_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    BPSet.dimSum a.dims = BPSet.dimSum b.dims :=
  serialWedge_dimSum_eq f.φ

end ChainCat
