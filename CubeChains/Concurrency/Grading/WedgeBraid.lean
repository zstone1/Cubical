import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Precubical.Basic.Terminal
import CubeChains.Machinery.Braid.Sum

/-!
# Concurrency/Grading/WedgeBraid — the crossing permutation of a chain morphism

A chain morphism is a wedge map; its coordinate bijection `coordMap`, read at both ends by the
lexicographic flattening `pos`, is a permutation of the strands.  Ordering by `pos` makes
`crossPerm` a function of the wedge map alone: a cocycle (`crossPerm_comp`) whose crossing counts
add (`permLen_crossPerm_comp`), a refinement being monotone on beads and order-preserving inside
one, and a block sum on the tensorator (`crossPerm_chConcat`).  `Concurrency/Grading/ChainHom`
reads it off a chain of the cube instead (`crossPerm_flatten`).
-/

open CategoryTheory CategoryTheory.Limits BPSet CubeChain StdCube

namespace ChainCat

open CubeChains

/-! ## The crossing permutation of a chain morphism

A chain morphism's coordinate bijection, read at each end through `strand`
(`Concurrency/Grading/CoordFunctor`). -/

/-- The target's strand count, forced by the source's. -/
theorem tgtStrands {K : BPSet} {a b : Ch K} {N : ℕ} (g : a ⟶ b) (h : dimSum a.dims = N) :
    dimSum b.dims = N := (dimSum_eq_of_hom g).symm.trans h

/-- **The crossing permutation** of a chain morphism, read at a strand count `N` its source meets:
the coordinate bijection between the two flattenings. -/
def crossPerm {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b) :
    Equiv.Perm (Fin N) :=
  conjPerm (strand a.dims h) (strand b.dims (tgtStrands g h)) (coordMapEquiv g.φ)

/-- **`crossPerm` reads the wedge map and nothing else** — the target `K` is not consulted, so two
chains on one pair of shapes carrying one wedge map cross alike. -/
theorem crossPerm_eq_of_φ {K K' : BPSet} {da db : List ℕ+} {ma : ⋁da ⟶ K} {mb : ⋁db ⟶ K}
    {ma' : ⋁da ⟶ K'} {mb' : ⋁db ⟶ K'} {N : ℕ} (h : dimSum da = N)
    {g : (⟨da, ma⟩ : Ch K) ⟶ ⟨db, mb⟩} {g' : (⟨da, ma'⟩ : Ch K') ⟶ ⟨db, mb'⟩}
    (hφ : Hom.φ g = Hom.φ g') : crossPerm h g = crossPerm h g' := by
  rw [crossPerm, crossPerm, hφ]

/-- What `crossPerm` does to a strand, read back on events — the workhorse of every law below. -/
theorem crossPerm_strand {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) (e : beadEvent a.dims) :
    crossPerm h g (strand a.dims h e) = strand b.dims (tgtStrands g h) (coordMap g.φ e) :=
  conjPerm_apply _ _ _ e

/-- `crossPerm` read on raw positions: the strand at `pos e` goes to `pos (coordMap e)`. -/
theorem crossPerm_val {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b)
    {e : beadEvent a.dims} {x : Fin N} (hx : (x : ℕ) = (pos e : ℕ)) :
    (crossPerm h g x : ℕ) = (pos (coordMap g.φ e) : ℕ) := by
  obtain rfl : x = strand a.dims h e := Fin.ext hx
  rw [crossPerm_strand, strand_val]

/-- **Recounting the strands conjugates** — the one transport in sight, and it is `rfl`. -/
theorem crossPerm_recount {K : BPSet} {a b : Ch K} {N N' : ℕ} (h : dimSum a.dims = N)
    (h' : dimSum a.dims = N') (g : a ⟶ b) :
    crossPerm h' g = (finCongr (h.symm.trans h')).permCongr (crossPerm h g) :=
  Equiv.ext fun _ => rfl

/-- **Crossing nothing is a property of the morphism**, not of the count it is read at. -/
theorem crossPerm_eq_one_congr {K : BPSet} {a b : Ch K} {N N' : ℕ} {h : dimSum a.dims = N}
    {h' : dimSum a.dims = N'} {g : a ⟶ b} (hg : crossPerm h g = 1) : crossPerm h' g = 1 := by
  obtain rfl : N = N' := h.symm.trans h'
  rwa [Subsingleton.elim h' h]

theorem crossPerm_id {K : BPSet} (a : Ch K) {N : ℕ} (h : dimSum a.dims = N) :
    crossPerm h (𝟙 a) = 1 := by
  rw [crossPerm, id_φ, coordMapEquiv_id]
  exact conjPerm_refl _

/-- **The cocycle law** — `coordMapEquiv`'s functoriality, with the middle numbering shared. -/
theorem crossPerm_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b)
    (k : b ⟶ c) : crossPerm h (g ≫ k) = crossPerm (tgtStrands g h) k * crossPerm h g := by
  rw [crossPerm, comp_φ, coordMapEquiv_comp]
  exact conjPerm_trans _ (strand b.dims (tgtStrands g h)) _ _ _

/-- **A crossing permutation rises along each bead of its source** — inside a bead a refinement is
an order embedding into its block. -/
theorem crossPerm_lt_of_index_eq {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (f : a ⟶ b) {x y : Fin N} (hxy : (dimComp a.dims h).index x = (dimComp a.dims h).index y)
    (hlt : x < y) : crossPerm h f x < crossPerm h f y := by
  obtain ⟨e, rfl⟩ := (strand a.dims h).surjective x
  obtain ⟨e', rfl⟩ := (strand a.dims h).surjective y
  have hbead : e.1 = e'.1 := Fin.ext ((index_strand a.dims h e).symm.trans
    ((congrArg Fin.val hxy).trans (index_strand a.dims h e')))
  rw [crossPerm_strand, crossPerm_strand, Fin.lt_def, strand_val, strand_val]
  exact Fin.lt_def.mp ((pos_coordMap_lt_iff f.φ hbead).mpr
    (Fin.lt_def.mpr ((strand_val _ _ e).symm.trans_lt ((Fin.lt_def.mp hlt).trans_eq
      (strand_val _ _ e')))))

/-- **The crossing count is additive.**  A refinement is monotone on beads and order-preserving
inside one, so a pair it crosses lands in one bead of its target — where the next refinement keeps
it crossed. -/
theorem permLen_crossPerm_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) (k : b ⟶ c) :
    permLen (crossPerm h (g ≫ k))
      = permLen (crossPerm h g) + permLen (crossPerm (tgtStrands g h) k) := by
  rw [crossPerm_comp]
  refine permLen_mul_of_inversions_subset fun ⟨x, y⟩ hxy => ?_
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
    at hxy ⊢
  obtain ⟨e, rfl⟩ := (strand a.dims h).surjective x
  obtain ⟨e', rfl⟩ := (strand a.dims h).surjective y
  simp only [crossPerm_strand, Fin.lt_def, strand_val] at hxy ⊢
  obtain ⟨hlt, hinv⟩ := hxy
  refine ⟨hlt, (pos_coordMap_lt_iff k.φ (le_antisymm
    (fst_le_of_pos_lt (Fin.lt_def.mpr hinv))
    (coordMap_fst_monotone g.φ (fst_le_of_pos_lt (Fin.lt_def.mpr hlt))))).mpr
    (Fin.lt_def.mpr hinv) |> Fin.lt_def.mp⟩

/-- **A chart shifts by the crossing permutation.**  A *chart* of a chain is a bijection of its
events with the strands; read the source's as the target's pulled back along the wedge map and the
two comparisons with the lexicographic order differ by exactly `crossPerm`.  Every firing order in
the development is such a comparison — `flatten` at a chain of the cube, `fibrePerm` at a
decoration by `H` — so this is the only functoriality any of them needs. -/
theorem crossPerm_mul_chart {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (cb : beadEvent b.dims ≃ Fin N) :
    crossPerm h f * conjPerm ((coordMapEquiv (Hom.φ f)).trans cb) (strand a.dims h) (Equiv.refl _)
      = conjPerm cb (strand b.dims (tgtStrands f h)) (Equiv.refl _) :=
  conjPerm_mul_pullback (strand a.dims h) (strand b.dims (tgtStrands f h)) cb
    (coordMapEquiv (Hom.φ f))

/-! ## Monoidality over the wedge

`chConcat` appends the beads and `coordMap` respects that splitting, so on the tensorator
`dimSum (a ++ b) = dimSum a + dimSum b` the crossing permutation is the **block sum** `permSum`.
Crossings then add across the tensorator, because the two blocks never interact. -/

/-- **The crossing permutation is monoidal over the wedge.** -/
theorem crossPerm_chConcat {K L : BPSet} {ab ab' : Ch K × Ch L} (fg : ab ⟶ ab') :
    crossPerm (dimSum_append ab.1.dims ab.2.dims) ((chConcat K L).map fg)
      = permSum (dimSum ab.1.dims) (dimSum ab.2.dims) (crossPerm rfl fg.1, crossPerm rfl fg.2) := by
  refine Equiv.ext fun x => x.addCases (fun y => Fin.ext ?_) (fun y => Fin.ext ?_)
  · set e := (strand ab.1.dims rfl).symm y with he
    have hy : (y : ℕ) = (pos e : ℕ) :=
      (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.1.dims rfl) y)).symm
    rw [permSum_apply_castAdd, Fin.val_castAdd,
      crossPerm_val _ _ (e := eventInl ab.1.dims ab.2.dims e)
        ((Fin.val_castAdd _ y).trans (hy.trans (pos_eventInl ab.1.dims ab.2.dims e).symm)),
      crossPerm_val rfl fg.1 hy]
    exact (congrArg (fun z => (pos z : ℕ)) (coordMap_concatHomφ_left fg.1 fg.2 e)).trans
      (pos_eventInl ab'.1.dims ab'.2.dims _)
  · set e := (strand ab.2.dims rfl).symm y with he
    have hy : (y : ℕ) = (pos e : ℕ) :=
      (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.2.dims rfl) y)).symm
    rw [permSum_apply_natAdd, Fin.val_natAdd,
      crossPerm_val (dimSum_append ab.1.dims ab.2.dims) ((chConcat K L).map fg)
        (e := eventInr ab.1.dims ab.2.dims e)
        ((Fin.val_natAdd _ y).trans (congrArg (dimSum ab.1.dims + ·) hy |>.trans
          (pos_eventInr ab.1.dims ab.2.dims e).symm)),
      crossPerm_val rfl fg.2 hy]
    exact ((congrArg (fun z => (pos z : ℕ)) (coordMap_concatHomφ_right fg.1 fg.2 e)).trans
      (pos_eventInr ab'.1.dims ab'.2.dims _)).trans
      (congrArg (· + (pos (coordMap fg.2.φ e) : ℕ)) (dimSum_eq_of_hom fg.1).symm)

end ChainCat
