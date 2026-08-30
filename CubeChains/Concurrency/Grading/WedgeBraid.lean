import CubeChains.Precubical.Chains.Category
import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Precubical.Basic.Terminal
import CubeChains.Machinery.Graded
import CubeChains.Machinery.Braid.Sum

/-!
# Concurrency/Grading/WedgeBraid — the braid grading of `Ch K`, from the coordinate map alone

A chain morphism is a wedge map; its coordinate bijection `coordMap`, read at both ends by the
lexicographic flattening `pos`, is a permutation of the strands, and crossings never undo
(`coordMap_noDoubleCross`).  Hence `chBraid K : Ch K ⥤ FullBraid`, factoring through the
serial-wedge category `Ch Zbp`.

Ordering by `pos` makes the grading a function of the wedge map alone, which is what a chain — with
no run to consult — wants.  It is also why it cannot grade *executions*:
`Concurrency/Complexification/NoMonodromy` shows `Ch (□ⁿ)` has no loops for such a grading to see.
-/

open CategoryTheory CategoryTheory.Limits BPSet CubeChain StdCube

namespace CubeChains

/-! ## The event order under a wedge map

Two facts drive everything.  A wedge map acts inside a bead by `faceEmb`, an **order embedding**, so
it never inverts a within-bead pair; and its bead component `blockIdx` is **monotone**, so an
inversion it does create has both events in one bead of the target.  Together: a crossed pair is
crossed inside a single bead downstream, where the next map preserves the order. -/

/-- **Inside a bead a wedge map preserves the event order** — there it is `faceEmb`. -/
theorem coordMap_pos_lt_of_fst_eq {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) {e e' : beadEvent a}
    (hb : e.1 = e'.1) (h : pos e < pos e') : pos (coordMap φ e) < pos (coordMap φ e') := by
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  obtain rfl : i = i' := hb
  rw [coordMap_eq, coordMap_eq, pos_lt_iff_of_fst_eq]
  exact (faceEmb (blockFace φ.hom i)).lt_iff_lt.mpr (pos_lt_iff_of_fst_eq.mp h)

/-- **A crossing lands inside one bead** — `blockIdx` is monotone, so it cannot reverse beads. -/
theorem coordMap_fst_eq_of_cross {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) {e e' : beadEvent a}
    (h : pos e < pos e') (hx : pos (coordMap φ e') < pos (coordMap φ e)) :
    (coordMap φ e').1 = (coordMap φ e).1 :=
  le_antisymm (Fin.le_def.mpr (fst_le_of_pos_lt hx))
    (coordMap_fst_monotone φ (Fin.le_def.mpr (fst_le_of_pos_lt h)))

/-- **No pair of events crosses twice.**  A crossing made by `φ` sits inside a single bead of `⋁b`,
where `ψ` preserves the order. -/
theorem coordMap_noDoubleCross {a b c : List ℕ+} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c)
    {e e' : beadEvent a} (h : pos e < pos e') (hx : pos (coordMap φ e') < pos (coordMap φ e)) :
    pos (coordMap ψ (coordMap φ e')) < pos (coordMap ψ (coordMap φ e)) :=
  coordMap_pos_lt_of_fst_eq ψ (coordMap_fst_eq_of_cross φ h hx) hx

end CubeChains

namespace ChainCat

open CubeChains

/-! ## The crossing permutation of a chain morphism

The strand count is *derived* from a chain (`dimSum a.dims`), so a permutation of the strands has to
be read at some count `N` the chain meets.  Carrying that count as an argument — rather than
transporting afterwards — is what makes the cocycle law a plain anti-homomorphism: the target
numbering of `g` and the source numbering of `h` differ only in their proofs, hence not at all. -/

/-- The strand an event occupies, at a strand count the chain meets — the events, flattened
lexicographically. -/
def strand {K : BPSet} (a : Ch K) {N : ℕ} (h : dimSum a.dims = N) : beadEvent a.dims ≃ Fin N :=
  pos.trans (finCongr ((dimSum_eq_sum_get a.dims).trans h))

@[simp] theorem strand_val {K : BPSet} (a : Ch K) {N : ℕ} (h : dimSum a.dims = N)
    (e : beadEvent a.dims) : (strand a h e : ℕ) = (pos e : ℕ) := rfl

theorem strand_lt_iff {K : BPSet} (a : Ch K) {N : ℕ} (h : dimSum a.dims = N)
    (e e' : beadEvent a.dims) : strand a h e < strand a h e' ↔ pos e < pos e' := Iff.rfl

/-- A chain morphism preserves the strand count. -/
theorem strandsEq {K : BPSet} {a b : Ch K} (g : a ⟶ b) : dimSum a.dims = dimSum b.dims :=
  serialWedge_dimSum_eq g.φ

/-- The target's strand count, forced by the source's. -/
theorem tgtStrands {K : BPSet} {a b : Ch K} {N : ℕ} (g : a ⟶ b) (h : dimSum a.dims = N) :
    dimSum b.dims = N := (strandsEq g).symm.trans h

/-- **The crossing permutation** of a chain morphism, read at a strand count `N` its source meets:
the coordinate bijection between the two flattenings. -/
def crossPerm {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b) :
    Equiv.Perm (Fin N) :=
  ((strand a h).symm.trans (coordMapEquiv g.φ)).trans (strand b (tgtStrands g h))

/-- What `crossPerm` does to a strand, read back on events — the workhorse of every law below. -/
theorem crossPerm_strand {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) (e : beadEvent a.dims) :
    crossPerm h g (strand a h e) = strand b (tgtStrands g h) (coordMap g.φ e) := by
  simp only [crossPerm, Equiv.trans_apply, Equiv.symm_apply_apply, coordMapEquiv_apply]

/-- `crossPerm` read on raw positions: the strand at `pos e` goes to `pos (coordMap e)`. -/
theorem crossPerm_val {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b)
    {e : beadEvent a.dims} {x : Fin N} (hx : (x : ℕ) = (pos e : ℕ)) :
    (crossPerm h g x : ℕ) = (pos (coordMap g.φ e) : ℕ) := by
  obtain rfl : x = strand a h e := Fin.ext hx
  rw [crossPerm_strand, strand_val]

/-- **Recounting the strands conjugates** — the one transport in sight, and it is `rfl`. -/
theorem crossPerm_recount {K : BPSet} {a b : Ch K} {N N' : ℕ} (h : dimSum a.dims = N)
    (h' : dimSum a.dims = N') (g : a ⟶ b) :
    crossPerm h' g = (finCongr (h.symm.trans h')).permCongr (crossPerm h g) :=
  Equiv.ext fun _ => rfl

/-- The crossing count does not depend on the strand count it is read at. -/
theorem permLen_crossPerm {K : BPSet} {a b : Ch K} {N N' : ℕ} (h : dimSum a.dims = N)
    (h' : dimSum a.dims = N') (g : a ⟶ b) : permLen (crossPerm h' g) = permLen (crossPerm h g) := by
  rw [crossPerm_recount h h', permLen_permCongr_finCongr]

theorem crossPerm_id {K : BPSet} (a : Ch K) {N : ℕ} (h : dimSum a.dims = N) :
    crossPerm h (𝟙 a) = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (strand a h).surjective i
  rw [crossPerm_strand, id_φ, coordMap_id, id_eq, Equiv.Perm.one_apply]

/-- **The cocycle law** — `coordMap_comp`, with the middle numbering shared. -/
theorem crossPerm_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b)
    (k : b ⟶ c) : crossPerm h (g ≫ k) = crossPerm (tgtStrands g h) k * crossPerm h g := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (strand a h).surjective i
  rw [Equiv.Perm.mul_apply, crossPerm_strand, crossPerm_strand, crossPerm_strand, comp_φ,
    coordMap_comp, Function.comp_apply]

/-- **No pair of strands crosses twice** — `coordMap_noDoubleCross`, in strand coordinates. -/
theorem crossPerm_noDoubleCross {K : BPSet} {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) (k : b ⟶ c) (i j : Fin N) (hij : i < j) (hx : crossPerm h g j < crossPerm h g i) :
    crossPerm (tgtStrands g h) k (crossPerm h g j)
      < crossPerm (tgtStrands g h) k (crossPerm h g i) := by
  obtain ⟨e, rfl⟩ := (strand a h).surjective i
  obtain ⟨e', rfl⟩ := (strand a h).surjective j
  rw [crossPerm_strand, crossPerm_strand] at hx ⊢
  rw [crossPerm_strand, crossPerm_strand]
  exact coordMap_noDoubleCross g.φ k.φ hij hx

/-- **Length-additivity of the crossing permutations** — the Coxeter length of a composite is the
sum, since a crossing made is never undone. -/
theorem permLen_crossPerm_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) (k : b ⟶ c) :
    permLen (crossPerm h (g ≫ k))
      = permLen (crossPerm h g) + permLen (crossPerm (tgtStrands g h) k) :=
  (congrArg permLen (crossPerm_comp h g k)).trans
    (permLen_mul_of_noDoubleCross (crossPerm_noDoubleCross h g k))

/-! ## Monoidality over the wedge

`chConcat` appends the beads and `coordMap` respects that splitting, so on the tensorator
`dimSum (a ++ b) = dimSum a + dimSum b` the crossing permutation is the **block sum** `permSum`.
Crossings then add across the tensorator, because the two blocks never interact. -/

/-- **The crossing permutation is monoidal over the wedge.** -/
theorem crossPerm_chConcat {K L : BPSet} {ab ab' : Ch K × Ch L} (fg : ab ⟶ ab') :
    crossPerm (dimSum_append ab.1.dims ab.2.dims) ((chConcat K L).map fg)
      = permSum (dimSum ab.1.dims) (dimSum ab.2.dims) (crossPerm rfl fg.1, crossPerm rfl fg.2) := by
  refine Equiv.ext fun x => x.addCases (fun y => Fin.ext ?_) (fun y => Fin.ext ?_)
  · set e := (strand ab.1 rfl).symm y with he
    have hy : (y : ℕ) = (pos e : ℕ) :=
      (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.1 rfl) y)).symm
    rw [permSum_apply_castAdd, Fin.val_castAdd,
      crossPerm_val _ _ (e := eventInl ab.1.dims ab.2.dims e)
        ((Fin.val_castAdd _ y).trans (hy.trans (pos_eventInl ab.1.dims ab.2.dims e).symm)),
      crossPerm_val rfl fg.1 hy]
    exact (congrArg (fun z => (pos z : ℕ)) (coordMap_concatHomφ_left fg.1 fg.2 e)).trans
      (pos_eventInl ab'.1.dims ab'.2.dims _)
  · set e := (strand ab.2 rfl).symm y with he
    have hy : (y : ℕ) = (pos e : ℕ) :=
      (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.2 rfl) y)).symm
    rw [permSum_apply_natAdd, Fin.val_natAdd,
      crossPerm_val _ _ (e := eventInr ab.1.dims ab.2.dims e)
        ((Fin.val_natAdd _ y).trans (congrArg (dimSum ab.1.dims + ·) hy |>.trans
          (pos_eventInr ab.1.dims ab.2.dims e).symm)),
      crossPerm_val rfl fg.2 hy]
    exact ((congrArg (fun z => (pos z : ℕ)) (coordMap_concatHomφ_right fg.1 fg.2 e)).trans
      (pos_eventInr ab'.1.dims ab'.2.dims _)).trans
      (congrArg (· + (pos (coordMap fg.2.φ e) : ℕ)) (strandsEq fg.1).symm)

/-- **Crossings add across the tensorator** — the two blocks never interact
(`permLen_permSum`). -/
theorem permLen_crossPerm_chConcat {K L : BPSet} {ab ab' : Ch K × Ch L} (fg : ab ⟶ ab') :
    permLen (crossPerm rfl ((chConcat K L).map fg))
      = permLen (crossPerm rfl fg.1) + permLen (crossPerm rfl fg.2) := by
  rw [permLen_crossPerm (dimSum_append ab.1.dims ab.2.dims) rfl ((chConcat K L).map fg),
    crossPerm_chConcat, permLen_permSum]

/-! ## The functor -/

/-- **The braid grading of `Ch K`**, valued in any germ family: a chain to its strand count, a
morphism to the simple of the permutation its coordinate map performs.  Length-additivity
(`crossPerm_noDoubleCross`) is the whole functor law. -/
def chGerm {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M) (K : BPSet) :
    Ch K ⥤ Graded M where
  obj a := dimSum a.dims
  map g := G.hom (strandsEq g) (crossPerm rfl g)
  map_id a := by rw [crossPerm_id]; exact G.hom_one _
  map_comp g k := by
    rw [show crossPerm rfl (g ≫ k) = crossPerm (tgtStrands g rfl) k * crossPerm rfl g from
        crossPerm_comp rfl g k,
      ← G.hom_comp (strandsEq g) (strandsEq k) (crossPerm_noDoubleCross rfl g k),
      ← crossPerm_recount (tgtStrands g rfl) rfl k]

@[simp] theorem chGerm_map {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M) {K : BPSet}
    {a b : Ch K} (g : a ⟶ b) : (chGerm G K).map g = G.hom (strandsEq g) (crossPerm rfl g) := rfl

/-- The braid grading proper — the germ family at `Braid`. -/
def chBraid (K : BPSet) : Ch K ⥤ FullBraid := chGerm braidGerm K

/-- **The positive braid grading**: the same cocycle read in the monoid, where the simples carry no
inverses. -/
def chPosBraid (K : BPSet) : Ch K ⥤ FullPosBraid := chGerm posGerm K

/-- **The grading is blind to `K`**: it is the serial-wedge grading `chBraid Zbp` pushed forward. -/
theorem chBraid_eq_pushforward (K : BPSet) :
    chBraid K = pushforward (isTerminalZbp.from K) ⋙ chBraid Zbp := rfl

/-! ## Against the run-ordered grading

`ConcPos K` (`Concurrency/Salvetti/EventBraid`) orders events by the run, so it agrees with
`chBraid` exactly where the run is recoverable from the wedge map — the `H`-model question of
whether the grading of `Ch⋆ K` factors along `Ch (Hbp K) ⥤ Ch Zbp`. -/

end ChainCat
