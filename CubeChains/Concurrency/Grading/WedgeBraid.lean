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

/-! ## The crossing permutation of a chain morphism -/

/-- The strand an event occupies — the chain's events, flattened lexicographically. -/
def strand {K : BPSet} (a : Ch K) : beadEvent a.dims ≃ Fin (dimSum a.dims) :=
  pos.trans (finCongr (dimSum_eq_sum_get a.dims))

@[simp] theorem strand_val {K : BPSet} (a : Ch K) (e : beadEvent a.dims) :
    (strand a e : ℕ) = (pos e : ℕ) := rfl

theorem strand_lt_iff {K : BPSet} (a : Ch K) (e e' : beadEvent a.dims) :
    strand a e < strand a e' ↔ pos e < pos e' := Iff.rfl

/-- A chain morphism preserves the strand count. -/
theorem strandsEq {K : BPSet} {a b : Ch K} (g : a ⟶ b) : dimSum a.dims = dimSum b.dims :=
  serialWedge_dimSum_eq g.φ

/-- **The crossing permutation** of a chain morphism: its coordinate bijection, read at both ends
by the flattening. -/
def crossPerm {K : BPSet} {a b : Ch K} (g : a ⟶ b) : Equiv.Perm (Fin (dimSum a.dims)) :=
  ((strand a).symm.trans ((coordMapEquiv g.φ).trans (strand b))).trans
    (finCongr (strandsEq g)).symm

/-- What `crossPerm` does to a strand, read back on events — the workhorse of every law below. -/
theorem crossPerm_strand {K : BPSet} {a b : Ch K} (g : a ⟶ b) (e : beadEvent a.dims) :
    (crossPerm g (strand a e) : ℕ) = (strand b (coordMap g.φ e) : ℕ) := by
  simp only [crossPerm, Equiv.trans_apply, Equiv.symm_apply_apply, coordMapEquiv_apply,
    finCongr_symm, finCongr_apply_coe]

/-- The crossing permutation at the target's flattening, the shape both functor laws need. -/
theorem finCongr_crossPerm {K : BPSet} {a b : Ch K} (g : a ⟶ b) (e : beadEvent a.dims) :
    finCongr (strandsEq g) (crossPerm g (strand a e)) = strand b (coordMap g.φ e) :=
  Fin.ext (crossPerm_strand g e)

theorem crossPerm_id {K : BPSet} (a : Ch K) : crossPerm (𝟙 a) = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (strand a).surjective i
  refine Fin.ext ?_
  rw [crossPerm_strand, id_φ, coordMap_id, id_eq, Equiv.Perm.one_apply]

/-- **The cocycle law**, at the middle chain's strand count — `coordMap_comp`. -/
theorem crossPerm_cocycle {K : BPSet} {a b c : Ch K} (g : a ⟶ b) (h : b ⟶ c)
    (i : Fin (dimSum a.dims)) :
    finCongr (strandsEq g) (crossPerm (g ≫ h) i)
      = crossPerm h (finCongr (strandsEq g) (crossPerm g i)) := by
  obtain ⟨e, rfl⟩ := (strand a).surjective i
  rw [finCongr_crossPerm]
  refine Fin.ext ?_
  rw [finCongr_apply_coe, crossPerm_strand, crossPerm_strand, comp_φ, coordMap_comp,
    Function.comp_apply]

/-- **No pair of strands crosses twice** — `coordMap_noDoubleCross`, in strand coordinates. -/
theorem crossPerm_noDoubleCross {K : BPSet} {a b c : Ch K} (g : a ⟶ b) (h : b ⟶ c)
    (i j : Fin (dimSum a.dims)) (hij : i < j) (hx : crossPerm g j < crossPerm g i) :
    crossPerm h (finCongr (strandsEq g) (crossPerm g j))
      < crossPerm h (finCongr (strandsEq g) (crossPerm g i)) := by
  obtain ⟨e, rfl⟩ := (strand a).surjective i
  obtain ⟨e', rfl⟩ := (strand a).surjective j
  rw [finCongr_crossPerm, finCongr_crossPerm, Fin.lt_def, crossPerm_strand, crossPerm_strand]
  refine coordMap_noDoubleCross g.φ h.φ ((strand_lt_iff a e e').mp hij) ?_
  rw [Fin.lt_def] at hx ⊢
  rw [crossPerm_strand, crossPerm_strand] at hx
  exact hx

/-- **Length-additivity of the crossing permutations** — the Coxeter length of a composite is the
sum, since a crossing made is never undone. -/
theorem permLen_crossPerm_comp {K : BPSet} {a b c : Ch K} (g : a ⟶ b) (h : b ⟶ c) :
    permLen (crossPerm (g ≫ h)) = permLen (crossPerm g) + permLen (crossPerm h) :=
  permLen_of_cocycle_noDoubleCross (strandsEq g) (crossPerm_cocycle g h)
    (crossPerm_noDoubleCross g h)

/-! ## Read at a fixed strand count

Naming the permutations at `Fin N` instead of at `Fin (dimSum a.dims)` keeps the `dimSum`
bookkeeping away from callers: `crossPermAt` absorbs the transport, so the cocycle law becomes a
plain anti-homomorphism. -/

/-- The crossing permutation of a chain morphism, read on `Fin N`. -/
def crossPermAt {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b) :
    Equiv.Perm (Fin N) :=
  (finCongr h).permCongr (crossPerm g)

theorem crossPermAt_apply_val {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (g : a ⟶ b)
    (x : Fin N) : (crossPermAt h g x : ℕ) = (crossPerm g ((finCongr h).symm x) : ℕ) := rfl

theorem crossPerm_eq_iff_crossPermAt {K : BPSet} {a b : Ch K} {N : ℕ} {h : dimSum a.dims = N}
    {g : a ⟶ b} {σ : Equiv.Perm (Fin N)} :
    crossPerm g = ((finCongr h).permCongr).symm σ ↔ crossPermAt h g = σ :=
  ⟨fun hf => by rw [crossPermAt, hf, Equiv.apply_symm_apply],
   fun hf => by rw [← hf, crossPermAt, Equiv.symm_apply_apply]⟩

theorem crossPermAt_eq_one_iff {K : BPSet} {a b : Ch K} {N : ℕ} {h : dimSum a.dims = N}
    {g : a ⟶ b} : crossPermAt h g = 1 ↔ crossPerm g = 1 :=
  (crossPerm_eq_iff_crossPermAt (h := h) (σ := 1)).symm.trans
    (by rw [show ((finCongr h).permCongr).symm (1 : Equiv.Perm (Fin N)) = 1 from
      Equiv.ext fun _ => rfl])

/-- **The cocycle law at a fixed strand count** — `crossPerm_cocycle`, with the transports absorbed
into `crossPermAt`. -/
theorem crossPermAt_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (g : a ⟶ b) (h : b ⟶ c) :
    crossPermAt ha (g ≫ h) = crossPermAt hb h * crossPermAt ha g := by
  refine Equiv.ext fun x => Fin.ext ?_
  have hcoc := congrArg Fin.val (crossPerm_cocycle g h ((finCongr ha).symm x))
  rw [finCongr_apply_coe] at hcoc
  rw [crossPermAt_apply_val, hcoc]
  exact congrArg Fin.val (congrArg (crossPerm h) (Fin.ext rfl))

@[simp] theorem permLen_crossPermAt {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (g : a ⟶ b) : permLen (crossPermAt h g) = permLen (crossPerm g) :=
  permLen_permCongr_finCongr _ _

/-- **Length-additivity at a fixed strand count** — a crossing made is never undone. -/
theorem permLen_crossPermAt_comp {K : BPSet} {a b c : Ch K} {N : ℕ} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) (g : a ⟶ b) (h : b ⟶ c) :
    permLen (crossPermAt hb h * crossPermAt ha g)
      = permLen (crossPermAt hb h) + permLen (crossPermAt ha g) := by
  rw [← crossPermAt_comp ha hb, permLen_crossPermAt, permLen_crossPermAt, permLen_crossPermAt,
    permLen_crossPerm_comp]
  exact Nat.add_comm _ _

/-! ## Monoidality over the wedge

`chConcat` appends the beads and `coordMap` respects that splitting, so on the tensorator
`dimSum (a ++ b) = dimSum a + dimSum b` the crossing permutation is the **block sum** `permSum`.
Crossings then add across the tensorator, because the two blocks never interact. -/

/-- The first factor's events keep their strand in the concatenation. -/
theorem strand_eventInl {K L : BPSet} (ab : Ch K × Ch L) (e : beadEvent ab.1.dims) :
    (strand ((chConcat K L).obj ab) (eventInl ab.1.dims ab.2.dims e) : ℕ) = (strand ab.1 e : ℕ) :=
  pos_eventInl ab.1.dims ab.2.dims e

/-- The second factor's events are shifted past the first factor's strands. -/
theorem strand_eventInr {K L : BPSet} (ab : Ch K × Ch L) (e : beadEvent ab.2.dims) :
    (strand ((chConcat K L).obj ab) (eventInr ab.1.dims ab.2.dims e) : ℕ)
      = dimSum ab.1.dims + (strand ab.2 e : ℕ) :=
  pos_eventInr ab.1.dims ab.2.dims e

/-- **The crossing permutation is monoidal over the wedge.** -/
theorem crossPerm_chConcat {K L : BPSet} {ab ab' : Ch K × Ch L} (fg : ab ⟶ ab') :
    crossPermAt (dimSum_append ab.1.dims ab.2.dims) ((chConcat K L).map fg)
      = permSum (dimSum ab.1.dims) (dimSum ab.2.dims) (crossPerm fg.1, crossPerm fg.2) := by
  simp only [crossPermAt]
  refine Equiv.ext fun x => x.addCases (fun y => ?_) (fun y => ?_)
  · set e := (strand ab.1).symm y with he
    have hx : (finCongr (dimSum_append ab.1.dims ab.2.dims)).symm (Fin.castAdd _ y)
        = strand ((chConcat K L).obj ab) (eventInl ab.1.dims ab.2.dims e) :=
      Fin.ext ((strand_eventInl ab e).trans
        (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.1) y))).symm
    rw [permSum_apply_castAdd]
    refine Fin.ext ?_
    calc ((finCongr (dimSum_append ab.1.dims ab.2.dims)).permCongr
            (crossPerm ((chConcat K L).map fg)) (Fin.castAdd _ y) : ℕ)
        = (crossPerm ((chConcat K L).map fg)
            (strand ((chConcat K L).obj ab) (eventInl ab.1.dims ab.2.dims e)) : ℕ) := by
          rw [Equiv.permCongr_apply, finCongr_apply_coe, hx]
          rfl
      _ = (strand ((chConcat K L).obj ab') (coordMap (concatHomφ fg.1 fg.2)
            (eventInl ab.1.dims ab.2.dims e)) : ℕ) := crossPerm_strand _ _
      _ = (strand ((chConcat K L).obj ab')
            (eventInl ab'.1.dims ab'.2.dims (coordMap fg.1.φ e)) : ℕ) :=
          congrArg _ (congrArg _ (coordMap_concatHomφ_left fg.1 fg.2 e))
      _ = (crossPerm fg.1 (strand ab.1 e) : ℕ) :=
          (strand_eventInl ab' _).trans (crossPerm_strand fg.1 e).symm
      _ = (Fin.castAdd _ (crossPerm fg.1 y) : ℕ) :=
          congrArg (fun t => ((crossPerm fg.1 t : Fin _) : ℕ)) (Equiv.apply_symm_apply _ y)
  · set e := (strand ab.2).symm y with he
    have hx : (finCongr (dimSum_append ab.1.dims ab.2.dims)).symm (Fin.natAdd _ y)
        = strand ((chConcat K L).obj ab) (eventInr ab.1.dims ab.2.dims e) :=
      Fin.ext ((strand_eventInr ab e).trans
        (congrArg (dimSum ab.1.dims + ·)
          (congrArg Fin.val (Equiv.apply_symm_apply (strand ab.2) y)))).symm
    rw [permSum_apply_natAdd]
    refine Fin.ext ?_
    calc ((finCongr (dimSum_append ab.1.dims ab.2.dims)).permCongr
            (crossPerm ((chConcat K L).map fg)) (Fin.natAdd _ y) : ℕ)
        = (crossPerm ((chConcat K L).map fg)
            (strand ((chConcat K L).obj ab) (eventInr ab.1.dims ab.2.dims e)) : ℕ) := by
          rw [Equiv.permCongr_apply, finCongr_apply_coe, hx]
          rfl
      _ = (strand ((chConcat K L).obj ab') (coordMap (concatHomφ fg.1 fg.2)
            (eventInr ab.1.dims ab.2.dims e)) : ℕ) := crossPerm_strand _ _
      _ = (strand ((chConcat K L).obj ab')
            (eventInr ab'.1.dims ab'.2.dims (coordMap fg.2.φ e)) : ℕ) :=
          congrArg _ (congrArg _ (coordMap_concatHomφ_right fg.1 fg.2 e))
      _ = dimSum ab'.1.dims + (crossPerm fg.2 (strand ab.2 e) : ℕ) :=
          (strand_eventInr ab' _).trans
            (congrArg (dimSum ab'.1.dims + ·) (crossPerm_strand fg.2 e).symm)
      _ = (Fin.natAdd _ (crossPerm fg.2 y) : ℕ) := by
          rw [Equiv.apply_symm_apply, strandsEq fg.1]
          rfl

/-- **Crossings add across the tensorator** — the two blocks never interact
(`permLen_permSum`). -/
theorem permLen_crossPerm_chConcat {K L : BPSet} {ab ab' : Ch K × Ch L} (fg : ab ⟶ ab') :
    permLen (crossPerm ((chConcat K L).map fg))
      = permLen (crossPerm fg.1) + permLen (crossPerm fg.2) :=
  (permLen_crossPermAt (dimSum_append ab.1.dims ab.2.dims) _).symm.trans
    (by rw [crossPerm_chConcat, permLen_permSum])

/-! ## The functor -/

/-- **The braid grading of `Ch K`**, valued in any germ family: a chain to its strand count, a
morphism to the simple of the permutation its coordinate map performs.  Length-additivity
(`permLen_crossPerm_comp`, packaged as `crossPerm_noDoubleCross`) is the whole functor law. -/
def chGerm {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M) (K : BPSet) :
    Ch K ⥤ Graded M where
  obj a := dimSum a.dims
  map g := G.hom (strandsEq g) (crossPerm g)
  map_id a := by rw [crossPerm_id]; exact G.hom_one _
  map_comp g h :=
    (G.hom_comp (strandsEq g) (strandsEq h) (crossPerm_cocycle g h)
      (crossPerm_noDoubleCross g h)).symm

@[simp] theorem chGerm_map {M : ℕ → Type*} [∀ n, Monoid (M n)] (G : Graded.Germ M) {K : BPSet}
    {a b : Ch K} (g : a ⟶ b) : (chGerm G K).map g = G.hom (strandsEq g) (crossPerm g) := rfl

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
