import CubeChains.Machinery.SortPerm
import CubeChains.Concurrency.Salvetti.ChainBraidFace
import CubeChains.Concurrency.Executions.RunSegal

/-!
# Concurrency/Executions/RunRestrict — restricting a run along a face preserves the step order

A `Run (□m)` linearises the `m` axes; `flatten r.chain` is the step at which `r` performs each axis.
Restricting along a `Box` face `g : ▫k ⟶ ▫m` is a `List.filterMap` of the bead list, and a
`filterMap` keeps its survivors in their original relative order — so the restricted run performs
the axes of `▫k` in the order `r` performs their `faceEmb g`-images.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet

namespace CubeChains

/-! ### `filterMap` keeps survivors in their original order -/

/-- Entry `i` of `l.filterMap f` is entry `s i` of `l`, with `s` strictly monotone.  Mathlib's
`Sublist` API cannot serve: `filterMap` changes the element type, so this is not a `Sublist`. -/
theorem exists_strictMono_filterMap {α β : Type*} (f : α → Option β) : ∀ l : List α,
    ∃ s : Fin (l.filterMap f).length → Fin l.length,
      StrictMono s ∧ ∀ i, f (l.get (s i)) = some ((l.filterMap f).get i)
  | [] => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | a :: l => by
    obtain ⟨s, hmono, hget⟩ := exists_strictMono_filterMap f l
    cases hfa : f a with
    | none =>
        rw [List.filterMap_cons_none hfa]
        exact ⟨fun i => (s i).succ, fun _ _ hij => Fin.succ_lt_succ_iff.mpr (hmono hij), hget⟩
    | some b =>
        rw [List.filterMap_cons_some hfa]
        refine ⟨Fin.cons 0 fun j => (s j).succ, ?_, ?_⟩
        · intro i j hij
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · exact absurd hij (Fin.not_lt_zero i)
          · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · simpa only [Fin.cons_zero, Fin.cons_succ] using Fin.succ_pos _
            · simpa only [Fin.cons_succ] using
                Fin.succ_lt_succ_iff.mpr (hmono (Fin.succ_lt_succ_iff.mp hij))
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · simpa only [Fin.cons_zero] using hfa
          · simpa only [Fin.cons_succ] using hget i'

/-! ### A cube-list entry and its sign vector -/

/-- The sign vector of a cube-list entry, read off the *bundle* — so `congrArg` transports an
equation of entries past the dependent second component. -/
def beadSign {m : ℕ} (c : Σ d : ℕ+, (□m).cells (d : ℕ)) : Fin m → Option Bool := (ev c.2).val

/-- **A chain's cube list reads its bead partition**: entry `t` is free at `q` iff `q`'s bead is
`t`. -/
theorem beadSign_toList_eq_none_iff {m : ℕ} (b : Ch (□m))
    (t : Fin (beadCell b.map.hom).toList.length) (q : Fin m) :
    beadSign ((beadCell b.map.hom).toList.get t) q = none ↔ (beadOf b q : ℕ) = (t : ℕ) := by
  rw [congrArg (fun c => beadSign c q) (Beads.toList_get (beadCell b.map.hom) t)]
  exact (ev_beadFace_eq_none_iff b _ q).trans
    ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-- **A surviving cube's sign vector is the original's along `faceEmb`** — `restrictCoord` is
precomposition with `faceEmb`, and `Box.ofSign` round-trips. -/
theorem beadSign_restrictCube {k m : ℕ} (g : ▫k ⟶ ▫m) (c : Σ d : ℕ+, (□m).cells (d : ℕ))
    (d : Σ d : ℕ+, (□k).cells (d : ℕ)) (h : restrictCube g c = some d) (i : Fin k) :
    beadSign d i = beadSign c (faceEmb g i) := by
  obtain ⟨-, rfl⟩ := eq_of_restrictCube_eq_some g h
  exact congrFun (congrArg Subtype.val (Box.sign_ofSign (restrictCell g (Box.sign c.2)))) i

/-! ### The cube list of a restricted run

`runPresheaf.map` is `EdgeChain.restrict` conjugated by the sealed `Run.equivEdgeChain`, and
`EdgeChain.restrict` is `List.filterMap (restrictCube g)` on cube lists.  `cubes_equivEdgeChain` is
the only handle needed on the seal. -/

/-- The restricted run's bead list is the original's, `filterMap`ped by the cube projection. -/
theorem cubes_runPresheaf_map {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    (beadCell (runPresheaf.map g.op r).map.hom).toList
      = ((beadCell r.map.hom).toList).filterMap (restrictCube g) := by
  have hr : Run.equivEdgeChain (□k) (runPresheaf.map g.op r)
      = EdgeChain.restrict g (Run.equivEdgeChain (□m) r) := by
    change Run.equivEdgeChain (□k) ((Run.equivEdgeChain (□k)).symm
      (EdgeChain.restrict g (Run.equivEdgeChain (□m) r))) = _
    exact Equiv.apply_symm_apply _ _
  rw [← cubes_equivEdgeChain (runPresheaf.map g.op r), hr]
  change restrictChain g (Run.equivEdgeChain (□m) r).1.cubes = _
  rw [cubes_equivEdgeChain r]
  rfl

/-! ### Restriction is order-preserving

The bead list of the restricted run is a `filterMap` of the original's, so its `t`-th bead is the
original's `s t`-th for a strictly monotone `s`; and the two beads are free at `i` resp.
`faceEmb g i`.  Since a run's `flatten` *is* its `beadOf` (`flatten_eq_beadOf_of_ones`), and
`beadOf` is *the* bead a coordinate is free in, that pins
`flatten r ∘ faceEmb g = s ∘ flatten (restricted run)`. -/

/-- The equation, for any run of `□k` whose bead list is the `filterMap` — stated this way so the
`Fin`-counts are spelled `k` and `m`, not `(op ▫k).unop.dim`. -/
theorem flatten_restrict_of_cubes {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) (r' : Run (□k))
    (hcubes : (beadCell r'.map.hom).toList
      = ((beadCell r.map.hom).toList).filterMap (restrictCube g)) :
    ∃ s : Fin k → Fin m, StrictMono s ∧
      ∀ i : Fin k, flatten r.chain (faceEmb g i) = s (flatten r'.chain i) := by
  obtain ⟨s₀, hmono, hstep⟩ : ∃ s : Fin (beadCell r'.map.hom).toList.length
      → Fin (beadCell r.map.hom).toList.length, StrictMono s ∧
      ∀ t, restrictCube g ((beadCell r.map.hom).toList.get (s t))
        = some ((beadCell r'.map.hom).toList.get t) := by
    rw [hcubes]; exact exists_strictMono_filterMap (restrictCube g) _
  have hlen : (beadCell r.map.hom).toList.length = m :=
    (Beads.length_toList _).trans (runCubeLength r)
  have hlen' : (beadCell r'.map.hom).toList.length = k :=
    (Beads.length_toList _).trans (runCubeLength r')
  refine ⟨fun x => (s₀ (x.cast hlen'.symm)).cast hlen, ?_, ?_⟩
  · intro x y hxy
    have hlt : s₀ (x.cast hlen'.symm) < s₀ (y.cast hlen'.symm) :=
      hmono (by rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]; exact hxy)
    rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]
    exact hlt
  · intro i
    have hfree : beadSign ((beadCell r'.map.hom).toList.get
        ((flatten r'.chain i).cast hlen'.symm)) i = none :=
      (beadSign_toList_eq_none_iff r'.chain _ i).mpr
        (by rw [Fin.val_cast]; exact (flatten_eq_beadOf_of_ones r'.ones i).symm)
    have hsrc : beadSign ((beadCell r.map.hom).toList.get
        (s₀ ((flatten r'.chain i).cast hlen'.symm))) (faceEmb g i) = none :=
      (beadSign_restrictCube g _ _ (hstep ((flatten r'.chain i).cast hlen'.symm)) i).symm.trans
        hfree
    have hval : (beadOf r.chain (faceEmb g i) : ℕ)
        = (s₀ ((flatten r'.chain i).cast hlen'.symm) : ℕ) :=
      (beadSign_toList_eq_none_iff r.chain _ (faceEmb g i)).mp hsrc
    refine Fin.ext ?_
    rw [Fin.val_cast, flatten_eq_beadOf_of_ones r.ones]
    exact hval

/-- **Restricting a run along a face is order-preserving, as an equation**: `s` re-embeds the
restricted steps into `r`'s strictly monotonically, hence is the order iso onto their image. -/
theorem flatten_restrict {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    ∃ s : Fin k → Fin m, StrictMono s ∧
      ∀ i : Fin k,
        flatten r.chain (faceEmb g i) = s (flatten (runPresheaf.map g.op r).chain i) :=
  flatten_restrict_of_cubes g r _ (cubes_runPresheaf_map g r)

/-- **Restriction along a face is order-preserving**, in comparison form. -/
theorem flatten_restrict_lt_iff {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) (i j : Fin k) :
    flatten (runPresheaf.map g.op r).chain i < flatten (runPresheaf.map g.op r).chain j
      ↔ flatten r.chain (faceEmb g i) < flatten r.chain (faceEmb g j) := by
  obtain ⟨s, hs, heq⟩ := flatten_restrict g r
  rw [heq i, heq j]
  exact hs.lt_iff_lt.symm

/-- **The positional form**: the restricted run performs axis `i` at the *rank* of
`flatten r (faceEmb g i)` among the steps `r` gives the face's axes. -/
theorem flatten_restrict_rank {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) (i : Fin k) :
    (flatten (runPresheaf.map g.op r).chain i : ℕ)
      = (Finset.univ.filter fun x : Fin k =>
          flatten r.chain (faceEmb g x) < flatten r.chain (faceEmb g i)).card := by
  set r' := runPresheaf.map g.op r
  have hrew : (Finset.univ.filter fun x : Fin k =>
        flatten r.chain (faceEmb g x) < flatten r.chain (faceEmb g i))
      = Finset.univ.filter fun x : Fin k => flatten r'.chain x < flatten r'.chain i :=
    Finset.filter_congr fun x _ => (flatten_restrict_lt_iff g r x i).symm
  rw [hrew, Equiv.Perm.card_filter_lt (flatten r'.chain) (flatten r'.chain i)]

end CubeChains
