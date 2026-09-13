import CubeChains.Concurrency.Salvetti.EventPerm

/-!
# Concurrency/Executions/RunSegal — the Segal decomposition of a run's linearization

A run `a` of `⋁dims` performs bead `i` at the consecutive block of steps
`[beadStart dims i, beadStart dims i + dᵢ)`, and inside that block in the order bead `i`'s own
local run `runProj a i` prescribes.  Equationally: the step index of an event is its
lexicographic position `pos`, twisted inside each bead by that bead's local run order
(`runTwist`).
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain

namespace CubeChains

open RunWedge

/-! ### The step order of a single cube's run

A run of `□m` is a chain of an all-edges shape, so the step at which it performs each axis is that
chain's firing order `flatten` (`Concurrency/Grading/CoordFunctor`). -/

theorem runCubeLength {m : ℕ} (r : Run (□m)) : r.dims.length = m :=
  (dimSum_eq_length_of_ones r.ones).symm.trans (wedgeDimSum_eq r.map)

/-- The step performing the axis that edge `e` of the run flips is `e`'s own index. -/
theorem flatten_run_coordFlip {m : ℕ} (r : Run (□m)) (e : beadEvent r.dims) :
    (flatten r.chain (coordFlip r.map e) : ℕ) = (e.1 : ℕ) :=
  (congrArg Fin.val (flatten_coordFlip r.map e)).trans (pos_ones r.ones e)

/-! ### The run's event permutation

`runTwist a` sends an event to the position at which `a` performs it: bead order first, then bead
`i`'s own local run order inside bead `i`. -/

/-- Reorder the events inside each bead by that bead's local run. -/
def runTwist {dims : List ℕ+} (a : Run (⋁dims)) : beadEvent dims ≃ beadEvent dims :=
  Equiv.sigmaCongrRight (fun i => flatten (runProj a i).chain)

@[simp] theorem runTwist_apply {dims : List ℕ+} (a : Run (⋁dims)) (e : beadEvent dims) :
    runTwist a e = ⟨e.1, flatten (runProj a e.1).chain e.2⟩ := rfl

theorem runTwist_mk {dims : List ℕ+} (a : Run (⋁dims)) (i : Fin dims.length)
    (x : Fin ((dims.get i : ℕ))) : runTwist a ⟨i, x⟩ = ⟨i, flatten (runProj a i).chain x⟩ := rfl

/-! ### The Segal recursion of `runProj`

A run of `⋁(c :: rest)` splits into a run of `□c` and a run of `⋁rest`; its local runs are the
head one and the tail's, because a run's classifier is a `Glue.desc` of the two transposes. -/

/-- The right leg of a run's classifier at a cons — the mirror of `runPshEquiv_symm_inl`. -/
theorem runPshEquiv_symm_inr (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    wedgeInr (□(c : ℕ)) (⋁rest) ≫ (runPshEquiv (c :: rest)).symm r
      = (runPshEquiv rest).symm (runSplit (consAltitude c rest) r).2 :=
  wedge2Desc_inr _ _ _

theorem runProj_zero (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    runProj r 0 = (runSplit (consAltitude c rest) r).1 :=
  (congrArg yonedaEquiv (runPshEquiv_symm_inl c rest r)).trans (Equiv.apply_symm_apply _ _)

theorem runProj_succ (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) (j : Fin rest.length) :
    runProj r j.succ = runProj (runSplit (consAltitude c rest) r).2 j :=
  congrArg yonedaEquiv
    ((Category.assoc (ιᵂ rest j) (wedgeInr (□(c : ℕ)) (⋁rest))
        ((runPshEquiv (c :: rest)).symm r)).trans
      (congrArg (fun t => ιᵂ rest j ≫ t) (runPshEquiv_symm_inr c rest r)))

theorem runProj_concat_zero (c : ℕ+) (rest : List ℕ+) (b₀ : Run (□(c : ℕ))) (b₁ : Run (⋁rest)) :
    runProj (a := c :: rest) ((runConcat (□(c : ℕ)) (⋁rest)).obj (b₀, b₁)) 0 = b₀ := by
  rw [runProj_zero c rest, runSplit_runConcat]

theorem runProj_concat_succ (c : ℕ+) (rest : List ℕ+) (b₀ : Run (□(c : ℕ))) (b₁ : Run (⋁rest))
    (j : Fin rest.length) :
    runProj (a := c :: rest) ((runConcat (□(c : ℕ)) (⋁rest)).obj (b₀, b₁)) j.succ
      = runProj b₁ j := by
  rw [runProj_succ c rest, runSplit_runConcat]

/-- The head bead of a cons contributes its local run's step index. -/
theorem pos_runTwist_cons_zero (c : ℕ+) (rest : List ℕ+) (a : Run (⋁(c :: rest)))
    (b₀ : Run (□(c : ℕ))) (hb : runProj a 0 = b₀) (x : Fin (((c :: rest).get 0 : ℕ))) :
    (pos (runTwist a ⟨0, x⟩) : ℕ) = (flatten b₀.chain x : ℕ) := by
  rw [runTwist_mk, pos_cons_zero, hb]
  rfl

/-- A later bead of a cons contributes the tail's step index, shifted past the head cube. -/
theorem pos_runTwist_cons_succ (c : ℕ+) (rest : List ℕ+) (a : Run (⋁(c :: rest)))
    (b₁ : Run (⋁rest)) (hb : ∀ j : Fin rest.length, runProj a j.succ = runProj b₁ j)
    (w : beadEvent rest) :
    (pos (runTwist a ⟨w.1.succ, w.2⟩) : ℕ) = (c : ℕ) + (pos (runTwist b₁ w) : ℕ) := by
  rw [runTwist_mk, pos_cons_succ, hb w.1, runTwist_apply]
  rfl

/-! ### The coordinate map of a chain concatenation

Concatenating a chain of `□c` with a chain of `⋁rest` puts the first chain's coordinates into bead
`0` of `⋁(c :: rest)` and shifts the second's by one bead. -/

/-- Left half: the first factor's events flip bead `0`'s coordinates. -/
theorem coordMap_concat_left (c : ℕ+) (rest : List ℕ+) (L : Ch (□(c : ℕ))) (R : Ch (⋁rest))
    (x : beadEvent L.dims) :
    coordMap (b := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R) (eventInl L.dims R.dims x)
      = ⟨0, coordFlip L.map x⟩ := by
  obtain ⟨i, k⟩ := x
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor (c' := c :: rest)
    (concatChainMap (□(c : ℕ)) (⋁rest) L R)
    (ι_appendL R.dims L.dims i (eventInl L.dims R.dims ⟨i, k⟩).1 rfl)
    (isBeadFactor_self (c := c :: rest) 0)
    (incl_sq_beadFace (c' := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R)
      (concatChainMap_inclL (□(c : ℕ)) (⋁rest) L R) i)
    (eventInl L.dims R.dims ⟨i, k⟩).2 k rfl
  exact beadEvent_ext (congrArg Fin.val h1)
    (h2.trans (congrArg Fin.val (coordFlip_eq L.map ⟨i, k⟩).symm))

/-- Right half: the second factor's events are `R`'s, shifted by one bead. -/
theorem coordMap_concat_right (c : ℕ+) (rest : List ℕ+) (L : Ch (□(c : ℕ))) (R : Ch (⋁rest))
    (y : beadEvent R.dims) :
    coordMap (b := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R) (eventInr L.dims R.dims y)
      = ⟨(coordMap R.map y).1.succ, (coordMap R.map y).2⟩ := by
  obtain ⟨j, k⟩ := y
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor (c' := c :: rest)
    (concatChainMap (□(c : ℕ)) (⋁rest) L R)
    (ι_appendR R.dims L.dims j (eventInr L.dims R.dims ⟨j, k⟩).1 rfl)
    (isBeadFactor_self (c := c :: rest) (blockIdx R.map.hom j).succ)
    (incl_sq_bead (c' := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R)
      (concatChainMap_inclR (□(c : ℕ)) (⋁rest) L R) j)
    (eventInr L.dims R.dims ⟨j, k⟩).2 k rfl
  refine beadEvent_ext ?_ ?_
  · exact (congrArg Fin.val h1).trans
      (congrArg (fun z : Fin rest.length => (z.succ : ℕ)) (coordMap_fst R.map ⟨j, k⟩).symm)
  · exact h2.trans (congrArg (fun z : beadEvent rest => (z.2 : ℕ)) (coordMap_eq R.map j k)).symm

/-! ### The Segal decomposition of a run

The step index of an event of `⋁dims` under a run `a` is its lexicographic position, twisted
inside each bead by that bead's local run.  Induction on `dims`: the Segal split of `a` is a run of
the head cube concatenated with a run of the tail wedge (`runConcat_runSplit`), the concatenation's
coordinate map is the disjoint union of the two halves', and `runProj` follows the same
recursion. -/

/-- **Segal for a run's linearization.**  A run's step `s` performs the event whose twisted
lexicographic position is `s`. -/
theorem pos_runTwist_coordMap : ∀ (dims : List ℕ+) (a : Run (⋁dims)) (e : beadEvent a.dims),
    (pos (runTwist a (coordMap a.map e)) : ℕ) = (pos e : ℕ) := by
  intro dims
  induction dims with
  | nil =>
      intro a e
      have h0 : a.dims.length = 0 := by
        rw [show a.dims = [] from obj_cube0_dims_nil a.chain]; rfl
      exact absurd e.1.isLt (by omega)
  | cons c rest ih =>
      intro a
      obtain ⟨⟨b₀, b₁⟩, rfl⟩ : ∃ p : Run (□(c : ℕ)) × Run (⋁rest),
          (runConcat (□(c : ℕ)) (⋁rest)).obj p = a :=
        ⟨runSplit (consAltitude c rest) a, runConcat_runSplit _ a⟩
      show ∀ e : beadEvent (b₀.dims ++ b₁.dims),
          (pos (runTwist (dims := c :: rest) ((runConcat (□(c : ℕ)) (⋁rest)).obj (b₀, b₁))
            (coordMap (b := c :: rest)
              (concatChainMap (□(c : ℕ)) (⋁rest) b₀.chain b₁.chain) e)) : ℕ) = (pos e : ℕ)
      refine eventAppendCases (fun x => ?_) (fun y => ?_)
      · rw [coordMap_concat_left c rest b₀.chain b₁.chain x,
          pos_runTwist_cons_zero c rest _ b₀ (runProj_concat_zero c rest b₀ b₁),
          pos_eventInl, pos_ones b₀.ones x]
        exact flatten_run_coordFlip b₀ x
      · rw [coordMap_concat_right c rest b₀.chain b₁.chain y,
          pos_runTwist_cons_succ c rest _ b₁ (runProj_concat_succ c rest b₀ b₁),
          ih b₁ y, pos_eventInr, wedgeDimSum_eq b₀.map]

/-! ### Consequences: the run performs bead `i`'s block in bead `i`'s own order -/

/-- **The step performing a given event**: bead order first, bead `i`'s local run order inside. -/
theorem pos_of_coordMap {dims : List ℕ+} (a : Run (⋁dims)) (e : beadEvent a.dims)
    (i : Fin dims.length) (k : Fin ((dims.get i : ℕ))) (h : coordMap a.map e = ⟨i, k⟩) :
    (pos e : ℕ) = beadStart dims i + (flatten (runProj a i).chain k : ℕ) := by
  rw [← pos_runTwist_coordMap dims a e, h, runTwist_mk, pos_val]

/-- The converse: a run-step is pinned by its twisted lexicographic position. -/
theorem coordMap_run {dims : List ℕ+} (a : Run (⋁dims)) (e : beadEvent a.dims)
    (i : Fin dims.length) (k : Fin ((dims.get i : ℕ)))
    (h : (pos e : ℕ) = beadStart dims i + (flatten (runProj a i).chain k : ℕ)) :
    coordMap a.map e = ⟨i, k⟩ := by
  refine (runTwist a).injective (pos.injective (Fin.ext ?_))
  rw [pos_runTwist_coordMap dims a e, h, runTwist_mk, pos_val]

/-- **Within one bead the run order is that bead's local run order.** -/
theorem pos_lt_iff_flatten_lt {dims : List ℕ+} (a : Run (⋁dims)) (e e' : beadEvent a.dims)
    (i : Fin dims.length) (k k' : Fin ((dims.get i : ℕ)))
    (he : coordMap a.map e = ⟨i, k⟩) (he' : coordMap a.map e' = ⟨i, k'⟩) :
    (pos e : ℕ) < (pos e' : ℕ)
      ↔ flatten (runProj a i).chain k < flatten (runProj a i).chain k' := by
  rw [pos_of_coordMap a e i k he, pos_of_coordMap a e' i k' he', Fin.lt_def]
  omega

/-- **The word a run performs is the concatenation of its per-bead words**: at step
`beadStart dims i + j` it flips bead `i`'s `j`-th axis in bead `i`'s local run order. -/
theorem coordFlip_run_concat {dims : List ℕ+} {n : ℕ} (a : Run (⋁dims)) (χ : ⋁dims ⟶ □n)
    (e : beadEvent a.dims) (i : Fin dims.length) (j : Fin ((dims.get i : ℕ)))
    (h : (pos e : ℕ) = beadStart dims i + (j : ℕ)) :
    coordFlip (a.map ≫ χ) e
      = faceEmb (beadFace χ.hom i) ((flatten (runProj a i).chain).symm j) := by
  rw [coordFlip_comp_apply, coordMap_run a e i ((flatten (runProj a i).chain).symm j)
    (by rw [h, Equiv.apply_symm_apply]), coordFlip_eq]

/-- **Within a bead, the run order is the bead's local run order** — on the run order itself. -/
theorem pos_coordMapEquiv_symm_lt_iff {dims : List ℕ+} (a : Run (⋁dims)) (i : Fin dims.length)
    (k k' : Fin ((dims.get i : ℕ))) :
    (pos ((coordMapEquiv a.map).symm ⟨i, k⟩) : ℕ)
        < (pos ((coordMapEquiv a.map).symm ⟨i, k'⟩) : ℕ)
      ↔ flatten (runProj a i).chain k < flatten (runProj a i).chain k' :=
  pos_lt_iff_flatten_lt a _ _ i k k'
    ((coordMapEquiv a.map).apply_symm_apply _) ((coordMapEquiv a.map).apply_symm_apply _)

end CubeChains
