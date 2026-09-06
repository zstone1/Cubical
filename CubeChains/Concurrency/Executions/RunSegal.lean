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

A run of `□m` is a chart of an all-edges shape, so the step at which it performs each axis is that
chart's firing order `flatten` (`Concurrency/Grading/CoordFunctor`). -/

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
head one and the tail's, because `pshOfRun` is a `Glue.desc` of the two transposes. -/

/-- The right leg of `pshOfRun` at a cons — the mirror of `pshOfRun_inl`. -/
theorem pshOfRun_inr (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    wedgeInr (□(c : ℕ)) (⋁rest) ≫ pshOfRun (c :: rest) r
      = pshOfRun rest (runSplit (consAltitude c rest) r).2 :=
  wedge2Desc_inr _ _ _

theorem runProj_zero (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    runProj r 0 = (runSplit (consAltitude c rest) r).1 :=
  (congrArg yonedaEquiv (pshOfRun_inl c rest r)).trans (Equiv.apply_symm_apply _ _)

theorem runProj_succ (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) (j : Fin rest.length) :
    runProj r j.succ = runProj (runSplit (consAltitude c rest) r).2 j :=
  congrArg yonedaEquiv
    ((Category.assoc (ιᵂ rest j) (wedgeInr (□(c : ℕ)) (⋁rest)) (pshOfRun (c :: rest) r)).trans
      (congrArg (fun t => ιᵂ rest j ≫ t) (pshOfRun_inr c rest r)))

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

/-- Left half: the first `|L.dims|` beads of the concatenation flip bead `0`'s coordinates. -/
theorem coordMap_concat_left (c : ℕ+) (rest : List ℕ+) (L : Ch (□(c : ℕ))) (R : Ch (⋁rest))
    (i : Fin L.dims.length) (s : Fin (L.dims ++ R.dims).length) (hs : (s : ℕ) = (i : ℕ))
    (k : Fin ((L.dims ++ R.dims).get s : ℕ)) (k' : Fin (L.dims.get i : ℕ))
    (hk : (k' : ℕ) = (k : ℕ)) :
    coordMap (b := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R) ⟨s, k⟩
      = ⟨0, coordFlip L.map ⟨i, k'⟩⟩ := by
  have hsq : (ιᵂ L.dims i ≫ wedgeInclL L.dims R.dims)
        ≫ (concatChainMap (□(c : ℕ)) (⋁rest) L R).hom
      = yoneda.map (beadFace L.map.hom i) ≫ ιᵂ (c :: rest) 0 :=
    incl_sq_beadFace (c' := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R)
      (concatChainMap_inclL (□(c : ℕ)) (⋁rest) L R) i
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor (c' := c :: rest)
    (concatChainMap (□(c : ℕ)) (⋁rest) L R) (ι_appendL R.dims L.dims i s hs)
    (isBeadFactor_self (c := c :: rest) 0) hsq k k' hk
  exact beadEvent_ext (congrArg Fin.val h1)
    (h2.trans (congrArg Fin.val (coordFlip_eq L.map ⟨i, k'⟩).symm))

/-- Right half: the last `|R.dims|` beads of the concatenation are `R`'s, shifted by one bead. -/
theorem coordMap_concat_right (c : ℕ+) (rest : List ℕ+) (L : Ch (□(c : ℕ))) (R : Ch (⋁rest))
    (j : Fin R.dims.length) (s : Fin (L.dims ++ R.dims).length)
    (hs : (s : ℕ) = L.dims.length + (j : ℕ))
    (k : Fin ((L.dims ++ R.dims).get s : ℕ)) (k' : Fin (R.dims.get j : ℕ))
    (hk : (k' : ℕ) = (k : ℕ)) :
    coordMap (b := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R) ⟨s, k⟩
      = ⟨(coordMap R.map ⟨j, k'⟩).1.succ, (coordMap R.map ⟨j, k'⟩).2⟩ := by
  have hsq : (ιᵂ R.dims j ≫ wedgeInclR L.dims R.dims)
        ≫ (concatChainMap (□(c : ℕ)) (⋁rest) L R).hom
      = yoneda.map (blockFace R.map.hom j) ≫ ιᵂ (c :: rest) (blockIdx R.map.hom j).succ :=
    incl_sq_bead (c' := c :: rest) (concatChainMap (□(c : ℕ)) (⋁rest) L R)
      (concatChainMap_inclR (□(c : ℕ)) (⋁rest) L R) j
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor (c' := c :: rest)
    (concatChainMap (□(c : ℕ)) (⋁rest) L R) (ι_appendR R.dims L.dims j s hs)
    (isBeadFactor_self (c := c :: rest) (blockIdx R.map.hom j).succ) hsq k k' hk
  refine beadEvent_ext ?_ ?_
  · exact (congrArg Fin.val h1).trans
      (congrArg (fun z : Fin rest.length => (z.succ : ℕ)) (coordMap_fst R.map ⟨j, k'⟩).symm)
  · exact h2.trans (congrArg (fun z : beadEvent rest => (z.2 : ℕ)) (coordMap_eq R.map j k')).symm

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
      have hnil : a.dims = [] := obj_cube0_dims_nil a.chain
      have h0 : a.dims.length = 0 := by rw [hnil]; rfl
      exact absurd e.1.isLt (by omega)
  | cons c rest ih =>
      intro a
      obtain ⟨⟨b₀, b₁⟩, rfl⟩ : ∃ p : Run (□(c : ℕ)) × Run (⋁rest),
          (runConcat (□(c : ℕ)) (⋁rest)).obj p = a :=
        ⟨runSplit (consAltitude c rest) a, runConcat_runSplit _ a⟩
      rintro ⟨s, k⟩
      have hones : ∀ d ∈ b₀.dims ++ b₁.dims, d = 1 :=
        ((runConcat (□(c : ℕ)) (⋁rest)).obj (b₀, b₁)).ones
      have hklt : (k : ℕ) < ((b₀.dims ++ b₁.dims).get s : ℕ) := k.isLt
      have hslt : (s : ℕ) < (b₀.dims ++ b₁.dims).length := s.isLt
      have hget : (((b₀.dims ++ b₁.dims).get s : ℕ)) = 1 :=
        congrArg PNat.val (hones _ (List.get_mem _ _))
      have hk0 : (k : ℕ) = 0 := by omega
      have hlen : (b₀.dims ++ b₁.dims).length = b₀.dims.length + b₁.dims.length :=
        List.length_append
      have hlen0 : b₀.dims.length = (c : ℕ) := runCubeLength b₀
      have hrhs : (pos (⟨s, k⟩ : beadEvent (b₀.dims ++ b₁.dims)) : ℕ) = (s : ℕ) :=
        pos_ones hones ⟨s, k⟩
      refine Eq.trans ?_ hrhs.symm
      change (pos (runTwist (dims := c :: rest)
            ((runConcat (□(c : ℕ)) (⋁rest)).obj (b₀, b₁))
            (coordMap (b := c :: rest)
              (concatChainMap (□(c : ℕ)) (⋁rest) b₀.chain b₁.chain)
              (⟨s, k⟩ : beadEvent (b₀.dims ++ b₁.dims)))) : ℕ) = (s : ℕ)
      by_cases hlt : (s : ℕ) < b₀.dims.length
      · -- the head cube's block: the first `c` steps are `b₀`'s own
        have hcm : coordMap (b := c :: rest)
              (concatChainMap (□(c : ℕ)) (⋁rest) b₀.chain b₁.chain)
              (⟨s, k⟩ : beadEvent (b₀.dims ++ b₁.dims))
            = ⟨0, coordFlip b₀.map ⟨⟨(s : ℕ), hlt⟩, ⟨0, (b₀.dims.get ⟨(s : ℕ), hlt⟩).pos⟩⟩⟩ :=
          coordMap_concat_left c rest b₀.chain b₁.chain ⟨(s : ℕ), hlt⟩ s rfl k
            ⟨0, (b₀.dims.get ⟨(s : ℕ), hlt⟩).pos⟩ hk0.symm
        rw [hcm, pos_runTwist_cons_zero c rest _ b₀ (runProj_concat_zero c rest b₀ b₁)]
        exact flatten_run_coordFlip b₀ ⟨⟨(s : ℕ), hlt⟩, ⟨0, (b₀.dims.get ⟨(s : ℕ), hlt⟩).pos⟩⟩
      · -- the tail wedge's blocks, shifted by the head cube's `c` steps
        have hjlt : (s : ℕ) - b₀.dims.length < b₁.dims.length := by omega
        have hcm : coordMap (b := c :: rest)
              (concatChainMap (□(c : ℕ)) (⋁rest) b₀.chain b₁.chain)
              (⟨s, k⟩ : beadEvent (b₀.dims ++ b₁.dims))
            = ⟨(coordMap b₁.map
                  ⟨⟨(s : ℕ) - b₀.dims.length, hjlt⟩,
                    ⟨0, (b₁.dims.get ⟨(s : ℕ) - b₀.dims.length, hjlt⟩).pos⟩⟩).1.succ,
               (coordMap b₁.map
                  ⟨⟨(s : ℕ) - b₀.dims.length, hjlt⟩,
                    ⟨0, (b₁.dims.get ⟨(s : ℕ) - b₀.dims.length, hjlt⟩).pos⟩⟩).2⟩ :=
          coordMap_concat_right c rest b₀.chain b₁.chain ⟨(s : ℕ) - b₀.dims.length, hjlt⟩ s
            (show (s : ℕ) = b₀.dims.length + ((s : ℕ) - b₀.dims.length) by omega) k
            ⟨0, (b₁.dims.get ⟨(s : ℕ) - b₀.dims.length, hjlt⟩).pos⟩ hk0.symm
        have hih : (pos (runTwist b₁ (coordMap b₁.map
              ⟨⟨(s : ℕ) - b₀.dims.length, hjlt⟩,
                ⟨0, (b₁.dims.get ⟨(s : ℕ) - b₀.dims.length, hjlt⟩).pos⟩⟩)) : ℕ)
            = (s : ℕ) - b₀.dims.length := by
          have h := ih b₁ ⟨⟨(s : ℕ) - b₀.dims.length, hjlt⟩,
            ⟨0, (b₁.dims.get ⟨(s : ℕ) - b₀.dims.length, hjlt⟩).pos⟩⟩
          rw [pos_ones b₁.ones] at h
          exact h
        rw [hcm, pos_runTwist_cons_succ c rest _ b₁ (runProj_concat_succ c rest b₀ b₁), hih]
        omega

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

/-- **A run performs bead `i` at exactly the steps `[beadStart i, beadStart i + dᵢ)`** — the blocks
are pinned by the bead order alone (`pos_lt_of_fst_lt`). -/
theorem coordMap_fst_run_iff {dims : List ℕ+} (a : Run (⋁dims)) (e : beadEvent a.dims)
    (i : Fin dims.length) :
    (coordMap a.map e).1 = i ↔
      beadStart dims i ≤ (pos e : ℕ) ∧ (pos e : ℕ) < beadStart dims i + (dims.get i : ℕ) := by
  rcases hfe : coordMap a.map e with ⟨i', k'⟩
  have hpos : (pos e : ℕ) = beadStart dims i' + (flatten (runProj a i').chain k' : ℕ) :=
    pos_of_coordMap a e i' k' hfe
  have hlt : ((flatten (runProj a i').chain k' : Fin _) : ℕ) < (dims.get i' : ℕ) :=
    (flatten (runProj a i').chain k').isLt
  constructor
  · intro hi
    obtain rfl : i' = i := hi
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    change i' = i
    by_contra hne
    rcases lt_trichotomy (i' : ℕ) (i : ℕ) with hc | hc | hc
    · have hp := pos_lt_of_fst_lt (dims := dims)
        (e := ⟨i', flatten (runProj a i').chain k'⟩) (e' := ⟨i, ⟨0, (dims.get i).pos⟩⟩) hc
      rw [Fin.lt_def, pos_mk, pos_mk] at hp
      have hz : ((⟨0, (dims.get i).pos⟩ : Fin ((dims.get i : ℕ))) : ℕ) = 0 := rfl
      omega
    · exact hne (Fin.ext hc)
    · have hd : 0 < (dims.get i : ℕ) := (dims.get i).pos
      have hp := pos_lt_of_fst_lt (dims := dims)
        (e := ⟨i, ⟨(dims.get i : ℕ) - 1, by omega⟩⟩)
        (e' := ⟨i', flatten (runProj a i').chain k'⟩) hc
      rw [Fin.lt_def, pos_mk, pos_mk] at hp
      have hz : ((⟨(dims.get i : ℕ) - 1, by omega⟩ : Fin ((dims.get i : ℕ))) : ℕ)
          = (dims.get i : ℕ) - 1 := rfl
      omega

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

/-- **The run order of an event** — `runOrd` with its outer recount dropped. -/
theorem pos_coordMapEquiv_symm {dims : List ℕ+} (a : Run (⋁dims)) (f : beadEvent dims) :
    (pos ((coordMapEquiv a.map).symm f) : ℕ) = (pos (runTwist a f) : ℕ) := by
  have h := pos_runTwist_coordMap dims a ((coordMapEquiv a.map).symm f)
  rw [show coordMap a.map ((coordMapEquiv a.map).symm f) = f from
    (coordMapEquiv a.map).apply_symm_apply f] at h
  exact h.symm

/-- **Within a bead, the run order is the bead's local run order** — on the run order itself. -/
theorem pos_coordMapEquiv_symm_lt_iff {dims : List ℕ+} (a : Run (⋁dims)) (i : Fin dims.length)
    (k k' : Fin ((dims.get i : ℕ))) :
    (pos ((coordMapEquiv a.map).symm ⟨i, k⟩) : ℕ)
        < (pos ((coordMapEquiv a.map).symm ⟨i, k'⟩) : ℕ)
      ↔ flatten (runProj a i).chain k < flatten (runProj a i).chain k' :=
  pos_lt_iff_flatten_lt a _ _ i k k'
    ((coordMapEquiv a.map).apply_symm_apply _) ((coordMapEquiv a.map).apply_symm_apply _)

end CubeChains
