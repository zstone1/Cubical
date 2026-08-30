import CubeChains.Concurrency.Grading.ShuffleHom
import CubeChains.Machinery.Braid.PosGerm

/-!
# Concurrency/Merge/AtomPair — the atom relation, realised by a composable pair of chain maps

`germ_of_atom` cuts the germ relations down to the products `β * adjT i` with
`permLen (β * adjT i) = permLen β + 1`.  Each of those is a two-step factorisation in `Ch Zbp`

  `𝟙^n ⟶ atomComp n i ⟶ [n]`,

the first step the *other* staircase of a square (`cubeReorder 1 1`, which takes the second
coordinate first) spliced at the beads `i, i+1`, the second an ascent of `β` across that one bead.
`crossPerm_cocycle` multiplies them, so the pair is the geometry `PosBraid.liftAtom` asks for.
-/

open CategoryTheory Equiv BPSet CubeChain StdCube

namespace CubeChains

variable {n : ℕ}

/-! ## Blocks of a composition made of edges

`atomComp` is all `1`s but for one `2`, so its `blockOfPos` is the identity shifted down past the
double bead — injective except on the swapped pair. -/

theorem blockOfPos_replicate_one_append (ds : List ℕ) :
    ∀ k p : ℕ, blockOfPos (List.replicate k 1 ++ ds) p
      = if p < k then p else blockOfPos ds (p - k) + k
  | 0, p => by simp
  | k + 1, p => by
      rw [List.replicate_succ, List.cons_append]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · rw [blockOfPos_cons_of_lt _ Nat.one_pos, if_pos (Nat.succ_pos k)]
      · rw [blockOfPos_cons_of_le _ hp, blockOfPos_replicate_one_append ds k (p - 1)]
        rcases Nat.lt_or_ge (p - 1) k with h | h
        · rw [if_pos h, if_pos (by omega)]; omega
        · rw [if_neg (by omega), if_neg (by omega), show p - 1 - k = p - (k + 1) by omega]
          omega

theorem blockOfPos_replicate_one (k p : ℕ) :
    blockOfPos (List.replicate k 1) p = if p < k then p else k := by
  have h := blockOfPos_replicate_one_append [] k p
  rwa [List.append_nil, blockOfPos_nil, Nat.zero_add] at h

/-- **Blocks are consecutive**: the block index rises with the position. -/
theorem blockOfPos_monotone : ∀ ds : List ℕ, Monotone (blockOfPos ds)
  | [] => fun _ _ _ => Nat.le_refl 0
  | d :: ds => fun p q hpq => by
      by_cases hp : p < d
      · rw [blockOfPos_cons_of_lt ds hp]; exact Nat.zero_le _
      · rw [blockOfPos_cons_of_le ds (Nat.not_lt.mp hp),
          blockOfPos_cons_of_le ds (Nat.le_trans (Nat.not_lt.mp hp) hpq)]
        exact Nat.succ_le_succ (blockOfPos_monotone ds (Nat.sub_le_sub_right hpq d))

/-- Inside the bead `d` at cut `k` of `1ᵏ d …` the block index is constant. -/
theorem blockOfPos_replicate_one_append_inside (d : ℕ) (ds : List ℕ) (k : ℕ) {x : ℕ}
    (h1 : k ≤ x) (h2 : x < k + d) : blockOfPos (List.replicate k 1 ++ d :: ds) x = k := by
  rw [blockOfPos_replicate_one_append (d :: ds) k x, if_neg (by omega),
    blockOfPos_cons_of_lt ds (by omega), Nat.zero_add]

/-- Past that bead the block index continues in the tail. -/
theorem blockOfPos_replicate_one_append_after (d : ℕ) (ds : List ℕ) (k : ℕ) {x : ℕ}
    (h : k + d ≤ x) :
    blockOfPos (List.replicate k 1 ++ d :: ds) x = blockOfPos ds (x - k - d) + (k + 1) := by
  rw [blockOfPos_replicate_one_append (d :: ds) k x, if_neg (by omega),
    blockOfPos_cons_of_le ds (by omega)]
  omega

/-- The all-ones composition separates every position. -/
theorem blockOfPos_ones (N : ℕ) {x : ℕ} (hx : x < N) :
    blockOfPos ((𝟙^N).map fun d : ℕ+ => (d : ℕ)) x = x := by
  rw [show ((𝟙^N).map fun d : ℕ+ => (d : ℕ)) = List.replicate N 1 by simp,
    blockOfPos_replicate_one, if_pos hx]

/-! ## The atom composition -/

/-- `1ⁱ 2 1^{n-2-i}` — the composition of `n` whose only non-trivial bead is `{i, i+1}`. -/
def atomComp (n : ℕ) (i : Fin (n - 1)) : List ℕ+ := 𝟙^(i : ℕ) ++ (2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))

/-- `n` as a positive natural — an inhabitant of `Fin (n - 1)` forces `2 ≤ n`. -/
def atomTop (n : ℕ) (i : Fin (n - 1)) : ℕ+ := ⟨n, by have := i.isLt; omega⟩

@[simp] theorem atomTop_coe (n : ℕ) (i : Fin (n - 1)) : ((atomTop n i : ℕ+) : ℕ) = n := rfl

@[simp] theorem dimSum_atomComp (n : ℕ) (i : Fin (n - 1)) : dimSum (atomComp n i) = n := by
  have hi := i.isLt
  have h2 : dimSum ((2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))) = 2 + (n - 2 - (i : ℕ)) := by
    rw [show ((2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))) = [(2 : ℕ+)] ++ 𝟙^(n - 2 - (i : ℕ)) from rfl,
      dimSum_append, dimSum_single, dimSum_replicate]
    rfl
  rw [show atomComp n i = 𝟙^(i : ℕ) ++ (2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ)) from rfl,
    dimSum_append, dimSum_replicate, h2]
  omega

theorem map_atomComp (n : ℕ) (i : Fin (n - 1)) :
    (atomComp n i).map (fun d : ℕ+ => (d : ℕ))
      = List.replicate (i : ℕ) 1 ++ 2 :: List.replicate (n - 2 - (i : ℕ)) 1 := by
  simp [atomComp]

/-- The block index of `atomComp n i`: the identity up to `i`, shifted down past the double bead. -/
theorem blockOfPos_atomComp (n : ℕ) (i : Fin (n - 1)) {x : ℕ} (hx : x < n) :
    blockOfPos ((atomComp n i).map fun d : ℕ+ => (d : ℕ)) x
      = if x ≤ (i : ℕ) then x else x - 1 := by
  have hi := i.isLt
  rw [map_atomComp, blockOfPos_replicate_one_append]
  rcases Nat.lt_or_ge x (i : ℕ) with h | h
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge (x - (i : ℕ)) 2 with h2 | h2
    · rw [blockOfPos_cons_of_lt _ h2]; split_ifs <;> omega
    · rw [blockOfPos_cons_of_le _ h2, blockOfPos_replicate_one, if_pos (by omega)]
      split_ifs <;> omega

/-- **Only the swapped pair shares a bead of `atomComp n i`.** -/
theorem eq_adj_of_blockOfPos_eq (n : ℕ) (i : Fin (n - 1)) {x y : Fin n}
    (h : blockOfPos ((atomComp n i).map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
       = blockOfPos ((atomComp n i).map fun d : ℕ+ => (d : ℕ)) (y : ℕ)) (hlt : x < y) :
    x = adjLo i ∧ y = adjHi i := by
  rw [blockOfPos_atomComp n i x.isLt, blockOfPos_atomComp n i y.isLt] at h
  rw [Fin.lt_def] at hlt
  have key : (x : ℕ) = (i : ℕ) ∧ (y : ℕ) = (i : ℕ) + 1 := by split_ifs at h <;> omega
  exact ⟨Fin.ext (by rw [adjLo_val]; exact key.1), Fin.ext (by rw [adjHi_val]; exact key.2)⟩

/-- An adjacent transposition preserves the beads of `ds` exactly when its pair shares one. -/
theorem adjT_mem_parabolic {ds : List ℕ} {k : Fin (n - 1)}
    (h : blockOfPos ds (k : ℕ) = blockOfPos ds ((k : ℕ) + 1)) : adjT k ∈ parabolic n ds :=
  mem_parabolic_swap.mpr (by rw [adjLo_val, adjHi_val]; exact h)

/-- **`atomComp n i` is refined by every composition merging `i` with `i+1`**: its only
non-singleton bead is that pair. -/
theorem coarsening_of_atomComp {i : Fin (n - 1)} {ds : List ℕ}
    (h : blockOfPos ds (i : ℕ) = blockOfPos ds ((i : ℕ) + 1)) (x y : Fin n)
    (hxy : blockOfPos ((atomComp n i).map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
      = blockOfPos ((atomComp n i).map fun d : ℕ+ => (d : ℕ)) (y : ℕ)) :
    blockOfPos ds (x : ℕ) = blockOfPos ds (y : ℕ) := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_blockOfPos_eq n i hxy hlt
    rw [adjLo_val, adjHi_val]; exact h
  · rfl
  · obtain ⟨rfl, rfl⟩ := eq_adj_of_blockOfPos_eq n i hxy.symm hlt
    rw [adjLo_val, adjHi_val]; exact h.symm

/-- The converse of `permLen_mul_adjT`: a length-additive `β * adjT i` is an ascent of `β`. -/
theorem ascent_of_permLen_mul_adjT {β : Perm (Fin n)} {i : Fin (n - 1)}
    (h : permLen (β * adjT i) = permLen β + 1) : β (adjLo i) < β (adjHi i) := by
  rcases lt_trichotomy (β (adjLo i)) (β (adjHi i)) with h1 | h1 | h1
  · exact h1
  · exact absurd (β.injective h1) (Fin.ne_of_val_ne (by rw [adjLo_val, adjHi_val]; omega))
  · have := permLen_mul_adjT_of_descent h1
    omega

end CubeChains

namespace ChainCat

open CubeChains

variable {a b : List ℕ+} {N : ℕ}

/-! ## Realising a permutation

`exists_crossPerm_eq` classifies the hom-sets of `Ch Zbp` by `IsShuffle`.  Read on `Fin N`, the two
clauses say: the permutation preserves each bead of the target, and it rises inside each bead of the
source.  The all-ones source and the one-bead target are the two degenerate cases. -/

/-- The event bijection named by a permutation of the strands, read back on strands. -/
theorem strand_permOfShuffle_symm (h : dimSum a = dimSum b) (σ : Perm (Fin (dimSum a)))
    (p : beadEvent a) :
    strand (zObj b) ((permOfShuffle h).symm σ p) = finCongr h (σ (strand (zObj a) p)) :=
  Equiv.apply_symm_apply _ _

/-- **A permutation is a crossing permutation `a ⟶ b` exactly when it preserves the beads of `b`
and rises inside the beads of `a`** — `IsShuffle`, read on `Fin N`.  `hcoarse` says `b` is a
coarsening of `a`, which is what turns bead-preservation into bead-monotonicity. -/
theorem exists_crossPermAt_blocks (ha : dimSum a = N) (hb : dimSum b = N) {σ : Perm (Fin N)}
    (hcoarse : ∀ x y : Fin N,
      blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
          = blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (y : ℕ) →
      blockOfPos (b.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
          = blockOfPos (b.map fun d : ℕ+ => (d : ℕ)) (y : ℕ))
    (hpar : σ ∈ parabolic N (b.map fun d : ℕ+ => (d : ℕ)))
    (hin : ∀ x y : Fin N, blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
        = blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (y : ℕ) → x < y → σ x < σ y) :
    ∃ f : zObj a ⟶ zObj b, crossPermAt ha f = σ := by
  have h : dimSum a = dimSum b := ha.trans hb.symm
  set σ' : Perm (Fin (dimSum a)) := ((finCongr ha).permCongr).symm σ
  set X : beadEvent a → Fin N := fun p => finCongr ha (strand (zObj a) p) with hX
  have hblocka : ∀ p : beadEvent a,
      blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) ((X p : Fin N) : ℕ) = (p.1 : ℕ) := fun p =>
    (strandBead_val a (strand (zObj a) p)).symm.trans
      (congrArg Fin.val (strandBead_strand a p))
  have hval : ∀ p : beadEvent a,
      ((strand (zObj b) ((permOfShuffle h).symm σ' p) : Fin (dimSum b)) : ℕ) = (σ (X p) : ℕ) :=
    fun p => congrArg Fin.val (strand_permOfShuffle_symm h σ' p)
  have hblockb : ∀ p : beadEvent a,
      blockOfPos (b.map fun d : ℕ+ => (d : ℕ)) ((σ (X p) : Fin N) : ℕ)
        = ((((permOfShuffle h).symm σ' p).1 : Fin b.length) : ℕ) := fun p => by
    rw [← hval p, ← strandBead_val, strandBead_strand]
  -- a coarsening is monotone, not merely bead-preserving
  have hmono : ∀ x y : Fin N,
      blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
          ≤ blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (y : ℕ) →
      blockOfPos (b.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
          ≤ blockOfPos (b.map fun d : ℕ+ => (d : ℕ)) (y : ℕ) := by
    intro x y hxy
    rcases Nat.lt_or_ge (blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (x : ℕ))
      (blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (y : ℕ)) with hlt | hge
    · refine blockOfPos_monotone _ ?_
      by_contra hc
      exact absurd (blockOfPos_monotone (a.map fun d : ℕ+ => (d : ℕ))
        (Nat.le_of_lt (Nat.not_le.mp hc))) (by omega)
    · exact Nat.le_of_eq (hcoarse x y (by omega))
  have hshuf : IsShuffle ((permOfShuffle h).symm σ') := by
    constructor
    · intro p q hpq
      rw [Fin.le_def, ← hblockb p, ← hblockb q, mem_parabolic.mp hpar (X p),
        mem_parabolic.mp hpar (X q)]
      exact hmono (X p) (X q) (by rw [hblocka p, hblocka q]; exact hpq)
    · intro p q hpq hlt
      refine (strand_lt_iff (zObj b) _ _).mp (Fin.lt_def.mpr ?_)
      rw [hval p, hval q]
      exact Fin.lt_def.mp (hin (X p) (X q) (by rw [hblocka p, hblocka q, hpq])
        (Fin.lt_def.mpr (Fin.lt_def.mp ((strand_lt_iff (zObj a) p q).mpr hlt))))
  obtain ⟨f, hf⟩ := (exists_crossPerm_eq h σ').mpr hshuf
  exact ⟨f, crossPerm_eq_iff_crossPermAt.mp hf⟩

/-- **Out of the all-ones shape**: a permutation of the strands preserving each bead of `b` is a
crossing permutation (`onesHomEquivParabolic`, as an existence statement at `Fin N`). -/
theorem exists_crossPermAt_ones (hb : dimSum b = N) {σ : Perm (Fin N)}
    (hσ : σ ∈ parabolic N (b.map fun d : ℕ+ => (d : ℕ))) :
    ∃ f : zObj (𝟙^N) ⟶ zObj b, crossPermAt (dimSum_replicate N) f = σ := by
  have hsep : ∀ x y : Fin N,
      blockOfPos ((𝟙^N).map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
        = blockOfPos ((𝟙^N).map fun d : ℕ+ => (d : ℕ)) (y : ℕ) → x = y := fun x y hxy =>
    Fin.ext (by rwa [blockOfPos_ones N x.isLt, blockOfPos_ones N y.isLt] at hxy)
  exact exists_crossPermAt_blocks (dimSum_replicate N) hb
    (fun x y hxy => by rw [hsep x y hxy]) hσ
    (fun x y hxy hlt => absurd (hsep x y hxy) (Fin.ne_of_lt hlt))

/-- **Into a single bead**: a permutation increasing on each bead of `a` is a crossing permutation
(`toSingleHomEquiv`, as an existence statement at `Fin N`). -/
theorem exists_crossPermAt_single (ha : dimSum a = N) {m : ℕ+} (hm : (m : ℕ) = N)
    {τ : Perm (Fin N)}
    (hτ : ∀ x y : Fin N, blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (x : ℕ)
        = blockOfPos (a.map fun d : ℕ+ => (d : ℕ)) (y : ℕ) → x < y → τ x < τ y) :
    ∃ g : zObj a ⟶ zObj [m], crossPermAt ha g = τ := by
  have hzero : ∀ z : Fin N, blockOfPos ([m].map fun d : ℕ+ => (d : ℕ)) (z : ℕ) = 0 := fun z =>
    blockOfPos_cons_of_lt _ (Nat.lt_of_lt_of_eq z.isLt hm.symm)
  exact exists_crossPermAt_blocks ha ((dimSum_single m).trans hm)
    (fun x y _ => by rw [hzero x, hzero y]) (fun z => by rw [hzero, hzero]) hτ

/-- **Out of an atom's target**: a permutation preserving every bead of `c` and rising across the
atom's own pair `{i, i+1}` is a crossing permutation `atomComp n i ⟶ c`.  The bead clause of
`IsShuffle` has only that one pair to check. -/
theorem exists_crossPermAt_atomComp {c : List ℕ+} {N : ℕ} (hc : dimSum c = N) {i : Fin (N - 1)}
    (hi : blockOfPos (c.map fun d : ℕ+ => (d : ℕ)) (i : ℕ)
      = blockOfPos (c.map fun d : ℕ+ => (d : ℕ)) ((i : ℕ) + 1))
    {σ : Perm (Fin N)} (hpar : σ ∈ parabolic N (c.map fun d : ℕ+ => (d : ℕ)))
    (hasc : σ (adjLo i) < σ (adjHi i)) :
    ∃ u : zObj (atomComp N i) ⟶ zObj c, crossPermAt (dimSum_atomComp N i) u = σ :=
  exists_crossPermAt_blocks (dimSum_atomComp N i) hc (coarsening_of_atomComp hi) hpar
    fun x y hxy hlt => by
      obtain ⟨rfl, rfl⟩ := eq_adj_of_blockOfPos_eq N i hxy hlt
      exact hasc

/-! ## The atom

`cubeReorder 1 1` is the *other* wedge-to-tensor comparison of a square: it sends the beads to the
opposite coordinate blocks, so they cross.  Spliced at a cut (`atomHom`) it exchanges exactly the
two strands there and fixes the rest — an adjacent transposition, and by the same token not a
merge. -/

/-- **The reordering staircase swaps its two strands.** -/
theorem pos_coordMap_pairMerge_cubeReorder (y : beadEvent [1, 1]) :
    (pos (coordMap (pairMerge 1 1 (cubeReorder 1 1)) y) : ℕ) = 1 - (pos y : ℕ) := by
  obtain ⟨i, k⟩ := y
  have hi : (i : ℕ) < 2 := by simp
  rcases Nat.lt_or_ge (i : ℕ) 1 with h | h
  · obtain rfl : i = 0 := Fin.ext (by simp; omega)
    have hk : (k : ℕ) = 0 := Nat.lt_one_iff.mp k.isLt
    rw [coordMap_pairMerge_zero, pos_cons_zero, pos_cons_zero, hk]
    exact (faceEmb_cubeReorder_inl _ _ k).trans (by rw [hk]; rfl)
  · obtain rfl : i = 1 := Fin.ext (by simp; omega)
    have hk : (k : ℕ) = 0 := Nat.lt_one_iff.mp k.isLt
    rw [coordMap_pairMerge_one, pos_cons_zero, pos_pair_one, hk]
    exact (faceEmb_cubeReorder_inr _ _ k).trans (by rw [hk]; rfl)

/-- **The reordering splice is an adjacent transposition** of the strands at the cut. -/
theorem pos_coordMap_splicePhi_cubeReorder (l r : List ℕ+) (e : beadEvent (l ++ 1 :: 1 :: r))
    {t : ℕ} (ht : (pos e : ℕ) = t) :
    (pos (coordMap (splicePhi l r 1 1 (cubeReorder 1 1)) e) : ℕ)
      = if t = dimSum l then dimSum l + 1 else if t = dimSum l + 1 then dimSum l else t := by
  rw [pos_coordMap_splicePhi (g := fun s => 1 - s) l r 1 1 _
    pos_coordMap_pairMerge_cubeReorder e ht]
  simp only [PNat.one_coe]
  split_ifs <;> omega

/-- **An atom swaps its two strands** — the crossing permutation of `atomHom` is the adjacent
transposition at the cut.  Stated for an arbitrary source word so the caller can supply the list
identity. -/
theorem exists_crossPermAt_swap {d : List ℕ+} {N : ℕ} (l r : List ℕ+)
    (hd : d = l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) (h : dimSum d = N) {x y : Fin N}
    (hx : (x : ℕ) = dimSum l) (hy : (y : ℕ) = dimSum l + 1) :
    ∃ f : zObj d ⟶ zObj (l ++ (2 : ℕ+) :: r), crossPermAt h f = Equiv.swap x y := by
  subst hd
  refine ⟨atomHom l r, Equiv.ext fun z => Fin.ext ?_⟩
  obtain ⟨e, he⟩ :=
    (strand (zObj (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r))).surjective ((finCongr h).symm z)
  have hz : (pos e : ℕ) = (z : ℕ) := (strand_val _ e).symm.trans (congrArg Fin.val he)
  have hval : (crossPermAt h (atomHom l r) z : ℕ)
      = (pos (coordMap (splicePhi l r 1 1 (cubeReorder 1 1)) e) : ℕ) := by
    -- `exact`, not `rw`: `dimSum (zObj d).dims` and `dimSum d` are `rfl`-equal but `kabstract`
    -- will not unfold `zObj` to see it
    have hs := crossPerm_strand (atomHom l r) e
    rw [he] at hs
    exact hs
  refine hval.trans ?_
  rw [pos_coordMap_splicePhi_cubeReorder l r e hz]
  by_cases h1 : (z : ℕ) = dimSum l
  · rw [if_pos h1, show z = x from Fin.ext (h1.trans hx.symm), Equiv.swap_apply_left]
    exact hy.symm
  · rw [if_neg h1]
    by_cases h2 : (z : ℕ) = dimSum l + 1
    · rw [if_pos h2, show z = y from Fin.ext (h2.trans hy.symm), Equiv.swap_apply_right]
      exact hx.symm
    · rw [if_neg h2, Equiv.swap_apply_of_ne_of_ne
        (fun hzx => h1 (by rw [hzx, hx])) (fun hzy => h2 (by rw [hzy, hy]))]

/-- **The atom is not a merge** — the two comparisons `cubeMerge`/`cubeReorder` differ, and the
event at the cut is where. -/
theorem not_W_atomHom (l r : List ℕ+) : ¬ W Zbp (atomHom l r) := fun hW => by
  set e : beadEvent (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) :=
    eventInr l ((1 : ℕ+) :: (1 : ℕ+) :: r) ⟨0, 0⟩ with he
  have ht : (pos e : ℕ) = dimSum l := by
    rw [he, pos_eventInr]
    simpa using pos_cons_zero (1 : ℕ+) ((1 : ℕ+) :: r) 0
  have hswap : (pos (coordMap (splicePhi l r 1 1 (cubeReorder 1 1)) e) : ℕ) = dimSum l + 1 := by
    rw [pos_coordMap_splicePhi_cubeReorder l r e ht, if_pos rfl]
  -- `have`, not `rw`: `(zObj d).dims` and `d` are `rfl`-equal but `kabstract` will not unfold
  have h : (pos (coordMap (splicePhi l r 1 1 (cubeReorder 1 1)) e) : ℕ) = (pos e : ℕ) :=
    (W_iff_pos (atomHom l r)).mp hW e
  omega

/-- **The first step**: `adjT i` is the reordering staircase spliced at the beads `i, i+1` of the
all-ones chain. -/
theorem exists_crossPermAt_adjT (n : ℕ) (i : Fin (n - 1)) :
    ∃ f : zObj (𝟙^n) ⟶ zObj (atomComp n i), crossPermAt (dimSum_replicate n) f = adjT i := by
  have hi := i.isLt
  have hcons : ∀ k : ℕ, (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^k = 𝟙^(k + 2) := fun k => by
    rw [show k + 2 = k + 1 + 1 from rfl, List.replicate_succ, List.replicate_succ]
  have hsrc : 𝟙^(i : ℕ) ++ (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ)) = 𝟙^n := by
    rw [hcons, ← List.replicate_add]
    congr 1
    omega
  exact exists_crossPermAt_swap (d := 𝟙^n) (𝟙^(i : ℕ)) (𝟙^(n - 2 - (i : ℕ))) hsrc.symm
    (dimSum_replicate n) (x := adjLo i) (y := adjHi i)
    (by rw [adjLo_val, dimSum_replicate]) (by rw [adjHi_val, dimSum_replicate])

/-- **The second step**: a `β` that is an ascent across the one double bead sorts `atomComp n i`
into a single cube. -/
theorem exists_crossPermAt_of_ascent {n : ℕ} {i : Fin (n - 1)} {β : Perm (Fin n)}
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ g : zObj (atomComp n i) ⟶ zObj [atomTop n i], crossPermAt (dimSum_atomComp n i) g = β :=
  exists_crossPermAt_single (dimSum_atomComp n i) (atomTop_coe n i) fun _ _ hxy hlt => by
    obtain ⟨rfl, rfl⟩ := eq_adj_of_blockOfPos_eq n i hxy hlt
    exact ascent_of_permLen_mul_adjT hβ

/-- **The atom relation, geometrically**: every length-additive `β * adjT i` is the crossing
permutation of a composable pair through `atomComp n i` — the hypothesis of `PosBraid.liftAtom`,
realised in `Ch Zbp`. -/
theorem exists_atom_pair {n : ℕ} (i : Fin (n - 1)) {β : Perm (Fin n)}
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ (f : zObj (𝟙^n) ⟶ zObj (atomComp n i)) (g : zObj (atomComp n i) ⟶ zObj [atomTop n i]),
      crossPermAt (dimSum_replicate n) f = adjT i ∧
      crossPermAt (dimSum_atomComp n i) g = β ∧
      crossPermAt (dimSum_replicate n) (f ≫ g) = β * adjT i := by
  obtain ⟨f, hf⟩ := exists_crossPermAt_adjT n i
  obtain ⟨g, hg⟩ := exists_crossPermAt_of_ascent hβ
  exact ⟨f, g, hf, hg, by
    rw [crossPermAt_comp (dimSum_replicate n) (dimSum_atomComp n i), hf, hg]⟩

end ChainCat
