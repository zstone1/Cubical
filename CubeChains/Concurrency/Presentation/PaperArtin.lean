import CubeChains.Concurrency.Presentation.DirectPresents
import CubeChains.Concurrency.Presentation.ArtinDegreeZero
import CubeChains.Machinery.Presentation.Bijective

/-!
# Concurrency/Presentation/PaperArtin — at the base the paper's polygraph is Artin's

A run of `Zbp` is its strand count, so a cell of `Paper.poly Zbp` is a loop:

    Run Zbp ────────────▸ ℕ                              0-cells
    Cell 1 ──obj──▸ atomComp N k ────▸ Fin (N−1)          1-cells, the generators
    Cell 2 ──obj──▸ pairChain N lo hi ─▸ AtomPair N       2-cells, the relations

and a 2-cell's two climbs are its pair's two alternating words, letter for letter. -/

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains Equiv

namespace ChainCat.Paper

/-! ## A run of the base is its strand count -/

/-- The run on `N` events at the base. -/
def zRun (N : ℕ) : Run Zbp := ⟨zObj (𝟙^N), fun _ hd => List.eq_of_mem_replicate hd⟩

@[simp] theorem dimSum_zRun (N : ℕ) : dimSum (zRun N).dims = N := dimSum_replicate N

/-- **A run of the base is the run on its own events.** -/
theorem eq_zRun (X : Run Zbp) : X = zRun (dimSum X.dims) :=
  Run.ext ((degree_eq_zero_iff_eq_run X.chain).mp ((isRun_iff_degree_eq_zero _).mp X.property))

/-- **…so the 0-cells are the strand counts.** -/
def zRunEquiv : Run Zbp ≃ ℕ where
  toFun X := dimSum X.dims
  invFun := zRun
  left_inv X := (eq_zRun X).symm
  right_inv := dimSum_replicate

theorem zRun_injective : Function.Injective zRun := zRunEquiv.symm.injective

/-- **The run below a chain of the base is the run on the chain's events.** -/
theorem bottomRun_eq_zRun (a : Ch Zbp) : bottomRun a = zRun (dimSum a.dims) :=
  (eq_zRun (bottomRun a)).trans (congrArg zRun (dimSum_eq_of_hom (bottomHom a)))

/-- **…and so is the run at its top.** -/
theorem topRun_eq_zRun (a : Ch Zbp) : topRun a = zRun (dimSum a.dims) :=
  (eq_zRun (topRun a)).trans (congrArg zRun (dimSum_eq_of_hom (topHom a)))

/-- **A cell of the base is a loop** — both its ends are the run on its object's events. -/
theorem Cell.ends_eq {n : ℕ} {X Y : Run Zbp} (α : Cell n X Y) : X = Y :=
  ((α.below.symm.trans (bottomRun_eq_zRun α.obj)).trans (topRun_eq_zRun α.obj).symm).trans α.top

/-- **A cell's object has the events of its ends.** -/
theorem Cell.dimSum_obj {n : ℕ} {X Y : Run Zbp} (α : Cell n X Y) :
    dimSum α.obj.dims = dimSum X.dims :=
  (dimSum_eq_of_hom (bottomHom α.obj)).symm.trans
    (congrArg (fun Z : Run Zbp => dimSum Z.dims) α.below)

/-- **Every run over a chain of the base is the run on its events.** -/
theorem shapeRun_eq_zRun (e : Ch Zbp) {N : ℕ} (σ : ChPerm e N) : shapeRun e σ = zRun N :=
  Run.ext (Obj.eq_of_dims rfl)

/-! ## The 1-cells are the cuts out of the run -/

/-- The 1-cell at the run whose object is the `k`-th atom's shape. -/
def atomGen (N : ℕ) (k : Fin (N - 1)) : Gen (zRun N) (zRun N) where
  obj := zObj (atomComp N k)
  degree_obj := degree_atomComp N k
  below := (bottomRun_eq_zRun _).trans (congrArg zRun (dimSum_atomComp N k))
  top := (topRun_eq_zRun _).trans (congrArg zRun (dimSum_atomComp N k))

/-- **The 1-cells at `N` strands are Artin's `N−1` generators** — a degree-one object above the run
is an atom's cell (`exists_atomComp`), and distinct atoms cut distinct cells (`atomComp_ne`). -/
noncomputable def genArtinEquiv (N : ℕ) : Gen (zRun N) (zRun N) ≃ artinBP.S N :=
  (Equiv.ofBijective (atomGen N)
    ⟨fun i j h => Fin.ext (by
        by_contra hne
        exact atomComp_ne hne (congrArg Cell.obj h)),
      fun α => by
        obtain ⟨k, hk⟩ := exists_atomComp α.hom α.codim_hom
        exact ⟨k, Cell.ext hk.symm⟩⟩).symm

/-! ## The 2-cells are the degree-two objects above it -/

/-- The 2-cell at the run whose object is the chain a pair of cuts share. -/
noncomputable def cellOfPair {N : ℕ} (p : AtomPair N) : Cell 2 (zRun N) (zRun N) where
  obj := p.chain
  degree_obj := degree_pairChain p.ne
  below := (bottomRun_eq_zRun _).trans (congrArg zRun (dimSum_pairChain p.ne))
  top := (topRun_eq_zRun _).trans (congrArg zRun (dimSum_pairChain p.ne))

/-- The two junctions of a 2-cell's object, at its ends' strand count. -/
noncomputable abbrev cellPair {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) : AtomPair N :=
  shapePair (zObj α.obj.dims) (α.dimSum_obj.trans (dimSum_zRun N)) α.degree_obj

/-- **A 2-cell is a pair of cuts** — its object is the chain its two junctions share
(`eq_pairChain`), and the pair chain drops exactly the pair. -/
noncomputable def cellAtomPairEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ AtomPair N where
  toFun := cellPair
  invFun := cellOfPair
  left_inv α := Cell.ext ((eq_pairChain (cellPair α).ne α.degree_obj
    (nonempty_atomComp_lo _ _) (nonempty_atomComp_hi _ _)).symm.trans (eq_zObj α.obj))
  right_inv p := (AtomPair.eq_of_mem
    ((nonempty_atomComp_iff (s := zObj (cellOfPair p).obj.dims) _ _ p.lo).mp
      (nonempty_left_pairChain p.ne))
    ((nonempty_atomComp_iff (s := zObj (cellOfPair p).obj.dims) _ _ p.hi).mp
      (nonempty_right_pairChain p.ne))).symm

/-- **The 2-cells are Artin's relations**, one per pair of cuts. -/
noncomputable def relArtinEquiv (N : ℕ) : Cell 2 (zRun N) (zRun N) ≃ artinBP.Rel N :=
  (cellAtomPairEquiv N).trans (artinRelEquiv N)

/-- **A 2-cell's object is the chain its two cuts share.** -/
theorem obj_eq_pairChain {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    α.obj = (cellAtomPairEquiv N α).chain :=
  (congrArg Cell.obj ((cellAtomPairEquiv N).symm_apply_apply α)).symm

/-- **The two cuts are adjacent exactly when the object has a bead of dimension three** — the two
shapes the species leaves, and a square's beads are edges and pairs. -/
theorem cell_adj_iff {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    ((cellAtomPairEquiv N α).hi : ℕ) = ((cellAtomPairEquiv N α).lo : ℕ) + 1
      ↔ (3 : ℕ+) ∈ α.obj.dims := by
  refine ⟨fun hadj => ?_, fun h3 => ?_⟩
  · obtain ⟨p, q, hd⟩ := dims_pairChain_of_adj (cellAtomPairEquiv N α).ne (Or.inl hadj)
    rw [congrArg (fun c : Ch Zbp => c.dims) (obj_eq_pairChain α), hd]
    simp
  · refine (cellAtomPairEquiv N α).adj_or_apart.resolve_right fun hfar => ?_
    obtain ⟨p, m, q, hd⟩ := dims_pairChain_of_apart (cellAtomPairEquiv N α).ne (Or.inl hfar)
    rw [congrArg (fun c : Ch Zbp => c.dims) (obj_eq_pairChain α), hd] at h3
    exact absurd (le_two_of_mem_two_two_bead h3) (by decide)

/-! ## …word for word -/

/-- The strand-`N` leg of the Artin polygraph, read on the cells of the paper's. -/
noncomputable def artinLegPre (N : ℕ) :
    GenObj (artinBP.P N).Gen ⥤q GenObj (Gen (K := Zbp)) where
  obj _ := runPt (zRun N)
  map g := atomGen N g

/-- **The climb through a pair, read at the base, is the pair's alternating word.** -/
theorem readAt_riseClimb (e : Ch Zbp) {N : ℕ} (hN : dimSum e.dims = N) {i k : Fin (N - 1)}
    (hik : (i : ℕ) ≠ (k : ℕ)) (hi : Nonempty (zObj (atomComp N i) ⟶ zObj e.dims))
    (hk : Nonempty (zObj (atomComp N k) ⟶ zObj e.dims)) :
    ∀ (t : ℕ) (ht : t ≤ cox i k) (hx : shapeRun e (shapeBot (zObj e.dims) hN) = zRun N)
      (hy : shapeRun e (riseElem hN hik hi hk t ht) = zRun N),
      readAt hx hy ((ascPre e N).mapPath (riseClimb hN hik hi hk t ht))
        = (artinLegPre N).mapPath (MonoidPoly.path (rels := ArtinRel N) (artinRise i k t))
  | 0, _, hx, hy => readAt_nil hx hy
  | t + 1, ht, hx, hy => by
      have hm := shapeRun_eq_zRun e (riseElem hN hik hi hk t (Nat.le_of_succ_le ht))
      change readAt hx hy (((ascPre e N).mapPath (riseClimb hN hik hi hk t _)).cons
        (ascGen e (riseAsc hN hik hi hk t ht))) = _
      rw [artinRise_succ, MonoidPoly.path_mul, MonoidPoly.path_of, Quiver.Path.comp_cons,
        Quiver.Path.comp_nil]
      change _ = ((artinLegPre N).mapPath (MonoidPoly.path (rels := ArtinRel N)
        (artinRise i k t))).cons (atomGen N (altIdx i k t))
      rw [← readAt_riseClimb e hN hik hi hk t _ hx hm]
      exact readAt_cons hx hm hy _ (Obj.eq_of_dims rfl)

/-- **A 2-cell's two words are its pair's Artin relation**, spelled in the atoms. -/
theorem src_eq_artinWords {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    (poly Zbp).src (x := runPt (zRun N)) (y := runPt (zRun N)) α
      = (artinLegPre N).mapPath
        (MonoidPoly.path (rels := ArtinRel N) (artinWords (cellAtomPairEquiv N α)).1) := by
  rw [poly_src α (α.dimSum_obj.trans (dimSum_zRun N)), loWord, riseWord, readAt_trans]
  exact readAt_riseClimb α.obj _ _ _ _ _ _ _ _

theorem tgt_eq_artinWords {N : ℕ} (α : Cell 2 (zRun N) (zRun N)) :
    (poly Zbp).tgt (x := runPt (zRun N)) (y := runPt (zRun N)) α
      = (artinLegPre N).mapPath
        (MonoidPoly.path (rels := ArtinRel N) (artinWords (cellAtomPairEquiv N α)).2) := by
  rw [poly_tgt α (α.dimSum_obj.trans (dimSum_zRun N)), hiWord, riseWord, readAt_trans]
  exact readAt_riseClimb α.obj _ _ _ _ _ _ _ _

/-- **The strand-`N` leg of the Artin polygraph is the paper's cells there** — generator to
generator, relation to relation, word for word. -/
noncomputable def artinLegHom (N : ℕ) : artinBP.P N ⟶ poly Zbp where
  pre := artinLegPre N
  two β := (relArtinEquiv N).symm β
  src_two β := (src_eq_artinWords ((relArtinEquiv N).symm β)).trans
    (congrArg (fun γ : artinBP.Rel N => (artinLegPre N).mapPath ((artinBP.P N).src γ))
      ((relArtinEquiv N).apply_symm_apply β))
  tgt_two β := (tgt_eq_artinWords ((relArtinEquiv N).symm β)).trans
    (congrArg (fun γ : artinBP.Rel N => (artinLegPre N).mapPath ((artinBP.P N).tgt γ))
      ((relArtinEquiv N).apply_symm_apply β))

/-- **The Artin polygraph's cells are the paper's at the base**, leg by leg. -/
noncomputable def artinHom : artinBP.poly ⟶ poly Zbp :=
  Polygraph.coprodDescHom artinBP.P artinLegHom

/-- **The 0-cells are the strand counts either way.** -/
noncomputable def artinObjEquiv : GenObj artinBP.poly.Gen ≃ GenObj (Gen (K := Zbp)) where
  toFun A := runPt (zRun A.as.1)
  invFun x := ⟨⟨dimSum x.as.dims, ()⟩⟩
  left_inv A := GenObj.ext (Sigma.ext (dimSum_zRun A.as.1) (by rfl))
  right_inv x := GenObj.ext (eq_zRun x.as).symm

theorem artinHom_obj_bijective : Function.Bijective artinHom.pre.obj :=
  artinObjEquiv.bijective

/-- **The 1-cells at one strand count are its generators, and there are none across counts.** -/
theorem artinHom_map_bijective (A B : GenObj artinBP.poly.Gen) :
    Function.Bijective (artinHom.pre.map : (A ⟶ B) → _) := by
  obtain ⟨⟨M, x⟩⟩ := A
  obtain ⟨⟨M', y⟩⟩ := B
  by_cases hM : M = M'
  · subst hM
    refine ⟨fun e e' h => ?_, fun β => ⟨CoprodGen.mk (genArtinEquiv M β), ?_⟩⟩
    · cases e with
      | mk g =>
          cases e' with
          | mk g' => exact congrArg CoprodGen.mk ((genArtinEquiv M).symm.injective h)
    · exact (genArtinEquiv M).symm_apply_apply β
  · refine ⟨fun e e' h => ?_, fun β => ?_⟩
    · cases e with
      | mk g => exact absurd rfl hM
    · exact absurd (zRun_injective (Cell.ends_eq β)) hM

/-- **…and so are the 2-cells.** -/
theorem artinHom_two_bijective (A B : GenObj artinBP.poly.Gen) :
    Function.Bijective (artinHom.two : artinBP.poly.Rel A B → _) := by
  obtain ⟨⟨M, x⟩⟩ := A
  obtain ⟨⟨M', y⟩⟩ := B
  by_cases hM : M = M'
  · subst hM
    refine ⟨fun γ γ' h => ?_, fun α => ⟨CoprodRel.mk (relArtinEquiv M α), ?_⟩⟩
    · cases γ with
      | @mk _ x₁ y₁ β =>
          cases γ' with
          | @mk _ x₂ y₂ β' =>
              obtain rfl : x₁ = x₂ := GenObj.ext rfl
              obtain rfl : y₁ = y₂ := GenObj.ext rfl
              exact congrArg CoprodRel.mk ((relArtinEquiv M).symm.injective h)
    · exact (relArtinEquiv M).symm_apply_apply α
  · refine ⟨fun γ γ' h => ?_, fun α => ?_⟩
    · cases γ with
      | mk β => exact absurd rfl hM
    · exact absurd (zRun_injective (Cell.ends_eq α)) hM

/-- **At the base the paper's polygraph is Artin's** — cell for cell, word for word. -/
noncomputable def paperArtinIso : poly Zbp ≅ artinBP.poly :=
  (Polygraph.isoOfBijective artinHom artinHom_obj_bijective artinHom_map_bijective
    artinHom_two_bijective).symm

end ChainCat.Paper

namespace ChainCat

/-- **`Ch Zbp[W⁻¹]` *is* the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands.  Two presentations of one polygraph:
`artinBraids.braids` is pure braid theory and `paperPresents` knows no braid, so the equivalence is
all `paperArtinIso` contributes. -/
noncomputable def fullBaseEquiv : FullPosBraidᵒᵖ ≌ ((W Zbp).op).Localization :=
  artinBraids.braids.equiv.symm.trans
    ((Polygraph.presentedEquiv Paper.paperArtinIso).symm.trans (Paper.paperPresents Zbp).equiv)

end ChainCat
