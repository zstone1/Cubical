import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Concurrency.Presentation.BasePresentation

/-!
# Concurrency/Presentation/ArtinDegreeZero — the cells of degree zero are Artin's

`degree` vanishes exactly at a run, so a degree-zero codimension-`k` refinement is a `k`-fold cut
*out of the basepoint*: at `k = 1` the `N−1` atoms, at `k = 2` the unordered pairs of them, each
imposing the Artin relation of its species — a hexagon for adjacent cuts, a square for apart ones.

                  cut i                      cut j
    zObj (𝟙^N) ──────────▸ zObj (atomComp N i) ──────▸ pairChain N i j

That these cells *present* the localization is `artinBP.part`, and nothing here.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## Degree zero is the run -/

/-- **A chain has degree zero exactly when it is the run on its own events.** -/
theorem degree_eq_zero_iff_eq_run (d : Ch Zbp) :
    degree d = 0 ↔ d = zObj (𝟙^(dimSum d.dims)) := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact degree_ones _⟩
  have hall : ∀ c ∈ d.dims, c = (1 : ℕ+) := (degree_eq_zero_iff d).mp h
  have hrep : d.dims = 𝟙^(d.dims.length) := List.eq_replicate_of_mem hall
  have hlen : dimSum d.dims = d.dims.length := by
    conv_lhs => rw [hrep]
    exact dimSum_replicate _
  exact Obj.eq_of_dims (by rw [zObj_dims, hlen, ← hrep])

/-! ## The codimension-one cuts out of a run -/

/-- **A codimension-one cut out of the run on `N` events that crosses.** -/
structure RunAtom (N : ℕ) where
  /-- the shape it cuts into -/
  tgt : Ch Zbp
  /-- the cut -/
  cut : zObj (𝟙^N) ⟶ tgt
  /-- …of codimension one -/
  codim_cut : codim cut = 1
  /-- …and not a merge -/
  not_merge : ¬ W Zbp cut

/-- The `k`-th atom, as a cut out of the run. -/
def runAtom (N : ℕ) (k : Fin (N - 1)) : RunAtom N :=
  ⟨zObj (atomComp N k), atomOnes N k, codim_atomOnes N k, not_W_atomOnes N k⟩

/-- **The codimension-one cuts out of the run are its `N−1` atoms** — `exists_atomComp` names the
shape, `eq_atomOnes` the cut, and `atomComp_ne` keeps the indices apart. -/
noncomputable def runAtomEquiv (N : ℕ) : Fin (N - 1) ≃ RunAtom N :=
  Equiv.ofBijective (runAtom N)
    ⟨fun i j h => Fin.ext (by
        by_contra hne
        exact atomComp_ne hne (congrArg RunAtom.tgt h)),
      fun a => by
        obtain ⟨t, c, hc, hm⟩ := a
        obtain ⟨k, rfl⟩ := exists_atomComp c hc
        obtain rfl := eq_atomOnes hm
        exact ⟨k, rfl⟩⟩

@[simp] theorem runAtomEquiv_apply (N : ℕ) (k : Fin (N - 1)) : runAtomEquiv N k = runAtom N k := rfl

/-- The atom loop a cut out of the run performs. -/
noncomputable def runAtomLoop {N : ℕ} (a : RunAtom N) :
    @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
  atomLoop N ((runAtomEquiv N).symm a)

@[simp] theorem runAtomLoop_runAtom (N : ℕ) (k : Fin (N - 1)) :
    runAtomLoop (runAtom N k) = atomLoop N k := by
  rw [runAtomLoop, show (runAtomEquiv N).symm (runAtom N k) = k from
    (runAtomEquiv N).symm_apply_apply k]

/-! ## The codimension-two shapes above a run -/

/-- **A degree-two shape on `N` events** — the codimension-two refinements out of the run are the
refinements *into* it. -/
structure RunSquare (N : ℕ) where
  /-- the shape -/
  apex : Ch Zbp
  /-- …on `N` events -/
  strands : dimSum apex.dims = N
  /-- …of degree two -/
  degree_apex : degree apex = 2

/-- An ordered pair of distinct cuts. -/
def AtomPair (N : ℕ) : Type := {p : Fin (N - 1) × Fin (N - 1) // (p.1 : ℕ) < (p.2 : ℕ)}

namespace AtomPair

variable {N : ℕ} (p : AtomPair N)

/-- the lower cut -/
abbrev lo : Fin (N - 1) := p.1.1

/-- the upper cut -/
abbrev hi : Fin (N - 1) := p.1.2

theorem lt : (p.lo : ℕ) < (p.hi : ℕ) := p.2

theorem ne : (p.lo : ℕ) ≠ (p.hi : ℕ) := Nat.ne_of_lt p.2

/-- **Adjacent or apart** — the two Artin species. -/
theorem adj_or_apart : (p.hi : ℕ) = (p.lo : ℕ) + 1 ∨ (p.lo : ℕ) + 1 < (p.hi : ℕ) := by
  have := p.lt; omega

theorem ext' {p q : AtomPair N} (hlo : p.lo = q.lo) (hhi : p.hi = q.hi) : p = q :=
  Subtype.ext (Prod.ext hlo hhi)

end AtomPair

/-- The degree-two shape a pair of cuts share. -/
noncomputable def runSquare {N : ℕ} (p : AtomPair N) : RunSquare N :=
  ⟨pairChain N p.lo p.hi p.ne, dimSum_pairChain p.ne, degree_pairChain p.ne⟩

theorem codim_runMerge_of_degree {N : ℕ} (s : RunSquare N) :
    codim (runMerge s.apex s.strands) = 2 := by
  rw [codim, s.degree_apex, degree_ones]

/-- **A pair of cuts is recovered from the shape they share** — `boundaries` of the pair chain
misses exactly the two junctions the cuts drop. -/
theorem runSquare_injective {N : ℕ} : Function.Injective (runSquare (N := N)) := by
  intro p q h
  have hb : Finset.range (N + 1) \ {(p.lo : ℕ) + 1, (p.hi : ℕ) + 1}
      = Finset.range (N + 1) \ {(q.lo : ℕ) + 1, (q.hi : ℕ) + 1} :=
    (boundaries_pairChain p.ne).symm.trans
      ((congrArg (fun s : RunSquare N => boundaries s.apex.dims) h).trans
        (boundaries_pairChain q.ne))
  have hsub : ∀ r : AtomPair N,
      ({(r.lo : ℕ) + 1, (r.hi : ℕ) + 1} : Finset ℕ) ⊆ Finset.range (N + 1) := by
    intro r x hx
    have h1 := r.lo.isLt
    have h2 := r.hi.isLt
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    omega
  have hpair : ({(p.lo : ℕ) + 1, (p.hi : ℕ) + 1} : Finset ℕ)
      = {(q.lo : ℕ) + 1, (q.hi : ℕ) + 1} := by
    rw [← Finset.sdiff_sdiff_eq_self (hsub p), ← Finset.sdiff_sdiff_eq_self (hsub q), hb]
  have hmem : ∀ x : ℕ, (x ∈ ({(p.lo : ℕ) + 1, (p.hi : ℕ) + 1} : Finset ℕ))
      ↔ (x ∈ ({(q.lo : ℕ) + 1, (q.hi : ℕ) + 1} : Finset ℕ)) := fun x => by rw [hpair]
  have h1 := (hmem ((p.lo : ℕ) + 1)).mp (by simp)
  have h2 := (hmem ((p.hi : ℕ) + 1)).mp (by simp)
  have h3 := (hmem ((q.lo : ℕ) + 1)).mpr (by simp)
  have h4 := (hmem ((q.hi : ℕ) + 1)).mpr (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
  have hp := p.lt
  have hq := q.lt
  exact AtomPair.ext' (Fin.ext (by omega)) (Fin.ext (by omega))

/-- **The degree-two shapes on `N` events are the pairs of cuts** — `exists_atomPair_of_codim_two`
names the pair, and `eq_pairChain` says the shape is theirs. -/
noncomputable def runSquareEquiv (N : ℕ) : AtomPair N ≃ RunSquare N :=
  Equiv.ofBijective runSquare
    ⟨runSquare_injective, fun s => by
      obtain ⟨d, hd, hdeg⟩ := s
      obtain ⟨i, j, hij, hcount⟩ :=
        exists_atomPair_of_codim_two (runMerge d hd) (codim_runMerge_of_degree ⟨d, hd, hdeg⟩)
      obtain rfl := eq_pairChain (Nat.ne_of_lt hij) hdeg ((hcount i).mpr (Or.inl rfl))
        ((hcount j).mpr (Or.inr rfl))
      exact ⟨⟨(i, j), hij⟩, rfl⟩⟩

/-- **Each degree-two shape imposes the Artin relation of its species** — the hexagon when its two
cuts are adjacent, the square when they are apart. -/
theorem runSquare_artin {N : ℕ} (p : AtomPair N) :
    ((p.hi : ℕ) = (p.lo : ℕ) + 1 ∧
        atomLoop N p.lo ≫ atomLoop N p.hi ≫ atomLoop N p.lo
          = atomLoop N p.hi ≫ atomLoop N p.lo ≫ atomLoop N p.hi)
      ∨ ((p.lo : ℕ) + 1 < (p.hi : ℕ) ∧
        atomLoop N p.lo ≫ atomLoop N p.hi = atomLoop N p.hi ≫ atomLoop N p.lo) :=
  p.adj_or_apart.imp (fun h => ⟨h, atomLoop_braid h⟩) fun h => ⟨h, atomLoop_comm h⟩

/-! ## …and those are the Artin relations

A 2-cell of `artinBP` is a pair of words its relation family relates, and `ArtinRel` relates exactly
one pair per pair of cuts: the hexagon when they are adjacent, the square when they are not. -/

/-- The two words of a pair's Artin relation — a hexagon when the cuts are adjacent, a square when
they are apart. -/
def artinWords {N : ℕ} (p : AtomPair N) :
    FreeMonoid (Fin (N - 1)) × FreeMonoid (Fin (N - 1)) :=
  if (p.hi : ℕ) = (p.lo : ℕ) + 1 then ([p.lo, p.hi, p.lo], [p.hi, p.lo, p.hi])
  else ([p.lo, p.hi], [p.hi, p.lo])

theorem artinRel_artinWords {N : ℕ} (p : AtomPair N) :
    ArtinRel N (artinWords p).1 (artinWords p).2 := by
  unfold artinWords
  split
  · next h => exact ArtinRel.braid p.lo p.hi h
  · next h => exact ArtinRel.comm p.lo p.hi (by have := p.lt; omega)

/-- Both species start with the two cuts in order, which is what pins the pair. -/
theorem artinWords_cons {N : ℕ} (p : AtomPair N) :
    ∃ t, (artinWords p).1 = p.lo :: p.hi :: t := by
  unfold artinWords
  split
  · exact ⟨[p.lo], rfl⟩
  · exact ⟨[], rfl⟩

theorem artinWords_injective {N : ℕ} : Function.Injective (artinWords (N := N)) := by
  intro p q h
  obtain ⟨t, hp⟩ := artinWords_cons p
  obtain ⟨u, hq⟩ := artinWords_cons q
  have h' : p.lo :: p.hi :: t = q.lo :: q.hi :: u :=
    hp.symm.trans ((congrArg Prod.fst h).trans hq)
  injection h' with ha hb
  injection hb with hc _hd
  exact AtomPair.ext' ha hc

/-- **Every Artin relation is a pair of cuts'** — the two constructors are the two species. -/
theorem exists_atomPair_of_artinRel {N : ℕ} {x y : FreeMonoid (Fin (N - 1))}
    (h : ArtinRel N x y) : ∃ p : AtomPair N, artinWords p = (x, y) := by
  cases h with
  | comm i j hij =>
      refine ⟨⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩, ?_⟩
      unfold artinWords
      rw [if_neg (show ¬ ((j : ℕ) = (i : ℕ) + 1) by omega)]
      rfl
  | braid i j hij =>
      refine ⟨⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩, ?_⟩
      unfold artinWords
      rw [if_pos (show (j : ℕ) = (i : ℕ) + 1 from hij)]
      rfl

/-- The Artin 2-cell of a pair of cuts. -/
noncomputable def artinCell {N : ℕ} (p : AtomPair N) : artinBP.Rel N :=
  ⟨(MonoidPoly.path (artinWords p).1, MonoidPoly.path (artinWords p).2), by
    rw [MonoidPoly.word_path, MonoidPoly.word_path]; exact artinRel_artinWords p⟩

/-- **The Artin 2-cells at `N` strands are the pairs of cuts** — hence, by `runSquareEquiv`, the
degree-two shapes on `N` events. -/
noncomputable def artinRelEquiv (N : ℕ) : AtomPair N ≃ artinBP.Rel N :=
  Equiv.ofBijective artinCell
    ⟨fun p q h => artinWords_injective (Prod.ext
        ((MonoidPoly.word_path (artinWords p).1).symm.trans
          ((congrArg (fun α : artinBP.Rel N => MonoidPoly.word α.1.1) h).trans
            (MonoidPoly.word_path (artinWords q).1)))
        ((MonoidPoly.word_path (artinWords p).2).symm.trans
          ((congrArg (fun α : artinBP.Rel N => MonoidPoly.word α.1.2) h).trans
            (MonoidPoly.word_path (artinWords q).2)))),
      fun α => by
        obtain ⟨p, hp⟩ := exists_atomPair_of_artinRel α.2
        refine ⟨p, Subtype.ext (Prod.ext ?_ ?_)⟩
        · exact (congrArg MonoidPoly.path (congrArg Prod.fst hp)).trans
            (MonoidPoly.path_word α.1.1)
        · exact (congrArg MonoidPoly.path (congrArg Prod.snd hp)).trans
            (MonoidPoly.path_word α.1.2)⟩

/-- **The degree-two cells and the Artin relations are one family.** -/
noncomputable def runSquareArtinEquiv (N : ℕ) : RunSquare N ≃ artinBP.Rel N :=
  (runSquareEquiv N).symm.trans (artinRelEquiv N)

/-! ## The degree-zero presentation

1-cells the cuts out of each run, 2-cells the degree-two shapes above it — the Artin presentation,
relabelled along the two bijections.  That those cells *present* is `artinBP.part`, i.e.
Artin-from-Garside; dropping the surplus relations of a contracted cut presentation is a different
move, and is not this one. -/

/-- The source word of a degree-two shape: its pair's Artin relation, spelled in the cuts. -/
noncomputable def runSrc (N : ℕ) (s : RunSquare N) :
    Quiver.Path (Polygraph.loopPt (RunAtom N)) (Polygraph.loopPt (RunAtom N)) :=
  (Polygraph.loopPre (runAtomEquiv N)).mapPath (artinBP.src N (runSquareArtinEquiv N s))

/-- …and its target word. -/
noncomputable def runTgt (N : ℕ) (s : RunSquare N) :
    Quiver.Path (Polygraph.loopPt (RunAtom N)) (Polygraph.loopPt (RunAtom N)) :=
  (Polygraph.loopPre (runAtomEquiv N)).mapPath (artinBP.tgt N (runSquareArtinEquiv N s))

/-- **The degree-zero polygraph at `N` strands *is* the Artin one** — generator to generator,
relation to relation. -/
noncomputable def runRelabel (N : ℕ) :
    Polygraph.loopPoly (RunAtom N) (RunSquare N) (runSrc N) (runTgt N) ≅ artinBP.P N :=
  Polygraph.loopRelabel (runAtomEquiv N).symm (runAtomEquiv N)
    (runAtomEquiv N).apply_symm_apply (runAtomEquiv N).symm_apply_apply
    (runSquareArtinEquiv N) (runSquareArtinEquiv N).symm
    (runSquareArtinEquiv N).symm_apply_apply (runSquareArtinEquiv N).apply_symm_apply
    (artinBP.src N) (artinBP.tgt N)

/-- **The degree-zero presentation of `Ch(Z)[W⁻¹]`.** -/
noncomputable def runBP : BraidPresentation where
  Gen := RunAtom
  Rel := RunSquare
  src := runSrc
  tgt := runTgt
  part N := (artinBP.part N).ofPolyIso (runRelabel N).symm

@[simp] theorem runBP_braid {N : ℕ} (a : runBP.S N) :
    runBP.braid a = artinBP.braid ((runAtomEquiv N).symm a) := rfl

theorem runBP_perm {N : ℕ} (a : runBP.S N) : runBP.perm a = adjT ((runAtomEquiv N).symm a) := by
  rw [BraidPresentation.perm, runBP_braid, artinBP_braid, posPermHom_posPerm]

theorem runBP_bySimples : runBP.BySimples := fun _ a => by
  rw [runBP_braid, runBP_perm, artinBP_braid]

/-- **A degree-zero 1-cell names the atom loop its cut performs.** -/
theorem runBase_arrow_atomLoop (N : ℕ) (a : RunAtom N) :
    runBP.base.arrow (runBP.gen a) = runAtomLoop a :=
  (runBP.base_arrow_of_simple runBP_bySimples a).trans
    (by rw [runBP_perm, runLoop_adjT]; rfl)

end ChainCat
