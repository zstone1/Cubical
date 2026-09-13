import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Concurrency.Presentation.BasePresentation

/-!
# Concurrency/Presentation/ArtinDegreeZero — the pairs of cuts, and Artin's relations

`degree` vanishes exactly at a run, so a degree-zero codimension-`k` refinement is a `k`-fold cut
*out of the basepoint*: at `k = 1` the `N−1` atoms, at `k = 2` the unordered pairs of them.

                  cut i                      cut j
    zObj (𝟙^N) ──────────▸ zObj (atomComp N i) ──────▸ pairChain N i j

`AtomPair` is that pair, and `artinWords` the relation `ArtinRel` imposes on it — a hexagon when the
cuts are adjacent, a square when they are apart.  That the degree-two *objects* are these pairs is
`Paper.cellAtomPairEquiv`, and that they present is `artinBP.part`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## Degree zero is the run -/

/-- **A chain has degree zero exactly when it is the run on its own events.** -/
theorem degree_eq_zero_iff_eq_run (d : Ch Zbp) :
    degree d = 0 ↔ d = zObj (𝟙^(dimSum d.dims)) :=
  ⟨eq_zObj_ones_of_degree_eq_zero rfl, fun h => by rw [h]; exact degree_ones _⟩

/-- **The `k`-th atom's cut drops the junction `k+1`.** -/
theorem cutsOf_atomOnes (N : ℕ) (k : Fin (N - 1)) : cutsOf (atomOnes N k) = {(k : ℕ) + 1} := by
  rw [cutsOf, zObj_dims, zObj_dims, boundaries_ones, boundaries_atomComp,
    Finset.sdiff_sdiff_eq_self]
  intro x hx
  have := k.isLt
  rw [Finset.mem_singleton] at hx
  rw [Finset.mem_range]
  omega

/-! ## The greatest cut out of a run

The atoms are the codimension-one cuts, so a pair of events one bead of the target puts together is
a pair the *greatest* crossing inverts — else that atom's own cut would lengthen it past the
capacity.  Two such inversions pin the crossing: the commuting product at cuts apart, the braid word
at consecutive ones. -/

/-- **The greatest crossing inverts every pair one of the target's beads allows.** -/
theorem descent_of_nonempty_atomComp {N : ℕ} {b : Ch Zbp} {f : zObj (𝟙^N) ⟶ b}
    (hf : permLen (crossPerm (dimSum_replicate N) f) = crossCap b.dims) {k : Fin (N - 1)}
    (hk : Nonempty (zObj (atomComp N k) ⟶ b)) :
    crossPerm (dimSum_replicate N) f (adjHi k) < crossPerm (dimSum_replicate N) f (adjLo k) := by
  rcases lt_trichotomy (crossPerm (dimSum_replicate N) f (adjLo k))
      (crossPerm (dimSum_replicate N) f (adjHi k)) with hasc | heq | hdesc
  · obtain ⟨w, hw⟩ := exists_leg k (dimSum_eq_of_onesHom f) hk hasc (u := f) rfl
    have hle := permLen_crossPerm_le_crossCap b.dims (atomOnes N k ≫ w) rfl (dimSum_replicate N)
    rw [crossPerm_comp, hw, crossPerm_atomOnes, permLen_mul_adjT hasc, hf] at hle
    omega
  · exact absurd ((crossPerm (dimSum_replicate N) f).injective heq) (adjLo_ne_adjHi k)
  · exact hdesc

/-! ## The pair of cuts a degree-two shape carries -/

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

/-- The two junctions the cuts drop are junctions of the run. -/
theorem junctions_subset :
    ({(p.lo : ℕ) + 1, (p.hi : ℕ) + 1} : Finset ℕ) ⊆ Finset.range (N + 1) := by
  intro x hx
  have h1 := p.lo.isLt
  have h2 := p.hi.isLt
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Finset.mem_range]
  omega

/-- The degree-two shape the two cuts share. -/
noncomputable abbrev chain : Ch Zbp := pairChain N p.lo p.hi p.ne

end AtomPair

/-- **A set of junctions is what its complement in the run's says** — the cancellation every
`boundaries` comparison runs. -/
theorem eq_of_sdiff_range {M : ℕ} {s t : Finset ℕ} (hs : s ⊆ Finset.range M)
    (ht : t ⊆ Finset.range M) (h : Finset.range M \ s = Finset.range M \ t) : s = t := by
  rw [← Finset.sdiff_sdiff_eq_self hs, ← Finset.sdiff_sdiff_eq_self ht, h]

/-- **A pair of cuts is recovered from the junctions the shape they share drops** — `boundaries` of
the pair chain misses exactly those two. -/
theorem AtomPair.eq_of_boundaries {N : ℕ} {p q : AtomPair N}
    (h : boundaries p.chain.dims = boundaries q.chain.dims) : p = q := by
  have hpair : ({(p.lo : ℕ) + 1, (p.hi : ℕ) + 1} : Finset ℕ)
      = {(q.lo : ℕ) + 1, (q.hi : ℕ) + 1} :=
    eq_of_sdiff_range p.junctions_subset q.junctions_subset
      ((boundaries_pairChain p.ne).symm.trans (h.trans (boundaries_pairChain q.ne)))
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

/-- **The Artin 2-cells at `N` strands are the pairs of cuts.** -/
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

end ChainCat
