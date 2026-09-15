import CubeChains.Concurrency.Presentation.PairChain
import CubeChains.Concurrency.Presentation.BasePresentation

/-!
# Concurrency/Presentation/ArtinDegreeZero — the pairs of cuts, and Artin's relations

A degree-two shape above a run drops two junctions (`AtomPair`), and Artin's relation equates the
two alternating words of length `cox` they spell, each starting at one cut:

    artinRise i k t = i · k · i ⋯        (t letters, the first `i`)

`ArtinRel` orients a relation by its lower generator first — `artinRise lo hi` in both species. -/

open CategoryTheory Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## Degree zero is the run -/

/-- **A chain has degree zero exactly when it is the run on its own events.** -/
theorem degree_eq_zero_iff_eq_run (d : Ch Zbp) :
    degree d = 0 ↔ d = zObj (𝟙^(dimSum d.dims)) :=
  ⟨eq_zObj_ones_of_degree_eq_zero rfl, fun h => by rw [h]; exact degree_ones _⟩

namespace AtomPair

variable {N : ℕ} (p : AtomPair N)

/-- **Adjacent or apart** — the two Artin species. -/
theorem adj_or_apart : (p.hi : ℕ) = (p.lo : ℕ) + 1 ∨ (p.lo : ℕ) + 1 < (p.hi : ℕ) := by
  have := p.lt; omega

/-- The degree-two shape the two cuts share. -/
noncomputable abbrev chain : Ch Zbp := pairChain N p.lo p.hi p.ne

/-- **A pair is pinned by containing the cuts of another.** -/
theorem eq_of_mem {p q : AtomPair N} (hlo : p.lo = q.lo ∨ p.lo = q.hi)
    (hhi : p.hi = q.lo ∨ p.hi = q.hi) : p = q := by
  have hp := p.lt
  have hq := q.lt
  refine ext' ?_ ?_ <;> rcases hlo with h | h <;> rcases hhi with h' | h' <;>
    simp only [Fin.ext_iff] at h h' ⊢ <;> omega

end AtomPair

/-! ## …and those are the Artin relations -/

/-- **The alternating word through `i` and `k`, the first letter `i`** — `altProd` read in the
opposite monoid, since a word composes source-first. -/
def artinRise {N : ℕ} (i k : Fin (N - 1)) (t : ℕ) : FreeMonoid (Fin (N - 1)) :=
  (altProd (fun s => MulOpposite.op (FreeMonoid.of s)) i k t).unop

theorem artinRise_succ {N : ℕ} (i k : Fin (N - 1)) (t : ℕ) :
    artinRise i k (t + 1) = artinRise i k t * FreeMonoid.of (altIdx i k t) := rfl

/-- The two words of a pair's Artin relation, each the alternating word of length `cox` starting at
one of the two cuts. -/
noncomputable def artinWords {N : ℕ} (p : AtomPair N) :
    FreeMonoid (Fin (N - 1)) × FreeMonoid (Fin (N - 1)) :=
  (artinRise p.lo p.hi (cox p.lo p.hi), artinRise p.hi p.lo (cox p.hi p.lo))

/-- **The species, read once**: a pair apart spells two letters, an adjacent pair three. -/
theorem artinWords_eq {N : ℕ} (p : AtomPair N) :
    ((p.lo : ℕ) + 1 < (p.hi : ℕ) ∧ artinWords p = (FreeMonoid.of p.lo * FreeMonoid.of p.hi,
        FreeMonoid.of p.hi * FreeMonoid.of p.lo))
      ∨ ((p.hi : ℕ) = (p.lo : ℕ) + 1 ∧ artinWords p =
        (FreeMonoid.of p.lo * FreeMonoid.of p.hi * FreeMonoid.of p.lo,
          FreeMonoid.of p.hi * FreeMonoid.of p.lo * FreeMonoid.of p.hi)) := by
  have hc : cox p.hi p.lo = cox p.lo p.hi := cox_comm _ _
  rcases orderOf_adjT_mul_adjT_cases p.ne with ⟨hfar, h⟩ | ⟨hadj, h⟩
  · refine Or.inl ⟨by have := p.lt; omega, ?_⟩
    rw [artinWords, hc, show cox p.lo p.hi = 2 from h]
    simp [artinRise, altProd, altIdx]
  · refine Or.inr ⟨by have := p.lt; omega, ?_⟩
    rw [artinWords, hc, show cox p.lo p.hi = 3 from h]
    simp [artinRise, altProd, altIdx, mul_assoc]

theorem artinRel_artinWords {N : ℕ} (p : AtomPair N) :
    ArtinRel N (artinWords p).1 (artinWords p).2 := by
  rcases artinWords_eq p with ⟨h, hw⟩ | ⟨h, hw⟩ <;> rw [hw]
  · exact ArtinRel.comm p.lo p.hi h
  · exact ArtinRel.braid p.lo p.hi h

theorem artinWords_injective {N : ℕ} : Function.Injective (artinWords (N := N)) := by
  intro p q h
  have key : ∀ r : AtomPair N,
      ∃ t, (artinWords r).1 = FreeMonoid.of r.lo * FreeMonoid.of r.hi * t :=
    fun r => by
      rcases artinWords_eq r with ⟨-, hw⟩ | ⟨-, hw⟩ <;> rw [hw]
      · exact ⟨1, (mul_one _).symm⟩
      · exact ⟨_, rfl⟩
  obtain ⟨t, hp⟩ := key p
  obtain ⟨u, hq⟩ := key q
  have h' := congrArg FreeMonoid.toList (hp.symm.trans ((congrArg Prod.fst h).trans hq))
  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.cons_append, List.nil_append,
    List.cons.injEq] at h'
  exact AtomPair.ext' h'.1 h'.2.1

/-- **Every Artin relation is a pair of cuts'** — the two constructors are the two species. -/
theorem exists_atomPair_of_artinRel {N : ℕ} {x y : FreeMonoid (Fin (N - 1))}
    (h : ArtinRel N x y) : ∃ p : AtomPair N, artinWords p = (x, y) := by
  cases h with
  | comm i j hij =>
      refine ⟨⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩, ?_⟩
      rcases artinWords_eq ⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩ with ⟨-, hw⟩ | ⟨h, -⟩
      · exact hw
      · exact absurd (show (j : ℕ) = (i : ℕ) + 1 from h) (by omega)
  | braid i j hij =>
      refine ⟨⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩, ?_⟩
      rcases artinWords_eq ⟨(i, j), show (i : ℕ) < (j : ℕ) by omega⟩ with ⟨h, -⟩ | ⟨-, hw⟩
      · exact absurd (show (i : ℕ) + 1 < (j : ℕ) from h) (by omega)
      · exact hw

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
