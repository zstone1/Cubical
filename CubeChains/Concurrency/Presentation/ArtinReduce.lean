import CubeChains.Concurrency.Presentation.ArtinDegreeZero
import CubeChains.Machinery.Presentation.Reduce

/-!
# Concurrency/Presentation/ArtinReduce — the germ presentation reduced to the atoms

`germBP` carries one 1-cell per simple; only the `N−1` atoms are needed, since a loop at the run is
the word its crossing permutation spells (`exists_atomWord`), one atom per inversion.

    germBP.gen σ  ═══▸  atomLoop N k₁ ≫ ⋯ ≫ atomLoop N k_(permLen σ)

`Machinery/Presentation/Reduce` drops the rest and keeps every 2-cell with its letters substituted;
those 2-cells are the germ's, **not** Artin's — for the latter see
`Concurrency/Presentation/ArtinDegreeZero`.
-/

open CategoryTheory Opposite BPSet CubeChains

namespace ChainCat

/-! ## The atoms among the germ's 1-cells

A 1-cell of `germBP.poly` lies in one strand count, so it is a permutation there; its 0-cells carry
`Unit`, whose eta makes source and target the same 0-cell with no transport. -/

/-- The permutation a germ 1-cell performs. -/
def germPerm {a b : germBP.poly.V} (e : germBP.poly.Gen a b) : Equiv.Perm (Fin a.1) :=
  match e with
  | .mk s => s

@[simp] theorem germPerm_gen {N : ℕ} (s : germBP.S N) : germPerm (germBP.gen s) = s := rfl

/-- **The 1-cells to keep**: those performing an adjacent transposition. -/
def GermAtom {a b : germBP.poly.V} (e : germBP.poly.Gen a b) : Prop :=
  ∃ k : Fin (a.1 - 1), germPerm e = adjT k

theorem germAtom_gen_adjT {N : ℕ} (k : Fin (N - 1)) : GermAtom (germBP.gen (adjT k)) := ⟨k, rfl⟩

/-- **A kept 1-cell is an atom** — `germPerm` pins the 1-cell and `adjT` is injective. -/
theorem eq_gen_adjT_of_germAtom {N : ℕ} {e : germBP.pt N ⟶ germBP.pt N} {k : Fin (N - 1)}
    (h : germPerm e = adjT k) : e = germBP.gen (adjT k) := by
  obtain ⟨s, rfl⟩ := germBP.exists_gen e
  exact congrArg germBP.gen h

/-- **…and the kept 1-cells at `N` strands are the `N−1` atoms.** -/
noncomputable def germKeptEquiv (N : ℕ) :
    Fin (N - 1) ≃ keptGen GermAtom (germBP.pt N).as (germBP.pt N).as :=
  Equiv.ofBijective (fun k => ⟨germBP.gen (adjT k), germAtom_gen_adjT k⟩)
    ⟨fun i j h => Fin.ext (adjT_inj (germBP.gen_injective (congrArg Subtype.val h))),
      fun e => by
        obtain ⟨k, hk⟩ := e.2
        exact ⟨k, Subtype.ext (eq_gen_adjT_of_germAtom hk).symm⟩⟩

/-! ## The atom word of a permutation -/

/-- The atoms a permutation spells, one per inversion. -/
noncomputable def atomList (N : ℕ) (σ : Equiv.Perm (Fin N)) : List (Fin (N - 1)) :=
  (exists_atomWord N σ).choose

theorem runLoop_atomList (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    runLoop N σ = (atomList N σ).foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) :=
  (exists_atomWord N σ).choose_spec.2.2

/-- A word of atoms, appended to a word already spelled. -/
noncomputable def germAtomCons (N : ℕ) (p : Quiver.Path (germBP.pt N) (germBP.pt N))
    (l : List (Fin (N - 1))) : Quiver.Path (germBP.pt N) (germBP.pt N) :=
  l.foldl (fun p k => p.cons (germBP.gen (adjT k))) p

theorem all_germAtomCons (N : ℕ) : ∀ (l : List (Fin (N - 1)))
    (p : Quiver.Path (germBP.pt N) (germBP.pt N)),
    Quiver.Path.All (fun ⦃_ _⦄ e => GermAtom e) p →
      Quiver.Path.All (fun ⦃_ _⦄ e => GermAtom e) (germAtomCons N p l) := by
  intro l
  induction l with
  | nil => exact fun _ hp => hp
  | cons k l ih =>
      intro p hp
      exact ih _ ((Quiver.Path.all_cons_iff p _).mpr ⟨hp, germAtom_gen_adjT k⟩)

theorem eval_germAtomCons (N : ℕ) : ∀ (l : List (Fin (N - 1)))
    (p : Quiver.Path (germBP.pt N) (germBP.pt N))
    (v : germBP.base.at' (germBP.pt N) ⟶ germBP.base.at' (germBP.pt N)),
    germBP.base.eval.map p = v →
      germBP.base.eval.map (germAtomCons N p l)
        = l.foldl (fun g k => g ≫ atomLoop N k) v := by
  intro l
  induction l with
  | nil => exact fun _ _ h => h
  | cons k l ih =>
      intro p v h
      refine ih _ _ ?_
      rw [germBP.base.eval_cons, h,
        show germBP.base.arrow (germBP.gen (adjT k)) = atomLoop N k from
          (germBP.base_arrow_of_simple germBP_bySimples (adjT k)).trans
            (by rw [germBP_perm, runLoop_adjT])]
      rfl

/-! ## The reduction -/

/-- The atom word a germ 1-cell spells. -/
noncomputable def germAtomWord {a b : germBP.poly.V} (e : germBP.poly.Gen a b) :
    Quiver.Path (germBP.poly.pt a) (germBP.poly.pt b) :=
  match e with
  | .mk s => germAtomCons _ Quiver.Path.nil (atomList _ s)

/-- …or the 1-cell itself, when that is already an atom. -/
noncomputable def germWord {a b : germBP.poly.V} (e : germBP.poly.Gen a b) :
    Quiver.Path (germBP.poly.pt a) (germBP.poly.pt b) :=
  @dite _ (GermAtom e) (Classical.propDecidable _) (fun _ => (Polygraph.cell e).toPath)
    (fun _ => germAtomWord e)

theorem all_germAtomWord {a b : germBP.poly.V} (e : germBP.poly.Gen a b) :
    Quiver.Path.All (fun ⦃_ _⦄ e' => GermAtom e') (germAtomWord e) := by
  cases e with
  | mk s => exact all_germAtomCons _ _ _ (Quiver.Path.all_nil _)

/-- **An atom word names the loop its permutation performs** — `exists_atomWord`, read in the
presentation. -/
theorem eval_germAtomWord {a b : germBP.poly.V} (e : germBP.poly.Gen a b) :
    germBP.base.eval.map (germAtomWord e) = germBP.base.arrow (Polygraph.cell e) := by
  cases e with
  | mk s =>
      refine Eq.trans (eval_germAtomCons _ _ _ _ (germBP.base.eval_nil _)) ?_
      refine Eq.trans (runLoop_atomList _ s).symm ?_
      exact ((germBP.base_arrow_of_simple germBP_bySimples s).trans
        (congrArg (runLoop _) (germBP_perm s))).symm

theorem all_germWord {a b : germBP.poly.V} (e : germBP.poly.Gen a b) :
    Quiver.Path.All (fun ⦃_ _⦄ e' => GermAtom e') (germWord e) := by
  by_cases h : GermAtom e
  · rw [germWord, dif_pos h]
    exact Quiver.Path.all_toPath.mpr h
  · rw [germWord, dif_neg h]
    exact all_germAtomWord e

/-- **Eliminating the non-atom germ generators loses nothing** — each names the atom word its
crossing permutation spells. -/
noncomputable def germSpans : Spans germBP.poly GermAtom (fun _ => True) where
  word := germWord
  word_all := all_germWord
  word_eq e := by
    by_cases h : GermAtom e
    · rw [germWord, dif_pos h]
    · rw [germWord, dif_neg h]
      exact germBP.base.E.map_injective (eval_germAtomWord e)
  word_self e h := dif_pos h
  cell_derivable {X Y} α := by
    exact Polygraph.quot_src_tgt
      (Polygraph.sub (P := germBP.poly) GermAtom (fun _ => True) germWord all_germWord)
      (x := ⟨X.as⟩) (y := ⟨Y.as⟩) ⟨α, trivial⟩

/-- **`Ch(Z)[W⁻¹]` presented on the `N−1` atoms**, with the germ's 2-cells substituted. -/
noncomputable def germAtomPresentation :
    Presents germSpans.poly (((W Zbp).op).Localization) :=
  germBP.base.restrictCells germSpans

/-- **A kept 1-cell names the atom loop it always named.** -/
theorem germAtomPresentation_arrow {N : ℕ} (k : Fin (N - 1)) :
    germAtomPresentation.arrow (germKeptEquiv N k) = atomLoop N k :=
  (germBP.base.restrictCells_arrow germSpans _).trans
    ((germBP.base_arrow_of_simple germBP_bySimples (adjT k)).trans
      (by rw [germBP_perm, runLoop_adjT]))

end ChainCat
