import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Machinery.Presentation.Basic

/-!
# Concurrency/Presentation/CubePresentation — the localized cube slice, presented

`Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`), so its presentation carries no word problem: the
generators are the **atom steps** — one per descent of a run's permutation — and the relations are
*all* of them, `Presents.ofThin`.  Fullness is `exists_word` read as a path, essential surjectivity
is the merge out of a chain's own run (`classRunIso`).

The 0-cells are permutations rather than `Run (□n)`: `Word` and `exists_word` are indexed that way,
and `runAt` realises each class on the nose.
-/

open CategoryTheory BPSet CubeChains CubeChain Polygraph

namespace ChainCat

variable {n : ℕ}

/-- **The generating 1-cells: the atom steps.**  A step out of the run at `σ` is a descent `i` of
`σ`, and it lands on the run at `σ * adjT i`. -/
def CubeStep (n : ℕ) (σ τ : Equiv.Perm (Fin n)) : Type :=
  {i : Fin (n - 1) // σ (adjHi i) < σ (adjLo i) ∧ τ = σ * adjT i}

/-- The interpretation: a 0-cell is the run of its class, a 1-cell the step between two runs —
which is unique, the localization being thin, so nothing that matters is chosen. -/
noncomputable def cubeEval (n : ℕ) : GenObj (CubeStep n) ⥤q (W (□n)).Localization where
  obj σ := (W (□n)).Q.obj (runAt σ.as).chain
  map {σ τ} e := (nonempty_loc_hom (c := (runAt σ.as).chain) (c' := (runAt τ.as).chain) (by
    simp only [weakClass_runAt, e.2.2]
    exact WeakOrder.of_mul_adjT_le e.2.1)).some

/-- **A word in the atom steps is a path of generators.** -/
theorem nonempty_path_of_word {σ τ : Equiv.Perm (Fin n)}
    {g : (W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain} (w : Word σ τ g) :
    Nonempty (Quiver.Path (⟨σ⟩ : GenObj (CubeStep n)) ⟨τ⟩) := by
  induction w with
  | nil s => exact ⟨Quiver.Path.nil⟩
  | @cons σ' _ i d u hd _ _ ih =>
      obtain ⟨p⟩ := ih
      exact ⟨(Quiver.Hom.toPath (show (⟨σ'⟩ : GenObj (CubeStep n)) ⟶ ⟨σ' * adjT i⟩ from
        ⟨i, descent_of_word_step u hd, rfl⟩)).comp p⟩

/-- **Fullness**: every morphism of the localization is spelled by a path of atom steps
(`exists_word`). -/
theorem nonempty_path_of_loc_hom (x y : GenObj (CubeStep n))
    (f : (cubeEval n).obj x ⟶ (cubeEval n).obj y) : Nonempty (Quiver.Path x y) := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  have hle : WeakOrder.of y ≤ WeakOrder.of x := by
    simpa using weakClass_le_of_loc_hom f
  obtain ⟨g, hg⟩ := exists_word x y hle
  exact nonempty_path_of_word hg

/-- **Essential surjectivity**: every object is its class's run, up to the merge into it. -/
theorem exists_run_of_loc_obj (X : (W (□n)).Localization) :
    ∃ x : GenObj (CubeStep n), Nonempty ((cubeEval n).obj x ≅ X) := by
  obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj _ X
  exact ⟨⟨cross c⟩, ⟨classRunIso (rfl : cross c = cross c)⟩⟩

/-- **`Ch (□n)[W⁻¹]` is presented by its atom steps**: 0-cells the runs, 1-cells the atom steps
between them, and every parallel pair of words related — which is all the relations there are,
`locCube_isThin`. -/
noncomputable def cubePresentation (n : ℕ) :
    Presents (Polygraph.thin (CubeStep n)) ((W (□n)).Localization) :=
  Presents.ofThin (cubeEval n) nonempty_path_of_loc_hom exists_run_of_loc_obj

end ChainCat
