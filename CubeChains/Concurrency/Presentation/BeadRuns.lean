import CubeChains.Concurrency.Presentation.SliceRunSet

/-!
# Concurrency/Presentation/BeadRuns — the runs over a chain are the block sums

A run over `zObj d` is a wedge map into `⋁d` out of an all-edges wedge
(`runSet_iff_exists_wedgeHom`); such a map splits at every junction of its target
(`splitTarget`), and `crossPerm` is monoidal there (`crossPerm_chConcat`).  So the runs over a
concatenation are exactly the block sums of the runs over the two halves, and a single cube — the
coarsest chain on its events — admits *every* permutation of its axes.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

/-! ## A run over a standard chain is an all-edges wedge map -/

/-- **A run over `zObj d` is a wedge map into `⋁d` out of an all-edges wedge**, named by its
crossing permutation.  The source shape stays free: pinning it to `𝟙^N` (`RunOver.left_eq`) would
put a `List.replicate_add` transport in the way of every splitting below. -/
theorem runSet_iff_exists_wedgeHom {d : List ℕ+} {N : ℕ} {σ : Perm (Fin N)} :
    RunSet (zObj d) N σ ↔ ∃ (e : List ℕ+) (_ : ∀ x ∈ e, x = 1) (h : dimSum e = N)
      (φ : ⋁e ⟶ ⋁d), crossPerm (a := zObj e) h (zHom φ) = σ := by
  constructor
  · rintro ⟨⟨⟨⟨⟨ed, em⟩, ⟨⟩, g⟩, hrun⟩, hN⟩, rfl⟩
    exact ⟨ed, hrun, hN, g.φ, rfl⟩
  · rintro ⟨e, hone, h, φ, rfl⟩
    exact ⟨⟨⟨Over.mk (zHom φ), hone⟩, h⟩, rfl⟩

/-! ## Splitting at a junction -/

/-- **The crossing of a wedge concatenation is the block sum** — `crossPerm_chConcat` read on
`Ch Zbp`, where a wedge map *is* a chain map (`zHom`).  The strand counts are named, so the
equation is between permutations of `Fin (m + n)` with no `Fin` transport. -/
theorem crossPerm_zHom_concat {e₁ e₂ dl dr : List ℕ+} (φ₁ : ⋁e₁ ⟶ ⋁dl) (φ₂ : ⋁e₂ ⟶ ⋁dr)
    {m n : ℕ} (h₁ : dimSum e₁ = m) (h₂ : dimSum e₂ = n) (h : dimSum (e₁ ++ e₂) = m + n) :
    crossPerm h (zHom (concatHomφ (zHom φ₁) (zHom φ₂)))
      = permSum m n (crossPerm h₁ (zHom φ₁), crossPerm h₂ (zHom φ₂)) := by
  subst h₁
  subst h₂
  refine Eq.trans ?_ (crossPerm_chConcat (ab := (zObj e₁, zObj e₂))
    (ab' := (zObj dl, zObj dr)) (zHom φ₁, zHom φ₂))
  exact crossPerm_eq_of_φ h rfl

/-- **The runs over a concatenation are the block sums of the runs over the halves.**  Naming the
two counts `m`, `n` keeps the block sum an honest equality of permutations of `Fin (m + n)`. -/
theorem runSet_append {dl dr : List ℕ+} {m n : ℕ} (hl : dimSum dl = m) (hr : dimSum dr = n)
    (σ : Perm (Fin (m + n))) :
    RunSet (zObj (dl ++ dr)) (m + n) σ ↔
      ∃ (σ₁ : Perm (Fin m)) (σ₂ : Perm (Fin n)),
        RunSet (zObj dl) m σ₁ ∧ RunSet (zObj dr) n σ₂ ∧ σ = permSum m n (σ₁, σ₂) := by
  constructor
  · rintro h
    obtain ⟨e, hone, he, φ, rfl⟩ := runSet_iff_exists_wedgeHom.mp h
    obtain ⟨e₁, e₂, φ₁, φ₂, rfl, hφ⟩ := splitTarget φ
    rw [eqToHom_refl, Category.id_comp] at hφ
    have hφ' : φ = concatHomφ (zHom φ₁) (zHom φ₂) := hφ
    have h₁ : dimSum e₁ = m := (serialWedge_dimSum_eq φ₁).trans hl
    have h₂ : dimSum e₂ = n := (serialWedge_dimSum_eq φ₂).trans hr
    refine ⟨crossPerm h₁ (zHom φ₁), crossPerm h₂ (zHom φ₂),
      runSet_iff_exists_wedgeHom.mpr
        ⟨e₁, fun x hx => hone x (List.mem_append_left _ hx), h₁, φ₁, rfl⟩,
      runSet_iff_exists_wedgeHom.mpr
        ⟨e₂, fun x hx => hone x (List.mem_append_right _ hx), h₂, φ₂, rfl⟩, ?_⟩
    rw [hφ']
    exact crossPerm_zHom_concat φ₁ φ₂ h₁ h₂ he
  · rintro ⟨σ₁, σ₂, hσ₁, hσ₂, rfl⟩
    obtain ⟨e₁, hone₁, h₁, φ₁, rfl⟩ := runSet_iff_exists_wedgeHom.mp hσ₁
    obtain ⟨e₂, hone₂, h₂, φ₂, rfl⟩ := runSet_iff_exists_wedgeHom.mp hσ₂
    exact runSet_iff_exists_wedgeHom.mpr
      ⟨e₁ ++ e₂, fun x hx => (List.mem_append.mp hx).elim (hone₁ x) (hone₂ x),
        by rw [dimSum_append, h₁, h₂], concatHomφ (zHom φ₁) (zHom φ₂),
        crossPerm_zHom_concat φ₁ φ₂ h₁ h₂ _⟩

/-! ## A single cube -/

/-- **The one-bead shape's runs are every permutation** — nothing is coarser on its events. -/
theorem runSet_topDims (N : ℕ) (σ : Perm (Fin N)) : RunSet (zObj (topDims N)) N σ :=
  ⟨⟨⟨Over.mk ((onesTopEquiv N).symm σ), fun _ hd => List.eq_of_mem_replicate hd⟩,
      dimSum_replicate N⟩,
    crossPerm_onesTopEquiv_symm N σ⟩

/-- **Every permutation of a single bead's axes is a run over it** — a one-bead shape is the
coarsest chain on its events. -/
theorem runSet_single (c : ℕ+) (σ : Perm (Fin (c : ℕ))) : RunSet (zObj [c]) (c : ℕ) σ := by
  rw [← topDims_coe c]
  exact runSet_topDims _ σ

end ChainCat
