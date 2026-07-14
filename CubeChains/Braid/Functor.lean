import CubeChains.Braid.Category
import CubeChains.Salvetti.BraidCharacters

/-!
# Braid/Functor — the braid of an execution

An execution refines into another by reordering its events; the braid of that refinement is the
**simple** braid of its event permutation.  There is no choice here and nothing to lift: in the germ
presentation `ofPerm (evPerm f)` *is* a generator.

Functoriality is the germ relation, and it is already proved: `writhe` is a functor and
`writhe_braidPsi` identifies it with the inversion count, so **composable refinements never cross
the same pair of events twice** — inversion counts add.

    Ψ : ConcCatN K n ⥤ BraidFib n      f ↦ ofPerm (evPerm f)
    Φ = FreeGroupoid.lift Ψ            2-cells ↦ honest braids
-/

namespace CubeChains

open CategoryTheory Equiv

variable {K : BPSet} {n : ℕ}

/-- The germ's length is the repo's inversion count: both count the crossed pairs. -/
theorem invCount_eq_permLen (σ : Perm (Fin n)) : invCount σ = permLen σ := by
  classical
  simp only [invCount, permLen, inversions]
  refine Finset.card_bij' (fun (e : BraidGround n) _ => e.1)
    (fun (p : Fin n × Fin n) hp => (⟨p, (Finset.mem_filter.mp hp).2.1⟩ : BraidGround n))
    ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ _, e.2, he.2⟩
  · intro p hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.2⟩
  · intro e _
    exact Subtype.ext rfl
  · intro p _
    rfl

/-- **Composable refinements never cross the same pair of events twice**: inversion counts add.
This is `writhe` being a functor, read through `writhe_braidPsi` — and it is precisely the germ
relation `[σ][τ] = [στ]`. -/
theorem permLen_evPerm_comp {x y z : ConcCatN K n} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (evPerm g * evPerm f) = permLen (evPerm g) + permLen (evPerm f) := by
  have hfun : (writhe n).map ((braidPsi K n).map (f ≫ g))
      = (writhe n).map ((braidPsi K n).map f) ≫ (writhe n).map ((braidPsi K n).map g) := by
    rw [Functor.map_comp, Functor.map_comp]
  rw [writhe_braidPsi, writhe_braidPsi, writhe_braidPsi, SingleObj.comp_as_mul,
    ← ofAdd_add] at hfun
  have hZ := Multiplicative.ofAdd.injective hfun
  have hN : invCount (evPerm (f ≫ g))⁻¹
      = invCount (evPerm g)⁻¹ + invCount (evPerm f)⁻¹ := by exact_mod_cast hZ
  rw [invCount_eq_permLen, invCount_eq_permLen, invCount_eq_permLen, permLen_inv, permLen_inv,
    permLen_inv, evPerm_comp] at hN
  exact hN

/-- **The braid of a refinement**: the simple braid of its event permutation. -/
noncomputable def braidPsiGerm (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ BraidFib n where
  obj _ := SingleObj.star _
  map {_ _} f := ofPerm (evPerm f)
  map_id x := by
    change ofPerm (evPerm (𝟙 x)) = (1 : Braid n)
    rw [evPerm_id]
    exact ofPerm_one
  map_comp {_ _ _} f g := by
    rw [SingleObj.comp_as_mul]
    change ofPerm (evPerm (f ≫ g)) = ofPerm (evPerm g) * ofPerm (evPerm f)
    rw [evPerm_comp, ofPerm_mul (permLen_evPerm_comp f g)]

/-- **The braid functor**: every 2-cell of the concurrency groupoid is an honest braid.
`FreeGroupoid.lift` — no presentation theorem, no Salvetti. -/
noncomputable def braidPhi (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ BraidFib n :=
  FreeGroupoid.lift (braidPsiGerm K n)

/-- Read into the braid category, where the strand count is visible. -/
noncomputable def braidPhiCat (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ Braids :=
  braidPhi K n ⋙ braidIncl n

@[simp] theorem braidPhi_homMk {x y : ConcCatN K n} (f : x ⟶ y) :
    (braidPhi K n).map (FreeGroupoid.homMk f) = ofPerm (evPerm f) :=
  FreeGroupoid.lift_map_homMk _ f

/-- **`Φ` lifts the event monodromy**: its `Sₙ`-shadow is exactly `evPerm`. -/
@[simp] theorem permHom_braidPhi {x y : ConcCatN K n} (f : x ⟶ y) :
    permHom n ((braidPhi K n).map (FreeGroupoid.homMk f)) = evPerm f := by
  rw [braidPhi_homMk, permHom_ofPerm]

end CubeChains
