import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Concurrency.Grading.CoordFunctor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Precubical/Chains/ChainSkeletal — `Ch(K)` is an acyclic, skeletal category

For **every** bi-pointed precubical set `K`, the cube-chain category `Ch(K)` has only identity
endomorphisms and is skeletal — no `NonSelfLinked`, no `AdmitsAltitude K`, no thinness.  The engine
is `blockIdx`: monotone (`serialWedge_blockIdx_monotone`) and surjective (the coordinate coend,
`CubeChains.coordMap_bijective`), so a coarsening never gains beads and equal bead counts already
force the two chains to coincide.

* `serialWedge_bipointed_endo_id` — a bi-pointed endomorphism of a serial wedge is the identity.
* `ChainCat.eq_of_hom_hom` — `Ch(K)` is skeletal: `a ⟶ b` and `b ⟶ a` force `a = b`.
* `ChainCat.lt_dims_length_of_not_isIso` — a proper coarsening strictly drops the bead count.
* `ChainCat.exists_hom_maximal` — hence coarsening terminates: every chain maps into a maximal one.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet

namespace CubeChain

/-! ### `blockIdx` is a monotone surjection -/

/-- **`blockIdx` of a bi-pointed serial-wedge map is surjective.**  Every target bead has a
coordinate (beads have positive dimension); pull it back through the coordinate bijection
`coordMap_bijective`, whose bead component is `blockIdx` (`coordMap_fst`). -/
theorem blockIdx_surjective {ad cd : List ℕ+}
    (φ : ⋁ad ⟶ ⋁cd) :
    Function.Surjective (blockIdx φ.hom) := fun j => by
  obtain ⟨p, hp⟩ := (CubeChains.coordMap_bijective φ).2 ⟨j, ⟨0, (cd.get j).pos⟩⟩
  exact ⟨p.1, by rw [← CubeChains.coordMap_fst φ p, hp]⟩

/-- **Equal bead counts pin `blockIdx` to the length cast.**  A monotone surjection between `Fin`s
of equal cardinality is strictly monotone, hence *the* order isomorphism. -/
theorem blockIdx_val_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd)
    (hlen : ad.length = cd.length) (i : Fin ad.length) :
    (blockIdx φ.hom i).val = i.val := by
  have hsurj := blockIdx_surjective φ
  have hstrict : StrictMono (blockIdx φ.hom) :=
    (serialWedge_blockIdx_monotone φ.hom φ.app_init).strictMono_of_injective
      ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by simp [hlen]⟩).1
  exact congrArg (fun e : Fin ad.length ≃o Fin cd.length => (e i).val)
    (Subsingleton.elim (hstrict.orderIsoOfSurjective _ hsurj) (Fin.castOrderIso hlen))

/-! ### Rigidity of the serial wedge -/

/-- **Equal bead counts force equal dimension lists.**  `blockIdx φ` is then the identity, each
`blockFace` bounds `adᵢ ≤ cdᵢ`, and the two dimension sums agree (`serialWedge_dimSum_eq`) — so
every bound is an equality. -/
theorem serialWedge_dims_eq_of_length_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd)
    (hlen : ad.length = cd.length) : ad = cd := by
  have hbij : Function.Bijective (blockIdx φ.hom) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨blockIdx_surjective φ, by simp [hlen]⟩
  have hface : ∀ i, (ad.get i : ℕ) ≤ (cd.get (blockIdx φ.hom i) : ℕ) := fun i =>
    cells_card_le (ev (blockFace φ.hom i))
  have hsum : (∑ i, (ad.get i : ℕ)) = ∑ i, (cd.get (blockIdx φ.hom i) : ℕ) := by
    have ereindex : (∑ i, (cd.get (blockIdx φ.hom i) : ℕ)) = ∑ j, (cd.get j : ℕ) :=
      Fintype.sum_bijective (blockIdx φ.hom) hbij _ _ (fun _ => rfl)
    -- `get`-spelled restatements: `rw` will not unfold `get` to `getElem` for `kabstract`.
    have ea : (∑ i, (ad.get i : ℕ)) = dimSum ad :=
      Fin.sum_univ_fun_getElem ad (fun d => (d : ℕ))
    have ec : (∑ j, (cd.get j : ℕ)) = dimSum cd :=
      Fin.sum_univ_fun_getElem cd (fun d => (d : ℕ))
    rw [ereindex, ea, ec]
    exact serialWedge_dimSum_eq φ
  have hpt := (Finset.sum_eq_sum_iff_of_le (fun i _ => hface i)).mp hsum
  refine List.ext_getElem hlen (fun k h1 h2 => ?_)
  change ad.get ⟨k, h1⟩ = cd.get ⟨k, h2⟩
  rw [PNat.coe_injective (hpt ⟨k, h1⟩ (Finset.mem_univ _))]
  exact congrArg cd.get (Fin.ext (blockIdx_val_eq φ hlen ⟨k, h1⟩))

/-- **Every bi-pointed endomorphism of a serial wedge is the identity.**

`blockIdx φ` is the identity (`blockIdx_val_eq`), so bead `i`'s image is a *full-dimensional*
`Box`-face of bead `i` — and `Box` is rigid, so that face is `𝟙`.  `serialWedge_hom_ext` then
assembles `φ = 𝟙`. -/
theorem serialWedge_bipointed_endo_id (dims : List ℕ+)
    (φ : ⋁dims ⟶ ⋁dims) :
    φ = 𝟙 (⋁dims) := by
  have hblock : ∀ i : Fin dims.length,
      ιᵂ dims i ≫ φ.hom = ιᵂ dims i := by
    intro i
    obtain ⟨r, incl, hincl⟩ := wedgeMap_block φ.hom i
    have hr : r = i :=
      (blockIdx_eq_of_factor φ.hom i r incl hincl).trans (Fin.ext (blockIdx_val_eq φ rfl i))
    subst r
    rw [Box.endo_eq_id incl, CategoryTheory.Functor.map_id, Category.id_comp] at hincl
    exact hincl
  -- Assemble via the serial-wedge uniqueness.
  apply hom_ext
  rw [id_hom]
  refine serialWedge_hom_ext dims φ.hom (𝟙 (⋁dims).toPsh) (fun i => ?_) ?_
  · rw [Category.comp_id]; exact hblock i
  · rw [φ.app_init]; rfl

end CubeChain

open CubeChain

/-! ### Consequences for the chain category `Ch(K)` -/

/-- **Every endomorphism of `Ch(K)` is the identity** — for every `K`. -/
theorem ChainCat.endo_eq_id {K : BPSet} {a : Ch K} (f : a ⟶ a) : f = 𝟙 a := by
  apply ChainCat.hom_ext'
  rw [ChainCat.id_φ]
  exact serialWedge_bipointed_endo_id a.dims f.φ

/-- **A coarsening never increases the bead count.**  `blockIdx fᵂ` is a surjection
`ChainCat.Bead a ↠ ChainCat.Bead b`. -/
theorem ChainCat.dims_length_le_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    b.dims.length ≤ a.dims.length := by
  have h := Fintype.card_le_of_surjective _ (blockIdx_surjective f.φ)
  simpa using h

/-- **Equal bead counts force equal dimension lists** — the serial-wedge fact
`serialWedge_dims_eq_of_length_eq`, read on the chain's own wedge. -/
theorem ChainCat.dims_eq_of_hom_of_length_eq {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hlen : a.dims.length = b.dims.length) : a.dims = b.dims :=
  serialWedge_dims_eq_of_length_eq f.φ hlen

/-- **Equal bead counts force equal chains.**  Combines `dims_eq_of_hom_of_length_eq` with the
serial-wedge endo-rigidity (`serialWedge_bipointed_endo_id`). -/
theorem ChainCat.eq_of_hom_of_dims_length_eq {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hlen : a.dims.length = b.dims.length) : a = b := by
  have hdimseq := ChainCat.dims_eq_of_hom_of_length_eq f hlen
  cases a with
  | mk da ma =>
    cases b with
    | mk db mb =>
      obtain rfl : da = db := hdimseq
      have hφ : f.φ = 𝟙 (⋁da) := serialWedge_bipointed_endo_id da f.φ
      have hmap : ma = mb := by
        have hw := f.w
        rw [hφ, Category.id_comp] at hw
        exact hw.symm
      rw [hmap]

/-- **`Ch(K)` is skeletal**: any pair of morphisms `a ⟶ b`, `b ⟶ a` forces `a = b`.  Each arrow
bounds the other's bead count (`dims_length_le_of_hom`), so the counts agree — and equal counts
already force equality. -/
theorem ChainCat.eq_of_hom_hom {K : BPSet} {a b : Ch K}
    (f : a ⟶ b) (g : b ⟶ a) : a = b :=
  ChainCat.eq_of_hom_of_dims_length_eq f
    (Nat.le_antisymm (ChainCat.dims_length_le_of_hom g) (ChainCat.dims_length_le_of_hom f))

/-- **Antisymmetry of the chain order** (`a ≤ b` := a morphism `a ⟶ b` exists).
With thinness (`chainCat_hom_subsingleton`, under `NonSelfLinked` + `AdmitsAltitude`),
`Ch(K)` is therefore a **poset**: the objects with `≤` form a partial order and the
category is thin, i.e. is that poset. -/
theorem ChainCat.le_antisymm {K : BPSet} {a b : Ch K}
    (hab : Nonempty (a ⟶ b)) (hba : Nonempty (b ⟶ a)) : a = b :=
  ChainCat.eq_of_hom_hom hab.some hba.some

/-- **A proper coarsening strictly drops the bead count.**  A non-isomorphism `g : a ⟶ c` has
`c.dims.length < a.dims.length`: equal length would force `a = c`, making `g` an endomorphism, hence
the identity (`ChainCat.endo_eq_id`), an isomorphism — contradiction.  The well-foundedness input
for `exists_hom_maximal`. -/
theorem ChainCat.lt_dims_length_of_not_isIso {K : BPSet} {a c : Ch K} (g : a ⟶ c)
    (hg : ¬ IsIso g) : c.dims.length < a.dims.length := by
  rcases (ChainCat.dims_length_le_of_hom g).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain rfl : a = c := ChainCat.eq_of_hom_of_dims_length_eq g h.symm
    exact hg (by rw [ChainCat.endo_eq_id g]; infer_instance)

/-! ### Maximal chains -/

/-- **A chain with no proper coarsening.**  Arrows run finer ⟶ coarser, so a set that every chain
maps *into* must consist of these. -/
def ChainCat.MaximalChains (K : BPSet) : Set (Ch K) :=
  {c | ∀ (b : Ch K) (f : c ⟶ b), IsIso f}

/-- **Coarsening terminates**: every chain admits an arrow into a maximal one.  Induction on the
bead count, which `lt_dims_length_of_not_isIso` strictly drops at every proper step — no finiteness
and no acyclicity hypothesis on `K`. -/
theorem ChainCat.exists_hom_maximal {K : BPSet} (c : Ch K) :
    ∃ s ∈ ChainCat.MaximalChains K, Nonempty (c ⟶ s) := by
  generalize hn : c.dims.length = n
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases hc : ∀ (b : Ch K) (f : c ⟶ b), IsIso f
    · exact ⟨c, hc, ⟨𝟙 c⟩⟩
    · simp only [not_forall] at hc
      obtain ⟨b, f, hf⟩ := hc
      obtain ⟨s, hs, ⟨g⟩⟩ :=
        ih b.dims.length (hn ▸ ChainCat.lt_dims_length_of_not_isIso f hf) b rfl
      exact ⟨s, hs, ⟨f ≫ g⟩⟩
