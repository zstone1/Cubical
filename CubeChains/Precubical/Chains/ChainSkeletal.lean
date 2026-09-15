import CubeChains.Concurrency.Grading.BlockDecomp
import Mathlib.CategoryTheory.Skeletal

/-!
# Precubical/Chains/ChainSkeletal — `Ch(K)` is an acyclic, skeletal category

For **every** bi-pointed precubical set `K`, the cube-chain category `Ch(K)` has only identity
endomorphisms and is skeletal — no `NonSelfLinked`, no `AdmitsAltitude K`, no thinness.  A
refinement keeps every junction of its target (`boundaries_subset_of_wedgeHom`) and a shape is its
junction set, so equal bead counts force equal shapes; on one shape a bead lies inside the bead of
its own index, and `Box` being rigid, it fills it.
-/

open CategoryTheory Opposite CubeChain CubeChains StdCube BPSet

namespace CubeChain

/-! ### Rigidity of the serial wedge -/

/-- **Equal bead counts force equal dimension lists** — nested junction sets of one size. -/
theorem serialWedge_dims_eq_of_length_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd)
    (hlen : ad.length = cd.length) : ad = cd :=
  (boundaries_injective (Finset.eq_of_subset_of_card_le (ChainCat.boundaries_subset_of_wedgeHom φ)
    (by rw [card_boundaries, card_boundaries, hlen]))).symm

/-- **On one shape a bead lies in the bead of its own index** — it sits inside its target block,
and the bead starts strictly rise. -/
theorem blockIdx_endo {d : List ℕ+} (φ : ⋁d ⟶ ⋁d) (i : Fin d.length) : blockIdx φ.hom i = i := by
  have hsub := serialWedge_bead_sub_block φ.hom φ.app_init i
  have hs := beadStart_succ d i
  have hpos := (d.get i).pos
  refine Fin.ext (le_antisymm (not_lt.mp fun h => ?_) (not_lt.mp fun h => ?_))
  · have := beadStart_mono d (show i.val + 1 ≤ (blockIdx φ.hom i).val by omega)
    omega
  · have := beadStart_mono d (show (blockIdx φ.hom i).val + 1 ≤ i.val by omega)
    omega

/-- **Every bi-pointed endomorphism of a serial wedge is the identity** — each bead lands on its own
cube as a full-dimensional face, which in `Box` is `𝟙`. -/
theorem serialWedge_bipointed_endo_id (dims : List ℕ+) (φ : ⋁dims ⟶ ⋁dims) :
    φ = 𝟙 (⋁dims) := by
  have hblock : ∀ i : Fin dims.length, ιᵂ dims i ≫ φ.hom = ιᵂ dims i := by
    intro i
    obtain ⟨r, incl, hincl⟩ := wedgeMap_block φ.hom i
    have hr : r = i := (blockIdx_eq_of_factor φ.hom i r incl hincl).trans (blockIdx_endo φ i)
    subst r
    rw [Box.endo_eq_id incl, CategoryTheory.Functor.map_id, Category.id_comp] at hincl
    exact hincl
  apply hom_ext
  rw [id_hom]
  refine serialWedge_hom_ext dims φ.hom (𝟙 (⋁dims).toPsh) (fun i => ?_) ?_
  · rw [Category.comp_id]; exact hblock i
  · rw [φ.app_init]; rfl

end CubeChain

/-! ### Consequences for the chain category `Ch(K)` -/

/-- **Every endomorphism of `Ch(K)` is the identity** — for every `K`. -/
theorem ChainCat.endo_eq_id {K : BPSet} {a : Ch K} (f : a ⟶ a) : f = 𝟙 a := by
  apply ChainCat.hom_ext'
  rw [ChainCat.id_φ]
  exact serialWedge_bipointed_endo_id a.dims f.φ

/-- **A coarsening never increases the bead count** — its junctions are among the source's. -/
theorem ChainCat.dims_length_le_of_hom {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    b.dims.length ≤ a.dims.length := by
  have h := Finset.card_le_card (ChainCat.boundaries_subset_of_hom f)
  rw [card_boundaries, card_boundaries] at h
  omega

/-- **Equal bead counts force equal dimension lists**, read on the chain's own wedge. -/
theorem ChainCat.dims_eq_of_hom_of_length_eq {K : BPSet} {a b : Ch K} (f : a ⟶ b)
    (hlen : a.dims.length = b.dims.length) : a.dims = b.dims :=
  serialWedge_dims_eq_of_length_eq f.φ hlen

/-- **Equal bead counts force equal chains** — equal shapes, and then the wedge map is `𝟙`. -/
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

/-- **`Ch(K)` is skeletal**: arrows both ways bound each other's bead counts, and equal counts
force equality. -/
theorem ChainCat.eq_of_hom_hom {K : BPSet} {a b : Ch K}
    (f : a ⟶ b) (g : b ⟶ a) : a = b :=
  ChainCat.eq_of_hom_of_dims_length_eq f
    (Nat.le_antisymm (ChainCat.dims_length_le_of_hom g) (ChainCat.dims_length_le_of_hom f))

/-- **…which is `Skeletal` in mathlib's sense** — the form the rest of the tree should cite. -/
theorem ChainCat.skeletal (K : BPSet) : Skeletal (Ch K) :=
  fun _ _ ⟨e⟩ => ChainCat.eq_of_hom_hom e.hom e.inv
