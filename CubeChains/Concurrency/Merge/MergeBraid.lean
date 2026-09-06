import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid

/-!
# Concurrency/Merge/MergeBraid — the merges cross nothing

A cut exhibits `f` as `𝟙 ∨ w ∨ 𝟙` (`eq_splicePhi_of_sq`), so a cut with `w = cubeMerge p q` *is*
the spliced staircase `mergeHom`; that one runs its first bead through the coordinate block
`[0, p)` and its second through `[p, p+q)`, both increasingly, hence crosses nothing.  Crossings
multiply, so the whole class it generates crosses nothing and every germ grading inverts it.

The converse — a refinement that crosses nothing is a composite of merges — is
`Concurrency/Merge/MergeGenerate`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain StdCube

namespace ChainCat

/-- **The crossing permutation sees only the wedge map**, so pushing a chain morphism forward to
the serial wedges leaves it alone. -/
theorem crossPerm_zHom {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    crossPerm (a := zObj a.dims) (b := zObj b.dims) h (zHom f.φ) = crossPerm h f := rfl

/-! ### The merge staircase keeps the coordinate order -/

/-- **The merge staircase does not braid its two beads**: the first runs the low coordinate block,
the second the high one, both increasingly. -/
theorem pos_coordMap_pairMerge_cubeMerge (p q : ℕ+) (y : beadEvent [p, q]) :
    (pos (coordMap (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ))) y) : ℕ) = (pos y : ℕ) :=
  pos_coordMap_pairMerge p q _ (g := fun s => s)
    (faceEmb_cubeMerge_inl _ _) (faceEmb_cubeMerge_inr _ _) y

/-- **A merge preserves the event order**, whatever it is spliced between. -/
theorem pos_coordMap_splicePhi_cubeMerge (l r : List ℕ+) (p q : ℕ+)
    (e : beadEvent (l ++ p :: q :: r)) :
    (pos (coordMap (splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ))) e) : ℕ) = (pos e : ℕ) := by
  rw [pos_coordMap_splicePhi (g := fun s => s) l r p q _
    (pos_coordMap_pairMerge_cubeMerge p q) e rfl]
  split_ifs <;> omega

/-! ### The class crosses nothing -/

/-- **A generator keeps the event order** — by `eq_splicePhi_of_sq` it *is* the spliced
staircase. -/
theorem pos_coordMap_of_merge {K : BPSet} {a b : Ch K} {f : a ⟶ b} (h : merge K f) :
    ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  obtain ⟨d, hw⟩ := h
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  rw [eq_splicePhi_of_sq sq, hw]
  exact pos_coordMap_splicePhi_cubeMerge l r p q

/-- **The class keeps the event order**: the generators do, and the property is multiplicative. -/
theorem pos_coordMap_of_W {K : BPSet} {a b : Ch K} {f : a ⟶ b} (hf : W K f) :
    ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) := by
  induction hf with
  | of _ h => exact pos_coordMap_of_merge h
  | id x => intro e; rw [id_φ, coordMap_id]; rfl
  | comp_of u v _ hv ih =>
      intro e
      rw [comp_φ, coordMap_comp, Function.comp_apply, pos_coordMap_of_merge hv, ih e]

/-- **A merge crosses nothing** — at any strand count its source meets, since recounting
conjugates. -/
theorem crossPerm_eq_one_of_W {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    {f : a ⟶ b} (hf : W K f) : crossPerm h f = 1 :=
  Equiv.ext fun i => by
    obtain ⟨e, rfl⟩ := (strand a.dims h).surjective i
    exact Fin.ext (by rw [Equiv.Perm.one_apply, crossPerm_strand, strand_val, strand_val,
      pos_coordMap_of_W hf e])

end ChainCat
