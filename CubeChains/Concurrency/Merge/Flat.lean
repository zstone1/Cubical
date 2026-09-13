import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Concurrency.Merge.MergeBraid

/-!
# Concurrency/Merge/Flat — the refinements that reorder nothing

A shape's **standard chain** reads it into the cube on its own events, firing the coordinates in
their own order (`stdChain`).  A refinement is **flat** when it carries the standard chain of its
target back to the standard chain of its source.

Flatness composes on the nose, and it is inherited by **factors** — which is the geometric content
of "a crossing is never undone": a coarsening of a chain of a cube is pinned by its shape
(`chain_ext_of_dims`), so the middle chain of a flat composite has nowhere to go but the middle
standard chain.  No permutation, no event, no bead.

`flat_iff_pos` is the one bridge to coordinates, spent once in `MergeGenerate`, at the generator,
where the middle map of a cut must be told from the braiding one.
-/

open CategoryTheory CubeChains CubeChain BPSet StdCube

namespace ChainCat

variable {K : BPSet}

/-! ## Reading a chain of a cube -/

/-- A chain of a cube is its map: the shape being fixed, the object equation is the map
equation. -/
theorem map_eq_of_chain_eq {N : ℕ} {d : List ℕ+} {χ χ' : ⋁d ⟶ □N}
    (h : (⟨d, χ⟩ : Ch (□N)) = ⟨d, χ'⟩) : χ = χ' := by
  obtain ⟨hd, hmap⟩ := ChainCat.Obj.eq_mk_of_eq h
  rw [Subsingleton.elim hd rfl] at hmap
  simpa using hmap

/-- **A chain fires in the event order exactly when every event flips the coordinate of its own
rank** — `flatten_coordFlip`, read as a condition on the chain. -/
theorem flatten_eq_one_iff {d : List ℕ+} {N : ℕ} (χ : ⋁d ⟶ □N) :
    flatten (⟨d, χ⟩ : Ch (□N)) = 1 ↔
      ∀ e : beadEvent d, coordFlip χ e = strand d (wedgeDimSum_eq χ) e := by
  refine ⟨fun h e => ?_, fun h => Equiv.ext fun x => ?_⟩
  · have hc := flatten_coordFlip χ e
    rw [h] at hc
    simpa using hc
  · obtain ⟨e, rfl⟩ := (coordFlip χ).surjective x
    rw [flatten_coordFlip, Equiv.Perm.one_apply]
    exact (h e).symm

/-- **The standard chains are compatible**: a coarsening is realised between them, a coarsening's
blocks being unions of the refinement's (`index_lt_iff_of_subset`). -/
theorem nonempty_stdChain_hom {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N) (hb : dimSum b = N)
    (hsub : boundaries b ⊆ boundaries a) :
    Nonempty ((⟨a, stdChain ha⟩ : Ch (□N)) ⟶ ⟨b, stdChain hb⟩) :=
  ⟨reflectHom (chFace_faceLE_iff.mpr fun p q hne => by
    simp only [beadOf_stdChain] at hne ⊢
    exact index_lt_iff_of_subset ha hb hsub hne)⟩

/-! ## Flatness -/

/-- A refinement is **flat** when it carries the standard chain of its target back to the standard
chain of its source — it reorders nothing.  The count is determined by the source; quantifying it
keeps the statement a bare equation of wedge maps, which is what makes flatness transport along any
relabelling of the two classifying maps (`W_iff_of_φ`). -/
def Flat {a b : Ch K} (u : a ⟶ b) : Prop :=
  ∀ {N : ℕ} (ha : dimSum a.dims = N) (hb : dimSum b.dims = N),
    Hom.φ u ≫ stdChain hb = stdChain ha

theorem flat_of_eq {a b : Ch K} {u : a ⟶ b} {N : ℕ} {ha : dimSum a.dims = N}
    {hb : dimSum b.dims = N} (h : Hom.φ u ≫ stdChain hb = stdChain ha) : Flat u := by
  subst ha
  intro _ ha' _
  subst ha'
  exact h

theorem flat_id (a : Ch K) : Flat (𝟙 a) := fun ha hb => by
  rw [id_φ, Category.id_comp, Subsingleton.elim hb ha]

/-- **Flatness composes** — the middle standard chain cancels. -/
theorem Flat.comp {a b c : Ch K} {f : a ⟶ b} {g : b ⟶ c} (hf : Flat f) (hg : Flat g) :
    Flat (f ≫ g) := fun ha hc => by
  rw [comp_φ, Category.assoc, hg ((dimSum_eq_of_hom f).symm.trans ha) hc]
  exact hf ha _

/-- **A factor of a flat refinement is flat** — the geometric no-double-crossing.  The middle chain
of the composite is a coarsening of the source's standard chain, and a coarsening is pinned by its
shape (`chain_ext_of_dims`), so it *is* the middle standard chain. -/
theorem Flat.of_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) (h : Flat (f ≫ g)) :
    Flat f ∧ Flat g := by
  have hb : dimSum b.dims = dimSum a.dims := (dimSum_eq_of_hom f).symm
  have hc : dimSum c.dims = dimSum a.dims := (dimSum_eq_of_hom (f ≫ g)).symm
  have hA : Hom.φ f ≫ (Hom.φ g ≫ stdChain hc) = stdChain (d := a.dims) rfl := by
    rw [← Category.assoc, ← comp_φ]; exact h rfl hc
  have hfA : (⟨a.dims, stdChain (d := a.dims) rfl⟩ : Ch (□(dimSum a.dims)))
      ⟶ (⟨b.dims, Hom.φ g ≫ stdChain hc⟩ : Ch (□(dimSum a.dims))) :=
    ⟨Hom.φ (K := K) f, hA⟩
  have hg : Hom.φ g ≫ stdChain hc = stdChain hb :=
    map_eq_of_chain_eq (chain_ext_of_dims hfA
      (nonempty_stdChain_hom rfl hb (boundaries_subset_of_hom f)).some rfl)
  exact ⟨flat_of_eq (ha := rfl) (hb := hb) (by rw [← hg]; exact hA),
    flat_of_eq (ha := hb) (hb := hc) hg⟩

/-! ## The bridge to coordinates -/

/-- **Flatness is the event order preserved.**  The standard chain has every event flip the
coordinate of its own rank, so a refinement pulls it back to the standard chain exactly when its
event map keeps every rank. -/
theorem flat_iff_pos {a b : Ch K} (u : a ⟶ b) :
    Flat u ↔ ∀ e : beadEvent a.dims, (pos (coordMap (Hom.φ u) e) : ℕ) = (pos e : ℕ) := by
  have hb : dimSum b.dims = dimSum a.dims := (dimSum_eq_of_hom u).symm
  have key : ∀ e' : beadEvent b.dims, coordFlip (stdChain hb) e' = strand b.dims hb e' :=
    (flatten_eq_one_iff _).mp (flatten_stdChain hb)
  have hflat : Flat u ↔
      flatten (⟨a.dims, Hom.φ u ≫ stdChain hb⟩ : Ch (□(dimSum a.dims))) = 1 := by
    refine ⟨fun h => by rw [h rfl hb]; exact flatten_stdChain _, fun h => ?_⟩
    exact flat_of_eq (ha := rfl) (hb := hb) (map_eq_of_chain_eq
      (chain_ext_of_flatten (A' := ⟨a.dims, stdChain (d := a.dims) rfl⟩) rfl
        (by rw [h, flatten_stdChain])))
  rw [hflat, flatten_eq_one_iff]
  refine ⟨fun h e => ?_, fun h e => ?_⟩
  · have hc := h e
    rw [coordFlip_comp_apply, key] at hc
    simpa using congrArg Fin.val hc
  · rw [coordFlip_comp_apply, key]
    exact Fin.ext (by simpa using h e)

/-- **A merge is flat** — it keeps the event order (`pos_coordMap_of_W`). -/
theorem flat_of_W {a b : Ch K} {u : a ⟶ b} (h : W K u) : Flat u :=
  (flat_iff_pos u).mpr fun e => pos_coordMap_of_W h e

/-- **Flatness in crossing coordinates** — the one place `W` meets the crossing permutation. -/
theorem crossPerm_eq_one_iff_flat {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (u : a ⟶ b) :
    crossPerm h u = 1 ↔ Flat u := by
  rw [flat_iff_pos]
  refine ⟨fun h1 e => ?_, fun h1 => Equiv.ext fun x => ?_⟩
  · have hv := crossPerm_val h u (e := e) (x := strand a.dims h e) (strand_val a.dims h e)
    rw [h1, Equiv.Perm.one_apply, strand_val] at hv
    exact hv.symm
  · obtain ⟨e, rfl⟩ := (strand a.dims h).surjective x
    rw [crossPerm_strand, Equiv.Perm.one_apply]
    exact Fin.ext ((strand_val _ _ _).trans ((h1 e).trans (strand_val a.dims h e).symm))

end ChainCat
