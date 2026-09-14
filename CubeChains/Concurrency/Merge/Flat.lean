import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Concurrency.Merge.MergeBraid

/-!
# Concurrency/Merge/Flat — the refinements that reorder nothing

Read a refinement in the **standard chain** of its target (`stdChain`, the reading of a shape that
fires the coordinates in their own order) and it becomes a chain of the cube on the source's shape,
whose firing order is the crossing permutation inverted (`crossPerm_mul_flatten`).  `Flat u` says
that reading *is* the source's standard chain.

So flatness and "crosses nothing" are one fact (`crossPerm_eq_one_iff_flat`), and a composite is
flat exactly when both legs are (`flat_comp_iff`), because a coarsening of a chain of a cube is
pinned by its shape.  Behind all of it is the one geometric lemma `inversions_flatten_subset`: a
coarsening only ever *removes* an out-of-order pair.
-/

open CategoryTheory CubeChains CubeChain BPSet StdCube

namespace ChainCat

variable {K : BPSet}

/-- A chain of a cube is its map: the shape being fixed, the object equation is the map
equation. -/
theorem map_eq_of_chain_eq {N : ℕ} {d : List ℕ+} {χ χ' : ⋁d ⟶ □N}
    (h : (⟨d, χ⟩ : Ch (□N)) = ⟨d, χ'⟩) : χ = χ' := by
  obtain ⟨hd, hmap⟩ := ChainCat.Obj.eq_mk_of_eq h
  rw [Subsingleton.elim hd rfl] at hmap
  simpa using hmap

/-- A refinement is **flat** when it carries the standard chain of its target back to the standard
chain of its source — it reorders nothing.  The count is determined by the source; quantifying it
keeps the statement a bare equation of wedge maps, which is what makes flatness transport along any
relabelling of the two classifying maps. -/
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

/-- **Flatness is "crosses nothing".**  A refinement read in the target's standard chain is a chain
of the cube whose firing order is the crossing permutation, inverted; it is the source's standard
chain exactly when that order is trivial. -/
theorem crossPerm_eq_one_iff_flat {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (u : a ⟶ b) :
    crossPerm h u = 1 ↔ Flat u := by
  have hb : dimSum b.dims = N := tgtStrands u h
  have key := flatten_comp_stdChain h u hb
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rw [h1, inv_one] at key
    exact flat_of_eq (ha := h) (hb := hb)
      (map_eq_of_chain_eq (chain_ext_of_flatten rfl (key.trans (flatten_stdChain h).symm)))
  · rw [h1 h hb, flatten_stdChain] at key
    exact inv_eq_one.mp key.symm

/-- **A merge is flat** — it crosses nothing. -/
theorem flat_of_W {a b : Ch K} {u : a ⟶ b} (h : W K u) : Flat u :=
  (crossPerm_eq_one_iff_flat rfl u).mp (crossPerm_eq_one_of_W rfl h)

/-- **A coarsening is realised between the standard chains** — `exists_crossPerm_eq_one_of_coarser`,
read as flatness. -/
theorem nonempty_stdChain_hom {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N) (hb : dimSum b = N)
    (hsub : boundaries b ⊆ boundaries a) :
    Nonempty ((⟨a, stdChain ha⟩ : Ch (□N)) ⟶ ⟨b, stdChain hb⟩) :=
  let ⟨v, hv⟩ := exists_crossPerm_eq_one_of_coarser (a := zObj a) (b := zObj b) ha
    ⟨ha.trans hb.symm, hsub⟩
  ⟨⟨Hom.φ (K := Zbp) v, (crossPerm_eq_one_iff_flat ha v).mp hv ha hb⟩⟩

/-- **A composite is flat exactly when both legs are.**  Forwards: the middle chain of a flat
composite is a coarsening of the source's standard chain, and a coarsening is pinned by its shape
(`chain_ext_of_dims`), so it *is* the middle standard chain.  Backwards: the middle standard chain
cancels.  "A crossing is never undone" and "two flat steps stay flat", in one statement and with no
count. -/
theorem flat_comp_iff {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    Flat (f ≫ g) ↔ Flat f ∧ Flat g := by
  have hb : dimSum b.dims = dimSum a.dims := (dimSum_eq_of_hom f).symm
  have hc : dimSum c.dims = dimSum a.dims := (dimSum_eq_of_hom (f ≫ g)).symm
  refine ⟨fun h => ?_, fun ⟨hf, hg⟩ => flat_of_eq (ha := rfl) (hb := hc) ?_⟩
  · have hA : Hom.φ f ≫ (Hom.φ g ≫ stdChain hc) = stdChain (d := a.dims) rfl := by
      rw [← Category.assoc, ← comp_φ]; exact h rfl hc
    have hstep : (⟨a.dims, stdChain (d := a.dims) rfl⟩ : Ch (□(dimSum a.dims)))
        ⟶ (⟨b.dims, Hom.φ g ≫ stdChain hc⟩ : Ch (□(dimSum a.dims))) :=
      ⟨Hom.φ (K := K) f, hA⟩
    have hmid : Hom.φ g ≫ stdChain hc = stdChain hb :=
      map_eq_of_chain_eq (chain_ext_of_dims hstep
        (nonempty_stdChain_hom rfl hb (boundaries_subset_of_hom f)).some rfl)
    exact ⟨flat_of_eq (ha := rfl) (hb := hb) (by rw [← hmid]; exact hA),
      flat_of_eq (ha := hb) (hb := hc) hmid⟩
  · rw [comp_φ, Category.assoc, hg hb hc]
    exact hf rfl hb

end ChainCat
