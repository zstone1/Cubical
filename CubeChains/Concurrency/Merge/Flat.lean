import CubeChains.Concurrency.Grading.Coarser

/-!
# Concurrency/Merge/Flat — the refinements that reorder nothing

Read a refinement in the **standard chain** of its target (`stdChain`, the reading of a shape that
fires the coordinates in their own order) and it becomes a chain of the cube on the source's shape;
`Flat u` says that reading *is* the source's standard chain.  On coordinates that is exactly "every
event keeps its rank" (`flat_iff_pos_coordMap`), so flatness is monoidal over the wedge
(`flat_concatHomφ`) and a splice is flat as soon as its middle map is — with `cubeMerge` in the
middle it is, and a merge reorders nothing.

A composite is flat exactly when both legs are (`flat_comp_iff`), because a coarsening of a chain of
a cube is pinned by its shape.  Behind that is the one geometric lemma `inversions_flatten_subset`:
a coarsening only ever *removes* an out-of-order pair.
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

/-- **A chain fires in its own order exactly when it realises the flattening** — `flatten` compares
the coordinate order with the lexicographic one, so it is trivial exactly when the chain flips the
coordinate of rank `i` at its own rank. -/
theorem flatten_eq_one_iff {N : ℕ} {d : List ℕ+} (χ : ⋁d ⟶ □N) :
    flatten (⟨d, χ⟩ : Ch (□N)) = 1 ↔ ∀ e : beadEvent d, (coordFlip χ e : ℕ) = (pos e : ℕ) := by
  refine ⟨fun h e => ?_, fun h => Equiv.ext fun q => Fin.ext ?_⟩
  · have hk := flatten_coordFlip χ e
    rw [h, Equiv.Perm.one_apply] at hk
    exact (congrArg Fin.val hk).trans (strand_val d _ e)
  · rw [Equiv.Perm.one_apply, flatten_val]
    exact (h _).symm.trans (congrArg Fin.val ((coordFlip χ).apply_symm_apply q))

/-- **The standard chain realises the flattening**: it flips the coordinate of rank `i` at rank
`i`.  This is `flatten_stdChain` with the permutation read on events, and the only property of
`stdChain` any flatness argument uses. -/
theorem coordFlip_stdChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (e : beadEvent d) :
    (coordFlip (stdChain hd) e : ℕ) = (pos e : ℕ) :=
  (flatten_eq_one_iff (stdChain hd)).mp (flatten_stdChain hd) e

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

/-- **Flatness on coordinates**: a flat refinement is one that keeps every event's rank.  Both
standard chains realise the flattening, so the equation of maps into the cube *is* that. -/
theorem flat_iff_pos_coordMap {a b : Ch K} (u : a ⟶ b) :
    Flat u ↔ ∀ e : beadEvent a.dims, (pos (coordMap (Hom.φ u) e) : ℕ) = (pos e : ℕ) := by
  have hb : dimSum b.dims = dimSum a.dims := (dimSum_eq_of_hom u).symm
  refine ⟨fun h e => ?_, fun h => flat_of_eq (ha := rfl) (hb := hb) ?_⟩
  · have hk : (coordFlip (Hom.φ u ≫ stdChain hb) e : ℕ)
        = (coordFlip (stdChain (d := a.dims) rfl) e : ℕ) :=
      congrArg (fun χ => (coordFlip χ e : ℕ)) (h rfl hb)
    rwa [coordFlip_comp_apply, coordFlip_stdChain, coordFlip_stdChain] at hk
  · refine map_eq_of_chain_eq (chain_ext_of_flatten (A := ⟨a.dims, Hom.φ u ≫ stdChain hb⟩)
      (A' := ⟨a.dims, stdChain rfl⟩) rfl ?_)
    rw [flatten_stdChain]
    exact (flatten_eq_one_iff _).mpr fun e => by
      rw [coordFlip_comp_apply, coordFlip_stdChain]; exact h e

/-- **The crossing permutation, like flatness, sees only the wedge map**, so pushing a chain
morphism forward to the serial wedges leaves it alone. -/
theorem crossPerm_zHom {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    crossPerm (a := zObj a.dims) (b := zObj b.dims) h (zHom f.φ) = crossPerm h f := rfl

/-- **Flatness is "crosses nothing".**  `crossPerm` compares the two flattenings, so it is trivial
exactly when every event keeps its rank — which is flatness. -/
theorem crossPerm_eq_one_iff_flat {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (u : a ⟶ b) :
    crossPerm h u = 1 ↔ Flat u := by
  rw [flat_iff_pos_coordMap]
  refine ⟨fun h1 e => ?_, fun h1 => Equiv.ext fun x => Fin.ext ?_⟩
  · have hv := crossPerm_val h u (x := strand a.dims h e) (strand_val a.dims h e)
    rw [h1, Equiv.Perm.one_apply, strand_val] at hv
    exact hv.symm
  · have hs : (pos ((strand a.dims h).symm x) : ℕ) = (x : ℕ) :=
      (strand_val a.dims h _).symm.trans (congrArg Fin.val ((strand a.dims h).apply_symm_apply x))
    rw [Equiv.Perm.one_apply, crossPerm_val h u hs.symm, h1]
    exact hs

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

/-! ### Flatness is monoidal over the wedge

`coordMap` is a map of coproducts over `++` (`coordMap_concatHomφ_left`/`_right`) and `pos` shifts
the second block past the first, so a concatenation keeps every rank exactly when both halves do.
A splice is a concatenation twice over (`zHom_splicePhi_eq`, `zHom_spliceNil_eq`), so it is flat as
soon as its middle staircase is. -/

/-- **A concatenation is flat exactly when both halves are.** -/
theorem flat_concatHomφ {A A' B B' : List ℕ+} {f : zObj A ⟶ zObj A'} {g : zObj B ⟶ zObj B'}
    (hf : Flat f) (hg : Flat g) :
    Flat (zHom (concatHomφ f g) : zObj (A ++ B) ⟶ zObj (A' ++ B')) := by
  rw [flat_iff_pos_coordMap] at hf hg
  refine (flat_iff_pos_coordMap _).mpr ?_
  change ∀ e : beadEvent ((zObj A).dims ++ (zObj B).dims),
    (pos (coordMap (concatHomφ f g) e) : ℕ) = (pos e : ℕ)
  refine eventAppendCases (fun x => ?_) (fun y => ?_)
  · rw [coordMap_concatHomφ_left, pos_eventInl, pos_eventInl]
    exact hf x
  · rw [coordMap_concatHomφ_right, pos_eventInr, pos_eventInr, dimSum_eq_of_hom f]
    exact congrArg (dimSum (zObj A').dims + ·) (hg y)

/-- **A splice is flat as soon as its middle staircase is** — the beads flanking the cut are
carried by identities. -/
theorem flat_splicePhi (l r : List ℕ+) (p q : ℕ+)
    {w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)} (hw : Flat (zHom (pairMerge p q w))) :
    Flat (zHom (splicePhi l r p q w)) := by
  have hmid : Flat (zHom (spliceNil r p q w)) := by
    intro N ha hb
    rw [zHom_φ, spliceNil_eq_concat]
    exact flat_concatHomφ (A := [p, q]) (B := r) hw (flat_id _) ha hb
  intro N ha hb
  rw [zHom_φ, splicePhi_eq_concat]
  exact flat_concatHomφ (A := l) (B := p :: q :: r) (flat_id _) hmid ha hb

/-- **The merge staircase is flat** — `pos_coordMap_pairMerge_cubeMerge`. -/
theorem flat_pairMerge_cubeMerge (p q : ℕ+) :
    Flat (zHom (pairMerge p q (cubeMerge (p : ℕ) (q : ℕ)))) :=
  (flat_iff_pos_coordMap _).mpr (pos_coordMap_pairMerge_cubeMerge p q)

/-- **A generator is flat** — by `eq_splicePhi_of_sq` it *is* a splice, and its middle map is the
merge staircase. -/
theorem flat_of_merge {a b : Ch K} {f : a ⟶ b} (hm : merge K f) : Flat f := by
  obtain ⟨d, hw⟩ := hm
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hsrc := d.src_dims
  have htgt := d.tgt_dims
  obtain ⟨l, r, p, q, w, e₁, e₂, sq⟩ := d
  dsimp only at hsrc htgt hw e₁ e₂ ⊢
  subst hsrc
  subst htgt
  intro N ha hb
  rw [show Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) from
    (eq_splicePhi_of_sq sq).trans (congrArg _ hw)]
  exact flat_splicePhi l r p q (flat_pairMerge_cubeMerge p q) ha hb

/-- **A merge is flat** — the generators are, and flatness is closed under composition. -/
theorem flat_of_W {a b : Ch K} {u : a ⟶ b} (h : W K u) : Flat u := by
  induction h with
  | of _ hm => exact flat_of_merge hm
  | id x => exact flat_id x
  | comp_of u v _ hv ih => exact (flat_comp_iff u v).mpr ⟨ih, flat_of_merge hv⟩

/-- **A merge crosses nothing** — `flat_of_W` in braid vocabulary. -/
theorem crossPerm_eq_one_of_W {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) {f : a ⟶ b}
    (hf : W K f) : crossPerm h f = 1 :=
  (crossPerm_eq_one_iff_flat h f).mpr (flat_of_W hf)

/-- **…so a merge keeps the event order** — `flat_of_W`, read on positions. -/
theorem pos_coordMap_of_W {a b : Ch K} {f : a ⟶ b} (hf : W K f) (e : beadEvent a.dims) :
    (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) :=
  (flat_iff_pos_coordMap f).mp (flat_of_W hf) e

end ChainCat
