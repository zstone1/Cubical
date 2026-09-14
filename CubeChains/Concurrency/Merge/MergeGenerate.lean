import CubeChains.Concurrency.Merge.Flat

/-!
# Concurrency/Merge/MergeGenerate — the geometric reading of `W`

`W_iff_flat`: a composite of bead merges is exactly a refinement that reorders nothing.  Flatness
is inherited by factors (`flat_comp_iff`), so a flat refinement splits into flat pieces; cutting at
any junction the target does not separate and factoring (`exists_factor`) peels one bead off, and
induction on the bead count exhausts it.  At codimension one the middle map is forced, a chain
morphism being its crossing permutation — the one step that reads coordinates.
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace ChainCat

variable {K : BPSet}

/-! ### A flat refinement of codimension one is a merge -/

/-- **The middle map is forced.**  A chain morphism is its crossing permutation, and the canonical
merge crosses nothing — so it is the only codimension-one refinement that reorders nothing. -/
theorem merge_of_flat_of_codim_one {a b : Ch K} {f : a ⟶ b} (hcod : codim f = 1)
    (hflat : Flat f) : merge K f := by
  have h1 : crossPerm rfl f = 1 := (crossPerm_eq_one_iff_flat rfl f).mpr hflat
  obtain ⟨l, r, p, q, hb, ha⟩ := (codim_eq_one_iff f).mp hcod
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  subst ha
  subst hb
  have hz : crossPerm rfl (zHom (Hom.φ f)) = crossPerm rfl f := Equiv.ext fun _ => rfl
  have hm : crossPerm rfl (mergeHom l r p q) = 1 :=
    crossPerm_eq_one_of_W rfl (W_mergeHom l r p q)
  have heq : zHom (Hom.φ f) = mergeHom l r p q :=
    hom_ext_of_crossPerm (h := rfl) (by rw [hz, h1, hm]; rfl)
  have hfφ : Hom.φ f = splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) := congrArg Hom.φ heq
  have hw : splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)) ≫ bm = am := by
    rw [← hfφ]; exact f.w
  rw [show f = ⟨splicePhi l r p q (cubeMerge (p : ℕ) (q : ℕ)), hw⟩ from hom_ext' hfφ]
  exact ⟨spliceCutAt hw, rfl⟩

/-! ### Peeling one merge -/

/-- **Peeling.**  A flat refinement that loses a bead factors as a bead merge followed by a flat
refinement losing one bead fewer: cut at a junction the target does not separate, and
`exists_factor` supplies the two legs, flat because flatness is inherited by factors. -/
theorem exists_merge_factor {a b : Ch K} (f : a ⟶ b) (h1 : Flat f)
    (hlt : b.dims.length < a.dims.length) :
    ∃ (c : Ch K) (g : a ⟶ c) (h : c ⟶ b), merge K g ∧ f = g ≫ h ∧
      c.dims.length + 1 = a.dims.length ∧ Flat h := by
  have hsub := boundaries_subset_of_hom f
  have hcardlt : (boundaries b.dims).card < (boundaries a.dims).card := by
    rw [card_boundaries, card_boundaries]; omega
  obtain ⟨t, htd, htd'⟩ := Finset.exists_of_ssubset
    (hsub.ssubset_of_ne fun hh => absurd (congrArg Finset.card hh) (by omega))
  have hdim := dimSum_eq_of_hom f
  have h0 : t ≠ 0 := fun hh => htd' (hh ▸ zero_mem_boundaries b.dims)
  have hlast : t ≠ dimSum a.dims := fun hh =>
    htd' (by rw [hh, hdim]; exact dimSum_mem_boundaries b.dims)
  obtain ⟨l, r, p, q, hadims, hlp⟩ := exists_split_of_mem_boundaries a.dims htd h0 hlast
  have hcut : boundaries a.dims = insert t (boundaries (l ++ (p + q) :: r)) := by
    rw [hadims, boundaries_cut, hlp]
  have hdimc : dimSum a.dims = dimSum (l ++ (p + q) :: r) := by
    rw [hadims]; exact dimSum_cut l r p q
  have hsub1 : boundaries (l ++ (p + q) :: r) ⊆ boundaries a.dims := by
    rw [hcut]; exact Finset.subset_insert _ _
  have hsub2 : boundaries b.dims ⊆ boundaries (l ++ (p + q) :: r) := fun y hy => by
    rcases Finset.mem_insert.mp (hcut ▸ hsub hy) with rfl | hy'
    · exact absurd hy htd'
    · exact hy'
  have hac : Nonempty (zObj a.dims ⟶ zObj (l ++ (p + q) :: r)) :=
    nonempty_hom_iff.mpr ⟨hdimc, hsub1⟩
  have hcb : Nonempty (zObj (l ++ (p + q) :: r) ⟶ zObj b.dims) :=
    nonempty_hom_iff.mpr ⟨hdimc.symm.trans hdim, hsub2⟩
  obtain ⟨g₀, h₀, hgh⟩ := exists_factor hac hcb (zHom (Hom.φ f))
  have hφ0 : Hom.φ g₀ ≫ Hom.φ h₀ = Hom.φ f := by rw [← comp_φ]; exact congrArg Hom.φ hgh
  obtain ⟨φg, φh, hφ⟩ : ∃ (φg : ⋁a.dims ⟶ ⋁(l ++ (p + q) :: r))
      (φh : ⋁(l ++ (p + q) :: r) ⟶ ⋁b.dims), φg ≫ φh = Hom.φ f := ⟨_, _, hφ0⟩
  have hgw : φg ≫ (φh ≫ b.map) = a.map := by rw [← Category.assoc, hφ]; exact f.w
  set c : Ch K := ⟨l ++ (p + q) :: r, φh ≫ b.map⟩ with hcdef
  set g : a ⟶ c := ⟨φg, hgw⟩ with hgdef
  set h : c ⟶ b := ⟨φh, rfl⟩ with hhdef
  have hfgh : f = g ≫ h := hom_ext' (by rw [comp_φ]; exact hφ.symm)
  have hlen : c.dims.length + 1 = a.dims.length := by
    rw [hcdef, hadims]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨hg1, hh1⟩ := (flat_comp_iff g h).mp (by rw [← hfgh]; exact h1)
  refine ⟨c, g, h, merge_of_flat_of_codim_one ?_ hg1, hfgh, hlen, hh1⟩
  rw [codim_eq_length_sub]
  omega

/-! ### What the merges generate -/

/-- **A refinement is a merge exactly when it reorders nothing** — peeling merges off strictly
shortens the dimension list, so the induction terminates at an endomorphism, the identity. -/
theorem W_iff_flat {a b : Ch K} (f : a ⟶ b) : W K f ↔ Flat f := by
  refine ⟨flat_of_W, fun h1 => ?_⟩
  generalize hn : a.dims.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    rcases Nat.lt_or_ge b.dims.length a.dims.length with hlt | hge
    · obtain ⟨c, u, v, hu, huv, hc, hv⟩ := exists_merge_factor f h1 hlt
      rw [huv]
      exact (W K).comp_mem u v (merge_le_W K u hu)
        (ih c.dims.length (by omega) v hv rfl)
    · obtain rfl : a = b :=
        eq_of_hom_of_dims_length_eq f (Nat.le_antisymm hge (dims_length_le_of_hom f))
      rw [endo_eq_id f]
      exact MorphismProperty.id_mem _ a

/-- Flatness in crossing coordinates, at the class — the interface to `Machinery/Braid`. -/
theorem W_iff_crossPerm_eq_one {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    W K f ↔ crossPerm h f = 1 :=
  (W_iff_flat f).trans (crossPerm_eq_one_iff_flat h f).symm

/-! ### Everything is a pullback from `Ch Zbp`

Flatness is an equation between wedge maps, so `pushforward` neither creates nor destroys a
member. -/

theorem W_inverseImage {K L : BPSet} (g : K ⟶ L) : W K = (W L).inverseImage (pushforward g) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    (W_iff_flat f).trans (W_iff_flat ((pushforward g).map f)).symm

/-- **The class lives on the serial wedges.** -/
theorem W_eq_inverseImage_toChZ (X : BPSet) : W X = (W Zbp).inverseImage (toChZ X) :=
  W_inverseImage _

/-- **The generators are the codimension-one members of the class they generate.** -/
theorem merge_iff {a b : Ch K} (f : a ⟶ b) : merge K f ↔ W K f ∧ codim f = 1 :=
  ⟨fun h => ⟨merge_le_W K f h, codim_eq_one_of_merge K h⟩,
    fun ⟨hW, hc⟩ => merge_of_flat_of_codim_one hc (flat_of_W hW)⟩

/-! ### The class respects isomorphisms

A chain isomorphism is an identity: it cannot change the bead count either way, and `Ch K` has no
non-trivial endomorphisms. -/

theorem eq_of_isIso {a b : Ch K} (f : a ⟶ b) [IsIso f] : a = b :=
  ChainCat.skeletal K ⟨asIso f⟩

instance respectsIso_W (K : BPSet) : (W K).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.id_comp])
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.comp_id])

end ChainCat
