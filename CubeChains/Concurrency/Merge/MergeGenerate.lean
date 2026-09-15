import CubeChains.Concurrency.Merge.MergeBraid

/-!
# Concurrency/Merge/MergeGenerate — the geometric reading of `W`

`W_iff_crossPerm_eq_one`: a composite of bead merges is exactly a refinement that crosses nothing.
A refinement is pinned by its crossing permutation, and every coarsening is reached by merges
(`exists_W_of_coarser`), which cross nothing — so the crossing-free refinement of a shape *is* the
merge, and a cut constraining the wedge map alone, it is one for every chain carrying it
(`W_of_zHom`).
-/

open CategoryTheory CubeChains CubeChain BPSet

namespace ChainCat

variable {K : BPSet}

/-! ### Merges see only the wedge map -/

/-- **A cut of the serial wedges is a cut of every chain carrying it** — `CutData` names the wedge
map and the two shapes, nothing else. -/
theorem merge_of_zHom {x y : Ch Zbp} {u : x ⟶ y} (hu : merge Zbp u) {am : ⋁x.dims ⟶ K}
    {m : ⋁y.dims ⟶ K} (hw : u.φ ≫ m = am) :
    merge K (⟨u.φ, hw⟩ : (⟨x.dims, am⟩ : Ch K) ⟶ ⟨y.dims, m⟩) :=
  let ⟨d, hd⟩ := hu
  ⟨⟨d.l, d.r, d.p, d.q, d.w, d.e₁, d.e₂, d.sq⟩, hd⟩

/-- **…and so is a composite of them.** -/
theorem W_of_zHom {x y : Ch Zbp} {u : x ⟶ y} (hu : W Zbp u) :
    ∀ {am : ⋁x.dims ⟶ K} {m : ⋁y.dims ⟶ K} (hw : u.φ ≫ m = am),
      W K (⟨u.φ, hw⟩ : (⟨x.dims, am⟩ : Ch K) ⟶ ⟨y.dims, m⟩) := by
  induction hu with
  | of _ hu => exact fun hw => merge_le_W K _ (merge_of_zHom hu hw)
  | id x =>
      intro am m hw
      obtain rfl : am = m := hw.symm.trans (Category.id_comp m)
      have he : (⟨_, hw⟩ : (⟨x.dims, am⟩ : Ch K) ⟶ ⟨x.dims, am⟩) = 𝟙 (⟨x.dims, am⟩ : Ch K) :=
        hom_ext' rfl
      exact he ▸ (W K).id_mem _
  | @comp_of x y' y s t _ ht ih =>
      intro am m hw
      let g₁ : (⟨x.dims, am⟩ : Ch K) ⟶ ⟨y'.dims, t.φ ≫ m⟩ :=
        ⟨s.φ, (Category.assoc _ _ _).symm.trans hw⟩
      let g₂ : (⟨y'.dims, t.φ ≫ m⟩ : Ch K) ⟶ ⟨y.dims, m⟩ := ⟨t.φ, rfl⟩
      have he : g₁ ≫ g₂ = ⟨_, hw⟩ := hom_ext' rfl
      exact he ▸ (W K).comp_mem g₁ g₂ (ih _) (merge_le_W K _ (merge_of_zHom ht rfl))

/-! ### What the merges generate -/

/-- **A refinement is a merge exactly when it crosses nothing** — both are unique on a hom-set
(`hom_ext_of_crossPerm`), and merges reach every coarsening. -/
theorem W_iff_crossPerm_eq_one {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b) :
    W K f ↔ crossPerm h f = 1 := by
  refine ⟨crossPerm_eq_one_of_W h, fun h0 => ?_⟩
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  have hd : dimSum ad = dimSum bd := dimSum_eq_of_hom f
  have hs : boundaries bd ⊆ boundaries ad := boundaries_subset_of_hom f
  obtain ⟨u, hu⟩ := exists_W_of_coarser _ (a := zObj ad) (b := zObj bd) rfl hd hs
  have hN : dimSum (zObj ad).dims = N := h
  have heq : u = zHom f.φ := hom_ext_of_crossPerm (h := hN)
    ((crossPerm_eq_one_of_W hN hu).trans (h0.symm.trans (crossPerm_zHom h f).symm))
  exact W_of_zHom (heq ▸ hu) f.w

/-- **`W` sees only the wedge map** — the crossing permutation does (`crossPerm_eq_of_φ`), so two
chains on one pair of shapes carrying one wedge map are merges together or not at all. -/
theorem W_iff_of_φ {K K' : BPSet} {da db : List ℕ+} {ma : ⋁da ⟶ K} {mb : ⋁db ⟶ K}
    {ma' : ⋁da ⟶ K'} {mb' : ⋁db ⟶ K'} {f : (⟨da, ma⟩ : Ch K) ⟶ ⟨db, mb⟩}
    {f' : (⟨da, ma'⟩ : Ch K') ⟶ ⟨db, mb'⟩} (hφ : Hom.φ f = Hom.φ f') : W K f ↔ W K' f' :=
  (W_iff_crossPerm_eq_one rfl f).trans
    (Iff.trans (by rw [crossPerm_eq_of_φ rfl hφ]) (W_iff_crossPerm_eq_one rfl f').symm)

/-! ### Everything is a pullback from `Ch Zbp`

The crossing permutation reads the wedge map alone, so `pushforward` neither creates nor destroys a
member. -/

theorem W_inverseImage {K L : BPSet} (g : K ⟶ L) : W K = (W L).inverseImage (pushforward g) :=
  MorphismProperty.ext _ _ fun _ _ _ => W_iff_of_φ rfl

/-- **The class lives on the serial wedges.** -/
theorem W_eq_inverseImage_toChZ (X : BPSet) : W X = (W Zbp).inverseImage (toChZ X) :=
  W_inverseImage _

/-- **The generators are the codimension-one members of the class they generate** — at a cut the
crossing-free refinement is the merge splice, a refinement being its crossing permutation. -/
theorem merge_iff {a b : Ch K} (f : a ⟶ b) : merge K f ↔ W K f ∧ codim f = 1 := by
  refine ⟨fun h => ⟨merge_le_W K f h, codim_eq_one_of_merge K h⟩, fun ⟨hW, hcod⟩ => ?_⟩
  obtain ⟨l, r, p, q, hb, ha⟩ := (codim_eq_one_iff f).mp hcod
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  subst ha
  subst hb
  have hφ : Hom.φ f = Hom.φ (mergeHom l r p q) := congrArg Hom.φ
    (hom_ext_of_crossPerm (x := zObj _) (h := rfl) ((crossPerm_zHom rfl f).trans
      ((crossPerm_eq_one_of_W rfl hW).trans (crossPerm_eq_one_of_W rfl (W_mergeHom l r p q)).symm)))
  have hw : Hom.φ (mergeHom l r p q) ≫ bm = am := hφ ▸ f.w
  rw [show f = ⟨_, hw⟩ from hom_ext' hφ]
  exact merge_of_zHom (merge_mergeHom l r p q) hw

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
