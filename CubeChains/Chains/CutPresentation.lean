import CubeChains.Chains.Heights
import CubeChains.Foundations.CutGradedPresentation

/-!
# Chains/CutPresentation — `Ch Zbp` presented by its bead cuts

Generators the codimension-one refinements, relations the codimension-two ones.  This is the input
`Chains/LiftPresentation` transports to `Ch K`, not a rival to the Garside and Artin presentations
of the vertex monoids.

Everything rests on **unique factorisation through an intermediate shape**
(`existsUnique_factorisation`).  The second factor enumerates each bead of the middle shape in the
order the composite imposes on it (`Finset.orderEmbOfFin`), and the first is what is left; the two
are pinned because a bijection of events monotone for the event order is the identity.
-/

open CategoryTheory Equiv BPSet CubeChain CubeChains

namespace ChainCat

open CubeChains

variable {a m b : Ch Zbp}

/-! ## Uniqueness

Inside a bead of `m` the second factor preserves the event order, so the order the first factor
imposes on the source is read off the composite; across beads it is the bead order.  Two first
factors therefore differ by a monotone bijection of `beadEvent m.dims`, which is the identity. -/

/-- **The relative order inside a bead of `m` is read off the composite.** -/
private theorem pos_lt_of_factor {f : a ⟶ b} (u : a ⟶ m) (v : m ⟶ b) (huv : u ≫ v = f)
    {p q : beadEvent a.dims} (hb : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1)
    (hlt : pos (coordMap (Hom.φ u) p) < pos (coordMap (Hom.φ u) q)) :
    pos (coordMap (Hom.φ f) p) < pos (coordMap (Hom.φ f) q) := by
  have hcomp : ∀ w, coordMap (Hom.φ f) w = coordMap (Hom.φ v) (coordMap (Hom.φ u) w) := fun w => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  rw [hcomp, hcomp]
  exact coordMap_pos_lt_of_fst_eq (Hom.φ v) hb hlt

/-- **Two factorisations impose the same order on the source.** -/
private theorem lt_of_factor_of_factor {f : a ⟶ b} {u u' : a ⟶ m} {v v' : m ⟶ b}
    (huv : u ≫ v = f) (hu'v' : u' ≫ v' = f) {p q : beadEvent a.dims}
    (hlt : coordMap (Hom.φ u) p < coordMap (Hom.φ u) q) :
    coordMap (Hom.φ u') p < coordMap (Hom.φ u') q := by
  have hp := coordMap_fst_congr (Hom.φ u') (Hom.φ u) p
  have hq := coordMap_fst_congr (Hom.φ u') (Hom.φ u) q
  by_cases hbead : (coordMap (Hom.φ u) p).1 = (coordMap (Hom.φ u) q).1
  · have hf := pos_lt_of_factor u v huv hbead hlt
    rcases lt_trichotomy (coordMap (Hom.φ u') p) (coordMap (Hom.φ u') q) with h | h | h
    · exact h
    · exact absurd (congrArg (coordMap (Hom.φ u)) ((coordMapEquiv (Hom.φ u')).injective h))
        (ne_of_lt hlt)
    · exact absurd (pos_lt_of_factor u' v' hu'v' (by rw [hp, hq, hbead]) h) (asymm hf)
  · refine pos_lt_of_fst_lt ?_
    rw [hp, hq]
    exact lt_of_le_of_ne (fst_le_of_pos_lt hlt) fun hc => hbead (Fin.ext hc)

/-- **The two factors are determined.**  A bijection of events monotone for the event order
preserves the flattening (`pos_eq_of_monotone`), hence is the identity. -/
theorem factor_ext {f : a ⟶ b} {g g' : a ⟶ m} {e e' : m ⟶ b}
    (h : g ≫ e = f) (h' : g' ≫ e' = f) : g = g' ∧ e = e' := by
  have hmono : Monotone ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))) := by
    intro x y hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · have hx : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm x) = x :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply x
      have hy : coordMap (Hom.φ g) ((coordMapEquiv (Hom.φ g)).symm y) = y :=
        (coordMapEquiv (Hom.φ g)).apply_symm_apply y
      exact le_of_lt (lt_of_factor_of_factor h h' (by rw [hx, hy]; exact hlt))
  have hGG : coordMapEquiv (Hom.φ g) = coordMapEquiv (Hom.φ g') := by
    refine Equiv.ext fun p => ?_
    have hp := pos_eq_of_monotone hmono
      ((coordMapEquiv (Hom.φ g)).symm.trans (coordMapEquiv (Hom.φ g'))).bijective
      (coordMapEquiv (Hom.φ g) p)
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hp
    exact (pos.injective (Fin.ext hp)).symm
  have hgg : ∀ p, coordMap (Hom.φ g) p = coordMap (Hom.φ g') p := Equiv.ext_iff.mp hGG
  have hv : ∀ (u : a ⟶ m) (v : m ⟶ b), u ≫ v = f → ∀ p,
      coordMap (Hom.φ v) (coordMap (Hom.φ u) p) = coordMap (Hom.φ f) p := fun u v huv p => by
    rw [← huv, comp_φ, coordMap_comp, Function.comp_apply]
  refine ⟨hom_ext' (wedgeHom_ext hGG), hom_ext' (wedgeHom_ext (Equiv.ext fun y => ?_))⟩
  obtain ⟨p, rfl⟩ := (coordMapEquiv (Hom.φ g)).surjective y
  show coordMap (Hom.φ e) (coordMap (Hom.φ g) p) = coordMap (Hom.φ e') (coordMap (Hom.φ g) p)
  rw [hv g e h, hgg p, hv g' e' h']

/-- Two factorisations through the same shape are the same factorisation. -/
theorem factorisation_eq {f : a ⟶ b} (p q : Factorisation f) (hp : p.mid = m) (hq : q.mid = m) :
    p = q := by
  obtain ⟨mp, gp, ep, hcp⟩ := p
  obtain ⟨mq, gq, e₂, hcq⟩ := q
  dsimp only at hp hq
  subst hp
  subst hq
  obtain ⟨rfl, rfl⟩ := factor_ext hcp hcq
  rfl

/-! ## Existence

The second factor sends the `k`-th event of the bead `j` of `m` to the `k`-th smallest event of
`b` in the image, under the composite, of the events sitting in that bead. -/

/-- **Unique factorisation through an intermediate shape.**  Once `a ⟶ m ⟶ b` is possible at all,
every refinement `a ⟶ b` factors through `m` in exactly one way. -/
theorem existsUnique_factorisation (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b))
    (f : a ⟶ b) : ∃! p : Factorisation f, p.mid = m := by
  obtain ⟨h₁, hb₁⟩ := nonempty_wedgeHom_iff_coarser.mp (ham.map Hom.φ)
  obtain ⟨h₂, hb₂⟩ := nonempty_wedgeHom_iff_coarser.mp (hmb.map Hom.φ)
  obtain ⟨u, v, hu, hv, huv⟩ :=
    exists_isShuffle_factor hb₁ hb₂ (isShuffle_coordMapEquiv (Hom.φ f))
  obtain ⟨γ, hγ⟩ := exists_coordMapEquiv_eq hu
  obtain ⟨ε, hε⟩ := exists_coordMapEquiv_eq hv
  have hcomp : (Hom.mk γ (Subsingleton.elim _ _) : a ⟶ m)
      ≫ (Hom.mk ε (Subsingleton.elim _ _) : m ⟶ b) = f := by
    refine hom_ext' (wedgeHom_ext (Equiv.ext fun p => ?_))
    change coordMap (γ ≫ ε) p = coordMap (Hom.φ f) p
    rw [coordMap_comp, Function.comp_apply,
      show coordMap γ p = u p from Equiv.ext_iff.mp hγ p,
      show coordMap ε (u p) = v (u p) from Equiv.ext_iff.mp hε (u p)]
    exact huv p
  exact ⟨⟨m, _, _, hcomp⟩, rfl, fun p hp => factorisation_eq p ⟨m, _, _, hcomp⟩ hp rfl⟩

/-! ## The cut grading -/

private theorem eq_insert_of_sdiff_singleton {A B : Finset ℕ} (hsub : B ⊆ A) {t : ℕ}
    (h : A \ B = {t}) : A = insert t B := by
  ext x
  constructor
  · intro hx
    by_cases hb : x ∈ B
    · exact Finset.mem_insert_of_mem hb
    · exact Finset.mem_insert.mpr
        (Or.inl (Finset.mem_singleton.mp (h ▸ Finset.mem_sdiff.mpr ⟨hx, hb⟩)))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hb
    · exact (Finset.mem_sdiff.mp (h ▸ Finset.mem_singleton_self x)).1
    · exact hsub hb

private theorem sdiff_insert_self {B : Finset ℕ} {t : ℕ} (ht : t ∉ B) :
    insert t B \ B = {t} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun ⟨hx, hnb⟩ => hx.resolve_right hnb, fun hx => ⟨Or.inl hx, hx ▸ ht⟩⟩

/-- The heights a refinement of serial wedges removes. -/
def cutsOf {a b : Ch Zbp} (_f : a ⟶ b) : Finset ℕ := heights a.dims \ heights b.dims

theorem card_cutsOf {a b : Ch Zbp} (f : a ⟶ b) : (cutsOf f).card = codim f := by
  rw [cutsOf, Finset.card_sdiff, Finset.inter_eq_left.mpr (heights_subset_of_hom f),
    card_heights, card_heights, codim_eq_length_sub]
  omega

theorem cutsOf_comp {a b c : Ch Zbp} (f : a ⟶ b) (g : b ⟶ c) :
    cutsOf (f ≫ g) = cutsOf f ∪ cutsOf g := by
  have h1 := heights_subset_of_hom f
  have h2 := heights_subset_of_hom g
  ext x
  simp only [cutsOf, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx, hxc⟩
    by_cases hb : x ∈ heights b.dims
    · exact Or.inr ⟨hb, hxc⟩
    · exact Or.inl ⟨hx, hb⟩
  · rintro (⟨hx, hb⟩ | ⟨hb, hc⟩)
    · exact ⟨hx, fun hc => hb (h2 hc)⟩
    · exact ⟨h1 hb, hc⟩

/-! ## The two intermediate shapes at a height -/

/-- The coarse end, cut once more at a height the refinement removes. -/
private theorem exists_mid_cut {a b : Ch Zbp} (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ m : Ch Zbp, heights m.dims = insert t (heights b.dims)
      ∧ dimSum m.dims = dimSum b.dims := by
  rw [cutsOf, Finset.mem_sdiff] at ht
  have hdim := strandsEq f
  have hle : t ≤ dimSum b.dims := by
    have := le_dimSum_of_mem_heights ht.1
    omega
  obtain ⟨l, r, p, q, hb, hl⟩ := exists_cut_of_notMem_heights b.dims hle ht.2
  exact ⟨zObj (l ++ p :: q :: r), by rw [zObj_dims, hb, heights_cut, hl],
    by rw [zObj_dims, hb]; exact dimSum_cut l r p q⟩

/-- The fine end, with the two beads meeting at that height merged. -/
private theorem exists_mid_merge {a b : Ch Zbp} (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ m : Ch Zbp, heights a.dims = insert t (heights m.dims) ∧ t ∉ heights m.dims
      ∧ dimSum m.dims = dimSum a.dims := by
  rw [cutsOf, Finset.mem_sdiff] at ht
  have h0 : t ≠ 0 := fun h => ht.2 (h ▸ zero_mem_heights _)
  have hlast : t ≠ dimSum a.dims := fun h =>
    ht.2 (by rw [h, strandsEq f]; exact dimSum_mem_heights b.dims)
  obtain ⟨l, r, p, q, ha, hl⟩ := exists_split_of_mem_heights a.dims ht.1 h0 hlast
  refine ⟨zObj (l ++ (p + q) :: r), by rw [zObj_dims, ha, heights_cut, hl], ?_, ?_⟩
  · rw [zObj_dims, ← hl]; exact notMem_heights_cut l r p q
  · rw [zObj_dims, ha]; exact (dimSum_cut l r p q).symm

/-! ## Factoring off a single cut -/

/-- **A refinement splits off its last cut at any height, in exactly one way.** -/
theorem existsUnique_factor_last {a b : Ch Zbp} (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃! p : Factorisation f, cutsOf p.π = {t} := by
  obtain ⟨m, hm, hmd⟩ := exists_mid_cut f ht
  have ht' := Finset.mem_sdiff.mp ht
  have hd := strandsEq f
  have h1 : Nonempty (a ⟶ m) := nonempty_hom_iff.mpr
    ⟨by omega, by rw [hm]; exact Finset.insert_subset ht'.1 (heights_subset_of_hom f)⟩
  have h2 : Nonempty (m ⟶ b) := nonempty_hom_iff.mpr ⟨hmd, hm ▸ Finset.subset_insert _ _⟩
  obtain ⟨p₀, hp₀, huniq⟩ := existsUnique_factorisation h1 h2 f
  refine ⟨p₀, ?_, fun p hp => huniq p ?_⟩
  · simp only [cutsOf, hp₀, hm]
    exact sdiff_insert_self ht'.2
  · exact Obj.eq_of_dims (heights_injective
      ((eq_insert_of_sdiff_singleton (heights_subset_of_hom p.π) hp).trans hm.symm))

/-- **…and its first cut**, the mirror statement: the same factorisation theorem, with the
intermediate shape got by merging instead of cutting. -/
theorem existsUnique_factor_first {a b : Ch Zbp} (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃! p : Factorisation f, cutsOf p.ι = {t} := by
  obtain ⟨m, hm, hnm, hmd⟩ := exists_mid_merge f ht
  have ht' := Finset.mem_sdiff.mp ht
  have hd := strandsEq f
  have hsb : heights b.dims ⊆ heights m.dims := by
    intro x hx
    rcases Finset.mem_insert.mp (hm ▸ heights_subset_of_hom f hx) with rfl | hx'
    · exact absurd hx ht'.2
    · exact hx'
  have h1 : Nonempty (a ⟶ m) := nonempty_hom_iff.mpr
    ⟨hmd.symm, hm ▸ Finset.subset_insert _ _⟩
  have h2 : Nonempty (m ⟶ b) := nonempty_hom_iff.mpr ⟨by omega, hsb⟩
  obtain ⟨p₀, hp₀, huniq⟩ := existsUnique_factorisation h1 h2 f
  refine ⟨p₀, ?_, fun p hp => huniq p ?_⟩
  · simp only [cutsOf, hp₀, hm]
    exact sdiff_insert_self hnm
  · refine Obj.eq_of_dims (heights_injective ?_)
    have hpm := eq_insert_of_sdiff_singleton (heights_subset_of_hom p.ι) hp
    have hnp : t ∉ heights p.mid.dims := (Finset.mem_sdiff.mp (hp ▸ Finset.mem_singleton_self t)).2
    rw [← Finset.erase_insert hnp, ← hpm, hm, Finset.erase_insert hnm]

/-! ## The presentation -/

/-- **The cut grading of `Ch Zbp`.** -/
noncomputable def cutData : CutGraded.Data (Ch Zbp) where
  toGrading := grading Zbp
  cuts := cutsOf
  card_cuts := card_cutsOf
  cuts_comp := cutsOf_comp
  isId_of_codim_eq_zero := fun {a b} f h => by
    obtain rfl : a = b := (codim_eq_zero_iff f).mp h
    exact ⟨rfl, by rw [endo_eq_id f, eqToHom_refl]⟩
  factor_last := fun f _ ht => existsUnique_factor_last f ht

/-- **The same on the opposite category**, where a cut is split off at the front. -/
noncomputable def cutDataOp : CutGraded.Data (Ch Zbp)ᵒᵖ where
  toGrading := (grading Zbp).op
  cuts f := cutsOf f.unop
  card_cuts f := card_cutsOf f.unop
  cuts_comp f g := (cutsOf_comp g.unop f.unop).trans (Finset.union_comm _ _)
  isId_of_codim_eq_zero := fun {A B} F h => by
    obtain ⟨hab, hf⟩ := cutData.isId_of_codim_eq_zero F.unop h
    obtain rfl : A = B := Opposite.unop_injective hab.symm
    exact ⟨rfl, Quiver.Hom.unop_inj (by rw [hf]; rfl)⟩
  factor_last := fun {A B} F t ht => by
    obtain ⟨q, hq, huniq⟩ := existsUnique_factor_first F.unop ht
    refine ⟨(factorisationOpEquiv F).symm q, hq, fun p hp => ?_⟩
    rw [← huniq (factorisationOpEquiv F p) hp, Equiv.symm_apply_apply]

/-- **`Ch Zbp` is presented by its bead cuts.** -/
noncomputable def zPresentation : CategoryTheory.Quotient (CutGraded.rel cutData) ≌ Ch Zbp :=
  CutGraded.presentation cutData

/-- **…and so is its opposite**, which is the form `chPresentation` consumes. -/
noncomputable def zPresentationOp :
    CategoryTheory.Quotient (CutGraded.rel cutDataOp) ≌ (Ch Zbp)ᵒᵖ :=
  CutGraded.presentation cutDataOp

end ChainCat
