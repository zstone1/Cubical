import CubeChains.Chains.Heights
import CubeChains.Chains.MergeGenerate
import CubeChains.Foundations.CutGradedPresentation
import CubeChains.Foundations.SortPerm
import Mathlib.Data.Prod.Lex

/-!
# Chains/CutPresentation — `Ch Zbp` presented by its bead cuts

Generators the codimension-one refinements, relations the codimension-two ones.  This is the input
`Chains/LiftPresentation` transports to `Ch K`, not a rival to the Garside and Artin presentations
of the vertex monoids.

Everything rests on **unique factorisation through an intermediate shape**
(`existsUnique_factorisation`): a refinement `a ⟶ b` factors through any `m` between them in
exactly one way.  Read on `Fin N` that is the tower of parabolic coset representatives, and the
second factor is a sort (`Tuple.sort`) by the middle shape's beads.
-/

open CategoryTheory Equiv BPSet CubeChain CubeChains

namespace ChainCat

open CubeChains

variable {N : ℕ}

local notation "dm[" d "]" => List.map (fun c : ℕ+ => (c : ℕ)) d
local notation "blk[" d "]" => blockOfPos (List.map (fun c : ℕ+ => (c : ℕ)) d)

private theorem perm_apply_inv (π : Perm (Fin N)) (z : Fin N) : π (π⁻¹ z) = z :=
  Equiv.apply_symm_apply π z

private theorem perm_inv_apply (π : Perm (Fin N)) (z : Fin N) : π⁻¹ (π z) = z :=
  Equiv.symm_apply_apply π z

/-! ## Sorting by the middle shape

The second factor of a factorisation through `m` enumerates the strands in the order "`m`-bead of
the source first, then position" — a `Tuple.sort`.  The first factor is what is left. -/

/-- The sorting key: the `m`-bead of a strand's source under `σ`, then the strand. -/
private def midKey (m : List ℕ+) (σ : Perm (Fin N)) (x : Fin N) : ℕ ×ₗ ℕ :=
  toLex (blk[m] ((σ⁻¹ x : Fin N) : ℕ), (x : ℕ))

private theorem midKey_injective (m : List ℕ+) (σ : Perm (Fin N)) :
    Function.Injective (midKey m σ) := fun _ _ h =>
  Fin.ext (congrArg (fun z => (ofLex z).2) h)

/-- **The second factor of a factorisation through `m`.** -/
private noncomputable def midPerm (m : List ℕ+) (σ : Perm (Fin N)) : Perm (Fin N) :=
  Tuple.sort (midKey m σ)

private theorem midKey_midPerm_strictMono (m : List ℕ+) (σ : Perm (Fin N)) :
    StrictMono (midKey m σ ∘ midPerm m σ) :=
  (Tuple.monotone_sort _).strictMono_of_injective
    ((midKey_injective m σ).comp (midPerm m σ).injective)

/-- **The sort respects the middle shape's beads**: it carries each bead of `m` onto the strands
whose `σ`-source lies in that bead — both sides are monotone with the same fibre sizes. -/
private theorem blk_midPerm (m : List ℕ+) (σ : Perm (Fin N)) (x : Fin N) :
    blk[m] ((σ⁻¹ (midPerm m σ x) : Fin N) : ℕ) = blk[m] ((x : ℕ)) := by
  have hu : Monotone fun z : Fin N => blk[m] ((z : ℕ)) := fun _ _ h => blockOfPos_monotone _ h
  have hmono : Monotone ((fun z : Fin N => blk[m] ((z : ℕ))) ∘ (σ⁻¹ * midPerm m σ)) :=
    fun _ _ hyz => Prod.Lex.monotone_fst_ofLex ((midKey_midPerm_strictMono m σ).monotone hyz)
  exact congrFun (comp_perm_eq_of_monotone hu (σ⁻¹ * midPerm m σ) hmono) x

/-- The sort rises inside each bead of `m`. -/
private theorem midPerm_lt (m : List ℕ+) (σ : Perm (Fin N)) {x y : Fin N}
    (hxy : blk[m] ((x : ℕ)) = blk[m] ((y : ℕ))) (hlt : x < y) :
    midPerm m σ x < midPerm m σ y := by
  have h := midKey_midPerm_strictMono m σ hlt
  rw [Function.comp_apply, Function.comp_apply, midKey, midKey,
    Prod.Lex.toLex_lt_toLex'] at h
  exact Fin.lt_def.mpr (h.2 (by rw [blk_midPerm, blk_midPerm, hxy]))

/-- The sort preserves the beads of any shape the middle one refines. -/
private theorem midPerm_mem_parabolic (m bd : List ℕ+) (σ : Perm (Fin N))
    (hcmb : ∀ x y : Fin N, blk[m] ((x : ℕ)) = blk[m] ((y : ℕ)) →
      blk[bd] ((x : ℕ)) = blk[bd] ((y : ℕ)))
    (hσ : σ ∈ parabolic N dm[bd]) : midPerm m σ ∈ parabolic N dm[bd] := by
  intro x
  have h1 := hcmb (σ⁻¹ (midPerm m σ x)) x (blk_midPerm m σ x)
  have h2 := mem_parabolic.mp hσ (σ⁻¹ (midPerm m σ x))
  rw [perm_apply_inv] at h2
  rw [← h1, ← h2]

/-- What is left of `σ` after the sort preserves every bead of `m`. -/
private theorem inv_midPerm_mul_mem_parabolic (m : List ℕ+) (σ : Perm (Fin N)) :
    (midPerm m σ)⁻¹ * σ ∈ parabolic N dm[m] := by
  intro x
  have h := blk_midPerm m σ ((midPerm m σ)⁻¹ (σ x))
  rw [perm_apply_inv, perm_inv_apply] at h
  exact h.symm

/-- …and it rises inside every bead of the source. -/
private theorem inv_midPerm_mul_lt (m ad : List ℕ+) (σ : Perm (Fin N))
    (hcam : ∀ x y : Fin N, blk[ad] ((x : ℕ)) = blk[ad] ((y : ℕ)) →
      blk[m] ((x : ℕ)) = blk[m] ((y : ℕ)))
    (hσasc : ∀ x y : Fin N, blk[ad] ((x : ℕ)) = blk[ad] ((y : ℕ)) → x < y → σ x < σ y)
    {x y : Fin N} (hxy : blk[ad] ((x : ℕ)) = blk[ad] ((y : ℕ))) (hlt : x < y) :
    ((midPerm m σ)⁻¹ * σ) x < ((midPerm m σ)⁻¹ * σ) y := by
  have hkey : ∀ z : Fin N, midKey m σ (midPerm m σ (((midPerm m σ)⁻¹ * σ) z))
      = toLex (blk[m] ((z : ℕ)), ((σ z : Fin N) : ℕ)) := by
    intro z
    rw [show midPerm m σ (((midPerm m σ)⁻¹ * σ) z) = σ z from perm_apply_inv _ _, midKey,
      perm_inv_apply]
  refine (midKey_midPerm_strictMono m σ).lt_iff_lt.mp ?_
  rw [Function.comp_apply, Function.comp_apply, hkey, hkey, Prod.Lex.toLex_lt_toLex',
    hcam x y hxy]
  exact ⟨le_rfl, fun _ => Fin.lt_def.mp (hσasc x y hxy hlt)⟩

/-- **A permutation preserving each bead of `m` and rising inside them is the identity.** -/
theorem perm_eq_one_of_parabolic (m : List ℕ+) {γ : Perm (Fin N)}
    (hpar : γ ∈ parabolic N dm[m])
    (hasc : ∀ x y : Fin N, blk[m] ((x : ℕ)) = blk[m] ((y : ℕ)) → x < y → γ x < γ y) : γ = 1 := by
  have hval : ∀ z : Fin N, midKey m (1 : Perm (Fin N)) z = toLex (blk[m] ((z : ℕ)), (z : ℕ)) :=
    fun _ => rfl
  refine Tuple.perm_eq_of_monotone (midKey_injective m 1) (σ := γ) (τ := 1) ?_ ?_
  · intro x y hxy
    rw [Function.comp_apply, Function.comp_apply, hval, hval, Prod.Lex.toLex_le_toLex',
      mem_parabolic.mp hpar x, mem_parabolic.mp hpar y]
    refine ⟨blockOfPos_monotone _ (Fin.le_def.mp hxy), fun heq => ?_⟩
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact Fin.le_def.mp (hasc x y heq hlt).le
  · intro x y hxy
    rw [Function.comp_apply, Function.comp_apply]
    change midKey m (1 : Perm (Fin N)) x ≤ midKey m (1 : Perm (Fin N)) y
    rw [hval, hval, Prod.Lex.toLex_le_toLex']
    exact ⟨blockOfPos_monotone _ (Fin.le_def.mp hxy), fun _ => Fin.le_def.mp hxy⟩

/-! ## Unique factorisation through an intermediate shape -/

variable {a m b : Ch Zbp}

/-- **The relative order inside a bead of `m` is read off the composite.**  The second factor rises
inside the beads of `m`, so it neither creates nor destroys an inversion there. -/
private theorem lt_iff_of_factor (ha : dimSum a.dims = N) (hm : dimSum m.dims = N)
    {f : a ⟶ b} (u : a ⟶ m) (w : m ⟶ b) (huw : u ≫ w = f) {x y : Fin N}
    (hxy : blk[m.dims] (((crossPermAt ha u) x : Fin N) : ℕ)
      = blk[m.dims] (((crossPermAt ha u) y : Fin N) : ℕ)) :
    (crossPermAt ha u x < crossPermAt ha u y ↔ crossPermAt ha f x < crossPermAt ha f y) := by
  have hmul : ∀ z : Fin N, crossPermAt ha f z = crossPermAt hm w (crossPermAt ha u z) := by
    intro z
    rw [← huw, crossPermAt_comp ha hm u w]
    rfl
  have hfwd : ∀ p q : Fin N, blk[m.dims] (((crossPermAt ha u) p : Fin N) : ℕ)
      = blk[m.dims] (((crossPermAt ha u) q : Fin N) : ℕ) →
      crossPermAt ha u p < crossPermAt ha u q → crossPermAt ha f p < crossPermAt ha f q := by
    intro p q hb hlt
    rw [hmul, hmul]
    exact crossPermAt_lt hm w hb hlt
  refine ⟨hfwd x y hxy, fun hlt => ?_⟩
  rcases lt_trichotomy (crossPermAt ha u x) (crossPermAt ha u y) with hc | hc | hc
  · exact hc
  · exact absurd (congrArg (crossPermAt ha f) ((crossPermAt ha u).injective hc)) (ne_of_lt hlt)
  · exact absurd (hfwd y x hxy.symm hc) (asymm hlt)

/-- **The two factors are determined.**  Two factorisations through the same shape induce the same
order inside each of its beads, so their first factors differ by the identity. -/
theorem factor_ext (ha : dimSum a.dims = N) (hm : dimSum m.dims = N) {f : a ⟶ b}
    {g g' : a ⟶ m} {e e' : m ⟶ b} (h : g ≫ e = f) (h' : g' ≫ e' = f) : g = g' ∧ e = e' := by
  have hgpar := crossPermAt_mem_parabolic ha g
  have hg'par := crossPermAt_mem_parabolic ha g'
  have hgg : crossPermAt ha g = crossPermAt ha g' := by
    refine (mul_inv_eq_one.mp (perm_eq_one_of_parabolic m.dims
      (mul_mem hg'par (inv_mem hgpar)) ?_)).symm
    intro x y hxy hlt
    have hux : crossPermAt ha g ((crossPermAt ha g)⁻¹ x) = x := perm_apply_inv _ _
    have hvy : crossPermAt ha g ((crossPermAt ha g)⁻¹ y) = y := perm_apply_inv _ _
    have hbu : blk[m.dims] (((crossPermAt ha g) ((crossPermAt ha g)⁻¹ x) : Fin N) : ℕ)
        = blk[m.dims] (((crossPermAt ha g) ((crossPermAt ha g)⁻¹ y) : Fin N) : ℕ) := by
      rw [hux, hvy]; exact hxy
    have hbu' : blk[m.dims] (((crossPermAt ha g') ((crossPermAt ha g)⁻¹ x) : Fin N) : ℕ)
        = blk[m.dims] (((crossPermAt ha g') ((crossPermAt ha g)⁻¹ y) : Fin N) : ℕ) := by
      rw [mem_parabolic.mp hg'par ((crossPermAt ha g)⁻¹ x),
        mem_parabolic.mp hg'par ((crossPermAt ha g)⁻¹ y),
        ← mem_parabolic.mp hgpar ((crossPermAt ha g)⁻¹ x),
        ← mem_parabolic.mp hgpar ((crossPermAt ha g)⁻¹ y), hux, hvy]
      exact hxy
    exact (lt_iff_of_factor ha hm g' e' h' hbu').mpr
      ((lt_iff_of_factor ha hm g e h hbu).mp (by rw [hux, hvy]; exact hlt))
  have hg : g = g' := crossPermAt_injective ha hgg
  refine ⟨hg, crossPermAt_injective hm (mul_right_cancel (b := crossPermAt ha g) ?_)⟩
  change crossPermAt hm e * crossPermAt ha g = crossPermAt hm e' * crossPermAt ha g
  rw [← crossPermAt_comp ha hm, h, hgg, ← crossPermAt_comp ha hm, h']

/-- Two factorisations through the same shape are the same factorisation. -/
theorem factorisation_eq (ha : dimSum a.dims = N) (hm : dimSum m.dims = N) {f : a ⟶ b}
    (p q : Factorisation f) (hp : p.mid = m) (hq : q.mid = m) : p = q := by
  obtain ⟨mp, gp, ep, hcp⟩ := p
  obtain ⟨mq, gq, e₂, hcq⟩ := q
  dsimp only at hp hq
  subst hp
  subst hq
  obtain ⟨rfl, rfl⟩ := factor_ext ha hm hcp hcq
  rfl

/-- **Unique factorisation through an intermediate shape.**  Once `a ⟶ m ⟶ b` is possible at all,
every refinement `a ⟶ b` factors through `m` in exactly one way. -/
theorem existsUnique_factorisation (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b))
    (f : a ⟶ b) : ∃! p : Factorisation f, p.mid = m := by
  obtain ⟨hdam, hsam⟩ := nonempty_hom_iff.mp ham
  obtain ⟨hdmb, hsmb⟩ := nonempty_hom_iff.mp hmb
  have ha : dimSum a.dims = dimSum a.dims := rfl
  have hm : dimSum m.dims = dimSum a.dims := hdam.symm
  have hb : dimSum b.dims = dimSum a.dims := (hdam.trans hdmb).symm
  have hcam : ∀ x y : Fin (dimSum a.dims), blk[a.dims] ((x : ℕ)) = blk[a.dims] ((y : ℕ)) →
      blk[m.dims] ((x : ℕ)) = blk[m.dims] ((y : ℕ)) := fun x y h =>
    blocks_of_heights_subset hdam hsam x.isLt y.isLt h
  have hcmb : ∀ x y : Fin (dimSum a.dims), blk[m.dims] ((x : ℕ)) = blk[m.dims] ((y : ℕ)) →
      blk[b.dims] ((x : ℕ)) = blk[b.dims] ((y : ℕ)) := fun x y h =>
    blocks_of_heights_subset hdmb hsmb (by omega) (by omega) h
  have hσpar : crossPermAt ha f ∈ parabolic (dimSum a.dims) dm[b.dims] :=
    crossPermAt_mem_parabolic ha f
  obtain ⟨e, he⟩ := exists_crossPermAt_hom hm hb hcmb
    (midPerm_mem_parabolic m.dims b.dims _ hcmb hσpar)
    (fun _ _ hxy hlt => midPerm_lt m.dims _ hxy hlt)
  obtain ⟨g, hg⟩ := exists_crossPermAt_hom ha hm hcam
    (inv_midPerm_mul_mem_parabolic m.dims _)
    (fun _ _ hxy hlt => inv_midPerm_mul_lt m.dims a.dims _ hcam
      (fun _ _ h₁ h₂ => crossPermAt_lt ha f h₁ h₂) hxy hlt)
  have hcomp : g ≫ e = f := by
    refine crossPermAt_injective ha ?_
    change crossPermAt ha (g ≫ e) = crossPermAt ha f
    rw [crossPermAt_comp ha hm g e, he, hg, ← mul_assoc, mul_inv_cancel, one_mul]
  exact ⟨⟨m, g, e, hcomp⟩, rfl, fun p hp => factorisation_eq ha hm p ⟨m, g, e, hcomp⟩ hp rfl⟩

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
  refine ⟨zObj (l ++ p :: q :: r), ?_, ?_⟩
  · rw [zObj_dims, hb, heights_cut, hl]
  · rw [zObj_dims, hb, dimSum_append, dimSum_append, dimSum_cons, dimSum_cons, dimSum_cons,
      PNat.add_coe]
    omega

/-- The fine end, with the two beads meeting at that height merged. -/
private theorem exists_mid_merge {a b : Ch Zbp} (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ m : Ch Zbp, heights a.dims = insert t (heights m.dims) ∧ t ∉ heights m.dims
      ∧ dimSum m.dims = dimSum a.dims := by
  rw [cutsOf, Finset.mem_sdiff] at ht
  have hdim := strandsEq f
  have h0 : t ≠ 0 := fun h => ht.2 (h ▸ zero_mem_heights _)
  have hlast : t ≠ dimSum a.dims := fun h =>
    ht.2 (by rw [h, hdim]; exact dimSum_mem_heights b.dims)
  obtain ⟨l, r, p, q, ha, hl⟩ := exists_split_of_mem_heights a.dims ht.1 h0 hlast
  have hd : dimSum (l ++ (p + q) :: r) = dimSum a.dims := by
    rw [ha, dimSum_append, dimSum_append, dimSum_cons, dimSum_cons, dimSum_cons, PNat.add_coe]
    omega
  have hins : heights a.dims = insert t (heights (l ++ (p + q) :: r)) := by
    rw [ha, heights_cut, hl]
  refine ⟨zObj (l ++ (p + q) :: r), by rw [zObj_dims]; exact hins, ?_, by rw [zObj_dims]; exact hd⟩
  rw [zObj_dims]
  intro hmem
  have hcard := congrArg Finset.card hins
  rw [Finset.insert_eq_self.mpr hmem, card_heights, card_heights, ha] at hcard
  simp only [List.length_append, List.length_cons] at hcard
  omega

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
