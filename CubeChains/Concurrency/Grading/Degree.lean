import CubeChains.Precubical.Chains.ChainSkeletal
import CubeChains.Machinery.Grading
import CubeChains.Concurrency.Grading.Boundaries
import CubeChains.Precubical.Segal.Split

/-!
# Concurrency/Grading/Degree — the grading on `Ch K`, and the codimension of a refinement

A morphism of `Ch K` runs **finer → coarser**: it preserves `dimSum` and drops the bead count, so
`degree = Σ (dim − 1)` only grows, and the gain is the codimension — `codim` is the number of beads
lost, and `grading` makes that a functor to the delooping of `(ℕ, +)`.  Everything structural comes
from `splitWedgeMorphism` (`Precubical/Segal/Split`), the tensorator read backwards: it splits the
source at every junction of the target, which is `boundaries_subset_of_hom` and hence the whole
classification.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChain CubeChains

namespace ChainCat

variable {K : BPSet}

/-- The degree of a chain — `0` exactly on the runs, by `degree_eq_zero_iff`. -/
def degree (a : Ch K) : ℕ := BPSet.degree a.dims

theorem degree_eq_zero_iff (a : Ch K) : degree a = 0 ↔ ∀ d ∈ a.dims, d = 1 :=
  BPSet.degree_eq_zero_iff a.dims

theorem degree_add_length (a : Ch K) : degree a + a.dims.length = BPSet.dimSum a.dims :=
  BPSet.degree_add_length a.dims

/-! ### Codimension -/

/-- The **codimension** of a refinement `f : a ⟶ b` — the degree it gains.  It depends on `f` only
through its endpoints; `codim_eq_length_sub` is the bead-count formula. -/
def codim {a b : Ch K} (_f : a ⟶ b) : ℕ := degree b - degree a

/-- **Degree and bead count trade off along a refinement**: both sum to the preserved `dimSum`, so
what one gains the other loses.  Everything below is this equation plus `dims_length_le_of_hom`. -/
theorem degree_add_length_eq_of_hom {a b : Ch K} (f : a ⟶ b) :
    degree b + b.dims.length = degree a + a.dims.length := by
  rw [degree_add_length, degree_add_length, dimSum_eq_of_hom f]

/-- **Codimension counts beads.** -/
theorem codim_eq_length_sub {a b : Ch K} (f : a ⟶ b) :
    codim f = a.dims.length - b.dims.length := by
  have h := degree_add_length_eq_of_hom f
  have hlen := ChainCat.dims_length_le_of_hom f
  simp only [codim]
  omega

theorem degree_le_of_hom {a b : Ch K} (f : a ⟶ b) : degree a ≤ degree b := by
  have h := degree_add_length_eq_of_hom f
  have hlen := ChainCat.dims_length_le_of_hom f
  omega

/-- **Codimension is the degree gained**, with the truncated subtraction discharged. -/
theorem degree_eq_add_codim {a b : Ch K} (f : a ⟶ b) : degree b = degree a + codim f := by
  have := degree_le_of_hom f
  simp only [codim]
  omega

/-- **`Ch K` is graded by the degree a refinement gains.** -/
def grading (K : BPSet) : Grading (Ch K) := Grading.ofRise degree degree_le_of_hom

@[simp] theorem codim_id (a : Ch K) : codim (𝟙 a) = 0 := (grading K).codim_id a

/-- Codimension is additive along composites. -/
theorem codim_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    codim (f ≫ g) = codim f + codim g := (grading K).codim_comp f g

/-- Codimension `0` pins the refinement: `Ch K` is skeletal at equal bead counts. -/
theorem codim_eq_zero_iff {a b : Ch K} (f : a ⟶ b) : codim f = 0 ↔ a = b := by
  constructor
  · intro h
    rw [codim_eq_length_sub] at h
    exact ChainCat.eq_of_hom_of_dims_length_eq f
      (Nat.le_antisymm (Nat.le_of_sub_eq_zero h) (ChainCat.dims_length_le_of_hom f))
  · rintro rfl
    exact codim_id a

/-! ### Splitting a wedge map at a junction

The tensorator is invertible on serial wedges (`splitWedgeMorphism`), so a wedge map splits at
every junction of its target.  That single fact is the source of everything below. -/

/-- **The source splits wherever the target does.** -/
def splitTarget {ad cd₁ cd₂ : List ℕ+} (φ : ⋁ad ⟶ ⋁(cd₁ ++ cd₂)) :
    Σ' (ad₁ ad₂ : List ℕ+) (φ₁ : ⋁ad₁ ⟶ ⋁cd₁) (φ₂ : ⋁ad₂ ⟶ ⋁cd₂) (h : ad = ad₁ ++ ad₂),
      φ = eqToHom (congrArg BPSet.serialWedge h) ≫ (serialWedgeAppend ad₁ ad₂).inv
            ≫ (φ₁ ⊗ₘ φ₂) ≫ (serialWedgeAppend cd₁ cd₂).hom := by
  obtain ⟨P, Q, hPQ, hmap⟩ := splitWedgeMorphism
    (BPSet.wedge2_admitsAltitude (BPSet.serialWedge_admitsAltitude cd₁)
      (BPSet.serialWedge_admitsAltitude cd₂)) ad (φ ≫ (serialWedgeAppend cd₁ cd₂).inv)
  refine ⟨P.dims, Q.dims, P.map, Q.map, hPQ, ?_⟩
  rw [← Category.comp_id φ, ← (serialWedgeAppend cd₁ cd₂).inv_hom_id, ← Category.assoc, hmap]
  simp [concatChainMap]

/-- **A wedge map only refines**: every boundary of the target is a boundary of the source. -/
theorem boundaries_subset_of_wedgeHom {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    boundaries cd ⊆ boundaries ad := by
  intro t ht
  obtain ⟨cd₁, cd₂, rfl, rfl⟩ := mem_boundaries_iff.mp ht
  obtain ⟨ad₁, ad₂, φ₁, -, rfl, -⟩ := splitTarget φ
  exact mem_boundaries_iff.mpr ⟨ad₁, ad₂, rfl, serialWedge_dimSum_eq φ₁⟩

/-- **A refinement inherits every boundary of its coarsening.** -/
theorem boundaries_subset_of_hom {a b : Ch K} (f : a ⟶ b) :
    boundaries b.dims ⊆ boundaries a.dims :=
  boundaries_subset_of_wedgeHom f.φ

/-- **Codimension counts the boundaries dropped** — the bead-count formula read on boundary sets. -/
theorem codim_eq_card_sdiff {a b : Ch K} (f : a ⟶ b) :
    codim f = (boundaries a.dims \ boundaries b.dims).card := by
  rw [Finset.card_sdiff_of_subset (boundaries_subset_of_hom f), card_boundaries, card_boundaries,
    codim_eq_length_sub]
  omega

/-! ### The boundaries are the bead starts -/

/-- A boundary is where a bead starts. -/
theorem mem_boundaries_iff_beadStart {d : List ℕ+} {t : ℕ} :
    t ∈ boundaries d ↔ ∃ i ≤ d.length, beadStart d i = t :=
  mem_boundaries_iff_take rfl

/-- The junction set, enumerated by bead index. -/
theorem boundaries_eq_image (d : List ℕ+) :
    boundaries d = (Finset.range (d.length + 1)).image (beadStart d) := by
  ext t
  simp only [Finset.mem_image, Finset.mem_range, mem_boundaries_iff_beadStart, Nat.lt_succ_iff]

/-- **The bead starts are distinct.**  There are `length + 1` of each, so `card_boundaries` says
the enumeration is injective — block positivity, paid for once. -/
theorem beadStart_injOn (d : List ℕ+) :
    Set.InjOn (beadStart d) (Finset.range (d.length + 1)) :=
  Finset.injOn_of_card_image_eq (by
    rw [← boundaries_eq_image, card_boundaries, Finset.card_range])

/-- A shape is pinned by its bead starts. -/
theorem eq_of_beadStart_eq {d d' : List ℕ+} (hlen : d.length = d'.length)
    (h : ∀ j ≤ d.length, beadStart d j = beadStart d' j) : d = d' := by
  refine List.ext_get hlen fun j h1 h2 => PNat.coe_injective ?_
  have e1 : beadStart d (j + 1) = beadStart d j + ((d.get ⟨j, h1⟩ : ℕ+) : ℕ) :=
    beadStart_succ d ⟨j, h1⟩
  have e2 : beadStart d' (j + 1) = beadStart d' j + ((d'.get ⟨j, h2⟩ : ℕ+) : ℕ) :=
    beadStart_succ d' ⟨j, h2⟩
  have s1 := h j h1.le
  have s2 := h (j + 1) h1
  omega

/-! ### The species of a refinement

`codim` counts the boundaries removed, so the classification is `Concurrency/Grading/Boundaries`
applied to `boundaries_subset_of_hom`. -/

/-- **The cut of a codimension-one refinement**, as data: one bead `p + q` of the target replaced
by the two beads `p, q`. -/
def cutOfCodimOne {a b : Ch K} (f : a ⟶ b) (hcod : codim f = 1) :
    Σ' (l r : List ℕ+) (p q : ℕ+),
      b.dims = l ++ (p + q) :: r ∧ a.dims = l ++ p :: q :: r := by
  have hle := ChainCat.dims_length_le_of_hom f
  rw [codim_eq_length_sub] at hcod
  exact cutOfLengthSucc (dimSum_eq_of_hom f) (boundaries_subset_of_hom f) (by omega)

/-- **A refinement of codimension one is `𝟙 ∨ w ∨ 𝟙` on dimension lists**: one bead `p + q` of the
target is replaced by the two beads `p, q`, and nothing else moves. -/
theorem codim_eq_one_iff {a b : Ch K} (f : a ⟶ b) :
    codim f = 1 ↔ ∃ (l r : List ℕ+) (p q : ℕ+),
      b.dims = l ++ (p + q) :: r ∧ a.dims = l ++ p :: q :: r := by
  constructor
  · exact fun hcod => let ⟨l, r, p, q, hb, ha⟩ := cutOfCodimOne f hcod; ⟨l, r, p, q, hb, ha⟩
  · rintro ⟨l, r, p, q, hb, ha⟩
    rw [codim_eq_length_sub, ha, hb]
    simp
    omega

/-! ### Rigidity of the serial wedges -/

/-- **A serial wedge is rigid**, so an isomorphism out of one is unique: two isos differ by a
bi-pointed endomorphism of `⋁d`, and there is only the identity. -/
theorem serialWedge_iso_unique {d : List ℕ+} {Z : BPSet} (e e' : ⋁d ≅ Z) : e = e' := by
  have h : e.hom ≫ e'.inv = 𝟙 (⋁d) := serialWedge_bipointed_endo_id d _
  refine Iso.ext ?_
  calc e.hom = e.hom ≫ e'.inv ≫ e'.hom := by rw [e'.inv_hom_id, Category.comp_id]
    _ = e'.hom := by rw [← Category.assoc, h, Category.id_comp]

/-- **A serial wedge determines its dimension list.**  `Ch` is skeletal, and an iso gives
morphisms both ways. -/
theorem serialWedge_iso_dims_eq {d d' : List ℕ+} (e : ⋁d ≅ ⋁d') : d = d' := by
  have h : (⟨d, e.hom⟩ : Ch (⋁d')) = ⟨d', 𝟙 (⋁d')⟩ :=
    ChainCat.eq_of_hom_hom ⟨e.hom, by simp⟩ ⟨e.inv, by simp⟩
  exact congrArg Obj.dims h

/-- **`∨` is faithful in each variable**: a wedge map is pinned by its two restrictions, and the
inclusions are monos. -/
theorem wedge2Map_cancel {A B A' B' : BPSet} {f f' : A ⟶ A'} {g g' : B ⟶ B'}
    (e : f ⊗ₘ g = f' ⊗ₘ g') : f = f' ∧ g = g' := by
  have hl : wedgeInl A B ≫ wedge2MapPsh f g = wedgeInl A B ≫ wedge2MapPsh f' g' :=
    congrArg (fun m : (A ∨ B) ⟶ (A' ∨ B') => wedgeInl A B ≫ m.hom) e
  have hr : wedgeInr A B ≫ wedge2MapPsh f g = wedgeInr A B ≫ wedge2MapPsh f' g' :=
    congrArg (fun m : (A ∨ B) ⟶ (A' ∨ B') => wedgeInr A B ≫ m.hom) e
  rw [wedge2MapPsh_inl, wedge2MapPsh_inl] at hl
  rw [wedge2MapPsh_inr, wedge2MapPsh_inr] at hr
  exact ⟨BPSet.hom_ext ((cancel_mono (wedgeInl A' B')).mp hl),
    BPSet.hom_ext ((cancel_mono (wedgeInr A' B')).mp hr)⟩

/-- **The merge `w` is unique too**: `𝟙 ∨ · ∨ 𝟙` is injective on morphisms. -/
theorem wedge_middle_unique {l r : List ℕ+} {p q : ℕ+}
    {w w' : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)}
    (h : 𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r)) = 𝟙 (⋁l) ⊗ₘ (w' ⊗ₘ 𝟙 (⋁r))) : w = w' :=
  (wedge2Map_cancel (wedge2Map_cancel h).2).1

/-! ### `f ≅ 𝟙 ∨ w ∨ 𝟙`

The classification, stated where it belongs: in the arrow category of the monoidal `(BPSet, ∨)`.
The isomorphism absorbs every identification of endpoints, so no list decomposition appears. -/

/-- **The codimension-one decomposition of `f`**: one bead merge `w` between two serial wedges,
together with the identification of each endpoint; the `Subsingleton` instance says it is unique. -/
structure CutData {a b : Ch K} (f : a ⟶ b) where
  /-- The beads of the target before the cut. -/
  l : List ℕ+
  /-- The beads of the target after the cut. -/
  r : List ℕ+
  /-- The first piece of the cut bead. -/
  p : ℕ+
  /-- The second piece of the cut bead. -/
  q : ℕ+
  /-- The bead merge. -/
  w : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)
  /-- Identification of the source. -/
  e₁ : ⋁a.dims ≅ ⋁l ∨ ((□(p : ℕ) ∨ □(q : ℕ)) ∨ ⋁r)
  /-- Identification of the target. -/
  e₂ : ⋁b.dims ≅ ⋁l ∨ (□((p + q : ℕ+) : ℕ) ∨ ⋁r)
  /-- `f` *is* `𝟙 ∨ w ∨ 𝟙`. -/
  sq : e₁.hom ≫ (𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r))) = f.φ ≫ e₂.hom

/-- The dimension list of the source, read off the identification. -/
theorem CutData.src_dims {a b : Ch K} {f : a ⟶ b} (d : CutData f) :
    a.dims = d.l ++ d.p :: d.q :: d.r :=
  serialWedge_iso_dims_eq (d.e₁ ≪≫ cutSrcIso d.l d.r d.p d.q)

/-- The dimension list of the target, read off the identification. -/
theorem CutData.tgt_dims {a b : Ch K} {f : a ⟶ b} (d : CutData f) :
    b.dims = d.l ++ (d.p + d.q) :: d.r :=
  serialWedge_iso_dims_eq (d.e₂ ≪≫ serialWedgeAppend d.l ((d.p + d.q) :: d.r))

/-- **The decomposition is unique** — every field is determined by `f`. -/
instance {a b : Ch K} (f : a ⟶ b) : Subsingleton (CutData f) := by
  constructor
  rintro ⟨l, r, p, q, w, e₁, e₂, sq⟩ ⟨l', r', p', q', w', e₁', e₂', sq'⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ := cut_unique
    ((CutData.tgt_dims ⟨l, r, p, q, w, e₁, e₂, sq⟩).symm.trans
      (CutData.tgt_dims ⟨l', r', p', q', w', e₁', e₂', sq'⟩))
    ((CutData.src_dims ⟨l, r, p, q, w, e₁, e₂, sq⟩).symm.trans
      (CutData.src_dims ⟨l', r', p', q', w', e₁', e₂', sq'⟩))
  obtain rfl : e₁ = e₁' := serialWedge_iso_unique e₁ e₁'
  obtain rfl : e₂ = e₂' := serialWedge_iso_unique e₂ e₂'
  obtain rfl : w = w' := wedge_middle_unique ((cancel_epi e₁.hom).mp (sq.trans sq'.symm))
  rfl

/-- **A splice has codimension one.**  The two identities contribute nothing and the merge loses
exactly one bead. -/
theorem CutData.codim_eq_one {a b : Ch K} {f : a ⟶ b} (d : CutData f) : codim f = 1 :=
  (codim_eq_one_iff f).mpr ⟨d.l, d.r, d.p, d.q, d.tgt_dims, d.src_dims⟩

end ChainCat
