import CubeChains.Precubical.Chains.ChainSkeletal
import CubeChains.Machinery.Grading
import CubeChains.Concurrency.Grading.Boundaries
import CubeChains.Precubical.Chains.ChainRestrictions
import CubeChains.Precubical.Segal.Segal
import CubeChains.Precubical.Segal.Split
import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Precubical.Segal.WedgeLaxMonoidal

/-!
# Concurrency/Grading/Degree — the grading on `Ch K`, and the codimension of a refinement

A morphism of `Ch K` runs **finer → coarser**: it preserves `dimSum` and drops the bead count, so
`degree = Σ (dim − 1)` only grows, and the gain is the codimension — `codim` is the number of beads
lost.  `codim` is a functor to the delooping of `(ℕ, +)`, and a *monoidal* transformation out of the
lax monoidal `chFunctor`, so it is additive along the tensorator.  Everything structural comes from
`splitWedgeMorphism` (`Precubical/Segal/Split`), the tensorator read backwards: it splits the
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

/-- Concatenation of chains adds degrees (`chConcat` appends the dimension lists). -/
@[simp] theorem degree_chConcat (X Y : BPSet) (ab : Ch X × Ch Y) :
    degree ((chConcat X Y).obj ab) = degree ab.1 + degree ab.2 :=
  BPSet.degree_append ab.1.dims ab.2.dims

/-! ### Codimension -/

/-- The **codimension** of a refinement `f : a ⟶ b` — the degree it gains.  It depends on `f` only
through its endpoints; `codim_eq_length_sub` is the bead-count formula. -/
def codim {a b : Ch K} (_f : a ⟶ b) : ℕ := degree b - degree a

theorem dimSum_eq_of_hom {a b : Ch K} (f : a ⟶ b) : BPSet.dimSum a.dims = BPSet.dimSum b.dims :=
  serialWedge_dimSum_eq f.φ

/-- **Codimension counts beads.**  `dimSum` is preserved, so the degree gained is exactly the bead
count lost. -/
theorem codim_eq_length_sub {a b : Ch K} (f : a ⟶ b) :
    codim f = a.dims.length - b.dims.length := by
  have ha := degree_add_length a
  have hb := degree_add_length b
  have hs := dimSum_eq_of_hom f
  have hlen := ChainCat.dims_length_le_of_hom f
  simp only [codim]
  omega

theorem degree_le_of_hom {a b : Ch K} (f : a ⟶ b) : degree a ≤ degree b := by
  have ha := degree_add_length a
  have hb := degree_add_length b
  have hs := dimSum_eq_of_hom f
  have hlen := ChainCat.dims_length_le_of_hom f
  omega

/-- **`Ch K` is graded by the degree a refinement gains.** -/
def grading (K : BPSet) : Grading (Ch K) := Grading.ofRise degree degree_le_of_hom

@[simp] theorem codim_id (a : Ch K) : codim (𝟙 a) = 0 := (grading K).codim_id a

/-- Codimension is additive along composites. -/
theorem codim_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) :
    codim (f ≫ g) = codim f + codim g := (grading K).codim_comp f g

/-- **A refinement of positive codimension is not invertible**: two refinements over a common
coarsening form a span, never a pair of mutual inverses. -/
theorem not_isIso_of_codim_ne_zero {a b : Ch K} (f : a ⟶ b) (h : codim f ≠ 0) : ¬ IsIso f :=
  (grading K).not_isIso_of_codim_ne_zero f h

/-- **Codimension is a grading.**  `codim_id` and `codim_comp` are exactly functoriality into the
delooping of `(ℕ, +)`; `degree` is then the grading of the objects it lifts. -/
def codimFunctor (K : BPSet) : Ch K ⥤ Grade := (grading K).functor

/-- **…and it is monoidal**: concatenating two refinements adds their codimensions, matching
`degree_chConcat` on objects. -/
theorem codim_chConcat {X Y : BPSet} {ab ab' : Ch X × Ch Y} (fg : ab ⟶ ab') :
    codim ((chConcat X Y).map fg) = codim fg.1 + codim fg.2 := by
  have h1 := ChainCat.dims_length_le_of_hom fg.1
  have h2 := ChainCat.dims_length_le_of_hom fg.2
  rw [codim_eq_length_sub, codim_eq_length_sub, codim_eq_length_sub]
  simp only [chConcat_obj_dims, List.length_append]
  omega

/-! ### The grading is a monoidal natural transformation

`chFunctor` is lax monoidal (`Precubical/Segal/WedgeLaxMonoidal`) and `gradeFunctor`, the constant
functor at the delooping of `(ℕ, +)`, is lax monoidal by addition.  `codimNat` is `codimFunctor`
read as a transformation between them; its `tensor` law is `codim_chConcat`.  `Cat` is *cartesian*
monoidal, so every coherence square below reduces — via `grade_ext`, since the target has one
object — to a monoid law of `Multiplicative ℕ`. -/

/-- The constant functor at the grading category. -/
def gradeFunctor : BPSet ⥤ Cat := (Functor.const BPSet).obj (Cat.of Grade)

instance : gradeFunctor.LaxMonoidal where
  ε := (Cat.fromChosenTerminalEquiv.symm (SingleObj.star (Multiplicative ℕ))).toCatHom
  μ _ _ := gradeAdd.toCatHom
  μ_natural_left _ _ := Cat.ext (grade_ext fun _ => rfl)
  μ_natural_right _ _ := Cat.ext (grade_ext fun _ => rfl)
  associativity _ _ _ := Cat.ext (grade_ext fun _ => mul_assoc (G := Multiplicative ℕ) _ _ _)
  left_unitality _ := Cat.ext (grade_ext fun _ => (one_mul (M := Multiplicative ℕ) _).symm)
  right_unitality _ := Cat.ext (grade_ext fun _ => (mul_one (M := Multiplicative ℕ) _).symm)

/-- **Codimension, as a transformation `chFunctor ⟹ gradeFunctor`.**  Naturality is definitional:
`pushforward` leaves the dimension sequence alone. -/
def codimNat : chFunctor ⟶ gradeFunctor where
  app K := (codimFunctor K).toCatHom
  naturality _ _ _ := Cat.ext (grade_ext fun _ => rfl)

/-- **The grading is monoidal.**  `unit` is `codim_id`, `tensor` is `codim_chConcat`. -/
instance : NatTrans.IsMonoidal codimNat where
  unit := Cat.ext (grade_ext fun _ => congrArg Multiplicative.ofAdd (codim_id _))
  tensor _ _ := Cat.ext (grade_ext fun fg => congrArg Multiplicative.ofAdd (codim_chConcat fg))

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

/-- **Splitting at a junction the source already has**: `dimSum` pins which beads land on which
side, so the two halves are honest wedge maps. -/
def splitAt {ad₁ ad₂ cd₁ cd₂ : List ℕ+} (φ : ⋁(ad₁ ++ ad₂) ⟶ ⋁(cd₁ ++ cd₂))
    (h : BPSet.dimSum ad₁ = BPSet.dimSum cd₁) :
    Σ' (φ₁ : ⋁ad₁ ⟶ ⋁cd₁) (φ₂ : ⋁ad₂ ⟶ ⋁cd₂),
      φ = (serialWedgeAppend ad₁ ad₂).inv ≫ (φ₁ ⊗ₘ φ₂)
        ≫ (serialWedgeAppend cd₁ cd₂).hom := by
  obtain ⟨ad₁', ad₂', φ₁, φ₂, hsplit, hmap⟩ := splitTarget φ
  obtain rfl : ad₁ = ad₁' :=
    BPSet.dimSum_prefix_eq hsplit (h.trans (serialWedge_dimSum_eq φ₁).symm)
  obtain rfl : ad₂' = ad₂ := (List.append_cancel_left hsplit).symm
  exact ⟨φ₁, φ₂, by simpa using hmap⟩

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

theorem beadStart_mem_boundaries (d : List ℕ+) {i : ℕ} (hi : i ≤ d.length) :
    beadStart d i ∈ boundaries d :=
  mem_boundaries_iff_beadStart.mpr ⟨i, hi, rfl⟩

/-- Bead starts strictly increase — every bead is nonempty. -/
theorem beadStart_lt_beadStart {d : List ℕ+} {i j : ℕ} (hj : j ≤ d.length) (hij : i < j) :
    beadStart d i < beadStart d j := by
  have hi : i < d.length := lt_of_lt_of_le hij hj
  have h1 : beadStart d (i + 1) = beadStart d i + ((d.get ⟨i, hi⟩ : ℕ+) : ℕ) :=
    beadStart_succ d ⟨i, hi⟩
  have h2 := beadStart_mono d (show i + 1 ≤ j from hij)
  have h3 : 0 < ((d.get ⟨i, hi⟩ : ℕ+) : ℕ) := (d.get ⟨i, hi⟩).pos
  omega

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
  · intro hcod
    obtain ⟨l, r, p, q, hb, ha⟩ := cutOfCodimOne f hcod
    exact ⟨l, r, p, q, hb, ha⟩
  · rintro ⟨l, r, p, q, hb, ha⟩
    rw [codim_eq_length_sub, ha, hb]
    simp
    omega

/-- **Codimension two has exactly two species**: one bead cut in three (`𝟙 ∨ w₃ ∨ 𝟙`), or two
distinct beads each cut in two (`𝟙 ∨ w ∨ 𝟙 ∨ w' ∨ 𝟙`). -/
theorem codim_eq_two_iff {a b : Ch K} (f : a ⟶ b) :
    codim f = 2 ↔
      (∃ (l r : List ℕ+) (x y z : ℕ+),
          b.dims = l ++ (x + y + z) :: r ∧ a.dims = l ++ x :: y :: z :: r) ∨
      (∃ (l m r : List ℕ+) (x y x' y' : ℕ+),
          b.dims = l ++ (x + y) :: (m ++ (x' + y') :: r) ∧
          a.dims = l ++ x :: y :: (m ++ x' :: y' :: r)) := by
  constructor
  · intro hcod
    have hle := ChainCat.dims_length_le_of_hom f
    rw [codim_eq_length_sub] at hcod
    exact exists_cuts_of_length_add_two (dimSum_eq_of_hom f) (boundaries_subset_of_hom f) (by omega)
  · rintro (⟨l, r, x, y, z, hb, ha⟩ | ⟨l, m, r, x, y, x', y', hb, ha⟩) <;>
      · rw [codim_eq_length_sub, ha, hb]
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

/-- Whiskering by an identity is faithful — the wedge inclusions are monos. -/
theorem tensor_left_cancel {X A B : BPSet} {h h' : A ⟶ B}
    (e : 𝟙 X ⊗ₘ h = 𝟙 X ⊗ₘ h') : h = h' := by
  have hh : wedgeInr X A ≫ wedge2MapPsh (𝟙 X) h = wedgeInr X A ≫ wedge2MapPsh (𝟙 X) h' :=
    congrArg (fun m : (X ∨ A) ⟶ (X ∨ B) => wedgeInr X A ≫ m.hom) e
  rw [wedge2MapPsh_inr, wedge2MapPsh_inr] at hh
  haveI : Mono (wedgeInr X B) := CubeChain.wedge2_inr_mono X B
  exact BPSet.hom_ext ((cancel_mono (wedgeInr X B)).mp hh)

theorem tensor_right_cancel {X A B : BPSet} {h h' : A ⟶ B}
    (e : h ⊗ₘ 𝟙 X = h' ⊗ₘ 𝟙 X) : h = h' := by
  have hh : wedgeInl A X ≫ wedge2MapPsh h (𝟙 X) = wedgeInl A X ≫ wedge2MapPsh h' (𝟙 X) :=
    congrArg (fun m : (A ∨ X) ⟶ (B ∨ X) => wedgeInl A X ≫ m.hom) e
  rw [wedge2MapPsh_inl, wedge2MapPsh_inl] at hh
  haveI : Mono (wedgeInl B X) := CubeChain.wedge2_inl_mono B X
  exact BPSet.hom_ext ((cancel_mono (wedgeInl B X)).mp hh)

/-- **The merge `w` is unique too**: `𝟙 ∨ · ∨ 𝟙` is injective on morphisms. -/
theorem wedge_middle_unique {l r : List ℕ+} {p q : ℕ+}
    {w w' : □(p : ℕ) ∨ □(q : ℕ) ⟶ □((p + q : ℕ+) : ℕ)}
    (h : 𝟙 (⋁l) ⊗ₘ (w ⊗ₘ 𝟙 (⋁r)) = 𝟙 (⋁l) ⊗ₘ (w' ⊗ₘ 𝟙 (⋁r))) : w = w' :=
  tensor_right_cancel (tensor_left_cancel h)

/-! ### `f ≅ 𝟙 ∨ w ∨ 𝟙`

The classification, stated where it belongs: in the arrow category of the monoidal `(BPSet, ∨)`.
The isomorphism absorbs every identification of endpoints, so no list decomposition appears. -/

/-- `⋁[p,q] ≅ □p ∨ □q` — drop the unit tail of the serial wedge. -/
def pairIso (p q : ℕ+) : ⋁[p, q] ≅ □(p : ℕ) ∨ □(q : ℕ) :=
  whiskerLeftIso (□(p : ℕ)) (ρ_ (□(q : ℕ)))

/-- The append iso at a two-letter word is the associator, modulo that unit tail. -/
theorem serialWedgeAppend_pair (p q : ℕ+) (r : List ℕ+) :
    (serialWedgeAppend [p, q] r).hom
      = ((pairIso p q).hom ⊗ₘ 𝟙 (⋁r)) ≫ (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)).hom := by
  rw [show serialWedgeAppend [p, q] r
      = wedge2Assoc (□(p : ℕ)) (⋁[q]) (⋁r) ≪≫ wedge2MapIso (Iso.refl _) (serialWedgeAppend [q] r)
      from rfl,
    show serialWedgeAppend [q] r
      = wedge2Assoc (□(q : ℕ)) (⋁([] : List ℕ+)) (⋁r) ≪≫ wedge2MapIso (Iso.refl _)
          (serialWedgeAppend ([] : List ℕ+) r) from rfl,
    show serialWedgeAppend ([] : List ℕ+) r = wedge2LeftUnit (⋁r) from rfl]
  change (α_ _ _ _).hom ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (λ_ (⋁r)).hom))) = _
  simp only [pairIso, whiskerLeftIso_hom, triangle, tensorHom_id]
  monoidal

/-- The append iso at a one-letter word is the right unitor — the monoidal triangle. -/
theorem serialWedgeAppend_singleton (n : ℕ+) (r : List ℕ+) :
    (serialWedgeAppend [n] r).hom = (ρ_ (□(n : ℕ))).hom ▷ ⋁r := by
  change (α_ (□(n : ℕ)) (𝟙_ BPSet) (⋁r)).hom ≫ (□(n : ℕ) ◁ (λ_ (⋁r)).hom) = _
  rw [triangle]

/-- `⋁l ∨ ((□p ∨ □q) ∨ ⋁r) ≅ ⋁(l ++ p :: q :: r)` — the source identification, as a `def` so the
existence and the uniqueness proofs share it. -/
def cutSrcIso (l r : List ℕ+) (p q : ℕ+) :
    ⋁l ∨ ((□(p : ℕ) ∨ □(q : ℕ)) ∨ ⋁r) ≅ ⋁(l ++ p :: q :: r) :=
  whiskerLeftIso (⋁l) (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)) ≪≫ serialWedgeAppend l (p :: q :: r)

/-- **The codimension-one decomposition of `f`**: one bead merge `w` between two serial wedges,
together with the identification of each endpoint.  `Unique` — see `codimOneWedge` and the
`Subsingleton` instance. -/
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

/-- The arrow-category repackaging: `f ≅ 𝟙 ∨ w ∨ 𝟙`. -/
def CutData.arrowIso {a b : Ch K} {f : a ⟶ b} (d : CutData f) :
    Arrow.mk f.φ ≅ Arrow.mk (𝟙 (⋁d.l) ⊗ₘ (d.w ⊗ₘ 𝟙 (⋁d.r))) :=
  Arrow.isoMk' _ _ d.e₁ d.e₂ d.sq

/-- **The two-letter case of `splitAt`, in the cons spelling.**  Combines the pair coherence with
the triangle, once, so no construction below has to redo them.  Stating it with `T`, `T'` free is
what keeps `⋁([x,y] ++ T)` and `⋁(x :: y :: T)` from drifting apart. -/
theorem splitAt_pair {T T' : List ℕ+} {x y : ℕ+} {ψ₁ : ⋁[x, y] ⟶ ⋁[x + y]} {ψ₂ : ⋁T ⟶ ⋁T'} :
    (serialWedgeAppend [x, y] T).inv ≫ (ψ₁ ⊗ₘ ψ₂) ≫ (serialWedgeAppend [x + y] T').hom
      = (α_ (□(x : ℕ)) (□(y : ℕ)) (⋁T)).inv
        ≫ (((pairIso x y).inv ≫ ψ₁ ≫ (ρ_ (□((x + y : ℕ+) : ℕ))).hom) ⊗ₘ ψ₂) := by
  rw [serialWedgeAppend_singleton]
  have hp : (serialWedgeAppend [x, y] T).inv
      = (α_ (□(x : ℕ)) (□(y : ℕ)) (⋁T)).inv ≫ ((pairIso x y).inv ⊗ₘ 𝟙 (⋁T)) := by
    rw [show serialWedgeAppend [x, y] T
        = (pairIso x y ⊗ᵢ Iso.refl (⋁T)) ≪≫ α_ (□(x : ℕ)) (□(y : ℕ)) (⋁T) from
      Iso.ext (by simpa using serialWedgeAppend_pair x y T)]
    simp
  rw [hp]
  -- `Category.assoc` will not `rw` here (the two `≫` carry different object spellings), so
  -- reassociate with `exact`, which unifies at default transparency.
  refine Eq.trans (Category.assoc _ _ _) ?_
  congr 1
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [tensorHom_comp_tensorHom]
  exact (tensorHom_comp_tensorHom _ _ _ _).trans (by simp)

/-- **Existence from a dimension-list decomposition**: build `𝟙 ∨ w ∨ 𝟙`.  Two applications of
`splitAt` — one per junction — and rigidity to see that the outer pieces are identities. -/
def cutDataOf {a b : Ch K} (f : a ⟶ b) {l r : List ℕ+} {p q : ℕ+}
    (hb : b.dims = l ++ (p + q) :: r) (ha : a.dims = l ++ p :: q :: r) : CutData f := by
  -- Transport `f.φ` onto the decomposed dimension lists.
  obtain ⟨φ₁, φ₂, hφ⟩ := splitAt (ad₁ := l) (ad₂ := p :: q :: r) (cd₁ := l) (cd₂ := (p + q) :: r)
    (eqToHom (congrArg BPSet.serialWedge ha).symm ≫ f.φ ≫ eqToHom (congrArg BPSet.serialWedge hb))
    rfl
  obtain rfl : φ₁ = 𝟙 (⋁l) := serialWedge_bipointed_endo_id l φ₁
  -- Split again inside the bead being cut.
  obtain ⟨ψ₁, ψ₂, hψ⟩ := splitAt (ad₁ := [p, q]) (ad₂ := r) (cd₁ := [p + q]) (cd₂ := r) φ₂
    (by simp [BPSet.dimSum])
  obtain rfl : ψ₂ = 𝟙 (⋁r) := serialWedge_bipointed_endo_id r ψ₂
  refine ⟨l, r, p, q, (pairIso p q).inv ≫ ψ₁ ≫ (ρ_ (□((p + q : ℕ+) : ℕ))).hom,
    eqToIso (congrArg BPSet.serialWedge ha) ≪≫ (serialWedgeAppend l (p :: q :: r)).symm
      ≪≫ whiskerLeftIso (⋁l) (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)).symm,
    eqToIso (congrArg BPSet.serialWedge hb) ≪≫ (serialWedgeAppend l ((p + q) :: r)).symm, ?_⟩
  -- The middle factor is `w` reassociated: `serialWedgeAppend_pair` on the source, the triangle
  -- (`serialWedgeAppend_singleton`) on the target.
  have hmid : (α_ (□(p : ℕ)) (□(q : ℕ)) (⋁r)).inv
      ≫ ((((pairIso p q).inv ≫ ψ₁ ≫ (ρ_ (□((p + q : ℕ+) : ℕ))).hom)) ⊗ₘ 𝟙 (⋁r)) = φ₂ := by
    exact splitAt_pair.symm.trans hψ.symm
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc, eqToIso.hom]
  -- Read the square off `hφ`, moving the two endpoint identifications across.
  have hsq : f.φ ≫ eqToHom (congrArg BPSet.serialWedge hb)
      ≫ (serialWedgeAppend l ((p + q) :: r)).inv
      = eqToHom (congrArg BPSet.serialWedge ha)
        ≫ (serialWedgeAppend l (p :: q :: r)).inv ≫ (𝟙 (⋁l) ⊗ₘ φ₂) := by
    have h2 := congrArg (fun m => eqToHom (congrArg BPSet.serialWedge ha) ≫ m
      ≫ (serialWedgeAppend l ((p + q) :: r)).inv) hφ
    simpa [Category.assoc, eqToHom_trans] using h2
  refine Eq.trans ?_ hsq.symm
  rw [← hmid]
  simp only [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp]
  rfl

/-- **Existence**: a codimension-one refinement decomposes as `𝟙 ∨ w ∨ 𝟙`. -/
def codimOneWedge {a b : Ch K} (f : a ⟶ b) (hcod : codim f = 1) : CutData f := by
  obtain ⟨l, r, p, q, hb, ha⟩ := cutOfCodimOne f hcod
  exact cutDataOf f hb ha

/-! ## Diamonds

The codimension-two *existence* a braid relation needs.  Separation makes a lift unique where it
exists (`mergeLift`); nothing makes it exist, and two routes round a diamond use disjoint sets of
codimension-one cells, so one can be fillable and the other not. -/

/-- `K` **has diamonds**: two distinct codimension-one refinements of a chain are joined by one
further codimension-one step each, commutingly.  `Ch (□n)` has it (`hasDiamonds_cube`); `Ch Zbp`'s
`exists_diamond` is the same square, but under a hypothesised common upper bound.

It is the 3-cell condition in the form the chains can consume: for two *adjacent* cuts the join has
one bead of size three, so a `K` with all its squares and no 3-cell — the 2-skeleton of `□3`, say —
already fails it. -/
def HasDiamonds (K : BPSet) : Prop :=
  ∀ {a d d' : Ch K} (u : a ⟶ d) (u' : a ⟶ d'), codim u = 1 → codim u' = 1 → d ≠ d' →
    ∃ (e : Ch K) (v : d ⟶ e) (v' : d' ⟶ e), codim v = 1 ∧ codim v' = 1 ∧ u ≫ v = u' ≫ v'

end ChainCat
