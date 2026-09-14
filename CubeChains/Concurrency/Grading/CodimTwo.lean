import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Merge.Atom
import CubeChains.Concurrency.Merge.Factorisation

/-!
# Concurrency/Grading/CodimTwo — the capacity of a shape, and codimension two at degree zero

`crossCap` is the reversal inside each bead — the pairs of events a shape makes concurrent, and so
the bound on every run over it (`permLen_cross_le_crossCap`).

At codimension two out of a run the shape is a hexagon or a square, told apart by `boundaries`; the
capacity of each is then a computation.  Factoring is orthogonal to all of it: a factorisation whose
first leg is a single cut *is* that cut (`oneCutEquivCuts`), so there are exactly two, indexed by
`Bool`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain Equiv

namespace ChainCat

section Shapes

variable {a : Ch Zbp}

/-! ## The capacity of a shape

The **pairs of events sharing a bead** — the concurrent pairs the shape makes commute.  A crossing
is a set of pairs, so it cannot exceed the pairs there are (`permLen_cross_le_crossCap`), and the
reversal inside each bead attains it (`Paper.permLen_runCross_topOf`). -/

/-- The **crossing capacity** of a shape: the pairs of events sharing a bead. -/
def crossCap (d : List ℕ+) : ℕ := (d.map fun x => Nat.choose (x : ℕ) 2).sum

@[simp] theorem crossCap_nil : crossCap [] = 0 := rfl

@[simp] theorem crossCap_cons (x : ℕ+) (d : List ℕ+) :
    crossCap (x :: d) = Nat.choose (x : ℕ) 2 + crossCap d := rfl

@[simp] theorem crossCap_append (d e : List ℕ+) :
    crossCap (d ++ e) = crossCap d + crossCap e := by
  simp [crossCap, List.sum_append]

/-- An edge has no pair to cross. -/
@[simp] theorem crossCap_replicate_one (n : ℕ) : crossCap (𝟙^n) = 0 := by
  induction n with
  | zero => rfl
  | succ k hk => rw [List.replicate_succ, crossCap_cons, hk]; decide

/-! ### …read off its degree

`degree` is the size of each bead less one, so below degree three one bead carries everything and
the capacity is a function of the degree — except at degree two, where the two species part: one
bead of three reverses three pairs, two beads of two reverse one each. -/

private theorem pnat_eq_one {x : ℕ+} (h : (x : ℕ) = 1) : x = 1 :=
  PNat.coe_injective (h.trans (show (1 : ℕ) = ((1 : ℕ+) : ℕ) from rfl))

private theorem pnat_eq_two {x : ℕ+} (h : (x : ℕ) = 2) : x = 2 :=
  PNat.coe_injective (h.trans (show (2 : ℕ) = ((2 : ℕ+) : ℕ) from rfl))

private theorem pnat_eq_three {x : ℕ+} (h : (x : ℕ) = 3) : x = 3 :=
  PNat.coe_injective (h.trans (show (3 : ℕ) = ((3 : ℕ+) : ℕ) from rfl))

theorem crossCap_eq_zero_of_degree : ∀ {d : List ℕ+}, BPSet.degree d = 0 → crossCap d = 0
  | [], _ => rfl
  | x :: rest, h => by
      rw [BPSet.degree_cons] at h
      have hx := x.pos
      have hrest : BPSet.degree rest = 0 := by omega
      obtain rfl : x = 1 := pnat_eq_one (by omega)
      rw [crossCap_cons, crossCap_eq_zero_of_degree hrest]
      decide

theorem crossCap_eq_one_of_degree : ∀ {d : List ℕ+}, BPSet.degree d = 1 → crossCap d = 1
  | [], h => absurd h (by decide)
  | x :: rest, h => by
      rw [BPSet.degree_cons] at h
      have hx := x.pos
      rcases Nat.lt_or_ge (x : ℕ) 2 with h1 | h1
      · have hrest : BPSet.degree rest = 1 := by omega
        obtain rfl : x = 1 := pnat_eq_one (by omega)
        rw [crossCap_cons, crossCap_eq_one_of_degree hrest]
        decide
      · have hrest : BPSet.degree rest = 0 := by omega
        obtain rfl : x = 2 := pnat_eq_two (by omega)
        rw [crossCap_cons, crossCap_eq_zero_of_degree hrest]
        decide

/-- **At degree two the capacity is two or three** — the square and the hexagon, told apart by
whether one bead carries both units of degree. -/
theorem crossCap_of_degree_eq_two : ∀ {d : List ℕ+}, BPSet.degree d = 2 →
    crossCap d = 2 ∨ crossCap d = 3
  | [], h => absurd h (by decide)
  | x :: rest, h => by
      rw [BPSet.degree_cons] at h
      have hx := x.pos
      rcases Nat.lt_or_ge (x : ℕ) 2 with h1 | h1
      · have hrest : BPSet.degree rest = 2 := by omega
        obtain rfl : x = 1 := pnat_eq_one (by omega)
        rcases crossCap_of_degree_eq_two hrest with h2 | h3
        · exact Or.inl (by rw [crossCap_cons, h2]; decide)
        · exact Or.inr (by rw [crossCap_cons, h3]; decide)
      rcases Nat.lt_or_ge (x : ℕ) 3 with h2 | h2
      · have hrest : BPSet.degree rest = 1 := by omega
        obtain rfl : x = 2 := pnat_eq_two (by omega)
        exact Or.inl (by rw [crossCap_cons, crossCap_eq_one_of_degree hrest]; decide)
      · have hrest : BPSet.degree rest = 0 := by omega
        obtain rfl : x = 3 := pnat_eq_three (by omega)
        exact Or.inr (by rw [crossCap_cons, crossCap_eq_zero_of_degree hrest]; decide)

/-- A chain of `Ch Zbp` of degree zero is the run on its events. -/
theorem eq_zObj_ones_of_degree_eq_zero {N : ℕ} (h : dimSum a.dims = N) (ha : degree a = 0) :
    a = zObj (𝟙^N) := by
  have hlen : a.dims.length = N := by have := degree_add_length a; omega
  exact Obj.eq_of_dims (by
    rw [zObj_dims, ← hlen]
    exact List.eq_replicate_iff.mpr ⟨rfl, (degree_eq_zero_iff a).mp ha⟩)

/-! ## The two codimension-two shapes, and what they drop

A degree-two chain of the base carries two junctions fewer than the run, and `boundaries` pins the
shape (`boundaries_injective`).  So the two species are two **shapes** — one bead of three, or two
of two — told apart by *which* pair of junctions is missing: consecutive, or not.  The capacity of
each is then a computation, not a discriminant. -/

/-- **A bead of size three drops two consecutive junctions.** -/
theorem boundaries_three_bead (p q : ℕ) :
    boundaries (𝟙^p ++ (3 : ℕ+) :: 𝟙^q) = Finset.range (p + 3 + q + 1) \ {p + 1, p + 2} := by
  rw [boundaries_append, boundaries_cons, boundaries_ones, boundaries_ones, dimSum_replicate]
  ext t
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_range,
    Finset.mem_sdiff, Finset.mem_singleton, show ((3 : ℕ+) : ℕ) = 3 from rfl]
  constructor
  · rintro (ht | ⟨s, (rfl | ⟨u, hu, rfl⟩), rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · rintro ⟨ht, hne⟩
    rcases Nat.lt_or_ge t (p + 1) with h | h
    · exact Or.inl h
    · refine Or.inr ⟨t - p, Or.inr ⟨t - p - 3, by omega, by omega⟩, by omega⟩

private theorem boundaries_two_ones (q : ℕ) :
    boundaries ((2 : ℕ+) :: 𝟙^q) = Finset.range (q + 3) \ {1} := by
  rw [boundaries_cons, boundaries_ones]
  ext t
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range, Finset.mem_sdiff,
    Finset.mem_singleton, show ((2 : ℕ+) : ℕ) = 2 from rfl]
  constructor
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · rintro ⟨ht, hne⟩
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ⟨t - 2, by omega, by omega⟩

private theorem boundaries_ones_two_ones (m q : ℕ) :
    boundaries (𝟙^m ++ (2 : ℕ+) :: 𝟙^q) = Finset.range (m + q + 3) \ {m + 1} := by
  rw [boundaries_append, boundaries_ones, boundaries_two_ones, dimSum_replicate]
  ext t
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro (ht | ⟨s, ⟨hs, hne⟩, rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · rintro ⟨ht, hne⟩
    rcases Nat.lt_or_ge t (m + 1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨t - m, ⟨by omega, by omega⟩, by omega⟩

/-- **Two beads of size two drop two junctions that are not consecutive.** -/
theorem boundaries_two_two_bead (p m q : ℕ) :
    boundaries (𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q))
      = Finset.range (p + m + q + 5) \ {p + 1, p + m + 3} := by
  rw [boundaries_append, boundaries_ones, boundaries_cons, boundaries_ones_two_ones,
    dimSum_replicate]
  ext t
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_range,
    Finset.mem_sdiff, Finset.mem_singleton, show ((2 : ℕ+) : ℕ) = 2 from rfl]
  constructor
  · rintro (ht | ⟨s, (rfl | ⟨u, ⟨hu, hune⟩, rfl⟩), rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · rintro ⟨ht, hne⟩
    rcases Nat.lt_or_ge t (p + 1) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨t - p, Or.inr ⟨t - p - 2, ⟨by omega, by omega⟩, by omega⟩, by omega⟩

/-- **The hexagon's capacity is three.** -/
theorem crossCap_three_bead (p q : ℕ) : crossCap (𝟙^p ++ (3 : ℕ+) :: 𝟙^q) = 3 := by
  rw [crossCap_append, crossCap_cons, crossCap_replicate_one, crossCap_replicate_one]
  decide

/-- **The square's capacity is two.** -/
theorem crossCap_two_two_bead (p m q : ℕ) :
    crossCap (𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q)) = 2 := by
  rw [crossCap_append, crossCap_cons, crossCap_append, crossCap_cons, crossCap_replicate_one,
    crossCap_replicate_one, crossCap_replicate_one]
  decide

/-- **A square's beads carry no crossing of three** — which is what tells it from a hexagon. -/
theorem le_two_of_mem_two_two_bead {p m q : ℕ} {x : ℕ+}
    (hx : x ∈ 𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q)) : x ≤ 2 := by
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
  rcases hx with ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ <;> decide

end Shapes

/-! ## The factorisations whose first leg is one cut

A `Factorisation` is pinned by its middle shape (`Factorisation.ext_dims`), and a middle shape one
junction below the source *is* the junction dropped (`dims_eq_of_cuts_eq`) — so such a
factorisation is its first cut.  At codimension two there are two cuts, hence `Bool`. -/

variable {K : BPSet} {a b : Ch K}

/-- A factorisation whose first leg removes a single boundary. -/
abbrev OneCut (f : a ⟶ b) : Type := {F : Factorisation f // codim F.ι = 1}

/-- At codimension two the second leg is a single cut as well, so `OneCut f` is the set of
factorisations into two codimension-one steps. -/
theorem OneCut.codim_π {f : a ⟶ b} (F : OneCut f) (hf : codim f = 2) : codim F.1.π = 1 := by
  have := codim_comp F.1.ι F.1.π
  rw [F.1.ι_π, hf, F.2] at this
  omega

/-- The first leg's cut set, which is a singleton. -/
theorem OneCut.cutsOf_ι_eq_singleton {f : a ⟶ b} (F : OneCut f) :
    cutsOf F.1.ι = {(exists_cutsOf_eq_singleton F.2).choose} :=
  (exists_cutsOf_eq_singleton F.2).choose_spec

/-- **A one-cut factorisation is its cut.**  Injectivity is `dims_eq_of_cuts_eq` into
`Factorisation.ext_dims`; surjectivity is `exists_factor_first`. -/
noncomputable def oneCutEquivCuts (f : a ⟶ b) : OneCut f ≃ (cutsOf f : Finset ℕ) :=
  Equiv.ofBijective
    (fun F => ⟨_, Finset.mem_sdiff.mpr ⟨(mem_cutsOf F.cutsOf_ι_eq_singleton).1, fun hb =>
      (mem_cutsOf F.cutsOf_ι_eq_singleton).2 (boundaries_subset_of_hom F.1.π hb)⟩⟩)
    ⟨fun F G hFG => Subtype.ext (Factorisation.ext_dims
        (dims_eq_of_cuts_eq F.cutsOf_ι_eq_singleton
          (G.cutsOf_ι_eq_singleton.trans
            (congrArg (fun t => ({t} : Finset ℕ)) (congrArg Subtype.val hFG).symm)))),
     fun t => by
       obtain ⟨c, e, g, hcut, heg⟩ := exists_factor_first f t.2
       refine ⟨⟨⟨c, e, g, heg⟩, codim_eq_one_of_cutsOf hcut⟩, Subtype.ext ?_⟩
       exact Finset.singleton_injective
         ((OneCut.cutsOf_ι_eq_singleton
           ⟨⟨c, e, g, heg⟩, codim_eq_one_of_cutsOf hcut⟩).symm.trans hcut)⟩

/-- **A one-cut factorisation is the junction it names.** -/
theorem coe_oneCutEquivCuts {f : a ⟶ b} (F : OneCut f) {t : ℕ} (h : cutsOf F.1.ι = {t}) :
    (oneCutEquivCuts f F : ℕ) = t :=
  Finset.singleton_injective (F.cutsOf_ι_eq_singleton.symm.trans h)

/-! ### Orienting the two cuts

The two junctions are ordered, so naming one of them `false` is a choice of orientation.  The one
made here is the one the Artin dichotomy reads: **the lower junction at consecutive cuts, the upper
one at cuts apart**.  Both sides spell the same arrow either way; what the orientation fixes is
which word is the *source* of the relation, and the Artin source starts at the lower cut in both
species — a hexagon's word being a palindrome where a square's is not. -/

/-- **Consecutive cuts**: no junction of the source lies between the two a refinement drops, so the
target merges three of the source's beads into one. -/
def CutsAdjacent (f : a ⟶ b) : Prop :=
  ∀ s ∈ cutsOf f, ∀ t ∈ cutsOf f, ∀ u ∈ boundaries a.dims, ¬ (s < u ∧ u < t)

/-- The two junctions in their own order. -/
noncomputable def cutsOrder (f : a ⟶ b) (hf : codim f = 2) : (cutsOf f : Finset ℕ) ≃ Fin 2 :=
  ((cutsOf f).orderIsoOfFin ((card_cutsOf f).trans hf)).symm.toEquiv

open Classical in
/-- **The two junctions, oriented.** -/
noncomputable def cutsEquivBool (f : a ⟶ b) (hf : codim f = 2) :
    (cutsOf f : Finset ℕ) ≃ Bool :=
  (cutsOrder f hf).trans
    (if CutsAdjacent f then finTwoEquiv
      else finTwoEquiv.trans ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩)

/-- **A codimension-two refinement has exactly two factorisations into codimension-one steps**, and
the boolean names which of its two junctions the first leg drops. -/
noncomputable def oneCutEquivBool (f : a ⟶ b) (hf : codim f = 2) : OneCut f ≃ Bool :=
  (oneCutEquivCuts f).trans (cutsEquivBool f hf)

/-- **The `false` factorisation drops the lower junction at consecutive cuts and the upper one at
cuts apart.**  Both clauses are `cutsOrder`'s monotonicity, read through the two branches of the
orientation. -/
theorem oneCutEquivBool_of_lt {f : a ⟶ b} (hf : codim f = 2) {F G : OneCut f}
    (hFG : (oneCutEquivCuts f F : ℕ) < (oneCutEquivCuts f G : ℕ)) :
    (CutsAdjacent f → oneCutEquivBool f hf F = false ∧ oneCutEquivBool f hf G = true) ∧
      (¬ CutsAdjacent f → oneCutEquivBool f hf F = true ∧ oneCutEquivBool f hf G = false) := by
  have hlt : cutsOrder f hf (oneCutEquivCuts f F) < cutsOrder f hf (oneCutEquivCuts f G) :=
    ((cutsOf f).orderIsoOfFin ((card_cutsOf f).trans hf)).symm.lt_iff_lt.mpr
      (Subtype.coe_lt_coe.mp hFG)
  rw [Fin.lt_def] at hlt
  have h1 := (cutsOrder f hf (oneCutEquivCuts f F)).isLt
  have h2 := (cutsOrder f hf (oneCutEquivCuts f G)).isLt
  have hs : cutsOrder f hf (oneCutEquivCuts f F) = 0 := Fin.ext (by omega)
  have ht : cutsOrder f hf (oneCutEquivCuts f G) = 1 := Fin.ext (by omega)
  refine ⟨fun hadj => ?_, fun hadj => ?_⟩ <;>
    rw [oneCutEquivBool, Equiv.trans_apply, Equiv.trans_apply, cutsEquivBool, Equiv.trans_apply,
      Equiv.trans_apply, hs, ht]
  · rw [if_pos hadj]; exact ⟨rfl, rfl⟩
  · rw [if_neg hadj]; exact ⟨rfl, rfl⟩

end ChainCat
