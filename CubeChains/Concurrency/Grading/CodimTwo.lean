import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Merge.Atom
import CubeChains.Concurrency.Merge.Factorisation

/-!
# Concurrency/Grading/CodimTwo — the capacity of a shape, and codimension two at degree zero

Crossings add at every junction of the *target* (`permLen_crossPerm_junction`): `splitTarget` cuts
the wedge map there and `crossPerm` is monoidal over the wedge.  Inducting on the target's beads
turns that into `crossCap`, the reversal inside each bead, which bounds every crossing onto a shape.

At codimension two out of a run the shape is a hexagon or a square, told apart by `boundaries`; the
capacity of each is then a computation.  Factoring is orthogonal to all of it: a factorisation whose
first leg is a single cut *is* that cut (`oneCutEquivCuts`), so there are exactly two, indexed by
`Bool`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains BPSet CubeChain Equiv

namespace ChainCat

section Shapes

variable {a b : Ch Zbp}

/-! ## Crossings add at a junction of the target

`crossPerm` reads the wedge map alone (`crossPerm_eq_of_φ`), so the tensorator law
`permLen_crossPerm_chConcat` applies to *any* morphism whose wedge map is a concatenation — which,
by `splitTarget`, is every morphism read at a junction of its target. -/

/-- **A concatenated wedge map splits its crossing count.** -/
theorem permLen_crossPerm_concat {A₁ A₂ C₁ C₂ : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) (f : zObj (A₁ ++ A₂) ⟶ zObj (C₁ ++ C₂))
    (hf : Hom.φ f = concatHomφ g₁ g₂) {N : ℕ} (h : dimSum (A₁ ++ A₂) = N) :
    permLen (crossPerm h f) = permLen (crossPerm rfl g₁) + permLen (crossPerm rfl g₂) := by
  have hc : crossPerm (dimSum_append A₁ A₂) f
      = crossPerm (dimSum_append A₁ A₂) (zHom (concatHomφ g₁ g₂)) :=
    crossPerm_eq_of_φ (dimSum_append A₁ A₂) hf
  rw [permLen_crossPerm (dimSum_append A₁ A₂) h f, hc, crossPerm_concat, permLen_permSum]
  rfl

/-- **Crossings add at a junction of the target.**  Where the source's own beads fall is
`splitTarget`'s output, not its input, so no hypothesis relates the two shapes. -/
theorem permLen_crossPerm_junction (f : a ⟶ b) {C₁ C₂ : List ℕ+} (hb : b.dims = C₁ ++ C₂)
    {N : ℕ} (h : dimSum a.dims = N) :
    ∃ (A₁ A₂ : List ℕ+) (g₁ : zObj A₁ ⟶ zObj C₁) (g₂ : zObj A₂ ⟶ zObj C₂),
      a.dims = A₁ ++ A₂ ∧
        permLen (crossPerm h f) = permLen (crossPerm rfl g₁) + permLen (crossPerm rfl g₂) := by
  obtain ⟨da, ma⟩ := a
  obtain ⟨db, mb⟩ := b
  dsimp only at hb h
  subst hb
  obtain ⟨A₁, A₂, φ₁, φ₂, hsplit, hmap⟩ :=
    splitTarget (ad := da) (cd₁ := C₁) (cd₂ := C₂) (Hom.φ f)
  subst hsplit
  refine ⟨A₁, A₂, zHom φ₁, zHom φ₂, rfl, ?_⟩
  refine (permLen_crossPerm h rfl f).symm.trans ?_
  refine Eq.trans (congrArg permLen (crossPerm_eq_of_φ (K' := Zbp)
    (ma' := isTerminalZbp.from _) (mb' := isTerminalZbp.from _)
    (g' := zHom (Hom.φ f)) rfl rfl)) ?_
  exact permLen_crossPerm_concat (zHom φ₁) (zHom φ₂) (zHom (Hom.φ f))
    (by simpa [concatHomφ, serialWedgeAppendHom] using hmap) rfl

/-! ## The capacity of a shape

The reversal inside each bead.  It bounds every crossing onto the shape — `permLen` adds at each
junction, and nothing is longer than a reversal — and the greatest refinement out of a run attains
it (`Paper.permLen_runCross_topOf`). -/

/-- The **crossing capacity** of a shape: the reversal inside each bead. -/
def crossCap (d : List ℕ+) : ℕ := (d.map fun x => permLen (Fin.revPerm : Perm (Fin (x : ℕ)))).sum

@[simp] theorem crossCap_nil : crossCap [] = 0 := rfl

@[simp] theorem crossCap_cons (x : ℕ+) (d : List ℕ+) :
    crossCap (x :: d) = permLen (Fin.revPerm : Perm (Fin (x : ℕ))) + crossCap d := rfl

@[simp] theorem crossCap_append (d e : List ℕ+) :
    crossCap (d ++ e) = crossCap d + crossCap e := by
  simp [crossCap, List.sum_append]

/-- An edge has no pair to cross. -/
@[simp] theorem crossCap_replicate_one (n : ℕ) : crossCap (𝟙^n) = 0 := by
  induction n with
  | zero => rfl
  | succ k hk => rw [List.replicate_succ, crossCap_cons, hk]; decide

/-- **The capacity bounds every crossing onto a shape.**  Induction on the target's beads: each
junction splits the count, and onto one bead nothing beats the reversal. -/
theorem permLen_crossPerm_le_crossCap : ∀ (C : List ℕ+) {a b : Ch Zbp} (f : a ⟶ b),
    b.dims = C → ∀ {N : ℕ} (h : dimSum a.dims = N), permLen (crossPerm h f) ≤ crossCap C
  | [], _, b, f, hb, N, h => by
      obtain rfl : N = 0 := by rw [← h, dimSum_eq_of_hom f, hb]; rfl
      refine (permLen_le_revPerm _).trans ?_
      rw [crossCap_nil]
      decide
  | x :: C, _, _, f, hb, _, h => by
      obtain ⟨A₁, A₂, g₁, g₂, -, hlen⟩ :=
        permLen_crossPerm_junction f (C₁ := [x]) (C₂ := C) hb h
      have hx : dimSum A₁ = (x : ℕ) := (dimSum_eq_of_hom g₁).trans (dimSum_single x)
      refine hlen.trans_le (Nat.add_le_add ?_ (permLen_crossPerm_le_crossCap C g₂ rfl rfl))
      exact (permLen_crossPerm hx rfl g₁).trans_le (permLen_le_revPerm _)

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

A `Factorisation` is its middle shape (`factorisationEquiv`), and a middle shape one junction below
the source *is* the junction dropped (`dims_eq_of_cuts_eq`) — so such a factorisation is its first
cut.  At codimension two there are two cuts, hence `Bool`. -/

variable {K : BPSet} {a b : Ch K}

/-- A factorisation whose first leg removes a single boundary. -/
abbrev OneCut (f : a ⟶ b) : Type := {F : Factorisation f // codim F.fst = 1}

/-- At codimension two the second leg is a single cut as well, so `OneCut f` is the set of
factorisations into two codimension-one steps. -/
theorem OneCut.codim_snd {f : a ⟶ b} (F : OneCut f) (hf : codim f = 2) : codim F.1.snd = 1 := by
  have := codim_comp F.1.fst F.1.snd
  rw [F.1.comp, hf, F.2] at this
  omega

/-- The first leg's cut set, which is a singleton. -/
theorem OneCut.cutsOf_fst_eq_singleton {f : a ⟶ b} (F : OneCut f) :
    cutsOf F.1.fst = {(exists_cutsOf_eq_singleton F.2).choose} :=
  (exists_cutsOf_eq_singleton F.2).choose_spec

/-- **A one-cut factorisation is its cut.**  Injectivity is `dims_eq_of_cuts_eq` into
`Factorisation.ext_dims`; surjectivity is `exists_factor_first`. -/
noncomputable def oneCutEquivCuts (f : a ⟶ b) : OneCut f ≃ (cutsOf f : Finset ℕ) :=
  Equiv.ofBijective
    (fun F => ⟨_, Finset.mem_sdiff.mpr ⟨(mem_cutsOf F.cutsOf_fst_eq_singleton).1, fun hb =>
      (mem_cutsOf F.cutsOf_fst_eq_singleton).2 (boundaries_subset_of_hom F.1.snd hb)⟩⟩)
    ⟨fun F G hFG => Subtype.ext (Factorisation.ext_dims
        (dims_eq_of_cuts_eq F.cutsOf_fst_eq_singleton
          (G.cutsOf_fst_eq_singleton.trans
            (congrArg (fun t => ({t} : Finset ℕ)) (congrArg Subtype.val hFG).symm)))),
     fun t => by
       obtain ⟨c, e, g, hcut, heg⟩ := exists_factor_first f t.2
       refine ⟨⟨⟨c, e, g, heg⟩, codim_eq_one_of_cutsOf hcut⟩, Subtype.ext ?_⟩
       exact Finset.singleton_injective
         ((OneCut.cutsOf_fst_eq_singleton
           ⟨⟨c, e, g, heg⟩, codim_eq_one_of_cutsOf hcut⟩).symm.trans hcut)⟩

/-- **A one-cut factorisation is the junction it names.** -/
theorem coe_oneCutEquivCuts {f : a ⟶ b} (F : OneCut f) {t : ℕ} (h : cutsOf F.1.fst = {t}) :
    (oneCutEquivCuts f F : ℕ) = t :=
  Finset.singleton_injective (F.cutsOf_fst_eq_singleton.symm.trans h)

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
