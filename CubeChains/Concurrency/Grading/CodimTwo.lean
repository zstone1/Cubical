import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Merge.Factorisation

/-!
# Concurrency/Grading/CodimTwo — the capacity of a shape, and codimension two at degree zero

Crossings add at every junction of the *target* (`permLen_crossPerm_junction`): `splitTarget` cuts
the wedge map there and `crossPerm` is monoidal over the wedge.  Inducting on the target's beads
turns that into `crossCap`, the reversal inside each bead, which is the greatest crossing a run can
perform onto a shape (`isGreatest_permLen_crossPerm`).

Factoring is orthogonal to all of it: a factorisation whose first leg is a single cut *is* that cut
(`oneCutEquivCuts`), so at codimension two there are exactly two, indexed by `Bool`.
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
  have hcat : crossPerm (N := dimSum (A₁ ++ A₂)) rfl f
      = crossPerm rfl ((chConcat Zbp Zbp).map (X := (zObj A₁, zObj A₂))
          (Y := (zObj C₁, zObj C₂)) (g₁, g₂)) :=
    crossPerm_eq_of_φ rfl hf
  refine (permLen_crossPerm h rfl f).symm.trans ((congrArg permLen hcat).trans ?_)
  exact permLen_crossPerm_chConcat (ab := (zObj A₁, zObj A₂)) (ab' := (zObj C₁, zObj C₂)) (g₁, g₂)

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

/-- **Concatenating realises the sum of two crossing counts** — `permLen_crossPerm_concat` read
forwards, with the two shapes given by equations so no caller has to transport. -/
theorem exists_permLen_crossPerm_add {A₁ A₂ C₁ C₂ A C : List ℕ+} (g₁ : zObj A₁ ⟶ zObj C₁)
    (g₂ : zObj A₂ ⟶ zObj C₂) (hA : A = A₁ ++ A₂) (hC : C = C₁ ++ C₂) {N : ℕ}
    (h : dimSum A = N) :
    ∃ f : zObj A ⟶ zObj C,
      permLen (crossPerm h f) = permLen (crossPerm rfl g₁) + permLen (crossPerm rfl g₂) := by
  subst hA
  subst hC
  exact ⟨zHom (concatHomφ g₁ g₂), permLen_crossPerm_concat g₁ g₂ _ rfl h⟩

/-! ## The capacity of a shape

The reversal inside each bead.  It bounds every crossing onto the shape — `permLen` adds at each
junction, and nothing is longer than a reversal — and a run attains it. -/

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

theorem crossCap_eq_zero_of_ones {d : List ℕ+} (hd : ∀ x ∈ d, x = 1) : crossCap d = 0 := by
  rw [List.eq_replicate_iff.mpr ⟨rfl, hd⟩, crossCap_replicate_one]

/-- A bead with two events to reverse has a crossing to make. -/
theorem eq_one_of_permLen_revPerm_eq_zero {y : ℕ+}
    (hy : permLen (Fin.revPerm : Perm (Fin (y : ℕ))) = 0) : y = 1 := by
  have hle : (y : ℕ) ≤ 1 := by
    by_contra hlt
    have h2 : 0 < (y : ℕ) := y.2
    have h1 : (Fin.revPerm : Perm (Fin (y : ℕ))) = 1 := eq_one_of_permLen_eq_zero _ hy
    have := congrArg (fun σ : Perm (Fin (y : ℕ)) => ((σ ⟨0, h2⟩ : Fin (y : ℕ)) : ℕ)) h1
    simp only [Fin.revPerm_apply, Fin.val_rev, Equiv.Perm.coe_one, id_eq] at this
    omega
  exact PNat.coe_injective (Nat.le_antisymm hle y.2)

/-- **…and only an all-edges shape has no capacity.** -/
theorem ones_of_crossCap_eq_zero : ∀ {d : List ℕ+}, crossCap d = 0 → ∀ x ∈ d, x = 1
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: rest, h, x, hx => by
      rw [crossCap_cons] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact eq_one_of_permLen_revPerm_eq_zero (by omega)
      · exact ones_of_crossCap_eq_zero (d := rest) (by omega) x hx

theorem crossCap_eq_zero_iff {d : List ℕ+} : crossCap d = 0 ↔ ∀ x ∈ d, x = 1 :=
  ⟨ones_of_crossCap_eq_zero, crossCap_eq_zero_of_ones⟩

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

/-- **The reversal is realised out of a run onto a single bead** — `onesTopEquiv` is surjective,
and one bead *is* the coarsest shape on its events. -/
theorem exists_crossPerm_eq_revPerm (x : ℕ+) :
    ∃ g : zObj (𝟙^(x : ℕ)) ⟶ zObj [x],
      crossPerm (dimSum_replicate (x : ℕ)) g = Fin.revPerm := by
  rw [← topDims_coe x]
  exact ⟨(onesTopEquiv (x : ℕ)).symm Fin.revPerm,
    (onesTopEquiv (x : ℕ)).apply_symm_apply Fin.revPerm⟩

/-- **A run attains the capacity**: the reversal on each bead, concatenated. -/
theorem exists_permLen_crossPerm_eq_crossCap : ∀ (C : List ℕ+) {N : ℕ}, dimSum C = N →
    ∃ f : zObj (𝟙^N) ⟶ zObj C, permLen (crossPerm (dimSum_replicate N) f) = crossCap C
  | [], N, hC => by
      obtain rfl : N = 0 := hC.symm
      exact ⟨𝟙 _, (congrArg permLen (crossPerm_id _ _)).trans permLen_one⟩
  | x :: C, N, hC => by
      obtain rfl : N = (x : ℕ) + dimSum C := by rw [← hC]; rfl
      obtain ⟨g₁, hg₁⟩ := exists_crossPerm_eq_revPerm x
      obtain ⟨g₂, hg₂⟩ := exists_permLen_crossPerm_eq_crossCap C (N := dimSum C) rfl
      obtain ⟨f, hf⟩ := exists_permLen_crossPerm_add g₁ g₂
        (A := 𝟙^((x : ℕ) + dimSum C)) (C := x :: C) (List.replicate_add _ _ _) rfl
        (dimSum_replicate _)
      refine ⟨f, hf.trans ?_⟩
      rw [permLen_crossPerm (dimSum_replicate (x : ℕ)) rfl g₁, hg₁,
        permLen_crossPerm (dimSum_replicate (dimSum C)) rfl g₂, hg₂, crossCap_cons]

/-- A chain of `Ch Zbp` of degree zero is the run on its events. -/
theorem eq_zObj_ones_of_degree_eq_zero {N : ℕ} (h : dimSum a.dims = N) (ha : degree a = 0) :
    a = zObj (𝟙^N) := by
  have hlen : a.dims.length = N := by have := degree_add_length a; omega
  exact Obj.eq_of_dims (by
    rw [zObj_dims, ← hlen]
    exact List.eq_replicate_iff.mpr ⟨rfl, (degree_eq_zero_iff a).mp ha⟩)

/-- **The greatest crossing out of a run is the target's capacity.** -/
theorem isGreatest_permLen_crossPerm (ha : degree a = 0) {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) :
    IsGreatest (Set.range fun f : a ⟶ b => permLen (crossPerm h f)) (crossCap b.dims) := by
  refine ⟨?_, by rintro _ ⟨f, rfl⟩; exact permLen_crossPerm_le_crossCap b.dims f rfl h⟩
  obtain ⟨f⟩ := hab
  have hN : dimSum b.dims = N := (dimSum_eq_of_hom f).symm.trans h
  obtain rfl := eq_zObj_ones_of_degree_eq_zero h ha
  obtain ⟨bd, bm⟩ := b
  obtain rfl : bm = isTerminalZbp.from (⋁bd) := Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := exists_permLen_crossPerm_eq_crossCap bd hN
  exact ⟨g, hg⟩

/-! ## The two species at degree zero

Out of a run every bead of the source is an edge, so `codim_eq_two_iff`'s two shapes have all their
sizes forced — one bead of size three, or two of size two — and the flanking stretches carry no
capacity.  That is the **one** place the codimension-two dichotomy is read, and the capacity is what
tells the two apart: `3` against `2`. -/

/-- **The capacity of a degree-zero codimension-two refinement is its species**: three for the one
bead of size three (the braid relation), two for the two beads of size two (commutation). -/
theorem crossCap_of_codim_eq_two (f : a ⟶ b) (ha : degree a = 0) (hf : codim f = 2) :
    ((∃ l r : List ℕ+, a.dims = l ++ 1 :: 1 :: 1 :: r ∧ b.dims = l ++ 3 :: r)
        ∧ crossCap b.dims = 3) ∨
      ((∃ l m r : List ℕ+, a.dims = l ++ 1 :: 1 :: (m ++ 1 :: 1 :: r) ∧
          b.dims = l ++ 2 :: (m ++ 2 :: r)) ∧ crossCap b.dims = 2) := by
  have hone : ∀ z ∈ a.dims, z = 1 := (degree_eq_zero_iff a).mp ha
  have hflank : ∀ {l : List ℕ+}, (∀ z ∈ l, z ∈ a.dims) → crossCap l = 0 :=
    fun hsub => crossCap_eq_zero_of_ones fun z hz => hone z (hsub z hz)
  rcases (codim_eq_two_iff f).mp hf with ⟨l, r, p, q, s, hb, ha'⟩ | ⟨l, m, r, p, q, p', q', hb, ha'⟩
  · obtain rfl : p = 1 := hone p (by rw [ha']; simp)
    obtain rfl : q = 1 := hone q (by rw [ha']; simp)
    obtain rfl : s = 1 := hone s (by rw [ha']; simp)
    rw [show (1 + 1 + 1 : ℕ+) = 3 from rfl] at hb
    refine Or.inl ⟨⟨l, r, ha', hb⟩, ?_⟩
    rw [hb, crossCap_append, crossCap_cons,
      hflank fun z hz => by rw [ha']; simp [hz], hflank fun z hz => by rw [ha']; simp [hz]]
    decide
  · obtain rfl : p = 1 := hone p (by rw [ha']; simp)
    obtain rfl : q = 1 := hone q (by rw [ha']; simp)
    obtain rfl : p' = 1 := hone p' (by rw [ha']; simp)
    obtain rfl : q' = 1 := hone q' (by rw [ha']; simp)
    rw [show (1 + 1 : ℕ+) = 2 from rfl] at hb
    refine Or.inr ⟨⟨l, m, r, ha', hb⟩, ?_⟩
    rw [hb, crossCap_append, crossCap_cons, crossCap_append, crossCap_cons,
      hflank fun z hz => by rw [ha']; simp [hz], hflank fun z hz => by rw [ha']; simp [hz],
      hflank fun z hz => by rw [ha']; simp [hz]]
    decide

/-- **A bead of size three drops two consecutive junctions** — which is what tells a hexagon's two
cuts from a square's. -/
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

/-! ### The species, read off `cutsOf`

`crossCap_of_codim_eq_two` gives the two shapes; `boundaries_three_bead` says which junctions the
size-three one drops.  Put together, the species of a codimension-two refinement of the run is
**whether its two cuts are consecutive** — which is the form the Artin dichotomy consumes, a hexagon
at adjacent cuts and a square at cuts apart.  Nothing below needs the shapes again. -/

/-- **Capacity three means the two cuts are consecutive** — the one bead of size three drops two
adjacent junctions and nothing else. -/
theorem cuts_adjacent_of_crossCap_eq_three {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b)
    (hf : codim f = 2) (hcap : crossCap b.dims = 3) {s t : ℕ} (hcut : cutsOf f = {s, t})
    (hst : s < t) : t = s + 1 := by
  rcases crossCap_of_codim_eq_two f (degree_ones N) hf with ⟨⟨l, r, hones, hdims⟩, -⟩ | ⟨-, h2⟩
  swap
  · exact absurd (hcap.symm.trans h2) (by decide)
  rw [zObj_dims] at hones
  have hall : ∀ c ∈ l ++ (1 : ℕ+) :: 1 :: 1 :: r, c = 1 := by
    rw [← hones]; exact fun c hc => List.eq_of_mem_replicate hc
  obtain ⟨p, rfl⟩ : ∃ p, l = 𝟙^p :=
    ⟨l.length, List.eq_replicate_of_mem fun c hc => hall c (by simp [hc])⟩
  obtain ⟨q, rfl⟩ : ∃ q, r = 𝟙^q :=
    ⟨r.length, List.eq_replicate_of_mem fun c hc => hall c (by simp [hc])⟩
  have hlen : p + 3 + q = N := by
    have h := congrArg List.length hones
    simp only [List.length_replicate, List.length_append, List.length_cons] at h
    omega
  have hsub : ({p + 1, p + 2} : Finset ℕ) ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    omega
  have hpair : ({s, t} : Finset ℕ) = {p + 1, p + 2} := by
    rw [← hcut, cutsOf, zObj_dims, boundaries_ones, hdims, boundaries_three_bead, hlen,
      Finset.sdiff_sdiff_eq_self hsub]
  have hmem : ∀ x : ℕ, x ∈ ({s, t} : Finset ℕ) ↔ x ∈ ({p + 1, p + 2} : Finset ℕ) := fun x => by
    rw [hpair]
  have h1 := (hmem s).mp (by simp)
  have h2 := (hmem t).mp (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega

/-- **…so cuts that are apart have capacity two** — the square, by elimination against the only
other species. -/
theorem crossCap_eq_two_of_cuts_apart {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b)
    (hf : codim f = 2) {s t : ℕ} (hcut : cutsOf f = {s, t}) (hst : s + 1 < t) :
    crossCap b.dims = 2 := by
  rcases (crossCap_of_codim_eq_two f (degree_ones N) hf).imp (fun h => h.2) (fun h => h.2) with
    h3 | h2
  · exact absurd (cuts_adjacent_of_crossCap_eq_three f hf h3 hcut (by omega)) (by omega)
  · exact h2

/-- **The crossing length is not a function of the species.**  The merge onto one bead of size three
has codimension two out of a run and crosses nothing, so the capacity is attained only at the top of
the hom-set. -/
theorem exists_codim_eq_two_crossPerm_eq_one :
    ∃ (c : Ch Zbp) (f : zObj (𝟙^3) ⟶ c), degree (zObj (𝟙^3)) = 0 ∧ codim f = 2 ∧
      crossPerm (dimSum_replicate 3) f = 1 := by
  obtain ⟨f, hf⟩ := exists_W_to_top (a := zObj (𝟙^3)) (dimSum_replicate 3)
  exact ⟨_, f, rfl, rfl, (W_iff_crossPerm_eq_one _ f).mp hf⟩

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

/-- Reading the two junctions in their own order. -/
noncomputable def cutsEquivFinTwo (f : a ⟶ b) (hf : codim f = 2) :
    (cutsOf f : Finset ℕ) ≃ Fin 2 :=
  ((cutsOf f).orderIsoOfFin ((card_cutsOf f).trans hf)).symm.toEquiv

/-- **The lower junction comes first.** -/
theorem cutsEquivFinTwo_lt {f : a ⟶ b} (hf : codim f = 2) {s t : (cutsOf f : Finset ℕ)}
    (hst : (s : ℕ) < (t : ℕ)) :
    cutsEquivFinTwo f hf s = 0 ∧ cutsEquivFinTwo f hf t = 1 := by
  have h : cutsEquivFinTwo f hf s < cutsEquivFinTwo f hf t :=
    ((cutsOf f).orderIsoOfFin ((card_cutsOf f).trans hf)).symm.lt_iff_lt.mpr
      (Subtype.coe_lt_coe.mp hst)
  rw [Fin.lt_def] at h
  have h1 := (cutsEquivFinTwo f hf s).isLt
  have h2 := (cutsEquivFinTwo f hf t).isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

open Classical in
/-- **The two junctions, oriented.** -/
noncomputable def cutsEquivBool (f : a ⟶ b) (hf : codim f = 2) :
    (cutsOf f : Finset ℕ) ≃ Bool :=
  (cutsEquivFinTwo f hf).trans
    (if CutsAdjacent f then finTwoEquiv
      else finTwoEquiv.trans ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩)

/-- **The lower junction is the `false` one at consecutive cuts and the `true` one at cuts apart.**
Both clauses are the same `cutsEquivFinTwo_lt`, read through the two branches of the orientation. -/
theorem cutsEquivBool_lt {f : a ⟶ b} (hf : codim f = 2) {s t : (cutsOf f : Finset ℕ)}
    (hst : (s : ℕ) < (t : ℕ)) :
    (CutsAdjacent f → cutsEquivBool f hf s = false ∧ cutsEquivBool f hf t = true) ∧
      (¬ CutsAdjacent f → cutsEquivBool f hf s = true ∧ cutsEquivBool f hf t = false) := by
  obtain ⟨hs, ht⟩ := cutsEquivFinTwo_lt hf hst
  refine ⟨fun hadj => ?_, fun hadj => ?_⟩ <;>
    rw [cutsEquivBool, Equiv.trans_apply, Equiv.trans_apply, hs, ht]
  · rw [if_pos hadj]; exact ⟨rfl, rfl⟩
  · rw [if_neg hadj]; exact ⟨rfl, rfl⟩

/-- **A codimension-two refinement has exactly two factorisations into codimension-one steps**, and
the boolean names which of its two junctions the first leg drops. -/
noncomputable def oneCutEquivBool (f : a ⟶ b) (hf : codim f = 2) : OneCut f ≃ Bool :=
  (oneCutEquivCuts f).trans (cutsEquivBool f hf)

/-- **The `false` factorisation drops the lower junction at consecutive cuts and the upper one at
cuts apart.** -/
theorem oneCutEquivBool_of_lt {f : a ⟶ b} (hf : codim f = 2) {F G : OneCut f}
    (hFG : (oneCutEquivCuts f F : ℕ) < (oneCutEquivCuts f G : ℕ)) :
    (CutsAdjacent f → oneCutEquivBool f hf F = false ∧ oneCutEquivBool f hf G = true) ∧
      (¬ CutsAdjacent f → oneCutEquivBool f hf F = true ∧ oneCutEquivBool f hf G = false) :=
  cutsEquivBool_lt hf hFG

end ChainCat
