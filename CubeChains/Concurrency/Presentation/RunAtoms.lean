import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Machinery.Braid.MatsumotoCat
import Mathlib.Data.Fintype.Lattice

/-!
# Concurrency/Presentation/RunAtoms — the runs over a shape, and the polygon of a degree-two one

A run over a shape of `Ch Zbp` is a refinement out of the run on its events, pinned by its crossing
permutation, so the runs are a lower set of the right weak order (`shapeLower`).  An ascent between
two of them is an atom over the shape (`ascLeg`), a refinement of shapes carries the runs along by
composition, and the longest run (`shapeTop`) descends through every atom over the shape.

Over a degree-two shape the lower set is a polygon: the longest run crosses the alternating word of
the two junctions in either order (`crossPerm_shapeTop`), and the two maximal climbs from the bottom
alternately through them end there (`polyClimb`).
-/

open CategoryTheory Opposite BPSet CubeChains Equiv

namespace ChainCat

/-! ## The runs over a shape

A run over a shape is a refinement out of the run on `N` events.  It is pinned by its crossing
permutation (`hom_ext_of_crossPerm`), so the runs index the permutations they realise faithfully,
and the exchange `exists_run_mul_adjT` closes them downwards. -/

/-- **The runs over a shape are a lower set of the right weak order.** -/
noncomputable def shapeLower (N : ℕ) (s : Ch Zbp) : WeakOrder.Lower N (zObj (𝟙^N) ⟶ s) where
  perm := crossPerm (dimSum_replicate N)
  perm_inj _ _ h := hom_ext_of_crossPerm h
  isLowerSet := WeakOrder.isLowerSet_of_covBy (by
    rintro x _ hcov ⟨σ, rfl⟩
    obtain ⟨k, hd, hx⟩ := WeakOrder.covBy_iff.mp hcov
    simp only [WeakOrder.perm_of] at hd hx
    obtain ⟨r, hr⟩ := exists_run_mul_adjT (dimSum_eq_of_onesHom σ) σ hd
    exact ⟨r, congrArg WeakOrder.of (hr.trans hx.symm)⟩)

@[simp] theorem shapeLower_perm (N : ℕ) (s : Ch Zbp) (σ : zObj (𝟙^N) ⟶ s) :
    (shapeLower N s).perm σ = crossPerm (dimSum_replicate N) σ := rfl

/-- **Every run is climbed to from the merge.** -/
theorem runMerge_le {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (σ : zObj (𝟙^N) ⟶ s) :
    WeakOrder.of ((shapeLower N s).perm (runMerge s hs))
      ≤ WeakOrder.of ((shapeLower N s).perm σ) := by
  rw [shapeLower_perm, shapeLower_perm, crossPerm_runMerge]
  exact WeakOrder.le_of_mul_eq (one_mul _) (by rw [permLen_one, Nat.add_zero])

/-! ## The longest run over a shape

The runs over a shape are finitely many, so one is longest.  It descends through every atom over the
shape — ascending through one climbs to a longer run (`exists_atom_step`) — and a descent of any run
is such an atom (`nonempty_atomComp_of_descent`). -/

theorem exists_longest {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    ∃ σ : zObj (𝟙^N) ⟶ s, ∀ τ : zObj (𝟙^N) ⟶ s,
      permLen (crossPerm (dimSum_replicate N) τ) ≤ permLen (crossPerm (dimSum_replicate N) σ) :=
  haveI : Finite (zObj (𝟙^N) ⟶ s) := Finite.of_injective _ (shapeLower N s).perm_inj
  haveI : Nonempty (zObj (𝟙^N) ⟶ s) := ⟨runMerge s hs⟩
  Finite.exists_max fun σ : zObj (𝟙^N) ⟶ s => permLen (crossPerm (dimSum_replicate N) σ)

/-- **The longest run over a shape.** -/
noncomputable def shapeTop {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) : zObj (𝟙^N) ⟶ s :=
  (exists_longest s hs).choose

theorem permLen_le_shapeTop {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (τ : zObj (𝟙^N) ⟶ s) :
    permLen (crossPerm (dimSum_replicate N) τ)
      ≤ permLen (crossPerm (dimSum_replicate N) (shapeTop s hs)) :=
  (exists_longest s hs).choose_spec τ

/-- **The longest run descends through every atom over the shape.** -/
theorem descent_shapeTop {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) {k : Fin (N - 1)}
    (hk : Nonempty (zObj (atomComp N k) ⟶ s)) :
    crossPerm (dimSum_replicate N) (shapeTop s hs) (adjHi k)
      < crossPerm (dimSum_replicate N) (shapeTop s hs) (adjLo k) :=
  (ascent_or_descent _ k).resolve_left fun ha => by
    obtain ⟨w, -, hw⟩ := exists_atom_step hk (t := shapeTop s hs) rfl ha
    have h := permLen_le_shapeTop hs (atomOnes N k ≫ w)
    rw [hw, permLen_mul_adjT ha] at h
    omega

/-- **Over a degree-zero shape the only run is the merge** — a descent would be an atom over it. -/
theorem crossPerm_eq_one_of_degree_zero {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N)
    (h0 : degree s = 0) (σ : zObj (𝟙^N) ⟶ s) : crossPerm (dimSum_replicate N) σ = 1 :=
  eq_one_of_no_adjacent_descent _ fun k hk => by
    have h := degree_le_of_hom (nonempty_atomComp_of_descent hs σ hk).some
    rw [degree_atomComp, h0] at h
    omega

/-- **Over an atom's shape the longest run is the atom.** -/
theorem shapeTop_atomComp {N : ℕ} (k : Fin (N - 1)) (hs : dimSum (atomComp N k) = N) :
    shapeTop (zObj (atomComp N k)) hs = atomOnes N k :=
  eq_atomOnes fun hW => by
    have h := descent_shapeTop hs ⟨𝟙 (zObj (atomComp N k))⟩
    rw [crossPerm_eq_one_of_W _ hW, Perm.one_apply, Perm.one_apply] at h
    exact absurd h (not_lt.mpr (adjLo_lt_adjHi k).le)

/-- **…so over a degree-one shape it crosses one pair.** -/
theorem permLen_shapeTop_of_degree_one {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N)
    (h1 : degree s = 1) : permLen (crossPerm (dimSum_replicate N) (shapeTop s hs)) = 1 := by
  obtain ⟨k, rfl⟩ := exists_atomComp (runMerge s hs) (by rw [codim, h1, degree_ones])
  rw [shapeTop_atomComp k hs, crossPerm_atomOnes, permLen_adjT]

/-! ## An ascent is an atom over the shape

At an ascent the run below factors through the `k`-th atom shape and the one above crosses it
(`exists_atom_step`), so the leg is a chain of atom shape over the shape. -/

section Asc

variable {N : ℕ} {s : Ch Zbp}

private theorem exists_ascLeg {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    ∃ w : zObj (atomComp N e.idx) ⟶ s, mergeOnes N e.idx ≫ w = a ∧ atomOnes N e.idx ≫ w = b := by
  obtain ⟨w, hw, hw'⟩ := exists_atom_step
    (nonempty_atomComp_of_descent (dimSum_eq_of_onesHom b) b e.descent) (t := a) rfl e.asc
  exact ⟨w, hw, hom_ext_of_crossPerm (hw'.trans e.perm_eq.symm)⟩

/-- The leg an ascent crosses: the atom shape at its index, over the shape. -/
noncomputable def ascLeg {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    zObj (atomComp N e.idx) ⟶ s :=
  (exists_ascLeg e).choose

theorem mergeOnes_ascLeg {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    mergeOnes N e.idx ≫ ascLeg e = a :=
  (exists_ascLeg e).choose_spec.1

theorem atomOnes_ascLeg {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    atomOnes N e.idx ≫ ascLeg e = b :=
  (exists_ascLeg e).choose_spec.2

end Asc

/-! ## A refinement of shapes carries the runs along

Crossings compose, so a run over the source read over the target is left translation by the
refinement's crossing, and the lengths add: covers go to covers. -/

section Push

variable {N : ℕ} {s s' : Ch Zbp} (t : s ⟶ s')

/-- **Pushing an ascent** — crossings add, so the length still goes up by one. -/
noncomputable def pushAscent {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    Ascent (shapeLower N s').perm (a ≫ t) (b ≫ t) where
  idx := e.idx
  asc := by
    have hperm : crossPerm (dimSum_replicate N) (b ≫ t)
        = crossPerm (dimSum_replicate N) (a ≫ t) * adjT e.idx := by
      rw [crossPerm_comp, crossPerm_comp, mul_assoc]
      exact congrArg (crossPerm (tgtStrands a (dimSum_replicate N)) t * ·) e.perm_eq
    refine ascent_of_permLen_mul_adjT ?_
    rw [shapeLower_perm, ← hperm, permLen_crossPerm_comp (dimSum_replicate N) b t,
      permLen_crossPerm_comp (dimSum_replicate N) a t]
    have := e.permLen_eq
    simp only [shapeLower_perm] at this
    omega
  perm_eq := by
    rw [shapeLower_perm, shapeLower_perm, crossPerm_comp, crossPerm_comp, mul_assoc]
    exact congrArg (crossPerm (tgtStrands a (dimSum_replicate N)) t * ·) e.perm_eq

/-- …so a whole climb pushes, by `mapPath`. -/
noncomputable def pushPre : Ascents (shapeLower N s).perm ⥤q Ascents (shapeLower N s').perm where
  obj σ := σ ≫ t
  map e := pushAscent t e

/-- The leg of a pushed ascent is its own leg, composed with the refinement. -/
theorem ascLeg_pushAscent {a b : zObj (𝟙^N) ⟶ s} (e : Ascent (shapeLower N s).perm a b) :
    ascLeg (pushAscent t e) = ascLeg e ≫ t := by
  have key : ∀ x : zObj (atomComp N e.idx) ⟶ s', crossPerm (dimSum_replicate N)
      (mergeOnes N e.idx ≫ x) = crossPerm (dimSum_atomComp N e.idx) x := fun x => by
    rw [crossPerm_comp, crossPerm_eq_one_of_W _ (W_mergeOnes N e.idx), mul_one]
  refine hom_ext_of_crossPerm ((key _).symm.trans (Eq.trans ?_ (key _)))
  exact congrArg (crossPerm _) ((mergeOnes_ascLeg (pushAscent t e)).trans
    ((congrArg (· ≫ t) (mergeOnes_ascLeg e)).symm.trans (Category.assoc _ _ _)))

end Push

/-! ## The two junctions of a degree-two shape -/

/-- An ordered pair of distinct cuts. -/
def AtomPair (N : ℕ) : Type := {p : Fin (N - 1) × Fin (N - 1) // (p.1 : ℕ) < (p.2 : ℕ)}

namespace AtomPair

variable {N : ℕ} (p : AtomPair N)

/-- the lower cut -/
abbrev lo : Fin (N - 1) := p.1.1

/-- the upper cut -/
abbrev hi : Fin (N - 1) := p.1.2

theorem lt : (p.lo : ℕ) < (p.hi : ℕ) := p.2

theorem ne : (p.lo : ℕ) ≠ (p.hi : ℕ) := Nat.ne_of_lt p.2

theorem ext' {p q : AtomPair N} (hlo : p.lo = q.lo) (hhi : p.hi = q.hi) : p = q :=
  Subtype.ext (Prod.ext hlo hhi)

end AtomPair

/-- The two junctions a degree-two shape drops, in order. -/
noncomputable def shapePair {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) (h2 : degree s = 2) :
    AtomPair N :=
  have h := exists_atomPair_of_codim_two (runMerge s hs) (by rw [codim, h2, degree_ones])
  ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec.1⟩

/-- **The atoms over a degree-two shape are its two junctions'.** -/
theorem nonempty_atomComp_iff {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (h2 : degree s = 2)
    (k : Fin (N - 1)) :
    Nonempty (zObj (atomComp N k) ⟶ s) ↔ k = (shapePair s hs h2).lo ∨ k = (shapePair s hs h2).hi :=
  (exists_atomPair_of_codim_two (runMerge s hs) (by rw [codim, h2, degree_ones])).choose_spec
    |>.choose_spec.2 k

theorem nonempty_atomComp_lo {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (h2 : degree s = 2) :
    Nonempty (zObj (atomComp N (shapePair s hs h2).lo) ⟶ s) :=
  (nonempty_atomComp_iff hs h2 _).mpr (Or.inl rfl)

theorem nonempty_atomComp_hi {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (h2 : degree s = 2) :
    Nonempty (zObj (atomComp N (shapePair s hs h2).hi) ⟶ s) :=
  (nonempty_atomComp_iff hs h2 _).mpr (Or.inr rfl)

/-! ## The polygon over a degree-two shape

Climbing from the bottom alternately through two junctions spells the alternating word, and every
prefix is realised because each letter crosses a junction the shape has (`exists_atom_step`). -/

section Rise

variable {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) {i k : Fin (N - 1)}
  (hik : (i : ℕ) ≠ (k : ℕ)) (hi : Nonempty (zObj (atomComp N i) ⟶ s))
  (hk : Nonempty (zObj (atomComp N k) ⟶ s))

include hs hik hi hk in
theorem exists_rise : ∀ t ≤ cox i k,
    ∃ σ : zObj (𝟙^N) ⟶ s, crossPerm (dimSum_replicate N) σ = altWord i k t
  | 0, _ => ⟨runMerge s hs, (crossPerm_runMerge s hs).trans (altWord_zero i k).symm⟩
  | t + 1, ht => by
      obtain ⟨σ, hσ⟩ := exists_rise t (Nat.le_of_succ_le ht)
      have hm : Nonempty (zObj (atomComp N (altIdx i k t)) ⟶ s) := by
        rcases altIdx_cases i k t with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> assumption
      obtain ⟨w, -, hw⟩ := exists_atom_step hm hσ (hσ ▸ ascent_altWord hik ht)
      exact ⟨atomOnes N (altIdx i k t) ≫ w, by rw [hw, altWord_succ]⟩

/-- The `t`-th run the climb through `i, k` reaches. -/
noncomputable def riseElem : (t : ℕ) → t ≤ cox i k → (zObj (𝟙^N) ⟶ s)
  | 0, _ => runMerge s hs
  | t + 1, ht => (exists_rise hs hik hi hk (t + 1) ht).choose

theorem riseElem_val : ∀ (t : ℕ) (ht : t ≤ cox i k),
    crossPerm (dimSum_replicate N) (riseElem hs hik hi hk t ht) = altWord i k t
  | 0, _ => (crossPerm_runMerge s hs).trans (altWord_zero i k).symm
  | t + 1, ht => (exists_rise hs hik hi hk (t + 1) ht).choose_spec

/-- The ascent into a run crossing one more letter of the alternating word: the `t`-th letter. -/
noncomputable def riseAsc (t : ℕ) (ht : t + 1 ≤ cox i k) {σ : zObj (𝟙^N) ⟶ s}
    (hσ : crossPerm (dimSum_replicate N) σ = altWord i k (t + 1)) :
    Ascent (shapeLower N s).perm (riseElem hs hik hi hk t (Nat.le_of_succ_le ht)) σ where
  idx := altIdx i k t
  asc := by rw [shapeLower_perm, riseElem_val]; exact ascent_altWord hik ht
  perm_eq := by rw [shapeLower_perm, shapeLower_perm, riseElem_val, hσ, altWord_succ]

/-- **The climb from the bottom alternately through `i` and `k`** — `i` first. -/
noncomputable def riseClimb : (t : ℕ) → (ht : t ≤ cox i k) →
    Climb (shapeLower N s).perm (runMerge s hs) (riseElem hs hik hi hk t ht)
  | 0, _ => Quiver.Path.nil
  | t + 1, ht => (riseClimb t (Nat.le_of_succ_le ht)).cons
      (riseAsc hs hik hi hk t ht (riseElem_val hs hik hi hk (t + 1) ht))

/-- **The maximal climb through `i` and `k`**, `i` first, into any run crossing the whole
alternating word. -/
noncomputable def polyClimb {σ : zObj (𝟙^N) ⟶ s}
    (hσ : crossPerm (dimSum_replicate N) σ = altWord i k (cox i k)) :
    Climb (shapeLower N s).perm (runMerge s hs) σ :=
  (riseClimb hs hik hi hk (cox i k - 1) (Nat.sub_le _ _)).cons
    (riseAsc hs hik hi hk (cox i k - 1) (by have := two_le_cox hik; omega)
      (by rw [Nat.sub_add_cancel (by have := two_le_cox hik; omega)]; exact hσ))

/-- **A maximal climb ends in its last letter.** -/
theorem polyClimb_eq_cons {σ : zObj (𝟙^N) ⟶ s}
    (hσ : crossPerm (dimSum_replicate N) σ = altWord i k (cox i k)) :
    ∃ (x : zObj (𝟙^N) ⟶ s) (R : Climb (shapeLower N s).perm (runMerge s hs) x)
      (f : Ascent (shapeLower N s).perm x σ),
      polyClimb hs hik hi hk hσ = R.cons f ∧ f.idx = altIdx i k (cox i k - 1) :=
  ⟨_, _, _, rfl, rfl⟩

end Rise

/-- **Over a degree-two shape the longest run is the polygon's top** — it descends through both
junctions, so its foot ascends through both, and a descent of the foot would be a third junction. -/
theorem shapeTop_val_of_degree_two {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N)
    (h2 : degree s = 2) :
    crossPerm (dimSum_replicate N) (shapeTop s hs)
      = altWord (shapePair s hs h2).lo (shapePair s hs h2).hi
        (cox (shapePair s hs h2).lo (shapePair s hs h2).hi) := by
  have hlo := descent_shapeTop hs (nonempty_atomComp_lo hs h2)
  have hhi := descent_shapeTop hs (nonempty_atomComp_hi hs h2)
  obtain ⟨τ, hτ⟩ := (shapeLower N s).exists_of_le (v := shapeTop s hs)
    (polyFoot_le (shapePair s hs h2).ne hlo hhi)
  have hτ' : crossPerm (dimSum_replicate N) τ
      = polyFoot (crossPerm (dimSum_replicate N) (shapeTop s hs)) (shapePair s hs h2).lo
        (shapePair s hs h2).hi := congrArg WeakOrder.perm hτ
  have hfoot : polyFoot (crossPerm (dimSum_replicate N) (shapeTop s hs)) (shapePair s hs h2).lo
      (shapePair s hs h2).hi = 1 :=
    eq_one_of_no_adjacent_descent _ fun m hm => absurd hm (not_lt.mpr
      (ascent_polyFoot (shapePair s hs h2).ne hlo hhi ((nonempty_atomComp_iff hs h2 m).mp
        (nonempty_atomComp_of_descent hs τ (hτ' ▸ hm)))).le)
  rw [polyFoot, mul_eq_one_iff_eq_inv] at hfoot
  exact hfoot.trans (altWord_cox_inv (shapePair s hs h2).ne)

/-- **…through its two junctions in either order**, so both maximal climbs end there. -/
theorem crossPerm_shapeTop {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) (h2 : degree s = 2)
    {i k : Fin (N - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) (hi : Nonempty (zObj (atomComp N i) ⟶ s))
    (hk : Nonempty (zObj (atomComp N k) ⟶ s)) :
    crossPerm (dimSum_replicate N) (shapeTop s hs) = altWord i k (cox i k) :=
  (shapeTop_val_of_degree_two hs h2).trans (altWord_cox_of_pair
    ((nonempty_atomComp_iff hs h2 i).mp hi) ((nonempty_atomComp_iff hs h2 k).mp hk) hik).symm

end ChainCat
