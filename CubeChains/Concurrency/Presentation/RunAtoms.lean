import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Machinery.Braid.MatsumotoCat

/-!
# Concurrency/Presentation/RunAtoms — the runs over a shape, and the polygon of a degree-two one

The run-arrows into a shape of `Ch Zbp` are a lower set of the right weak order (`shapeLower`), an
ascent between two of them is an atom over the shape (`ascLeg`), and a refinement of shapes carries
the runs over its source to those over its target by left translation (`pushPerm`).

Over a degree-two shape the lower set is a polygon, climbed from the bottom alternately through its
two junctions (`riseClimb`): the alternating word, which is reduced up to the Coxeter exponent.
-/

open CategoryTheory Opposite BPSet CubeChains Equiv

namespace ChainCat

/-! ## The alternating word, climbed

`RankTwo` reads the alternating word as a reduced word up to the Coxeter exponent; climbed from the
identity each letter is an ascent, and its top is an involution the pair's order does not see. -/

section Alternating

variable {n : ℕ} {i k : Fin (n - 1)}

/-- **Each letter of the alternating word ascends**, up to the Coxeter exponent. -/
theorem ascent_altWord (hik : (i : ℕ) ≠ (k : ℕ)) {t : ℕ} (ht : t + 1 ≤ cox i k) :
    altWord i k t (adjLo (altIdx i k t)) < altWord i k t (adjHi (altIdx i k t)) :=
  ascent_of_permLen_mul_adjT (by
    rw [← altWord_succ, permLen_altWord_of_le hik ht,
      permLen_altWord_of_le hik (Nat.le_of_succ_le ht)])

theorem altIdx_eq_or (i k : Fin (n - 1)) (t : ℕ) : altIdx i k t = i ∨ altIdx i k t = k := by
  unfold altIdx; split <;> simp

/-- Two cuts of a pair, placed against the two walks' `t`-th letters. -/
theorem altIdx_cases (hik : (i : ℕ) ≠ (k : ℕ)) {a b : Fin (n - 1)} (ha : a = i ∨ a = k)
    (hb : b = i ∨ b = k) (hab : (a : ℕ) ≠ (b : ℕ)) (t : ℕ) :
    (a = altIdx i k t ∧ b = altIdx k i t) ∨ (a = altIdx k i t ∧ b = altIdx i k t) := by
  unfold altIdx
  split <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- **The top of the polygon does not see the order of the pair.** -/
theorem altWord_cox_of_pair (hik : (i : ℕ) ≠ (k : ℕ)) {a b : Fin (n - 1)} (ha : a = i ∨ a = k)
    (hb : b = i ∨ b = k) (hab : (a : ℕ) ≠ (b : ℕ)) :
    altWord a b (cox a b) = altWord i k (cox i k) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · rw [cox_comm, altWord_cox]
  · exact absurd rfl hab

/-- **…so it is its own inverse**: read from its far end it is the other walk's word. -/
theorem altWord_cox_inv (hik : (i : ℕ) ≠ (k : ℕ)) :
    (altWord i k (cox i k))⁻¹ = altWord i k (cox i k) := by
  have h := altWord_cox_of_pair hik (altIdx_eq_or k i (cox i k)).symm (altIdx_eq_or i k (cox i k))
    (altIdx_ne (Ne.symm hik) (cox i k))
  rw [cox_altIdx, cox_comm k i] at h
  exact (altWord_inv _ k i).trans h

/-- The foot ascends through the letter the walk undoes last. -/
theorem ascent_polyFoot_of_succ {u : Perm (Fin n)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) {c : ℕ}
    (hc : c + 1 = cox i k) :
    polyFoot u i k (adjLo (altIdx i k c)) < polyFoot u i k (adjHi (altIdx i k c)) := by
  have h1 := permLen_mul_altWord hi hk c
  have h2 := permLen_mul_altWord hi hk (c + 1)
  rw [permLen_altWord_of_le hik (by omega)] at h1
  rw [permLen_altWord_of_le hik hc.le] at h2
  have hfoot : polyFoot u i k * adjT (altIdx i k c) = u * altWord i k c := by
    rw [polyFoot, ← hc, altWord_succ, ← mul_assoc, mul_adjT_adjT]
  refine ascent_of_permLen_mul_adjT ?_
  rw [hfoot, polyFoot, ← hc]
  omega

/-- **The foot of a polygon ascends through both of its crossings** — each is the last letter one
of the two walks undoes. -/
theorem ascent_polyFoot {u : Perm (Fin n)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) {m : Fin (n - 1)}
    (hm : m = i ∨ m = k) : polyFoot u i k (adjLo m) < polyFoot u i k (adjHi m) := by
  obtain ⟨c, hc⟩ : ∃ c, c + 1 = cox i k :=
    ⟨cox i k - 1, Nat.sub_add_cancel (by have := two_le_cox hik; omega)⟩
  have h₁ := ascent_polyFoot_of_succ hik hi hk hc
  have h₂ := ascent_polyFoot_of_succ (Ne.symm hik) hk hi (hc.trans (cox_comm i k))
  rw [← polyFoot_comm hik u] at h₂
  unfold altIdx at h₁ h₂
  split_ifs at h₁ h₂ <;> rcases hm with rfl | rfl <;> assumption

end Alternating

/-! ## The runs over a shape

A run-arrow into a shape is pinned by its crossing permutation, so the runs index the permutations
they realise faithfully, and the arrow is recovered from the permutation. -/

/-- A crossing permutation some run-arrow into a shape realises. -/
def ShapePerm (N : ℕ) (s : Ch Zbp) : Type :=
  {σ : Perm (Fin N) // ∃ r : zObj (𝟙^N) ⟶ s, crossPerm (dimSum_replicate N) r = σ}

namespace ShapePerm

variable {N : ℕ} {s : Ch Zbp}

/-- The run-arrow a realised permutation names. -/
noncomputable def arr (σ : ShapePerm N s) : zObj (𝟙^N) ⟶ s := σ.2.choose

@[simp] theorem crossPerm_arr (σ : ShapePerm N s) :
    crossPerm (dimSum_replicate N) σ.arr = σ.1 := σ.2.choose_spec

/-- **A run-arrow is pinned by its crossing permutation.** -/
theorem eq_arr (σ : ShapePerm N s) {r : zObj (𝟙^N) ⟶ s}
    (hr : crossPerm (dimSum_replicate N) r = σ.1) : r = σ.arr :=
  hom_ext_of_crossPerm (hr.trans (σ.crossPerm_arr).symm)

theorem strands (σ : ShapePerm N s) : dimSum s.dims = N := dimSum_eq_of_onesHom σ.arr

end ShapePerm

/-- The run a map out of a run names. -/
def runOf {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) : ShapePerm N s :=
  ⟨crossPerm (dimSum_replicate N) r, ⟨r, rfl⟩⟩

@[simp] theorem runOf_val {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) :
    (runOf r).1 = crossPerm (dimSum_replicate N) r := rfl

@[simp] theorem arr_runOf {N : ℕ} {s : Ch Zbp} (r : zObj (𝟙^N) ⟶ s) :
    (runOf r).arr = r := ((runOf r).eq_arr rfl).symm

/-- **The runs over a shape are a lower set of the right weak order** — `exists_run_mul_adjT` is the
exchange, so every cover below a run is realised. -/
noncomputable def shapeLower (N : ℕ) (s : Ch Zbp) : WeakOrder.Lower N (ShapePerm N s) where
  perm := Subtype.val
  perm_inj := Subtype.val_injective
  isLowerSet := WeakOrder.isLowerSet_of_covBy (by
    rintro x _ hcov ⟨σ, rfl⟩
    obtain ⟨k, hd, hx⟩ := WeakOrder.covBy_iff.mp hcov
    simp only [WeakOrder.perm_of] at hd hx
    obtain ⟨r, hr⟩ := exists_run_mul_adjT σ.strands σ.arr (by simpa using hd)
    refine ⟨runOf r, congrArg WeakOrder.of ?_⟩
    rw [runOf_val, hr, σ.crossPerm_arr]
    exact hx.symm)

@[simp] theorem shapeLower_perm (N : ℕ) (s : Ch Zbp) (σ : ShapePerm N s) :
    (shapeLower N s).perm σ = σ.1 := rfl

/-- The run a shape is merged into from. -/
noncomputable def shapeBot {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    ShapePerm N s := runOf (runMerge s hs)

@[simp] theorem shapeBot_val {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    (shapeBot s hs).1 = 1 := crossPerm_eq_one_of_W _ (W_runMerge _ _)

theorem arr_shapeBot {N : ℕ} (s : Ch Zbp) (hs : dimSum s.dims = N) :
    (shapeBot s hs).arr = runMerge s hs := arr_runOf _

/-- **Every run is climbed to from the merge run.** -/
theorem shapeBot_le {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N)
    (σ : ShapePerm N s) : WeakOrder.of ((shapeLower N s).perm (shapeBot s hs))
      ≤ WeakOrder.of ((shapeLower N s).perm σ) := by
  rw [shapeLower_perm, shapeLower_perm, shapeBot_val]
  exact WeakOrder.le_of_mul_eq (one_mul σ.1) (by rw [permLen_one, Nat.add_zero])

theorem W_shapeBot_arr {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) :
    W Zbp ((shapeBot s hs).arr) := by
  rw [shapeBot, arr_runOf]
  exact W_runMerge _ _

/-! ## An ascent is an atom over the shape

At an ascent the run-arrow below factors through the `k`-th atom shape and the one above crosses it
(`exists_atom_step`), so the leg is a chain of atom shape over the shape. -/

section Asc

variable {N : ℕ} {s : Ch Zbp}

/-- The leg an ascent crosses: the atom shape at its index, over the shape. -/
noncomputable def ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    zObj (atomComp N e.idx) ⟶ s :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose

theorem mergeOnes_ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    mergeOnes N e.idx ≫ ascLeg e = a.arr :=
  (exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.1

theorem atomOnes_ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    atomOnes N e.idx ≫ ascLeg e = b.arr :=
  b.eq_arr (((exists_atom_step a.strands e.idx
    (nonempty_atomComp_of_descent b.strands b.arr (by simpa using e.descent))
    a.crossPerm_arr (by simpa using e.asc)).choose_spec.2).trans e.perm_eq.symm)

/-- **An ascent's leg crosses what the run below it does** — the atom's merge crosses nothing. -/
theorem crossPerm_ascLeg {a b : ShapePerm N s} (e : Ascent (shapeLower N s).perm a b) :
    crossPerm (dimSum_atomComp N e.idx) (ascLeg e) = a.1 := by
  have h := crossPerm_comp (dimSum_replicate N) (mergeOnes N e.idx) (ascLeg e)
  rw [mergeOnes_ascLeg e, a.crossPerm_arr, crossPerm_eq_one_of_W _ (W_mergeOnes N e.idx),
    mul_one] at h
  exact h.symm

end Asc

/-! ## A refinement of shapes carries the runs along

Crossings compose, so a run over the source read over the target is left translation by the
refinement's crossing, and the lengths add: covers go to covers, and an ascent's leg is its own,
composed with the refinement. -/

section Push

variable {N : ℕ} {s s' : Ch Zbp} (t : s ⟶ s')

/-- A run over a shape, read over a shape it refines. -/
noncomputable def pushPerm (σ : ShapePerm N s) : ShapePerm N s' := runOf (σ.arr ≫ t)

theorem arr_pushPerm (σ : ShapePerm N s) : (pushPerm t σ).arr = σ.arr ≫ t := arr_runOf _

theorem val_pushPerm (hs : dimSum s.dims = N) (σ : ShapePerm N s) :
    (pushPerm t σ).1 = crossPerm hs t * σ.1 :=
  (runOf_val (σ.arr ≫ t)).trans ((crossPerm_comp (dimSum_replicate N) σ.arr t).trans
    (congrArg (fun p => crossPerm hs t * p) σ.crossPerm_arr))

theorem permLen_pushPerm (hs : dimSum s.dims = N) (σ : ShapePerm N s) :
    permLen (pushPerm t σ).1 = permLen σ.1 + permLen (crossPerm hs t) :=
  ((congrArg permLen (runOf_val (σ.arr ≫ t))).trans
      (permLen_crossPerm_comp (dimSum_replicate N) σ.arr t)).trans
    (congrArg (fun n => n + permLen (crossPerm hs t)) (congrArg permLen σ.crossPerm_arr))

theorem pushPerm_comp {s'' : Ch Zbp} (t' : s' ⟶ s'') (σ : ShapePerm N s) :
    pushPerm t' (pushPerm t σ) = pushPerm (t ≫ t') σ :=
  congrArg runOf (by rw [pushPerm, arr_runOf, Category.assoc])

/-- **Pushing an ascent** — crossings add, so the length still goes up by one. -/
noncomputable def pushAscent (hs : dimSum s.dims = N) {a b : ShapePerm N s}
    (e : Ascent (shapeLower N s).perm a b) :
    Ascent (shapeLower N s').perm (pushPerm t a) (pushPerm t b) where
  idx := e.idx
  asc := by
    have hperm : (pushPerm t b).1 = (pushPerm t a).1 * adjT e.idx := by
      rw [val_pushPerm t hs b, val_pushPerm t hs a, mul_assoc]
      exact congrArg (fun p => crossPerm hs t * p) e.perm_eq
    refine ascent_of_permLen_mul_adjT ?_
    rw [shapeLower_perm, ← hperm, permLen_pushPerm t hs b, permLen_pushPerm t hs a]
    have := e.permLen_eq
    simp only [shapeLower_perm] at this
    omega
  perm_eq := by
    rw [shapeLower_perm, shapeLower_perm, val_pushPerm t hs b, val_pushPerm t hs a, mul_assoc]
    exact congrArg (fun p => crossPerm hs t * p) e.perm_eq

/-- …so a whole climb pushes, by `mapPath`. -/
noncomputable def pushPre (hs : dimSum s.dims = N) :
    Ascents (shapeLower N s).perm ⥤q Ascents (shapeLower N s').perm where
  obj := pushPerm t
  map e := pushAscent t hs e

/-- The leg of a pushed ascent is its own leg, composed with the refinement. -/
theorem ascLeg_pushAscent (hs : dimSum s.dims = N) {a b : ShapePerm N s}
    (e : Ascent (shapeLower N s).perm a b) : ascLeg (pushAscent t hs e) = ascLeg e ≫ t :=
  hom_ext_of_crossPerm (h := dimSum_atomComp N e.idx)
    (((crossPerm_ascLeg (pushAscent t hs e)).trans (val_pushPerm t hs a)).trans
      ((congrArg (fun p => crossPerm hs t * p) (crossPerm_ascLeg e).symm).trans
        (crossPerm_comp (dimSum_atomComp N e.idx) (ascLeg e) t).symm))

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

/-- **A pair is pinned by the cuts it contains.** -/
theorem eq_of_iff {p q : AtomPair N} (h : ∀ k, k = p.lo ∨ k = p.hi ↔ k = q.lo ∨ k = q.hi) :
    p = q := by
  have h1 := (h p.lo).mp (Or.inl rfl)
  have h2 := (h p.hi).mp (Or.inr rfl)
  have h3 := (h q.lo).mpr (Or.inl rfl)
  have h4 := (h q.hi).mpr (Or.inr rfl)
  simp only [Fin.ext_iff] at h1 h2 h3 h4
  have := p.lt
  have := q.lt
  exact ext' (Fin.ext (by omega)) (Fin.ext (by omega))

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
theorem exists_rise : ∀ t ≤ cox i k, ∃ σ : ShapePerm N s, σ.1 = altWord i k t
  | 0, _ => ⟨shapeBot s hs, (shapeBot_val s hs).trans (altWord_zero i k).symm⟩
  | t + 1, ht => by
      obtain ⟨σ, hσ⟩ := exists_rise t (Nat.le_of_succ_le ht)
      have hm : Nonempty (zObj (atomComp N (altIdx i k t)) ⟶ s) := by
        rcases altIdx_eq_or i k t with h | h <;> rw [h] <;> assumption
      obtain ⟨w, -, hw⟩ := exists_atom_step hs (altIdx i k t) hm σ.crossPerm_arr
        (hσ ▸ ascent_altWord hik ht)
      exact ⟨runOf (atomOnes N (altIdx i k t) ≫ w), by rw [runOf_val, hw, hσ, altWord_succ]⟩

/-- The `t`-th run the climb through `i, k` reaches. -/
noncomputable def riseElem : (t : ℕ) → t ≤ cox i k → ShapePerm N s
  | 0, _ => shapeBot s hs
  | t + 1, ht => (exists_rise hs hik hi hk (t + 1) ht).choose

theorem riseElem_val : ∀ (t : ℕ) (ht : t ≤ cox i k),
    (riseElem hs hik hi hk t ht).1 = altWord i k t
  | 0, _ => (shapeBot_val s hs).trans (altWord_zero i k).symm
  | t + 1, ht => (exists_rise hs hik hi hk (t + 1) ht).choose_spec

/-- The ascent between two consecutive runs of the climb: the `t`-th letter. -/
noncomputable def riseAsc (t : ℕ) (ht : t + 1 ≤ cox i k) :
    Ascent (shapeLower N s).perm (riseElem hs hik hi hk t (Nat.le_of_succ_le ht))
      (riseElem hs hik hi hk (t + 1) ht) where
  idx := altIdx i k t
  asc := by rw [shapeLower_perm, riseElem_val]; exact ascent_altWord hik ht
  perm_eq := by rw [shapeLower_perm, shapeLower_perm, riseElem_val, riseElem_val, altWord_succ]

/-- **The climb from the bottom alternately through `i` and `k`** — `i` first. -/
noncomputable def riseClimb : (t : ℕ) → (ht : t ≤ cox i k) →
    Climb (shapeLower N s).perm (shapeBot s hs) (riseElem hs hik hi hk t ht)
  | 0, _ => Quiver.Path.nil
  | t + 1, ht => (riseClimb t (Nat.le_of_succ_le ht)).cons (riseAsc hs hik hi hk t ht)

/-- **A nonempty climb ends in its last letter.** -/
theorem riseClimb_eq_cons (t : ℕ) (ht : t ≤ cox i k) (m : ℕ) (hm : m + 1 = t) :
    ∃ (x : ShapePerm N s) (R : Climb (shapeLower N s).perm (shapeBot s hs) x)
      (f : Ascent (shapeLower N s).perm x (riseElem hs hik hi hk t ht)),
      riseClimb hs hik hi hk t ht = R.cons f ∧ f.idx = altIdx i k m := by
  subst hm
  exact ⟨_, _, _, rfl, rfl⟩

end Rise

/-- **The two climbs through a pair meet at the top** — the alternating words of length `cox` agree
as permutations. -/
theorem riseElem_cox {N : ℕ} {s : Ch Zbp} (hs : dimSum s.dims = N) {i k : Fin (N - 1)}
    (hik : (i : ℕ) ≠ (k : ℕ)) (hi : Nonempty (zObj (atomComp N i) ⟶ s))
    (hk : Nonempty (zObj (atomComp N k) ⟶ s)) :
    riseElem hs hik hi hk (cox i k) le_rfl
      = riseElem hs (Ne.symm hik) hk hi (cox k i) le_rfl :=
  Subtype.ext (by rw [riseElem_val, riseElem_val, cox_comm k i, altWord_cox])

end ChainCat
