import CubeChains.Testing.FastExec
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Logic.Equiv.Basic

/-!
# Testing/Parabolic — the crossing permutations out of one execution

A refinement of an execution shuffles the directions inside each bead and nowhere else, so the
crossing permutations `fperm X Y` available out of `X` are exactly the parabolic subgroup
`S_{d₁} × ⋯ × S_{d_k}` of the bead dimensions.  Blocks of positions are named by `blockIdx`, and
`beadAt` reads off the bead a position belongs to.

Not built by `lake build CubeChains`.
-/

variable {α : Type*} {n : ℕ}

/-! ## Blocks of a composition -/

/-- Which block of the composition `ds` the position `p` falls in. -/
def blockIdx : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: ds, p => if p < d then 0 else blockIdx ds (p - d) + 1

@[simp] theorem blockIdx_nil (p : ℕ) : blockIdx [] p = 0 := rfl

theorem blockIdx_cons_of_lt {d p : ℕ} (ds : List ℕ) (h : p < d) : blockIdx (d :: ds) p = 0 :=
  if_pos h

theorem blockIdx_cons_of_le {d p : ℕ} (ds : List ℕ) (h : d ≤ p) :
    blockIdx (d :: ds) p = blockIdx ds (p - d) + 1 :=
  if_neg (Nat.not_lt.2 h)

theorem blockIdx_cons_add (d : ℕ) (ds : List ℕ) (p : ℕ) :
    blockIdx (d :: ds) (d + p) = blockIdx ds p + 1 := by
  rw [blockIdx_cons_of_le ds (Nat.le_add_right d p), Nat.add_sub_cancel_left]

/-- The parabolic subgroup of permutations preserving each consecutive block of sizes `ds`. -/
def parabolic (n : ℕ) (ds : List ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i : Fin n, blockIdx ds ((σ i : Fin n) : ℕ) = blockIdx ds (i : ℕ)}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb i := by rw [Equiv.Perm.mul_apply, ha (b i), hb i]
  inv_mem' {a} ha i := by
    have h := ha (a⁻¹ i)
    rw [show a (a⁻¹ i) = i by simp] at h
    exact h.symm

theorem mem_parabolic {ds : List ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ parabolic n ds ↔ ∀ i : Fin n, blockIdx ds ((σ i : Fin n) : ℕ) = blockIdx ds (i : ℕ) :=
  Iff.rfl

/-- A transposition lies in the parabolic exactly when it stays inside one block. -/
theorem mem_parabolic_swap {ds : List ℕ} {i j : Fin n} :
    Equiv.swap i j ∈ parabolic n ds ↔ blockIdx ds (i : ℕ) = blockIdx ds (j : ℕ) := by
  constructor
  · intro h
    have h' := h i
    rwa [Equiv.swap_apply_left, eq_comm] at h'
  · intro h k
    by_cases hki : k = i
    · subst hki; rw [Equiv.swap_apply_left]; exact h.symm
    · by_cases hkj : k = j
      · subst hkj; rw [Equiv.swap_apply_right]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-! ## The bead a position belongs to -/

/-- The bead of `A` containing the `i`-th letter of `A.flatten`, and `[]` past the end. -/
def beadAt (A : List (List α)) (i : ℕ) : List α := (A[blockIdx (A.map List.length) i]?).getD []

theorem beadAt_congr {A : List (List α)} {i j : ℕ}
    (h : blockIdx (A.map List.length) i = blockIdx (A.map List.length) j) :
    beadAt A i = beadAt A j := by rw [beadAt, beadAt, h]

@[simp] theorem beadAt_nil (i : ℕ) : beadAt ([] : List (List α)) i = [] := by simp [beadAt]

theorem beadAt_cons_of_lt {b : List α} {A : List (List α)} {i : ℕ} (h : i < b.length) :
    beadAt (b :: A) i = b := by
  rw [beadAt, List.map_cons, blockIdx_cons_of_lt _ h]; simp

theorem beadAt_cons_of_le {b : List α} {A : List (List α)} {i : ℕ} (h : b.length ≤ i) :
    beadAt (b :: A) i = beadAt A (i - b.length) := by
  simp only [beadAt, List.map_cons, blockIdx_cons_of_le _ h, List.getElem?_cons_succ]

theorem beadAt_subset (A : List (List α)) (i : ℕ) : beadAt A i ⊆ A.flatten := by
  intro x hx
  rw [beadAt] at hx
  rcases hk : A[blockIdx (A.map List.length) i]? with _ | b
  · rw [hk] at hx; simp at hx
  · rw [hk] at hx
    exact List.mem_flatten_of_mem (List.mem_of_getElem? hk) hx

/-- Distinct beads of a repetition-free run are disjoint, so a letter names its block. -/
theorem blockIdx_eq_of_mem_beadAt : ∀ {A : List (List α)}, A.flatten.Nodup → ∀ {x : α} {i j : ℕ},
    x ∈ beadAt A i → x ∈ beadAt A j →
      blockIdx (A.map List.length) i = blockIdx (A.map List.length) j := by
  intro A
  induction A with
  | nil => intro _ x i j hi _; simp at hi
  | cons b A ih =>
    intro hA x i j hi hj
    rw [List.flatten_cons, List.nodup_append] at hA
    by_cases hib : i < b.length <;> by_cases hjb : j < b.length
    · rw [List.map_cons, blockIdx_cons_of_lt _ hib, blockIdx_cons_of_lt _ hjb]
    · rw [beadAt_cons_of_lt hib] at hi
      rw [beadAt_cons_of_le (Nat.not_lt.1 hjb)] at hj
      exact (hA.2.2 x hi x (beadAt_subset A _ hj) rfl).elim
    · rw [beadAt_cons_of_lt hjb] at hj
      rw [beadAt_cons_of_le (Nat.not_lt.1 hib)] at hi
      exact (hA.2.2 x hj x (beadAt_subset A _ hi) rfl).elim
    · rw [beadAt_cons_of_le (Nat.not_lt.1 hib)] at hi
      rw [beadAt_cons_of_le (Nat.not_lt.1 hjb)] at hj
      rw [List.map_cons, blockIdx_cons_of_le _ (Nat.not_lt.1 hib),
        blockIdx_cons_of_le _ (Nat.not_lt.1 hjb)]
      exact congrArg (· + 1) (ih hA.2.1 hi hj)

/-! ## Refinement moves nothing between beads -/

/-- A refinement keeps every letter in the bead of the coarse run its position belongs to. -/
theorem RefinesRel.getElem_flatten_mem_beadAt {A B : List (List (Fin n))} (h : RefinesRel A B) :
    ∀ (i : ℕ) (hi : i < B.flatten.length), B.flatten[i] ∈ beadAt A i := by
  induction h with
  | nil => intro i hi; simp at hi
  | @cons b bs ps ys hsub hlen h ih =>
    rw [List.flatten_append]
    intro i hi
    have hi' : i < ps.flatten.length + ys.flatten.length := by simpa using hi
    by_cases hib : i < b.length
    · have hip : i < ps.flatten.length := by omega
      rw [beadAt_cons_of_lt hib, List.getElem_append_left hip]
      obtain ⟨p, hp, hxp⟩ := List.mem_flatten.1 (List.getElem_mem hip)
      exact (hsub p hp).subset hxp
    · replace hib : b.length ≤ i := Nat.not_lt.1 hib
      have hip : ps.flatten.length ≤ i := by omega
      have hiy : i - ps.flatten.length < ys.flatten.length := by omega
      rw [beadAt_cons_of_le hib, List.getElem_append_right hip, ← hlen]
      exact ih _ hiy

theorem flatten_map_singleton (l : List α) : (l.map fun a => [a]).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Cutting a run into singletons refines `A` as soon as every letter sits in its own bead. -/
theorem refinesRel_map_singleton : ∀ {A : List (List (Fin n))} {w : List (Fin n)},
    w.length = A.flatten.length → (∀ (i : ℕ) (hi : i < w.length), w[i] ∈ beadAt A i) →
      RefinesRel A (w.map fun a => [a]) := by
  intro A
  induction A with
  | nil =>
    intro w hw _
    obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    exact .nil
  | cons b A ih =>
    intro w hw hmem
    have hbw : b.length ≤ w.length := by simp [hw]
    obtain ⟨w₁, w₂, rfl, hw₁⟩ : ∃ w₁ w₂, w = w₁ ++ w₂ ∧ w₁.length = b.length :=
      ⟨w.take b.length, w.drop b.length, (List.take_append_drop _ _).symm, by simp [hbw]⟩
    have hlen₂ : w₂.length = A.flatten.length := by
      simp only [List.length_append, List.flatten_cons] at hw
      omega
    rw [List.map_append]
    refine RefinesRel.cons (ps := w₁.map fun a => [a]) ?_ ?_ (ih hlen₂ ?_)
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      refine List.singleton_sublist.2 ?_
      have hb := hmem i (by simp only [List.length_append]; omega)
      rwa [List.getElem_append_left hi, beadAt_cons_of_lt (by omega)] at hb
    · rw [flatten_map_singleton, hw₁]
    · intro i hi
      have hb := hmem (i + w₁.length) (by simp only [List.length_append]; omega)
      rwa [← List.getElem_append_right' w₁ hi, hw₁, beadAt_cons_of_le (Nat.le_add_left _ _),
        Nat.add_sub_cancel] at hb

/-! ## The label set of an execution -/

namespace FExec

/-- The bead dimensions of the run. -/
def dims (X : FExec n) : List ℕ := X.1.map List.length

theorem dims_sum (X : FExec n) : X.dims.sum = n := by
  rw [dims, ← List.length_flatten]; exact X.word_length

theorem dims_pos (X : FExec n) : ∀ d ∈ X.dims, 0 < d := by
  intro d hd
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hd
  cases b with
  | nil => exact absurd rfl (X.beads_ne_nil _ hb)
  | cons _ _ => simp

@[simp] theorem dims_length (X : FExec n) : X.dims.length = X.1.length := List.length_map _

theorem flatten_length (X : FExec n) : X.1.flatten.length = n := X.word_length

theorem letter_mem_beadAt (X : FExec n) (i : Fin n) : X.letter i ∈ beadAt X.1 (i : ℕ) := by
  have hb : (i : ℕ) < X.1.flatten.length := by
    have h1 := X.flatten_length; have h2 := i.isLt; omega
  exact (RefinesRel.refl X.1).getElem_flatten_mem_beadAt (i : ℕ) hb

/-- Refining shuffles inside beads only. -/
theorem fperm_mem_parabolic {X Y : FExec n} (h : X.Refines Y) :
    fperm X Y ∈ parabolic n X.dims := by
  intro i
  have hb : ((fperm X Y i : Fin n) : ℕ) < Y.1.flatten.length := by
    have h1 := Y.flatten_length; have h2 := (fperm X Y i).isLt; omega
  have hmem := h.getElem_flatten_mem_beadAt _ hb
  have hY : Y.1.flatten[((fperm X Y i : Fin n) : ℕ)]'hb = X.letter i :=
    Y.perm.apply_symm_apply (X.letter i)
  rw [hY] at hmem
  exact blockIdx_eq_of_mem_beadAt X.word_nodup hmem (X.letter_mem_beadAt i)

/-- The all-singleton refinement performing the directions in the order `σ` prescribes. -/
def shuffled (X : FExec n) (σ : Equiv.Perm (Fin n)) : FExec n :=
  ⟨(List.ofFn fun i => X.letter (σ⁻¹ i)).map fun a => [a], by
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
      simp
    · rw [flatten_map_singleton]
      exact List.nodup_ofFn.2 fun i j hij => (σ⁻¹).injective (X.perm.injective hij)
    · rw [flatten_map_singleton, List.length_ofFn]⟩

@[simp] theorem shuffled_word (X : FExec n) (σ : Equiv.Perm (Fin n)) :
    (X.shuffled σ).word = List.ofFn fun i => X.letter (σ⁻¹ i) :=
  flatten_map_singleton _

@[simp] theorem shuffled_letter (X : FExec n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (X.shuffled σ).letter i = X.letter (σ⁻¹ i) := by
  simp [letter, shuffled_word]

theorem shuffled_perm (X : FExec n) (σ : Equiv.Perm (Fin n)) :
    (X.shuffled σ).perm = X.perm * σ⁻¹ := by
  ext i; simp [Equiv.Perm.mul_apply]

@[simp] theorem fperm_shuffled (X : FExec n) (σ : Equiv.Perm (Fin n)) :
    fperm X (X.shuffled σ) = σ := by
  rw [fperm, shuffled_perm, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

theorem refines_shuffled (X : FExec n) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ parabolic n X.dims) :
    X.Refines (X.shuffled σ) := by
  refine refinesRel_map_singleton (by rw [List.length_ofFn]; exact X.flatten_length.symm) ?_
  intro i hi
  have hi' : i < n := by rw [List.length_ofFn] at hi; exact hi
  have hget : (List.ofFn fun j => X.letter (σ⁻¹ j))[i]'hi = X.letter (σ⁻¹ ⟨i, hi'⟩) := by simp
  rw [hget]
  have hmem := X.letter_mem_beadAt (σ⁻¹ ⟨i, hi'⟩)
  rwa [beadAt_congr (A := X.1) (mem_parabolic.1 ((parabolic n X.dims).inv_mem hσ) ⟨i, hi'⟩)] at hmem

/-- **The crossing permutations out of `X` are the parabolic of its bead dimensions.** -/
theorem outLabels_eq_parabolic (X : FExec n) :
    {σ | ∃ Y, X.Refines Y ∧ fperm X Y = σ} = (parabolic n X.dims : Set (Equiv.Perm (Fin n))) := by
  ext σ
  constructor
  · rintro ⟨Y, h, rfl⟩
    exact fperm_mem_parabolic h
  · intro hσ
    exact ⟨X.shuffled σ, X.refines_shuffled hσ, X.fperm_shuffled σ⟩

/-! ## The parabolic determines the composition -/

/-- A composition of `m` into positive parts is determined by the partition of `[0, m)` it cuts. -/
theorem eq_of_blockIdx_iff : ∀ {ds es : List ℕ} {m : ℕ}, (∀ d ∈ ds, 0 < d) → (∀ e ∈ es, 0 < e) →
    ds.sum = m → es.sum = m →
    (∀ i j, i < m → j < m → (blockIdx ds i = blockIdx ds j ↔ blockIdx es i = blockIdx es j)) →
      ds = es := by
  intro ds
  induction ds with
  | nil =>
    intro es m _ hes hd hesum _
    simp only [List.sum_nil] at hd
    subst hd
    cases es with
    | nil => rfl
    | cons e u =>
      rw [List.sum_cons] at hesum
      have := hes e (by simp)
      omega
  | cons d t ih =>
    intro es m hd hes hdsum hesum hrel
    have hd0 : 0 < d := hd d (by simp)
    have hm : 0 < m := by rw [← hdsum, List.sum_cons]; omega
    cases es with
    | nil => rw [List.sum_nil] at hesum; omega
    | cons e u =>
      have he0 : 0 < e := hes e (by simp)
      have hde : d = e := by
        by_contra hne
        rcases Nat.lt_or_ge d e with hlt | hge
        · have hdm : d < m := by rw [← hesum, List.sum_cons]; omega
          have hb := (hrel 0 d hm hdm).2 (by
            rw [blockIdx_cons_of_lt _ he0, blockIdx_cons_of_lt _ hlt])
          rw [blockIdx_cons_of_lt _ hd0, blockIdx_cons_of_le _ (Nat.le_refl d)] at hb
          omega
        · have hlt : e < d := by omega
          have hem : e < m := by rw [← hdsum, List.sum_cons]; omega
          have hb := (hrel 0 e hm hem).1 (by
            rw [blockIdx_cons_of_lt _ hd0, blockIdx_cons_of_lt _ hlt])
          rw [blockIdx_cons_of_lt _ he0, blockIdx_cons_of_le _ (Nat.le_refl e)] at hb
          omega
      subst hde
      rw [List.sum_cons] at hdsum hesum
      refine congrArg (d :: ·) (ih (fun x hx => hd x (by simp [hx]))
        (fun x hx => hes x (by simp [hx])) rfl (by omega) ?_)
      intro i j hi hj
      have hb := hrel (d + i) (d + j) (by omega) (by omega)
      rw [blockIdx_cons_add, blockIdx_cons_add, blockIdx_cons_add, blockIdx_cons_add] at hb
      omega

/-- Executions with the same crossing permutations have the same beads. -/
theorem dims_eq_of_outLabels_eq {X Y : FExec n}
    (h : {σ | ∃ Z, X.Refines Z ∧ fperm X Z = σ} = {σ | ∃ Z, Y.Refines Z ∧ fperm Y Z = σ}) :
    X.dims = Y.dims := by
  rw [outLabels_eq_parabolic X, outLabels_eq_parabolic Y] at h
  refine eq_of_blockIdx_iff X.dims_pos Y.dims_pos X.dims_sum Y.dims_sum ?_
  intro i j hi hj
  have hs := Set.ext_iff.1 h (Equiv.swap (⟨i, hi⟩ : Fin n) ⟨j, hj⟩)
  simpa only [SetLike.mem_coe, mem_parabolic_swap] using hs

/-- The full symmetric group is available exactly out of the one-bead run. -/
theorem outLabels_eq_top_iff (X : FExec n) (hn : 0 < n) :
    (∀ σ : Equiv.Perm (Fin n), ∃ Y, X.Refines Y ∧ fperm X Y = σ) ↔ X.1.length = 1 := by
  have hsum := X.dims_sum
  constructor
  · intro h
    have hall : ∀ i j : ℕ, i < n → j < n → blockIdx X.dims i = blockIdx X.dims j := by
      intro i j hi hj
      obtain ⟨Y, hY, hf⟩ := h (Equiv.swap (⟨i, hi⟩ : Fin n) ⟨j, hj⟩)
      exact mem_parabolic_swap.1 (hf ▸ fperm_mem_parabolic hY)
    obtain ⟨d, t, hds⟩ : ∃ d t, X.dims = d :: t := by
      cases hd : X.dims with
      | nil => rw [hd] at hsum; simp at hsum; omega
      | cons d t => exact ⟨d, t, rfl⟩
    rw [← X.dims_length, hds]
    cases t with
    | nil => rfl
    | cons e u =>
      exfalso
      have hd0 : 0 < d := X.dims_pos d (by rw [hds]; simp)
      have he0 : 0 < e := X.dims_pos e (by rw [hds]; simp)
      have hdn : d < n := by rw [hds, List.sum_cons, List.sum_cons] at hsum; omega
      have hb := hall 0 d hn hdn
      rw [hds, blockIdx_cons_of_lt _ hd0, blockIdx_cons_of_le _ (Nat.le_refl d)] at hb
      omega
  · intro h σ
    obtain ⟨d, hd⟩ : ∃ d, X.dims = [d] := by
      have hlen : X.dims.length = 1 := by rw [X.dims_length, h]
      cases hds : X.dims with
      | nil => rw [hds] at hlen; simp at hlen
      | cons d t =>
        cases t with
        | nil => exact ⟨d, rfl⟩
        | cons e u => rw [hds] at hlen; simp at hlen
    have hdn : d = n := by rw [hd] at hsum; simpa using hsum
    refine ⟨X.shuffled σ, X.refines_shuffled (mem_parabolic.2 fun i => ?_), X.fperm_shuffled σ⟩
    have h1 : ((σ i : Fin n) : ℕ) < d := by have := (σ i).isLt; omega
    have h2 : (i : ℕ) < d := by have := i.isLt; omega
    rw [hd, blockIdx_cons_of_lt _ h1, blockIdx_cons_of_lt _ h2]

end FExec
