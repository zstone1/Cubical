import CubeChains.Testing.Enumerate.FastExec
import CubeChains.Machinery.Composition

/-!
# Testing/Pi1/Parabolic — the crossing permutations out of one execution

A refinement of an execution shuffles the directions inside each bead and nowhere else, so the
crossing permutations `fperm X Y` available out of `X` are exactly the Young subgroup
`S_{d₁} × ⋯ × S_{d_k}` of the bead dimensions (`Composition.parabolic`).  `beadAt` reads off the
bead a position belongs to, and `beadAt_eq_getElem` says that bead is `Composition.index`'s.

Not built by `lake build CubeChains`.
-/

variable {α : Type*} {n : ℕ}

/-! ## The bead a position belongs to -/

/-- The bead of `A` containing the `i`-th letter of `A.flatten`, and `[]` past the end. -/
def beadAt : List (List α) → ℕ → List α
  | [], _ => []
  | b :: A, i => if i < b.length then b else beadAt A (i - b.length)

@[simp] theorem beadAt_nil (i : ℕ) : beadAt ([] : List (List α)) i = [] := rfl

theorem beadAt_cons_of_lt {b : List α} {A : List (List α)} {i : ℕ} (h : i < b.length) :
    beadAt (b :: A) i = b := if_pos h

theorem beadAt_cons_of_le {b : List α} {A : List (List α)} {i : ℕ} (h : b.length ≤ i) :
    beadAt (b :: A) i = beadAt A (i - b.length) := if_neg (Nat.not_lt.2 h)

theorem beadAt_subset : ∀ (A : List (List α)) (i : ℕ), beadAt A i ⊆ A.flatten
  | [], _ => by simp
  | b :: A, i => by
      rw [List.flatten_cons]
      by_cases h : i < b.length
      · rw [beadAt_cons_of_lt h]; exact fun x hx => List.mem_append_left _ hx
      · rw [beadAt_cons_of_le (Nat.not_lt.1 h)]
        exact fun x hx => List.mem_append_right _ (beadAt_subset A _ hx)

/-- **`beadAt` reads the block the position falls in** — the bracket by prefix sums. -/
theorem beadAt_eq_getElem : ∀ (A : List (List α)) {i j : ℕ} (hj : j < A.length),
    ((A.map List.length).take j).sum ≤ i → i < ((A.map List.length).take (j + 1)).sum →
      beadAt A i = A[j]
  | [], _, _, hj, _, _ => absurd hj (by simp)
  | b :: A, i, 0, _, _, h2 => by
      simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.sum_cons,
        List.sum_nil, Nat.add_zero] at h2
      rw [beadAt_cons_of_lt h2]
      simp
  | b :: A, i, j + 1, hj, h1, h2 => by
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons] at h1 h2
      rw [beadAt_cons_of_le (by omega),
        beadAt_eq_getElem A (by simpa using hj) (by omega) (by omega)]
      simp

/-- Distinct beads of a repetition-free run are disjoint, so a letter names its bead. -/
theorem beadAt_eq_of_mem : ∀ {A : List (List α)}, A.flatten.Nodup → ∀ {x : α} {i j : ℕ},
    x ∈ beadAt A i → x ∈ beadAt A j → beadAt A i = beadAt A j := by
  intro A
  induction A with
  | nil => intro _ x i j hi _; simp at hi
  | cons b A ih =>
    intro hA x i j hi hj
    rw [List.flatten_cons, List.nodup_append] at hA
    by_cases hib : i < b.length <;> by_cases hjb : j < b.length
    · rw [beadAt_cons_of_lt hib, beadAt_cons_of_lt hjb]
    · rw [beadAt_cons_of_lt hib] at hi ⊢
      rw [beadAt_cons_of_le (Nat.not_lt.1 hjb)] at hj ⊢
      exact (hA.2.2 x hi x (beadAt_subset A _ hj) rfl).elim
    · rw [beadAt_cons_of_lt hjb] at hj ⊢
      rw [beadAt_cons_of_le (Nat.not_lt.1 hib)] at hi ⊢
      exact (hA.2.2 x hj x (beadAt_subset A _ hi) rfl).elim
    · rw [beadAt_cons_of_le (Nat.not_lt.1 hib)] at hi ⊢
      rw [beadAt_cons_of_le (Nat.not_lt.1 hjb)] at hj ⊢
      exact ih hA.2.1 hi hj

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

/-- The bead dimensions of the run, as a composition of `n`. -/
def comp (X : FExec n) : Composition n where
  blocks := X.dims
  blocks_pos {i} hi := X.dims_pos i hi
  blocks_sum := X.dims_sum

@[simp] theorem comp_blocks (X : FExec n) : X.comp.blocks = X.dims := rfl

@[simp] theorem comp_length (X : FExec n) : X.comp.length = X.1.length := X.dims_length

theorem comp_sizeUpTo (X : FExec n) (j : ℕ) :
    X.comp.sizeUpTo j = ((X.1.map List.length).take j).sum := rfl

/-- **A position's bead is its block** — the bracket `sizeUpTo (index i) ≤ i < sizeUpTo (index i+1)`
read through `beadAt_eq_getElem`. -/
theorem beadAt_eq_bead (X : FExec n) (i : Fin n) :
    beadAt X.1 (i : ℕ) = X.1[(X.comp.index i : ℕ)]'(by
      rw [← X.comp_length]; exact (X.comp.index i).isLt) := by
  refine beadAt_eq_getElem X.1 (by rw [← X.comp_length]; exact (X.comp.index i).isLt) ?_ ?_
  · rw [← comp_sizeUpTo]; exact X.comp.sizeUpTo_index_le i
  · rw [← comp_sizeUpTo]; exact X.comp.lt_sizeUpTo_index_succ i

/-- Distinct beads are disjoint, so a bead names its own index. -/
theorem index_eq_of_beadAt_eq (X : FExec n) {i j : Fin n}
    (h : beadAt X.1 (i : ℕ) = beadAt X.1 (j : ℕ)) : X.comp.index i = X.comp.index j := by
  set a := (X.comp.index i : ℕ) with ha
  set b := (X.comp.index j : ℕ) with hb
  have hal : a < X.1.length := by rw [ha, ← X.comp_length]; exact (X.comp.index i).isLt
  have hbl : b < X.1.length := by rw [hb, ← X.comp_length]; exact (X.comp.index j).isLt
  rw [X.beadAt_eq_bead i, X.beadAt_eq_bead j] at h
  refine Fin.ext ?_
  have key : ∀ u v : ℕ, ∀ (hu : u < X.1.length) (hv : v < X.1.length), u < v →
      X.1[u] ≠ X.1[v] := by
    intro u v hu hv huv heq
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.1[u] :=
      List.exists_mem_of_ne_nil _ (X.beads_ne_nil _ (List.getElem_mem hu))
    exact (List.pairwise_iff_getElem.mp ((List.nodup_flatten.mp X.word_nodup).2)) u v hu hv huv
      hx (heq ▸ hx)
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (key a b hal hbl hlt)
  · exact heq
  · exact absurd h.symm (key b a hbl hal hgt)

/-- Refining shuffles inside beads only. -/
theorem fperm_mem_parabolic {X Y : FExec n} (h : X.Refines Y) :
    fperm X Y ∈ X.comp.parabolic := by
  intro i
  have hb : ((fperm X Y i : Fin n) : ℕ) < Y.1.flatten.length := by
    have h1 := Y.flatten_length; have h2 := (fperm X Y i).isLt; omega
  have hmem := h.getElem_flatten_mem_beadAt _ hb
  have hY : Y.1.flatten[((fperm X Y i : Fin n) : ℕ)]'hb = X.letter i :=
    Y.perm.apply_symm_apply (X.letter i)
  rw [hY] at hmem
  exact X.index_eq_of_beadAt_eq (beadAt_eq_of_mem X.word_nodup hmem (X.letter_mem_beadAt i))

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

theorem refines_shuffled (X : FExec n) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ X.comp.parabolic) :
    X.Refines (X.shuffled σ) := by
  refine refinesRel_map_singleton (by rw [List.length_ofFn]; exact X.flatten_length.symm) ?_
  intro i hi
  have hi' : i < n := by rw [List.length_ofFn] at hi; exact hi
  have hget : (List.ofFn fun j => X.letter (σ⁻¹ j))[i]'hi = X.letter (σ⁻¹ ⟨i, hi'⟩) := by simp
  rw [hget]
  have hmem := X.letter_mem_beadAt (σ⁻¹ ⟨i, hi'⟩)
  have hidx := (Composition.mem_parabolic X.comp).mp (X.comp.parabolic.inv_mem hσ) ⟨i, hi'⟩
  rwa [X.beadAt_eq_bead (σ⁻¹ ⟨i, hi'⟩), hidx, ← X.beadAt_eq_bead ⟨i, hi'⟩] at hmem

/-- **The crossing permutations out of `X` are the Young subgroup of its bead dimensions.** -/
theorem outLabels_eq_parabolic (X : FExec n) :
    {σ | ∃ Y, X.Refines Y ∧ fperm X Y = σ} = (X.comp.parabolic : Set (Equiv.Perm (Fin n))) := by
  ext σ
  constructor
  · rintro ⟨Y, h, rfl⟩
    exact fperm_mem_parabolic h
  · intro hσ
    exact ⟨X.shuffled σ, X.refines_shuffled hσ, X.fperm_shuffled σ⟩

/-! ## The parabolic determines the composition -/

/-- Executions with the same crossing permutations have the same beads — a composition is
determined by the partition it cuts (`Composition.eq_of_index_iff`). -/
theorem dims_eq_of_outLabels_eq {X Y : FExec n}
    (h : {σ | ∃ Z, X.Refines Z ∧ fperm X Z = σ} = {σ | ∃ Z, Y.Refines Z ∧ fperm Y Z = σ}) :
    X.dims = Y.dims := by
  rw [outLabels_eq_parabolic X, outLabels_eq_parabolic Y] at h
  have hcomp : X.comp = Y.comp := Composition.eq_of_index_iff fun i j => by
    have hs := Set.ext_iff.1 h (Equiv.swap i j)
    simpa only [SetLike.mem_coe, Composition.mem_parabolic_swap] using hs
  exact congrArg Composition.blocks hcomp

/-- The full symmetric group is available exactly out of the one-bead run. -/
theorem outLabels_eq_top_iff (X : FExec n) (hn : 0 < n) :
    (∀ σ : Equiv.Perm (Fin n), ∃ Y, X.Refines Y ∧ fperm X Y = σ) ↔ X.1.length = 1 := by
  constructor
  · intro h
    have hall : ∀ i j : Fin n, X.comp.index i = X.comp.index j := fun i j => by
      obtain ⟨Y, hY, hf⟩ := h (Equiv.swap i j)
      exact (Composition.mem_parabolic_swap X.comp).1 (hf ▸ fperm_mem_parabolic hY)
    obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) + 1 = n := ⟨⟨n - 1, by omega⟩, by simp; omega⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin n, (z : ℕ) = 0 := ⟨⟨0, hn⟩, rfl⟩
    rw [← X.comp_length, X.comp.length_eq_index_succ p hp, congrArg Fin.val (hall p z),
      X.comp.index_zero hz]
  · intro h σ
    refine ⟨X.shuffled σ, X.refines_shuffled ((Composition.mem_parabolic X.comp).2 fun i => ?_),
      X.fperm_shuffled σ⟩
    have hlen : X.comp.length = 1 := by rw [X.comp_length, h]
    have h1 : ((X.comp.index (σ i) : ℕ)) < X.comp.length := (X.comp.index (σ i)).isLt
    have h2 : ((X.comp.index i : ℕ)) < X.comp.length := (X.comp.index i).isLt
    exact Fin.ext (by omega)

end FExec
