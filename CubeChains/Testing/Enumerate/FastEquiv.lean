import CubeChains.Concurrency.Executions.ExecData
import CubeChains.Testing.Enumerate.FastExec

/-!
# Testing/Enumerate/FastEquiv — the fast model enumerates exactly the executions of `□n`

`FExec n` (`Testing/Enumerate/FastExec`) is a word plus a grouping into consecutive nonempty
blocks; the chain side (`Concurrency/Executions/ExecData`) presents an execution as `ExecData n`, a
chain plus a run word. `fexecChStarEquiv : FExec n ≃ Ch⋆ (□n)` bridges them: tagging each letter of
the word with its block index gives a weakly monotone label list, and monotonicity is exactly
`WordCompat`.

Not built by `lake build CubeChains`.
-/

section FastBridge

open CategoryTheory Opposite CubeChain CubeChains CubeChains.ChStar

variable {n : ℕ}

/-- Label each letter of `bs.flatten` by its block, numbering blocks from `k`. -/
def tagFrom {α : Type*} : ℕ → List (List α) → List ℕ
  | _, [] => []
  | k, b :: bs => List.replicate b.length k ++ tagFrom (k + 1) bs

theorem length_tagFrom {α : Type*} :
    ∀ (k : ℕ) (bs : List (List α)), (tagFrom k bs).length = bs.flatten.length
  | _, [] => rfl
  | k, b :: bs => by
      simp only [tagFrom, List.length_append, List.length_replicate, List.flatten_cons,
        length_tagFrom (k + 1) bs]

theorem tagFrom_bounds {α : Type*} : ∀ (k : ℕ) (bs : List (List α)) (x : ℕ),
    x ∈ tagFrom k bs → k ≤ x ∧ x < k + bs.length
  | _, [], _, hx => absurd hx (by simp [tagFrom])
  | k, b :: bs, x, hx => by
      rw [tagFrom, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain rfl := List.eq_of_mem_replicate hx
        simp
      · have := tagFrom_bounds (k + 1) bs x hx
        simp only [List.length_cons]
        omega

/-- **The label list is weakly monotone** — the blocks are consecutive segments of the word. -/
theorem pairwise_tagFrom {α : Type*} :
    ∀ (k : ℕ) (bs : List (List α)), List.Pairwise (· ≤ ·) (tagFrom k bs)
  | _, [] => List.Pairwise.nil
  | k, b :: bs => by
      rw [tagFrom, List.pairwise_append]
      refine ⟨List.pairwise_iff_getElem.mpr fun i j hi hj _ => ?_,
        pairwise_tagFrom (k + 1) bs, fun a ha c hc => ?_⟩
      · rw [List.getElem_replicate, List.getElem_replicate]
      · have hak : a = k := List.eq_of_mem_replicate ha
        have := (tagFrom_bounds (k + 1) bs c hc).1
        omega

/-- Every block index is used — blocks are nonempty. -/
theorem mem_tagFrom {α : Type*} : ∀ (k : ℕ) (bs : List (List α)), (∀ b ∈ bs, b ≠ []) →
    ∀ j, k ≤ j → j < k + bs.length → j ∈ tagFrom k bs
  | k, [], _, j, hk, hj => by simp only [List.length_nil, Nat.add_zero] at hj; omega
  | k, b :: bs, hne, j, hk, hj => by
      rw [tagFrom, List.mem_append]
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact Or.inl (List.mem_replicate.mpr
          ⟨fun h0 => hne b (by simp) (List.length_eq_zero_iff.mp h0), rfl⟩)
      · refine Or.inr (mem_tagFrom (k + 1) bs (fun c hc => hne c (List.mem_cons_of_mem _ hc)) j
          hlt ?_)
        simp only [List.length_cons] at hj
        omega

namespace FExec

/-- The block index of each step of the word. -/
def tag (X : FExec n) : List ℕ := tagFrom 0 X.1

theorem length_tag (X : FExec n) : X.tag.length = n :=
  (length_tagFrom 0 X.1).trans X.word_length

/-- **The bead a direction is performed in.** -/
def blockOf (X : FExec n) (i : Fin n) : Fin X.1.length :=
  ⟨X.tag[(X.pos i : ℕ)]'(by rw [X.length_tag]; exact (X.pos i).isLt), by
    have hmem : X.tag[(X.pos i : ℕ)]'(by rw [X.length_tag]; exact (X.pos i).isLt) ∈ X.tag :=
      List.getElem_mem _
    have := (tagFrom_bounds 0 X.1 _ hmem).2
    omega⟩

theorem blockOf_le_of_pos_lt (X : FExec n) {i j : Fin n} (h : (X.pos i : ℕ) < (X.pos j : ℕ)) :
    (X.blockOf i : ℕ) ≤ (X.blockOf j : ℕ) :=
  List.pairwise_iff_getElem.mp (pairwise_tagFrom 0 X.1) _ _ _ _ h

theorem pos_injective (X : FExec n) : Function.Injective X.pos :=
  X.perm.symm.injective

/-- **The word's block labels are compatible with its order** — the `WordCompat` the chain side
asks for. -/
theorem wordCompat_blockOf (X : FExec n) : WordCompat X.perm X.blockOf := by
  intro i j hne
  have hnev : (X.blockOf i : ℕ) ≠ (X.blockOf j : ℕ) := fun h => hne (Fin.ext h)
  constructor
  · intro hb
    rcases lt_trichotomy (X.pos i : ℕ) (X.pos j : ℕ) with h | h | h
    · exact h
    · exact absurd (congrArg (fun q => (X.blockOf q : ℕ)) (X.pos_injective (Fin.ext h))) hnev
    · have := X.blockOf_le_of_pos_lt h
      exact absurd hb (by simp only [Fin.lt_def]; omega)
  · intro hp
    have := X.blockOf_le_of_pos_lt hp
    simp only [Fin.lt_def]
    omega

theorem blockOf_surjective (X : FExec n) : Function.Surjective X.blockOf := by
  intro k
  obtain ⟨s, hs, hval⟩ := List.getElem_of_mem
    (mem_tagFrom 0 X.1 X.beads_ne_nil (k : ℕ) (Nat.zero_le _) (by simp))
  have hs' : s < X.tag.length := hs
  have hsn : s < n := by rwa [X.length_tag] at hs'
  refine ⟨X.letter ⟨s, hsn⟩, Fin.ext ?_⟩
  have hpos : X.pos (X.letter ⟨s, hsn⟩) = ⟨s, hsn⟩ := X.perm.symm_apply_apply _
  change X.tag[(X.pos (X.letter ⟨s, hsn⟩) : ℕ)]'_ = (k : ℕ)
  simp only [hpos]
  exact hval

end FExec

/-- **The execution of `□n` a fast execution names.** -/
def fexecChStar (X : FExec n) : Ch⋆ (□n) :=
  ofWord X.perm X.blockOf X.blockOf_surjective X.wordCompat_blockOf

@[simp] theorem chain_fexecChStar (X : FExec n) :
    (fexecChStar X).chain = blockChain X.blockOf X.blockOf_surjective := rfl

/-- **The run word of the chain-side execution is the fast model's own word.** -/
@[simp] theorem runWord_fexecChStar (X : FExec n) : runWord (fexecChStar X) = X.perm :=
  runWord_ofWord _ _ _ _

/-- **The fast model's label is `ConcPos`'s crossing permutation.** -/
theorem fperm_eq_stepPerm {X Y : FExec n} (f : fexecChStar X ⟶ fexecChStar Y) :
    stepPerm f = FExec.fperm X Y := by
  rw [stepPerm_eq, runWord_fexecChStar, runWord_fexecChStar]
  rfl

/-- The same, at the strand count `permOf` is evaluated at. -/
theorem permOf_eq_fperm {X Y : FExec n} (f : fexecChStar X ⟶ fexecChStar Y) :
    RunWedge.permOf ((proj (□n)).map f)
      = RunWedge.permCast
          (dimSum_runWedge (fexecChStar X)).symm
          (FExec.fperm X Y) := by
  rw [permOf_eq_runWord]
  exact congrArg _ ((stepPerm_eq f).symm.trans (fperm_eq_stepPerm f))

/-- **`Y`'s beads refine `X`'s** — `beadOf_le` at the face order of the arrow's base. -/
theorem blockOf_le_of_arrow {X Y : FExec n} (f : fexecChStar X ⟶ fexecChStar Y) {q q' : Fin n}
    (h : (Y.blockOf q : ℕ) ≤ (Y.blockOf q' : ℕ)) : (X.blockOf q : ℕ) ≤ (X.blockOf q' : ℕ) := by
  have hb : ∀ (Z : FExec n) (r : Fin n),
      (beadOf (fexecChStar Z).chain r : ℕ) = (Z.blockOf r : ℕ) := fun Z r =>
    beadOf_blockChain _ _ r
  rw [← hb, ← hb]
  exact beadOf_le (chFace_faceLE f.1.unop) (by rw [hb, hb]; exact h)

/-! ## Regrouping a labelled list

A list whose labelling never decreases along it is the concatenation, in label order, of its label
fibres.  Both round trips of `fexecEquiv` are this fact: forwards it recovers the beads of `X` from
its word, backwards it says the fibres of `beadOf C` reassemble the word `w`. -/

section Regroup

variable {α : Type*}

/-- A list on which no `¬p` entry precedes a `p` entry splits into its `p`-part then its rest. -/
theorem filter_append_filter_not {p : α → Bool} : ∀ (l : List α),
    List.Pairwise (fun a b => p a ∨ ¬ p b) l →
      l.filter p ++ l.filter (fun a => !p a) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, Bool.not_true, Bool.false_eq_true, if_false,
        List.cons_append, ih hl]
    · have hpf : p a = false := by simpa using hp
      have hnone : ∀ b ∈ l, p b = false := fun b hb => by
        rcases ha b hb with h1 | h1
        · exact absurd h1 hp
        · simpa using h1
      have h1 : l.filter p = [] := List.filter_eq_nil_iff.mpr fun b hb => by simp [hnone b hb]
      have h2 : (l.filter fun x => !p x) = l := List.filter_eq_self.mpr fun b hb => by
        simp [hnone b hb]
      simp [hpf, h1, h2]

/-- **A list whose labelling never decreases is the concatenation of its fibres, in label
order.** -/
theorem flatten_map_filter_range' (f : α → ℕ) : ∀ (L m : ℕ) (l : List α),
    List.Pairwise (fun a b => f a ≤ f b) l → (∀ a ∈ l, m ≤ f a ∧ f a < m + L) →
      ((List.range' m L).map fun k => l.filter fun a => f a == k).flatten = l := by
  intro L
  induction L with
  | zero =>
    intro m l _ hb
    simp only [List.range'_zero, List.map_nil, List.flatten_nil]
    symm
    rw [List.eq_nil_iff_forall_not_mem]
    exact fun a ha => by have := hb a ha; omega
  | succ L ih =>
    intro m l hmono hb
    have hstep : ∀ k ∈ List.range' (m + 1) L,
        (l.filter fun a => f a == k)
          = (l.filter fun a => !(f a == m)).filter fun a => f a == k := by
      intro k hk
      have hkm : k ≠ m := by have := List.mem_range'_1.1 hk; omega
      rw [List.filter_filter]
      refine congrArg (fun P => List.filter P l) (funext fun a => ?_)
      by_cases h : f a = k
      · subst h; simp [hkm]
      · simp [h]
    have hsub : ∀ a ∈ l.filter fun a => !(f a == m), (m + 1) ≤ f a ∧ f a < (m + 1) + L := by
      intro a ha
      rw [List.mem_filter] at ha
      have h1 := hb a ha.1
      have h2 : f a ≠ m := by simpa using ha.2
      omega
    have hpair : List.Pairwise (fun a b => (f a == m) = true ∨ ¬ ((f b == m) = true)) l := by
      refine hmono.imp_of_mem fun {a b} ha _ hab => ?_
      by_cases h : f a = m
      · exact Or.inl (by simp [h])
      · have := (hb a ha).1
        exact Or.inr (by simp only [beq_iff_eq]; omega)
    rw [List.range'_succ, List.map_cons, List.flatten_cons,
      List.map_congr_left hstep, ih (m + 1) _ (hmono.filter _) hsub]
    exact filter_append_filter_not l hpair

/-- Filtering a flattened block list on the block label returns that block. -/
theorem filter_flatten_getElem? (f : α → ℕ) : ∀ (m : ℕ) (bs : List (List α)),
    (∀ (k : ℕ) (hk : k < bs.length) (a : α), a ∈ bs[k] → f a = m + k) →
      ∀ k : ℕ, bs.flatten.filter (fun a => f a == m + k) = (bs[k]?).getD [] := by
  intro m bs
  induction bs generalizing m with
  | nil => intro _ k; simp
  | cons b bs ih =>
    intro hf k
    have hb : ∀ a ∈ b, f a = m := fun a ha => by
      simpa using hf 0 (by simp) a (by simpa using ha)
    have hrest : ∀ (j : ℕ) (hj : j < bs.length) (a : α), a ∈ bs[j] → f a = (m + 1) + j := by
      intro j hj a ha
      have := hf (j + 1) (by simpa using hj) a (by simpa using ha)
      omega
    have hgt : ∀ a ∈ bs.flatten, m + 1 ≤ f a := by
      intro a ha
      obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      rw [hrest j hj a hac]
      omega
    rw [List.flatten_cons, List.filter_append]
    cases k with
    | zero =>
      rw [List.filter_eq_self.mpr fun a ha => by simp [hb a ha],
        List.filter_eq_nil_iff.mpr fun a ha => by have := hgt a ha; simp; omega]
      simp
    | succ k =>
      rw [List.filter_eq_nil_iff.mpr fun a ha => by have := hb a ha; simp; omega,
        List.nil_append, show m + (k + 1) = (m + 1) + k by omega, ih (m + 1) hrest k]
      simp

/-- The tag at a direction's position in the flattened word is its block index. -/
theorem getElem?_tagFrom_idxOf [DecidableEq α] : ∀ (m : ℕ) (bs : List (List α)),
    bs.flatten.Nodup → ∀ (k : ℕ) (hk : k < bs.length) (a : α), a ∈ bs[k] →
      (tagFrom m bs)[bs.flatten.idxOf a]? = some (m + k) := by
  intro m bs
  induction bs generalizing m with
  | nil => intro _ k hk; simp at hk
  | cons b bs ih =>
    intro hnd k hk a ha
    rw [List.flatten_cons] at hnd ⊢
    rw [tagFrom]
    cases k with
    | zero =>
      have hab : a ∈ b := by simpa using ha
      have hlt : b.idxOf a < b.length := List.idxOf_lt_length_iff.2 hab
      rw [List.idxOf_append_of_mem hab, List.getElem?_append_left (by simpa using hlt)]
      simp [hlt]
    | succ k =>
      have hk' : k < bs.length := by simpa using hk
      have hab : a ∈ bs[k] := by simpa using ha
      have hmem : a ∈ bs.flatten := List.mem_flatten.2 ⟨bs[k], List.getElem_mem _, hab⟩
      have hnb : a ∉ b := fun hbm => List.disjoint_of_nodup_append hnd hbm hmem
      rw [List.idxOf_append_of_notMem hnb, List.getElem?_append_right (by simp)]
      simp only [List.length_replicate, Nat.add_sub_cancel_left]
      rw [ih (m + 1) (List.nodup_append.1 hnd).2.1 k hk' a hab]
      exact congrArg some (by omega)

end Regroup

/-! ## The fast model is exactly the execution data -/

namespace FExec

theorem word_eq_map_perm (X : FExec n) : X.word = (List.finRange n).map X.perm := by
  refine List.ext_getElem (by simp [X.word_length]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_finRange]
  rfl

/-- A direction's bead index is the index of the bead listing it. -/
theorem blockOf_eq_of_mem (X : FExec n) {k : ℕ} (hk : k < X.1.length) {a : Fin n}
    (ha : a ∈ X.1[k]) : (X.blockOf a : ℕ) = k := by
  have h := getElem?_tagFrom_idxOf 0 X.1 X.word_nodup k hk a ha
  have hlt : X.1.flatten.idxOf a < (tagFrom 0 X.1).length := by
    rw [length_tagFrom]
    exact List.idxOf_lt_length_iff.2 (X.mem_word a)
  rw [List.getElem?_eq_getElem hlt] at h
  simpa using Option.some.inj h

end FExec

/-- The blocks of `C`, each listed in the order `w` performs it. -/
def blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) : List (List (Fin n)) :=
  (List.finRange C.dims.length).map fun k =>
    ((List.finRange n).map w).filter fun q => beadOf C q == k

/-- The same, with the bead index read as a natural number. -/
theorem blocksOf_eq (C : Ch (□n)) (w : Equiv.Perm (Fin n)) :
    blocksOf C w = (List.range C.dims.length).map fun k =>
      ((List.finRange n).map w).filter fun q => (beadOf C q : ℕ) == k := by
  refine List.ext_getElem (by simp [blocksOf]) fun i h1 h2 => ?_
  simp only [blocksOf, List.getElem_map, List.getElem_finRange, List.getElem_range]
  refine congrArg (fun P => List.filter P ((List.finRange n).map w)) (funext fun q => ?_)
  rw [Bool.eq_iff_iff]
  simp [Fin.ext_iff]

@[simp] theorem length_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) :
    (blocksOf C w).length = C.dims.length := by simp [blocksOf]

theorem mem_wordList (w : Equiv.Perm (Fin n)) (q : Fin n) : q ∈ (List.finRange n).map w :=
  List.mem_map.2 ⟨w.symm q, List.mem_finRange _, w.apply_symm_apply q⟩

theorem getElem?_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (k : ℕ)
    (hk : k < C.dims.length) :
    (blocksOf C w)[k]? =
      some (((List.finRange n).map w).filter fun q => (beadOf C q : ℕ) == k) := by
  rw [blocksOf_eq, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hk),
    List.getElem_range]
  rfl

theorem getElem_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (k : ℕ)
    (h : k < (blocksOf C w).length) :
    (blocksOf C w)[k] = ((List.finRange n).map w).filter fun q => (beadOf C q : ℕ) == k :=
  Option.some.inj ((List.getElem?_eq_getElem h).symm.trans
    (getElem?_blocksOf C w k (by simpa using h)))

theorem mem_getElem_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (q : Fin n)
    (h : (beadOf C q : ℕ) < (blocksOf C w).length) :
    q ∈ (blocksOf C w)[(beadOf C q : ℕ)] := by
  rw [getElem_blocksOf, List.mem_filter]
  exact ⟨mem_wordList w q, by simp⟩

/-- Blocks are nonempty: every bead index is used (`beadOf` is surjective). -/
theorem blocksOf_ne_nil (C : Ch (□n)) (w : Equiv.Perm (Fin n)) :
    ∀ b ∈ blocksOf C w, b ≠ [] := by
  intro b hb
  rw [blocksOf_eq, List.mem_map] at hb
  obtain ⟨k, hk, rfl⟩ := hb
  obtain ⟨q, hq⟩ := beadOf_surjective C ⟨k, by simpa using List.mem_range.1 hk⟩
  refine List.ne_nil_of_mem (a := q) (List.mem_filter.2 ⟨mem_wordList w q, ?_⟩)
  rw [hq]
  simp

/-- The bead labelling never decreases along the word `w` performs. -/
theorem pairwise_beadOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (hc : WordCompat w (beadOf C)) :
    List.Pairwise (fun a b => (beadOf C a : ℕ) ≤ (beadOf C b : ℕ)) ((List.finRange n).map w) := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_finRange] at hi hj
  set a := ((List.finRange n).map w)[i]'(by simp [hi]) with hadef
  set b := ((List.finRange n).map w)[j]'(by simp [hj]) with hbdef
  have hav : a = w ⟨i, hi⟩ := by rw [hadef, List.getElem_map, List.getElem_finRange]; rfl
  have hbv : b = w ⟨j, hj⟩ := by rw [hbdef, List.getElem_map, List.getElem_finRange]; rfl
  by_cases hne : beadOf C a = beadOf C b
  · exact le_of_eq (congrArg Fin.val hne)
  · have hlt : w.symm a < w.symm b := by
      rw [hav, hbv, w.symm_apply_apply, w.symm_apply_apply]
      exact hij
    exact le_of_lt ((hc a b hne).mpr hlt)

/-- **The blocks of `C`, concatenated, are the word `w` performs.** -/
theorem flatten_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (hc : WordCompat w (beadOf C)) :
    (blocksOf C w).flatten = (List.finRange n).map w := by
  rw [blocksOf_eq, List.range_eq_range']
  refine flatten_map_filter_range' (fun q => (beadOf C q : ℕ)) C.dims.length 0 _
    (pairwise_beadOf C w hc) fun a _ => ⟨Nat.zero_le _, by simp⟩

theorem isFExec_blocksOf (C : Ch (□n)) (w : Equiv.Perm (Fin n)) (hc : WordCompat w (beadOf C)) :
    IsFExec n (blocksOf C w) := by
  have hflat := flatten_blocksOf C w hc
  exact ⟨blocksOf_ne_nil C w, by rw [hflat]; exact (List.nodup_finRange n).map w.injective,
    by rw [hflat]; simp⟩

/-- The compatibility packaged into `ExecData`, read off the face order. -/
theorem wordCompat_of_execData (p : ExecData n) : WordCompat p.1.2 (beadOf p.1.1) :=
  wordCompat_of_faceLE p.2

/-- **The fast execution a chain-plus-word names.** -/
def fexecOfExecData (p : ExecData n) : FExec n :=
  ⟨blocksOf p.1.1 p.1.2, isFExec_blocksOf p.1.1 p.1.2 (wordCompat_of_execData p)⟩

theorem perm_fexecOfExecData (p : ExecData n) : (fexecOfExecData p).perm = p.1.2 := by
  have hw : (List.finRange n).map (fexecOfExecData p).perm = (List.finRange n).map p.1.2 := by
    rw [← FExec.word_eq_map_perm]
    exact flatten_blocksOf p.1.1 p.1.2 (wordCompat_of_execData p)
  exact Equiv.ext fun i => List.map_inj_left.1 hw i (List.mem_finRange i)

theorem blockOf_fexecOfExecData (p : ExecData n) (q : Fin n) :
    ((fexecOfExecData p).blockOf q : ℕ) = (beadOf p.1.1 q : ℕ) := by
  have hlt : (beadOf p.1.1 q : ℕ) < (blocksOf p.1.1 p.1.2).length := by simp
  exact (fexecOfExecData p).blockOf_eq_of_mem hlt (mem_getElem_blocksOf p.1.1 p.1.2 q hlt)

/-- **The blocks of an execution's own chain are its beads.** -/
theorem blocksOf_fexecChStar (X : FExec n) : blocksOf (fexecChStar X).chain X.perm = X.1 := by
  have hlen : (fexecChStar X).chain.dims.length = X.1.length := length_blockChain _ _
  have hbead : ∀ q, (beadOf (fexecChStar X).chain q : ℕ) = (X.blockOf q : ℕ) :=
    fun q => beadOf_blockChain _ _ q
  rw [blocksOf_eq, ← X.word_eq_map_perm]
  simp only [hbead]
  rw [hlen]
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  have hk : k < X.1.length := by simpa using h2
  rw [List.getElem_map, List.getElem_range]
  have := filter_flatten_getElem? (fun q : Fin n => (X.blockOf q : ℕ)) 0 X.1
    (fun j hj a ha => by simpa using X.blockOf_eq_of_mem hj ha) k
  simpa [FExec.word, List.getElem?_eq_getElem hk] using this

/-- **The execution built from the blocks of `C` in the order `w` is `(C, w)` again.** -/
theorem fexecChStar_blocksOf (p : ExecData n) : execData (fexecChStar (fexecOfExecData p)) = p :=
  Subtype.ext (Prod.ext
    (by
      change (fexecChStar (fexecOfExecData p)).chain = p.1.1
      rw [chain_fexecChStar]
      exact eq_of_beadOf fun q =>
        (beadOf_blockChain _ _ q).trans (blockOf_fexecOfExecData p q))
    (by
      change runWord (fexecChStar (fexecOfExecData p)) = p.1.2
      rw [runWord_fexecChStar, perm_fexecOfExecData]))

/-- **A fast execution is exactly a chain plus a linearization of it.** -/
def fexecEquiv : FExec n ≃ ExecData n where
  toFun X := execData (fexecChStar X)
  invFun := fexecOfExecData
  left_inv X := Subtype.ext (by
    change blocksOf (fexecChStar X).chain (runWord (fexecChStar X)) = X.1
    rw [runWord_fexecChStar, blocksOf_fexecChStar])
  right_inv := fexecChStar_blocksOf

/-- **The fast model enumerates exactly the executions of `□n`.** -/
def fexecChStarEquiv : FExec n ≃ Ch⋆ (□n) := fexecEquiv.trans execEquiv.symm

@[simp] theorem fexecChStarEquiv_apply (X : FExec n) : fexecChStarEquiv X = fexecChStar X :=
  execEquiv.symm_apply_apply (fexecChStar X)

@[simp] theorem runWord_fexecChStarEquiv (X : FExec n) :
    runWord (fexecChStarEquiv X) = X.perm := by
  rw [fexecChStarEquiv_apply, runWord_fexecChStar]

end FastBridge
