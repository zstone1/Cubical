import CubeChains.Testing.RunOrder
import CubeChains.Testing.FastExec

/-!
# Testing/FastEquiv — an execution of `□n` is a chain plus a linearization of it

`execEquiv : Ch⋆ (□n) ≃ ExecData n` presents an execution as its chain `C` together with the run
word `w` linearizing it, subject to one condition: `C`'s ordered partition must be coarser than
`w`'s (`chFace C ⊑ chFace (wordChain w)`).

Both halves are explicit.  Completeness (`ext_runWord`) is thinness of `Ch (□n)`: the run's map is
a *morphism* onto the chain, so the chain it linearizes determines it.  The construction (`ofWord`)
is `reflectHom` between the two `ofBlockMap` chains, so it computes.
-/

open CategoryTheory CubeChain BPSet Opposite

namespace CubeChains

open ChStar

variable {n L : ℕ}

/-! ## All-edges shapes

A shape is all edges exactly when its total dimension is its bead count: every bead contributes at
least one, so equality forces every bead to contribute exactly one. -/

/-- **A shape of total dimension its own length is all edges** — the converse of
`dimSum_eq_length_of_ones`. -/
theorem ones_of_dimSum_eq_length : ∀ {l : List ℕ+}, dimSum l = l.length → ∀ d ∈ l, d = 1
  | [], _ => by simp
  | a :: t, h => by
      have hpos : 0 < (a : ℕ) := a.pos
      have ih := length_le_dimSum t
      have hstep : dimSum (a :: t) = (a : ℕ) + dimSum t := rfl
      rw [List.length_cons, hstep] at h
      have ha : (a : ℕ) = 1 := by omega
      have ht : dimSum t = t.length := by omega
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact PNat.coe_injective ha
      · exact ones_of_dimSum_eq_length ht d hd

/-! ## The face order, in ordered-partition terms

`X ⊑ Y` compares two covectors coordinate by coordinate; for `braidSign` of a height function this
says the coarser height's strict order is the finer one's wherever the coarser one separates. -/

private theorem sign_sub_congr {x y u v : ℤ} (hxy : x ≠ y) (h₁ : x < y ↔ u < v)
    (h₂ : y < x ↔ v < u) : SignType.sign (x - y) = SignType.sign (u - v) := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [sign_neg (by omega), sign_neg (by have := h₁.mp hlt; omega)]
  · exact absurd heq hxy
  · rw [sign_pos (by omega), sign_pos (by have := h₂.mp hgt; omega)]

private theorem lt_iff_of_sign_sub {x y u v : ℤ} (hxy : x ≠ y)
    (h : SignType.sign (x - y) = SignType.sign (u - v)) :
    (x < y ↔ u < v) ∧ (y < x ↔ v < u) := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [sign_neg (by omega)] at h
    have huv := sign_eq_neg_one_iff.mp h.symm
    exact ⟨⟨fun _ => by omega, fun _ => by omega⟩, ⟨fun _ => by omega, fun _ => by omega⟩⟩
  · exact absurd heq hxy
  · rw [sign_pos (by omega)] at h
    have huv := sign_eq_one_iff.mp h.symm
    exact ⟨⟨fun _ => by omega, fun _ => by omega⟩, ⟨fun _ => by omega, fun _ => by omega⟩⟩

/-- **The face order of two braid covectors is order agreement off the coarser one's ties.** -/
theorem braidSign_faceLE_iff {b a : Fin n → ℤ} :
    braidSign b ⊑ braidSign a ↔ ∀ i j, b i ≠ b j → (b i < b j ↔ a i < a j) := by
  constructor
  · intro h i j hne
    have key : ∀ p q : Fin n, p < q → b p ≠ b q →
        (b p < b q ↔ a p < a q) ∧ (b q < b p ↔ a q < a p) := by
      intro p q hpq hpqne
      have he : SignType.sign (b p - b q) = 0 ∨
          SignType.sign (b p - b q) = SignType.sign (a p - a q) := h ⟨(p, q), hpq⟩
      refine lt_iff_of_sign_sub hpqne (he.resolve_left fun h0 => hpqne ?_)
      have := sign_eq_zero_iff.mp h0
      omega
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact (key i j hij hne).1
    · exact absurd rfl hne
    · exact (key j i hij (Ne.symm hne)).2
  · intro h e
    by_cases hb : b e.1.1 = b e.1.2
    · exact Or.inl (sign_eq_zero_iff.mpr (by omega))
    · exact Or.inr (sign_sub_congr hb (h _ _ hb) (h _ _ (Ne.symm hb)))

/-- **The refinement order on chains of `□n` reads their ordered partitions.** -/
theorem chFace_faceLE_iff {t C : Ch (□n)} :
    (chFace C).1 ⊑ (chFace t).1 ↔
      ∀ i j, (beadOf C i : ℕ) ≠ (beadOf C j : ℕ) →
        ((beadOf C i : ℕ) < (beadOf C j : ℕ) ↔ (beadOf t i : ℕ) < (beadOf t j : ℕ)) := by
  change braidSign (fun q => ((beadOf C q : ℕ) : ℤ)) ⊑ braidSign (fun q => ((beadOf t q : ℕ) : ℤ))
    ↔ _
  rw [braidSign_faceLE_iff]
  simp only [ne_eq, Nat.cast_inj, Nat.cast_lt]

/-! ## A run is pinned by the chain it linearizes

The run's classifying map `r.map` is itself a *morphism* `totalChain C r ⟶ C` in `Ch (□n)`, and
that category is thin — so nothing else can linearize the same chain. -/

/-- The chain of `□n` a run of `⋁C.dims` linearizes. -/
def totalChain (C : Ch (□n)) (r : Run (⋁C.dims)) : Ch (□n) := ⟨r.dims, r.map ≫ C.map⟩

/-- Two wedge maps that agree after `C.map` agree — `Ch (□n)` is thin. -/
theorem map_ext_over {C : Ch (□n)} {d : List ℕ+} {m m' : ⋁d ⟶ ⋁C.dims}
    (h : m ≫ C.map = m' ≫ C.map) : m = m' :=
  congrArg ChainCat.Hom.φ
    ((chainCat_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)
      (⟨d, m ≫ C.map⟩ : Ch (□n)) C).elim ⟨m, rfl⟩ ⟨m', h.symm⟩)

/-- **A run is determined by the chain it linearizes.** -/
theorem run_eq_of_totalChain {C : Ch (□n)} (r s : Run (⋁C.dims))
    (h : totalChain C r = totalChain C s) : r = s := by
  obtain ⟨hd, hm⟩ := ChainCat.Obj.eq_mk_of_eq h
  refine Run.ext (ChainCat.Obj.mk_eq_mk hd (map_ext_over ?_))
  rw [Category.assoc]
  exact hm

namespace ChStar

/-- The run word determines the chain the run linearizes. -/
theorem runChain_eq_of_runWord {x y : Ch⋆ (□n)} (hw : runWord x = runWord y) :
    runChain x = runChain y :=
  eq_of_beadOf fun q => by rw [← runWord_symm_val, ← runWord_symm_val, hw]

/-- **Executions are pinned by their chain and their run word.**  This is what makes an enumeration
of run words *complete*. -/
theorem ext_runWord {x y : Ch⋆ (□n)} (hc : x.chain = y.chain) (hw : runWord x = runWord y) :
    x = y := by
  obtain ⟨cx, ax⟩ := x
  obtain ⟨cy, ay⟩ := y
  obtain rfl : cx = cy := Opposite.unop_injective hc
  refine congrArg (Sigma.mk cx) ((runPshEquiv cx.unop.dims).injective ?_)
  exact run_eq_of_totalChain _ _ (runChain_eq_of_runWord hw)

/-- An execution refines its own linearization. -/
def runRefine (x : Ch⋆ (□n)) : runChain x ⟶ x.chain := ⟨x.run.map, rfl⟩

/-- The chain of an execution is coarser than its run. -/
theorem chFace_runChain_le (x : Ch⋆ (□n)) :
    (chFace x.chain).1 ⊑ (chFace (runChain x)).1 :=
  chFace_faceLE (runRefine x)

end ChStar

/-! ## Building an execution from a word -/

/-- The chain of `□n` whose beads are the blocks of `β`, in order. -/
def blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) : Ch (□n) :=
  (chEquivCubeChain (□n)).symm (ofBlockMap β hβ)

theorem beadOf_blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) (q : Fin n) :
    (beadOf (blockChain β hβ) q : ℕ) = (β q : ℕ) := beadOf_ofBlockMap β hβ q

theorem length_blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    (blockChain β hβ).dims.length = L := by
  simp only [blockChain]
  rw [chEquivCubeChain_symm_dims]
  change ((ofBlockMap β hβ).cubes.map (fun c => c.1)).length = L
  rw [List.length_map]
  exact length_blockCubes β hβ

/-- **The all-edges chain performing the directions in the order `w`** — one bead per step. -/
def wordChain (w : Equiv.Perm (Fin n)) : Ch (□n) := blockChain ⇑w.symm w.symm.surjective

theorem beadOf_wordChain (w : Equiv.Perm (Fin n)) (q : Fin n) :
    (beadOf (wordChain w) q : ℕ) = (w.symm q : ℕ) := beadOf_blockChain _ _ q

theorem length_wordChain (w : Equiv.Perm (Fin n)) : (wordChain w).dims.length = n :=
  length_blockChain _ _

theorem ones_wordChain (w : Equiv.Perm (Fin n)) : ∀ d ∈ (wordChain w).dims, d = 1 :=
  ones_of_dimSum_eq_length
    ((wedgeDimSum_eq (wordChain w).map).trans (length_wordChain w).symm)

/-- The compatibility a word must satisfy to linearize the blocks of `β`: `β`'s strict order is
`w`'s wherever `β` separates. -/
def WordCompat (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) : Prop :=
  ∀ i j, β i ≠ β j → (β i < β j ↔ w.symm i < w.symm j)

theorem faceLE_of_wordCompat {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L}
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    (chFace (blockChain β hβ)).1 ⊑ (chFace (wordChain w)).1 := by
  refine chFace_faceLE_iff.mpr fun i j hne => ?_
  rw [beadOf_blockChain, beadOf_blockChain] at hne
  rw [beadOf_blockChain, beadOf_blockChain, beadOf_wordChain, beadOf_wordChain]
  exact hc i j (fun he => hne (congrArg Fin.val he))

theorem wordCompat_of_faceLE {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L}
    (hβ : Function.Surjective β)
    (h : (chFace (blockChain β hβ)).1 ⊑ (chFace (wordChain w)).1) : WordCompat w β := by
  intro i j hne
  have hval := chFace_faceLE_iff.mp h i j (by
    rw [beadOf_blockChain, beadOf_blockChain]; exact fun he => hne (Fin.val_injective he))
  rw [beadOf_blockChain, beadOf_blockChain, beadOf_wordChain, beadOf_wordChain] at hval
  exact hval

/-- The refinement of `blockChain β` by the run `w` performs. -/
def wordRefine {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L} (hβ : Function.Surjective β)
    (hc : WordCompat w β) : wordChain w ⟶ blockChain β hβ :=
  reflectHom (faceLE_of_wordCompat hβ hc)

/-- **The execution performing the directions in the order `w`, with beads the blocks of `β`.** -/
def ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hc : WordCompat w β) : Ch⋆ (□n) :=
  ⟨op (blockChain β hβ),
    (runPshEquiv (blockChain β hβ).dims).symm
      ⟨⟨(wordChain w).dims, (wordRefine hβ hc).φ⟩, ones_wordChain w⟩⟩

@[simp] theorem chain_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    (ofWord w β hβ hc).chain = blockChain β hβ := rfl

theorem run_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hc : WordCompat w β) :
    (ofWord w β hβ hc).run = ⟨⟨(wordChain w).dims, (wordRefine hβ hc).φ⟩, ones_wordChain w⟩ :=
  (runPshEquiv (blockChain β hβ).dims).apply_symm_apply _

theorem runChain_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    runChain (ofWord w β hβ hc) = wordChain w :=
  (congrArg (totalChain (blockChain β hβ)) (run_ofWord w β hβ hc)).trans
    (congrArg (ChainCat.Obj.mk (wordChain w).dims) (wordRefine hβ hc).w)

@[simp] theorem runWord_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    runWord (ofWord w β hβ hc) = w :=
  runWord_of_runChain_ofBlockMap _ w (runChain_ofWord w β hβ hc)

/-! ## Completeness: every execution is `ofWord` of its own data -/

/-- A chain is the block chain of its own ordered partition. -/
theorem blockChain_beadOf (C : Ch (□n)) : blockChain (beadOf C) (beadOf_surjective C) = C :=
  eq_of_beadOf fun q => beadOf_blockChain _ _ q

namespace ChStar

/-- The chain a run linearizes is the word chain of its run word. -/
theorem runChain_eq_wordChain (x : Ch⋆ (□n)) : runChain x = wordChain (runWord x) :=
  eq_of_beadOf fun q => (runWord_symm_val x q).symm.trans (beadOf_wordChain _ q).symm

theorem wordCompat_runWord (x : Ch⋆ (□n)) : WordCompat (runWord x) (beadOf x.chain) := by
  refine wordCompat_of_faceLE (beadOf_surjective x.chain) ?_
  rw [blockChain_beadOf, ← runChain_eq_wordChain]
  exact chFace_runChain_le x

/-- **Every execution is built from its own chain and run word.** -/
theorem eq_ofWord (x : Ch⋆ (□n)) :
    ofWord (runWord x) (beadOf x.chain) (beadOf_surjective x.chain) (wordCompat_runWord x) = x :=
  ext_runWord (by rw [chain_ofWord, blockChain_beadOf]) (by rw [runWord_ofWord])

end ChStar

/-! ## The object equivalence -/

/-- **The data of an execution of `□n`**: a chain together with a run word linearizing it. -/
def ExecData (n : ℕ) : Type :=
  {p : Ch (□n) × Equiv.Perm (Fin n) // (chFace p.1).1 ⊑ (chFace (wordChain p.2)).1}

/-- The chain and run word of an execution. -/
def execData (x : Ch⋆ (□n)) : ExecData n :=
  ⟨(x.chain, runWord x), by
    rw [← ChStar.runChain_eq_wordChain]; exact ChStar.chFace_runChain_le x⟩

/-- The execution a chain-plus-word names. -/
def ofExecData (p : ExecData n) : Ch⋆ (□n) :=
  ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1)
    (wordCompat_of_faceLE (beadOf_surjective p.1.1) (by rw [blockChain_beadOf]; exact p.2))

@[simp] theorem chain_ofExecData (p : ExecData n) : (ofExecData p).chain = p.1.1 := by
  refine Eq.trans ?_ (blockChain_beadOf p.1.1)
  exact chain_ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1) _

@[simp] theorem runWord_ofExecData (p : ExecData n) : runWord (ofExecData p) = p.1.2 :=
  runWord_ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1) _

theorem execData_ofExecData (p : ExecData n) : execData (ofExecData p) = p := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact chain_ofExecData p
  · exact runWord_ofExecData p

/-- **An execution of `□n` is a chain plus a linearization of it.** -/
def execEquiv : Ch⋆ (□n) ≃ ExecData n where
  toFun := execData
  invFun := ofExecData
  left_inv := ChStar.eq_ofWord
  right_inv := execData_ofExecData

end CubeChains

/-! ## The fast model

`Testing/FastExec`'s `FExec n` is a word plus a grouping into consecutive nonempty blocks.  Tagging
each letter of the word with its block index gives a weakly monotone label list, and monotonicity is
exactly the `WordCompat` the chain side asks for. -/

section FastBridge

open CategoryTheory Opposite CubeChains CubeChains.ChStar

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
          (RunWedge.Sev_eq_dim (fexecChStar X).runWedge (fexecChStar X).chain.map).symm
          (FExec.fperm X Y) := by
  rw [permOf_eq_runWord]
  exact congrArg _ ((stepPerm_eq f).symm.trans (fperm_eq_stepPerm f))

/-- **`Y`'s beads refine `X`'s** — the base of an arrow is a chain refinement, and `blockIdx` is
monotone. -/
theorem blockOf_le_of_arrow {X Y : FExec n} (f : fexecChStar X ⟶ fexecChStar Y) {q q' : Fin n}
    (h : (Y.blockOf q : ℕ) ≤ (Y.blockOf q' : ℕ)) : (X.blockOf q : ℕ) ≤ (X.blockOf q' : ℕ) := by
  have hb : ∀ (Z : FExec n) (r : Fin n),
      (beadOf (fexecChStar Z).chain r : ℕ) = (Z.blockOf r : ℕ) := fun Z r =>
    beadOf_blockChain _ _ r
  have hmono : Monotone (blockIdx (f.1.unop)ᵂ) :=
    serialWedge_blockIdx_monotone _ f.1.unop.φ.app_init
  have hstep : ∀ r : Fin n,
      beadOf (fexecChStar X).chain r = blockIdx (f.1.unop)ᵂ (beadOf (fexecChStar Y).chain r) :=
    fun r => beadOf_blockIdx f.1.unop r
  have hle : beadOf (fexecChStar Y).chain q ≤ beadOf (fexecChStar Y).chain q' := by
    rw [Fin.le_def, hb, hb]; exact h
  have := hmono hle
  rw [← hstep, ← hstep, Fin.le_def, hb, hb] at this
  exact this

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
  wordCompat_of_faceLE (beadOf_surjective p.1.1) (by rw [blockChain_beadOf]; exact p.2)

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
