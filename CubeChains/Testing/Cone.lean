import CubeChains.Foundations.FreeGroupoidLift
import CubeChains.Salvetti.Elements
import CubeChains.Testing.FastEquiv
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.FinCases

/-!
# Testing/Cone — the two Artin relations of `□n` are loops inside a principal up-set

`loop_trivial_of_mem_upSet` (`Foundations/FreeGroupoidLift`) kills every loop of `FreeGroupoid C`
staying in `↑b`.  Both Artin relations of `□n` are such loops, over the execution with 2-beads
`[i,i+1]`, `[j,j+1]` (commutation) resp. the 3-bead `[i,i+1,i+2]` (braiding).  Beads are
`Sublist`s, hence *ordered*, which is what spares `Δ²`.

Not built by `lake build CubeChains`.
-/

/-! ### The cone lands on `Ch⋆ (□n)`

Thinness of the cube's execution category is the whole hypothesis; nothing else about `□n` is
used, and no `NonSelfLinked`/`AdmitsAltitude` side condition escapes into the statement. -/

open CategoryTheory CubeChain BPSet in
example (n : ℕ) : Quiver.IsThin (Ch⋆ (□n)) := inferInstance

/-! ## Executions with a distinguished local window -/

variable {n : ℕ}

namespace RefinesRel

/-- Refinements concatenate. -/
theorem append {A₁ B₁ A₂ B₂ : List (List (Fin n))} (h₁ : RefinesRel A₁ B₁)
    (h₂ : RefinesRel A₂ B₂) : RefinesRel (A₁ ++ A₂) (B₁ ++ B₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hsub hlen _ ih =>
      rw [List.cons_append, List.append_assoc]
      exact .cons hsub hlen ih

/-- Splitting a single bead into ordered pieces. -/
theorem single {blk : List (Fin n)} {M : List (List (Fin n))}
    (hsub : ∀ p ∈ M, p.Sublist blk) (hlen : M.flatten.length = blk.length) :
    RefinesRel [blk] M := by
  simpa using RefinesRel.cons hsub hlen RefinesRel.nil

end RefinesRel

namespace CubeChains

/-- Beads performing one direction each. -/
def singles (l : List (Fin n)) : List (List (Fin n)) := l.map ([·])

@[simp] theorem flatten_singles (l : List (Fin n)) : (singles l).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [singles] using ih

theorem singles_ne_nil (l : List (Fin n)) : ∀ p ∈ singles l, p ≠ [] := by
  simp [singles]

/-- `M`, framed by singleton beads: the shape every Artin witness and every object of its relation
loop has, with all the content in `M`. -/
def window (pre post : List (Fin n)) (M : List (List (Fin n))) : List (List (Fin n)) :=
  singles pre ++ (M ++ singles post)

@[simp] theorem flatten_window (pre post : List (Fin n)) (M : List (List (Fin n))) :
    (window pre post M).flatten = pre ++ (M.flatten ++ post) := by
  simp [window]

/-- Refining inside the window. -/
theorem refines_window (pre post : List (Fin n)) {A B : List (List (Fin n))}
    (h : RefinesRel A B) : RefinesRel (window pre post A) (window pre post B) :=
  (RefinesRel.refl _).append (h.append (RefinesRel.refl _))

theorem isFExec_window {pre post : List (Fin n)} {M : List (List (Fin n))}
    (hne : ∀ p ∈ M, p ≠ []) (hnd : (pre ++ (M.flatten ++ post)).Nodup)
    (hlen : (pre ++ (M.flatten ++ post)).length = n) : IsFExec n (window pre post M) := by
  refine ⟨fun p hp => ?_, by simpa using hnd, by simpa using hlen⟩
  rcases List.mem_append.1 hp with h | h
  · exact singles_ne_nil pre p h
  · rcases List.mem_append.1 h with h | h
    · exact hne p h
    · exact singles_ne_nil post p h

/-- Rearranging the window's middle keeps it an execution. -/
theorem isFExec_window_of_perm {pre post : List (Fin n)} {A M : List (List (Fin n))}
    (hw : IsFExec n (window pre post A)) (hne : ∀ p ∈ M, p ≠ [])
    (hperm : M.flatten.Perm A.flatten) : IsFExec n (window pre post M) := by
  obtain ⟨-, hnd, hlen⟩ := hw
  rw [flatten_window] at hnd hlen
  have hp : (pre ++ (M.flatten ++ post)).Perm (pre ++ (A.flatten ++ post)) :=
    (hperm.append_right post).append_left pre
  exact isFExec_window hne (hp.nodup_iff.2 hnd) (by rw [hp.length_eq]; exact hlen)

/-! ## The braid relation `σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁`

Each σ-step is a span whose apex merges two adjacent window slots, so a route alternates
permutation, apex, permutation, …  Both routes run from `abc` to `cba`. -/

/-- The middles along `abc → bac → bca → cba`. -/
def braidRouteP (a b c : Fin n) : List (List (List (Fin n))) :=
  [[[a], [b], [c]], [[a, b], [c]], [[b], [a], [c]], [[b], [a, c]], [[b], [c], [a]],
    [[b, c], [a]], [[c], [b], [a]]]

/-- The middles along `abc → acb → cab → cba`. -/
def braidRouteQ (a b c : Fin n) : List (List (List (Fin n))) :=
  [[[a], [b], [c]], [[a], [b, c]], [[a], [c], [b]], [[a, c], [b]], [[c], [a], [b]],
    [[c], [a, b]], [[c], [b], [a]]]

/-- The twelve objects of the braid relation's loop, as window middles. -/
def braidMiddles (a b c : Fin n) : List (List (List (Fin n))) :=
  braidRouteP a b c ++ braidRouteQ a b c

/-- The 3-bead witness `[a,b,c]`, framed by singletons. -/
def braidWitness (pre post : List (Fin n)) (a b c : Fin n) : List (List (Fin n)) :=
  window pre post [[a, b, c]]

theorem ne_nil_of_mem_braidMiddles {a b c : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ braidMiddles a b c) : ∀ p ∈ M, p ≠ [] := by
  simp only [braidMiddles, braidRouteP, braidRouteQ, List.cons_append, List.nil_append] at hM
  fin_cases hM <;> simp

theorem perm_of_mem_braidMiddles {a b c : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ braidMiddles a b c) : M.flatten.Perm [a, b, c] := by
  have pbac : ([b, a, c] : List (Fin n)).Perm [a, b, c] := .swap a b [c]
  have pacb : ([a, c, b] : List (Fin n)).Perm [a, b, c] := .cons a (.swap b c [])
  have pbca : ([b, c, a] : List (Fin n)).Perm [a, b, c] :=
    (List.Perm.cons b (.swap a c [])).trans pbac
  have pcab : ([c, a, b] : List (Fin n)).Perm [a, b, c] := (List.Perm.swap a c [b]).trans pacb
  have pcba : ([c, b, a] : List (Fin n)).Perm [a, b, c] := (List.Perm.swap b c [a]).trans pbca
  simp only [braidMiddles, braidRouteP, braidRouteQ, List.cons_append, List.nil_append] at hM
  fin_cases hM <;>
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append] <;>
    first
      | exact List.Perm.refl _
      | assumption

/-- **Every object of the braid relation's loop refines the 3-bead witness.** -/
theorem refinesRel_braidMiddles {a b c : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ braidMiddles a b c) : RefinesRel [[a, b, c]] M := by
  have sa : ([a] : List (Fin n)).Sublist [a, b, c] := .cons_cons a (List.nil_sublist _)
  have sb : ([b] : List (Fin n)).Sublist [a, b, c] := .cons a (.cons_cons b (List.nil_sublist _))
  have sc : ([c] : List (Fin n)).Sublist [a, b, c] :=
    .cons a (.cons b (.cons_cons c (List.nil_sublist _)))
  have sab : ([a, b] : List (Fin n)).Sublist [a, b, c] :=
    .cons_cons a (.cons_cons b (List.nil_sublist _))
  have sac : ([a, c] : List (Fin n)).Sublist [a, b, c] :=
    .cons_cons a (.cons b (.cons_cons c (List.nil_sublist _)))
  have sbc : ([b, c] : List (Fin n)).Sublist [a, b, c] :=
    .cons a (.cons_cons b (.cons_cons c (List.nil_sublist _)))
  simp only [braidMiddles, braidRouteP, braidRouteQ, List.cons_append, List.nil_append] at hM
  fin_cases hM <;> exact RefinesRel.single (by simp [*]) (by simp)

/-- The witness is an execution as soon as its word is. -/
theorem isFExec_braidWitness {pre post : List (Fin n)} {a b c : Fin n}
    (hnd : (pre ++ a :: b :: c :: post).Nodup)
    (hlen : (pre ++ a :: b :: c :: post).length = n) :
    IsFExec n (braidWitness pre post a b c) :=
  isFExec_window (by simp) (by simpa using hnd) (by simpa using hlen)

/-- The 3-bead witness, as an execution. -/
def braidWitnessExec {pre post : List (Fin n)} {a b c : Fin n}
    (hw : IsFExec n (braidWitness pre post a b c)) : FExec n := ⟨_, hw⟩

/-- An object of the braid relation's loop, as an execution. -/
def braidObj {pre post : List (Fin n)} {a b c : Fin n}
    (hw : IsFExec n (braidWitness pre post a b c)) {M : List (List (Fin n))}
    (hM : M ∈ braidMiddles a b c) : FExec n :=
  ⟨window pre post M,
    isFExec_window_of_perm hw (ne_nil_of_mem_braidMiddles hM) (perm_of_mem_braidMiddles hM)⟩

/-- **The braid relation's loop lies in the up-set of the 3-bead witness.** -/
theorem refines_braidObj {pre post : List (Fin n)} {a b c : Fin n}
    (hw : IsFExec n (braidWitness pre post a b c)) {M : List (List (Fin n))}
    (hM : M ∈ braidMiddles a b c) : (braidWitnessExec hw).Refines (braidObj hw hM) :=
  refines_window pre post (refinesRel_braidMiddles hM)

/-- **A bead above a one-bead witness inherits its order.**  This is the whole reason the cone
distinguishes the Artin relations from `Δ²`. -/
theorem sublist_pair_of_refinesRel {blk : List (Fin n)} {M : List (List (Fin n))}
    (h : RefinesRel [blk] M) {q : List (Fin n)} (hq : q ∈ M) {x y : Fin n}
    (hxy : ([x, y] : List (Fin n)).Sublist q) : ([x, y] : List (Fin n)).Sublist blk := by
  obtain ⟨z, hz, hsub⟩ := h.exists_sublist q hq
  rw [List.mem_singleton] at hz
  exact hxy.trans (hz ▸ hsub)

/-- **The witness spares `Δ²`**: nothing above it lists two of `a, b, c` inside one bead in the
witness's *opposite* order, and the `Δ²` hexagon's apexes are exactly of that shape. -/
theorem not_refinesRel_of_reversed {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {M : List (List (Fin n))} {q : List (Fin n)} (hq : q ∈ M) {x y : Fin n}
    (hxy : ([x, y] : List (Fin n)).Sublist q)
    (hyx : ([y, x] : List (Fin n)).Sublist [a, b, c]) : ¬ RefinesRel [[a, b, c]] M := by
  intro h
  set r : Fin n → ℕ := fun z => if z = a then 0 else if z = b then 1 else 2 with hr
  have ra : r a = 0 := by simp [hr]
  have rb : r b = 1 := by simp [hr, Ne.symm hab]
  have rc : r c = 2 := by simp [hr, Ne.symm hac, Ne.symm hbc]
  have hp : ([a, b, c] : List (Fin n)).Pairwise fun u v => r u < r v := by
    refine .cons (fun z hz => ?_) (.cons (fun z hz => ?_) (.cons (by simp) .nil))
    · rcases List.mem_cons.1 hz with rfl | hz
      · omega
      · rw [List.mem_singleton] at hz; subst hz; omega
    · rw [List.mem_singleton] at hz; subst hz; omega
  have key : ∀ {u v : Fin n}, ([u, v] : List (Fin n)).Sublist [a, b, c] → r u < r v :=
    fun hs => hp.forall_sublist hs
  have := key (sublist_pair_of_refinesRel h hq hxy)
  have := key hyx
  omega

/-! ## The commutation relation `σᵢσⱼ = σⱼσᵢ` for `|i − j| ≥ 2`

The two 2-beads sit at unrelated slots of the window, so the loop's objects range independently
over the refinements of each. -/

/-- Two beads separated by singletons. -/
def commMiddle (mid : List (Fin n)) (M N : List (List (Fin n))) : List (List (Fin n)) :=
  M ++ (singles mid ++ N)

theorem ne_nil_commMiddle {mid : List (Fin n)} {M N : List (List (Fin n))}
    (hM : ∀ p ∈ M, p ≠ []) (hN : ∀ p ∈ N, p ≠ []) : ∀ p ∈ commMiddle mid M N, p ≠ [] := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact hM p h
  · rcases List.mem_append.1 h with h | h
    · exact singles_ne_nil mid p h
    · exact hN p h

/-- The three refinements of a 2-bead. -/
def pairSplits (x y : Fin n) : List (List (List (Fin n))) := [[[x], [y]], [[y], [x]], [[x, y]]]

theorem ne_nil_of_mem_pairSplits {x y : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ pairSplits x y) : ∀ p ∈ M, p ≠ [] := by
  simp only [pairSplits] at hM
  fin_cases hM <;> simp

theorem perm_of_mem_pairSplits {x y : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ pairSplits x y) : M.flatten.Perm [x, y] := by
  simp only [pairSplits] at hM
  fin_cases hM <;>
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append] <;>
    first
      | exact List.Perm.refl _
      | exact .swap x y []

theorem refinesRel_pairSplits {x y : Fin n} {M : List (List (Fin n))}
    (hM : M ∈ pairSplits x y) : RefinesRel [[x, y]] M := by
  have sx : ([x] : List (Fin n)).Sublist [x, y] := .cons_cons x (List.nil_sublist _)
  have sy : ([y] : List (Fin n)).Sublist [x, y] := .cons x (.cons_cons y (List.nil_sublist _))
  have sxy : ([x, y] : List (Fin n)).Sublist [x, y] := List.Sublist.refl _
  simp only [pairSplits] at hM
  fin_cases hM <;> exact RefinesRel.single (by simp [*]) (by simp)

/-- The middles along `σᵢ` then `σⱼ`. -/
def commRouteP (a b c d : Fin n) : List (List (List (Fin n)) × List (List (Fin n))) :=
  [([[a], [b]], [[c], [d]]), ([[a, b]], [[c], [d]]), ([[b], [a]], [[c], [d]]),
    ([[b], [a]], [[c, d]]), ([[b], [a]], [[d], [c]])]

/-- The middles along `σⱼ` then `σᵢ`. -/
def commRouteQ (a b c d : Fin n) : List (List (List (Fin n)) × List (List (Fin n))) :=
  [([[a], [b]], [[c], [d]]), ([[a], [b]], [[c, d]]), ([[a], [b]], [[d], [c]]),
    ([[a, b]], [[d], [c]]), ([[b], [a]], [[d], [c]])]

/-- The eight objects of the commutation relation's loop, as window middles. -/
def commMiddles (a b c d : Fin n) : List (List (List (Fin n)) × List (List (Fin n))) :=
  commRouteP a b c d ++ commRouteQ a b c d

theorem mem_pairSplits_of_mem_commMiddles {a b c d : Fin n}
    {p : List (List (Fin n)) × List (List (Fin n))} (hp : p ∈ commMiddles a b c d) :
    p.1 ∈ pairSplits a b ∧ p.2 ∈ pairSplits c d := by
  simp only [commMiddles, commRouteP, commRouteQ, List.cons_append, List.nil_append] at hp
  fin_cases hp <;> exact ⟨by simp [pairSplits], by simp [pairSplits]⟩

/-- The two-2-bead witness, framed by singletons. -/
def commWitness (pre mid post : List (Fin n)) (a b c d : Fin n) : List (List (Fin n)) :=
  window pre post (commMiddle mid [[a, b]] [[c, d]])

/-- The witness is an execution as soon as its word is. -/
theorem isFExec_commWitness {pre mid post : List (Fin n)} {a b c d : Fin n}
    (hnd : (pre ++ a :: b :: (mid ++ c :: d :: post)).Nodup)
    (hlen : (pre ++ a :: b :: (mid ++ c :: d :: post)).length = n) :
    IsFExec n (commWitness pre mid post a b c d) :=
  isFExec_window (ne_nil_commMiddle (by simp) (by simp)) (by simpa [commMiddle] using hnd)
    (by simpa [commMiddle] using hlen)

/-- The two-2-bead witness, as an execution. -/
def commWitnessExec {pre mid post : List (Fin n)} {a b c d : Fin n}
    (hw : IsFExec n (commWitness pre mid post a b c d)) : FExec n := ⟨_, hw⟩

/-- An object of the commutation relation's loop, as an execution. -/
def commObj {pre mid post : List (Fin n)} {a b c d : Fin n}
    (hw : IsFExec n (commWitness pre mid post a b c d))
    {p : List (List (Fin n)) × List (List (Fin n))} (hp : p ∈ commMiddles a b c d) : FExec n :=
  ⟨window pre post (commMiddle mid p.1 p.2), by
    obtain ⟨h1, h2⟩ := mem_pairSplits_of_mem_commMiddles hp
    refine isFExec_window_of_perm hw
      (ne_nil_commMiddle (ne_nil_of_mem_pairSplits h1) (ne_nil_of_mem_pairSplits h2)) ?_
    · simp only [commMiddle, List.flatten_append, flatten_singles]
      exact (perm_of_mem_pairSplits h1).append
        ((List.Perm.refl mid).append (perm_of_mem_pairSplits h2))⟩

/-- **The commutation relation's loop lies in the up-set of the two-2-bead witness.** -/
theorem refines_commObj {pre mid post : List (Fin n)} {a b c d : Fin n}
    (hw : IsFExec n (commWitness pre mid post a b c d))
    {p : List (List (Fin n)) × List (List (Fin n))} (hp : p ∈ commMiddles a b c d) :
    (commWitnessExec hw).Refines (commObj hw hp) := by
  obtain ⟨h1, h2⟩ := mem_pairSplits_of_mem_commMiddles hp
  exact refines_window pre post ((refinesRel_pairSplits h1).append
    ((RefinesRel.refl _).append (refinesRel_pairSplits h2)))

/-! ### Non-vacuity -/

example : IsFExec 3 (braidWitness [] [] 0 1 2) := isFExec_braidWitness (by decide) (by decide)

example : IsFExec 4 (commWitness [] [] [] 0 1 2 3) := isFExec_commWitness (by decide) (by decide)

/-
Smoke checks (`decide`-free evals, against `execs`/`refinesB` of `Testing/FastExec`):

#eval (braidMiddles (0 : Fin 3) 1 2).eraseDups.length                        -- 12
#eval (braidMiddles (0 : Fin 3) 1 2).all fun M => refinesB [[0, 1, 2]] M     -- true
#eval ((execs (SubCube.full 3)).filter fun X => refinesB [[0, 1, 2]] X.1).length  -- 13
#eval refinesB [[(0 : Fin 3), 1, 2]] [[2], [1, 0]]                           -- false  (Δ² apex)
#eval refinesB [[(0 : Fin 3), 1, 2]] [[2, 0], [1]]                           -- false  (Δ² apex)
#eval ((commMiddles (0 : Fin 4) 1 2 3).map fun p => commMiddle [] p.1 p.2).eraseDups.length  -- 8
-/

end CubeChains
