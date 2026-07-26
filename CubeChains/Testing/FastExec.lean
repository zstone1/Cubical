import CubeChains.Testing.Cells
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Basic

/-!
# Testing/FastExec — the executions of a sub-precubical set of `□n`, combinatorially

A cube chain of `□n` traverses every direction exactly once, so its beads are faces whose direction
sets partition `Fin n` in order; an execution linearizes each bead.  Hence an execution *is* a list
of nonempty blocks of `Fin n` whose concatenation (the `word`) lists every direction once, and a
refinement `X ⟶ Y` splits each bead of `X` into consecutive beads of `Y`, each a `List.Sublist` of
it.  Both are decidable and enumerable without touching the `Glue` presheaf machinery.

Not built by `lake build CubeChains`.
-/

variable {n : ℕ}

/-! ## Refinement of block lists

`RefinesRel X Y` — read "`Y` refines `X`" — groups `Y` into one consecutive run per bead of `X`.
-/

/-- One consecutive group of `Y` per bead `b` of `X`, each part an order-preserving piece of `b`
exhausting it. -/
inductive RefinesRel : List (List (Fin n)) → List (List (Fin n)) → Prop
  | nil : RefinesRel [] []
  | cons {b bs ps ys} (hsub : ∀ p ∈ ps, p.Sublist b) (hlen : ps.flatten.length = b.length)
      (h : RefinesRel bs ys) : RefinesRel (b :: bs) (ps ++ ys)

namespace RefinesRel

@[refl] theorem refl : ∀ bs : List (List (Fin n)), RefinesRel bs bs
  | [] => .nil
  | b :: bs => RefinesRel.cons (ps := [b])
      (fun p hp => by rw [List.mem_singleton.1 hp]) (by simp) (refl bs)

theorem length_flatten {A B : List (List (Fin n))} (h : RefinesRel A B) :
    B.flatten.length = A.flatten.length := by
  induction h with
  | nil => rfl
  | cons hsub hlen h ih => simp [List.flatten_append, hlen, ih]

/-- Every bead of the finer list sits inside some bead of the coarser one. -/
theorem exists_sublist {A B : List (List (Fin n))} (h : RefinesRel A B) :
    ∀ z ∈ B, ∃ a ∈ A, z.Sublist a := by
  induction h with
  | nil => simp
  | @cons b bs ps ys hsub hlen h ih =>
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact ⟨b, by simp, hsub z hz⟩
    · obtain ⟨a, ha, hza⟩ := ih z hz
      exact ⟨a, List.mem_cons_of_mem _ ha, hza⟩

/-- A refinement of a concatenation splits at the same place. -/
theorem split_append : ∀ {A₁ A₂ B : List (List (Fin n))}, RefinesRel (A₁ ++ A₂) B →
    ∃ B₁ B₂, B = B₁ ++ B₂ ∧ RefinesRel A₁ B₁ ∧ RefinesRel A₂ B₂ := by
  intro A₁
  induction A₁ with
  | nil => intro A₂ B h; exact ⟨[], B, rfl, .nil, h⟩
  | cons a A₁ ih =>
    intro A₂ B h
    cases h with
    | @cons _ _ ps ys hsub hlen h' =>
      obtain ⟨C₁, C₂, rfl, h1, h2⟩ := ih h'
      exact ⟨ps ++ C₁, C₂, by rw [List.append_assoc], .cons hsub hlen h1, h2⟩

theorem trans {A B C : List (List (Fin n))} (h₁ : RefinesRel A B) :
    RefinesRel B C → RefinesRel A C := by
  induction h₁ generalizing C with
  | nil => intro h2; cases h2; exact .nil
  | @cons b bs ps ys hsub hlen h ih =>
    intro h2
    obtain ⟨C₁, C₂, rfl, h1, h2'⟩ := h2.split_append
    refine .cons (fun z hz => ?_) ?_ (ih h2')
    · obtain ⟨p, hp, hzp⟩ := h1.exists_sublist z hz
      exact hzp.trans (hsub p hp)
    · rw [h1.length_flatten, hlen]

end RefinesRel

/-! ## Deciding refinement -/

/-- Consume from `ys` the beads making up one bead `b`, `m` of whose letters are unaccounted for. -/
def peel (b : List (Fin n)) : List (List (Fin n)) → ℕ → Option (List (List (Fin n)))
  | ys, 0 => some ys
  | [], _ + 1 => none
  | y :: ys, m + 1 =>
      if y.Sublist b ∧ y.length ≤ m + 1 then peel b ys (m + 1 - y.length) else none

theorem peel_some (b : List (Fin n)) (ys : List (List (Fin n))) :
    ∀ (m : ℕ) (rest : List (List (Fin n))), peel b ys m = some rest →
      ∃ ps, ys = ps ++ rest ∧ (∀ p ∈ ps, p.Sublist b) ∧ ps.flatten.length = m := by
  induction ys with
  | nil =>
    intro m rest h
    cases m with
    | zero => exact ⟨[], by simpa [peel] using h, by simp, by simp⟩
    | succ k => simp [peel] at h
  | cons y ys ih =>
    intro m rest h
    cases m with
    | zero => exact ⟨[], by simpa [peel] using h, by simp, by simp⟩
    | succ k =>
      rw [peel] at h
      split at h
      · next hc =>
        obtain ⟨ps, hps, hsub, hlen⟩ := ih _ _ h
        have h2 := hc.2
        refine ⟨y :: ps, by rw [hps]; rfl, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hc.1
          · exact hsub p hp
        · simp only [List.flatten_cons, List.length_append, hlen]
          omega
      · simp at h

theorem peel_of_split (b : List (Fin n)) : ∀ (ps rest : List (List (Fin n))) (m : ℕ),
    (∀ p ∈ ps, p ≠ []) → (∀ p ∈ ps, p.Sublist b) → ps.flatten.length = m →
      peel b (ps ++ rest) m = some rest := by
  intro ps
  induction ps with
  | nil => intro rest m _ _ hm; simp only [List.flatten_nil, List.length_nil] at hm
           subst hm; simp [peel]
  | cons p ps ih =>
    intro rest m hne hsub hm
    have hp : p ≠ [] := hne p (by simp)
    have hpl : 0 < p.length := by cases p with
      | nil => exact absurd rfl hp
      | cons _ _ => simp
    simp only [List.flatten_cons, List.length_append] at hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [List.cons_append, peel, if_pos ⟨hsub p (by simp), by omega⟩]
    exact ih rest (k + 1 - p.length) (fun q hq => hne q (by simp [hq]))
      (fun q hq => hsub q (by simp [hq])) (by omega)

/-- The refinement test: peel one group of `ys` per bead of `bs`. -/
def refinesB : List (List (Fin n)) → List (List (Fin n)) → Bool
  | [], ys => ys.isEmpty
  | b :: bs, ys =>
      match peel b ys b.length with
      | none => false
      | some rest => refinesB bs rest

theorem refinesB_sound : ∀ (bs ys : List (List (Fin n))), (∀ y ∈ ys, y ≠ []) →
    refinesB bs ys = true → RefinesRel bs ys := by
  intro bs
  induction bs with
  | nil =>
    intro ys _ h
    simp only [refinesB, List.isEmpty_iff] at h
    subst h; exact .nil
  | cons b bs ih =>
    intro ys hne h
    rw [refinesB] at h
    cases hpe : peel b ys b.length with
    | none => rw [hpe] at h; simp at h
    | some rest =>
      rw [hpe] at h
      obtain ⟨ps, hps, hsub, hlen⟩ := peel_some b ys b.length rest hpe
      subst hps
      exact .cons hsub hlen (ih rest (fun y hy => hne y (List.mem_append_right _ hy)) h)

theorem refinesB_complete : ∀ {bs ys : List (List (Fin n))}, RefinesRel bs ys →
    (∀ y ∈ ys, y ≠ []) → refinesB bs ys = true := by
  intro bs ys h
  induction h with
  | nil => intro _; simp [refinesB]
  | @cons b bs ps ys hsub hlen h ih =>
    intro hne
    have hpe := peel_of_split b ps ys b.length
      (fun p hp => hne p (List.mem_append_left _ hp)) hsub hlen
    rw [refinesB, hpe]
    exact ih (fun y hy => hne y (List.mem_append_right _ hy))

theorem refinesB_iff (bs ys : List (List (Fin n))) (hne : ∀ y ∈ ys, y ≠ []) :
    refinesB bs ys = true ↔ RefinesRel bs ys :=
  ⟨refinesB_sound bs ys hne, fun h => refinesB_complete h hne⟩

/-! ## Choosing an ordered block out of the remaining directions -/

variable {α : Type*}

/-- Choose one entry of a list, keeping the rest in order. -/
def selects : List α → List (α × List α)
  | [] => []
  | a :: as => (a, as) :: (selects as).map fun p => (p.1, a :: p.2)

theorem map_fst_selects : ∀ l : List α, (selects l).map Prod.fst = l
  | [] => rfl
  | a :: as => by simp [selects, List.map_map, Function.comp_def, map_fst_selects as]

theorem selects_perm : ∀ (l : List α) (a : α) (r : List α),
    (a, r) ∈ selects l → (a :: r).Perm l := by
  intro l
  induction l with
  | nil => intro a r h; simp [selects] at h
  | cons c cs ih =>
    intro a r h
    rw [selects, List.mem_cons] at h
    rcases h with h | h
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.Perm.refl _
    · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
      rw [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      exact (List.Perm.swap c p.1 p.2).trans ((ih p.1 p.2 hp).cons c)

theorem exists_mem_selects : ∀ (l : List α) (a : α), a ∈ l → ∃ r, (a, r) ∈ selects l := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons c cs ih =>
    intro a h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨cs, by simp [selects]⟩
    · obtain ⟨r, hr⟩ := ih a h
      exact ⟨c :: r, by
        rw [selects]
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(a, r), hr, rfl⟩)⟩

/-- All ways to pick an ordered `k`-tuple of distinct entries of `l`, with the leftover in order. -/
def picks : ℕ → List α → List (List α × List α)
  | 0, l => [([], l)]
  | k + 1, l => (selects l).flatMap fun s => (picks k s.2).map fun q => (s.1 :: q.1, q.2)

theorem picks_spec : ∀ (k : ℕ) (l : List α) (p : List α × List α), p ∈ picks k l →
    p.1.length = k ∧ (p.1 ++ p.2).Perm l := by
  intro k
  induction k with
  | zero => intro l p hp; simp only [picks, List.mem_singleton] at hp; subst hp; simp
  | succ k ih =>
    intro l p hp
    rw [picks, List.mem_flatMap] at hp
    obtain ⟨s, hs, hp⟩ := hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hql, hqp⟩ := ih s.2 q hq
    exact ⟨by simp [hql], (hqp.cons s.1).trans (selects_perm l s.1 s.2 hs)⟩

theorem exists_mem_picks : ∀ (b l : List α), l.Nodup → b.Nodup → b ⊆ l →
    ∃ r, (b, r) ∈ picks b.length l := by
  intro b
  induction b with
  | nil => intro l _ _ _; exact ⟨l, by simp [picks]⟩
  | cons a b ih =>
    intro l hl hb hsub
    obtain ⟨r₀, hr₀⟩ := exists_mem_selects l a (hsub (by simp))
    have hperm : (a :: r₀).Perm l := selects_perm l a r₀ hr₀
    have hnd : (a :: r₀).Nodup := hperm.nodup_iff.2 hl
    have hb' : b ⊆ r₀ := by
      intro x hx
      rcases List.mem_cons.1 (hperm.mem_iff.2 (hsub (List.mem_cons_of_mem _ hx))) with h | h
      · exact absurd hx (h ▸ (List.nodup_cons.1 hb).1)
      · exact h
    obtain ⟨r, hr⟩ := ih r₀ (List.nodup_cons.1 hnd).2 (List.nodup_cons.1 hb).2 hb'
    refine ⟨r, ?_⟩
    rw [List.length_cons, picks, List.mem_flatMap]
    exact ⟨(a, r₀), hr₀, List.mem_map.2 ⟨(b, r), hr, rfl⟩⟩

/-! ## Executions -/

/-- Nonempty beads whose concatenation performs each of the `n` directions exactly once. -/
def IsFExec (n : ℕ) (bs : List (List (Fin n))) : Prop :=
  (∀ b ∈ bs, b ≠ []) ∧ bs.flatten.Nodup ∧ bs.flatten.length = n

instance (n : ℕ) (bs : List (List (Fin n))) : Decidable (IsFExec n bs) := by
  unfold IsFExec; infer_instance

/-- An execution of `□n`: a subtype, so equality is decidable. -/
def FExec (n : ℕ) : Type := { bs : List (List (Fin n)) // IsFExec n bs }

instance : DecidableEq (FExec n) :=
  inferInstanceAs (DecidableEq { bs : List (List (Fin n)) // IsFExec n bs })

/-- Nodup and full-length forces a rearrangement of all of `Fin n`. -/
theorem nodup_perm_finRange {l : List (Fin n)} (hnd : l.Nodup) (hlen : l.length = n) :
    l.Perm (List.finRange n) :=
  (hnd.subperm fun x _ => List.mem_finRange x).perm_of_length_le (by simp [hlen])

namespace FExec

/-- The total order in which the run performs the directions. -/
def word (X : FExec n) : List (Fin n) := X.1.flatten

theorem beads_ne_nil (X : FExec n) : ∀ b ∈ X.1, b ≠ [] := X.2.1
theorem word_nodup (X : FExec n) : X.word.Nodup := X.2.2.1
theorem word_length (X : FExec n) : X.word.length = n := X.2.2.2

theorem word_perm (X : FExec n) : X.word.Perm (List.finRange n) :=
  nodup_perm_finRange X.word_nodup X.word_length

theorem mem_word (X : FExec n) (i : Fin n) : i ∈ X.word :=
  X.word_perm.mem_iff.2 (List.mem_finRange i)

/-- The step at which the run performs direction `i`. -/
def posOf (X : FExec n) (i : Fin n) : ℕ := X.word.idxOf i

theorem posOf_lt (X : FExec n) (i : Fin n) : X.posOf i < n := by
  have h := List.idxOf_lt_length_iff.2 (X.mem_word i)
  rwa [X.word_length] at h

def pos (X : FExec n) (i : Fin n) : Fin n := ⟨X.posOf i, X.posOf_lt i⟩

/-- The direction the run performs at step `i`. -/
def letter (X : FExec n) (i : Fin n) : Fin n :=
  X.word[(i : ℕ)]'(by rw [X.word_length]; exact i.isLt)

/-- The run's word read as a permutation of `Fin n`, inverted by `pos`. -/
def perm (X : FExec n) : Equiv.Perm (Fin n) where
  toFun := X.letter
  invFun := X.pos
  left_inv _ := Fin.ext (X.word_nodup.idxOf_getElem _ _)
  right_inv _ := List.getElem_idxOf _

@[simp] theorem perm_apply (X : FExec n) (i : Fin n) : X.perm i = X.letter i := rfl
@[simp] theorem perm_symm_apply (X : FExec n) (i : Fin n) : X.perm.symm i = X.pos i := rfl

/-! ### The refinement order — arrows of `Ch⋆` run coarse ⟶ fine -/

/-- `Y` refines `X`: each bead of `X` splits into consecutive beads of `Y`. -/
def Refines (X Y : FExec n) : Prop := RefinesRel X.1 Y.1

instance (X Y : FExec n) : Decidable (X.Refines Y) :=
  decidable_of_iff _ (refinesB_iff X.1 Y.1 Y.2.1)

@[refl] theorem Refines.refl (X : FExec n) : X.Refines X := RefinesRel.refl X.1

theorem Refines.trans {X Y Z : FExec n} (h₁ : X.Refines Y) (h₂ : Y.Refines Z) : X.Refines Z :=
  RefinesRel.trans h₁ h₂

/-! ### The crossing permutation -/

/-- Where `Y` performs the direction that `X` performs `i`-th. -/
def fperm (X Y : FExec n) : Equiv.Perm (Fin n) := Y.perm⁻¹ * X.perm

theorem fperm_apply (X Y : FExec n) (i : Fin n) : fperm X Y i = Y.pos (X.letter i) := rfl

@[simp] theorem fperm_self (X : FExec n) : fperm X X = 1 := inv_mul_cancel _

/-- The cocycle law over `X ⟶ Y ⟶ Z`. -/
theorem fperm_trans (X Y Z : FExec n) : fperm X Z = fperm Y Z * fperm X Y := by
  simp only [fperm, mul_assoc, mul_inv_cancel_left]

/-- The crossing permutation in one-line notation. -/
def fpermList (X Y : FExec n) : List ℕ :=
  (List.finRange n).map fun i => ((fperm X Y i : Fin n) : ℕ)

end FExec

/-! ## Enumeration -/

/-- Every bead-cell of `bs` lies in `K`, with `done` the directions already performed. -/
def CellsIn (K : SubCube n) : List (Fin n) → List (List (Fin n)) → Prop
  | _, [] => True
  | done, b :: bs => K.mem (beadCell done b) = true ∧ CellsIn K (done ++ b) bs

/-- DFS over (performed, remaining): choose the next bead, keep it if its cell lies in `K`, recurse.
Blocks arrive by increasing size, and `beadCell_isFace` says a rejected block rejects every
superset, so a superset filter may prune here.  The fuel bounds `rem.length`. -/
def go (K : SubCube n) : ℕ → List (Fin n) → List (Fin n) → List (List (List (Fin n)))
  | 0, _, _ => [[]]
  | f + 1, done, rem =>
      if rem = [] then [[]]
      else ((List.range' 1 rem.length).flatMap fun k => picks k rem).flatMap fun p =>
        if K.mem (beadCell done p.1) then (go K f (done ++ p.1) p.2).map (p.1 :: ·) else []

theorem eq_nil_of_flatten_nil {bs : List (List (Fin n))} (hne : ∀ b ∈ bs, b ≠ [])
    (h : bs.flatten = []) : bs = [] := by
  rcases bs with _ | ⟨b, bs⟩
  · rfl
  · exact absurd (List.flatten_eq_nil_iff.1 h b (by simp)) (hne b (by simp))

theorem mem_go_iff (K : SubCube n) : ∀ (f : ℕ) (done rem : List (Fin n))
    (bs : List (List (Fin n))), rem.Nodup → rem.length ≤ f →
    (bs ∈ go K f done rem ↔ (∀ b ∈ bs, b ≠ []) ∧ bs.flatten.Perm rem ∧ CellsIn K done bs) := by
  intro f
  induction f with
  | zero =>
    intro done rem bs hnd hf
    have hrem : rem = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hf)
    subst hrem
    rw [go]
    constructor
    · intro h
      have hb : bs = [] := by simpa using h
      subst hb; exact ⟨by simp, by simp, trivial⟩
    · rintro ⟨hne, hperm, -⟩
      have hb := eq_nil_of_flatten_nil hne (List.perm_nil.1 hperm)
      subst hb; simp
  | succ f ih =>
    intro done rem bs hnd hf
    rw [go]
    by_cases hrem : rem = []
    · subst hrem
      rw [if_pos rfl]
      constructor
      · intro h
        have hb : bs = [] := by simpa using h
        subst hb; exact ⟨by simp, by simp, trivial⟩
      · rintro ⟨hne, hperm, -⟩
        have hb := eq_nil_of_flatten_nil hne (List.perm_nil.1 hperm)
        subst hb; simp
    · rw [if_neg hrem]
      constructor
      · intro h
        rw [List.mem_flatMap] at h
        obtain ⟨p, hp, hbs⟩ := h
        rw [List.mem_flatMap] at hp
        obtain ⟨k, hk, hpk⟩ := hp
        obtain ⟨hplen, hpperm⟩ := picks_spec k rem p hpk
        by_cases hK : K.mem (beadCell done p.1) = true
        · rw [if_pos hK] at hbs
          obtain ⟨bs', hbs', rfl⟩ := List.mem_map.1 hbs
          have hrn : (p.1 ++ p.2).Nodup := hpperm.nodup_iff.2 hnd
          have h2nd : p.2.Nodup := (List.nodup_append.1 hrn).2.1
          have hk1 := List.mem_range'_1.1 hk
          have hlensum : p.1.length + p.2.length = rem.length := by
            simpa using hpperm.length_eq
          have hlen2 : p.2.length ≤ f := by omega
          obtain ⟨hne', hperm', hcells'⟩ :=
            (ih (done ++ p.1) p.2 bs' h2nd hlen2).1 hbs'
          refine ⟨?_, ?_, ⟨hK, hcells'⟩⟩
          · intro b hb
            rcases List.mem_cons.1 hb with rfl | hb
            · intro hcon; rw [hcon] at hplen; simp at hplen; omega
            · exact hne' b hb
          · simpa using (hperm'.append_left p.1).trans hpperm
        · rw [if_neg hK] at hbs; simp at hbs
      · rintro ⟨hne, hperm, hcells⟩
        rcases bs with _ | ⟨b, bs'⟩
        · exact absurd (List.nil_perm.1 (by simpa using hperm)) hrem
        have hb : b ≠ [] := hne b (by simp)
        rw [CellsIn] at hcells
        simp only [List.flatten_cons] at hperm
        have hall : (b ++ bs'.flatten).Nodup := hperm.nodup_iff.2 hnd
        have hbnd : b.Nodup := (List.nodup_append.1 hall).1
        have hbsub : b ⊆ rem := fun x hx => hperm.mem_iff.1 (List.mem_append_left _ hx)
        obtain ⟨r, hr⟩ := exists_mem_picks b rem hnd hbnd hbsub
        obtain ⟨-, hrperm⟩ := picks_spec b.length rem (b, r) hr
        have hbr : bs'.flatten.Perm r :=
          (List.perm_append_left_iff b).1 (hperm.trans hrperm.symm)
        have hrnd : r.Nodup := (List.nodup_append.1 (hrperm.nodup_iff.2 hnd)).2.1
        have hlensum : b.length + r.length = rem.length := by simpa using hrperm.length_eq
        have hbpos : 0 < b.length := by
          cases b with
          | nil => exact absurd rfl hb
          | cons _ _ => simp
        rw [List.mem_flatMap]
        refine ⟨(b, r), ?_, ?_⟩
        · rw [List.mem_flatMap]
          exact ⟨b.length, List.mem_range'_1.2 ⟨hbpos, by omega⟩, hr⟩
        · rw [if_pos hcells.1]
          exact List.mem_map.2 ⟨bs', (ih (done ++ b) r bs' hrnd (by omega)).2
            ⟨fun z hz => hne z (List.mem_cons_of_mem _ hz), hbr, hcells.2⟩, rfl⟩

theorem isFExec_of_mem_go {K : SubCube n} {bs : List (List (Fin n))}
    (h : bs ∈ go K n [] (List.finRange n)) : IsFExec n bs := by
  obtain ⟨hne, hperm, -⟩ :=
    (mem_go_iff K n [] (List.finRange n) bs (List.nodup_finRange n) (by simp)).1 h
  exact ⟨hne, hperm.nodup_iff.2 (List.nodup_finRange n), by rw [hperm.length_eq]; simp⟩

/-- The executions of `K ⊆ □n`, by DFS — output-linear, never a filtered candidate set. -/
def execs (K : SubCube n) : List (FExec n) :=
  (go K n [] (List.finRange n)).pmap (fun bs h => ⟨bs, h⟩) fun _ h => isFExec_of_mem_go h

/-- **`execs K` is exactly the executions all of whose bead-cells lie in `K`.** -/
theorem mem_execs_iff (K : SubCube n) (X : FExec n) : X ∈ execs K ↔ CellsIn K [] X.1 := by
  rw [execs, List.mem_pmap]
  constructor
  · rintro ⟨bs, hbs, rfl⟩
    exact ((mem_go_iff K n [] _ bs (List.nodup_finRange n) (by simp)).1 hbs).2.2
  · intro h
    exact ⟨X.1, (mem_go_iff K n [] _ X.1 (List.nodup_finRange n) (by simp)).2
      ⟨X.2.1, nodup_perm_finRange X.2.2.1 X.2.2.2, h⟩, rfl⟩

/-! ## Distinctness of the enumeration -/

/-- The chosen blocks regrouped by first pick — the shape `List.nodup_flatMap` wants. -/
theorem map_fst_picks_succ (k : ℕ) (l : List α) :
    (picks (k + 1) l).map Prod.fst
      = (selects l).flatMap fun s => ((picks k s.2).map Prod.fst).map (s.1 :: ·) := by
  simp [picks, List.map_flatMap, List.map_map, Function.comp_def]

theorem nodup_map_fst_picks : ∀ (k : ℕ) (l : List α), l.Nodup →
    ((picks k l).map Prod.fst).Nodup := by
  intro k
  induction k with
  | zero => intro l _; simp [picks]
  | succ k ih =>
    intro l hl
    have hpair : List.Pairwise (fun s t : α × List α => s.1 ≠ t.1) (selects l) :=
      List.pairwise_map.1 (by rw [map_fst_selects]; exact hl)
    have hsnd : ∀ s ∈ selects l, s.2.Nodup := fun s hs =>
      (List.nodup_cons.1 ((selects_perm l s.1 s.2 hs).nodup_iff.2 hl)).2
    have hhead : ∀ (s : α × List α) (x : List α),
        x ∈ ((picks k s.2).map Prod.fst).map (s.1 :: ·) → x.head? = some s.1 := by
      intro s x hx
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      rfl
    rw [map_fst_picks_succ]
    refine List.nodup_flatMap.2 ⟨fun s hs => ?_, hpair.imp ?_⟩
    · have hinj : Function.Injective (fun t : List α => s.1 :: t) := fun x y h => by simpa using h
      exact (ih s.2 (hsnd s hs)).map hinj
    · intro s t hst x hx hx'
      exact hst (Option.some.inj ((hhead s x hx).symm.trans (hhead t x hx')))

theorem nodup_map_fst_allPicks (l : List α) (hl : l.Nodup) :
    (((List.range' 1 l.length).flatMap fun k => picks k l).map Prod.fst).Nodup := by
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨fun k _ => nodup_map_fst_picks k l hl, ?_⟩
  refine (List.nodup_range' (s := 1) (n := l.length)).imp ?_
  intro j k hjk x hx hx'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  obtain ⟨v, hv, hvx⟩ := List.mem_map.1 hx'
  have h2 : v.1.length = k := (picks_spec k l v hv).1
  rw [hvx] at h2
  exact hjk ((picks_spec j l u hu).1.symm.trans h2)

theorem nodup_go (K : SubCube n) : ∀ (f : ℕ) (done rem : List (Fin n)), rem.Nodup →
    (go K f done rem).Nodup := by
  intro f
  induction f with
  | zero => intro done rem _; simp [go]
  | succ f ih =>
    intro done rem hnd
    rw [go]
    by_cases hrem : rem = []
    · rw [if_pos hrem]; simp
    rw [if_neg hrem]
    have hhead : ∀ (s : List (Fin n) × List (Fin n)) (y : List (List (Fin n))),
        y ∈ (if K.mem (beadCell done s.1) = true then
          (go K f (done ++ s.1) s.2).map (s.1 :: ·) else []) → y.head? = some s.1 := by
      intro s y hy
      by_cases hK : K.mem (beadCell done s.1) = true
      · rw [if_pos hK] at hy
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
        rfl
      · rw [if_neg hK] at hy; simp at hy
    refine List.nodup_flatMap.2 ⟨fun p hp => ?_, ?_⟩
    · rw [List.mem_flatMap] at hp
      obtain ⟨k, -, hpk⟩ := hp
      have h2 : p.2.Nodup :=
        (List.nodup_append.1 ((picks_spec k rem p hpk).2.nodup_iff.2 hnd)).2.1
      have hinj : Function.Injective (fun t : List (List (Fin n)) => p.1 :: t) :=
        fun x y h => by simpa using h
      split
      · exact (ih (done ++ p.1) p.2 h2).map hinj
      · simp
    · refine (List.pairwise_map.1 (nodup_map_fst_allPicks rem hnd)).imp ?_
      intro p q hpq x hx hx'
      exact hpq (Option.some.inj ((hhead p x hx).symm.trans (hhead q x hx')))

theorem nodup_execs (K : SubCube n) : (execs K).Nodup := by
  rw [execs]
  refine List.Nodup.pmap ?_ (nodup_go K n [] (List.finRange n) (List.nodup_finRange n))
  intro a ha b hb h
  exact congrArg Subtype.val h

/-! ## Indexed views -/

/-- The execution poset as index data: `le[i][j]` says node `i` refines to node `j`. -/
structure Poset (n : ℕ) where
  nodes : Array (FExec n)
  le : Array (Array Bool)

/-- Nodes and the full refinement relation, each computed once. -/
def buildPoset (K : SubCube n) : Poset n :=
  let ns := (execs K).toArray
  let raw := ns.map Subtype.val
  { nodes := ns
    le := raw.map fun bx => raw.map fun by_ => refinesB bx by_ }

/-
Smoke checks (evals live in `Testing/Demo.lean`):

#eval (execs (SubCube.full 2)).length                                  -- 4
#eval (execs (SubCube.full 3)).length                                  -- 24
#eval (execs (SubCube.full 4)).length                                  -- 192
#eval (execs (SubCube.full 5)).length                                  -- 1920 = 5! * 2^4
#eval (execs (SubCube.boundary 3)).length                              -- 18 = 24 - 3!
#eval (execs (SubCube.boundary 4)).length                              -- 168 = 192 - 4!
#eval ((buildPoset (SubCube.full 3)).le.map fun r => r.count true).sum  -- 120 arrows
-/
