import CubeChains.PrecubicalConstructions.Bipointed
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The standard cube `□ⁿ` (ClaudeSetup.md §3, first half)

The standard `N`-cube has, in dimension `k`, the functions `c : Fin N →
Option Bool` with exactly `k` values equal to `none` (`none = ∗`,
`some false = 0`, `some true = 1`).  A face `face ε i` substitutes `some ε` for
the `i`-th `none`, counting `none`-positions in increasing order.

The fiddly content is the precubical identity.  We model the `i`-th `none`
position as `(noneSet c).orderEmbOfFin _ i`, the order embedding of the finset
of `none`-positions.  The key lemma `face_nones` computes the order embedding of
the `none`-set *after* a substitution as `succAbove a ∘ (original embedding)`,
using `Finset.orderEmbOfFin_unique'`.  The precubical identity then reduces to
the commutation of two `Function.update`s at the independent positions
`e i.castSucc` and `e j.succ`, via the `succAbove` computation lemmas.
-/

open CategoryTheory

namespace StdCube

variable {N : ℕ}

/-- The set of `none`-coordinates (the "∗" positions, the free directions) of a
raw cell `c : Fin N → Option Bool`. -/
def noneSet (c : Fin N → Option Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun j => c j = none)

@[simp] theorem mem_noneSet {c : Fin N → Option Bool} {j : Fin N} :
    j ∈ noneSet c ↔ c j = none := by simp [noneSet]

/-- Substituting a non-`none` value at `p` removes `p` from the `none`-set. -/
theorem noneSet_update (c : Fin N → Option Bool) (p : Fin N) (ε : Bool) :
    noneSet (Function.update c p (some ε)) = (noneSet c).erase p := by
  ext j
  rw [mem_noneSet, Finset.mem_erase, mem_noneSet]
  by_cases hj : j = p
  · subst hj; simp
  · rw [Function.update_of_ne hj]; simp [hj]

/-- The `k`-cells of the standard `N`-cube: functions `Fin N → Option Bool` with
exactly `k` free (`none`) coordinates. -/
def cells (N k : ℕ) : Type :=
  { c : Fin N → Option Bool // (noneSet c).card = k }

/-- The order embedding of the `k` `none`-positions of a `k`-cell. -/
def nones {k : ℕ} (c : cells N k) : Fin k ↪o Fin N :=
  (noneSet c.val).orderEmbOfFin c.prop

/-- The `ε`-face at coordinate `i`: substitute `some ε` for the `i`-th `none`. -/
def face (ε : Bool) {k : ℕ} (i : Fin (k + 1)) (c : cells N (k + 1)) : cells N k :=
  ⟨Function.update c.val (nones c i) (some ε), by
    have hmem : nones c i ∈ noneSet c.val := Finset.orderEmbOfFin_mem _ c.prop i
    rw [noneSet_update, Finset.card_erase_of_mem hmem, c.prop, Nat.add_sub_cancel]⟩

@[simp] theorem face_val (ε : Bool) {k : ℕ} (i : Fin (k + 1)) (c : cells N (k + 1)) :
    (face ε i c).val = Function.update c.val (nones c i) (some ε) := rfl

/-- The crux computation: the order embedding of the `none`-set after a face is
the original embedding precomposed with `succAbove`.  Evaluated, the `x`-th
`none` of `face η a c` is the `(a.succAbove x)`-th `none` of `c`. -/
theorem face_nones (η : Bool) {k : ℕ} (c : cells N (k + 2)) (a : Fin (k + 2))
    (x : Fin (k + 1)) : nones (face η a c) x = nones c (a.succAbove x) := by
  have hmem : ∀ y, ((Fin.succAboveOrderEmb a).trans (nones c)) y ∈ noneSet (face η a c).val := by
    intro y
    change ((Fin.succAboveOrderEmb a).trans (nones c)) y
        ∈ noneSet (Function.update c.val (nones c a) (some η))
    rw [noneSet_update, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · simp only [RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
      exact fun h => (Fin.succAbove_ne a y) ((nones c).injective h)
    · simp only [RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply]
      exact Finset.orderEmbOfFin_mem _ c.prop _
  have key : nones (face η a c) = (Fin.succAboveOrderEmb a).trans (nones c) :=
    (Finset.orderEmbOfFin_unique' (face η a c).prop hmem).symm
  rw [key]
  simp [Fin.succAboveOrderEmb_apply]

/-- The precubical identity for the standard cube. -/
theorem face_face (ε η : Bool) {k : ℕ} {i j : Fin (k + 1)} (hij : i ≤ j) (c : cells N (k + 2)) :
    face ε i (face η j.succ c) = face η j (face ε i.castSucc c) := by
  apply Subtype.ext
  change Function.update (Function.update c.val (nones c j.succ) (some η))
        (nones (face η j.succ c) i) (some ε)
      = Function.update (Function.update c.val (nones c i.castSucc) (some ε))
        (nones (face ε i.castSucc c) j) (some η)
  rw [face_nones η c j.succ i, face_nones ε c i.castSucc j,
    Fin.succAbove_succ_of_le j i hij, Fin.succAbove_castSucc_of_le i j hij]
  have hne : nones c j.succ ≠ nones c i.castSucc := by
    refine (nones c).injective.ne ?_
    intro h
    rw [Fin.ext_iff] at h
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    have : i.val ≤ j.val := hij
    omega
  exact Function.update_comm hne (some η) (some ε) c.val

/-- The constant-`some ε` `0`-cell (a vertex). -/
def constVertex (N : ℕ) (ε : Bool) : cells N 0 :=
  ⟨fun _ => some ε, by simp [noneSet]⟩

/-- The standard `N`-cube as a precubical set. -/
def stdPre (N : ℕ) : PrecubicalConstructions where
  cells k := cells N k
  face := fun {_} ε i c => face ε i c
  face_face := by intro n ε η i j hij c; exact face_face ε η hij c

/-- The standard `N`-cube `□ⁿ` as a bi-pointed precubical set: bi-pointed at the
constant-`0` (source) and constant-`1` (target) vertices. -/
def stdCube (N : ℕ) : BPSet where
  toPrecubicalConstructions := stdPre N
  init := constVertex N false
  final := constVertex N true

@[inherit_doc] notation "□^" N => stdCube N

end StdCube
