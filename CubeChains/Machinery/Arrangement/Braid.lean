import CubeChains.Machinery.Arrangement.COM
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Machinery/Arrangement/Braid — the braid arrangement as a COM

The **braid arrangement** `A_{n-1}` as a complex of oriented matroids (in fact an oriented matroid,
`braidCOM_isOM`).  Ground set: the `C(n,2)` pairs `{i < j} ⊆ Fin n`; a height `x : Fin n → ℤ` gives
the covector `braidSign x` with `(braidSign x){i,j} = sign(xᵢ − xⱼ)`, and the covectors are all of
those.  Face symmetry and strong elimination get explicit integer witnesses — `n · height(x)`
dominating `height(y)` for FS, a sign-cancelling combination for SE.

`signAt` spreads a covector antisymmetrically over *all* ordered pairs (how reorientation, `⊙` and
`⊑` are read pair-by-pair downstream); `covectorHeight` is the `[0, n)`-valued inverse of
`braidSign` those witnesses use.
-/

open SignType

namespace CubeChains

/-! ### Sign arithmetic over `ℤ` -/

namespace SignInt

/-- `0 < B ⟹ sign (B * v) = sign v`. -/
theorem sign_pos_mul {B v : ℤ} (hB : 0 < B) : sign (B * v) = sign v := by
  rw [sign_mul, sign_pos hB, one_mul]

/-- Reversing a difference flips its sign. -/
theorem sign_sub_swap (a b : ℤ) : sign (b - a) = - sign (a - b) := by
  rw [show b - a = -(a - b) from by ring, Left.sign_neg]

/-- **Domination.**  A large multiple of `u` dominates a bounded `v`: if `0 < M`, `-M < v < M`
and `u ≠ 0`, then `sign (M * u - v) = sign u`. -/
theorem sign_dom_sub {M u v : ℤ} (hM : 0 < M) (hv1 : v < M) (hv2 : -M < v) (hu : u ≠ 0) :
    sign (M * u - v) = sign u := by
  rcases lt_or_lt_iff_ne.mpr hu with h | h
  · have hu1 : u ≤ -1 := by omega
    have hlt : M * u - v < 0 := by nlinarith [mul_le_mul_of_nonneg_left hu1 hM.le]
    rw [sign_neg hlt, sign_neg h]
  · have hu1 : 1 ≤ u := by omega
    have hgt : 0 < M * u - v := by nlinarith [mul_le_mul_of_nonneg_left hu1 hM.le]
    rw [sign_pos hgt, sign_pos h]

/-- **Sign-cancelling combination is zero** at an opposite-sign pair: if `sign u = -sign v`
then `|v| * u + |u| * v = 0`. -/
theorem abs_combo_zero {u v : ℤ} (h : sign u = -sign v) : |v| * u + |u| * v = 0 := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hv : 0 < v := by
      rcases lt_trichotomy v 0 with hv | hv | hv
      · rw [sign_neg hu, sign_neg hv] at h; exact absurd h (by decide)
      · rw [sign_neg hu, hv, sign_zero] at h; exact absurd h (by decide)
      · exact hv
    rw [abs_of_pos hv, abs_of_neg hu]; ring
  · subst hu; simp
  · have hv : v < 0 := by
      rcases lt_trichotomy v 0 with hv | hv | hv
      · exact hv
      · rw [sign_pos hu, hv, sign_zero] at h; exact absurd h (by decide)
      · rw [sign_pos hu, sign_pos hv] at h; exact absurd h (by decide)
    rw [abs_of_neg hv, abs_of_pos hu]; ring

/-- **Same-side combination.**  If `0 < A`, `0 < B`, `u ≠ 0` and `v` is not strictly opposite in
sign to `u` (`sign u ≠ -sign v`), then `sign (A * u + B * v) = sign u`. -/
theorem sign_same_side {A B u v : ℤ} (hA : 0 < A) (hB : 0 < B) (hu : u ≠ 0)
    (h : sign u ≠ -sign v) : sign (A * u + B * v) = sign u := by
  rcases lt_or_lt_iff_ne.mpr hu with hlt | hlt
  · have hv : v ≤ 0 := by
      by_contra hv
      exact h (by rw [sign_neg hlt, sign_pos (by omega)])
    have : A * u + B * v < 0 := by
      nlinarith [mul_pos hA (show (0:ℤ) < -u by omega), mul_nonneg hB.le (show (0:ℤ) ≤ -v by omega)]
    rw [sign_neg this, sign_neg hlt]
  · have hv : 0 ≤ v := by
      by_contra hv
      exact h (by rw [sign_pos hlt, sign_neg (by omega), neg_neg])
    have : 0 < A * u + B * v := by nlinarith [mul_pos hA hlt, mul_nonneg hB.le hv]
    rw [sign_pos this, sign_pos hlt]

end SignInt

/-- Two integers have the same sign exactly when they agree on both strict comparisons with `0`. -/
theorem sign_eq_sign_iff {p q : ℤ} :
    sign p = sign q ↔ ((p < 0 ↔ q < 0) ∧ (0 < p ↔ 0 < q)) := by
  constructor
  · intro h
    exact ⟨by rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h],
      by rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]⟩
  · rintro ⟨hn, hp⟩
    rcases lt_trichotomy p 0 with h | h | h
    · rw [sign_neg h, sign_neg (hn.mp h)]
    · have hq : q = 0 := by
        rcases lt_trichotomy q 0 with h' | h' | h'
        · exact absurd (hn.mpr h') (by omega)
        · exact h'
        · exact absurd (hp.mpr h') (by omega)
      rw [h, hq]
    · rw [sign_pos h, sign_pos (hp.mp h)]

/-- Raising an *attained* threshold strictly raises the strictly-below count. -/
theorem card_filter_lt_mono {α : Type*} {S : Finset α} {f : α → ℤ} {a b : ℤ} {w : α}
    [DecidablePred fun p => f p < a] [DecidablePred fun p => f p < b]
    (hw : w ∈ S) (hfw : f w = a) (hab : a < b) :
    (S.filter fun p => f p < a).card < (S.filter fun p => f p < b).card :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset (fun p hp => by
      rw [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.trans hab⟩)).mpr
    ⟨w, Finset.mem_filter.mpr ⟨hw, hfw ▸ hab⟩, fun hc =>
      absurd (Finset.mem_filter.mp hc).2 (by rw [hfw]; exact lt_irrefl a)⟩)

/-! ### Ground set and the sign-vector map -/

/-- The **ground set** of the braid arrangement `A_{n-1}`: the ordered pairs `{i < j} ⊆ Fin n`. -/
def BraidGround (n : ℕ) : Type := { p : Fin n × Fin n // p.1 < p.2 }

/-- The covector of a height function `x : Fin n → ℤ`: `(braidSign x){i,j} = sign(xᵢ − xⱼ)`. -/
def braidSign {n : ℕ} (x : Fin n → ℤ) : SignVec (BraidGround n) :=
  fun e => sign (x e.1.1 - x e.1.2)

@[simp] theorem braidSign_apply {n : ℕ} (x : Fin n → ℤ) (e : BraidGround n) :
    braidSign x e = sign (x e.1.1 - x e.1.2) := rfl

/-- A function order-matching `x` (strict values ↦ strict, ties ↦ ties) realises `x`'s covector. -/
theorem braidSign_eq_of_mono {n : ℕ} {x H : Fin n → ℤ} (hlt : ∀ i j, x i < x j → H i < H j)
    (heq : ∀ i j, x i = x j → H i = H j) : braidSign H = braidSign x := by
  funext e
  simp only [braidSign_apply]
  rcases lt_trichotomy (x e.1.1) (x e.1.2) with h | h | h
  · rw [sign_neg (show H e.1.1 - H e.1.2 < 0 by have := hlt _ _ h; omega), sign_neg (by omega)]
  · rw [heq _ _ h, sub_self, show x e.1.1 - x e.1.2 = 0 from by omega]
  · rw [sign_pos (show 0 < H e.1.1 - H e.1.2 by have := hlt _ _ h; omega), sign_pos (by omega)]

/-- Difference of a two-term linear combination witness (`SE`). -/
theorem braidSign_lincomb {n : ℕ} (A B : ℤ) (x y : Fin n → ℤ) (e : BraidGround n) :
    braidSign (fun i => A * x i + B * y i) e
      = sign (A * (x e.1.1 - x e.1.2) + B * (y e.1.1 - y e.1.2)) := by
  rw [braidSign_apply]; congr 1; ring

/-! ### The antisymmetric extension to all ordered pairs

A covector is indexed only by the pairs `{i < j}`; `signAt` spreads it antisymmetrically over
*every* ordered pair, and `signAt_ext` is the recursor that identifies it: an antisymmetric
function of ordered pairs agreeing with `V` on the ground set *is* `signAt V`. -/

section Extension
variable {n : ℕ}

/-- Antisymmetric extension: `V{p,q}` for `p<q`, `-V{q,p}` for `q<p`, `0` on the diagonal. -/
def signAt (V : SignVec (BraidGround n)) (p q : Fin n) : SignType :=
  if h : p < q then V ⟨(p, q), h⟩
  else if h' : q < p then - V ⟨(q, p), h'⟩
  else 0

theorem signAt_lt (V : SignVec (BraidGround n)) {p q : Fin n} (h : p < q) :
    signAt V p q = V ⟨(p, q), h⟩ := by
  unfold signAt; rw [dif_pos h]

theorem signAt_gt (V : SignVec (BraidGround n)) {p q : Fin n} (h : q < p) :
    signAt V p q = - V ⟨(q, p), h⟩ := by
  unfold signAt; rw [dif_neg (not_lt.mpr h.le), dif_pos h]

theorem signAt_self (V : SignVec (BraidGround n)) (p : Fin n) : signAt V p p = 0 := by
  unfold signAt; rw [dif_neg (lt_irrefl p), dif_neg (lt_irrefl p)]

/-- `signAt` is antisymmetric in its two indices. -/
theorem signAt_antisymm (V : SignVec (BraidGround n)) (p q : Fin n) :
    signAt V q p = - signAt V p q := by
  rcases lt_trichotomy p q with h | rfl | h
  · rw [signAt_gt V h, signAt_lt V h]
  · rw [signAt_self, neg_zero]
  · rw [signAt_lt V h, signAt_gt V h, neg_neg]

/-- On an actual ground element (where `i<j`) the extension returns the coordinate itself. -/
theorem signAt_of_pair (V : SignVec (BraidGround n)) (e : BraidGround n) :
    signAt V e.1.1 e.1.2 = V e := by
  rw [signAt_lt V e.2]; congr 1

/-- **Extension recursor.**  An antisymmetric function of ordered pairs agreeing with `V` on the
ground set is `signAt V`; the diagonal is forced because `a = -a` only for `a = 0`. -/
theorem signAt_ext {V : SignVec (BraidGround n)} {G : Fin n → Fin n → SignType}
    (hG : ∀ p q, G q p = -G p q) (hgr : ∀ e : BraidGround n, G e.1.1 e.1.2 = V e) (p q : Fin n) :
    signAt V p q = G p q := by
  have hdiag : ∀ a : SignType, a = -a → a = 0 := by decide
  rcases lt_trichotomy p q with h | rfl | h
  · rw [signAt_lt V h, ← hgr ⟨(p, q), h⟩]
  · rw [signAt_self, hdiag _ (hG p p)]
  · rw [signAt_gt V h, ← hgr ⟨(q, p), h⟩, hG q p]

/-- The extension of a realised covector is the sign of the height difference. -/
theorem signAt_braidSign (x : Fin n → ℤ) (p q : Fin n) :
    signAt (braidSign x) p q = sign (x p - x q) :=
  signAt_ext (G := fun p q => sign (x p - x q))
    (fun p q => SignInt.sign_sub_swap (x p) (x q)) (fun _ => rfl) p q

/-- The ground pair of two distinct coordinates, in whichever order they come. -/
theorem exists_ground {p q : Fin n} (h : p ≠ q) :
    ∃ e : BraidGround n, (e.1.1 = p ∧ e.1.2 = q) ∨ (e.1.1 = q ∧ e.1.2 = p) := by
  rcases lt_or_gt_of_ne h with hc | hc
  · exact ⟨⟨(p, q), hc⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨(q, p), hc⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- The antisymmetric extension of a composite is the composite of the extensions. -/
theorem signAt_comp (X T : SignVec (BraidGround n)) (p q : Fin n) :
    signAt (X ⊙ T) p q = if signAt X p q = 0 then signAt T p q else signAt X p q := by
  have key : ∀ a b c d : SignType, a = -c → b = -d →
      (if a = 0 then b else a) = -(if c = 0 then d else c) := by decide
  exact signAt_ext (G := fun p q => if signAt X p q = 0 then signAt T p q else signAt X p q)
    (fun p q => key _ _ _ _ (signAt_antisymm X p q) (signAt_antisymm T p q))
    (fun e => by simp only [signAt_of_pair]; rfl) p q

/-- The face order is the coordinatewise disjunction at *every* ordered pair, not just the ground
ones: `X ⊑ Y` iff `X` is absorbed by `Y` under `⊙`, which `signAt` transports. -/
theorem faceLE_iff_signAt {X Y : SignVec (BraidGround n)} :
    X ⊑ Y ↔ ∀ p q, signAt X p q = 0 ∨ signAt X p q = signAt Y p q := by
  refine ⟨fun h p q => ?_, fun h e => by simpa only [signAt_of_pair] using h e.1.1 e.1.2⟩
  have hc := signAt_comp X Y p q
  rw [SignVec.comp_eq_right_of_faceLE h] at hc
  by_cases h0 : signAt X p q = 0
  · exact Or.inl h0
  · exact Or.inr (by rw [if_neg h0] at hc; exact hc.symm)

end Extension

/-! ### The canonical height of a covector

A covector `Y` names, for every ordered pair, whether `p` ranks below `q` (`covectorBelow`, read off
the sign at that pair).  Counting the predecessors gives a **computable** height `covectorHeight`
realising `Y` — the `Classical.choice`-free inverse to `braidSign`, bounded into `[0, n)` because no
coordinate precedes itself, which is also what makes it the face-symmetry witness. -/

section Height
variable {n : ℕ}

/-- `p` ranks strictly below `q` in the covector `Y`, read off the sign of the ordered pair. -/
def covectorBelow (Y : SignVec (BraidGround n)) (p q : Fin n) : Bool := decide (signAt Y p q = -1)

/-- The **canonical height** realising `Y`: `q ↦ #{p : p ranks below q}`. -/
def covectorHeight (Y : SignVec (BraidGround n)) (q : Fin n) : ℤ :=
  ((Finset.univ.filter (fun p => covectorBelow Y p q = true)).card : ℤ)

/-- No coordinate ranks below itself. -/
@[simp] theorem covectorBelow_self (Y : SignVec (BraidGround n)) (p : Fin n) :
    covectorBelow Y p p = false := by
  simp [covectorBelow, signAt_self]

theorem covectorHeight_nonneg (Y : SignVec (BraidGround n)) (q : Fin n) :
    0 ≤ covectorHeight Y q := Int.natCast_nonneg _

/-- The height is bounded by `n`: `q` is never its own predecessor, so one coordinate is missed. -/
theorem covectorHeight_lt (Y : SignVec (BraidGround n)) (q : Fin n) : covectorHeight Y q < n := by
  have hq : q ∉ Finset.univ.filter (fun p => covectorBelow Y p q = true) := by
    simp [covectorBelow_self]
  have hcard : (Finset.univ.filter (fun p => covectorBelow Y p q = true)).card < n :=
    calc (Finset.univ.filter (fun p => covectorBelow Y p q = true)).card
        ≤ (Finset.univ.erase q).card :=
          Finset.card_le_card fun p hp =>
            Finset.mem_erase.mpr ⟨fun h => hq (h ▸ hp), Finset.mem_univ p⟩
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, Fintype.card_fin]
      _ < n := Nat.sub_lt (Fin.pos q) one_pos
  rw [covectorHeight]
  exact_mod_cast hcard

/-- On a realised covector, `covectorBelow` is exactly the height order. -/
theorem covectorBelow_braidSign (x : Fin n → ℤ) (p q : Fin n) :
    covectorBelow (braidSign x) p q = decide (x p < x q) := by
  simp only [covectorBelow, signAt_braidSign, sign_eq_neg_one_iff, sub_neg]

/-- `covectorHeight` of a realised covector counts the coordinates strictly below. -/
theorem covectorHeight_braidSign (x : Fin n → ℤ) (q : Fin n) :
    covectorHeight (braidSign x) q = ((Finset.univ.filter (fun p => x p < x q)).card : ℤ) := by
  rw [covectorHeight]
  refine congrArg (fun s : Finset (Fin n) => (s.card : ℤ)) ?_
  ext p
  simp [Finset.mem_filter, covectorBelow_braidSign]

/-- The strict-below count is strictly monotone in the threshold value. -/
theorem covectorHeight_strictMono (x : Fin n → ℤ) {i j : Fin n} (hij : x i < x j) :
    covectorHeight (braidSign x) i < covectorHeight (braidSign x) j := by
  rw [covectorHeight_braidSign, covectorHeight_braidSign]
  exact_mod_cast card_filter_lt_mono (f := x) (Finset.mem_univ i) rfl hij

/-- **The realization.**  The canonical height of a covector realises it — the strict-below count
order-matches `x`. -/
theorem braidSign_covectorHeight (x : Fin n → ℤ) :
    braidSign (covectorHeight (braidSign x)) = braidSign x :=
  braidSign_eq_of_mono (fun _ _ h => covectorHeight_strictMono x h)
    (fun _ _ h => by rw [covectorHeight_braidSign, covectorHeight_braidSign, h])

/-- `covectorHeight` realises any covector of the arrangement. -/
theorem braidSign_covectorHeight_mem {Y : SignVec (BraidGround n)}
    (h : Y ∈ Set.range braidSign) : braidSign (covectorHeight Y) = Y := by
  obtain ⟨x, rfl⟩ := h
  exact braidSign_covectorHeight x

/-- Difference of the `FS` witness `i ↦ n · height(x)ᵢ − height(y)ᵢ`. -/
theorem braidSign_fsWitness (x y : Fin n → ℤ) (e : BraidGround n) :
    braidSign (fun i => (n : ℤ) * covectorHeight (braidSign x) i
        - covectorHeight (braidSign y) i) e
      = sign ((n : ℤ) * (covectorHeight (braidSign x) e.1.1 - covectorHeight (braidSign x) e.1.2)
          - (covectorHeight (braidSign y) e.1.1 - covectorHeight (braidSign y) e.1.2)) := by
  rw [braidSign_apply]; congr 1; ring

end Height

/-! ### The braid COM -/

/-- The covectors of the braid arrangement: all sign vectors of height functions. -/
def braidCovectors (n : ℕ) : Set (SignVec (BraidGround n)) := Set.range (braidSign (n := n))

/-- **The braid arrangement `A_{n-1}` as a COM** (in fact an oriented matroid): covectors are the
sign vectors of height functions `Fin n → ℤ`, closed under face symmetry and strong elimination. -/
def braidCOM (n : ℕ) : COM (BraidGround n) where
  covectors := braidCovectors n
  carrier_nonempty := ⟨braidSign 0, 0, rfl⟩
  faceSymm := by
    rintro X ⟨x, rfl⟩ Y ⟨y, rfl⟩
    refine ⟨fun i => (n : ℤ) * covectorHeight (braidSign x) i
      - covectorHeight (braidSign y) i, ?_⟩
    funext e
    have hn : (0 : ℤ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le e.1.1.val) e.1.1.isLt
    have hX : braidSign x e
        = sign (covectorHeight (braidSign x) e.1.1 - covectorHeight (braidSign x) e.1.2) :=
      (congrFun (braidSign_covectorHeight x) e).symm
    have hY : braidSign y e
        = sign (covectorHeight (braidSign y) e.1.1 - covectorHeight (braidSign y) e.1.2) :=
      (congrFun (braidSign_covectorHeight y) e).symm
    have hylt := covectorHeight_lt (braidSign y) e.1.1
    have hygt := covectorHeight_nonneg (braidSign y) e.1.2
    have hylt' := covectorHeight_lt (braidSign y) e.1.2
    have hygt' := covectorHeight_nonneg (braidSign y) e.1.1
    have hcomp : (braidSign x ⊙ (-braidSign y)) e
        = if braidSign x e = 0 then -(braidSign y e) else braidSign x e := rfl
    rw [braidSign_fsWitness, hcomp]
    by_cases hu : covectorHeight (braidSign x) e.1.1 - covectorHeight (braidSign x) e.1.2 = 0
    · rw [if_pos (show braidSign x e = 0 by rw [hX, hu, sign_zero]), hu, mul_zero, zero_sub,
        Left.sign_neg, hY]
    · rw [if_neg (show ¬ braidSign x e = 0 by rw [hX]; exact sign_ne_zero.mpr hu), hX,
        SignInt.sign_dom_sub hn (by omega) (by omega) hu]
  strongElim := by
    rintro X ⟨x, rfl⟩ Y ⟨y, rfl⟩ e he
    have hopp : sign (x e.1.1 - x e.1.2) = -sign (y e.1.1 - y e.1.2) := he.1
    have hune : x e.1.1 - x e.1.2 ≠ 0 := fun h0 => he.2 (by rw [braidSign_apply, h0, sign_zero])
    have hvne : y e.1.1 - y e.1.2 ≠ 0 := by
      intro h0; rw [h0, sign_zero, neg_zero] at hopp; exact hune (sign_eq_zero_iff.mp hopp)
    have hApos : 0 < |y e.1.1 - y e.1.2| := abs_pos.mpr hvne
    have hBpos : 0 < |x e.1.1 - x e.1.2| := abs_pos.mpr hune
    refine ⟨braidSign (fun i => |y e.1.1 - y e.1.2| * x i + |x e.1.1 - x e.1.2| * y i),
      ⟨_, rfl⟩, ?_, ?_⟩
    · rw [braidSign_lincomb, SignInt.abs_combo_zero hopp, sign_zero]
    · intro f hf
      rw [braidSign_lincomb]
      have hcomp : (braidSign x ⊙ braidSign y) f
          = if braidSign x f = 0 then braidSign y f else braidSign x f := rfl
      rw [hcomp]
      by_cases huf : x f.1.1 - x f.1.2 = 0
      · rw [if_pos (show braidSign x f = 0 by rw [braidSign_apply, huf, sign_zero]),
          huf, mul_zero, zero_add, SignInt.sign_pos_mul hBpos, braidSign_apply]
      · rw [if_neg (show ¬ braidSign x f = 0 by rw [braidSign_apply]; exact sign_ne_zero.mpr huf),
          braidSign_apply]
        refine SignInt.sign_same_side hApos hBpos huf (fun hcon => hf ⟨?_, ?_⟩)
        · rw [braidSign_apply, braidSign_apply]; exact hcon
        · rw [braidSign_apply]; exact sign_ne_zero.mpr huf

/-- The braid arrangement is an oriented matroid: it contains the zero covector. -/
theorem braidCOM_isOM (n : ℕ) : (braidCOM n).IsOM :=
  ⟨0, by funext e; simp [braidSign_apply]⟩

end CubeChains
