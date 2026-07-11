import CubeChains.Arrangements.COM
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arrangements/Braid — the braid arrangement as a COM

The **braid arrangement** `A_{n-1}` assembled as a complex of oriented matroids (in fact an
oriented matroid).  The ground set is the `C(n,2)` ordered pairs `{i < j} ⊆ Fin n`; a height
function `x : Fin n → ℤ` gives the covector `braidSign x` with `(braidSign x){i,j} =
sign(xᵢ − xⱼ)`, and the covectors are all such sign vectors.  Closure under face symmetry (FS)
and strong elimination (SE) is proved by explicit integer witnesses — dense-rank scaling
(`n · rank(x)` dominates `rank(y)`) for FS, a sign-cancelling combination for SE — so
`braidCOM n : COM (BraidGround n)` is an oriented matroid (`braidCOM_isOM`).

-/

open SignType

namespace FinalBraid

/-! ### Sign arithmetic over `ℤ` -/

namespace SignInt

/-- `0 < B ⟹ sign (B * v) = sign v`. -/
theorem sign_pos_mul {B v : ℤ} (hB : 0 < B) : sign (B * v) = sign v := by
  rw [sign_mul, sign_pos hB, one_mul]

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

/-! ### Ground set and the sign-vector map -/

/-- The **ground set** of the braid arrangement `A_{n-1}`: the ordered pairs `{i < j} ⊆ Fin n`. -/
def BraidGround (n : ℕ) : Type := { p : Fin n × Fin n // p.1 < p.2 }

/-- The covector of a height function `x : Fin n → ℤ`: `(braidSign x){i,j} = sign(xᵢ − xⱼ)`. -/
def braidSign {n : ℕ} (x : Fin n → ℤ) : SignVec (BraidGround n) :=
  fun e => sign (x e.1.1 - x e.1.2)

@[simp] theorem braidSign_apply {n : ℕ} (x : Fin n → ℤ) (e : BraidGround n) :
    braidSign x e = sign (x e.1.1 - x e.1.2) := rfl

/-- Difference of a two-term linear combination witness (`SE`). -/
theorem braidSign_lincomb {n : ℕ} (A B : ℤ) (x y : Fin n → ℤ) (e : BraidGround n) :
    braidSign (fun i => A * x i + B * y i) e
      = sign (A * (x e.1.1 - x e.1.2) + B * (y e.1.1 - y e.1.2)) := by
  rw [braidSign_apply]; congr 1; ring

/-! ### Dense rank: a bounded integer realisation of any height function -/

/-- The **dense rank** of `x` at `i`: the number of distinct values of `x` strictly below `xᵢ`. -/
def denseRank {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : ℤ :=
  ((Finset.univ.image x).filter (· < x i)).card

theorem denseRank_nonneg {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : 0 ≤ denseRank x i :=
  Int.natCast_nonneg _

theorem denseRank_lt {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : denseRank x i < n := by
  have hsub : (Finset.univ.image x).filter (· < x i) ⊂ Finset.univ.image x :=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
      ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i),
        fun hc => lt_irrefl (x i) (Finset.mem_filter.mp hc).2⟩
  have h2 : (Finset.univ.image x).card ≤ n := by
    calc (Finset.univ.image x).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have h1 : ((Finset.univ.image x).filter (· < x i)).card < n := by
    have := Finset.card_lt_card hsub; omega
  calc denseRank x i = (((Finset.univ.image x).filter (· < x i)).card : ℤ) := rfl
    _ < (n : ℤ) := by exact_mod_cast h1

theorem denseRank_strictMono {n : ℕ} (x : Fin n → ℤ) {i j : Fin n} (h : x i < x j) :
    denseRank x i < denseRank x j := by
  have hss : (Finset.univ.image x).filter (· < x i) ⊆ (Finset.univ.image x).filter (· < x j) := by
    intro a ha; rw [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, lt_trans ha.2 h⟩
  have hsub : (Finset.univ.image x).filter (· < x i) ⊂ (Finset.univ.image x).filter (· < x j) :=
    (Finset.ssubset_iff_of_subset hss).mpr
      ⟨x i, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem x (Finset.mem_univ i), h⟩,
        fun hc => lt_irrefl (x i) (Finset.mem_filter.mp hc).2⟩
  have hlt := Finset.card_lt_card hsub
  calc denseRank x i = (((Finset.univ.image x).filter (· < x i)).card : ℤ) := rfl
    _ < (((Finset.univ.image x).filter (· < x j)).card : ℤ) := by exact_mod_cast hlt
    _ = denseRank x j := rfl

/-- Dense rank realises the same covector: `braidSign (denseRank x) = braidSign x`. -/
theorem braidSign_denseRank {n : ℕ} (x : Fin n → ℤ) : braidSign (denseRank x) = braidSign x := by
  funext e
  simp only [braidSign_apply]
  rcases lt_trichotomy (x e.1.1) (x e.1.2) with h | h | h
  · have h1 : x e.1.1 - x e.1.2 < 0 := by omega
    have h2 : denseRank x e.1.1 - denseRank x e.1.2 < 0 := by
      have := denseRank_strictMono x h; omega
    rw [sign_neg h1, sign_neg h2]
  · have hd : denseRank x e.1.1 = denseRank x e.1.2 := by simp only [denseRank, h]
    rw [hd, sub_self, show x e.1.1 - x e.1.2 = 0 from by omega]
  · have h1 : 0 < x e.1.1 - x e.1.2 := by omega
    have h2 : 0 < denseRank x e.1.1 - denseRank x e.1.2 := by
      have := denseRank_strictMono x h; omega
    rw [sign_pos h1, sign_pos h2]

theorem denseRank_diff_lt {n : ℕ} (x : Fin n → ℤ) (i j : Fin n) :
    denseRank x i - denseRank x j < n := by
  have h1 := denseRank_lt x i; have h2 := denseRank_nonneg x j; omega

theorem denseRank_diff_gt {n : ℕ} (x : Fin n → ℤ) (i j : Fin n) :
    -(n : ℤ) < denseRank x i - denseRank x j := by
  have h1 := denseRank_lt x j; have h2 := denseRank_nonneg x i; omega

/-- Difference of the `FS` witness `i ↦ n · rank(x)ᵢ − rank(y)ᵢ`. -/
theorem braidSign_fsWitness {n : ℕ} (x y : Fin n → ℤ) (e : BraidGround n) :
    braidSign (fun i => (n : ℤ) * denseRank x i - denseRank y i) e
      = sign ((n : ℤ) * (denseRank x e.1.1 - denseRank x e.1.2)
          - (denseRank y e.1.1 - denseRank y e.1.2)) := by
  rw [braidSign_apply]; congr 1; ring

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
    refine ⟨fun i => (n : ℤ) * denseRank x i - denseRank y i, ?_⟩
    funext e
    have hn : (0 : ℤ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le e.1.1.val) e.1.1.isLt
    have hX : braidSign x e = sign (denseRank x e.1.1 - denseRank x e.1.2) :=
      (congrFun (braidSign_denseRank x) e).symm
    have hY : braidSign y e = sign (denseRank y e.1.1 - denseRank y e.1.2) :=
      (congrFun (braidSign_denseRank y) e).symm
    have hcomp : SignVec.comp (braidSign x) (-braidSign y) e
        = if braidSign x e = 0 then -(braidSign y e) else braidSign x e := rfl
    rw [braidSign_fsWitness, hcomp]
    by_cases hu : denseRank x e.1.1 - denseRank x e.1.2 = 0
    · rw [if_pos (show braidSign x e = 0 by rw [hX, hu, sign_zero]), hu, mul_zero, zero_sub,
        Left.sign_neg, hY]
    · rw [if_neg (show ¬ braidSign x e = 0 by rw [hX]; exact sign_ne_zero.mpr hu), hX,
        SignInt.sign_dom_sub hn (denseRank_diff_lt y e.1.1 e.1.2)
          (denseRank_diff_gt y e.1.1 e.1.2) hu]
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
      have hcomp : SignVec.comp (braidSign x) (braidSign y) f
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

end FinalBraid
