import CubeChains.Braid.Jux
import CubeChains.Braid.Grading

/-!
# Braid/JuxAssoc — juxtaposition is associative and unital

The coherence the delooping needs: juxtaposing three braids is associative up to the strand-count
recast `(n+m)+k = n+(m+k)`, and the empty braid is a two-sided unit.

Everything reduces to `blockPerm_assoc` on the generators `ofPerm σ`, assembled through the three
block-slide lemmas (`juxL_juxL`, `juxL_juxR`, `juxR_juxR`) — a strand never leaves its block, so the
two bracketings move no strand.
-/

namespace CubeChains

open Equiv

variable {n m k : ℕ}

/-! ## `braidCast` as a homomorphism -/

theorem braidCast_mul {n m : ℕ} (h : n = m) (a b : Braid n) :
    braidCast h (a * b) = braidCast h a * braidCast h b := by
  subst h; rfl

/-- Recasting a braid along an equality of strand counts, as a group homomorphism. -/
def braidCastHom (h : n = m) : Braid n →* Braid m where
  toFun := braidCast h
  map_one' := by subst h; rfl
  map_mul' := braidCast_mul h

@[simp] theorem braidCastHom_apply (h : n = m) (x : Braid n) :
    braidCastHom h x = braidCast h x := rfl

@[simp] theorem braidCastHom_ofPerm (h : n = m) (σ : Perm (Fin n)) :
    braidCastHom h (ofPerm σ) = ofPerm ((finCongr h).permCongr σ) :=
  braidCast_ofPerm h σ

/-- Two homomorphisms out of `Braid n` agreeing on the simple braids are equal. -/
theorem braidHom_ext {P : Type*} [Group P] {F G : Braid n →* P}
    (h : ∀ σ : Perm (Fin n), F (ofPerm σ) = G (ofPerm σ)) : F = G := by
  let H : Subgroup (Braid n) :=
    { carrier := {y | F y = G y}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      inv_mem' := by intro a ha; simp only [Set.mem_setOf_eq, map_inv] at *; rw [ha] }
  refine MonoidHom.ext (fun x => ?_)
  exact braid_mem_of_gens (H := H) (fun σ => h σ) x

/-! ## The three block-slides

Each lands in `Braid (n + (m + k))` and says: the block-`n`/`m`/`k` events, embedded via the left
bracketing then recast, sit exactly where the right bracketing puts them. -/

/-- The `n`-block slides straight through. -/
theorem juxL_juxL (n m k : ℕ) :
    (braidCastHom (Nat.add_assoc n m k)).comp ((juxL (n + m) k).comp (juxL n m))
      = juxL n (m + k) := by
  refine braidHom_ext (fun σ => ?_)
  simp only [MonoidHom.comp_apply, juxL_ofPerm, braidCastHom_ofPerm]
  rw [show ((finCongr (Nat.add_assoc n m k)).permCongr (blockPerm (blockPerm σ 1) 1))
      = blockPerm σ (blockPerm (1 : Perm (Fin m)) (1 : Perm (Fin k))) from blockPerm_assoc σ 1 1,
    blockPerm_one]

/-- The `m`-block slides into the right factor's first block. -/
theorem juxL_juxR (n m k : ℕ) :
    (braidCastHom (Nat.add_assoc n m k)).comp ((juxL (n + m) k).comp (juxR n m))
      = (juxR n (m + k)).comp (juxL m k) := by
  refine braidHom_ext (fun τ => ?_)
  simp only [MonoidHom.comp_apply, juxL_ofPerm, juxR_ofPerm, braidCastHom_ofPerm]
  rw [show ((finCongr (Nat.add_assoc n m k)).permCongr (blockPerm (blockPerm 1 τ) 1))
      = blockPerm (1 : Perm (Fin n)) (blockPerm τ 1) from blockPerm_assoc 1 τ 1]

/-- The `k`-block slides into the right factor's second block. -/
theorem juxR_juxR (n m k : ℕ) :
    (braidCastHom (Nat.add_assoc n m k)).comp (juxR (n + m) k)
      = (juxR n (m + k)).comp (juxR m k) := by
  refine braidHom_ext (fun ρ => ?_)
  simp only [MonoidHom.comp_apply, juxR_ofPerm, braidCastHom_ofPerm]
  rw [show (blockPerm (1 : Perm (Fin (n + m))) ρ)
      = blockPerm (blockPerm (1 : Perm (Fin n)) (1 : Perm (Fin m))) ρ by rw [blockPerm_one],
    show ((finCongr (Nat.add_assoc n m k)).permCongr (blockPerm (blockPerm 1 1) ρ))
      = blockPerm (1 : Perm (Fin n)) (blockPerm 1 ρ) from blockPerm_assoc 1 1 ρ]

/-! ## Associativity and unitality of `juxHom` -/

/-- **Juxtaposition is associative**, across the `(n+m)+k = n+(m+k)` recast. -/
theorem juxHom_assoc (a : Braid n) (b : Braid m) (c : Braid k) :
    braidCast (Nat.add_assoc n m k) (juxHom (n + m) k (juxHom n m (a, b), c))
      = juxHom n (m + k) (a, juxHom m k (b, c)) := by
  have hL := DFunLike.congr_fun (juxL_juxL n m k) a
  have hM := DFunLike.congr_fun (juxL_juxR n m k) b
  have hR := DFunLike.congr_fun (juxR_juxR n m k) c
  simp only [MonoidHom.coe_comp, Function.comp_apply, braidCastHom_apply] at hL hM hR
  simp only [juxHom_eq, map_mul, braidCast_mul, hL, hM, hR, mul_assoc]

/-- The right block of width `0` is empty: `blockPerm σ 1₀ = σ` (over the definitional `n + 0 = n`). -/
theorem blockPerm_one_right (σ : Perm (Fin n)) :
    blockPerm σ (1 : Perm (Fin 0)) = σ := by
  refine Equiv.ext (fun i => ?_)
  exact blockPerm_castAdd σ (1 : Perm (Fin 0)) i

/-- **Right unit**: `n + 0 = n` is definitional, so the empty braid on the right does nothing. -/
theorem juxL_zero (a : Braid n) : juxL n 0 a = a := by
  have h : juxL n 0 = MonoidHom.id (Braid n) :=
    braidHom_ext (fun σ => by rw [juxL_ofPerm, blockPerm_one_right, MonoidHom.id_apply])
  rw [h, MonoidHom.id_apply]

@[simp] theorem juxHom_zero_right (a : Braid n) :
    juxHom n 0 (a, (1 : Braid 0)) = a := by
  rw [juxHom_one_right, juxL_zero]

/-- **Left unit**, across the `0 + n = n` recast. -/
theorem juxR_zero (b : Braid n) : juxR 0 n b = braidCast (Nat.zero_add n).symm b := by
  refine DFunLike.congr_fun (braidHom_ext (F := juxR 0 n)
    (G := braidCastHom (Nat.zero_add n).symm) (fun σ => ?_)) b
  rw [juxR_ofPerm, braidCastHom_ofPerm]
  congr 1
  refine Equiv.ext (fun i => Fin.ext ?_)
  rw [blockPerm_val_ge (1 : Perm (Fin 0)) σ i ⟨(i : ℕ),
    i.isLt.trans_eq (Nat.zero_add n)⟩ (by simp)]
  simp only [Nat.zero_add, Equiv.permCongr_apply, finCongr_symm, finCongr_apply, Fin.coe_cast]
  exact congrArg (fun j => ((σ j : Fin n) : ℕ)) (Fin.ext rfl)

@[simp] theorem juxHom_zero_left (b : Braid n) :
    juxHom 0 n ((1 : Braid 0), b) = braidCast (Nat.zero_add n).symm b := by
  rw [juxHom_one_left, juxR_zero]

end CubeChains
