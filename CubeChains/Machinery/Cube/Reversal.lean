import CubeChains.Machinery.Cube.BoxMonoidal

/-!
# Machinery/Cube/Reversal — running a cube backwards

`flipCell` reverses a sign vector: `0 ↔ 1`, with `∗` fixed.  It commutes with substitution
(`flipCell_subst`), because substitution only *moves* entries — and that single fact makes it a
functor `Box.rev`, an involution on every hom-set.

Reversal is the complement's engine: on a bead cut into `k` pieces it acts by the longest element
of `Sₖ`, so it turns the merge out of a run into the greatest crossing onto the same chain.
-/

open CategoryTheory

namespace StdCube

variable {N n k : ℕ}

/-- Flip every fixed sign of a raw sign vector; the free coordinates stay free. -/
def flipFun (c : Fin N → Option Bool) : Fin N → Option Bool := fun j => (c j).map not

@[simp] theorem flipFun_flipFun (c : Fin N → Option Bool) : flipFun (flipFun c) = c := by
  funext j; cases h : c j <;> simp [flipFun, h]

@[simp] theorem noneSet_flipFun (c : Fin N → Option Bool) : noneSet (flipFun c) = noneSet c := by
  ext j; cases h : c j <;> simp [mem_noneSet, flipFun, h]

/-- **The reversal of a sign vector**: `0 ↔ 1`, `∗` fixed. -/
def flipCell (c : Cell N n) : Cell N n :=
  ⟨flipFun c.val, by rw [noneSet_flipFun]; exact c.prop⟩

@[simp] theorem flipCell_val (c : Cell N n) : (flipCell c).val = flipFun c.val := rfl

@[simp] theorem flipCell_flipCell (c : Cell N n) : flipCell (flipCell c) = c :=
  Subtype.ext (flipFun_flipFun c.val)

@[simp] theorem flipCell_topCell (n : ℕ) : flipCell (topCell n) = topCell n :=
  Subtype.ext (funext fun _ => rfl)

theorem flipCell_constVertex (N : ℕ) (ε : Bool) :
    flipCell (constVertex N ε) = constVertex N (!ε) := rfl

theorem nones_flipCell (c : Cell N n) : nones (flipCell c) = nones c :=
  (Finset.orderEmbOfFin_unique' (flipCell c).prop
    (fun i => by rw [flipCell_val, noneSet_flipFun]; exact nones_mem c i)).symm

theorem nonesIdx_flipCell (c : Cell N n) (j : Fin N) (h : j ∈ noneSet (flipCell c).val)
    (h' : j ∈ noneSet c.val) : nonesIdx (flipCell c) j h = nonesIdx c j h' := by
  apply (nones (flipCell c)).injective
  rw [nones_nonesIdx, nones_flipCell, nones_nonesIdx]

/-- **Reversal is compatible with substitution**: substitution only *moves* entries, so flipping
before and after agree.  This is the whole content of `Box.rev`'s functoriality. -/
theorem flipCell_subst (c : Cell N n) (a : Cell n k) :
    flipCell (subst c a) = subst (flipCell c) (flipCell a) := by
  apply Subtype.ext
  funext j
  by_cases hc : c.val j = none
  · have hc' : (flipCell c).val j = none := by rw [flipCell_val, flipFun, hc]; rfl
    rw [flipCell_val, flipFun, subst_val, substFun_of_none c a hc, subst_val,
      substFun_of_none _ _ hc', nonesIdx_flipCell c j (mem_noneSet.mpr hc') (mem_noneSet.mpr hc)]
    rfl
  · have hc' : (flipCell c).val j ≠ none := by
      rw [flipCell_val, flipFun]; cases h : c.val j <;> simp_all
    rw [flipCell_val, flipFun, subst_val, substFun_of_some c a hc, subst_val,
      substFun_of_some _ _ hc', flipCell_val]
    rfl

end StdCube

namespace Box

open StdCube

/-- **The reversal functor.**  Identity on objects; on morphisms it flips every fixed sign and
leaves `∗` alone.  Functoriality is `flipCell_subst`. -/
def rev : Box ⥤ Box where
  obj X := X
  map f := ofSign (flipCell (sign f))
  map_id X := hom_ext (by rw [sign_ofSign, sign_id, flipCell_topCell])
  map_comp f g := hom_ext (by
    rw [sign_ofSign, sign_comp, sign_comp, sign_ofSign, sign_ofSign, flipCell_subst])

@[simp] theorem rev_obj (X : Box) : rev.obj X = X := rfl

@[simp] theorem sign_rev {X Y : Box} (f : X ⟶ Y) : sign (rev.map f) = flipCell (sign f) :=
  sign_ofSign _

/-- **Reversal is an involution.** -/
@[simp] theorem rev_rev_map {X Y : Box} (f : X ⟶ Y) : rev.map (rev.map f) = f :=
  hom_ext (((sign_rev (rev.map f)).trans (congrArg flipCell (sign_rev f))).trans
    (flipCell_flipCell (sign f)))

@[simp] theorem rev_ofSign {N n : ℕ} (c : Cell N n) :
    rev.map (ofSign c) = ofSign (flipCell c) := congrArg (ofSign ∘ flipCell) (sign_ofSign c)

/-- Reversal as a self-inverse bijection of each hom-set. -/
def revEquivHom (a b : Box) : (a ⟶ b) ≃ (a ⟶ b) where
  toFun f := rev.map f
  invFun f := rev.map f
  left_inv f := rev_rev_map f
  right_inv f := rev_rev_map f

end Box
