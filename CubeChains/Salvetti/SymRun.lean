import CubeChains.Foundations.SymPresheaf
import CubeChains.Foundations.Terminal
import CubeChains.Salvetti.RunPerm

/-!
# Salvetti/SymRun — the symmetric round trip of `Z` is the run presheaf

A cell of `H.obj Z` at `▫n` is nothing but an order on the `n` axes, and `runPermEquiv` says that
is a run of `□n`.  Restriction along a face is `Tuple.sort` on both sides — `SHom.sortPerm_J_map`
on the left, `runPermEquiv_restrict` on the right.
-/

open CategoryTheory Opposite

namespace CubeChains

/-- An order on the axes of `▫n` is a run of `□n`; the `Z`-cell carries no information. -/
def symRunEquiv (n : ℕ) : (Equiv.Perm (Fin n) × Z.obj (op ▫n)) ≃ Run (□n) where
  toFun p := (runPermEquiv n).symm p.1
  invFun r := (runPermEquiv n r, PUnit.unit)
  left_inv p := Prod.ext ((runPermEquiv n).apply_symm_apply p.1) rfl
  right_inv r := (runPermEquiv n).symm_apply_apply r

/-- Both sides restrict by sorting the tuple `σ ∘ faceEmb g`. -/
theorem symRunEquiv_restrict {k m : ℕ} (g : ▫k ⟶ ▫m) (p : Equiv.Perm (Fin m) × Z.obj (op ▫m)) :
    symRunEquiv k ((H.obj Z).map g.op p) = runPresheaf.map g.op (symRunEquiv m p) := by
  have h : runPermEquiv k (runPresheaf.map g.op ((runPermEquiv m).symm p.1))
      = SHom.sortPerm (J.map g) p.1 := by
    rw [runPermEquiv_restrict, SHom.sortPerm_J_map, Equiv.apply_symm_apply]
  change (runPermEquiv k).symm (SHom.sortPerm (J.map g) p.1)
    = runPresheaf.map g.op ((runPermEquiv m).symm p.1)
  rw [← h, Equiv.symm_apply_apply]

/-- **The symmetric round trip of the terminal precubical set is the run presheaf.** -/
def HZIsoRun : H.obj Z ≅ runPresheaf :=
  NatIso.ofComponents (fun X => Equiv.toIso (symRunEquiv X.unop.dim)) fun {X Y} g => by
    apply ConcreteCategory.hom_ext; intro p
    simp only [CategoryTheory.comp_apply]
    exact symRunEquiv_restrict g.unop p

end CubeChains
