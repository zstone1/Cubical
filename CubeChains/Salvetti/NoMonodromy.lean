import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Foundations.FreeGroupoidLift

/-!
# Salvetti/NoMonodromy — the chain category of the cube carries no loops

The coarsest chain of `□ⁿ` — one bead performing all `n` axes, the zero covector — is terminal, and
`Ch (□ⁿ)` is thin, so `FreeGroupoid (Ch (□ⁿ))` and `FreeGroupoid ((Ch (□ⁿ))ᵒᵖ)` are both
codiscrete.  A grading of the executions that depends only on the underlying chain morphism — which
is what ordering an execution's events by the run-free flattening `pos` would give — therefore
factors through a category with no loops, and sees none.  The run is the datum a loop moves.
-/

open CategoryTheory Opposite CubeChain CategoryTheory.FreeGroupoid

namespace CubeChains

variable {n : ℕ}

/-- The coarsest chain of `□ⁿ`: one bead performing every axis, the chain of the zero covector. -/
def topChain (n : ℕ) : Ch (□n) := chFaceEquiv.symm ⟨0, braidCOM_isOM n⟩

@[simp] theorem chFace_topChain (n : ℕ) : (chFace (topChain n)).1 = 0 :=
  congrArg Subtype.val (chFaceEquiv.apply_symm_apply _)

/-- **The coarsest chain is terminal**: the zero covector is below every face, so `reflectHom`
merges every chain into it, and `Ch (□ⁿ)` is thin, so in one way. -/
def isTerminalTopChain (n : ℕ) : Limits.IsTerminal (topChain n) :=
  haveI := chainCat_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)
  Limits.IsTerminal.ofUniqueHom
    (fun a => reflectHom (a := a) (b := topChain n)
      (by rw [chFace_topChain]; exact fun _ => Or.inl rfl))
    fun _ _ => Subsingleton.elim _ _

/-- **The chains of `□ⁿ` have no loops**: their free groupoid is codiscrete. -/
theorem subsingleton_hom_freeGroupoid_ch (X Y : FreeGroupoid (Ch (□n))) :
    Subsingleton (X ⟶ Y) :=
  subsingleton_hom_of_isTerminal _ (isTerminalTopChain n) X Y

/-- **…and neither does the base of `Ch⋆ (□ⁿ)`**, which is the opposite category. -/
theorem subsingleton_hom_freeGroupoid_chOp (X Y : FreeGroupoid (Ch (□n))ᵒᵖ) :
    Subsingleton (X ⟶ Y) :=
  subsingleton_hom_of_isInitial _ (isTerminalTopChain n).op X Y

end CubeChains
