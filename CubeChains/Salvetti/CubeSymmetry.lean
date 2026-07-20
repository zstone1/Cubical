import CubeChains.Salvetti.BraidIso
import CubeChains.Arrangements.SalSymmetry
import CubeChains.Foundations.SkeletalEquiv
import CubeChains.Foundations.QuotientCat

/-!
# Salvetti/CubeSymmetry — the free `Sₙ` action on the executions of the cube

`Sₙ` **relabels the coordinates a run visits**: `σ • x` is the execution whose `p`-th coordinate is
flipped where `x` flips `σ⁻¹ p` (`chStarSmul_runHeight`).  That law is the whole public API; run
heights are genuine block indices, so it holds on the nose and freeness is immediate from
`runHeight_injective`.

Precubical sets here are symmetry-free, so `Aut(□ⁿ) = 1` and no map `□ⁿ ⟶ □ⁿ` realises a coordinate
permutation.  The action can therefore only be *defined* through the combinatorial classification
`braidSalEquiv`, where relabelling is `reorient`; both sides are posets, so that equivalence is a
bijection on objects (`Equivalence.objEquivOfSkeletal`) and the transport is a genuine `MulAction`.
The equivalence is crossed once, in the instance, and once more to prove
`chStarSmul_runHeight` — after which nothing downstream mentions a Salvetti cell.
-/

open CategoryTheory CubeChain

namespace CubeChains

variable {n : ℕ}

/-! ### Skeletality of the two sides -/

/-- `Ch K` is a poset: isomorphic chains are equal (`ChainCat.le_antisymm`). -/
theorem chainCat_skeletal (K : BPSet) : Skeletal (Ch K) := fun _ _ h =>
  h.elim fun e => ChainCat.le_antisymm ⟨e.hom⟩ ⟨e.inv⟩

theorem chainCat_op_skeletal (K : BPSet) : Skeletal (Ch K)ᵒᵖ :=
  (chainCat_skeletal K).op

/-- Executions of the cube form a poset: the base `(Ch (□ⁿ))ᵒᵖ` is thin and skeletal. -/
theorem chStar_cube_skeletal (n : ℕ) : Skeletal (Ch⋆ (□n)) :=
  Functor.elements_skeletal (chainCat_op_skeletal (□n)) (Lines (□n))

/-- The Salvetti poset of a COM is skeletal, being a partial order. -/
theorem sal_skeletal {E : Type*} (L : COM E) : Skeletal (Sal L) := fun _ _ h =>
  h.elim fun e => le_antisymm (leOfHom e.hom) (leOfHom e.inv)

/-! ### The action -/

/-- `braidSalEquiv` on objects: a bijection, since both sides are posets. -/
def salChStarEquiv (n : ℕ) : Sal (braidCOM n) ≃ Ch⋆ (□n) :=
  (braidSalEquiv n).objEquivOfSkeletal (sal_skeletal _) (chStar_cube_skeletal n)

/-- The `Sₙ` action on executions of the cube, transported from the reorientation action.  Use
`chStarSmul_runHeight`, not this, to compute with it. -/
instance : MulAction (Equiv.Perm (Fin n)) (Ch⋆ (□n)) where
  smul σ x := salChStarEquiv n (σ • (salChStarEquiv n).symm x)
  one_smul x := by
    change salChStarEquiv n ((1 : Equiv.Perm (Fin n)) • (salChStarEquiv n).symm x) = x
    rw [one_smul, Equiv.apply_symm_apply]
  mul_smul σ τ x := by
    change salChStarEquiv n ((σ * τ) • (salChStarEquiv n).symm x)
      = salChStarEquiv n (σ • (salChStarEquiv n).symm (salChStarEquiv n (τ • _)))
    rw [Equiv.symm_apply_apply, mul_smul]

/-! ### The classification dictionary

The three facts below are the entire content of crossing `braidSalEquiv`, and each is `rfl` —
`salLinesIso` is built from `ofRun`, whose tope is `braidSign (runHeight …)`.  Everything after
this section is intrinsic to `Ch⋆`. -/

/-- The cell classifying `x` has `x`'s run height as its tope. -/
theorem symm_tope (x : Ch⋆ (□n)) :
    ((salChStarEquiv n).symm x).tope = braidSign (runHeight x.chain x.run) := rfl

/-- …and `x`'s chain covector as its face. -/
theorem symm_face (x : Ch⋆ (□n)) :
    ((salChStarEquiv n).symm x).face = braidSign (chCovectorHeight x.chain) := rfl

/-- The classification is equivariant by construction of the action. -/
theorem symm_smul (σ : Equiv.Perm (Fin n)) (x : Ch⋆ (□n)) :
    (salChStarEquiv n).symm (σ • x) = σ • (salChStarEquiv n).symm x :=
  (salChStarEquiv n).symm_apply_apply _

/-! ### The intrinsic law

Reorienting the classifying tope only pins the run height *as a covector*; `runHeight` is its own
dense rank (`denseRank_runHeight`), which upgrades that to equality on the nose. -/

/-- **The action relabels run heights**: `σ • x` flips at position `p` the coordinate that `x`
flips at position `σ⁻¹ p`. -/
theorem chStarSmul_runHeight (σ : Equiv.Perm (Fin n)) (x : Ch⋆ (□n)) (p : Fin n) :
    runHeight (σ • x).chain (σ • x).run p = runHeight x.chain x.run (σ⁻¹ p) := by
  have htope : braidSign (runHeight (σ • x).chain (σ • x).run)
      = braidSign (fun q => runHeight x.chain x.run (σ⁻¹ q)) := by
    rw [← symm_tope, symm_smul, smul_tope, symm_tope, reorient_braidSign]
  have hrank := denseRank_eq_of_braidSign_eq htope
  calc runHeight (σ • x).chain (σ • x).run p
      = denseRank (runHeight (σ • x).chain (σ • x).run) p := by rw [denseRank_runHeight]
    _ = denseRank (fun q => runHeight x.chain x.run (σ⁻¹ q)) p := by rw [hrank]
    _ = denseRank (runHeight x.chain x.run) (σ⁻¹ p) := denseRank_comp_perm _ _ _
    _ = _ := by rw [denseRank_runHeight]

/-- The chain component is relabelled the same way.  Only the covector is pinned here: a chain's
height function has ties, so it is not its own dense rank. -/
theorem chStarSmul_chCovectorHeight (σ : Equiv.Perm (Fin n)) (x : Ch⋆ (□n)) :
    braidSign (chCovectorHeight (σ • x).chain)
      = braidSign (fun q => chCovectorHeight x.chain (σ⁻¹ q)) := by
  rw [← symm_face, symm_smul, smul_face, symm_face, reorient_braidSign]

/-! ### Freeness -/

/-- **The `Sₙ` action on `Ch⋆ (□ⁿ)` is free.**  A fixed execution has its own height function
reindexed by `σ⁻¹`; run heights have no ties, so `σ⁻¹` is the identity. -/
theorem chStarSmul_free {σ : Equiv.Perm (Fin n)} {x : Ch⋆ (□n)} (h : σ • x = x) : σ = 1 := by
  have hinv : σ⁻¹ = 1 := Equiv.ext fun p =>
    runHeight_injective x.chain x.run <| by
      rw [← chStarSmul_runHeight σ x p]
      exact congrArg (fun y : Ch⋆ (□n) => runHeight y.chain y.run p) h
  rw [← inv_inv σ, hinv, inv_one]

/-! ### Executions as a poset

`Ch⋆ (□ⁿ)` already carries the category-of-elements structure, whose hom is a subtype; a
`PartialOrder` instance on it would supply a second `Category` via `Preorder.smallCategory`, whose
hom is `ULift (PLift _)` — not defeq to the first.  The order therefore lives on a synonym. -/

/-- Executions of the cube carrying the order `x ≤ y := Nonempty (x ⟶ y)`. -/
def ChStarOrd (n : ℕ) : Type := Ch⋆ (□n)

/-- The synonym is the identity on elements. -/
def chStarOrdEquiv (n : ℕ) : ChStarOrd n ≃ Ch⋆ (□n) := Equiv.refl _

instance : PartialOrder (ChStarOrd n) where
  le x y := Nonempty (chStarOrdEquiv n x ⟶ chStarOrdEquiv n y)
  le_refl x := ⟨𝟙 _⟩
  le_trans _ _ _ h1 h2 := ⟨h1.some ≫ h2.some⟩
  le_antisymm _ _ h1 h2 :=
    chStar_cube_skeletal n
      ⟨Iso.mk h1.some h2.some (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

theorem chStarOrd_le_iff (x y : ChStarOrd n) :
    x ≤ y ↔ Nonempty (chStarOrdEquiv n x ⟶ chStarOrdEquiv n y) := Iff.rfl

instance : MulAction (Equiv.Perm (Fin n)) (ChStarOrd n) :=
  inferInstanceAs (MulAction (Equiv.Perm (Fin n)) (Ch⋆ (□n)))

/-! ### The categorical form -/

/-- Reorientation as an endofunctor of executions, conjugated across `braidSalEquiv`. -/
def chStarReorient (σ : Equiv.Perm (Fin n)) : Ch⋆ (□n) ⥤ Ch⋆ (□n) :=
  (braidSalEquiv n).inverse ⋙ salReorientFunctor σ ⋙ (braidSalEquiv n).functor

/-- The functor computes the action on objects — both `objEquivOfSkeletal` and
`salReorientFunctor` keep their object maps definitional. -/
@[simp] theorem chStarReorient_obj (σ : Equiv.Perm (Fin n)) (x : Ch⋆ (□n)) :
    (chStarReorient σ).obj x = σ • x := rfl

/-! ### Order-freeness

Monotonicity is functoriality of `chStarReorient`, and reflection is the same for `σ⁻¹`; no order
is transported across the equivalence. -/

theorem chStarOrd_smul_le_smul_iff (σ : Equiv.Perm (Fin n)) {x y : ChStarOrd n} :
    σ • x ≤ σ • y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => ⟨(chStarReorient σ).map h.some⟩⟩
  have hx : σ⁻¹ • σ • (x : Ch⋆ (□n)) = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
  have hy : σ⁻¹ • σ • (y : Ch⋆ (□n)) = y := by rw [← mul_smul, inv_mul_cancel, one_smul]
  exact ⟨eqToHom hx.symm ≫ (chStarReorient σ⁻¹).map h.some ≫ eqToHom hy⟩

/-- **The `Sₙ` action on executions is order-free**, which is what `QuotCat` consumes. -/
instance : OrderQuotient.OrderFreeAction (Equiv.Perm (Fin n)) (ChStarOrd n) :=
  OrderQuotient.OrderFreeAction.of_finite_of_free
    (fun σ => chStarOrd_smul_le_smul_iff σ) (fun _ _ h => chStarSmul_free h)

end CubeChains
