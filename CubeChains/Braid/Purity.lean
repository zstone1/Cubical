import CubeChains.Braid.Functor
import CubeChains.Foundations.FreeGroupoidLift

/-!
# Braid/Purity — forgetting the line can only lose *pure* braids

`Int(Lines K)` fibres over the chains, and forgetting the line is `π : Int(Lines K) ⥤ (Ch K)ᵒᵖ`.
The braids a chain-level invariant cannot see are exactly those of the loops `π` kills — and this
file proves they are **pure**.

The reason is that the event bijection of a refinement reads *only* the chain: `concFrameSystem`'s
action on morphisms is `(eventEquiv (concRefine f)).symm`, and `concRefine f` is the chain map.  So
the frame-free event monodromy **factors through `π`** (`concRho_forget`).  A loop killed by `π`
therefore permutes its events trivially, and `evMonodromy_loop_eq_one_iff` — "the frames cancel on a
loop" — converts that into purity of the braid.

    π-trivial loop  ⟹  trivial event monodromy  ⟹  trivial permutation  ⟹  pure braid

The converse fails, and that is the point: `Ch(□ⁿ)` has a terminal object, so *every* loop of
`ConcGrpd (□ⁿ)` is π-trivial, yet its braid is a nontrivial pure braid (on `□²`, the full twist).
-/

open CategoryTheory Opposite

namespace CubeChains

variable {K : BPSet} {n : ℕ}

/-! ## Forgetting the line -/

/-- The chain of an execution, on the `n`-event stratum. -/
noncomputable def chainProjN (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ (Ch K)ᵒᵖ :=
  (ConcN K n).ι ⋙ CategoryOfElements.π (Lines K)

/-- Forgetting the line, on the concurrency groupoid. -/
noncomputable def concProjN (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ FreeGroupoid ((Ch K)ᵒᵖ) :=
  FreeGroupoid.map (chainProjN K n)

/-- The event local system, read on `(Ch K)ᵒᵖ`: a refinement bijects the events, backwards. -/
noncomputable def eventSystemOp (K : BPSet) : (Ch K)ᵒᵖ ⥤ EvSet where
  obj a := ⟨EventObj a.unop⟩
  map f := (eventEquiv f.unop).symm
  map_id a := by
    change (eventEquiv (𝟙 a.unop)).symm = Equiv.refl _
    rw [eventEquiv_id]
    rfl
  map_comp {a b c} f g := by
    change (eventEquiv (g.unop ≫ f.unop)).symm
      = (eventEquiv f.unop).symm.trans (eventEquiv g.unop).symm
    rw [eventEquiv_comp]
    rfl

/-! ## The event monodromy reads only the chain -/

/-- **The framed event system forgets to the chain-level one** — on the nose: `concFrameSystem`'s
action on a morphism is `eventEquiv` of its *chain* map, and nothing else. -/
theorem concFrameSystem_forget (K : BPSet) (n : ℕ) :
    concFrameSystem K n ⋙ EvFrame.forget n = chainProjN K n ⋙ eventSystemOp K := rfl

/-- **The frame-free event monodromy factors through `forget the line`.** -/
theorem concRho_forget (K : BPSet) (n : ℕ) :
    concRho K n ⋙ EvFrame.forget n
      = concProjN K n ⋙ FreeGroupoid.lift (eventSystemOp K) := by
  refine FreeGroupoid.lift_ext ?_
  rw [← Functor.assoc, concRho, FreeGroupoid.lift_spec, concFrameSystem_forget,
    ← Functor.assoc, concProjN, FreeGroupoid.of_comp_map, Functor.assoc,
    FreeGroupoid.lift_spec]

/-- **A loop that `π` kills permutes its events trivially.** -/
theorem concRhoMap_eq_refl_of_concProjN {x : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x)
    (h : (concProjN K n).map γ = 𝟙 _) :
    concRhoMap γ = Equiv.refl (EventObj x.obj.chain) := by
  have key := Functor.congr_hom (concRho_forget K n) γ
  simp only [Functor.comp_map, h, CategoryTheory.Functor.map_id] at key
  exact key

/-! ## The braid of such a loop is pure -/

/-- In a one-object category the identity *is* the unit, so an `eqToHom` is trivial. -/
private theorem eqToHom_singleObj {M : Type*} [Monoid M] {a b : SingleObj M} (h : a = b) :
    (eqToHom h : a ⟶ b) = (1 : M) := by
  cases h
  rfl

/-- **`Φ`'s permutation part is the event monodromy** — for the *germ* braid functor. -/
theorem braidPhi_comp_permHom (K : BPSet) (n : ℕ) :
    braidPhi K n ⋙ SingleObj.mapHom _ _ (permHom n) = evMonodromy K n := by
  refine FreeGroupoid.lift_unique (eventMonodromy K n) _ ?_
  rw [← Functor.assoc, braidPhi, FreeGroupoid.lift_spec]
  refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y f => ?_)
  rw [eqToHom_singleObj, eqToHom_singleObj]
  change permHom n (ofPerm (evPerm f)) = _
  rw [permHom_ofPerm]
  simp [SingleObj.comp_as_mul]

/-- **The braids that forgetting the line can lose are PURE.**

A loop of executions whose chain-zigzag is trivial has a braid with **trivial permutation** — and
`PureBraid n` *is* `(permHom n).ker`, so this says exactly that its braid is pure.

This is the left-hand vertical of a map of exact sequences:

    1 ──▶ ker(concProjN) ──▶ Aut(mk x) ──concProjN──▶ Aut(mk (chain x))
              │                 │                          │
              │ Φ               │ Φ                        │ ρ   (event monodromy of the chain)
              ▼                 ▼                          ▼
    1 ──▶  PureBraid n ─────▶ Braid n ───permHom──────▶ Perm (Fin n)

The bottom row is exact by definition.  The right square commutes: `braidPhi_comp_permHom` says the
permutation part of the braid *is* the event monodromy, and `concRho_forget` says the event
monodromy reads only the chain.  The top row is split by the standard line
(`stdSectionGrpd_comp_concProj`, `Braid/ChGrading`).  This theorem is the induced map on kernels —
the statement that it lands where it must.

The converse fails, and that is the whole point: over `□ⁿ` the chain category has a terminal object,
so **every** loop is `concProjN`-trivial, yet the braids are the nontrivial pure braids. -/
theorem permHom_braidPhi_eq_one_of_concProjN {x : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x)
    (h : (concProjN K n).map γ = 𝟙 _) :
    permHom n ((braidPhi K n).map γ : Braid n) = 1 := by
  have hperm : permHom n ((braidPhi K n).map γ : Braid n) = (evMonodromy K n).map γ :=
    Functor.congr_hom (braidPhi_comp_permHom K n) γ
  have hmono : (evMonodromy K n).map γ = 𝟙 _ :=
    (evMonodromy_loop_eq_one_iff x γ).mpr (concRhoMap_eq_refl_of_concProjN γ h)
  rw [hperm, hmono]
  rfl

end CubeChains
