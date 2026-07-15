import CubeChains.Braid.Functor
import CubeChains.Braid.ChGrading
import CubeChains.Salvetti.BraidCharacters
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

/-! ## The short exact sequence

To make the top row *exact* — not merely a square — the chain side must be cut down to the same
stratum: `stdSection` sends an `n`-event chain to an `n`-event execution, so it restricts, and the
restriction is a strict section. -/

/-- The chains with `n` events. -/
def ChN (K : BPSet) (n : ℕ) : ObjectProperty ((Ch K)ᵒᵖ) :=
  fun a => Fintype.card (EventObj a.unop) = n

/-- The category of `n`-event chains — one stratum of `(Ch K)ᵒᵖ`. -/
abbrev ChCatN (K : BPSet) (n : ℕ) : Type _ := (ChN K n).FullSubcategory

/-- Forgetting the line, within the stratum. -/
noncomputable def chainProjN' (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ ChCatN K n :=
  ObjectProperty.lift _ (chainProjN K n) (fun x => x.property)

/-- The standard line, within the stratum: an `n`-event chain has an `n`-event standard run. -/
noncomputable def stdSectionN (K : BPSet) (n : ℕ) : ChCatN K n ⥤ ConcCatN K n :=
  ObjectProperty.lift _ ((ChN K n).ι ⋙ stdSection K) (fun a => a.property)

/-- **A strict section, stratum by stratum.** -/
theorem stdSectionN_comp_chainProjN' (K : BPSet) (n : ℕ) :
    stdSectionN K n ⋙ chainProjN' K n = 𝟭 (ChCatN K n) := rfl

/-- Forgetting the line, on the groupoid of the stratum. -/
noncomputable def concProjN' (K : BPSet) (n : ℕ) :
    ConcGrpdN K n ⥤ FreeGroupoid (ChCatN K n) :=
  FreeGroupoid.map (chainProjN' K n)

/-- The standard line, on the groupoid of the stratum. -/
noncomputable def stdSectionGrpdN (K : BPSet) (n : ℕ) :
    FreeGroupoid (ChCatN K n) ⥤ ConcGrpdN K n :=
  FreeGroupoid.map (stdSectionN K n)

/-- **`forget the line` is a split epimorphism on the stratum's groupoid** — so the top row of the
sequence below really is exact. -/
theorem stdSectionGrpdN_comp_concProjN' (K : BPSet) (n : ℕ) :
    stdSectionGrpdN K n ⋙ concProjN' K n = 𝟭 (FreeGroupoid (ChCatN K n)) := by
  refine FreeGroupoid.lift_ext ?_
  rw [← Functor.assoc, stdSectionGrpdN, FreeGroupoid.of_comp_map, Functor.assoc, concProjN',
    FreeGroupoid.of_comp_map, ← Functor.assoc, stdSectionN_comp_chainProjN', Functor.id_comp,
    Functor.comp_id]

/-- The event local system on the stratum of `n`-event chains. -/
noncomputable def eventSystemOpN (K : BPSet) (n : ℕ) : ChCatN K n ⥤ EvSet :=
  (ChN K n).ι ⋙ eventSystemOp K

/-- The event monodromy factors through `forget the line`, **within the stratum**. -/
theorem concRho_forget' (K : BPSet) (n : ℕ) :
    concRho K n ⋙ EvFrame.forget n
      = concProjN' K n ⋙ FreeGroupoid.lift (eventSystemOpN K n) := by
  refine FreeGroupoid.lift_ext ?_
  rw [← Functor.assoc, concRho, FreeGroupoid.lift_spec, ← Functor.assoc, concProjN',
    FreeGroupoid.of_comp_map, Functor.assoc, FreeGroupoid.lift_spec]
  rfl

/-- **Purity, on the stratum.**  A loop of executions whose chain-loop is trivial *in its own
stratum* has a pure braid.  This is the version the short exact sequence needs. -/
theorem permHom_braidPhi_eq_one_of_concProjN' {x : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x)
    (h : (concProjN' K n).map γ = 𝟙 _) :
    permHom n ((braidPhi K n).map γ : Braid n) = 1 := by
  have hrho : concRhoMap γ = Equiv.refl (EventObj x.obj.chain) := by
    have key := Functor.congr_hom (concRho_forget' K n) γ
    simp only [Functor.comp_map, h, CategoryTheory.Functor.map_id] at key
    exact key
  have hperm : permHom n ((braidPhi K n).map γ : Braid n) = (evMonodromy K n).map γ :=
    Functor.congr_hom (braidPhi_comp_permHom K n) γ
  rw [hperm, (evMonodromy_loop_eq_one_iff x γ).mpr hrho]
  rfl

/-! ### The sequence

Fix an execution `x` with `n` events and let `a` be its chain.  Write

    G := Aut x   in  ConcGrpdN K n            -- loops of EXECUTIONS  (zigzags in Int(Lines K))
    H := Aut a   in  FreeGroupoid (ChCatN K n) -- loops of CHAINS      (zigzags in Ch K)

Then `loopProj` is `q : G →* H`, split by `loopSection` when `x` is the standard execution over `a`,
and `braidPhi` gives `Φ : G →* Bₙ`.  The content of this file is the commuting square

    permHom ∘ Φ  =  ρ ∘ q          (`braidPhi_comp_permHom` + `concRho_forget`)

whose induced map on kernels is `Φ (ker q) ⊆ Pₙ` — forgetting the line loses only pure braids. -/

/-- `q : G →* H` — the loop of chains under a loop of executions. -/
noncomputable def loopProj (K : BPSet) (n : ℕ) (x : ConcCatN K n) :
    Aut (FreeGroupoid.mk x : ConcGrpdN K n) →*
      Aut ((concProjN' K n).obj (FreeGroupoid.mk x)) :=
  (concProjN' K n).mapAut _

/-- `σ : H →* G` — the standard-line lift of a loop of chains. -/
noncomputable def loopSection (K : BPSet) (n : ℕ) (a : ChCatN K n) :
    Aut (FreeGroupoid.mk a : FreeGroupoid (ChCatN K n)) →*
      Aut ((stdSectionGrpdN K n).obj (FreeGroupoid.mk a)) :=
  (stdSectionGrpdN K n).mapAut _

/-- **`q ∘ σ = id`**, so `q` is a split surjection: every loop of chains is realised by a loop of
executions — namely its standard-line lift.  This is exactness of the top row at `H`. -/
theorem loopProj_loopSection (K : BPSet) (n : ℕ) (a : ChCatN K n)
    (γ : Aut (FreeGroupoid.mk a : FreeGroupoid (ChCatN K n))) :
    loopProj K n ((stdSectionN K n).obj a) (loopSection K n a γ) = γ := by
  apply Iso.ext
  show (stdSectionGrpdN K n ⋙ concProjN' K n).map γ.hom = γ.hom
  rw [Functor.congr_hom (stdSectionGrpdN_comp_concProjN' K n) γ.hom]
  show 𝟙 (FreeGroupoid.mk a) ≫ γ.hom ≫ 𝟙 (FreeGroupoid.mk a) = γ.hom
  simp

/-- `q` is surjective: the top row of the sequence is exact at `H`. -/
theorem loopProj_surjective (K : BPSet) (n : ℕ) (a : ChCatN K n) :
    Function.Surjective (loopProj K n ((stdSectionN K n).obj a)) :=
  fun γ => ⟨loopSection K n a γ, loopProj_loopSection K n a γ⟩

end CubeChains
