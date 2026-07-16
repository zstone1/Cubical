import CubeChains.Braid.TerminalSurj

/-!
# Braid/TerminalInj — the concurrency braid map on the terminal `Zbp` is injective onto `Bₙ`

Surjectivity (`TerminalSurj`) built the canonical loops `loopZ L` with braid `ofPerm σ`.  Here we
assemble the inverse `Ψ : Braid n → ConcBraid Zbp (RZ)` through the germ presentation
(`PresentedGroup.toGroup`), whose two obligations are geometric:

* `loopZ_mul` — the germ relation holds as an equality of *loops*, not just of braids;
* `loopZ_closure` — the canonical loops generate the whole vertex group.

Given both, `concBraidHomGen (RZ)` is a bijection onto `Braid n`.
-/

open CategoryTheory Opposite Equiv

namespace CubeChains

section Basepoint

variable (n : ℕ) (hn : 0 < n)

/-! ## The canonical generator loop `Lσ σ`

`lineOf σ` is a line of the single `[n]`-bead whose sequentialization realises `σ` (in the coarse
frame).  `Lσ σ := loopZ (lineOf σ)` is then a loop at `RZ` whose braid is exactly `ofPerm σ`. -/

/-- A line of the coarse bead realising the permutation `σ` in the standard frame. -/
noncomputable def lineOf (σ : Perm (Fin n)) : LinesObj (bZ n hn).chain :=
  Function.surjInv (transport_surjective_Z n hn)
    ((finCongr (nEvents_bZ n hn)).symm.permCongr σ)

theorem evPerm'_lineOf (σ : Perm (Fin n)) :
    evPerm' (seqMor (bZ n hn) (lineOf n hn σ))
      = (finCongr (nEvents_bZ n hn)).symm.permCongr σ :=
  Function.surjInv_eq (transport_surjective_Z n hn) _

/-- **The canonical generator loop** for `σ`: the loop at `RZ` realising `ofPerm σ`. -/
noncomputable def Lσ (σ : Perm (Fin n)) : ConcBraid Zbp (RZ n hn) :=
  loopZ n hn (lineOf n hn σ)

/-- The concurrency-braid map at `RZ`, recast to the fixed strand count `n`. -/
noncomputable def Φ : ConcBraid Zbp (RZ n hn) →* Braid n :=
  (braidEqHom (nEvents_RZ n hn)).comp (concBraidHomGen (RZ n hn))

/-- **The braid of the canonical loop is `ofPerm σ`.**  `Φ` is a set-section of the map on
generators. -/
theorem Φ_Lσ (σ : Perm (Fin n)) : Φ n hn (Lσ n hn σ) = ofPerm σ := by
  rw [Φ, MonoidHom.comp_apply, Lσ, concBraidHomGen_loopZ, evPerm'_lineOf, braidEqHom,
    MonoidHom.coe_mk, OneHom.coe_mk, braidCast_ofPerm]
  congr 1

/-! ## The inverse `Ψ`, and injectivity — modulo the two geometric obligations

`Ψ := toGroup Lσ` is well defined once the germ relations hold as *loop* equalities
(`Hmul`); it is surjective once the loops generate (`Hgen`).  Both together make
`concBraidHomGen (RZ)` a bijection onto `Braid n`. -/

section Reduction

/-- `Hmul` — the germ relation as an equality of loops (not merely of braids). -/
abbrev LoopMul : Prop :=
  ∀ σ τ : Perm (Fin n), permLen (σ * τ) = permLen σ + permLen τ →
    Lσ n hn σ * Lσ n hn τ = Lσ n hn (σ * τ)

/-- `Hgen` — the canonical loops generate the whole vertex group. -/
abbrev LoopGen : Prop :=
  ∀ a : ConcBraid Zbp (RZ n hn), a ∈ Subgroup.closure (Set.range (Lσ n hn))

variable (Hmul : LoopMul n hn)

/-- The candidate inverse `Braid n → ConcBraid Zbp (RZ)`, built from the presentation. -/
noncomputable def Ψ : Braid n →* ConcBraid Zbp (RZ n hn) :=
  PresentedGroup.toGroup (f := Lσ n hn) (rels := germRels n) (by
    rintro r ⟨σ, τ, hlen, rfl⟩
    rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, Hmul σ τ hlen, mul_inv_cancel])

@[simp] theorem Ψ_ofPerm (σ : Perm (Fin n)) : Ψ n hn Hmul (ofPerm σ) = Lσ n hn σ :=
  PresentedGroup.toGroup.of _

/-- `Φ` is a retraction of `Ψ`: `Φ ∘ Ψ = id`. -/
theorem Φ_comp_Ψ : (Φ n hn).comp (Ψ n hn Hmul) = MonoidHom.id (Braid n) := by
  refine PresentedGroup.ext (fun σ => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  change Φ n hn (Ψ n hn Hmul (ofPerm σ)) = ofPerm σ
  rw [Ψ_ofPerm, Φ_Lσ]

theorem Ψ_injective : Function.Injective (Ψ n hn Hmul) :=
  Function.LeftInverse.injective (g := Φ n hn) fun b => by
    rw [← MonoidHom.comp_apply, Φ_comp_Ψ, MonoidHom.id_apply]

theorem Ψ_surjective (Hgen : LoopGen n hn) : Function.Surjective (Ψ n hn Hmul) := by
  intro a
  have hsub : Subgroup.closure (Set.range (Lσ n hn)) ≤ (Ψ n hn Hmul).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, rfl⟩
    exact ⟨ofPerm σ, Ψ_ofPerm n hn Hmul σ⟩
  exact hsub (Hgen a)

/-- **`Φ` is bijective** — hence so is `concBraidHomGen (RZ)`. -/
theorem Φ_bijective (Hgen : LoopGen n hn) : Function.Bijective (Φ n hn) := by
  refine ⟨fun a a' h => ?_, fun b => ⟨Ψ n hn Hmul b, ?_⟩⟩
  · obtain ⟨b, rfl⟩ := Ψ_surjective n hn Hmul Hgen a
    obtain ⟨b', rfl⟩ := Ψ_surjective n hn Hmul Hgen a'
    have hb : b = b' := by
      rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, Φ_comp_Ψ, MonoidHom.id_apply,
        MonoidHom.id_apply] at h
    rw [hb]
  · rw [← MonoidHom.comp_apply, Φ_comp_Ψ, MonoidHom.id_apply]

/-- **Injectivity of the concurrency braid map at the terminal basepoint.** -/
theorem concBraidHomGen_RZ_injective (Hgen : LoopGen n hn) :
    Function.Injective (concBraidHomGen (RZ n hn)) := by
  intro a a' h
  apply (Φ_bijective n hn Hmul Hgen).1
  rw [Φ, MonoidHom.comp_apply, MonoidHom.comp_apply, h]

/-- **`ConcBraid Zbp (RZ) ≅ Braid n`.**  The concurrency braid group of the terminal precubical set
at its run basepoint is the full braid group. -/
noncomputable def concBraidMulEquiv (Hgen : LoopGen n hn) :
    ConcBraid Zbp (RZ n hn) ≃* Braid n :=
  (MulEquiv.ofBijective (Ψ n hn Hmul)
    ⟨Ψ_injective n hn Hmul, Ψ_surjective n hn Hmul Hgen⟩).symm

end Reduction

end Basepoint

end CubeChains
