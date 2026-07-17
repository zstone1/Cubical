import CubeChains.Braid.TerminalInj
import CubeChains.Braid.CubeViaZ
import CubeChains.Braid.CubePureBraidResult
import CubeChains.Salvetti.FZSurj
import CubeChains.Braid.SalvettiBraidResult

/-!
# Braid/TerminalSaturation — the terminal braid group modulo terminal saturation (T)

The concurrency braid map `Φ` at the run basepoint of `Zbp` is surjective onto `Braid n`
(`concBraidHomGen_surjective_Zn`).  Injectivity reduces to one geometric hypothesis, **terminal
saturation** (T): every pure terminal loop (one whose event-permutation monodromy `permHom ∘ Φ` is
trivial) is the image of a cube loop under `concToZAut`.  Given (T), the cube's injective
`concBraidHom` (Salvetti asphericity) forces `ker Φ = ⊥`, so `Φ` is a group iso `ConcBraid Zbp (RZ)
≃* Braid n`.
-/

open CategoryTheory Equiv OrderQuotient

namespace CubeChains

/-! ## Transport of the terminal braid map along an equality of executions -/

/-- On `Zbp`, `concBraidHomGen` and `zbpBraidHom` are the same map (a hom-level defeq). -/
theorem concBraidHomGen_eq_zbpBraidHom (y : ConcCat Zbp) : concBraidHomGen y = zbpBraidHom y := rfl

/-- The terminal braid map is invariant under transporting the execution along an equality:
conjugation by `eqToIso` becomes trivial after `subst`. -/
theorem concBraidHomGen_autMulEquivOfIso {a b : ConcCat Zbp} (h : a = b) (γ : ConcBraid Zbp a) :
    concBraidHomGen b ((Aut.autMulEquivOfIso (eqToIso (congrArg FreeGroupoid.mk h))) γ)
      = braidEqHom (congrArg nEvents h) (concBraidHomGen a γ) := by
  subst h
  have hid : (Aut.autMulEquivOfIso (eqToIso (congrArg FreeGroupoid.mk (rfl : a = a)))) γ = γ := by
    apply Aut.ext
    simp [Aut.autMulEquivOfIso]
  rw [hid]
  rfl

section
variable (n : ℕ) (hn : 0 < n)

/-! ## The cube preimage of the run basepoint -/

/-- A cube execution whose push to `Zbp` is the run basepoint `RZ`. -/
noncomputable def xRun : ConcCat (□n) :=
  (concToZ_obj_surjective (RZ n hn) (nEvents_RZ n hn)).choose

theorem concToZ_xRun : (concToZ (□n)).obj (xRun n hn) = RZ n hn :=
  (concToZ_obj_surjective (RZ n hn) (nEvents_RZ n hn)).choose_spec

theorem nEvents_xRun : nEvents (xRun n hn) = n :=
  (congrArg nEvents (concToZ_xRun n hn)).trans (nEvents_RZ n hn)

/-- `concToZAut` at the cube preimage `xRun`, transported to the run basepoint `RZ`. -/
noncomputable def concToZAutRun : ConcBraid (□n) (xRun n hn) →* ConcBraid Zbp (RZ n hn) :=
  (Aut.autMulEquivOfIso (eqToIso (congrArg FreeGroupoid.mk (concToZ_xRun n hn)))).toMonoidHom.comp
    (concToZAut n (xRun n hn))

/-! ## Terminal saturation (T) -/

/-- **Terminal saturation (T).**  Every pure terminal loop at the run basepoint (trivial
event-permutation monodromy `permHom ∘ Φ`) is the image of a cube loop under `concToZAut`. -/
def TerminalSaturation : Prop :=
  ∀ γ : ConcBraid Zbp (RZ n hn), permHom n (Φ n hn γ) = 1 → γ ∈ (concToZAutRun n hn).range

/-! ## Injectivity of `Φ` modulo (T) -/

/-- `Φ` applied, unfolded (keeps the argument symbolic to avoid evaluating the braid map). -/
theorem Phi_apply (z : ConcBraid Zbp (RZ n hn)) :
    Φ n hn z = braidEqHom (nEvents_RZ n hn) (concBraidHomGen (RZ n hn) z) := rfl

/-- `concToZAutRun` applied, unfolded (kept syntactic to avoid projecting the braid map). -/
theorem concToZAutRun_apply (δ : ConcBraid (□n) (xRun n hn)) :
    concToZAutRun n hn δ
      = (Aut.autMulEquivOfIso (eqToIso (congrArg FreeGroupoid.mk (concToZ_xRun n hn))))
          (concToZAut n (xRun n hn) δ) := by
  unfold concToZAutRun
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

set_option maxHeartbeats 1000000 in
-- The rewrite and closing `generalize` run over the free-groupoid loop `concToZAut n xRun δ`,
-- whose `braidGrpd`-image the elaborator whnf-reduces; hence the raised limit.
/-- `Φ` on a transported cube loop is the cube's `concBraidHom`, recast to `n` strands. -/
theorem Phi_concToZAutRun (δ : ConcBraid (□n) (xRun n hn)) :
    Φ n hn (concToZAutRun n hn δ)
      = braidEqHom (nEvents_xRun n hn) (concBraidHom n (xRun n hn) δ) := by
  rw [Phi_apply, concToZAutRun_apply,
      concBraidHomGen_autMulEquivOfIso (concToZ_xRun n hn) (concToZAut n (xRun n hn) δ),
      concBraidHomGen_eq_zbpBraidHom, concBraidHom_factor n (xRun n hn)]
  generalize zbpBraidHom ((concToZ (□n)).obj (xRun n hn)) (concToZAut n (xRun n hn) δ) = Y
  exact braidCast_trans (congrArg nEvents (concToZ_xRun n hn)) (nEvents_RZ n hn) Y

/-- **Injectivity of the terminal concurrency braid map, modulo (T).** -/
theorem terminal_Phi_injective (hT : TerminalSaturation n hn) : Function.Injective (Φ n hn) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hperm : permHom n (Φ n hn γ) = 1 := by rw [hγ, map_one]
  obtain ⟨δ, rfl⟩ := hT γ hperm
  have hΦ : braidEqHom (nEvents_xRun n hn) (concBraidHom n (xRun n hn) δ) = 1 := by
    rw [← Phi_concToZAutRun n hn δ]; exact hγ
  have hinj : Function.Injective (braidEqHom (nEvents_xRun n hn)) :=
    Function.LeftInverse.injective (g := braidCast (nEvents_xRun n hn).symm)
      (fun y => braidCast_leftInverse (nEvents_xRun n hn) y)
  have hcast : concBraidHom n (xRun n hn) δ = 1 := hinj (hΦ.trans (map_one _).symm)
  have hδ : δ = 1 :=
    concBraidHom_injective n (crossPerm_eq_evPerm n) (xRun n hn) (by rw [hcast, map_one])
  rw [hδ, map_one]

/-! ## The terminal braid group isomorphism modulo (T) -/

/-- **`ConcBraid Zbp (RZ) ≃* Braid n`, modulo (T).**  The concurrency braid group of the terminal
precubical set at its run basepoint is the full braid group. -/
noncomputable def terminal_concBraidMulEquiv (hT : TerminalSaturation n hn) :
    ConcBraid Zbp (RZ n hn) ≃* Braid n :=
  MulEquiv.ofBijective (Φ n hn)
    ⟨terminal_Phi_injective n hn hT, concBraidHomGen_surjective_Zn n hn⟩

/-! ## Connectivity of the run stratum -/

/-- Every terminal `n`-event execution is joined to the run basepoint in `ConcGrpd Zbp`
(`runCollapse`): the `RZ`-stratum is connected. -/
theorem concGrpdZ_run_connected (x : ConcCat Zbp) (hx : nEvents x = n) :
    Nonempty ((FreeGroupoid.mk x : ConcGrpd Zbp) ⟶ FreeGroupoid.mk (RZ n hn)) :=
  ⟨(runCollapse (hx.trans (nEvents_RZ n hn).symm)).hom⟩

/-! ## Assembly with the reorient-quotient monodromy (Piece A) -/

/-- **`ConcBraid Zbp (RZ) ≃* Aut(mk ⟦defaultCell⟧)`, modulo (T).**  Composing with Piece A's
`braidMonodromyMulEquiv` identifies the terminal run vertex group with the reorient-quotient
free-groupoid vertex group. -/
noncomputable def terminal_concBraid_monodromyMulEquiv (hT : TerminalSaturation n hn) :
    ConcBraid Zbp (RZ n hn)
      ≃* Aut (FreeGroupoid.mk (Quotient.mk'' (defaultCell n)) :
          FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))) :=
  (terminal_concBraidMulEquiv n hn hT).trans (braidMonodromyMulEquiv n hn (defaultCell n)).symm

end

end CubeChains

