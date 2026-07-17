import CubeChains.Braid.CubeCovering
import CubeChains.Braid.TerminalSurj
import CubeChains.Foundations.NerveQuot
import CubeChains.Salvetti.BraidSalObj

/-!
# Braid/SalQuotZ — coverings of the braid Salvetti model into the terminal concurrency groupoid

Two functors out of `FreeGroupoid (Sal (braidCOM n))`:
* `coverZ n` — refine to `ConcGrpd (□n)` (`concCubeEquiv`), then forget axis labels to
  `ConcGrpd Zbp` (`FreeGroupoid.map (concToZ (□n))`);
* `quotCover n` — the free-groupoid push of the `Sₙ`-quotient functor `quotFunctor`.

`braidSalEquiv` intertwines `salReindex σ` with `concReindex σ` (`braidSalReindexIso`); `quotCover`
inverts that action strictly (`reindex_comp_quotCover`).  `coverZ`'s analogous descent runs through
the run-collapse isos (`runCollapse`), whose faithfulness is the `Pₙ ↪ Bₙ` injection
(`CubeCovering`, `TerminalInj`).
-/

open CategoryTheory OrderQuotient

namespace CubeChains

variable {n : ℕ}

/-! ## `braidSalEquiv` intertwines the two `Sₙ`-actions -/

/-- `(salReindexEquiv σ).functor` is the poset reindex functor `salReindex σ` (same object map,
proof-irrelevant edge map). -/
def salReindexEquivFunctorIso (σ : Equiv.Perm (Fin n)) :
    (salReindexEquiv σ).functor ≅ salReindex σ :=
  eqToIso rfl

/-- **Equivariance of `braidSalEquiv`.**  The Salvetti reorientation `salReindex σ` transported
through `braidSalEquiv` is the concurrency reindexing `concReindex σ`. -/
noncomputable def braidSalReindexIso (σ : Equiv.Perm (Fin n)) :
    salReindex σ ⋙ (braidSalEquiv n).functor
      ≅ (braidSalEquiv n).functor ⋙ (concReindex σ).functor :=
  (Functor.isoWhiskerRight (braidSalEquiv n).unitIso.symm
      ((salReindexEquiv σ).functor ⋙ (braidSalEquiv n).functor)
    ≪≫ Functor.isoWhiskerRight (salReindexEquivFunctorIso σ) (braidSalEquiv n).functor).symm

/-! ## The two coverings out of `FreeGroupoid (Sal (braidCOM n))` -/

/-- The **ordered covering into the terminal set**: refine the Salvetti model to `ConcGrpd (□n)`
(via `concCubeEquiv`), then forget axis labels to `ConcGrpd Zbp`. -/
noncomputable def coverZ (n : ℕ) : FreeGroupoid (Sal (braidCOM n)) ⥤ ConcGrpd Zbp :=
  (concCubeEquiv n).functor ⋙ FreeGroupoid.map (concToZ (□n))

/-- The **free `Sₙ`-quotient covering**: the free-groupoid push of the poset quotient functor
`quotFunctor : Sal (braidCOM n) ⥤ QuotCat (Sal (braidCOM n)) (Perm (Fin n))`. -/
noncomputable def quotCover (n : ℕ) :
    FreeGroupoid (Sal (braidCOM n))
      ⥤ FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) :=
  FreeGroupoid.map (OrderQuotient.quotFunctor
    (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)))

/-- `coverZ` is a single free-groupoid push: refine-then-forget on the base
(`(braidSalEquiv n).functor ⋙ concToZ (□n) : Sal (braidCOM n) ⥤ ConcCat Zbp`). -/
theorem coverZ_eq (n : ℕ) :
    coverZ n = FreeGroupoid.map ((braidSalEquiv n).functor ⋙ concToZ (□n)) := by
  rw [coverZ,
    show (concCubeEquiv n).functor = FreeGroupoid.map (braidSalEquiv n).functor from rfl,
    ← FreeGroupoid.map_comp]

/-! ## The quotient covering strictly coequalizes the `Sₙ`-reorientation action

`quotFunctor` is `Sₙ`-invariant on the poset (`smulFunctor_comp_quotFunctor`), and `salReindex σ`
*is* `smulFunctor σ`, so `quotCover` inverts the deck action on the nose. -/

/-- On the poset, reorientation is the abstract `smulFunctor`. -/
theorem salReindex_eq_smulFunctor (σ : Equiv.Perm (Fin n)) :
    salReindex σ
      = OrderQuotient.smulFunctor (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) σ := rfl

/-- Reorienting a Salvetti cell does not change its orbit's image under `quotFunctor`. -/
theorem salReindex_comp_quotFunctor (σ : Equiv.Perm (Fin n)) :
    salReindex σ ⋙ OrderQuotient.quotFunctor
        (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n))
      = OrderQuotient.quotFunctor := by
  rw [salReindex_eq_smulFunctor]; exact OrderQuotient.smulFunctor_comp_quotFunctor σ

/-- **The `Sₙ`-quotient covering coequalizes the deck action (strictly).**  Pre-reorienting by
`σ` before pushing to the quotient covering is the covering itself — `quotCover` is
`Sₙ`-invariant on the nose. -/
theorem reindex_comp_quotCover (σ : Equiv.Perm (Fin n)) :
    FreeGroupoid.map (salReindex σ) ⋙ quotCover n = quotCover n := by
  rw [quotCover, ← FreeGroupoid.map_comp, salReindex_comp_quotFunctor]

/-! ## Run-collapse: a fixed event count is one connected component of `ConcGrpd Zbp`

`coverZ` cannot descend to a strict functor `QuotCat _ _ ⥤ ConcCat Zbp` — reorienting a Salvetti
cell changes the line (`concToZ ∘ concReindex σ ≠ concToZ` on the nose).  What repairs this at the
free-groupoid level: on the terminal set all executions of a given event count sequentialize to
*one* run (`seqChain_eq_terminal`), so they are canonically isomorphic in `ConcGrpd Zbp`. -/

/-- Sequentializations of two terminal executions with the same event count coincide: both are runs
with all-`1` dims of length that count, and `Zbp` is terminal (`chZbp_ext`). -/
theorem seqChain_eq_of_nEvents {x y : ConcCat Zbp} (h : nEvents x = nEvents y) :
    seqChain x.line = seqChain y.line := by
  apply chZbp_ext
  rw [run_dims_eq_replicate (seqChain_isRun x.line),
      run_dims_eq_replicate (seqChain_isRun y.line),
      ← run_card_length (seqChain_isRun x.line),
      ← run_card_length (seqChain_isRun y.line),
      card_eventObj_eq_of_hom (seqRefine x.line),
      card_eventObj_eq_of_hom (seqRefine y.line)]
  exact congrArg (fun k => List.replicate k 1) h

/-- The canonical iso `mk x ≅ mk (run x)` in `ConcGrpd Zbp`: refine `x` to its own
sequentialization (a free-groupoid iso, refinements being invertible upstairs). -/
noncomputable def toRunZ (x : ConcCat Zbp) :
    (FreeGroupoid.mk x : ConcGrpd Zbp)
      ≅ FreeGroupoid.mk (runExec (seqChain x.line) (seqChain_isRun x.line)) :=
  asIso (FreeGroupoid.homMk (seqMor x x.line))

/-- **Run-collapse.**  Any two executions of `Zbp` with the same event count are canonically
isomorphic in `ConcGrpd Zbp` — the chamber-count mismatch between the `Sₙ`-quotient Salvetti model
and the terminal model dissolves once refinements are inverted. -/
noncomputable def runCollapse {x y : ConcCat Zbp} (h : nEvents x = nEvents y) :
    (FreeGroupoid.mk x : ConcGrpd Zbp) ≅ FreeGroupoid.mk y :=
  toRunZ x
    ≪≫ eqToIso (congrArg FreeGroupoid.mk
        (runExec_congr (seqChain_eq_of_nEvents h)
          (seqChain_isRun x.line) (seqChain_isRun y.line)))
    ≪≫ (toRunZ y).symm

/-! ## The descent functor `Ψ : ConcCat Zbp ⥤ QuotCat (Sal) Sₙ`

`F := braidSalEquiv.functor ⋙ concToZ` pushes a Salvetti cell to its terminal execution.  Its fiber
is exactly one `Sₙ`-orbit (`braidSal_concToZ_fiber`), so the orbit `⟦a⟧` is a function of `F a`
alone — this is the object map of `Ψ`. -/

/-- Refine a Salvetti cell to `ConcCat (□n)`, then forget axis labels to `ConcCat Zbp`. -/
noncomputable def FZ (n : ℕ) : Sal (braidCOM n) ⥤ ConcCat Zbp :=
  (braidSalEquiv n).functor ⋙ concToZ (□n)

theorem FZ_eq (n : ℕ) : FZ n = (braidSalEquiv n).functor ⋙ concToZ (□n) := rfl

/-- The image of `FZ` lands in the `n`-event stratum: a Salvetti cell of `braidCOM n` refines a
`□n`-execution, which has exactly `n` events, and forgetting axis labels preserves the count. -/
theorem nEvents_FZ (n : ℕ) (a : Sal (braidCOM n)) : nEvents ((FZ n).obj a) = n := by
  rw [show (FZ n).obj a
        = (concMap (toZbp (□n))).obj ((braidSalEquiv n).functor.obj a) from rfl,
      nEvents_concMap]
  exact eventObj_card_cube _

/-- The tope realised by the injective height `i ↦ i`. -/
theorem defaultTope_isTope (n : ℕ) :
    (braidCOM n).IsTope (braidSign (fun i : Fin n => (i.val : ℤ))) := by
  refine (braidCOM_isTope_iff_injective _).mpr ⟨fun i : Fin n => (i.val : ℤ), ?_, rfl⟩
  intro a b h
  have h' : (a.val : ℤ) = (b.val : ℤ) := h
  exact Fin.ext (by exact_mod_cast h')

/-- A fixed Salvetti cell of `braidCOM n`: the diagonal cell `(T, T)` at that tope. -/
def defaultCell (n : ℕ) : Sal (braidCOM n) :=
  ⟨(braidSign (fun i : Fin n => (i.val : ℤ)), braidSign (fun i : Fin n => (i.val : ℤ))),
    (defaultTope_isTope n).1, defaultTope_isTope n, SignVec.faceLE_refl _⟩

open Classical in
/-- Object map of `Ψ`: the `Sₙ`-orbit of any Salvetti cell whose terminal execution is `y`
(fixed dummy off the image of `FZ`). -/
noncomputable def psiObj (n : ℕ) (y : ConcCat Zbp) :
    QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)) :=
  if h : ∃ a : Sal (braidCOM n), (FZ n).obj a = y then
    Quotient.mk'' h.choose
  else Quotient.mk'' (defaultCell n)

/-- **Object half of the transport equation.**  `Ψ.obj (F a) = ⟦a⟧`, regardless of the choice
inside `psiObj`: any two preimages differ by an `Sₙ`-reorientation (`braidSal_concToZ_fiber`), so
their orbits coincide. -/
theorem psiObj_FZ (n : ℕ) (a : Sal (braidCOM n)) :
    psiObj n ((FZ n).obj a) = Quotient.mk'' a := by
  have hex : ∃ a' : Sal (braidCOM n), (FZ n).obj a' = (FZ n).obj a := ⟨a, rfl⟩
  rw [psiObj, dif_pos hex]
  obtain ⟨σ, hσ⟩ := braidSal_concToZ_fiber (a := hex.choose) (a' := a) hex.choose_spec
  rw [← hσ]
  exact mk_smul_eq σ a

end CubeChains
