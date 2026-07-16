import CubeChains.Braid.SalQuotZ
import CubeChains.Salvetti.SalBraidChain

/-!
# Salvetti/FZSurj — essential surjectivity of `FZ` onto the `nEvents = n` stratum

Every terminal execution `y : ConcCat Zbp` with `nEvents y = n` is `(FZ n).obj a` for some
Salvetti cell `a`.  Two independent object-surjectivities compose:

* `braidSalEquiv` is object-surjective **on the nose** (`braidSalEquiv_obj_surjective`): the
  codomain `(Lines □ⁿ).Elements` is a category of elements over the thin, antisymmetric base
  `(Ch □ⁿ)ᵒᵖ`, so the counit iso is an equality (`elements_iso_eq`).
* `concToZ` is object-surjective onto its stratum (`concToZ_obj_surjective`): a terminal chain of
  dimension sequence `D` (with `∑D = n`) is lifted to the `□ⁿ` chain of the consecutive-block
  ordered set partition (`chainOf`), whose pushforward to the terminal set is forced (`chZbp_ext`).
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

variable {n : ℕ}

/-! ## `braidSalEquiv` is object-surjective on the nose -/

/-- The opposite of a thin category is thin. -/
instance chainCat_op_isThin : Quiver.IsThin ((Ch (□n))ᵒᵖ) :=
  fun _ _ => ⟨fun f g => Quiver.Hom.unop_inj (Subsingleton.elim f.unop g.unop)⟩

/-- **`braidSalEquiv` is object-surjective (equality, not just iso).**  Every execution of `□ⁿ`
is literally `braidSalEquiv.functor.obj a` for some Salvetti cell `a`: apply the inverse and use
that the counit iso is an equality over the thin, antisymmetric base `(Ch □ⁿ)ᵒᵖ`. -/
theorem braidSalEquiv_obj_surjective (n : ℕ) (x : ConcCat (□n)) :
    ∃ a : Sal (braidCOM n), (braidSalEquiv n).functor.obj a = x :=
  ⟨(braidSalEquiv n).inverse.obj x,
    elements_iso_eq (P := Lines (□n))
      (fun f g => Opposite.unop_injective (ChainCat.eq_of_hom_hom g.unop f.unop))
      ((braidSalEquiv n).counitIso.app x)⟩

/-! ## `concToZ` is object-surjective onto the `nEvents = n` stratum -/

/-- The dimension sequence of the chain associated to an ordered set partition is its bead-size
list. -/
theorem refineChain_dims (x : RefineObj (□n).init (□n).final) :
    ((cubeChainRefineEquiv n).functor.obj x).dims = x.cubes.map (fun c => c.1) := rfl

/-- The fibre of `Sigma.fst` over `i` in `Σ j, Fin (d j)` is `Fin (d i)`. -/
def sigmaFstFib {k : ℕ} (d : Fin k → ℕ) (i : Fin k) :
    {s : (Σ j : Fin k, Fin (d j)) // s.1 = i} ≃ Fin (d i) where
  toFun s := s.2 ▸ s.1.2
  invFun r := ⟨⟨i, r⟩, rfl⟩
  left_inv := fun s => by obtain ⟨⟨j, r⟩, h⟩ := s; cases h; rfl
  right_inv := fun _ => rfl

/-- **Lifting a dimension sequence to a `□ⁿ` chain.**  Any `D : List ℕ+` summing to `n` is the
dimension sequence of some cube chain of `□ⁿ`: take the consecutive-block ordered set partition
`β = Sigma.fst ∘ e` (`e : Fin n ≃ Σ i, Fin (D.get i)`) and run `chainOf`. -/
theorem exists_cube_chain_of_dimSum (D : List ℕ+)
    (hD : (D.map (fun d : ℕ+ => (d : ℕ))).sum = n) :
    ∃ c : Ch (□n), c.dims = D := by
  set k := D.length with hk
  set d : Fin k → ℕ := fun i => (D.get i : ℕ) with hd
  have hsum : ∑ i : Fin k, d i = n :=
    (CubeChain.sum_get_eq_sum_map D (fun d : ℕ+ => (d : ℕ))).trans hD
  have hcard : Fintype.card (Σ j : Fin k, Fin (d j)) = n := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hsum
  set e : Fin n ≃ Σ j : Fin k, Fin (d j) := (Fintype.equivFinOfCardEq hcard).symm with he
  set β : Fin n → Fin k := fun p => (e p).1 with hβdef
  have hβ : Function.Surjective β := by
    intro i
    have hpos : 0 < d i := (D.get i).pos
    exact ⟨e.symm ⟨i, ⟨0, hpos⟩⟩, by rw [hβdef]; simp [e.apply_symm_apply]⟩
  have hfib : ∀ i : Fin k, (Finset.univ.filter (fun p => β p = i)).card = d i := by
    intro i
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr
      ((e.subtypeEquiv (fun p => Iff.rfl)).trans (sigmaFstFib d i))).trans (Fintype.card_fin _)
  refine ⟨(cubeChainRefineEquiv n).functor.obj (chainOf β hβ), ?_⟩
  rw [refineChain_dims, chainOf_cubes, List.map_ofFn]
  have hfun : (fun i : Fin k => (bead β hβ i).1) = fun i : Fin k => D.get i := by
    funext i
    apply PNat.coe_injective
    change (Finset.univ.filter (fun p => β p = i)).card = (D.get i : ℕ)
    exact hfib i
  rw [show ((fun c => c.1) ∘ bead β hβ) = (fun i : Fin k => (bead β hβ i).1) from rfl, hfun]
  exact List.ofFn_get D

/-- Lifting a line along a chain equality of terminal chains: `concToZ` sends the lifted execution
to the given one, because the pushforward-to-`Zbp` chain is forced. -/
theorem concToZ_lift {c : Ch (□n)} {b : Ch Zbp}
    (hcb : (ChainCat.pushforward (toZbp (□n))).obj c = b) (M : LinesObj b) :
    (concToZ (□n)).obj
        ⟨op c, linesRestrict (a := (ChainCat.pushforward (toZbp (□n))).obj c) (eqToHom hcb) M⟩
      = ⟨op b, M⟩ := by
  subst hcb
  rw [eqToHom_refl, linesRestrict_id]
  rfl

/-- **`concToZ` is object-surjective onto its stratum.**  Every terminal execution `y` with
`nEvents y = n` is `(concToZ □ⁿ).obj x` for some `□ⁿ`-execution `x`: lift `y`'s dimension sequence
to a `□ⁿ` chain (`exists_cube_chain_of_dimSum`) and carry `y`'s line across. -/
theorem concToZ_obj_surjective (y : ConcCat Zbp) (hy : nEvents y = n) :
    ∃ x : ConcCat (□n), (concToZ (□n)).obj x = y := by
  have hD : (y.chain.dims.map (fun d : ℕ+ => (d : ℕ))).sum = n :=
    (eventObj_card y.chain).symm.trans hy
  obtain ⟨c, hcdims⟩ := exists_cube_chain_of_dimSum y.chain.dims hD
  have hcb : (ChainCat.pushforward (toZbp (□n))).obj c = y.chain :=
    chZbp_ext hcdims
  exact ⟨_, concToZ_lift hcb y.line⟩

/-! ## Essential surjectivity of `FZ` onto the stratum -/

/-- **Every terminal `n`-execution lifts to a cube execution in the image of `FZ`.**  Compose the
two object-surjectivities: lift `y` to a `□ⁿ`-execution `x` (`concToZ_obj_surjective`), then realise
`x` as `braidSalEquiv.functor.obj a` (`braidSalEquiv_obj_surjective`); `FZ` sends `a` to `y`. -/
theorem FZ_essSurj {n : ℕ} {y : ConcCat Zbp} (hy : nEvents y = n) :
    ∃ a : Sal (braidCOM n), (FZ n).obj a = y := by
  obtain ⟨x, hx⟩ := concToZ_obj_surjective y hy
  obtain ⟨a, ha⟩ := braidSalEquiv_obj_surjective n x
  refine ⟨a, ?_⟩
  change (concToZ (□n)).obj ((braidSalEquiv n).functor.obj a) = y
  rw [ha]; exact hx

end CubeChains
