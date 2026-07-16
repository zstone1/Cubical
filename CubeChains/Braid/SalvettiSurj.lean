import CubeChains.Braid.SalvettiDeckCompat
import Mathlib.CategoryTheory.Conj

/-!
# Braid/SalvettiSurj — surjectivity of the pure-braid monodromy

`pureMonodromy n x : Aut (mk x) →* Pₙ` is onto, *taking as a hypothesis* the connectivity of the
`n`-event executions in `ConcGrpd (□n)` (`hconn_conc`, discharged elsewhere).

The Salvetti loop-to-braid map, read through `salvettiConstruction_eq`, is the concurrency braid
`concBraidHom` at the run `(braidSalEquiv n).functor.obj x`, transported by the fixed-frame collapse
`readBraid n`.  Surjectivity at the single-cube run (`concPureBraidHom_surjective`) is moved to an
arbitrary `n`-event basepoint by conjugating along a connecting iso; `Pₙ` is normal, so a conjugate
of it is again `Pₙ`.
-/

open CategoryTheory

namespace CubeChains

variable {n : ℕ}

/-- The cube braid functor collapsed onto the fixed `Braid n` fibre. -/
noncomputable def cubeRead (n : ℕ) : ConcGrpd (□n) ⥤ SingleObj (Braid n) :=
  braidGrpd (□n) ⋙ readBraid n

/-- Read any morphism of `ConcGrpd (□n)` as an honest braid on `n` strands.  The codomain `Braid n`
forces the `SingleObj`-hom-to-`Braid n` collapse, so group operations resolve. -/
noncomputable def cubeReadHom {X Y : ConcGrpd (□n)} (f : X ⟶ Y) : Braid n := (cubeRead n).map f

theorem autToBraid_cubeRead (w : ConcCat (□n)) (b : ConcBraid (□n) w) :
    autToBraid (cubeRead n) (FreeGroupoid.mk w) b = cubeReadHom b.hom := rfl

theorem cubeReadHom_id (X : ConcGrpd (□n)) : cubeReadHom (𝟙 X) = 1 := by
  rw [show cubeReadHom (𝟙 X) = 𝟙 ((cubeRead n).obj X) from (cubeRead n).map_id X,
    SingleObj.id_as_one]

theorem cubeReadHom_comp {X Y Z : ConcGrpd (□n)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cubeReadHom (f ≫ g) = cubeReadHom g * cubeReadHom f := by
  have h := (cubeRead n).map_comp f g
  rw [SingleObj.comp_as_mul] at h
  exact h

theorem cubeReadHom_inv {y z : ConcCat (□n)}
    (p : (FreeGroupoid.mk y : ConcGrpd (□n)) ≅ FreeGroupoid.mk z) :
    cubeReadHom p.inv = (cubeReadHom p.hom)⁻¹ := by
  have hone : cubeReadHom p.hom * cubeReadHom p.inv = 1 := by
    rw [← cubeReadHom_comp, p.inv_hom_id, cubeReadHom_id]
  exact eq_inv_of_mul_eq_one_right hone

/-- `braidCast` neither creates nor destroys purity. -/
theorem braidCast_mem_pure {m k : ℕ} (h : m = k) (p : Braid m) :
    braidCast h p ∈ PureBraid k ↔ p ∈ PureBraid m := by
  cases h
  rw [braidCast_rfl]

/-- **Bridge.**  On an `n`-event basepoint the fixed-frame monodromy `autToBraid (cubeRead n)` is
the concurrency braid `concBraidHom`, recast to `Braid n`. -/
theorem cubeRead_autToBraid (w : ConcCat (□n)) (hw : nEvents w = n) (b : ConcBraid (□n) w) :
    autToBraid (cubeRead n) (FreeGroupoid.mk w) b = braidCast hw (concBraidHom n w b) := by
  have hb : concBraidHom n w b
      = braidCast hw.symm (autToBraid (cubeRead n) (FreeGroupoid.mk w) b) := by
    rw [concBraidHom_apply]
    exact endBraid_of_readBraid ((braidGrpd (□n)).map b.hom) hw
  have hcancel := braidCast_leftInverse hw.symm (autToBraid (cubeRead n) (FreeGroupoid.mk w) b)
  rw [← hb] at hcancel
  exact hcancel.symm

/-- **Conjugation.**  A connecting iso `p : mk y ≅ mk z` conjugates the monodromy: reading `p` as a
braid `cubeReadHom p.hom`, the loop `p.conjAut b` at `z` traces `r · (loop at y) · r⁻¹`. -/
theorem cubeRead_conjAut {y z : ConcCat (□n)}
    (p : (FreeGroupoid.mk y : ConcGrpd (□n)) ≅ FreeGroupoid.mk z) (b : ConcBraid (□n) y) :
    autToBraid (cubeRead n) (FreeGroupoid.mk z) (p.conjAut b)
      = cubeReadHom p.hom * autToBraid (cubeRead n) (FreeGroupoid.mk y) b
          * (cubeReadHom p.hom)⁻¹ := by
  rw [autToBraid_cubeRead, autToBraid_cubeRead, Iso.conjAut_hom, Iso.conj_apply,
    cubeReadHom_comp, cubeReadHom_comp, cubeReadHom_inv]

/-- **(C) Agreement.**  The underlying braid of `pureMonodromy n x` is the fixed-frame monodromy of
the concurrency loop at the run `(braidSalEquiv n).functor.obj x`. -/
theorem pureMonodromy_subtype_eq (x : Sal (braidCOM n))
    (a : Aut (FreeGroupoid.mk x : FreeGroupoid (Sal (braidCOM n)))) :
    (PureBraid n).subtype (pureMonodromy n x a)
      = autToBraid (cubeRead n) (FreeGroupoid.mk ((braidSalEquiv n).functor.obj x))
          (salVertexMulEquiv n x a) := by
  have hsub : (PureBraid n).subtype (pureMonodromy n x a)
      = (salvettiConstruction n).map a.hom := rfl
  have hsv : (concCubeEquiv n).functor.map a.hom = (salVertexMulEquiv n x a).hom := rfl
  rw [hsub, salvettiConstruction_eq n (crossPerm_eq_evPerm n)]
  simp only [CategoryTheory.Functor.comp_map]
  rw [hsv]
  rfl

/-- **(B, base).**  At an `n`-event execution `z` where `concPureBraidHom` is onto `Pₙ`, the
fixed-frame monodromy `autToBraid (cubeRead n)` hits every pure braid. -/
theorem autToBraid_surjective_of_concPure (z : ConcCat (□n)) (hz : nEvents z = n)
    (hsurj : Function.Surjective (concPureBraidHom n z)) :
    ∀ q : Braid n, q ∈ PureBraid n →
      ∃ c : ConcBraid (□n) z, autToBraid (cubeRead n) (FreeGroupoid.mk z) c = q := by
  intro q hq
  have hmem : braidCast hz.symm q ∈ PureBraid (nEvents z) := (braidCast_mem_pure hz.symm q).mpr hq
  obtain ⟨c, hc⟩ := hsurj ⟨braidCast hz.symm q, hmem⟩
  have hc' : concBraidHom n z c = braidCast hz.symm q := congrArg Subtype.val hc
  refine ⟨c, ?_⟩
  rw [cubeRead_autToBraid z hz c, hc']
  exact braidCast_leftInverse hz.symm q

/-- **(B, transport).**  Along a connecting iso `p : mk y ≅ mk z`, surjectivity of the fixed-frame
monodromy onto `Pₙ` transports from `z` to `y`: conjugation by `cubeReadHom p.hom` fixes the normal
subgroup `Pₙ`. -/
theorem autToBraid_range_pure {y z : ConcCat (□n)}
    (p : (FreeGroupoid.mk y : ConcGrpd (□n)) ≅ FreeGroupoid.mk z)
    (hz : ∀ q : Braid n, q ∈ PureBraid n →
      ∃ c : ConcBraid (□n) z, autToBraid (cubeRead n) (FreeGroupoid.mk z) c = q) :
    ∀ q : Braid n, q ∈ PureBraid n →
      ∃ b : ConcBraid (□n) y, autToBraid (cubeRead n) (FreeGroupoid.mk y) b = q := by
  intro q hq
  have hnorm : cubeReadHom p.hom * q * (cubeReadHom p.hom)⁻¹ ∈ PureBraid n :=
    (inferInstance : (PureBraid n).Normal).conj_mem q hq (cubeReadHom p.hom)
  obtain ⟨c, hc⟩ := hz _ hnorm
  refine ⟨(p.conjAut).symm c, ?_⟩
  have hid := cubeRead_conjAut p ((p.conjAut).symm c)
  rw [MulEquiv.apply_symm_apply, hc] at hid
  exact (mul_left_cancel (mul_right_cancel hid)).symm

/-- **Surjectivity of the Salvetti pure monodromy.**  With connectivity of the `n`-event executions
(`hconn_conc`, an explicit hypothesis), `pureMonodromy n x` is onto `Pₙ`. -/
theorem pureMonodromy_surjective (n : ℕ) (hn : 0 < n) (x : Sal (braidCOM n))
    (hconn_conc : ∀ y z : ConcCat (□n), nEvents y = n → nEvents z = n →
      Nonempty ((FreeGroupoid.mk y : ConcGrpd (□n)) ⟶ FreeGroupoid.mk z)) :
    Function.Surjective (pureMonodromy n x) := by
  have hy₀ : nEvents ((braidSalEquiv n).functor.obj x) = n := nEvents_braidSalEquiv_obj n x
  have hz₀ : nEvents (seqExec (x₀ hn)) = n := eventObj_card_cube _
  obtain ⟨w⟩ := hconn_conc ((braidSalEquiv n).functor.obj x) (seqExec (x₀ hn)) hy₀ hz₀
  have p : (FreeGroupoid.mk ((braidSalEquiv n).functor.obj x) : ConcGrpd (□n))
      ≅ FreeGroupoid.mk (seqExec (x₀ hn)) :=
    (Groupoid.isoEquivHom (FreeGroupoid.mk ((braidSalEquiv n).functor.obj x))
      (FreeGroupoid.mk (seqExec (x₀ hn)))).symm w
  have hZ := autToBraid_surjective_of_concPure (seqExec (x₀ hn)) hz₀
    (concPureBraidHom_surjective n hn)
  have hY := autToBraid_range_pure p hZ
  intro q
  obtain ⟨b, hb⟩ := hY q.val q.property
  refine ⟨(salVertexMulEquiv n x).symm b, Subgroup.subtype_injective _ ?_⟩
  rw [pureMonodromy_subtype_eq x, MulEquiv.apply_symm_apply]
  exact hb

end CubeChains
