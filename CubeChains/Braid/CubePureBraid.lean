import CubeChains.Braid.CubeIso
import CubeChains.Braid.SalvettiConstruction
import CubeChains.Salvetti.ConcGroupoid
import CubeChains.Salvetti.BraidSalObj
import CubeChains.Braid.Surjectivity
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Braid/CubePureBraid — the cube's concurrency braid group is the pure braid group

The Salvetti construction `salvettiConstruction n` (computable braid words, faithful by
`salvettiConstruction_faithful`) is identified with the geometric cube functor `braidGrpd (□n)`
read in the fixed `Fin n` frame (`readBraid`).  Faithfulness transports across the equivalence
`concCubeEquiv`, so `braidGrpd (□n) ⋙ readBraid n` is faithful; its `mapAut` is then injective, so
`concBraidHom n x` is injective for every cube execution.  With the green surjectivity
(`concPureBraidHom_surjective`) this gives the isomorphism `ConcBraid(□n) ≃* Pₙ`.

The single geometric input is `htarget`: a Salvetti edge's tope-crossing permutation equals the
event permutation of the corresponding cube refinement, read in the fixed frame.
-/

open CategoryTheory Equiv

namespace CubeChains

/-- The event count of a cube execution coming from a Salvetti cell is `n`. -/
theorem nEvents_braidSalEquiv_obj (n : ℕ) (a : Sal (braidCOM n)) :
    nEvents ((braidSalEquiv n).functor.obj a) = n :=
  eventObj_card_cube _

/-- The braid grading of a cube refinement, collapsed to `SingleObj (Braid n)`: the event
permutation of `f` read in the fixed frame `Fin n`.  Mirrors `braidGrading_comp_readPerm`. -/
theorem braidGrading_readBraid_map {n : ℕ} {x y : ConcCat (□n)} (f : x ⟶ y) (h : nEvents x = n) :
    (braidGrading (□n) ⋙ readBraid n).map f = ofPerm ((finCongr h).permCongr (evPerm' f)) := by
  rw [Functor.comp_map, braidGrading_map_eq]
  erw [Functor.map_comp, readBraid_map_eqToHom, Category.comp_id, readBraid_map_braidHom]
  rw [braidSelfHom_eq n h, braidCast_ofPerm]

section
variable (n : ℕ)
variable (htarget : ∀ (a b : Sal (braidCOM n)) (hab : a ≤ b),
    crossPerm a b
      = (finCongr (nEvents_braidSalEquiv_obj n a)).permCongr
          (evPerm' ((braidSalEquiv n).functor.map (homOfLE hab))))
include htarget

/-- **The computable Salvetti grading is the geometric cube grading**, read in the fixed `Fin n`
frame.  Objects both land at `star`; a Salvetti edge `a ⟶ b` goes to `ofPerm (crossPerm a b)`,
which `htarget` identifies with the event permutation of the image refinement. -/
theorem salvettiGrading_eq :
    salvettiGrading n = (braidSalEquiv n).functor ⋙ braidGrading (□n) ⋙ readBraid n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun a b f => ?_
  change ofPerm (crossPerm a b)
      = 𝟙 _ ≫ (braidGrading (□n) ⋙ readBraid n).map
          ((braidSalEquiv n).functor.map (homOfLE (leOfHom f))) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id,
      braidGrading_readBraid_map ((braidSalEquiv n).functor.map (homOfLE (leOfHom f)))
        (nEvents_braidSalEquiv_obj n a),
      htarget a b (leOfHom f)]

/-- **The Salvetti construction factors as the geometric cube functor read in `Fin n`.**  The
free-groupoid lift of `salvettiGrading` is the equivalence `concCubeEquiv` followed by
`braidGrpd (□n) ⋙ readBraid n`. -/
theorem salvettiConstruction_eq :
    salvettiConstruction n = (concCubeEquiv n).functor ⋙ braidGrpd (□n) ⋙ readBraid n := by
  show FreeGroupoid.lift (salvettiGrading n) = _
  rw [salvettiGrading_eq n htarget, ← FreeGroupoid.map_comp_lift, FreeGroupoid.lift_comp]
  rfl

/-- **`braidGrpd (□n) ⋙ readBraid n` is faithful.**  Faithfulness of `salvettiConstruction`
(Salvetti's asphericity axiom) transports across the equivalence `concCubeEquiv`. -/
theorem readBraid_braidGrpd_faithful : (braidGrpd (□n) ⋙ readBraid n).Faithful := by
  haveI hsf : (salvettiConstruction n).Faithful := salvettiConstruction_faithful n
  rw [salvettiConstruction_eq n htarget] at hsf
  exact Functor.Faithful.of_iso
    ((Functor.associator (concCubeEquiv n).inverse (concCubeEquiv n).functor
        (braidGrpd (□n) ⋙ readBraid n)).symm
      ≪≫ Functor.isoWhiskerRight (concCubeEquiv n).counitIso (braidGrpd (□n) ⋙ readBraid n)
      ≪≫ (braidGrpd (□n) ⋙ readBraid n).leftUnitor)

/-- **`concBraidHom n x` is injective** for every cube execution.  It is `autStrandsBraid` (an
isomorphism) composed with `braidGrpd (□n)`'s `mapAut`, which is injective because the faithful
functor `braidGrpd (□n) ⋙ readBraid n` factors its `mapAut` through it. -/
theorem concBraidHom_injective (x : ConcCat (□n)) :
    Function.Injective (concBraidHom n x) := by
  haveI := readBraid_braidGrpd_faithful n htarget
  have hf : Function.Injective ⇑((braidGrpd (□n)).mapAut (FreeGroupoid.mk x)) := by
    intro a b hab
    have hcomp : ((braidGrpd (□n) ⋙ readBraid n).mapAut (FreeGroupoid.mk x)) a
        = ((braidGrpd (□n) ⋙ readBraid n).mapAut (FreeGroupoid.mk x)) b := by
      change ((readBraid n).mapAut ((braidGrpd (□n)).obj (FreeGroupoid.mk x)))
          (((braidGrpd (□n)).mapAut (FreeGroupoid.mk x)) a)
        = ((readBraid n).mapAut ((braidGrpd (□n)).obj (FreeGroupoid.mk x)))
          (((braidGrpd (□n)).mapAut (FreeGroupoid.mk x)) b)
      rw [hab]
    exact (braidGrpd (□n) ⋙ readBraid n).mapIso_injective hcomp
  intro a b hab
  apply hf
  change (autStrandsBraid (nEvents x)) ((braidGrpd (□n)).mapAut (FreeGroupoid.mk x) a)
      = (autStrandsBraid (nEvents x)) ((braidGrpd (□n)).mapAut (FreeGroupoid.mk x) b) at hab
  exact (autStrandsBraid (nEvents x)).injective hab

end

/-- Recast the pure braids along an equality of strand counts. -/
noncomputable def pureBraidCast {m k : ℕ} (h : m = k) : PureBraid m ≃* PureBraid k := by
  subst h; exact MulEquiv.refl _

/-- **The cube's concurrency braid group is the pure braid group.**  `concPureBraidHom` at the
single-cube run is injective (`concBraidHom_injective`, via codomain restriction) and surjective
(`concPureBraidHom_surjective`), hence a group isomorphism `ConcBraid(□n) ≃* Pₙ`. -/
noncomputable def cube_concBraid_mulEquiv_pureBraid (n : ℕ)
    (htarget : ∀ (a b : Sal (braidCOM n)) (hab : a ≤ b),
      crossPerm a b
        = (finCongr (nEvents_braidSalEquiv_obj n a)).permCongr
            (evPerm' ((braidSalEquiv n).functor.map (homOfLE hab))))
    (hn : 0 < n) :
    ConcBraid (□n) (seqExec (x₀ hn)) ≃* PureBraid n := by
  have hinj : Function.Injective (concPureBraidHom n (seqExec (x₀ hn))) := by
    intro a b h
    exact concBraidHom_injective n htarget (seqExec (x₀ hn)) (Subtype.ext_iff.mp h)
  have hsurj : Function.Surjective (concPureBraidHom n (seqExec (x₀ hn))) :=
    concPureBraidHom_surjective n hn
  have hN : nEvents (seqExec (x₀ hn)) = n := eventObj_card_cube _
  exact (MulEquiv.ofBijective (concPureBraidHom n (seqExec (x₀ hn))) ⟨hinj, hsurj⟩).trans
    (pureBraidCast hN)

end CubeChains
