import CubeChains.Braid.Naturality
import CubeChains.Braid.CubeIso

/-!
# Braid/CubeViaZ — the cube's braid groupoid functor factors through the terminal set

`braidGrpd` reads only an execution's event count and event permutation, both blind to relabelling
(`braidGrading_factor`), so on the free groupoid the cube's braid functor is the terminal-set one
precomposed with the push `FreeGroupoid.map (concToZ (□n))`.  The mechanism is the universal
property (`FreeGroupoid.map_comp_lift`): `lift` turns a `⋙` of the underlying grading into a `map ⋙`
of the lifts.

On vertex groups this exposes the comparison map `concToZAut` through which `concBraidHom (□n)`
factors — the concurrency braid of a cube loop is the braid of its image loop in `Zbp`.
-/

open CategoryTheory

namespace CubeChains

/-! ## The groupoid factorization -/

/-- **`braidGrpd` factors through the terminal set.**  `braidGrpd K` is the terminal-set braid
functor precomposed with the push of executions to `Zbp`.  A `lift` of a `⋙` is the `map ⋙` of the
pieces (`map_comp_lift`); the grading itself factors by `braidGrading_factor`. -/
theorem braidGrpd_factor (K : BPSet) :
    braidGrpd K = FreeGroupoid.map (concToZ K) ⋙ braidGrpd Zbp := by
  change FreeGroupoid.lift (braidGrading K)
      = FreeGroupoid.map (concToZ K) ⋙ FreeGroupoid.lift (braidGrading Zbp)
  rw [braidGrading_factor K, FreeGroupoid.map_comp_lift]

/-- The `n`-cube instance of `braidGrpd_factor`: `ConcCat (□n)`'s braids come from `Zbp`. -/
theorem cube_braidGrpd_factor (n : ℕ) :
    braidGrpd (□n) = FreeGroupoid.map (concToZ (□n)) ⋙ braidGrpd Zbp :=
  braidGrpd_factor (□n)

/-! ## The vertex-group factorization

`Functor.mapAut` is functorial in the functor: `(F ⋙ G).mapAut X = (G.mapAut (F.obj X)).comp
(F.mapAut X)` definitionally (functor composition is defeq on maps, `MonoidHom.comp` is defeq
associative).  Combined with `braidGrpd_factor` — via `congr_arg_heq`, since `mapAut`'s codomain is
functor-dependent — the cube's vertex-group map factors through the push-to-`Zbp` comparison map. -/

/-- The comparison map `φ_x`: push a concurrency loop of `□n` at `x` to a loop of `Zbp` at its
image.  Its codomain object `mk ((concToZ (□n)).obj x)` is `map (concToZ (□n)) |>.obj (mk x)`. -/
noncomputable def concToZAut (n : ℕ) (x : ConcCat (□n)) :
    ConcBraid (□n) x →* ConcBraid Zbp ((concToZ (□n)).obj x) :=
  (FreeGroupoid.map (concToZ (□n))).mapAut (FreeGroupoid.mk x)

/-- The terminal-set analogue of `concBraidHom`: a `Zbp` loop's braid, on its `nEvents` events. -/
noncomputable def zbpBraidHom (y : ConcCat Zbp) : ConcBraid Zbp y →* Braid (nEvents y) :=
  (autStrandsBraid (nEvents y)).toMonoidHom.comp ((braidGrpd Zbp).mapAut (FreeGroupoid.mk y))

/-- **The cube's vertex-group map factors through `Zbp`.**  `braidGrpd (□n)`'s automorphism map at
`x` is the terminal-set map at the image loop, precomposed with the comparison map. -/
theorem braidGrpd_mapAut_factor (n : ℕ) (x : ConcCat (□n)) :
    (braidGrpd (□n)).mapAut (FreeGroupoid.mk x)
      = ((braidGrpd Zbp).mapAut (FreeGroupoid.mk ((concToZ (□n)).obj x))).comp
          (concToZAut n x) :=
  eq_of_heq (congr_arg_heq
    (fun K : ConcGrpd (□n) ⥤ Braids => K.mapAut (FreeGroupoid.mk x)) (braidGrpd_factor (□n)))

/-- **`concBraidHom (□n)` factors through the comparison map.**  The concurrency braid of a cube
loop at `x` is the braid of its image loop in `Zbp`. -/
theorem concBraidHom_factor (n : ℕ) (x : ConcCat (□n)) :
    concBraidHom n x = (zbpBraidHom ((concToZ (□n)).obj x)).comp (concToZAut n x) := by
  change (autStrandsBraid (nEvents x)).toMonoidHom.comp
      ((braidGrpd (□n)).mapAut (FreeGroupoid.mk x)) = _
  rw [braidGrpd_mapAut_factor n x]
  rfl

end CubeChains
