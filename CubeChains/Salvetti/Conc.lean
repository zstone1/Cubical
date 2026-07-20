import CubeChains.Salvetti.BraidIso
import CubeChains.Braid.Category
import CubeChains.Braid.SalvettiConstruction
import Mathlib.CategoryTheory.Whiskering

/-!
# Salvetti/Conc — the concurrency braid groupoid and its braid functor on `□ⁿ`

`Conc K` is the free groupoid on the executions `ConcPos K`: the braiding is *created* here, by
formally inverting the chain refinements.  For the standard cube the braid functor is transported
from Salvetti along `braidSalEquiv`, so faithfulness follows from Salvetti's asphericity.

    Ch⋆ (□ⁿ) ←≌── Sal(braidCOM n) ──salvettiGrading──→ SingleObj (Braid n)
-/

open CategoryTheory

noncomputable section

namespace CategoryTheory.FreeGroupoid

/-! ### Transporting faithfulness along `FreeGroupoid.map`

`map` is strictly functorial (`map_id`/`map_comp` are equalities), so `map e.inverse` retracts onto
the identity on the nose and only the natural-isomorphism step needs proving.  Mathlib gets here
generically — `of C` is a localization at `⊤`, and `Localization.of_equivalences` transports
localizations along equivalences — but that costs more plumbing than the strictness needs. -/

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- `map` sends a natural isomorphism to one, since `of C ⋙ map F = F ⋙ of D` on the nose. -/
private def mapNatIso {F G : C ⥤ D} (τ : F ≅ G) : map F ≅ map G :=
  liftNatIso _ _ (Functor.isoWhiskerRight τ (of D))

/-- `map e.inverse` retracts onto the identity, so it is faithful. -/
instance faithful_map_inverse (e : C ≌ D) : (map e.inverse).Faithful :=
  Functor.Faithful.of_comp_iso (G := map e.functor) (H := 𝟭 (FreeGroupoid D))
    (eqToIso (map_comp e.inverse e.functor).symm ≪≫ mapNatIso e.counitIso ≪≫ eqToIso (map_id D))

end CategoryTheory.FreeGroupoid

namespace CubeChains

/-- **The positive concurrency category**: executions of `K`, refinements not yet inverted. -/
abbrev ConcPos (K : BPSet) : Type _ := Ch⋆ K

/-- **The concurrency braid groupoid**: executions of `K`, with every refinement inverted. -/
abbrev Conc (K : BPSet) : Type _ := FreeGroupoid (ConcPos K)

/-- The braid word of an execution edge of the cube, read through Salvetti. -/
def cubeBraidPos (n : ℕ) : ConcPos (□n) ⥤ SingleObj (Braid n) :=
  (braidSalEquiv n).inverse ⋙ salvettiGrading n

/-- `cubeBraidPos` with its strand count remembered. -/
def cubeBraidGraded (n : ℕ) : ConcPos (□n) ⥤ Braids :=
  cubeBraidPos n ⋙ braidIncl n

/-- **The braid functor on the concurrency groupoid of the cube.** -/
def cubeBraid (n : ℕ) : Conc (□n) ⥤ SingleObj (Braid n) :=
  FreeGroupoid.lift (cubeBraidPos n)

/-- `cubeBraid` is the Salvetti construction transported along `braidSalEquiv`. -/
theorem cubeBraid_eq (n : ℕ) :
    cubeBraid n = FreeGroupoid.map (braidSalEquiv n).inverse ⋙ salvettiConstruction n :=
  (FreeGroupoid.map_comp_lift _ _).symm

/-- **Salvetti's asphericity, transported**: the braid functor on `Conc (□ⁿ)` is faithful. -/
theorem cubeBraid_faithful (n : ℕ) : (cubeBraid n).Faithful := by
  haveI := salvettiConstruction_faithful n
  haveI : (FreeGroupoid.map (braidSalEquiv n).inverse).Faithful :=
    FreeGroupoid.faithful_map_inverse (braidSalEquiv n)
  rw [cubeBraid_eq]
  exact Functor.Faithful.comp (FreeGroupoid.map (braidSalEquiv n).inverse)
    (salvettiConstruction n)

/-- Executions of `□ⁿ` all sit over `n` strands. -/
@[simp] theorem cubeBraidGraded_obj (n : ℕ) (x : ConcPos (□n)) :
    (cubeBraidGraded n).obj x = strands n := rfl

end CubeChains

end
