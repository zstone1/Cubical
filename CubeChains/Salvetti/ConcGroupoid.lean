import CubeChains.Salvetti.SalWedge
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Endomorphism

/-!
# Salvetti/ConcGroupoid — the concurrency braid groupoid

`Int(Lines K)` is the category whose objects are executions of `K` (a cube chain plus a total
order of each bead's concurrent events) and whose morphisms refine one execution into another.
Its groupoidification `ConcGrpd K = FreeGroupoid (Int(Lines K))` — equivalently (Gabriel–Zisman)
the fundamental groupoid of the nerve — is the **concurrency braid groupoid** of `K`.

Transporting `braidSalEquiv` / `braidSerialSalEquiv` along `freeGroupoidCongr` identifies it, for
a cube or a serial wedge, with the free groupoid on the Salvetti poset of the braid arrangement.
-/

open CategoryTheory

universe v v' u u'

namespace CategoryTheory

namespace FreeGroupoid

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- `map` sends a natural iso of functors to a natural iso of the mapped functors.  The whiskered
iso has type `of C ⋙ map F ≅ of C ⋙ map G` only up to the *equality* `of_comp_map`. -/
noncomputable def mapIso {F G : C ⥤ D} (e : F ≅ G) : map F ≅ map G :=
  liftNatIso (map F) (map G) (Functor.isoWhiskerRight e (of D))

end FreeGroupoid

/-- `FreeGroupoid` preserves equivalences: it is 2-functorial, `map_id`/`map_comp` being
equalities, so the unit/counit transport with no coherence debt (`Equivalence.mk` adjointifies). -/
noncomputable def freeGroupoidCongr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : FreeGroupoid C ≌ FreeGroupoid D :=
  Equivalence.mk (FreeGroupoid.map e.functor) (FreeGroupoid.map e.inverse)
    ((FreeGroupoid.mapId C).symm ≪≫ FreeGroupoid.mapIso e.unitIso
      ≪≫ FreeGroupoid.mapComp e.functor e.inverse)
    ((FreeGroupoid.mapComp e.inverse e.functor).symm ≪≫ FreeGroupoid.mapIso e.counitIso
      ≪≫ FreeGroupoid.mapId D)

end CategoryTheory

namespace CubeChains

/-- The **concurrency category** of `K` (the global Salvetti complex `Int(Lines K)`): an object is
a cube chain of `K` together with a total order of each bead's events. -/
abbrev ConcCat (K : BPSet) : Type _ := (Lines K).Elements

/-- The **concurrency braid groupoid** of `K`: the groupoidification of `ConcCat K`, i.e. the
fundamental groupoid of its nerve.  A morphism deforms one execution of `K` into another through
concurrent events. -/
abbrev ConcGrpd (K : BPSet) : Type _ := FreeGroupoid (ConcCat K)

/-- The braid arrangement computes the concurrency braid groupoid of the `n`-cube. -/
noncomputable def concCubeEquiv (n : ℕ) : FreeGroupoid (Sal (braidCOM n)) ≌ ConcGrpd (□n) :=
  freeGroupoidCongr (braidSalEquiv n)

/-- The serial-wedge version of `concCubeEquiv`. -/
noncomputable def concWedgeEquiv (dims : List ℕ+) :
    FreeGroupoid (Sal (braidDirectSum dims)) ≌ ConcGrpd (⋁dims) :=
  freeGroupoidCongr (braidSerialSalEquiv dims)

/-- The **concurrency braid group** of `K` at an execution `x`: the vertex group of `ConcGrpd K`.
By Salvetti's theorem `|N (Sal (braidCOM n))|` is the ordered configuration space of `n` points in
`ℂ`, so for `K = □ⁿ` this group is the pure braid group `P n`. -/
abbrev ConcBraid (K : BPSet) (x : ConcCat K) : Type _ := Aut (FreeGroupoid.mk x)

/-- The vertex group of `FreeGroupoid (Sal (braidCOM n))` — the pure braid group `P n` by
Salvetti's theorem (the nerve of `Sal (braidCOM n)` models the ordered configuration space of `n`
points in `ℂ`). -/
abbrev PureBraid (n : ℕ) (x : Sal (braidCOM n)) : Type _ := Aut (FreeGroupoid.mk x)

/-- Vertex groups transport along `concCubeEquiv`: the concurrency braid group of `□ⁿ` at an
execution coming from the Salvetti cell `x` is the corresponding braid vertex group. -/
noncomputable def pureBraidMulEquiv (n : ℕ) (x : Sal (braidCOM n)) :
    PureBraid n x ≃* ConcBraid (□n) ((braidSalEquiv n).functor.obj x) :=
  (concCubeEquiv n).fullyFaithfulFunctor.autMulEquivOfFullyFaithful (FreeGroupoid.mk x)

end CubeChains
