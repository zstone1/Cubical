import CubeChains.Foundations.Cylinder
import CubeChains.Cobordisms.Cospan

/-!
# Cobordisms/Collar — collars on the cylinder (M1, the collar part)

A **collar** is the "thickened boundary" datum (C4) of a directed cobordism: rather
than a bare boundary leg `i : X ⟶ W`, a collar records a monic *cylinder*
`Cyl X ↪ W` whose appropriate end recovers `i`.  Geometrically `i = X ⊗ {0} → W` is
thickened to a neighbourhood `X ⊗ □¹ ↪ W`.

We provide:

* `SourceCollar i` — a mono `Cyl X ↪ W` whose **bottom** end (`cylEnd false`)
  recovers a source leg `i : X ⟶ W`;
* `SinkCollar j` — dually, a mono `Cyl Y ↪ W` whose **top** end (`cylEnd true`)
  recovers a sink leg `j : Y ⟶ W`;
* `SourceCollar.leg_mono` / `SinkCollar.leg_mono` — a collared leg is automatically
  mono (a mono end composed with a mono collar);
* the **canonical collars on the cylinder** (M1: "the cylinder carries canonical
  source/sink collars"): for the identity cobordism `Cyl X`, the identity
  `𝟙 (Cyl.obj X)` is both a source collar of `cylEnd false X` and a sink collar of
  `cylEnd true X`;
* the **cylinder cospan** `cylCospan X : Cospan X X` — the underlying cospan of the
  identity cobordism, with disjoint legs (`cylCospan_legsDisjoint`).

**Layer:** Cobordisms.  **Imports:** `Foundations.Cylinder` (the geometric cylinder
`Cyl`, the two ends `cylEnd`, their monos + disjointness), `Cobordisms.Cospan` (the
cospan backbone).
-/

set_option relaxedAutoImplicit false

open CategoryTheory

namespace PrecubicalSet

open Cylinder

variable {X Y W : PrecubicalSet}

/-! ### Source and sink collars -/

/-- A **source collar** of a source leg `i : X ⟶ W` is a monic cylinder
`Cyl X ↪ W` whose **bottom** end (`cylEnd false`, the `δ⁰` inclusion `X ⊗ {0}`)
recovers `i`.  This is the thickened-boundary datum C4 on the source side. -/
structure SourceCollar (i : X ⟶ W) where
  /-- The collar: a map of the geometric cylinder of `X` into `W`. -/
  collar : Cyl.obj X ⟶ W
  /-- The collar is a monomorphism. -/
  [mono : Mono collar]
  /-- The bottom end of the collar recovers the source leg `i`. -/
  bottom : cylEnd false X ≫ collar = i

/-- A **sink collar** of a sink leg `j : Y ⟶ W` is a monic cylinder `Cyl Y ↪ W`
whose **top** end (`cylEnd true`, the `δ¹` inclusion `Y ⊗ {1}`) recovers `j`.  This
is the thickened-boundary datum C4 on the sink side. -/
structure SinkCollar (j : Y ⟶ W) where
  /-- The collar: a map of the geometric cylinder of `Y` into `W`. -/
  collar : Cyl.obj Y ⟶ W
  /-- The collar is a monomorphism. -/
  [mono : Mono collar]
  /-- The top end of the collar recovers the sink leg `j`. -/
  top : cylEnd true Y ≫ collar = j

attribute [instance] SourceCollar.mono SinkCollar.mono

namespace SourceCollar

/-- A collared **source leg is mono**: it is the bottom end (mono) composed with the
collar (mono). -/
theorem leg_mono {i : X ⟶ W} (κ : SourceCollar i) : Mono i := by
  rw [← κ.bottom]
  exact mono_comp _ _

end SourceCollar

namespace SinkCollar

/-- A collared **sink leg is mono**: it is the top end (mono) composed with the
collar (mono). -/
theorem leg_mono {j : Y ⟶ W} (κ : SinkCollar j) : Mono j := by
  rw [← κ.top]
  exact mono_comp _ _

end SinkCollar

/-! ### The cylinder carries canonical collars (M1)

For the identity cobordism `Cyl X` (the cospan `X ⇒ X` via the two ends), the
identity `𝟙 (Cyl.obj X)` is *both* a source collar of `cylEnd false X` and a sink
collar of `cylEnd true X`: thickening either end of the cylinder by the cylinder
itself is the identity. -/

/-- **The cylinder's canonical source collar.**  The identity `𝟙 (Cyl.obj X)` is a
source collar of the bottom end `cylEnd false X`. -/
def cylSourceCollar (X : PrecubicalSet) : SourceCollar (cylEnd false X) where
  collar := 𝟙 (Cyl.obj X)
  mono := inferInstance
  bottom := Category.comp_id _

/-- **The cylinder's canonical sink collar.**  The identity `𝟙 (Cyl.obj X)` is a
sink collar of the top end `cylEnd true X`. -/
def cylSinkCollar (X : PrecubicalSet) : SinkCollar (cylEnd true X) where
  collar := 𝟙 (Cyl.obj X)
  mono := inferInstance
  top := Category.comp_id _

@[simp] theorem cylSourceCollar_collar (X : PrecubicalSet) :
    (cylSourceCollar X).collar = 𝟙 (Cyl.obj X) := rfl

@[simp] theorem cylSinkCollar_collar (X : PrecubicalSet) :
    (cylSinkCollar X).collar = 𝟙 (Cyl.obj X) := rfl

/-! ### The cylinder cospan

The underlying cospan of the identity cobordism `Cyl X`: apex `Cyl X`, source leg the
bottom end, sink leg the top end.  Its legs are mono (`cylEnd_mono`) and disjoint
(`cylEnd_disjoint`). -/

/-- **The cylinder cospan** `X ⇒ X`: apex `Cyl X`, left leg `cylEnd false X`
(bottom), right leg `cylEnd true X` (top).  Both ends are mono. -/
noncomputable def cylCospan (X : PrecubicalSet) : Cospan X X :=
  Cospan.of (cylEnd false X) (cylEnd true X)

@[simp] theorem cylCospan_mid (X : PrecubicalSet) : (cylCospan X).mid = Cyl.obj X := rfl

@[simp] theorem cylCospan_inl (X : PrecubicalSet) :
    (cylCospan X).inl = cylEnd false X := rfl

@[simp] theorem cylCospan_inr (X : PrecubicalSet) :
    (cylCospan X).inr = cylEnd true X := rfl

/-- **The cylinder cospan has disjoint legs.**  The two ends of the cylinder land in
the disjoint `bot`/`top` summands, so no cell is in both images
(`cylEnd_disjoint`). -/
theorem cylCospan_legsDisjoint (X : PrecubicalSet) : (cylCospan X).LegsDisjoint := by
  intro n x y h
  rw [cylCospan_inl, cylCospan_inr] at h
  exact cylEnd_disjoint X x y h

end PrecubicalSet
