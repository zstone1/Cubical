import CubeChains.Foundations.Cylinder
import CubeChains.Cobordisms.Cospan

/-!
# Cobordisms/Collar — collars on the cylinder (M1, the collar part)

A **collar** is the "thickened boundary" datum (C4) of a directed cobordism: rather
than a bare boundary leg `i : X ⟶ W`, a collar records a monic *cylinder*
`Cyl X ↪ W` whose appropriate end recovers `i`.  Geometrically `i = X ⊗ {0} → W` is
thickened to a neighbourhood `X ⊗ □¹ ↪ W`.

Source and sink collars differ *only* in **which end** recovers the leg, so we package
them as a single `Bool`-indexed structure `Collar side i`:

* `Collar side i` — a mono `Cyl X ↪ W` whose `side` end (`cylEnd side`) recovers a leg
  `i : X ⟶ W` (`endEq`).  `side = false` is the **bottom** (source) end, `side = true`
  the **top** (sink) end;
* `SourceCollar i := Collar false i` / `SinkCollar j := Collar true j` — the
  side-specialized aliases (so `.collar`, `.mono`, `.endEq` all read through directly);
* `Collar.leg_mono` (with `SourceCollar.leg_mono` / `SinkCollar.leg_mono` aliases) — a
  collared leg is automatically mono (a mono end composed with a mono collar);
* the **canonical collars on the cylinder** (M1: "the cylinder carries canonical
  source/sink collars"): for the identity cobordism `Cyl X`, the identity
  `𝟙 (Cyl.obj X)` is a `Collar side (cylEnd side X)` for either `side` (`cylCollar`);
  `cylSourceCollar X` / `cylSinkCollar X` are the `false` / `true` specializations;
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

/-! ### Collars (the `Bool`-indexed datum) -/

/-- A **collar** of a leg `i : X ⟶ W` on the `side` end is a monic cylinder
`Cyl X ↪ W` whose `side` end (`cylEnd side`) recovers `i`.  `side = false` is the
**bottom** (`δ⁰` inclusion `X ⊗ {0}`, source side); `side = true` is the **top**
(`δ¹` inclusion `X ⊗ {1}`, sink side).  This is the thickened-boundary datum C4. -/
structure Collar (side : Bool) (i : X ⟶ W) where
  /-- The collar: a map of the geometric cylinder of `X` into `W`. -/
  collar : Cyl.obj X ⟶ W
  /-- The collar is a monomorphism. -/
  [mono : Mono collar]
  /-- The `side` end of the collar recovers the leg `i`. -/
  endEq : cylEnd side X ≫ collar = i

attribute [instance] Collar.mono

/-- A **source collar** of a source leg `i : X ⟶ W` is a collar on the **bottom** end
(`cylEnd false`, the `δ⁰` inclusion `X ⊗ {0}`).  Thin alias for `Collar false i`. -/
abbrev SourceCollar (i : X ⟶ W) := Collar false i

/-- A **sink collar** of a sink leg `j : Y ⟶ W` is a collar on the **top** end
(`cylEnd true`, the `δ¹` inclusion `Y ⊗ {1}`).  Thin alias for `Collar true j`. -/
abbrev SinkCollar (j : Y ⟶ W) := Collar true j

namespace Collar

/-- A collared **leg is mono**: it is the `side` end (mono) composed with the collar
(mono). -/
theorem leg_mono {side : Bool} {i : X ⟶ W} (κ : Collar side i) : Mono i := by
  rw [← κ.endEq]
  exact mono_comp _ _

end Collar

/-- A collared **source leg is mono** (the `side = false` specialization of
`Collar.leg_mono`). -/
theorem SourceCollar.leg_mono {i : X ⟶ W} (κ : SourceCollar i) : Mono i :=
  Collar.leg_mono κ

/-- A collared **sink leg is mono** (the `side = true` specialization of
`Collar.leg_mono`). -/
theorem SinkCollar.leg_mono {j : Y ⟶ W} (κ : SinkCollar j) : Mono j :=
  Collar.leg_mono κ

/-! ### The cylinder carries canonical collars (M1)

For the identity cobordism `Cyl X` (the cospan `X ⇒ X` via the two ends), the
identity `𝟙 (Cyl.obj X)` is a `Collar side (cylEnd side X)` for *either* `side`:
thickening either end of the cylinder by the cylinder itself is the identity. -/

/-- **The cylinder's canonical collar.**  The identity `𝟙 (Cyl.obj X)` is a collar of
the `side` end `cylEnd side X`. -/
def cylCollar (side : Bool) (X : PrecubicalSet) : Collar side (cylEnd side X) where
  collar := 𝟙 (Cyl.obj X)
  mono := inferInstance
  endEq := Category.comp_id _

/-- **The cylinder's canonical source collar** = `cylCollar false X`: the identity
`𝟙 (Cyl.obj X)` is a source collar of the bottom end `cylEnd false X`. -/
def cylSourceCollar (X : PrecubicalSet) : SourceCollar (cylEnd false X) := cylCollar false X

/-- **The cylinder's canonical sink collar** = `cylCollar true X`: the identity
`𝟙 (Cyl.obj X)` is a sink collar of the top end `cylEnd true X`. -/
def cylSinkCollar (X : PrecubicalSet) : SinkCollar (cylEnd true X) := cylCollar true X

@[simp] theorem cylCollar_collar (side : Bool) (X : PrecubicalSet) :
    (cylCollar side X).collar = 𝟙 (Cyl.obj X) := rfl

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
