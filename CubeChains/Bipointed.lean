import CubeChains.Box
import CubeChains.Representable
import Mathlib.CategoryTheory.Endomorphism

/-!
# Bi-pointed precubical sets (over the topos `PrecubicalSet`)

We now work in `PrecubicalSet = Boxᵒᵖ ⥤ Type` (the presheaf topos).  The
`n`-cells of a precubical set `X` are its value `X.obj [n]`.  A *bi-pointed*
precubical set is `X` with two chosen `0`-cells `init`, `final`; morphisms are
natural transformations preserving them.  `Aut K` is then mathlib's `Aut` in
this category, a group for free.
-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-- The `n`-cells of a precubical set: its value at the object `[n]` of `Box`. -/
abbrev cells (X : PrecubicalSet) (n : ℕ) : Type := X.obj (op (Box.ob n))

/-- The initial-vertex inclusion `[0] ⟶ [n]` in `Box` (the all-`0` vertex). -/
noncomputable def initVertexMap (n : ℕ) : Box.ob 0 ⟶ Box.ob n :=
  StdCube.canonicalMap (StdCube.constVertex n false)

/-- The final-vertex inclusion `[0] ⟶ [n]` in `Box` (the all-`1` vertex). -/
noncomputable def finalVertexMap (n : ℕ) : Box.ob 0 ⟶ Box.ob n :=
  StdCube.canonicalMap (StdCube.constVertex n true)

/-- The source extremal vertex `vertex₀ c` of an `n`-cell `c`: pull `c` back along
the initial-vertex inclusion. -/
noncomputable def vertex₀ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) : X.cells 0 :=
  X.map (initVertexMap n).op c

/-- The target extremal vertex `vertex₁ c` of an `n`-cell `c`. -/
noncomputable def vertex₁ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) : X.cells 0 :=
  X.map (finalVertexMap n).op c

end PrecubicalSet

/-- A bi-pointed precubical set: a precubical set with two chosen `0`-cells. -/
structure BPSet where
  /-- The underlying precubical set (presheaf). -/
  toPsh : PrecubicalSet
  /-- The initial vertex. -/
  init : toPsh.cells 0
  /-- The final vertex. -/
  final : toPsh.cells 0

namespace BPSet

/-- A morphism of bi-pointed precubical sets: a natural transformation of the
underlying presheaves preserving `init` and `final`. -/
@[ext]
structure Hom (K L : BPSet) where
  /-- The underlying natural transformation. -/
  hom : K.toPsh ⟶ L.toPsh
  /-- Preservation of the initial vertex. -/
  app_init : hom.app (op (Box.ob 0)) K.init = L.init
  /-- Preservation of the final vertex. -/
  app_final : hom.app (op (Box.ob 0)) K.final = L.final

namespace Hom

variable {K L M : BPSet}

/-- The identity bi-pointed morphism. -/
protected def id (K : BPSet) : Hom K K where
  hom := 𝟙 _
  app_init := rfl
  app_final := rfl

/-- Composition of bi-pointed morphisms. -/
protected def comp (f : Hom K L) (g : Hom L M) : Hom K M where
  hom := f.hom ≫ g.hom
  app_init := by rw [NatTrans.comp_app, types_comp_apply, f.app_init, g.app_init]
  app_final := by rw [NatTrans.comp_app, types_comp_apply, f.app_final, g.app_final]

end Hom

instance : Category BPSet where
  Hom K L := Hom K L
  id K := Hom.id K
  comp f g := Hom.comp f g

@[ext]
theorem hom_ext {K L : BPSet} {f g : K ⟶ L} (h : (f : Hom K L).hom = (g : Hom K L).hom) :
    f = g := Hom.ext h

@[simp]
theorem id_hom (K : BPSet) : (𝟙 K : Hom K K).hom = 𝟙 K.toPsh := rfl

@[simp]
theorem comp_hom {K L M : BPSet} (f : K ⟶ L) (g : L ⟶ M) :
    (f ≫ g : Hom K M).hom = (f : Hom K L).hom ≫ (g : Hom L M).hom := rfl

end BPSet
