import CubeChains.Foundations.Box
import CubeChains.Foundations.Representable
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Yoneda

/-!
# Foundations/Bipointed

Bi-pointed precubical sets over the topos `PrecubicalSet = Boxᵒᵖ ⥤ Type`: `BPSet`
(a presheaf `X` with two chosen `0`-cells `init`, `final`) + `Hom` + category, plus
`cells`, `vertex₀/₁`, `faceMap`/`cubeMap`, `init/finalVertexMap` and `IsAltitude`.

`faceMap`/`cubeMap` are built from the cube Yoneda lemma; `Aut K` is mathlib's `Aut`
in this category, a group for free.
-/

open CategoryTheory Opposite StdCube

/-- `φ⟪n⟫` — the component of a presheaf map at dimension `n`, i.e. `φ.app (op ▫n)`.
It is *notation*, not a definition, so the elaborated term is unchanged and `NatTrans` lemmas
(`naturality_apply`, …) still fire through it. -/
notation:max f "⟪" n "⟫" => NatTrans.app f (Opposite.op (Box.ob n))

namespace PrecubicalSet

/-- The `n`-cells of a precubical set: its value at the object `[n]` of `Box`. -/
abbrev cells (X : PrecubicalSet) (n : ℕ) : Type := X.obj (op ▫n)

end PrecubicalSet

/-! ### Evaluating an equation of presheaf maps at a cell

`≫` in the functor category is componentwise, but `ConcreteCategory` bundling means
`(f ≫ g)⟪m⟫ c` is not syntactically `g⟪m⟫ (f⟪m⟫ c)`.  These two peel the composite so callers
never hand-roll the `congrArg` + `simpa only [NatTrans.comp_app, types_comp_apply]` dance. -/

theorem comp_app_cell {A B C : PrecubicalSet} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C}
    (e : f ≫ g = h) (m : ℕ) (c : A.cells m) : g⟪m⟫ (f⟪m⟫ c) = h⟪m⟫ c := by
  have hc := congrArg (fun t : A ⟶ C => t⟪m⟫ c) e
  simpa only [NatTrans.comp_app, types_comp_apply] using hc

theorem comp_app_cell₂ {A B B' C : PrecubicalSet} {f : A ⟶ B} {g : B ⟶ C} {f' : A ⟶ B'}
    {g' : B' ⟶ C} (e : f ≫ g = f' ≫ g') (m : ℕ) (c : A.cells m) :
    g⟪m⟫ (f⟪m⟫ c) = g'⟪m⟫ (f'⟪m⟫ c) :=
  comp_app_cell e m c

namespace PrecubicalSet

/-- The face map `cells (n+1) → cells n` of a precubical set: pull back along the
coface. -/
def faceMap (X : PrecubicalSet) (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (c : X.cells (n + 1)) : X.cells n :=
  X.map (coface ε i).op c

/-- The canonical map `□ⁿ ⟶ X` classifying an `n`-cell `c` (Yoneda). -/
def cubeMap (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    yoneda.obj ▫n ⟶ X :=
  yonedaEquiv.symm c

/-- The initial-vertex inclusion `[0] ⟶ [n]` in `Box` (the all-`0` vertex). -/
def initVertexMap (n : ℕ) : ▫0 ⟶ ▫n :=
  canonicalMap (constVertex n false)

/-- The final-vertex inclusion `[0] ⟶ [n]` in `Box` (the all-`1` vertex). -/
def finalVertexMap (n : ℕ) : ▫0 ⟶ ▫n :=
  canonicalMap (constVertex n true)

/-- The source extremal vertex `vertex₀ c` of an `n`-cell `c`: pull `c` back along
the initial-vertex inclusion. -/
def vertex₀ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) : X.cells 0 :=
  X.map (initVertexMap n).op c

/-- The target extremal vertex `vertex₁ c` of an `n`-cell `c`. -/
def vertex₁ (X : PrecubicalSet) {n : ℕ} (c : X.cells n) : X.cells 0 :=
  X.map (finalVertexMap n).op c

/-! ### Vertices of Yoneda-classified cells and naturality

These general `PrecubicalSet`-level lemmas relate `vertex₀`/`vertex₁` to
`yonedaEquiv` and express naturality of a presheaf map (`BPSet`-level callers apply
them through `K.toPsh`). -/

/-- The source extremal vertex of a Yoneda-classified cell, computed by Yoneda
naturality: `vertex₀ (yonedaEquiv f) = f` evaluated at the initial-vertex map. -/
theorem vertex₀_yonedaEquiv {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj ▫n ⟶ K) :
    K.vertex₀ (yonedaEquiv f) = f⟪0⟫ (initVertexMap n) := by
  unfold vertex₀
  exact map_yonedaEquiv f (initVertexMap n)

/-- The target extremal vertex of a Yoneda-classified cell. -/
theorem vertex₁_yonedaEquiv {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj ▫n ⟶ K) :
    K.vertex₁ (yonedaEquiv f) = f⟪0⟫ (finalVertexMap n) := by
  unfold vertex₁
  exact map_yonedaEquiv f (finalVertexMap n)

/-- The source extremal vertex as the Yoneda class of the precomposed initial-vertex
inclusion (the morphism-level form used for vertex chases). -/
theorem vertex₀_eq {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj ▫n ⟶ K) :
    K.vertex₀ (yonedaEquiv f)
      = yonedaEquiv (yoneda.map (initVertexMap n) ≫ f) := by
  rw [vertex₀_yonedaEquiv, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- The target extremal vertex as the Yoneda class of the precomposed final-vertex
inclusion. -/
theorem vertex₁_eq {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj ▫n ⟶ K) :
    K.vertex₁ (yonedaEquiv f)
      = yonedaEquiv (yoneda.map (finalVertexMap n) ≫ f) := by
  rw [vertex₁_yonedaEquiv, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- A precubical map carries `vertex₀` to `vertex₀` (naturality of `φ` through the
initial-vertex inclusion). -/
theorem map_vertex₀ {K L : PrecubicalSet} (φ : K ⟶ L) {n : ℕ} (c : K.cells n) :
    φ⟪0⟫ (K.vertex₀ c) = L.vertex₀ (φ⟪n⟫ c) :=
  NatTrans.naturality_apply φ (initVertexMap n).op c

/-- A precubical map carries `vertex₁` to `vertex₁` (naturality of `φ` through the
final-vertex inclusion). -/
theorem map_vertex₁ {K L : PrecubicalSet} (φ : K ⟶ L) {n : ℕ} (c : K.cells n) :
    φ⟪0⟫ (K.vertex₁ c) = L.vertex₁ (φ⟪n⟫ c) :=
  NatTrans.naturality_apply φ (finalVertexMap n).op c

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

/-- The `n`-cells of a bi-pointed set — `K.toPsh.cells n`, said once. -/
abbrev cells (K : BPSet) (n : ℕ) : Type := K.toPsh.cells n

/-- Re-point `K` at a chosen pair of vertices.  The endpoints of a `BPSet` are a
*parameter*, not a commitment: everything indexed by `K` — `Ch`, `Lines` — is
read at other endpoints as `… (K.repoint u v)`.

`toPsh` is untouched, so `(K.repoint u v).cells n = K.cells n` by `rfl`, and re-pointing at
the original vertices is the identity (structure eta). -/
def repoint (K : BPSet) (u v : K.cells 0) : BPSet where
  toPsh := K.toPsh
  init := u
  final := v

@[simp] theorem repoint_toPsh (K : BPSet) (u v : K.cells 0) :
    (K.repoint u v).toPsh = K.toPsh := rfl

@[simp] theorem repoint_init (K : BPSet) (u v : K.cells 0) : (K.repoint u v).init = u := rfl

@[simp] theorem repoint_final (K : BPSet) (u v : K.cells 0) : (K.repoint u v).final = v := rfl

@[simp] theorem repoint_self (K : BPSet) : K.repoint K.init K.final = K := rfl

@[simp] theorem repoint_repoint (K : BPSet) (u v : K.cells 0) (u' v' : (K.repoint u v).cells 0) :
    (K.repoint u v).repoint u' v' = K.repoint u' v' := rfl

end BPSet

namespace BPSet

/-- A morphism of bi-pointed precubical sets: a natural transformation of the
underlying presheaves preserving `init` and `final`. -/
@[ext]
structure Hom (K L : BPSet) where
  /-- The underlying natural transformation. -/
  hom : K.toPsh ⟶ L.toPsh
  /-- Preservation of the initial vertex. -/
  app_init : hom⟪0⟫ K.init = L.init
  /-- Preservation of the final vertex. -/
  app_final : hom⟪0⟫ K.final = L.final

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

/-- The forgetful functor to the underlying precubical set, dropping the two base points. -/
@[simps]
def toPshFunctor : BPSet ⥤ PrecubicalSet where
  obj K := K.toPsh
  map f := f.hom
  map_id := id_hom
  map_comp := comp_hom

end BPSet
