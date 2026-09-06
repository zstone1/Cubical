import CubeChains.Machinery.Cube.Box
import CubeChains.Precubical.Basic.Representable
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Yoneda

/-!
# Precubical/Basic/Bipointed

Bi-pointed precubical sets over the topos `PrecubicalSet = Boxᵒᵖ ⥤ Type`: `BPSet`
(a presheaf `X` with two chosen `0`-cells `init`, `final`) + `Hom` + category, plus
`cells`, `vertexEnd`, `faceMap`/`cubeMap`, `endVertexMap` and `IsAltitude`.

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

/-- Peel the smallest fixed coordinate off an iterated face (`canonicalMap_peel`, applied). -/
theorem map_canonicalMap_peel (X : PrecubicalSet) {N k : ℕ} (x : X.cells N) (c' : Cell N k)
    (h : k < N) :
    X.map (canonicalMap c').op x
      = X.faceMap (minFixedVal c' h) (minFixedIdx c' h)
          (X.map (canonicalMap (freeMin c' h)).op x) := by
  have e1 : X.map (canonicalMap c').op x
      = X.map (PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
          ≫ canonicalMap (freeMin c' h)).op x :=
    congrArg (fun m => X.map (Quiver.Hom.op m) x) (canonicalMap_peel c' h)
  rw [e1, op_comp, Functor.map_comp]
  rfl

/-- An iterated face along a top cell is the cell itself.  `erw`: `Box`'s homs *are* cube maps, so
`canonicalMap_topCell` matches the `Box` composite only up to that defeq bridge. -/
theorem map_canonicalMap_top (X : PrecubicalSet) {N : ℕ} (x : X.cells N) (c' : Cell N N) :
    X.map (canonicalMap c').op x = x := by
  rw [eq_topCell c']
  erw [canonicalMap_topCell, op_id, X.map_id]
  rfl

/-- The canonical map `□ⁿ ⟶ X` classifying an `n`-cell `c` (Yoneda). -/
def cubeMap (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    yoneda.obj ▫n ⟶ X :=
  yonedaEquiv.symm c

/-- The extremal vertex inclusion `[0] ⟶ [n]` in `Box`: the all-`ε` vertex. -/
def endVertexMap (ε : Bool) (n : ℕ) : ▫0 ⟶ ▫n :=
  canonicalMap (constVertex n ε)

/-- The extremal vertex `vertexEnd ε c` of an `n`-cell `c`: pull `c` back along the
all-`ε` vertex inclusion (`false` is the source, `true` the target). -/
def vertexEnd (X : PrecubicalSet) (ε : Bool) {n : ℕ} (c : X.cells n) : X.cells 0 :=
  X.map (endVertexMap ε n).op c

/-! ### Vertices of Yoneda-classified cells and naturality

`BPSet`-level callers apply these through `K.toPsh`. -/

/-- The extremal vertex of a Yoneda-classified cell, by Yoneda naturality. -/
theorem vertexEnd_yonedaEquiv {K : PrecubicalSet} (ε : Bool) {n : ℕ}
    (f : yoneda.obj ▫n ⟶ K) :
    K.vertexEnd ε (yonedaEquiv f) = f⟪0⟫ (endVertexMap ε n) :=
  map_yonedaEquiv f (endVertexMap ε n)

/-- A precubical map commutes with `vertexEnd` (naturality through the vertex inclusion). -/
theorem map_vertexEnd (ε : Bool) {K L : PrecubicalSet} (φ : K ⟶ L) {n : ℕ} (c : K.cells n) :
    φ⟪0⟫ (K.vertexEnd ε c) = L.vertexEnd ε (φ⟪n⟫ c) :=
  NatTrans.naturality_apply φ (endVertexMap ε n).op c

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

/-- The `ε`-endpoint: `false` is `init`, `true` is `final`.  Both cases reduce by `rfl`, so an
endpoint fact is stated once at `vtx ε` and read at either end by `cases ε`. -/
def vtx (K : BPSet) : Bool → K.cells 0
  | false => K.init
  | true => K.final

/-- Re-point `K` at a chosen pair of vertices.  The endpoints of a `BPSet` are a
*parameter*, not a commitment: everything indexed by `K` — `Ch`, `Lines` — is
read at other endpoints as `… (K.repoint u v)`.

`toPsh` is untouched, so `(K.repoint u v).cells n = K.cells n` by `rfl`, and re-pointing at
the original vertices is the identity (structure eta). -/
def repoint (K : BPSet) (u v : K.cells 0) : BPSet where
  toPsh := K.toPsh
  init := u
  final := v

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

/-- `app_init` and `app_final` as one `ε`-indexed statement. -/
theorem app_vtx (f : Hom K L) (ε : Bool) : f.hom⟪0⟫ (K.vtx ε) = L.vtx ε := by
  cases ε
  exacts [f.app_init, f.app_final]

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

/-- Applying `Φ.inv` after `Φ.hom` is the identity, pointwise. -/
theorem psh_inv_hom {K L : PrecubicalSet} (Φ : K ≅ L) {n : ℕ} (c : K.cells n) :
    Φ.inv⟪n⟫ (Φ.hom⟪n⟫ c) = c :=
  comp_app_cell Φ.hom_inv_id n c

/-- Promote an iso of underlying presheaves preserving `init`/`final` to a `BPSet` iso: the
inverse's endpoint conditions come for free. -/
def isoOfPshIso {K L : BPSet} (Φ : K.toPsh ≅ L.toPsh)
    (hinit : Φ.hom⟪0⟫ K.init = L.init) (hfinal : Φ.hom⟪0⟫ K.final = L.final) : K ≅ L where
  hom := ⟨Φ.hom, hinit, hfinal⟩
  inv := ⟨Φ.inv, by rw [← hinit, psh_inv_hom], by rw [← hfinal, psh_inv_hom]⟩
  hom_inv_id := BPSet.hom_ext Φ.hom_inv_id
  inv_hom_id := BPSet.hom_ext Φ.inv_hom_id

@[simp] theorem isoOfPshIso_hom_hom {K L : BPSet} (Φ : K.toPsh ≅ L.toPsh)
    (hinit : Φ.hom⟪0⟫ K.init = L.init) (hfinal : Φ.hom⟪0⟫ K.final = L.final) :
    (isoOfPshIso Φ hinit hfinal).hom.hom = Φ.hom := rfl

/-- The forgetful functor to the underlying precubical set, dropping the two base points. -/
@[simps]
def toPshFunctor : BPSet ⥤ PrecubicalSet where
  obj K := K.toPsh
  map f := f.hom
  map_id := id_hom
  map_comp := comp_hom

/-! ### Targets with a single vertex

`app_init`/`app_final` are a *property* of the underlying presheaf map, and a target with only one
`0`-cell has no room for them to fail: over such a target the two categories have the same
hom-sets. -/

/-- **The endpoint conditions are free over a one-vertex target.** -/
@[simps]
def homEquivPsh (X Y : BPSet) [Subsingleton (Y.cells 0)] : (X ⟶ Y) ≃ (X.toPsh ⟶ Y.toPsh) where
  toFun f := f.hom
  invFun φ := ⟨φ, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

end BPSet
