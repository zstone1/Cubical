import CubeChains.Foundations.Bipointed
import CubeChains.Foundations.Reachability
import Mathlib.CategoryTheory.Whiskering

/-!
# Foundations/Nerve

The **nerve / model bridge** between the repo's two models of precubical sets:

* the **concrete** model `PrecubicalConstructions` (graded cells + face maps,
  `Foundations/PrecubicalConstructions/Basic.lean`), and
* the **topos** model `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`Foundations/Box.lean`).

We provide two functors and the round-trip iso identifying them:

* `realize : PrecubicalSet ⥤ PrecubicalConstructions` — forget a topos precubical
  set to its concrete graded skeleton (`cells := X.cells`, `face := X.faceMap`),
  using the precubical identity `PrecubicalSet.faceMap_faceMap`;
* `Nerve : PrecubicalConstructions ⥤ PrecubicalSet` — the restricted Yoneda nerve
  along `StdCube.cubeι : Box ⥤ PrecubicalConstructions`, assembled off the shelf
  from `yoneda` and `whiskeringLeft`;
* `nerveCellEquiv K n : (Nerve.obj K).cells n ≃ K.cells n`, the concrete cube
  Yoneda lemma `StdCube.cubeRepr`, with naturality against cells/faces/maps;
* `nerveRealizeIso X : Nerve.obj (realize.obj X) ≅ X` in `PrecubicalSet` — "the
  nerve of the realization recovers `X`".

**Layer:** Foundations.  **Imports:** `Bipointed`, `Reachability` (for the coface
naturality `map_faceMap`), mathlib `Whiskering`.

This is the bridge enabling the concrete cylinder construction (M0b stage 2 redo):
`nerveRealizeIso` is the handle the cylinder uses to define the end-inclusions
`X ⟶ Cyl X`.  The whole point is to **reuse** the cube Yoneda machinery
(`StdCube.ev`/`canonicalMap`/`cubeRepr`/`cubeι`), not re-derive cube combinatorics.
-/

set_option relaxedAutoImplicit false

open CategoryTheory Opposite
open scoped StdCube

namespace PrecubicalSet

/-! ### The coface relation and the topos-level precubical identity

The topos face maps `faceMap ε i = X.map (coface ε i).op` satisfy the precubical
identity because the *cofaces* `coface ε i : □ⁿ ⟶ □ⁿ⁺¹` satisfy the dual relation
in `Box`.  That relation is a plain morphism equation between concrete cube maps,
proved through the cube Yoneda lemma (`cubeRepr` is injective via `ev`) and the
standard cube's `StdCube.face_face`. -/

/-- **The coface relation in `Box`.**  For `i ≤ j`, the two ways of composing
cofaces agree: `coface ε i ≫ coface η j.succ = coface ε i.castSucc ≫ coface η j`.
This is the dual of the precubical identity, living among the *coface* box maps. -/
theorem coface_coface (ε η : Bool) {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    (coface ε i ≫ coface η j.succ : Box.ob n ⟶ Box.ob (n + 2))
      = coface η j ≫ coface ε i.castSucc := by
  -- Two maps `□ⁿ ⟶ □ⁿ⁺²` agree iff their `ev` (value on the top cell) agree.
  -- `ev (f ≫ coface η _) = app (face η _ ⊤) (ev f)`; with `f` a coface this is a
  -- double face of the top cell, and `StdCube.face_face` closes it.
  refine (StdCube.cubeRepr (StdCube.stdPre (n + 2)) n).injective ?_
  change StdCube.ev (coface ε i ≫ coface η j.succ)
      = StdCube.ev (coface η j ≫ coface ε i.castSucc)
  simp only [StdCube.ev_comp, coface, StdCube.canonicalMap_app, StdCube.ev_canonicalMap,
    StdCube.app_face, StdCube.app_topCell]
  exact StdCube.face_face ε η hij (StdCube.topCell (n + 2))

/-- **The precubical identity for topos face maps.**  The topos face maps
`faceMap ε i (c) = X.map (coface ε i).op c` satisfy the precubical identity: for
`i ≤ j`,
`faceMap ε i (faceMap η j.succ c) = faceMap η j (faceMap ε i.castSucc c)`.
Reduce to `X.map` of a single composed box morphism and invoke `coface_coface`. -/
theorem faceMap_faceMap (X : PrecubicalSet) (ε η : Bool) {n : ℕ} {i j : Fin (n + 1)}
    (hij : i ≤ j) (c : X.cells (n + 2)) :
    X.faceMap ε i (X.faceMap η j.succ c) = X.faceMap η j (X.faceMap ε i.castSucc c) := by
  change X.map (coface ε i).op (X.map (coface η j.succ).op c)
    = X.map (coface η j).op (X.map (coface ε i.castSucc).op c)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, coface_coface ε η hij]

/-! ### `realize` — forget a topos precubical set to the concrete model -/

/-- The concrete precubical set underlying a topos precubical set `X`: its graded
cells, with face maps the topos face maps `X.faceMap`. -/
noncomputable def realizeObj (X : PrecubicalSet) : PrecubicalConstructions where
  cells n := X.cells n
  face := fun {_n} ε i c => X.faceMap ε i c
  face_face := fun {_n} ε η {_i _j} hij c => X.faceMap_faceMap ε η hij c

@[simp] theorem realizeObj_cells (X : PrecubicalSet) (n : ℕ) :
    (realizeObj X).cells n = X.cells n := rfl

/-- The realization on morphisms: dimension-wise the components of `φ`, with face
commutation from `Reachability.map_faceMap` (naturality through cofaces). -/
def realizeMap {X Y : PrecubicalSet} (φ : X ⟶ Y) : realizeObj X ⟶ realizeObj Y where
  app n c := φ.app (op (Box.ob n)) c
  app_face := fun {_n} ε i c => map_faceMap φ ε i c

/-- **The realization functor** `PrecubicalSet ⥤ PrecubicalConstructions`: forget
a topos precubical set to its concrete graded skeleton. -/
@[simps]
noncomputable def realize : PrecubicalSet ⥤ PrecubicalConstructions where
  obj := realizeObj
  map φ := realizeMap φ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem realizeMap_app {X Y : PrecubicalSet} (φ : X ⟶ Y) (n : ℕ) (c : X.cells n) :
    PrecubicalConstructions.Hom.app (realizeMap φ) n c = φ.app (op (Box.ob n)) c := rfl

@[simp] theorem realizeObj_face {X : PrecubicalSet} {n : ℕ} (ε : Bool) (i : Fin (n + 1))
    (c : X.cells (n + 1)) : (realizeObj X).face ε i c = X.faceMap ε i c := rfl

/-! ### `Nerve` — the restricted Yoneda nerve along `cubeι`

Off the shelf: `Nerve = yoneda ⋙ (whiskeringLeft …).obj cubeι.op`.  Concretely
`(Nerve.obj K).obj (op b) = (cubeι.obj b ⟶ K) = (□^{b.dim} ⟶ K)`, the contravariant
action `.map g.op` precomposes by `cubeι.map g`, and `Nerve.map φ` postcomposes by
`φ`.  Functoriality is inherited from `yoneda` and `whiskeringLeft`. -/

/-- **The nerve functor** `PrecubicalConstructions ⥤ PrecubicalSet`: the restricted
Yoneda nerve along the cube inclusion `cubeι : Box ⥤ PrecubicalConstructions`.
`(Nerve.obj K).obj (op b) = (□^{b.dim} ⟶ K)`; restriction along `cubeι.op` makes it
a presheaf on `Box`, i.e. an object of `PrecubicalSet`. -/
def Nerve : PrecubicalConstructions ⥤ PrecubicalSet :=
  yoneda ⋙ (Functor.whiskeringLeft Boxᵒᵖ PrecubicalConstructionsᵒᵖ Type).obj StdCube.cubeι.op

@[simp] theorem Nerve_obj_obj (K : PrecubicalConstructions) (b : Boxᵒᵖ) :
    (Nerve.obj K).obj b = (StdCube.cubeι.obj b.unop ⟶ K) := rfl

@[simp] theorem Nerve_obj_map (K : PrecubicalConstructions) {b b' : Boxᵒᵖ} (g : b ⟶ b')
    (f : StdCube.cubeι.obj b.unop ⟶ K) :
    (Nerve.obj K).map g f = StdCube.cubeι.map g.unop ≫ f := rfl

@[simp] theorem Nerve_map_app (K L : PrecubicalConstructions) (φ : K ⟶ L) (b : Boxᵒᵖ)
    (f : StdCube.cubeι.obj b.unop ⟶ K) :
    (Nerve.map φ).app b f = f ≫ φ := rfl

/-! ### `nerveCellEquiv` — the cube Yoneda identification of the nerve's cells -/

/-- **The nerve's `n`-cells are `K`'s `n`-cells.**  `(Nerve.obj K).cells n` is by
definition `(□ⁿ ⟶ K)`, and the concrete cube Yoneda lemma `StdCube.cubeRepr`
identifies that with `K.cells n` (forward = `ev`, inverse = `canonicalMap`). -/
def nerveCellEquiv (K : PrecubicalConstructions) (n : ℕ) :
    (Nerve.obj K).cells n ≃ K.cells n :=
  StdCube.cubeRepr K n

@[simp] theorem nerveCellEquiv_apply (K : PrecubicalConstructions) {n : ℕ}
    (f : (Nerve.obj K).cells n) : nerveCellEquiv K n f = StdCube.ev f := rfl

@[simp] theorem nerveCellEquiv_symm_apply (K : PrecubicalConstructions) {n : ℕ}
    (c : K.cells n) : (nerveCellEquiv K n).symm c = StdCube.canonicalMap c := rfl

/-- **Naturality in `K`**: `nerveCellEquiv` intertwines `Nerve.map φ` (postcompose
by `φ`) on the nerve side with `K`'s cell action `φ.app n` on the concrete side. -/
theorem nerveCellEquiv_naturality {K L : PrecubicalConstructions} (φ : K ⟶ L) {n : ℕ}
    (f : (Nerve.obj K).cells n) :
    nerveCellEquiv L n ((Nerve.map φ).app (op (Box.ob n)) f)
      = PrecubicalConstructions.Hom.app φ n (nerveCellEquiv K n f) := by
  change StdCube.ev (f ≫ φ) = PrecubicalConstructions.Hom.app φ n (StdCube.ev f)
  exact StdCube.ev_comp f φ

/-- **Naturality against the box/face action**: the nerve's contravariant action
`(Nerve.obj K).map g` (precompose by `cubeι.map g`) corresponds, under
`nerveCellEquiv`, to evaluating the canonical map of the cell.  In particular for a
coface `g = (coface ε i).op` it is `K`'s concrete face map. -/
theorem nerveCellEquiv_map {K : PrecubicalConstructions} {m n : ℕ}
    (g : (Box.ob n) ⟶ (Box.ob m)) (f : (Nerve.obj K).cells m) :
    nerveCellEquiv K n ((Nerve.obj K).map g.op f)
      = StdCube.ev (StdCube.cubeι.map g ≫ f) := rfl

/-- **The face action through `nerveCellEquiv`.**  The topos face map of the nerve
`(Nerve.obj K).faceMap ε i` corresponds to `K`'s concrete `face ε i`. -/
theorem nerveCellEquiv_faceMap {K : PrecubicalConstructions} {n : ℕ} (ε : Bool)
    (i : Fin (n + 1)) (f : (Nerve.obj K).cells (n + 1)) :
    nerveCellEquiv K n ((Nerve.obj K).faceMap ε i f)
      = K.face ε i (nerveCellEquiv K (n + 1) f) := by
  -- `(Nerve.obj K).map (coface ε i).op f = cubeι.map (coface ε i) ≫ f = coface ε i ≫ f`;
  -- then `ev (coface ε i ≫ f)` peels the coface, faces the top cell, and
  -- `app_face`/`app_topCell` close it.
  change StdCube.ev (coface ε i ≫ f) = K.face ε i (StdCube.ev f)
  rw [StdCube.ev_comp, coface, StdCube.ev_canonicalMap]
  exact f.app_face ε i (StdCube.topCell (n + 1))

/-! ### `nerveRealizeIso` — the nerve of the realization recovers `X`

The round-trip `Nerve.obj (realize.obj X) ≅ X` in `PrecubicalSet`.  Componentwise
at `op b` it is the cube Yoneda equivalence `(□^{b.dim} ⟶ realize X) ≃ X.cells b.dim`.
Naturality against box morphisms is the key identity `ev_realize_app` below: the
concrete iterated-face value `StdCube.app c a` in the realization is just `X`'s
presheaf action `X.map (canonicalMap a).op c` (proved by peeling cofaces, exactly
mirroring `app_unfold`/`canonicalMap_peel`, with the realization's faces being
`X.faceMap = X.map (coface …).op`). -/

/-- **The concrete iterated-face value in the realization is `X`'s presheaf
action.**  For `c : X.cells N` and a `k`-cell `a` of `□ᴺ`, the value of
`StdCube.app` in `realizeObj X` is the pullback `X.map (canonicalMap a).op c`.
Proved by strong induction on the number of fixed coordinates `N - k`, peeling the
smallest one with `app_unfold`/`canonicalMap_peel`. -/
theorem ev_realize_app (X : PrecubicalSet) {N : ℕ} (c : X.cells N) :
    ∀ {k : ℕ} (a : StdCube.cells N k),
      StdCube.app (K := realizeObj X) c a = X.map (StdCube.canonicalMap a).op c := by
  intro k a
  induction hd : N - k using Nat.strong_induction_on generalizing k a with
  | _ d ih =>
    rcases Nat.lt_or_ge k N with hlt | hge
    · -- non-top: peel the smallest fixed coordinate
      rw [StdCube.app_unfold (K := realizeObj X) c a hlt]
      have hstep : StdCube.app (K := realizeObj X) c (StdCube.freeMin a hlt)
          = X.map (StdCube.canonicalMap (StdCube.freeMin a hlt)).op c :=
        ih (N - (k + 1)) (by omega) (StdCube.freeMin a hlt) rfl
      rw [hstep]
      -- the realization's face is the topos `faceMap`, i.e. `X.map (coface _).op`
      change X.faceMap (StdCube.minFixedVal a hlt) (StdCube.minFixedIdx a hlt)
          (X.map (StdCube.canonicalMap (StdCube.freeMin a hlt)).op c)
        = X.map (StdCube.canonicalMap a).op c
      rw [faceMap, ← Functor.map_comp_apply]
      -- reduce to the box-morphism equation `canonicalMap_peel`: peel down through
      -- `ConcreteCategory.hom`/`X.map`/`Quiver.Hom.op` to the bare `Box`-morphism
      -- equation (defeq to `canonicalMap_peel`).
      congr 3
      · -- the bare `Boxᵒᵖ` equation `M₁ = M₂`; take `unop` (peeling `.op`) to land back
        -- in `Box`, where `canonicalMap_peel` is the statement.
        apply Quiver.Hom.unop_inj
        exact (StdCube.canonicalMap_peel a hlt).symm
    · -- top cell: `k = N`, `a = topCell N`, `canonicalMap (topCell N) = 𝟙`
      have hkn : k = N := le_antisymm (StdCube.cells_card_le a) hge
      subst hkn
      rw [StdCube.eq_topCell a, StdCube.app_topCell]
      have hop : (StdCube.canonicalMap (StdCube.topCell k)).op
          = 𝟙 (op (Box.ob k)) :=
        (congrArg Quiver.Hom.op (StdCube.canonicalMap_topCell k)).trans (op_id (X := Box.ob k))
      rw [hop, Functor.map_id_apply]

/-- The key naturality identity, packaged on morphisms `f : □ᴺ ⟶ realizeObj X` and
a box map `h : □ᴹ ⟶ □ᴺ`: `ev (h ≫ f) = X.map h.op (ev f)`. -/
theorem ev_comp_realize (X : PrecubicalSet) {M N : ℕ}
    (h : Box.ob M ⟶ Box.ob N) (f : StdCube.stdPre N ⟶ realizeObj X) :
    StdCube.ev (h ≫ f) = X.map h.op (StdCube.ev f) := by
  rw [StdCube.ev_comp]
  -- write `f = canonicalMap (ev f)` to turn `Hom.app f` into `StdCube.app (ev f)`
  conv_lhs => rw [show f = StdCube.canonicalMap (StdCube.ev f) from
    ((StdCube.cubeRepr (realizeObj X) N).left_inv f).symm]
  rw [StdCube.canonicalMap_app, ev_realize_app X (StdCube.ev f) (StdCube.ev h)]
  -- `canonicalMap (ev h) = h` (cube Yoneda), so the box map matches
  have hcanon : StdCube.canonicalMap (StdCube.ev h) = h :=
    (StdCube.cubeRepr (StdCube.stdPre N) M).left_inv h
  exact congrFun (congrArg (fun m => (X.map m.op : X.obj _ → X.obj _)) hcanon) (StdCube.ev f)

/-- The componentwise iso `(Nerve.obj (realize.obj X)).obj b ≅ X.obj b`
in `Type`, from `nerveCellEquiv` on the realization. -/
noncomputable def nerveRealizeComponent (X : PrecubicalSet) (b : Boxᵒᵖ) :
    (Nerve.obj (realize.obj X)).obj b ≅ X.obj b :=
  (nerveCellEquiv (realize.obj X) b.unop.dim).toIso

theorem nerveRealizeComponent_hom (X : PrecubicalSet) (b : Boxᵒᵖ)
    (f : (Nerve.obj (realize.obj X)).obj b) :
    (nerveRealizeComponent X b).hom f = StdCube.ev f := rfl

/-- **The nerve of the realization recovers `X`.**  A natural iso
`Nerve.obj (realize.obj X) ≅ X` of presheaves: at `op b` it is the cube Yoneda
equivalence, and the naturality square is `ev_comp_realize` (the nerve's
contravariant action precomposes by a box map; on the realization that corresponds
to `X`'s presheaf action). -/
noncomputable def nerveRealizeIso (X : PrecubicalSet) : Nerve.obj (realize.obj X) ≅ X :=
  NatIso.ofComponents (nerveRealizeComponent X) (by
    intro b b' g
    ext f
    -- the box morphism is `g.unop : □^{b'.dim} ⟶ □^{b.dim}`, and `cubeι.map = id`
    exact ev_comp_realize X g.unop f)

@[simp] theorem nerveRealizeIso_hom_app (X : PrecubicalSet) (b : Boxᵒᵖ)
    (f : (Nerve.obj (realize.obj X)).obj b) :
    (nerveRealizeIso X).hom.app b f = StdCube.ev f := rfl

end PrecubicalSet
