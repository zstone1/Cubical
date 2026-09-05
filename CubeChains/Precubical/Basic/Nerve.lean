import CubeChains.Precubical.Basic.Bipointed
import CubeChains.Precubical.Basic.Reachability
import Mathlib.CategoryTheory.Whiskering

/-!
# Precubical/Basic/Nerve

The **nerve / model bridge** between the **concrete** model `PrecubicalConstructions`
(graded cells + face maps) and the **topos** model `PrecubicalSet := Boxᵒᵖ ⥤ Type`:

* `realize : PrecubicalSet ⥤ PrecubicalConstructions` — forget a topos precubical
  set to its concrete graded skeleton (`cells := X.cells`, `face := X.faceMap`);
* `Nerve : PrecubicalConstructions ⥤ PrecubicalSet` — the restricted Yoneda nerve
  along `cubeι : Box ⥤ PrecubicalConstructions`, assembled off the shelf
  from `yoneda` and `whiskeringLeft`;
* `realizeNerveIso : Nerve ⋙ realize ≅ 𝟭` and `nerveRealizeIso X : Nerve.obj (realize.obj X) ≅ X`
  — both round trips, each componentwise the concrete cube Yoneda lemma `cubeRepr`.
-/

set_option relaxedAutoImplicit false

open CategoryTheory Opposite
open StdCube

namespace PrecubicalSet

/-! ### The coface relation and the topos-level precubical identity

The topos face maps `faceMap ε i = X.map (coface ε i).op` satisfy the precubical
identity because the *cofaces* `coface ε i : □ⁿ ⟶ □ⁿ⁺¹` satisfy the dual relation
in `Box`.  That relation is a plain morphism equation between concrete cube maps,
proved through the cube Yoneda lemma (`cubeRepr` is injective via `ev`) and the
standard cube's `face_face`. -/

/-- **The coface relation in `Box`.**  For `i ≤ j`, the two ways of composing
cofaces agree: `coface ε i ≫ coface η j.succ = coface ε i.castSucc ≫ coface η j`.
This is the dual of the precubical identity, living among the *coface* box maps. -/
theorem coface_coface (ε η : Bool) {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    (coface ε i ≫ coface η j.succ : ▫n ⟶ ▫(n + 2))
      = coface η j ≫ coface ε i.castSucc := by
  -- Two maps `□ⁿ ⟶ □ⁿ⁺²` agree iff their `ev` (value on the top cell) agree.
  -- `ev (f ≫ coface η _) = app (face η _ ⊤) (ev f)`; with `f` a coface this is a
  -- double face of the top cell, and `face_face` closes it.
  refine (cubeRepr (stdPre (n + 2)) n).injective ?_
  change ev (coface ε i ≫ coface η j.succ)
      = ev (coface η j ≫ coface ε i.castSucc)
  simp only [ev_comp, coface, canonicalMap_app, ev_canonicalMap,
    app_face, app_topCell]
  exact face_face ε η hij (topCell (n + 2))

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
def realizeObj (X : PrecubicalSet) : PrecubicalConstructions where
  cells n := X.cells n
  face := fun {_n} ε i c => X.faceMap ε i c
  face_face := fun {_n} ε η {_i _j} hij c => X.faceMap_faceMap ε η hij c

/-- The realization on morphisms: dimension-wise the components of `φ`, with face
commutation from `Reachability.map_faceMap` (naturality through cofaces). -/
def realizeMap {X Y : PrecubicalSet} (φ : X ⟶ Y) : realizeObj X ⟶ realizeObj Y where
  app n c := φ⟪n⟫ c
  app_face := fun {_n} ε i c => map_faceMap φ ε i c

/-- **The realization functor** `PrecubicalSet ⥤ PrecubicalConstructions`: forget
a topos precubical set to its concrete graded skeleton. -/
@[simps]
def realize : PrecubicalSet ⥤ PrecubicalConstructions where
  obj := realizeObj
  map φ := realizeMap φ
  map_id _ := rfl
  map_comp _ _ := rfl

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
  yoneda ⋙ (Functor.whiskeringLeft Boxᵒᵖ PrecubicalConstructionsᵒᵖ Type).obj cubeι.op

/-! ### `realizeNerveIso` — the realization of the nerve recovers `K`

The nerve's `n`-cells *are* `K`'s: `(Nerve.obj K).cells n = (□ⁿ ⟶ K) ≃ K.cells n` is the concrete
cube Yoneda lemma `cubeRepr`.  Its compatibilities — with `K`'s faces, with `Nerve.map`, with the
`Box` action — are the two `Hom` fields and the naturality square of a single iso of functors. -/

/-- **The face action of the nerve is `K`'s.**  The one non-formal input to `realizeNerveIso`:
`ev (coface ε i ≫ f)` peels the coface, faces the top cell, and `app_face` closes it. -/
theorem ev_nerve_faceMap {K : PrecubicalConstructions} {n : ℕ} (ε : Bool)
    (i : Fin (n + 1)) (f : (Nerve.obj K).cells (n + 1)) :
    ev ((Nerve.obj K).faceMap ε i f) = K.face ε i (ev f) := by
  change ev (coface ε i ≫ f) = K.face ε i (ev f)
  rw [ev_comp, coface, ev_canonicalMap]
  exact f.app_face ε i (topCell (n + 1))

/-- **The realization of the nerve is the identity**, naturally in `K` — half of the comparison of
the two models.  Componentwise it is `cubeRepr` (`ev` forward, `canonicalMap` back); the face
square is `ev_nerve_faceMap` and naturality in `K` is `ev_comp`. -/
def realizeNerveIso : Nerve ⋙ realize ≅ 𝟭 PrecubicalConstructions :=
  NatIso.ofComponents
    (fun K =>
      { hom := { app := fun _ f => ev f, app_face := fun ε i f => ev_nerve_faceMap ε i f }
        inv :=
          { app := fun _ c => canonicalMap c
            app_face := fun ε i c => (cubeRepr K _).injective (by
              change ev (canonicalMap (K.face ε i c))
                = ev ((Nerve.obj K).faceMap ε i (canonicalMap c))
              rw [ev_canonicalMap, ev_nerve_faceMap, ev_canonicalMap]) }
        hom_inv_id := PrecubicalConstructions.hom_ext fun n f => (cubeRepr K n).left_inv f
        inv_hom_id := PrecubicalConstructions.hom_ext fun _ c => ev_canonicalMap c })
    (fun φ => PrecubicalConstructions.hom_ext fun _ f => ev_comp f φ)

/-! ### `nerveRealizeIso` — the nerve of the realization recovers `X`

The round-trip `Nerve.obj (realize.obj X) ≅ X` in `PrecubicalSet`.  Componentwise
at `op b` it is the cube Yoneda equivalence `(□^{b.dim} ⟶ realize X) ≃ X.cells b.dim`.
Naturality against box morphisms is the key identity `ev_realize_app` below: the
concrete iterated-face value `act c a` in the realization is just `X`'s
presheaf action `X.map (canonicalMap a).op c` (proved by peeling cofaces, exactly
mirroring `app_unfold`/`canonicalMap_peel`, with the realization's faces being
`X.faceMap = X.map (coface …).op`). -/

/-- **The concrete iterated-face value in the realization is `X`'s presheaf
action.**  For `c : X.cells N` and a `k`-cell `a` of `□ᴺ`, the value of
`act` in `realizeObj X` is the pullback `X.map (canonicalMap a).op c`. -/
theorem ev_realize_app (X : PrecubicalSet) {N : ℕ} (c : X.cells N) :
    ∀ {k : ℕ} (a : Cell N k),
      act (K := realizeObj X) c a = X.map (canonicalMap a).op c := by
  intro k a
  induction k, a using Cell.peelRec with
  | top a => rw [eq_topCell a, app_topCell, X.map_canonicalMap_top c _]
  | step k a h ih =>
      rw [app_unfold (K := realizeObj X) c a h, ih]
      exact (X.map_canonicalMap_peel c a h).symm

/-- The key naturality identity, packaged on morphisms `f : □ᴺ ⟶ realizeObj X` and
a box map `h : □ᴹ ⟶ □ᴺ`: `ev (h ≫ f) = X.map h.op (ev f)`. -/
theorem ev_comp_realize (X : PrecubicalSet) {M N : ℕ}
    (h : ▫M ⟶ ▫N) (f : stdPre N ⟶ realizeObj X) :
    ev (h ≫ f) = X.map h.op (ev f) := by
  rw [ev_comp]
  -- write `f = canonicalMap (ev f)` to turn `Hom.app f` into `act (ev f)`
  conv_lhs => rw [show f = canonicalMap (ev f) from
    ((cubeRepr (realizeObj X) N).left_inv f).symm]
  rw [canonicalMap_app, ev_realize_app X (ev f) (ev h)]
  -- `canonicalMap (ev h) = h` (cube Yoneda), so the box map matches
  have hcanon : canonicalMap (ev h) = h :=
    (cubeRepr (stdPre N) M).left_inv h
  exact congrFun (congrArg (fun m => (X.map m.op : X.obj _ → X.obj _)) hcanon) (ev f)

/-- **The nerve of the realization recovers `X`.**  A natural iso
`Nerve.obj (realize.obj X) ≅ X` of presheaves: at `op b` it is the cube Yoneda
equivalence `cubeRepr`, and the naturality square is `ev_comp_realize` (the nerve's
contravariant action precomposes by a box map; on the realization that corresponds
to `X`'s presheaf action). -/
def nerveRealizeIso (X : PrecubicalSet) : Nerve.obj (realize.obj X) ≅ X :=
  NatIso.ofComponents (fun b => (cubeRepr (realize.obj X) b.unop.dim).toIso) (by
    intro b b' g
    ext f
    -- the box morphism is `g.unop : □^{b'.dim} ⟶ □^{b.dim}`, and `cubeι.map = id`
    exact ev_comp_realize X g.unop f)

end PrecubicalSet
