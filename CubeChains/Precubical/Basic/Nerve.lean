import CubeChains.Precubical.Basic.Reachability
import CubeChains.Precubical.Basic.Basic
import Mathlib.CategoryTheory.Whiskering

/-!
# Precubical/Basic/Nerve

The **nerve / model bridge**: `realize` forgets a topos precubical set to its graded skeleton,
`Nerve` is restricted Yoneda along the cube inclusion `cubeι`, and both round trips are
isomorphisms, componentwise `concreteRepr`.

`concreteRepr` is cube Yoneda for a *concrete* precubical set — the one non-formal input: a
cell of `□ⁿ` acts on an abstract `c` by **iterated faces** (`act`, peeling the smallest fixed
coordinate), so face-naturality here costs `Fin.succAbove` bookkeeping that substitution
avoids.  That is the price of the concrete model, and only the bridge pays it.
-/

set_option relaxedAutoImplicit false

open CategoryTheory Opposite
open StdCube

namespace StdCube

/-- The standard `N`-cube as a concrete precubical set. -/
def stdPre (N : ℕ) : PrecubicalConstructions where
  cells k := Cell N k
  face := fun {_} ε i c => faceCell ε i c
  face_face := by intro n ε η i j hij c; exact face_face ε η hij c

/-- Evaluation of a concrete precubical map out of `□ⁿ` at the top cell. -/
def evC {K : PrecubicalConstructions} {n : ℕ} (f : stdPre n ⟶ K) : K.cells n :=
  PrecubicalConstructions.Hom.app f n (topCell n)

/-- `evC` of a composite peels the first factor. -/
theorem evC_comp {A : PrecubicalConstructions} {n : ℕ} (f : stdPre n ⟶ A)
    {K : PrecubicalConstructions} (g : A ⟶ K) :
    evC (f ≫ g) = PrecubicalConstructions.Hom.app g n (evC f) := rfl

/-- Substitution as a concrete precubical map `□ⁿ ⟶ □ᴺ`: the concrete reading of a cube map. -/
def substMap {N n : ℕ} (c : Cell N n) : stdPre n ⟶ stdPre N where
  app _k a := subst c a
  app_face ε i a := subst_faceCell c ε i a

@[simp] theorem evC_substMap {N n : ℕ} (c : Cell N n) : evC (substMap c) = c := subst_topCell c

/-! ### The iterated-face map into a concrete precubical set

`appAux c d a` faces `c` out at the `d = n - k` fixed coordinates of the `k`-cell `a`, peeling
the smallest one each step; we recurse on the *number of fixed coordinates* `d`, carrying
`k + d = n`. -/

/-- The iterated-face value of `c : K.cells n` along a `k`-cell `a` of `□ⁿ` with
`k + d = n`: peel the `d` fixed coordinates of `a`, smallest first. -/
def appAux {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    (d : ℕ) → {k : ℕ} → (a : Cell n k) → k + d = n → K.cells k
  | 0,     _, _, h => cast (congrArg K.cells h.symm) c
  | d + 1, _, a, h =>
      K.face (minFixedVal a (by omega)) (minFixedIdx a (by omega))
        (appAux c d (freeMin a (by omega)) (by omega))

/-- The iterated-face map underlying the concrete canonical map: send a `k`-cell `a` to the
face of `c` at the fixed coordinates of `a`. -/
def act {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) {k : ℕ} (a : Cell n k) :
    K.cells k :=
  appAux c (n - k) a (by have := cells_card_le a; omega)

/-- `appAux` does not depend on the choice of `d` (it is forced to `n - k`). -/
theorem appAux_eq_app {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) (d : ℕ) {k : ℕ}
    (a : Cell n k) (h : k + d = n) : appAux c d a h = act c a := by
  have hd : d = n - k := by omega
  subst hd; rfl

/-- The iterated-face map sends the top cell to `c`. -/
theorem app_topCell {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    act c (topCell n) = c := by
  rw [← appAux_eq_app c 0 (topCell n) (by omega)]
  exact cast_eq _ c

/-- Unfolding `act` at a non-top cell: peel the smallest fixed coordinate. -/
theorem app_unfold {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n) (a : Cell n k)
    (h : k < n) :
    act c a = K.face (minFixedVal a h) (minFixedIdx a h) (act c (freeMin a h)) := by
  rw [← appAux_eq_app c ((n - (k + 1)) + 1) a (by omega),
    show appAux c ((n - (k + 1)) + 1) a (by omega)
        = K.face (minFixedVal a h) (minFixedIdx a h)
            (appAux c (n - (k + 1)) (freeMin a h) (by omega)) from rfl,
    appAux_eq_app c (n - (k + 1)) (freeMin a h) (by omega)]

/-! ### Face-naturality of the iterated-face map

The crux: `act c` commutes with all faces.  The easy case is when the coordinate being faced
is already the smallest fixed coordinate of `faceCell ε i a`; otherwise we commute past the
smaller fixed coordinate using the precubical identity `face_face` and induct. -/

/-- Naturality when the faced coordinate `i` is the smallest fixed coordinate. -/
theorem app_face_caseA {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n)
    (a : Cell n (k + 1)) (ε : Bool) (i : Fin (k + 1)) (hlt : k < n)
    (hA : minFixed (faceCell ε i a) hlt = nones a i) :
    act c (faceCell ε i a) = K.face ε i (act c a) := by
  rw [app_unfold c (faceCell ε i a) hlt]
  have hfree : freeMin (faceCell ε i a) hlt = a := by
    apply Subtype.ext
    rw [freeMin_val, hA, face_val, Function.update_idem, ← val_nones a i,
      Function.update_eq_self]
  have hval : minFixedVal (faceCell ε i a) hlt = ε := by
    have hv := minFixed_val_eq (faceCell ε i a) hlt
    rw [hA, face_val, Function.update_self] at hv
    exact (Option.some.inj hv).symm
  have hidx : minFixedIdx (faceCell ε i a) hlt = i := by
    have hni := nones_minFixedIdx (faceCell ε i a) hlt
    rw [hA, hfree] at hni
    exact (nones a).injective hni
  rw [hfree, hval, hidx]

/-- `act c` commutes with all faces, keyed on the *faced* cell so that the peeling
recursion applies (`freeMin (faceCell ε i a)` is again a face of `freeMin a`). -/
theorem app_face_aux {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    ∀ {k : ℕ} (b : Cell n k) (a : Cell n (k + 1)) (ε : Bool) (i : Fin (k + 1)),
      faceCell ε i a = b → act c b = K.face ε i (act c a) := by
  intro k b
  induction k, b using Cell.peelRec with
  | top b => exact fun a => ((instIsEmptyCell (Nat.lt_succ_self n)).false a).elim
  | step k b h ih =>
      rintro a ε i rfl
      by_cases hpq : minFixed (faceCell ε i a) h = nones a i
      · exact app_face_caseA c a ε i h hpq
      · -- Case B: smallest fixed coordinate `p` of `faceCell ε i a` is below `q = nones a i`.
        have hfs : fixedSet (faceCell ε i a) = insert (nones a i) (fixedSet a) :=
          fixedSet_face a ε i
        have hp_in_a : minFixed (faceCell ε i a) h ∈ fixedSet a := by
          have hp_mem : minFixed (faceCell ε i a) h ∈ insert (nones a i) (fixedSet a) := by
            rw [← hfs]; exact minFixed_mem _ _
          rcases Finset.mem_insert.mp hp_mem with h' | h'
          · exact absurd h' hpq
          · exact h'
        have hlt1 : k + 1 < n := by
          have hcard := fixedSet_card a
          have := Finset.card_pos.mpr ⟨_, hp_in_a⟩
          omega
        have h1 : minFixed a hlt1 ≤ minFixed (faceCell ε i a) h := Finset.min'_le _ _ hp_in_a
        have h2 : minFixed (faceCell ε i a) h ≤ minFixed a hlt1 := by
          refine Finset.min'_le _ _ ?_
          rw [hfs, Finset.mem_insert]; right; exact minFixed_mem _ _
        have hp_eq : minFixed a hlt1 = minFixed (faceCell ε i a) h := le_antisymm h1 h2
        have hplt : minFixed a hlt1 < nones a i := by
          rw [hp_eq]
          refine lt_of_le_of_ne (Finset.min'_le _ _ ?_) hpq
          rw [hfs]; exact Finset.mem_insert_self _ _
        have hpa_ne_q : minFixed a hlt1 ≠ nones a i := ne_of_lt hplt
        -- The freed cell `freeMin a hlt1` and the index `i'` of `q = nones a i` in it.
        have hface_a : faceCell (minFixedVal a hlt1) (minFixedIdx a hlt1) (freeMin a hlt1) = a :=
          face_freeMin a hlt1
        have hnι'p : nones (freeMin a hlt1) (minFixedIdx a hlt1) = minFixed a hlt1 :=
          nones_minFixedIdx a hlt1
        have hq_in_a0 : nones a i ∈ noneSet (freeMin a hlt1).val := by
          rw [noneSet_freeMin, Finset.mem_insert]
          right; exact nones_mem a i
        have hni' : nones (freeMin a hlt1) (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0)
            = nones a i := nones_nonesIdx _ _ _
        -- C2: the freed cell of `faceCell ε i a` is `faceCell ε i' (freeMin a hlt1)`.
        have hC2 : freeMin (faceCell ε i a) h
            = faceCell ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0) (freeMin a hlt1) := by
          apply Subtype.ext
          rw [freeMin_val, face_val, ← hp_eq, face_val, hni', freeMin_val,
            Function.update_comm hpa_ne_q.symm]
        -- C3: the freed value matches.
        have hC3 : minFixedVal (faceCell ε i a) h = minFixedVal a hlt1 := by
          have hb := minFixed_val_eq (faceCell ε i a) h
          have ha2 := minFixed_val_eq a hlt1
          rw [← hp_eq, face_val, Function.update_of_ne hpa_ne_q] at hb
          rw [hb] at ha2
          exact Option.some.inj ha2
        -- index relations
        have hnιp : nones (faceCell ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0)
              (freeMin a hlt1))
            (minFixedIdx (faceCell ε i a) h) = minFixed a hlt1 := by
          rw [← hC2, nones_minFixedIdx]; exact hp_eq.symm
        have hR1 : (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0).succAbove
            (minFixedIdx (faceCell ε i a) h) = minFixedIdx a hlt1 := by
          have hh := hnιp
          rw [face_nones, ← hnι'p] at hh
          exact (nones (freeMin a hlt1)).injective hh
        have hR2 : (minFixedIdx a hlt1).succAbove i
            = nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
          have hh : nones a i = nones (freeMin a hlt1) ((minFixedIdx a hlt1).succAbove i) := by
            rw [← face_nones (minFixedVal a hlt1), hface_a]
          rw [← hni'] at hh
          exact ((nones (freeMin a hlt1)).injective hh).symm
        have hR3 : minFixedIdx a hlt1 < nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
          rw [← (nones (freeMin a hlt1)).lt_iff_lt, hnι'p, hni']; exact hplt
        have hcast : minFixedIdx a hlt1 = (minFixedIdx (faceCell ε i a) h).castSucc := by
          have hlt' : (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0).succAbove
              (minFixedIdx (faceCell ε i a) h)
              < nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 := by
            rw [hR1]; exact hR3
          have hc := (Fin.succAbove_lt_iff_castSucc_lt _ _).mp hlt'
          rw [← hR1, Fin.succAbove_of_castSucc_lt _ _ hc]
        have hsucc : nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0 = i.succ := by
          have hlt' : minFixedIdx a hlt1 < (minFixedIdx a hlt1).succAbove i := by
            rw [hR2]; exact hR3
          have hc := (Fin.lt_succAbove_iff_le_castSucc _ _).mp hlt'
          rw [← hR2, Fin.succAbove_of_le_castSucc _ _ hc]
        have hle : minFixedIdx (faceCell ε i a) h ≤ i := by
          have hlt' : (minFixedIdx (faceCell ε i a) h).castSucc < i.succ := by
            rw [← hcast, ← hsucc]; exact hR3
          exact Fin.castSucc_lt_succ_iff.mp hlt'
        -- assemble
        rw [app_unfold c (faceCell ε i a) h, hC3,
          ih (freeMin a hlt1) ε (nonesIdx (freeMin a hlt1) (nones a i) hq_in_a0) hC2.symm,
          app_unfold c a hlt1, hsucc, hcast]
        exact K.face_face (minFixedVal a hlt1) ε hle (act c (freeMin a hlt1))

/-- Naturality of `act`: it commutes with every face. -/
theorem app_face {K : PrecubicalConstructions} {n k : ℕ} (c : K.cells n) (a : Cell n (k + 1))
    (ε : Bool) (i : Fin (k + 1)) : act c (faceCell ε i a) = K.face ε i (act c a) :=
  app_face_aux c _ a ε i rfl

/-! ### Cube Yoneda for the concrete model -/

/-- The concrete precubical map `□ⁿ ⟶ K` determined by an `n`-cell `c`: iterated faces at the
fixed coordinates.  At `K = stdPre N` it is `substMap`. -/
def concreteMap {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) : stdPre n ⟶ K where
  app _k a := act c a
  app_face ε i a := app_face c a ε i

/-- Any precubical map agreeing with `c` on the top cell is `act c`. -/
theorem app_unique {K : PrecubicalConstructions} {n : ℕ} {c : K.cells n} (g : stdPre n ⟶ K)
    (hg : PrecubicalConstructions.Hom.app g n (topCell n) = c) :
    ∀ {k : ℕ} (a : Cell n k), PrecubicalConstructions.Hom.app g k a = act c a := by
  intro k a
  induction k, a using Cell.peelRec with
  | top a => rw [eq_topCell a, hg, app_topCell]
  | step k a h ih =>
      rw [app_unfold c a h, ← ih, ← g.app_face (minFixedVal a h) (minFixedIdx a h) (freeMin a h)]
      exact congrArg _ (face_freeMin a h).symm

/-- **Cube Yoneda for a concrete precubical set**: a map `□ⁿ ⟶ K` is the same data as an
`n`-cell of `K`.  Forward is `evC`; inverse is `concreteMap`. -/
def concreteRepr (K : PrecubicalConstructions) (n : ℕ) : (stdPre n ⟶ K) ≃ K.cells n where
  toFun := evC
  invFun := concreteMap
  left_inv f := PrecubicalConstructions.hom_ext fun _k a => (app_unique f rfl a).symm
  right_inv c := app_topCell c

@[simp] theorem evC_concreteMap {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    evC (concreteMap c) = c := app_topCell c

/-- The cube inclusion `Box ⥤ PrecubicalConstructions`, `[n] ↦ □ⁿ`: a sign vector read as a
concrete map.  Functoriality is `topCell_subst`/`subst_assoc`. -/
def cubeι : Box ⥤ PrecubicalConstructions where
  obj b := stdPre b.dim
  map f := substMap (Box.sign f)
  map_id _ := PrecubicalConstructions.hom_ext fun _ a => topCell_subst a
  map_comp f g :=
    PrecubicalConstructions.hom_ext fun _ a => subst_assoc (Box.sign g) (Box.sign f) a

end StdCube

namespace PrecubicalSet

/-! ### The coface relation and the topos-level precubical identity

The topos face maps `faceMap ε i = X.map (coface ε i).op` satisfy the precubical
identity because the *cofaces* satisfy the dual relation in `Box`; that relation is
`face_face` read through cube Yoneda. -/

/-- **The coface relation in `Box`.**  For `i ≤ j`, the two ways of composing
cofaces agree: `coface ε i ≫ coface η j.succ = coface ε i.castSucc ≫ coface η j`.
This is the dual of the precubical identity, living among the *coface* box maps. -/
theorem coface_coface (ε η : Bool) {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    (coface ε i ≫ coface η j.succ : ▫n ⟶ ▫(n + 2))
      = coface η j ≫ coface ε i.castSucc := by
  refine Box.hom_ext ?_
  change Box.sign (coface ε i ≫ coface η j.succ)
    = Box.sign (coface η j ≫ coface ε i.castSucc)
  rw [Box.sign_coface_comp, Box.sign_coface_comp, Box.sign_coface, Box.sign_coface]
  exact face_face ε η hij (topCell (n + 2))

/-- **The precubical identity for topos face maps.**  Reduce to `X.map` of a single composed
box morphism and invoke `coface_coface`. -/
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
Yoneda nerve along the cube inclusion `cubeι : Box ⥤ PrecubicalConstructions`. -/
def Nerve : PrecubicalConstructions ⥤ PrecubicalSet :=
  yoneda ⋙ (Functor.whiskeringLeft Boxᵒᵖ PrecubicalConstructionsᵒᵖ Type).obj cubeι.op

/-! ### `realizeNerveIso` — the realization of the nerve recovers `K`

The nerve's `n`-cells *are* `K`'s: `(Nerve.obj K).cells n = (□ⁿ ⟶ K) ≃ K.cells n` is
`concreteRepr`.  Its compatibilities — with `K`'s faces, with `Nerve.map`, with the `Box`
action — are the two `Hom` fields and the naturality square of a single iso of functors. -/

/-- **The face action of the nerve is `K`'s.**  The one non-formal input to `realizeNerveIso`:
`evC` of a coface-precomposition faces the top cell, and `app_face` closes it. -/
theorem evC_nerve_faceMap {K : PrecubicalConstructions} {n : ℕ} (ε : Bool)
    (i : Fin (n + 1)) (f : (Nerve.obj K).cells (n + 1)) :
    evC ((Nerve.obj K).faceMap ε i f) = K.face ε i (evC f) := by
  have h1 : evC ((Nerve.obj K).faceMap ε i f)
      = PrecubicalConstructions.Hom.app f n (faceCell ε i (topCell (n + 1))) :=
    (evC_comp (cubeι.map (coface ε i)) f).trans
      (congrArg _ (evC_substMap (faceCell ε i (topCell (n + 1)))))
  rw [h1]
  exact f.app_face ε i (topCell (n + 1))

/-- **The realization of the nerve is the identity**, naturally in `K` — half of the comparison of
the two models.  Componentwise it is `concreteRepr` (`evC` forward, `concreteMap` back); the face
square is `evC_nerve_faceMap` and naturality in `K` is `evC_comp`. -/
def realizeNerveIso : Nerve ⋙ realize ≅ 𝟭 PrecubicalConstructions :=
  NatIso.ofComponents
    (fun K =>
      { hom := { app := fun _ f => evC f, app_face := fun ε i f => evC_nerve_faceMap ε i f }
        inv :=
          { app := fun _ c => concreteMap c
            app_face := fun ε i c => (concreteRepr K _).injective (by
              change evC (concreteMap (K.face ε i c))
                = evC ((Nerve.obj K).faceMap ε i (concreteMap c))
              rw [evC_concreteMap, evC_nerve_faceMap, evC_concreteMap]) }
        hom_inv_id := PrecubicalConstructions.hom_ext fun n f => (concreteRepr K n).left_inv f
        inv_hom_id := PrecubicalConstructions.hom_ext fun _ c => evC_concreteMap c })
    (fun φ => PrecubicalConstructions.hom_ext fun _ f => evC_comp f φ)

/-! ### `nerveRealizeIso` — the nerve of the realization recovers `X`

At `op b` it is `concreteRepr` at `realize X`.  Naturality against box morphisms is
`ev_realize_app`. -/

/-- **The concrete iterated-face value in the realization is `X`'s presheaf action** — the
presheaf action *is* a concrete precubical map out of `□ᴺ` (`map_ofSign_faceCell` is its
`app_face`), and `act` is the only one. -/
theorem ev_realize_app (X : PrecubicalSet) {N : ℕ} (c : X.cells N) {k : ℕ} (a : Cell N k) :
    act (K := realizeObj X) c a = X.map (Box.ofSign a).op c :=
  let g : stdPre N ⟶ realizeObj X :=
    { app := fun _ a => X.map (Box.ofSign a).op c
      app_face := fun ε i a => X.map_ofSign_faceCell c ε i a }
  (app_unique (c := c) g (X.map_ofSign_top c _) a).symm

/-- The key naturality identity, on `f : □ᴺ ⟶ realizeObj X` and a box map `h : □ᴹ ⟶ □ᴺ`:
reading `h`'s precomposition is `X`'s presheaf action along `h`. -/
theorem evC_comp_realize (X : PrecubicalSet) {M N : ℕ}
    (h : ▫M ⟶ ▫N) (f : stdPre N ⟶ realizeObj X) :
    evC (cubeι.map h ≫ f) = X.map h.op (evC f) := by
  have h1 : evC (cubeι.map h ≫ f) = PrecubicalConstructions.Hom.app f M (Box.sign h) :=
    (evC_comp _ f).trans (congrArg _ (evC_substMap (Box.sign h)))
  rw [h1]
  -- write `f = concreteMap (evC f)` to turn `Hom.app f` into `act (evC f)`
  conv_lhs => rw [show f = concreteMap (evC f) from
    ((concreteRepr (realizeObj X) N).left_inv f).symm]
  exact ev_realize_app X (evC f) (Box.sign h)

/-- **The nerve of the realization recovers `X`.**  A natural iso
`Nerve.obj (realize.obj X) ≅ X` of presheaves: at `op b` it is `concreteRepr`, and the
naturality square is `evC_comp_realize`. -/
def nerveRealizeIso (X : PrecubicalSet) : Nerve.obj (realize.obj X) ≅ X :=
  NatIso.ofComponents (fun b => (concreteRepr (realize.obj X) b.unop.dim).toIso) (by
    intro b b' g
    ext f
    exact evC_comp_realize X g.unop f)

end PrecubicalSet
