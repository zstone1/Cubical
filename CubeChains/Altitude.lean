import CubeChains.Bipointed
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Cast.Defs

/-!
# Side conditions: altitude, accessibility, non-self-linked (ClaudeSetup.md §6)

Working over the topos `PrecubicalSet`.  The face maps are pulled back along the
*coface* box morphisms `□ⁿ ⟶ □ⁿ⁺¹` (built from `StdCube.canonicalMap`, hence
depending on the deferred cube Yoneda lemma).  `NonSelfLinked` is phrased via the
Yoneda canonical map and needs no `sorry`.
-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-- The coface `□ⁿ ⟶ □ⁿ⁺¹` selecting the `(ε, i)`-face of the top cell. -/
noncomputable def coface (ε : Bool) {n : ℕ} (i : Fin (n + 1)) : Box.ob n ⟶ Box.ob (n + 1) :=
  StdCube.canonicalMap (StdCube.face ε i (StdCube.topCell (n + 1)))

/-- The face map `cells (n+1) → cells n` of a precubical set: pull back along the
coface. -/
noncomputable def faceMap (X : PrecubicalSet) (ε : Bool) {n : ℕ} (i : Fin (n + 1))
    (c : X.cells (n + 1)) : X.cells n :=
  X.map (coface ε i).op c

/-- The canonical map `□ⁿ ⟶ X` classifying an `n`-cell `c` (Yoneda). -/
noncomputable def cubeMap (X : PrecubicalSet) {n : ℕ} (c : X.cells n) :
    yoneda.obj (Box.ob n) ⟶ X :=
  yonedaEquiv.symm c

/-- **The altitude axiom** for a candidate height function `alt` on the cells of a
precubical set `X`: altitude rises by `1` across target faces (`ε = true`) and is
unchanged across source faces (`ε = false`).  This is the inlined hypothesis that
the altitude theory below (`alt_map_eq`, `alt_vertex₀/₁`, `alt_cubeMap`) consumes;
bundling it lets callers pass `IsAltitude X alt` instead of the raw three-line `∀`. -/
def IsAltitude (X : PrecubicalSet) (alt : ∀ n, X.cells n → ℤ) : Prop :=
  ∀ {n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : X.cells (n + 1)),
    alt n (X.faceMap ε i c) = alt (n + 1) c + (if ε then 1 else 0)

/-- `X` is *non-self-linked*: the canonical map `□ⁿ ⟶ X` of every cube is injective
in every dimension (ClaudeSetup.md §6, via the Yoneda canonical map). -/
def NonSelfLinked (X : PrecubicalSet) : Prop :=
  ∀ (n : ℕ) (c : X.cells n) (m : ℕ),
    Function.Injective ((X.cubeMap c).app (op (Box.ob m)))

end PrecubicalSet

namespace BPSet

/-- `K` *admits an altitude function*: an integer height on cells rising by `1`
across target faces and unchanged across source faces, with `init` at height `0`
(ClaudeSetup.md §6). -/
def AdmitsAltitude (K : BPSet) : Prop :=
  ∃ alt : ∀ n, K.toPsh.cells n → ℤ,
    K.toPsh.IsAltitude alt ∧ alt 0 K.init = 0

/-- The one-step reachability relation generating the accessibility preorder:
`face false i c ≼ c` and `c ≼ face true i c`, closed under reflexivity and
transitivity, on cells of all dimensions. -/
inductive Reach (K : BPSet) : (Σ n, K.toPsh.cells n) → (Σ n, K.toPsh.cells n) → Prop
  | refl (x) : Reach K x x
  | source {n} (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) :
      Reach K ⟨n, K.toPsh.faceMap false i c⟩ ⟨n + 1, c⟩
  | target {n} (i : Fin (n + 1)) (c : K.toPsh.cells (n + 1)) :
      Reach K ⟨n + 1, c⟩ ⟨n, K.toPsh.faceMap true i c⟩
  | trans {x y z} : Reach K x y → Reach K y z → Reach K x z

/-- `K` is *accessible*: every cell lies between `init` and `final` for the
reachability preorder (ClaudeSetup.md §6). -/
def Accessible (K : BPSet) : Prop :=
  ∀ c : Σ n, K.toPsh.cells n, Reach K ⟨0, K.init⟩ c ∧ Reach K c ⟨0, K.final⟩

/-- `K` is *non-self-linked*: the canonical map `□ⁿ ⟶ K` of every cube is
injective in every dimension (ClaudeSetup.md §6, via the Yoneda canonical map).
Thin wrapper around `PrecubicalSet.NonSelfLinked` on the underlying presheaf. -/
def NonSelfLinked (K : BPSet) : Prop := K.toPsh.NonSelfLinked

end BPSet

/-! ### Altitude of pulled-back cells: the `trueCount` invariant

For the embedding theorem (`descent_mono`) we need that pulling a cell `c : K.cells n`
back along a box morphism (a cell `a` of `□ⁿ`) shifts altitude by the number of
coordinates that `a` fixes to `true`.  `trueCount a` counts those. -/

namespace StdCube

open Finset

/-- The number of coordinates a cell of `□ⁿ` fixes to `true`. -/
def trueCount {N k : ℕ} (a : cells N k) : ℕ :=
  (Finset.univ.filter (fun j => a.val j = some true)).card

theorem trueCount_topCell (N : ℕ) : trueCount (topCell N) = 0 := by
  rw [trueCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  simp [topCell]

theorem trueCount_constVertex_false (N : ℕ) : trueCount (constVertex N false) = 0 := by
  rw [trueCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  simp [constVertex]

theorem trueCount_constVertex_true (N : ℕ) : trueCount (constVertex N true) = N := by
  have h : (Finset.univ.filter (fun j => (constVertex N true).val j = some true))
      = Finset.univ := Finset.filter_true_of_mem (fun j _ => rfl)
  rw [trueCount, h, Finset.card_univ, Fintype.card_fin]

/-- A vertex (`0`-cell) all of whose coordinates are `true` is the all-`true` vertex. -/
theorem trueCount_eq_top {n : ℕ} (c : cells n 0) (hc : trueCount c = n) :
    c = constVertex n true := by
  apply Subtype.ext
  funext j
  have hfilter : Finset.univ.filter (fun j => c.val j = some true) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]; exact hc
  have hj : j ∈ Finset.univ.filter (fun j => c.val j = some true) := by
    rw [hfilter]; exact Finset.mem_univ j
  rw [Finset.mem_filter] at hj
  exact hj.2

/-- `trueCount` is bounded by the number of fixed coordinates `N - k`. -/
theorem trueCount_le {N k : ℕ} (a : cells N k) : trueCount a ≤ N - k := by
  rw [← fixedSet_card a]
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [fixedSet, Finset.mem_compl, mem_noneSet, hj.2]
  simp

/-- Facing a free coordinate to `ε` raises `trueCount` by `ε`. -/
theorem trueCount_face {N k : ℕ} (ε : Bool) (i : Fin (k + 1)) (b : cells N (k + 1)) :
    trueCount (face ε i b) = trueCount b + (if ε then 1 else 0) := by
  have hq : b.val (nones b i) = none := by
    rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ b.prop i
  cases ε with
  | false =>
      rw [if_neg (by simp), Nat.add_zero, trueCount, trueCount]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro j _
      by_cases hj : j = nones b i
      · subst hj; rw [face_val, Function.update_self]; simp [hq]
      · rw [face_val, Function.update_of_ne hj]
  | true =>
      rw [if_pos rfl, trueCount, trueCount]
      have hqnot : nones b i ∉ Finset.univ.filter (fun j => b.val j = some true) := by
        rw [Finset.mem_filter, hq]; simp
      have hins : Finset.univ.filter (fun j => (face true i b).val j = some true)
          = insert (nones b i) (Finset.univ.filter (fun j => b.val j = some true)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hj : j = nones b i
        · subst hj; rw [face_val, Function.update_self]; simp
        · rw [face_val, Function.update_of_ne hj]; simp [hj]
      rw [hins, Finset.card_insert_of_notMem hqnot]

/-- Freeing the smallest fixed coordinate drops `trueCount` by its (boolean) value. -/
theorem trueCount_freeMin {N k : ℕ} (a : cells N k) (h : k < N) :
    trueCount a = trueCount (freeMin a h) + (if minFixedVal a h then 1 else 0) := by
  conv_lhs => rw [← face_freeMin a h]
  rw [trueCount_face]

/-- Evaluating a canonical map at the top cell recovers the cell (cube Yoneda). -/
theorem ev_canonicalMap {K : PrecubicalConstructions} {n : ℕ} (c : K.cells n) :
    ev (canonicalMap c) = c := app_topCell c

/-- `ev` of a coface is the corresponding face of the top cell. -/
theorem ev_coface {k : ℕ} (ε : Bool) (i : Fin (k + 1)) :
    ev (PrecubicalSet.coface ε i) = face ε i (topCell (k + 1)) :=
  ev_canonicalMap _

/-- `ev` of a composite peels the first factor (cube Yoneda + composition). -/
theorem ev_comp {A : PrecubicalConstructions} {n : ℕ} (f : stdPre n ⟶ A)
    {K : PrecubicalConstructions} (g : A ⟶ K) :
    ev (f ≫ g) = PrecubicalConstructions.Hom.app g n (ev f) := rfl

/-- **Coface peeling of a canonical map.**  A non-top cell `c'` of `□ᴺ` factors its
canonical map through the smallest-fixed-coordinate coface. -/
theorem canonicalMap_peel {N k : ℕ} (c' : cells N k) (h : k < N) :
    canonicalMap c' = PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
      ≫ canonicalMap (freeMin c' h) := by
  have hev : ev ((PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
      ≫ canonicalMap (freeMin c' h) : stdPre k ⟶ stdPre N)) = c' := by
    rw [ev_comp, ev_coface, canonicalMap_app, app_face, app_topCell]
    exact face_freeMin c' h
  symm
  apply PrecubicalConstructions.hom_ext
  intro m a
  rw [canonicalMap_app]
  exact app_unique _ hev a

/-- The canonical map of the top cell is the identity. -/
theorem canonicalMap_topCell (N : ℕ) : canonicalMap (topCell N) = 𝟙 (stdPre N) := by
  symm
  apply PrecubicalConstructions.hom_ext
  intro m a
  rw [canonicalMap_app]
  exact app_unique (𝟙 (stdPre N)) rfl a

end StdCube

namespace PrecubicalSet

open StdCube CategoryTheory Opposite

variable {X : PrecubicalSet}

/-- **Altitude of a pulled-back cell.**  Pulling `x : X.cells N` back along the box
morphism classified by a cell `c'` of `□ᴺ` shifts altitude by the number of
coordinates `c'` fixes to `true`.  Proved by peeling cofaces (`canonicalMap_peel`),
using the altitude axiom (`IsAltitude`) one face at a time. -/
theorem alt_map_eq (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) :
    ∀ {k : ℕ} (c' : StdCube.cells N k),
      alt k (X.map (StdCube.canonicalMap c').op x) = alt N x + StdCube.trueCount c' := by
  intro k c'
  induction hd : N - k using Nat.strong_induction_on generalizing k c' with
  | _ d ih =>
    rcases Nat.lt_or_ge k N with h | h
    · have e1 : X.map (StdCube.canonicalMap c').op x
          = X.map (PrecubicalSet.coface (minFixedVal c' h) (minFixedIdx c' h)
              ≫ canonicalMap (freeMin c' h)).op x :=
        congrArg (fun m => X.map (Quiver.Hom.op m) x) (canonicalMap_peel c' h)
      have hstep : X.map (StdCube.canonicalMap c').op x
          = X.faceMap (minFixedVal c' h) (minFixedIdx c' h)
            (X.map (StdCube.canonicalMap (freeMin c' h)).op x) := by
        rw [e1, op_comp, Functor.map_comp]; rfl
      rw [hstep, hax, ih (N - (k + 1)) (by omega) (freeMin c' h) rfl, trueCount_freeMin c' h]
      cases minFixedVal c' h <;> push_cast <;> ring
    · have hkN : k = N := le_antisymm (cells_card_le c') h
      subst hkN
      rw [eq_topCell c']
      erw [canonicalMap_topCell, op_id, X.map_id]
      simp [trueCount_topCell]

/-- The altitude of the source vertex equals the altitude of the cell. -/
theorem alt_vertex₀ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertex₀ x) = alt N x := by
  have h := alt_map_eq alt hax x (StdCube.constVertex N false)
  rwa [trueCount_constVertex_false, Nat.cast_zero, add_zero] at h

/-- The altitude of the target vertex is `N` above the cell's altitude. -/
theorem alt_vertex₁ (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {N : ℕ} (x : X.cells N) : alt 0 (X.vertex₁ x) = alt N x + N := by
  have h := alt_map_eq alt hax x (StdCube.constVertex N true)
  rwa [trueCount_constVertex_true] at h

/-- The altitude of a face `(cubeMap c).app x` of an `n`-cube `c`, classified by a
box morphism `x : □ᵐ ⟶ □ⁿ`, exceeds `alt c` by `trueCount (ev x) ≤ n - m`. -/
theorem alt_cubeMap (alt : ∀ n, X.cells n → ℤ) (hax : X.IsAltitude alt)
    {n : ℕ} (c : X.cells n) {m : ℕ} (x : Box.ob m ⟶ Box.ob n) :
    alt m ((X.cubeMap c).app (op (Box.ob m)) x)
      = alt n c + StdCube.trueCount (StdCube.ev x) := by
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  conv_lhs => rw [show x = StdCube.canonicalMap (StdCube.ev x) from
    ((cubeRepr (stdPre n) m).left_inv x).symm]
  exact alt_map_eq alt hax c (StdCube.ev x)

end PrecubicalSet
