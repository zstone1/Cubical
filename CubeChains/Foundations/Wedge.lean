import CubeChains.Foundations.Bipointed
import CubeChains.Foundations.Representable
import CubeChains.Foundations.GluePushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.PNat.Basic

/-!
# Foundations/Wedge

The standard cube and wedges as `BPSet`s: `cube n` (the representable `よ[n]`,
bi-pointed at its extreme vertices), `vertexMap`/`initVertex`/`finalVertex`,
`wedge2 X Y` (the wedge `X ∨ Y` as a genuine pushout) and the `foldr` `serialWedge`.
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube

namespace BPSet
open BPSet

/-- The standard cube `□ⁿ` as a bi-pointed precubical set: the representable
presheaf `よ[n]`, bi-pointed at the constant-`0`/`1` vertices.  The vertices use
the canonical maps `□⁰ ⟶ □ⁿ` (see `canonicalMap`). -/
def cube (n : ℕ) : BPSet where
  toPsh := yoneda.obj ▫n
  init := canonicalMap (constVertex n false)
  final := canonicalMap (constVertex n true)

/-- `□⁰` has only the identity endomorphism (it is the representable point). -/
instance stdPre0_subsingleton : Subsingleton (stdPre 0 ⟶ stdPre 0) := by
  constructor; intro f g; apply PrecubicalConstructions.hom_ext; intro n
  match n with
  | 0     => intro c; apply Subtype.ext; funext i; exact i.elim0
  | (k+1) => intro c; exact absurd c.2 (by simp [noneSet])

instance : Subsingleton ((cube 0).cells 0) := stdPre0_subsingleton

/-- The map `□⁰ ⟶ X` selecting a vertex `v` of `X` (Yoneda).  Just `cubeMap` at
dimension `0`. -/
def vertexMap (X : PrecubicalSet) (v : X.cells 0) :
    yoneda.obj ▫0 ⟶ X :=
  X.cubeMap v

/-- The Yoneda inclusion `□⁰ ⟶ X` selecting `X`'s initial vertex. -/
def initVertex (X : BPSet) : yoneda.obj ▫0 ⟶ X.toPsh :=
  vertexMap X.toPsh X.init

/-- The Yoneda inclusion `□⁰ ⟶ X` selecting `X`'s final vertex. -/
def finalVertex (X : BPSet) : yoneda.obj ▫0 ⟶ X.toPsh :=
  vertexMap X.toPsh X.final

/-- The binary wedge `X ∨ Y`: glue `X.final` to `Y.init`, as the pushout of the
point `□⁰` in the topos `PrecubicalSet` (`X.finalVertex` against `Y.initVertex`).
Uses the *computable* `Glue.gluePsh` (a pointwise `Quot`) rather than the
`Classical.choice`-opaque `pushout`; `Glue.isPushout` recovers the universal property. -/
def wedge2 (X Y : BPSet) : BPSet where
  toPsh := Glue.gluePsh X.finalVertex Y.initVertex
  init := (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.init
  final := (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.final

/-- The serial wedge `□^∨(n₁,…,n_l)`: the end-to-end gluing of the standard cubes
`□^{nᵢ}` (the empty list gives the point `□⁰`). -/
def serialWedge : List ℕ+ → BPSet
  | [] => cube 0
  | n :: rest => wedge2 (cube (n : ℕ)) (serialWedge rest)

@[simp] theorem serialWedge_nil : serialWedge [] = cube 0 := rfl

theorem serialWedge_cons (n : ℕ+) (rest : List ℕ+) :
    serialWedge (n :: rest) = wedge2 (cube (n : ℕ)) (serialWedge rest) := rfl

def dimSum (a : List ℕ+) : ℕ := (a.map (fun d : ℕ+ => (d : ℕ))).sum

@[simp] theorem dimSum_sum (a : List ℕ+) : dimSum a = (a.map (fun d : ℕ+ => (d : ℕ))).sum := rfl

@[simp] theorem dimSum_append (a b : List ℕ+) : dimSum (a ++ b) = dimSum a + dimSum b := by
  simp [dimSum, List.map_append]

theorem dimSum_cons (d : ℕ+) (l : List ℕ+) : dimSum (d :: l) = (d : ℕ) + dimSum l := rfl

lemma dimSum0_nil (a : List ℕ+) : dimSum a = 0 → a = [] := by
  cases a <;> simp [dimSum]

/-- Every bead has dimension `≥ 1`, so a dimension list is at least as long as its total. -/
theorem length_le_dimSum : ∀ l : List ℕ+, l.length ≤ dimSum l
  | [] => by simp [dimSum]
  | d :: ds => by
    have ih := length_le_dimSum ds
    have hd : 0 < (d : ℕ) := d.pos
    simp only [dimSum, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- **A dimension list is determined by its total.**  Two decompositions of one list whose first
halves have the same `dimSum` have the same first half — beads have positive dimension, so the
prefix sums are strictly increasing. -/
theorem dimSum_prefix_eq : ∀ {x y u v : List ℕ+}, x ++ y = u ++ v → dimSum x = dimSum u → x = u
  | [], _, u, _, _, hs => (dimSum0_nil u hs.symm).symm
  | d :: x', y, [], v, _, hs => by
      exfalso
      simp only [dimSum, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hs
      have := d.pos
      omega
  | d :: x', y, e :: u', v, happ, hs => by
      obtain ⟨rfl, htl⟩ := List.cons_eq_cons.mp happ
      simp only [dimSum, List.map_cons, List.sum_cons] at hs
      exact congrArg (d :: ·) (dimSum_prefix_eq htl (by simp only [dimSum]; omega))

/-- The **degree** `Σ (dᵢ − 1)` of a dimension list: how far it is from being a run.  Spelled as a
sum, not as `dimSum − length`, so that `++`-additivity is a `simp` of `List.sum_append` and no
truncated subtraction appears at the top level (`degree_add_length` relates the two). -/
def degree (a : List ℕ+) : ℕ := (a.map (fun d : ℕ+ => (d : ℕ) - 1)).sum

@[simp] theorem degree_nil : degree [] = 0 := rfl

@[simp] theorem degree_cons (d : ℕ+) (a : List ℕ+) :
    degree (d :: a) = ((d : ℕ) - 1) + degree a := rfl

/-- Degree is additive over concatenation of dimension lists. -/
@[simp] theorem degree_append (a b : List ℕ+) : degree (a ++ b) = degree a + degree b := by
  simp [degree, List.sum_append]

/-- `degree` and `dimSum` differ by the bead count, with no truncated subtraction. -/
theorem degree_add_length : ∀ a : List ℕ+, degree a + a.length = dimSum a
  | [] => rfl
  | d :: ds => by
    have ih := degree_add_length ds
    have hd : 0 < (d : ℕ) := d.pos
    simp only [degree_cons, List.length_cons, dimSum, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem degree_eq_dimSum_sub_length (a : List ℕ+) : degree a = dimSum a - a.length := by
  have := degree_add_length a; omega

/-- Degree `0` is exactly the all-edges (run) condition. -/
theorem degree_eq_zero_iff : ∀ a : List ℕ+, degree a = 0 ↔ ∀ d ∈ a, d = 1
  | [] => by simp
  | d :: ds => by
    have hd : 0 < (d : ℕ) := d.pos
    have h1 : (d : ℕ) - 1 = 0 ↔ d = 1 := by rw [← PNat.coe_eq_one_iff]; omega
    rw [degree_cons, Nat.add_eq_zero_iff, h1, degree_eq_zero_iff ds]
    simp [or_imp, forall_and]

/-! ### Notation

`□n` for the standard cube, `X ∨ Y` for the binary wedge, and `⋁d` for the serial wedge — all
print, so goals read as the maths does.  `□`/`⋁` bind at `max` (write `□(n+1)`, `⋁(a ++ b)`); `∨`
is `infixr:30`, overloading `Or` (disambiguated by type: `BPSet` vs `Prop`). -/

@[inherit_doc cube] notation:max "□" n:max => BPSet.cube n
@[inherit_doc wedge2] infixr:30 " ∨ " => BPSet.wedge2
@[inherit_doc serialWedge] notation:max "⋁" d:max => BPSet.serialWedge d

def serialWedge.ι : (dims : List ℕ+) → (i : Fin dims.length) →
    ((□(dims.get i)).toPsh ⟶ (⋁dims).toPsh)
  | [], i => i.elim0
  | _ :: rest, i =>
        Fin.cases (Glue.inl _ _) (fun j => serialWedge.ι rest j ≫ Glue.inr _ _) i

/-- `ιᵂ dims i` — the inclusion of bead `i` into the serial wedge, `□(dims.get i) ⟶ ⋁dims`. -/
notation:max "ιᵂ" => BPSet.serialWedge.ι

end BPSet

namespace CubeChains

/-- An **event**: a coordinate of a bead.  (An `abbrev` so that the `Fintype` instance and the
`Sigma` pattern matches are available without unfolding.) -/
abbrev beadEvent (dims : List ℕ+) : Type := Σ i : Fin dims.length, Fin (dims.get i : ℕ)

end CubeChains
