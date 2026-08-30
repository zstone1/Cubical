import CubeChains.Machinery.Braid.PosGerm
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Graded — the total category of a family of monoids graded by `ℕ`

`Graded M` has a degree for each object and `End n = M n`; there are no morphisms between different
degrees.  A morphism carries its element on the **source** degree, so the degree transport lives
once, in composition — a functor *into* `Graded M` maps each arrow to its element with no `eqToHom`
bookkeeping.

The two instances: `FullPosBraid = Graded PosBraid`, the receptacle of the positive braid grading,
and `FullBraid = Graded Braid`, a groupoid because each `Braid n` is a group.
-/

open CategoryTheory

namespace CubeChains

/-- A morphism of `Graded M`: the (forced) equality of degrees, and an element of the source's
monoid. -/
@[ext]
structure GradedHom (M : ℕ → Type*) (m n : ℕ) where
  /-- Source and target degrees agree — `Graded M` has no cross-degree morphisms. -/
  deg : m = n
  /-- The element, at the source degree. -/
  val : M m

/-- **The total category of a graded family of monoids.**  The family is a phantom parameter: it
names the hom-sets through the `Category` instance, not the objects. -/
def Graded (_M : ℕ → Type*) : Type := ℕ

namespace Graded

variable {M : ℕ → Type*} [∀ n, Monoid (M n)]

instance : Category (Graded M) where
  Hom m n := GradedHom M m n
  id _ := ⟨rfl, 1⟩
  comp f g := ⟨f.deg.trans g.deg, (f.deg.symm ▸ g.val) * f.val⟩
  id_comp f := by obtain ⟨h, b⟩ := f; subst h; simp
  comp_id f := by obtain ⟨h, b⟩ := f; subst h; simp
  assoc f g k := by
    obtain ⟨hf, bf⟩ := f; obtain ⟨hg, bg⟩ := g; obtain ⟨hk, bk⟩ := k
    subst hf; subst hg; subst hk; simp [mul_assoc]

/-- An element, read as an endomorphism of its degree. -/
def ofVal {n : ℕ} (b : M n) : @Quiver.Hom (Graded M) _ n n := ⟨rfl, b⟩

@[simp] theorem ofVal_one (n : ℕ) :
    ofVal (1 : M n) = @CategoryStruct.id (Graded M) _ n := rfl

/-- `ofVal` is multiplicative in the concurrency convention `p (f ≫ g) = p g * p f`. -/
@[simp] theorem ofVal_comp {n : ℕ} (a b : M n) :
    ofVal a ≫ ofVal b = ofVal (b * a) := rfl

/-- A degree identification, as a morphism. -/
def ofDeg {m n : ℕ} (h : m = n) : @Quiver.Hom (Graded M) _ m n := ⟨h, 1⟩

/-- **The degree-`n` component**: one object, `M n` on it. -/
def single (n : ℕ) : SingleObj (M n) ⥤ Graded M where
  obj _ := n
  map b := ofVal b
  map_id _ := rfl
  map_comp _ _ := rfl

instance single_faithful (n : ℕ) : (single (M := M) n).Faithful where
  map_injective h := congrArg GradedHom.val h

instance single_full (n : ℕ) : (single (M := M) n).Full where
  map_surjective f := ⟨f.val, GradedHom.ext rfl⟩

/-- The degrees, assembled. -/
def sigmaDesc : (Σ n : ℕ, SingleObj (M n)) ⥤ Graded M := Sigma.desc (single (M := M))

instance : (sigmaDesc (M := M)).Faithful where
  map_injective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨g⟩ h
    obtain rfl : f = g := congrArg GradedHom.val h
    rfl

instance : (sigmaDesc (M := M)).Full where
  map_surjective := by
    rintro ⟨i, _⟩ ⟨j, _⟩ h
    obtain rfl : i = j := h.deg
    exact ⟨Sigma.SigmaHom.mk h.val, GradedHom.ext rfl⟩

instance : (sigmaDesc (M := M)).EssSurj where
  mem_essImage Y := ⟨⟨Y, SingleObj.star _⟩, ⟨Iso.refl Y⟩⟩

instance : (sigmaDesc (M := M)).IsEquivalence where

/-- **A graded family of monoids is the coproduct of its degrees** — there are no cross-degree
morphisms. -/
noncomputable def sigmaEquivalence : (Σ n : ℕ, SingleObj (M n)) ≌ Graded M :=
  (sigmaDesc (M := M)).asEquivalence

section Map

variable {N : ℕ → Type*} [∀ n, Monoid (N n)]

/-- A monoid map in each degree, as a functor of the total categories. -/
def map (e : ∀ n, M n →* N n) : Graded M ⥤ Graded N where
  obj n := n
  map f := ⟨f.deg, e _ f.val⟩
  map_id _ := GradedHom.ext (map_one _)
  map_comp f g := by
    obtain ⟨hf, bf⟩ := f; obtain ⟨hg, bg⟩ := g
    subst hf; subst hg
    exact GradedHom.ext (map_mul _ _ _)

/-- **A degreewise isomorphism of the families is an equivalence of the total categories** — the
objects are the degrees either way, so only the hom-monoids move. -/
noncomputable def congr (e : ∀ n, M n ≃* N n) : Graded M ≌ Graded N := by
  haveI : (map fun n => (e n).toMonoidHom).Faithful :=
    ⟨fun {X _ _ _} h => GradedHom.ext ((e X).injective (congrArg GradedHom.val h))⟩
  haveI : (map fun n => (e n).toMonoidHom).Full :=
    ⟨fun {X _} h => ⟨⟨h.deg, (e X).symm h.val⟩, GradedHom.ext ((e X).apply_symm_apply h.val)⟩⟩
  haveI : (map fun n => (e n).toMonoidHom).EssSurj := ⟨fun Y => ⟨Y, ⟨Iso.refl _⟩⟩⟩
  haveI : (map fun n => (e n).toMonoidHom).IsEquivalence := {}
  exact (map fun n => (e n).toMonoidHom).asEquivalence

end Map

instance isIso_ofDeg {m n : ℕ} (h : m = n) :
    IsIso (ofDeg h : @Quiver.Hom (Graded M) _ m n) := by
  subst h
  change IsIso (@CategoryStruct.id (Graded M) _ m)
  infer_instance

instance {M : ℕ → Type*} [∀ n, Group (M n)] : Groupoid (Graded M) where
  inv f := ⟨f.deg.symm, f.deg ▸ f.val⁻¹⟩
  inv_comp f := by obtain ⟨h, b⟩ := f; subst h; exact GradedHom.ext (mul_inv_cancel b)
  comp_inv f := by obtain ⟨h, b⟩ := f; subst h; exact GradedHom.ext (inv_mul_cancel b)

/-! ## Permutation cocycles

A grading valued in `Graded M` is a cocycle of permutations that never crosses a pair twice.
`Germ M` is what the target must supply for that to compose: the simples, multiplicative at every
length-additive product.  `Germ.hom_comp` then discharges the composition law once, for `Braid`,
`PosBraid` and anything else. -/

/-- **A germ family**: simples valued in a graded monoid, multiplicative at every length-additive
product. -/
structure Germ (M : ℕ → Type*) [∀ n, Monoid (M n)] where
  /-- The simple of a permutation. -/
  val : ∀ {n : ℕ}, Equiv.Perm (Fin n) → M n
  val_one : ∀ n : ℕ, val (1 : Equiv.Perm (Fin n)) = 1
  val_mul : ∀ {n : ℕ} (σ τ : Equiv.Perm (Fin n)),
    permLen (σ * τ) = permLen σ + permLen τ → val σ * val τ = val (σ * τ)

/-- A permutation of the source degree, as a morphism. -/
def Germ.hom (G : Germ M) {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    @Quiver.Hom (Graded M) _ m n := ⟨h, G.val σ⟩

@[simp] theorem Germ.hom_one (G : Germ M) (n : ℕ) :
    G.hom rfl (1 : Equiv.Perm (Fin n)) = @CategoryStruct.id (Graded M) _ n :=
  GradedHom.ext (G.val_one n)

/-- **The trivial simple is the degree identification** — the shape a grading takes on a class it
inverts. -/
theorem Germ.hom_one_eq_ofDeg (G : Germ M) {m n : ℕ} (h : m = n) :
    G.hom h (1 : Equiv.Perm (Fin m)) = ofDeg h :=
  GradedHom.ext (G.val_one m)

/-- **The germ relation, in `Graded M`**: `ρ` is the composite cocycle (`hmul`) and no pair crosses
twice (`H`), so the two simples multiply to `ρ`'s. -/
theorem Germ.hom_comp (G : Germ M) {m n p : ℕ} (hmn : m = n) (hnp : n = p)
    {σ : Equiv.Perm (Fin m)} {τ : Equiv.Perm (Fin n)} {ρ : Equiv.Perm (Fin m)}
    (hmul : ∀ i, finCongr hmn (ρ i) = τ (finCongr hmn (σ i)))
    (H : ∀ i j : Fin m, i < j → σ j < σ i →
      τ (finCongr hmn (σ j)) < τ (finCongr hmn (σ i))) :
    G.hom hmn σ ≫ G.hom hnp τ = G.hom (hmn.trans hnp) ρ := by
  have hlen := permLen_of_cocycle_noDoubleCross hmn hmul H
  subst hmn
  simp only [finCongr_refl, Equiv.refl_apply] at hmul hlen
  obtain rfl : ρ = τ * σ := Equiv.ext hmul
  refine GradedHom.ext ?_
  change G.val τ * G.val σ = G.val (τ * σ)
  exact G.val_mul τ σ (by omega)

end Graded

/-- The braid germ: `ofPerm`, with the relation `Braid n` is presented by. -/
def braidGerm : Graded.Germ Braid where
  val := ofPerm
  val_one _ := ofPerm_one
  val_mul _ _ h := ofPerm_mul h

/-- The positive braid germ: `posPerm`, with the same relation read in the monoid. -/
def posGerm : Graded.Germ PosBraid where
  val := posPerm
  val_one _ := posPerm_one
  val_mul _ _ h := posPerm_mul h

/-- **The positive braid grading's receptacle**: degrees as objects, `End n = PosBraid n`. -/
abbrev FullPosBraid : Type := Graded PosBraid

/-- **The full braid groupoid**: strand counts as objects, braids as (endo)morphisms. -/
abbrev FullBraid : Type := Graded Braid

end CubeChains
