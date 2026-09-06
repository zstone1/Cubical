import CubeChains.Machinery.Braid.PosGerm
import Mathlib.CategoryTheory.Groupoid

/-!
# Machinery/Graded — the total category of a family of monoids graded by `ℕ`

`Graded M` has a degree for each object and `End n = M n`; there are no morphisms between different
degrees.  A morphism carries its element on the **source** degree, so the degree transport lives
once, in composition — a functor *into* `Graded M` maps each arrow to its element with no `eqToHom`
bookkeeping.  `FullBraid = Graded Braid` is the receptacle of `Conc`, a groupoid because each
`Braid n` is a group.
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

/-- A degree identification, as a morphism. -/
def ofDeg {m n : ℕ} (h : m = n) : @Quiver.Hom (Graded M) _ m n := ⟨h, 1⟩

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

/-- **The germ relation, in `Graded M`**: two simples read at the *source* degree that cross no pair
twice (`H`) multiply, whatever degrees they are named at. -/
theorem Germ.hom_comp (G : Germ M) {m n p : ℕ} (hmn : m = n) (hnp : n = p)
    {σ τ : Equiv.Perm (Fin m)}
    (H : ∀ i j : Fin m, i < j → σ j < σ i → τ (σ j) < τ (σ i)) :
    G.hom hmn σ ≫ G.hom hnp ((finCongr hmn).permCongr τ) = G.hom (hmn.trans hnp) (τ * σ) := by
  subst hmn
  refine GradedHom.ext ?_
  change G.val ((finCongr rfl).permCongr τ) * G.val σ = G.val (τ * σ)
  rw [show (finCongr rfl).permCongr τ = τ from Equiv.ext fun _ => rfl]
  exact G.val_mul τ σ ((permLen_mul_of_noDoubleCross H).trans (Nat.add_comm _ _))

end Graded

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
