import CubeChains.Machinery.Braid.Sum
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Machinery/Graded — the total category of a family of monoids graded by `ℕ`

`Graded M` has a degree for each object and `End n = M n`; there are no morphisms between different
degrees.  A morphism carries its element on the **source** degree, so the degree transport lives
once, in composition — a functor *into* `Graded M` maps each arrow to its element with no `eqToHom`
bookkeeping.  `FullBraid = Graded Braid` is the receptacle of `ConcPos`, a groupoid because each
`Braid n` is a group.

A `Tensor` makes it **monoidal** over the addition of degrees: the associator and the unitors are
degree identifications, which carry the trivial element, so all the coherence is `ext_of_val_one`
and only the naturality squares have content.  `posTensor` is `permSum` read in the monoid.
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

@[simp] theorem ofDeg_val {m n : ℕ} (h : m = n) :
    (ofDeg h : @Quiver.Hom (Graded M) _ m n).val = 1 := rfl

/-- Transport an element along an equality of degrees. -/
def congrDeg {m n : ℕ} (h : m = n) : M m ≃* M n := by subst h; exact MulEquiv.refl _

@[simp] theorem congrDeg_symm_apply {m n : ℕ} (h : m = n) (a : M m) :
    congrDeg h.symm (congrDeg h a) = a := by subst h; rfl

theorem congrDeg_eq_symm {m n : ℕ} (h : m = n) {a : M m} {b : M n} (hab : congrDeg h a = b) :
    a = congrDeg h.symm b := by subst h; exact hab

/-- **A composite's element lives at the source degree** — the transport is the only place a
degree identification is spent. -/
theorem val_comp {m n p : ℕ} (f : @Quiver.Hom (Graded M) _ m n)
    (g : @Quiver.Hom (Graded M) _ n p) : (f ≫ g).val = congrDeg f.deg.symm g.val * f.val := by
  obtain ⟨hd, b⟩ := f; subst hd; rfl

/-- **A morphism performing nothing is a degree identification**, so any two parallel ones agree. -/
theorem ext_of_val_one {m n : ℕ} {f g : @Quiver.Hom (Graded M) _ m n}
    (hf : f.val = 1) (hg : g.val = 1) : f = g := GradedHom.ext (hf.trans hg.symm)

theorem val_comp_eq_one {m n p : ℕ} {f : @Quiver.Hom (Graded M) _ m n}
    {g : @Quiver.Hom (Graded M) _ n p} (hf : f.val = 1) (hg : g.val = 1) : (f ≫ g).val = 1 := by
  rw [val_comp, hf, hg, map_one, mul_one]

/-- An element, as a loop at its degree. -/
def loop {n : ℕ} (b : M n) : @Quiver.Hom (Graded M) _ n n := ⟨rfl, b⟩

@[simp] theorem loop_val {n : ℕ} (b : M n) : (loop b).val = b := rfl

/-- A degree identification, as an isomorphism. -/
def isoOfDeg {m n : ℕ} (h : m = n) : @Iso (Graded M) _ m n where
  hom := ofDeg h
  inv := ofDeg h.symm
  hom_inv_id := ext_of_val_one (val_comp_eq_one rfl rfl) rfl
  inv_hom_id := ext_of_val_one (val_comp_eq_one rfl rfl) rfl

@[simp] theorem isoOfDeg_hom_val {m n : ℕ} (h : m = n) :
    (isoOfDeg (M := M) h).hom.val = 1 := rfl

section DescOp

variable {C : Type*} [Category* C] (F : ℕ → C) (φ : ∀ n : ℕ, M n →* (End (F n))ᵐᵒᵖ)

/-- The arrow an element at degree `n` names, read at a degree it is identified with. -/
def descOpMap {m n : ℕ} (h : n = m) (b : M n) : F m ⟶ F n :=
  eqToHom (congrArg F h.symm) ≫ (φ n b).unop

@[simp] theorem descOpMap_one (n : ℕ) : descOpMap F φ (rfl : n = n) 1 = 𝟙 (F n) := by
  rw [descOpMap, eqToHom_refl, Category.id_comp, map_one]; rfl

theorem descOpMap_comp {m n p : ℕ} (h₁ : n = m) (h₂ : p = n) (b : M n) (c : M p) :
    descOpMap F φ (h₂.trans h₁) ((h₂.symm ▸ b) * c)
      = descOpMap F φ h₁ b ≫ descOpMap F φ h₂ c := by
  subst h₁; subst h₂
  rw [descOpMap, descOpMap, descOpMap, eqToHom_refl, Category.id_comp, Category.id_comp,
    Category.id_comp, map_mul]
  rfl

/-- **A functor out of `(Graded M)ᵒᵖ`**: an object per degree, and a monoid homomorphism into its
endomorphisms.  The `ᵐᵒᵖ` is the composition order — `End` multiplies backwards — and the degree
identification carries no element. -/
def descOp : (Graded M)ᵒᵖ ⥤ C where
  obj X := F X.unop
  map f := descOpMap F φ f.unop.deg f.unop.val
  map_id X := descOpMap_one F φ X.unop
  map_comp _ _ := descOpMap_comp F φ _ _ _ _

@[simp] theorem descOp_obj (n : ℕ) : (descOp F φ).obj (Opposite.op n) = F n := rfl

@[simp] theorem descOp_map {m n : ℕ} (f : (Opposite.op m : (Graded M)ᵒᵖ) ⟶ Opposite.op n) :
    (descOp F φ).map f = descOpMap F φ f.unop.deg f.unop.val := rfl

end DescOp

/-! ## …as the disjoint union of its degrees

A presentation is assembled degree by degree, so the graded category has to be recognised as the
disjoint union of the one-object categories it is made of.  The comparison is the identity on
degrees, which is what keeps a 0-cell's naming strict. -/

/-- The degree-`n` component, inside the graded total category. -/
def singleObjIncl (n : ℕ) : (SingleObj (M n))ᵒᵖ ⥤ (Graded M)ᵒᵖ where
  obj _ := Opposite.op n
  map f := Quiver.Hom.op (⟨rfl, f.unop⟩ : @Quiver.Hom (Graded M) _ n n)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The graded category is the disjoint union of its degrees.** -/
def sigmaDesc : (Σ n : ℕ, (SingleObj (M n))ᵒᵖ) ⥤ (Graded M)ᵒᵖ := Sigma.desc singleObjIncl

@[simp] theorem sigmaDesc_obj (n : ℕ) (x : (SingleObj (M n))ᵒᵖ) :
    (sigmaDesc (M := M)).obj ⟨n, x⟩ = Opposite.op n := rfl

instance sigmaDesc_faithful : (sigmaDesc (M := M)).Faithful where
  map_injective {X Y f g} h := by
    obtain ⟨m, x⟩ := X
    obtain ⟨n, y⟩ := Y
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    refine congrArg Sigma.SigmaHom.mk (Quiver.Hom.unop_inj ?_)
    exact congrArg (fun t : (Opposite.op m : (Graded M)ᵒᵖ) ⟶ Opposite.op m => t.unop.val) h

instance sigmaDesc_full : (sigmaDesc (M := M)).Full where
  map_surjective {X Y} h := by
    obtain ⟨m, x⟩ := X
    obtain ⟨n, y⟩ := Y
    obtain hmn : n = m := h.unop.deg
    subst hmn
    exact ⟨Sigma.SigmaHom.mk (Quiver.Hom.op (X := x.unop) (Y := y.unop) h.unop.val),
      Quiver.Hom.unop_inj (GradedHom.ext rfl)⟩

instance sigmaDesc_essSurj : (sigmaDesc (M := M)).EssSurj where
  mem_essImage X := ⟨⟨X.unop, Opposite.op (SingleObj.star (M X.unop))⟩, ⟨Iso.refl _⟩⟩

instance sigmaDesc_isEquivalence : (sigmaDesc (M := M)).IsEquivalence where

/-- **…as an equivalence**, the identity on degrees. -/
noncomputable def sigmaEquiv : (Σ n : ℕ, (SingleObj (M n))ᵒᵖ) ≌ (Graded M)ᵒᵖ :=
  sigmaDesc.asEquivalence

/-! ## Juxtaposition

A block sum makes `Graded M` monoidal, over the addition of degrees.  The associator and the two
unitors are *degree identifications*, which carry the trivial element, so the pentagon and the
triangle are free (`ext_of_val_one`); only the naturality squares have content, and each of them is
one of the block sum's own laws. -/

/-- **A block sum on a graded family**: degrees add and elements juxtapose. -/
structure Tensor (M : ℕ → Type*) [∀ n, Monoid (M n)] where
  /-- the juxtaposition -/
  sum : ∀ {m n : ℕ}, M m × M n →* M (m + n)
  /-- …associative, up to the identification of the two bracketings of the degree -/
  sum_assoc : ∀ {m n p : ℕ} (a : M m) (b : M n) (c : M p),
    congrDeg (Nat.add_assoc m n p) (sum (sum (a, b), c)) = sum (a, sum (b, c))
  /-- …with the empty block as a unit on the left, where the degree is only renumbered -/
  sum_one_left : ∀ {n : ℕ} (a : M n), sum ((1 : M 0), a) = congrDeg (Nat.zero_add n).symm a
  /-- …and on the right, where `n + 0` is already `n` -/
  sum_one_right : ∀ {n : ℕ} (a : M n), sum (a, (1 : M 0)) = a

namespace Tensor

variable (T : Tensor M)

/-- Two morphisms, side by side. -/
def hom {m n m' n' : ℕ} (f : @Quiver.Hom (Graded M) _ m m') (g : @Quiver.Hom (Graded M) _ n n') :
    @Quiver.Hom (Graded M) _ (m + n) (m' + n') :=
  ⟨congrArg₂ (· + ·) f.deg g.deg, T.sum (f.val, g.val)⟩

@[simp] theorem hom_val {m n m' n' : ℕ} (f : @Quiver.Hom (Graded M) _ m m')
    (g : @Quiver.Hom (Graded M) _ n n') : (T.hom f g).val = T.sum (f.val, g.val) := rfl

theorem hom_id (m n : ℕ) :
    T.hom (@CategoryStruct.id (Graded M) _ m) (@CategoryStruct.id (Graded M) _ n)
      = @CategoryStruct.id (Graded M) _ (m + n) :=
  GradedHom.ext (map_one _)

theorem hom_val_one {m n m' n' : ℕ} {f : @Quiver.Hom (Graded M) _ m m'}
    {g : @Quiver.Hom (Graded M) _ n n'} (hf : f.val = 1) (hg : g.val = 1) :
    (T.hom f g).val = 1 := by
  rw [hom_val, hf, hg]; exact map_one _

theorem hom_comp {m₁ m₂ m₃ n₁ n₂ n₃ : ℕ} (f₁ : @Quiver.Hom (Graded M) _ m₁ m₂)
    (f₂ : @Quiver.Hom (Graded M) _ m₂ m₃) (g₁ : @Quiver.Hom (Graded M) _ n₁ n₂)
    (g₂ : @Quiver.Hom (Graded M) _ n₂ n₃) :
    T.hom f₁ g₁ ≫ T.hom f₂ g₂ = T.hom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  obtain ⟨h₁, a₁⟩ := f₁; obtain ⟨h₂, a₂⟩ := f₂
  obtain ⟨k₁, b₁⟩ := g₁; obtain ⟨k₂, b₂⟩ := g₂
  subst h₁; subst h₂; subst k₁; subst k₂
  exact GradedHom.ext ((map_mul T.sum (a₂, b₂) (a₁, b₁)).symm)

/-- **A block sum makes `Graded M` monoidal.** -/
@[reducible] def monoidal : MonoidalCategory (Graded M) where
  tensorObj m n := Nat.add m n
  whiskerLeft X _ _ f := T.hom (𝟙 X) f
  whiskerRight f Y := T.hom f (𝟙 Y)
  tensorHom f g := T.hom f g
  tensorUnit := (0 : ℕ)
  associator X Y Z := isoOfDeg (Nat.add_assoc X Y Z)
  leftUnitor X := isoOfDeg (Nat.zero_add X)
  rightUnitor X := isoOfDeg (Nat.add_zero X)
  tensorHom_def f g := by
    rw [T.hom_comp, Category.comp_id, Category.id_comp]
  id_tensorHom_id := T.hom_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := T.hom_comp f₁ g₁ f₂ g₂
  whiskerLeft_id X Y := T.hom_id X Y
  id_whiskerRight X Y := T.hom_id X Y
  associator_naturality f₁ f₂ f₃ := GradedHom.ext (by
    simp only [val_comp, isoOfDeg_hom_val, map_one, one_mul, mul_one, hom_val]
    exact congrDeg_eq_symm _ (T.sum_assoc _ _ _))
  leftUnitor_naturality f := GradedHom.ext (by
    simp only [val_comp, isoOfDeg_hom_val, map_one, one_mul, mul_one, hom_val]
    exact T.sum_one_left f.val)
  rightUnitor_naturality f := GradedHom.ext (by
    simp only [val_comp, isoOfDeg_hom_val, map_one, one_mul, mul_one, hom_val]
    exact T.sum_one_right f.val)
  pentagon _ _ _ _ := by
    refine ext_of_val_one ?_ ?_
    · exact val_comp_eq_one (T.hom_val_one rfl rfl)
        (val_comp_eq_one rfl (T.hom_val_one rfl rfl))
    · exact val_comp_eq_one rfl rfl
  triangle _ _ := by
    refine ext_of_val_one ?_ ?_
    · exact val_comp_eq_one rfl (T.hom_val_one rfl rfl)
    · exact T.hom_val_one rfl rfl

end Tensor

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

/-! ## The braid tensor

`FullPosBraid` is monoidal over the addition of strand counts, `posSum` juxtaposing the braids.
Each law is one `permSum` identity read on the simples: `posPerm` generates, so a homomorphism out
of a braid monoid is pinned there. -/

theorem congrDeg_posPerm {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    Graded.congrDeg (M := PosBraid) h (posPerm σ) = posPerm ((finCongr h).permCongr σ) := by
  subst h
  exact congrArg posPerm (Equiv.ext fun _ => rfl)

theorem congrDeg_posSumL_posSumL {m n p : ℕ} :
    (Graded.congrDeg (M := PosBraid) (Nat.add_assoc m n p)).toMonoidHom.comp
        ((posSumL (m + n) p).comp (posSumL m n)) = posSumL m (n + p) :=
  posPerm_ext fun σ => by
    change Graded.congrDeg _ (posSumL (m + n) p (posSumL m n (posPerm σ)))
      = posSumL m (n + p) (posPerm σ)
    rw [posSumL_posPerm, posSumL_posPerm, congrDeg_posPerm, posSumL_posPerm, permSum_assoc,
      permSum_one_one]

theorem congrDeg_posSumL_posSumR {m n p : ℕ} :
    (Graded.congrDeg (M := PosBraid) (Nat.add_assoc m n p)).toMonoidHom.comp
        ((posSumL (m + n) p).comp (posSumR m n)) = (posSumR m (n + p)).comp (posSumL n p) :=
  posPerm_ext fun τ => by
    change Graded.congrDeg _ (posSumL (m + n) p (posSumR m n (posPerm τ)))
      = posSumR m (n + p) (posSumL n p (posPerm τ))
    rw [posSumR_posPerm, posSumL_posPerm, congrDeg_posPerm, posSumL_posPerm, posSumR_posPerm,
      permSum_assoc]

theorem congrDeg_posSumR {m n p : ℕ} :
    (Graded.congrDeg (M := PosBraid) (Nat.add_assoc m n p)).toMonoidHom.comp (posSumR (m + n) p)
      = (posSumR m (n + p)).comp (posSumR n p) :=
  posPerm_ext fun ρ => by
    have h1 : permSum (m + n) p ((1 : Equiv.Perm (Fin (m + n))), ρ)
        = permSum (m + n) p (permSum m n (1, 1), ρ) := by rw [permSum_one_one]
    change Graded.congrDeg _ (posSumR (m + n) p (posPerm ρ))
      = posSumR m (n + p) (posSumR n p (posPerm ρ))
    rw [posSumR_posPerm, congrDeg_posPerm, h1, permSum_assoc, posSumR_posPerm, posSumR_posPerm]

theorem posSum_assoc {m n p : ℕ} (a : PosBraid m) (b : PosBraid n) (c : PosBraid p) :
    Graded.congrDeg (Nat.add_assoc m n p) (posSum (m + n) p (posSum m n (a, b), c))
      = posSum m (n + p) (a, posSum n p (b, c)) := by
  have hL := DFunLike.congr_fun (congrDeg_posSumL_posSumL (m := m) (n := n) (p := p)) a
  have hM := DFunLike.congr_fun (congrDeg_posSumL_posSumR (m := m) (n := n) (p := p)) b
  have hR := DFunLike.congr_fun (congrDeg_posSumR (m := m) (n := n) (p := p)) c
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at hL hM hR
  rw [posSum_apply, posSum_apply, posSum_apply, posSum_apply, map_mul, map_mul, map_mul, map_mul,
    hL, hM, hR, mul_assoc]

theorem posSum_one_right {n : ℕ} (a : PosBraid n) : posSum n 0 (a, 1) = a := by
  rw [posSum_left]
  exact DFunLike.congr_fun (posPerm_ext (φ := posSumL n 0) (ψ := MonoidHom.id (PosBraid n))
    fun σ => by rw [posSumL_posPerm, permSum_zero_right]; rfl) a

theorem posSum_one_left {n : ℕ} (a : PosBraid n) :
    posSum 0 n (1, a) = Graded.congrDeg (Nat.zero_add n).symm a := by
  rw [posSum_right]
  refine DFunLike.congr_fun (posPerm_ext (φ := posSumR 0 n)
    (ψ := (Graded.congrDeg (M := PosBraid) (Nat.zero_add n).symm).toMonoidHom) fun σ => ?_) a
  change posSumR 0 n (posPerm σ) = Graded.congrDeg _ (posPerm σ)
  rw [posSumR_posPerm, congrDeg_posPerm, permSum_zero_left]
  exact congrArg posPerm (Equiv.ext fun _ => Fin.ext rfl)

/-- **The block sum of positive braids** — the tensor `FullPosBraid` carries: strand counts add and
braids juxtapose. -/
def posTensor : Graded.Tensor PosBraid where
  sum {m n} := posSum m n
  sum_assoc := posSum_assoc
  sum_one_left := posSum_one_left
  sum_one_right := posSum_one_right

/-- **`FullPosBraid` is monoidal**, over the addition of strand counts. -/
instance : CategoryTheory.MonoidalCategory FullPosBraid := Graded.Tensor.monoidal posTensor

end CubeChains
