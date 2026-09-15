import CubeChains.Machinery.Braid.PosGerm
import CubeChains.Machinery.Braid.MatsumotoCat
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Braid/Matsumoto — the germ is the Artin monoid

`Machinery/Braid/MatsumotoCat` extends a labelling of the covers of a lower set of the right weak
order to a functor.  Take the lower set to be all of `Sₙ` and the target the one-object category on
`M`: a climb is a reduced word, `Web.IsArtin` is `IsArtinFamily`, and `matsuLift` is the arrow out
of the identity.  Hence `posBraid_equiv_artinPos` and `garside_equiv_artin`.
-/

namespace CubeChains

open CategoryTheory Equiv

variable {n : ℕ}

section Recursion

variable {M : Type*} [Monoid M]

/-! ### `Sₙ` as a web -/

/-- **All of `Sₙ`**, as a lower set of its own right weak order. -/
def permLower (n : ℕ) : WeakOrder.Lower n (Perm (Fin n)) where
  perm := id
  perm_inj := Function.injective_id
  isLowerSet _ b _ _ := ⟨b, rfl⟩

/-- **A family of generators, as a labelling of the covers**: one object, the generators being
loops, and `ᵐᵒᵖ` because a climb spells its word left to right. -/
def permWeb (g : Fin (n - 1) → M) : Web n (Perm (Fin n)) (SingleObj Mᵐᵒᵖ) where
  toLower := permLower n
  pre :=
    { obj := fun _ => SingleObj.star Mᵐᵒᵖ
      map := fun {_ _} e => MulOpposite.op (g e.idx) }

/-- An arrow of the one-object category, read in `M`.  A plain `unop` would resolve to the
opposite *category*'s, the hom-type's head being `Quiver.Hom`. -/
def homVal {x y : SingleObj Mᵐᵒᵖ} (f : x ⟶ y) : M := MulOpposite.unop (f : Mᵐᵒᵖ)

variable (g : Fin (n - 1) → M)

/-- **The lift of a family**: the arrow the web names from the identity up to `σ`. -/
noncomputable def matsuLift (σ : Perm (Fin n)) : M :=
  homVal ((permWeb g).arrow (w := (1 : Perm (Fin n))) (v := σ) (WeakOrder.one_le σ))

@[simp] theorem matsuLift_one : matsuLift g (1 : Perm (Fin n)) = 1 := by
  unfold matsuLift
  rw [Web.arrow_refl]
  rfl

/-! ### Confluence, from the polygon -/

/-- The walk down the polygon, read upwards: a climb spelling every letter after the first. -/
private theorem exists_walk {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) :
    ∀ t < cox i k, ∃ R : Climb (permLower n).perm (u * altWord i k (t + 1)) (u * altWord i k 1),
      homVal ((permWeb g).eval.map R) = altProd g k i t
  | 0, _ => ⟨.nil, rfl⟩
  | t + 1, ht => by
      obtain ⟨R, hR⟩ := exists_walk hik hi hk t (by omega)
      refine ⟨(Quiver.Path.nil.cons (Ascent.ofPeel (p := (permLower n).perm)
        (descent_altWord hik hi hk (t + 1) ht)
        (by rw [altWord_succ i k (t + 1), ← mul_assoc]; rfl))).comp R, ?_⟩
      refine (congrArg homVal ((permWeb g).eval.map_comp _ R)).trans ?_
      change 1 * g (altIdx i k (t + 1)) * homVal ((permWeb g).eval.map R) = _
      rw [hR, one_mul, altIdx_succ]
      rfl

/-- **The two walks out of a double descent spell the same word** — `Web.IsArtin` for the web of
all of `Sₙ` is exactly the Coxeter relation on `g`. -/
theorem isArtin_permWeb (hg : IsArtinFamily g) : (permWeb g).IsArtin := by
  intro v b b' e e' hbb'
  have leg : ∀ {c b : Perm (Fin n)} {i k : Fin (n - 1)}, (i : ℕ) ≠ (k : ℕ) →
      v (adjHi i) < v (adjLo i) → v (adjHi k) < v (adjLo k) → c = polyFoot v i k →
      b = v * adjT i → ∃ R : Climb (permLower n).perm c b,
        homVal ((permWeb g).eval.map R) * g i = altProd g i k (cox i k) := by
    intro c b i k hik hi hk hc hb
    subst hc hb
    obtain ⟨t, ht⟩ : ∃ t, cox i k = t + 1 := ⟨cox i k - 1, by have := two_le_cox hik; omega⟩
    obtain ⟨R, hR⟩ := exists_walk g hik hi hk t (by omega)
    rw [polyFoot, ht, ← altWord_one i k]
    exact ⟨R, by rw [hR, altProd_succ_right]⟩
  have hik := Web.idx_ne _ e e' hbb'
  have hc := (permWeb g).perm_foot e e' hbb'
  generalize (permWeb g).foot e e' hbb' = c at hc ⊢
  obtain ⟨R, hR⟩ := leg hik e.descent e'.descent hc e.perm_eq'
  obtain ⟨R', hR'⟩ := leg (Ne.symm hik) e'.descent e.descent
    (hc.trans (polyFoot_comm hik _)) e'.perm_eq'
  refine ⟨R, R', MulOpposite.unop_injective (hR.trans ((hg.altProd_cox hik).trans ?_))⟩
  rw [cox_comm]
  exact hR'.symm

/-! ### The lift, as a map out of the germ -/

variable (hg : IsArtinFamily g)

include hg

theorem matsuLift_mul_adjT_ascent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjLo i) < σ (adjHi i)) : matsuLift g (σ * adjT i) = matsuLift g σ * g i := by
  let a : Ascent (permLower n).perm σ (σ * adjT i) := ⟨i, h, rfl⟩
  exact (congrArg homVal ((permWeb g).arrow_comp (isArtin_permWeb g hg)
    (WeakOrder.one_le σ) a.le).symm).trans
    (congrArg (matsuLift g σ * homVal ·) (Web.functor_map_ascent (isArtin_permWeb g hg) a))

@[simp] theorem matsuLift_adjT (i : Fin (n - 1)) : matsuLift g (adjT i) = g i := by
  have h : (1 : Perm (Fin n)) (adjLo i) < (1 : Perm (Fin n)) (adjHi i) := adjLo_lt_adjHi i
  simpa using matsuLift_mul_adjT_ascent g hg h

/-- **Matsumoto's theorem for `Sₙ`**: an Artin family extends over the whole germ, compatibly with
every length-additive product. -/
theorem matsuLift_mul (σ τ : Perm (Fin n))
    (h : permLen (σ * τ) = permLen σ + permLen τ) :
    matsuLift g σ * matsuLift g τ = matsuLift g (σ * τ) :=
  germ_of_atom (matsuLift_one g)
    (fun β i hβ => by
      rw [matsuLift_adjT g hg, matsuLift_mul_adjT_ascent g hg (ascent_of_permLen_mul_adjT hβ)])
    σ τ h

/-- **The universal property of the positive braid monoid**: it is the Artin monoid. -/
noncomputable def PosBraid.liftArtin : PosBraid n →* M :=
  PosBraid.lift (matsuLift g) (matsuLift_one g) (matsuLift_mul g hg)

@[simp] theorem PosBraid.liftArtin_posPerm (σ : Perm (Fin n)) :
    PosBraid.liftArtin g hg (posPerm σ) = matsuLift g σ := rfl

omit hg

/-- **…and the Artin lift is the only hom with the given atoms.** -/
theorem PosBraid.eq_liftArtin {g : Fin (n - 1) → M} (hg : IsArtinFamily g) (φ : PosBraid n →* M)
    (h : ∀ i : Fin (n - 1), φ (posPerm (adjT i)) = g i) : φ = PosBraid.liftArtin g hg :=
  posBraid_hom_ext fun i => by
    rw [h i, PosBraid.liftArtin_posPerm, matsuLift_adjT g hg i]

end Recursion

/-! ### The Artin monoid -/

/-- **The Artin braid monoid** on `n` strands. -/
def ArtinPosBraid (n : ℕ) : Type := PresentedMonoid (ArtinRel n)

instance : Monoid (ArtinPosBraid n) :=
  inferInstanceAs (Monoid (PresentedMonoid (ArtinRel n)))

/-- The `i`-th Artin generator. -/
def artinPosGen (i : Fin (n - 1)) : ArtinPosBraid n := PresentedMonoid.of _ i

/-- Evaluating a word at the generators is taking its class. -/
theorem lift_artinPosGen (w : FreeMonoid (Fin (n - 1))) :
    FreeMonoid.lift artinPosGen w = PresentedMonoid.mk (ArtinRel n) w :=
  DFunLike.congr_fun (FreeMonoid.hom_eq (f := FreeMonoid.lift artinPosGen)
    (g := PresentedMonoid.mk (ArtinRel n)) fun _ => rfl) w

theorem isArtinFamily_artinPosGen : IsArtinFamily (artinPosGen (n := n)) :=
  isArtinFamily_iff.mpr fun {x y} h => by
    rw [lift_artinPosGen, lift_artinPosGen]
    exact PresentedMonoid.mk_eq_mk_of_rel h

/-- **The universal property**: an Artin family extends. -/
def ArtinPosBraid.lift {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (hg : IsArtinFamily g) :
    ArtinPosBraid n →* M :=
  PresentedMonoid.lift g fun _ _ h => isArtinFamily_iff.mp hg h

@[simp] theorem ArtinPosBraid.lift_gen {M : Type*} [Monoid M] {g : Fin (n - 1) → M}
    {hg : IsArtinFamily g} (i : Fin (n - 1)) : ArtinPosBraid.lift g hg (artinPosGen i) = g i := rfl

theorem artinPosGen_ext {M : Type*} [Monoid M] {φ ψ : ArtinPosBraid n →* M}
    (h : ∀ i : Fin (n - 1), φ (artinPosGen i) = ψ (artinPosGen i)) : φ = ψ :=
  PresentedMonoid.ext _ h

/-! ### The positive braid monoid is the Artin monoid -/

/-- **The simples of the adjacent transpositions are an Artin family in the positive germ.** -/
theorem isArtinFamily_posPerm_adjT : IsArtinFamily fun i : Fin (n - 1) => posPerm (adjT i) :=
  isArtinFamily_of_atom fun _ _ ha => posPerm_mul_adjT ha

/-- **The easy direction**: each Artin generator is the simple of an adjacent transposition. -/
def posOfArtinPos (n : ℕ) : ArtinPosBraid n →* PosBraid n :=
  ArtinPosBraid.lift _ isArtinFamily_posPerm_adjT

@[simp] theorem posOfArtinPos_gen (i : Fin (n - 1)) :
    posOfArtinPos n (artinPosGen i) = posPerm (adjT i) := rfl

/-- **The Matsumoto section**: the positive lift `σ ↦ σ̂`. -/
noncomputable def posToArtinPos (n : ℕ) : PosBraid n →* ArtinPosBraid n :=
  PosBraid.liftArtin artinPosGen isArtinFamily_artinPosGen

@[simp] theorem posToArtinPos_posPerm (σ : Perm (Fin n)) :
    posToArtinPos n (posPerm σ) = matsuLift artinPosGen σ := rfl

/-- **The Artin presentation of the positive braid monoid.** -/
noncomputable def posBraid_equiv_artinPos (n : ℕ) : PosBraid n ≃* ArtinPosBraid n :=
  MonoidHom.toMulEquiv (posToArtinPos n) (posOfArtinPos n)
    (posBraid_hom_ext fun i => by
      simp [matsuLift_adjT artinPosGen isArtinFamily_artinPosGen])
    (artinPosGen_ext fun i => by
      simp [matsuLift_adjT artinPosGen isArtinFamily_artinPosGen])

@[simp] theorem posBraid_equiv_artinPos_adjT (i : Fin (n - 1)) :
    posBraid_equiv_artinPos n (posPerm (adjT i)) = artinPosGen i :=
  matsuLift_adjT artinPosGen isArtinFamily_artinPosGen i

/-- **Every atom factorisation of a simple has `permLen` letters** — no minimising. -/
theorem length_of_word_eq_posPerm {σ : Perm (Fin n)} {w : FreeMonoid (Fin (n - 1))}
    (hw : FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ) :
    w.length = permLen σ := by
  have h : ∀ w : FreeMonoid (Fin (n - 1)), posLen n (FreeMonoid.lift (fun i => posPerm (adjT i)) w)
      = Multiplicative.ofAdd w.length := fun w => by
    induction w with
    | one => rfl
    | of a => rw [FreeMonoid.lift_eval_of, posLen_posPerm, permLen_adjT]; rfl
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy, FreeMonoid.length_mul, ofAdd_add]
  exact Multiplicative.ofAdd.injective ((h w).symm.trans (by rw [hw, posLen_posPerm]))

/-- …and there is one, `matsuLift`'s own spelling. -/
theorem exists_word_eq_posPerm (σ : Perm (Fin n)) :
    ∃ w : FreeMonoid (Fin (n - 1)),
      FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ ∧ w.length = permLen σ := by
  obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk (posToArtinPos n (posPerm σ))
  have h : FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ :=
    (congrArg (posOfArtinPos n) hw).trans ((posBraid_equiv_artinPos n).symm_apply_apply (posPerm σ))
  exact ⟨w, h, length_of_word_eq_posPerm h⟩

/-! ### The Artin presentation of the braid group -/

/-- **The simples of the adjacent transpositions are an Artin family.** -/
theorem isArtinFamily_ofPerm_adjT : IsArtinFamily fun i : Fin (n - 1) => ofPerm (adjT i) :=
  isArtinFamily_of_atom fun _ _ ha => ofPerm_mul_adjT ha

/-- **The easy direction**: the Artin group maps to the germ, a generator to its simple. -/
def garsideOfArtin (n : ℕ) : ArtinBraid n →* GarsideBraid n :=
  ArtinBraid.lift _ isArtinFamily_ofPerm_adjT

@[simp] theorem garsideOfArtin_gen (i : Fin (n - 1)) :
    garsideOfArtin n (artinGen i) = ofPerm (adjT i) :=
  ArtinBraid.lift_gen i

/-- The positive lift, as a section of `garsideOfArtin`. -/
noncomputable def garsideToArtin (n : ℕ) : GarsideBraid n →* ArtinBraid n :=
  Braid.lift (matsuLift artinGen) (matsuLift_mul artinGen isArtinFamily_artinGen)

@[simp] theorem garsideToArtin_ofPerm (σ : Perm (Fin n)) :
    garsideToArtin n (ofPerm σ) = matsuLift artinGen σ :=
  Braid.lift_ofPerm σ

/-- **The Garside germ presentation is the Artin braid group.** -/
noncomputable def garside_equiv_artin (n : ℕ) : GarsideBraid n ≃* ArtinBraid n :=
  MonoidHom.toMulEquiv (garsideToArtin n) (garsideOfArtin n)
    (PresentedGroup.ext (map_eq_of_atom ofPerm_one (fun _ _ => ofPerm_mul_adjT) fun i => by
      simp [matsuLift_adjT artinGen isArtinFamily_artinGen]))
    (PresentedGroup.ext fun i => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
        show (PresentedGroup.of i : ArtinBraid n) = artinGen i from rfl, garsideOfArtin_gen,
        garsideToArtin_ofPerm]
      exact matsuLift_adjT artinGen isArtinFamily_artinGen i)

@[simp] theorem garside_equiv_artin_adjT (i : Fin (n - 1)) :
    garside_equiv_artin n (ofPerm (adjT i)) = artinGen i := by
  change garsideToArtin n (ofPerm (adjT i)) = _
  rw [garsideToArtin_ofPerm, matsuLift_adjT artinGen isArtinFamily_artinGen]

end CubeChains
