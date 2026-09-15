import CubeChains.Machinery.Braid.PosGerm
import CubeChains.Machinery.Braid.MatsumotoCat
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Braid/Matsumoto — the germ is the Artin monoid

`Machinery/Braid/MatsumotoCat` extends a labelling of the covers of a lower set of the right weak
order to a functor on the poset.  Take the lower set to be all of `Sₙ` and the target the one-object
category on `M`: a climb is a reduced word, and `matsuLift` is the arrow out of the identity.  The
confluence is not repeated here — `Web.IsArtin` asks only that the two walks out of a double descent
spell the same word, which is `IsArtinFamily.altProd_cox`.
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
  isLowerSet := by
    have h : (Set.range fun v : Perm (Fin n) => WeakOrder.of (id v)) = Set.univ :=
      Set.eq_univ_of_forall fun x => ⟨WeakOrder.perm x, rfl⟩
    rw [h]
    exact isLowerSet_univ

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

/-- Composition is multiplication, left to right. -/
theorem homVal_comp {x y z : SingleObj Mᵐᵒᵖ} (f : x ⟶ y) (h : y ⟶ z) :
    homVal (f ≫ h) = homVal f * homVal h := rfl

omit [Monoid M] in
theorem homVal_injective {x y : SingleObj Mᵐᵒᵖ} {f h : x ⟶ y}
    (hfh : homVal f = homVal h) : f = h := MulOpposite.unop_injective hfh

variable (g : Fin (n - 1) → M)

/-- **The lift of a family**: the arrow the web names from the identity up to `σ`.  Any climb
spells it — `eq_matsuLift` is that, read as the peel recursion. -/
noncomputable def matsuLift (σ : Perm (Fin n)) : M :=
  homVal ((permWeb g).arrow (w := (1 : Perm (Fin n))) (v := σ) (WeakOrder.one_le σ))

@[simp] theorem matsuLift_one : matsuLift g (1 : Perm (Fin n)) = 1 := by
  unfold matsuLift
  rw [Web.arrow_refl]
  rfl

/-- **A climb spells the peel recursion**, whatever climb it is — so a map obeying the recursion is
the lift along every climb at once. -/
theorem eq_eval_of_step {f : Perm (Fin n) → M} (h1 : f 1 = 1)
    (hstep : ∀ (σ : Perm (Fin n)) (i : Fin (n - 1)), σ (adjHi i) < σ (adjLo i) →
      f σ = f (σ * adjT i) * g i) :
    ∀ {v : Perm (Fin n)} (R : Climb (permLower n).perm 1 v),
      f v = homVal ((permWeb g).eval.map R)
  | _, .nil => h1
  | _, .cons R e =>
      ((hstep _ e.idx e.descent).trans
        (congrArg (fun x => f x * g e.idx) e.perm_eq'.symm)).trans
        (congrArg (fun x => x * g e.idx) (eq_eval_of_step h1 hstep R))

/-- **Uniqueness**: the recursion pins the map down, relations or no relations. -/
theorem eq_matsuLift {f : Perm (Fin n) → M} (h1 : f 1 = 1)
    (hstep : ∀ (σ : Perm (Fin n)) (i : Fin (n - 1)), σ (adjHi i) < σ (adjLo i) →
      f σ = f (σ * adjT i) * g i) (σ : Perm (Fin n)) : f σ = matsuLift g σ :=
  eq_eval_of_step g h1 hstep _

/-- A monoid map transports the value of a climb… -/
theorem map_eval {N : Type*} [Monoid N] (φ : M →* N) :
    ∀ {w v : Perm (Fin n)} (R : Climb (permLower n).perm w v),
      φ (homVal ((permWeb g).eval.map R)) = homVal ((permWeb (fun i => φ (g i))).eval.map R)
  | _, _, .nil => map_one φ
  | _, _, .cons R e =>
      (map_mul φ _ _).trans (congrArg (fun x => x * φ (g e.idx)) (map_eval φ R))

/-- …hence the lift. -/
theorem map_matsuLift {N : Type*} [Monoid N] (φ : M →* N) (σ : Perm (Fin n)) :
    φ (matsuLift g σ) = matsuLift (fun i => φ (g i)) σ :=
  map_eval g φ _

/-! ### Confluence, from the polygon

The only hypothesis is `IsArtinFamily`, and it enters exactly once: as the Coxeter relation on the
two alternating words the polygon's legs spell. -/

/-- The polygon's leg out of the foot, and the word it spells. -/
private theorem exists_leg {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) {s : ℕ}
    (hs : cox i k = 1 + s) {c b : Perm (Fin n)} (hc : c = u * altWord i k (cox i k))
    (hb : b = u * adjT i) :
    ∃ R : Climb (permLower n).perm c b, homVal ((permWeb g).eval.map R) = altProd g k i s := by
  subst hc; subst hb
  have key : ∀ t : ℕ, 1 + t ≤ cox i k →
      ∃ R : Climb (permLower n).perm (u * altWord i k (1 + t)) (u * altWord i k 1),
        homVal ((permWeb g).eval.map R) = altProd g k i t := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨Quiver.Path.nil, rfl⟩
    | succ t ih =>
        intro ht
        obtain ⟨R, hR⟩ := ih (by omega)
        refine ⟨Quiver.Path.comp (Quiver.Path.nil.cons (Ascent.ofPeel
            (p := (permLower n).perm) (k := altIdx i k (1 + t))
            (descent_altWord hik hi hk (1 + t) (by omega))
            (show u * altWord i k (1 + t + 1)
                = u * altWord i k (1 + t) * adjT (altIdx i k (1 + t)) from by
              rw [altWord_succ, mul_assoc]))) R, ?_⟩
        refine Eq.trans (congrArg homVal ((permWeb g).eval.map_comp _ R)) ?_
        rw [homVal_comp, hR]
        change (1 : M) * g (altIdx i k (1 + t)) * altProd g k i t = _
        rw [one_mul, Nat.add_comm 1 t, altIdx_succ]
        rfl
  obtain ⟨R, hR⟩ := key s (by omega)
  rw [hs, ← altWord_one i k]
  exact ⟨R, hR⟩

/-- **The two walks out of a double descent spell the same word** — `Web.IsArtin` for the web of
all of `Sₙ` is exactly the Coxeter relation on `g`. -/
theorem isArtin_permWeb (hg : IsArtinFamily g) : (permWeb g).IsArtin := by
  refine Web.isArtin_of_climbs _ ?_
  intro v b b' e e' hbb' c hc
  have hik : (e.idx : ℕ) ≠ (e'.idx : ℕ) := (e.idx_ne_iff (permLower n).perm_inj e').mpr hbb'
  obtain ⟨s, hs⟩ : ∃ s, cox e.idx e'.idx = 1 + s :=
    ⟨cox e.idx e'.idx - 1, by have := two_le_cox hik; omega⟩
  have hs' : cox e'.idx e.idx = 1 + s := by rw [← cox_comm e.idx e'.idx]; exact hs
  obtain ⟨R, hR⟩ := exists_leg g hik e.descent e'.descent hs hc e.perm_eq'
  obtain ⟨R', hR'⟩ := exists_leg g (Ne.symm hik) e'.descent e.descent hs'
    (hc.trans (polyFoot_comm hik v)) e'.perm_eq'
  refine ⟨R, R', homVal_injective ?_⟩
  change homVal ((permWeb g).eval.map R) * g e.idx = homVal ((permWeb g).eval.map R') * g e'.idx
  rw [hR, hR', altProd_succ_right, altProd_succ_right,
    show s + 1 = cox e.idx e'.idx from by omega]
  exact hg.altProd_cox hik

/-! ### The lift, as a map out of the germ -/

variable (hg : IsArtinFamily g)

include hg

theorem matsuLift_mul_adjT_ascent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjLo i) < σ (adjHi i)) : matsuLift g (σ * adjT i) = matsuLift g σ * g i := by
  obtain ⟨hasc, hidx⟩ : ∃ a : Ascent (permLower n).perm σ (σ * adjT i), a.idx = i :=
    ⟨⟨i, h, rfl⟩, rfl⟩
  have h1 : (permWeb g).arrow hasc.le = (permWeb g).pre.map hasc :=
    (Web.eval_eq_arrow (isArtin_permWeb g hg) (Quiver.Path.nil.cons hasc)).symm.trans
      (Category.id_comp _)
  have h2 : (permWeb g).arrow (w := (1 : Perm (Fin n))) (v := σ * adjT i)
        (WeakOrder.one_le (σ * adjT i))
      = (permWeb g).arrow (w := (1 : Perm (Fin n))) (v := σ) (WeakOrder.one_le σ)
        ≫ (permWeb g).arrow hasc.le :=
    (Web.arrow_comp (isArtin_permWeb g hg) (WeakOrder.one_le σ) hasc.le).symm
  unfold matsuLift
  rw [h2, homVal_comp, h1,
    show homVal ((permWeb g).pre.map hasc) = g hasc.idx from rfl, hidx]

@[simp] theorem matsuLift_adjT (i : Fin (n - 1)) : matsuLift g (adjT i) = g i := by
  have h : (1 : Perm (Fin n)) (adjLo i) < (1 : Perm (Fin n)) (adjHi i) := by
    simp only [Perm.one_apply, Fin.lt_def, adjLo_val, adjHi_val]; omega
  simpa using matsuLift_mul_adjT_ascent g hg h

/-- **Matsumoto's theorem for `Sₙ`**: the two Artin relations extend a family over the whole germ,
compatibly with every length-additive product. -/
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

/-- A germ generator is its own lift: `posPerm` and `ofPerm` are the `matsuLift` of their
restrictions to adjacent transpositions. -/
theorem eq_matsuLift_of_ascent {G : Perm (Fin n) → M} (hone : G 1 = 1)
    (hasc : ∀ (β : Perm (Fin n)) (i : Fin (n - 1)), β (adjLo i) < β (adjHi i) →
      G β * G (adjT i) = G (β * adjT i)) (σ : Perm (Fin n)) :
    G σ = matsuLift (fun i => G (adjT i)) σ :=
  eq_matsuLift _ hone (fun τ i hd => by
    have h := hasc (τ * adjT i) i (adjT_ascent_of_descent hd)
    rw [mul_adjT_adjT] at h
    exact h.symm) σ

/-- **A hom out of the germ is `matsuLift` of its atoms** — the simples multiply across an ascent,
which is the recursion's step. -/
theorem posPerm_eq_matsuLift (φ : PosBraid n →* M) (σ : Perm (Fin n)) :
    φ (posPerm σ) = matsuLift (fun i => φ (posPerm (adjT i))) σ :=
  eq_matsuLift_of_ascent (G := fun τ => φ (posPerm τ))
    (show φ (posPerm 1) = 1 by rw [posPerm_one, map_one])
    (fun _ _ h => show φ _ * φ _ = φ _ by rw [← map_mul, posPerm_mul_adjT h]) σ

/-- **A hom out of the germ is its atoms.** -/
theorem posBraid_hom_ext {φ ψ : PosBraid n →* M}
    (h : ∀ i : Fin (n - 1), φ (posPerm (adjT i)) = ψ (posPerm (adjT i))) : φ = ψ :=
  posPerm_ext fun σ => by
    rw [posPerm_eq_matsuLift φ, posPerm_eq_matsuLift ψ, funext h]

/-- **…so the Artin lift is the only hom with the given atoms.** -/
theorem PosBraid.eq_liftArtin {g : Fin (n - 1) → M} (hg : IsArtinFamily g) (φ : PosBraid n →* M)
    (h : ∀ i : Fin (n - 1), φ (posPerm (adjT i)) = g i) : φ = PosBraid.liftArtin g hg :=
  posBraid_hom_ext fun i => by
    rw [h i, PosBraid.liftArtin_posPerm, matsuLift_adjT g hg i]

end Recursion

/-! ### The Artin monoid

`ArtinRel` presents the group in `Machinery/Braid/Artin`; the germ is also a monoid, and the monoid
presentation does not follow from the group one without Garside's embedding theorem. -/

/-- **The Artin braid monoid** on `n` strands. -/
def ArtinPosBraid (n : ℕ) : Type := PresentedMonoid (ArtinRel n)

instance : Monoid (ArtinPosBraid n) :=
  inferInstanceAs (Monoid (PresentedMonoid (ArtinRel n)))

/-- The `i`-th Artin generator. -/
def artinPosGen (i : Fin (n - 1)) : ArtinPosBraid n := PresentedMonoid.of _ i

theorem isArtinFamily_artinPosGen : IsArtinFamily (artinPosGen (n := n)) :=
  isArtinFamily_of_comm_braid
    (fun i j h => PresentedMonoid.mk_eq_mk_of_rel (ArtinRel.comm i j h))
    (fun i j h => PresentedMonoid.mk_eq_mk_of_rel (ArtinRel.braid i j h))

/-- **The universal property**: an Artin family extends. -/
def ArtinPosBraid.lift {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (hg : IsArtinFamily g) :
    ArtinPosBraid n →* M :=
  PresentedMonoid.lift g fun _ _ h => hg.lift_eq h

@[simp] theorem ArtinPosBraid.lift_gen {M : Type*} [Monoid M] {g : Fin (n - 1) → M}
    {hg : IsArtinFamily g} (i : Fin (n - 1)) : ArtinPosBraid.lift g hg (artinPosGen i) = g i := rfl

theorem artinPosGen_ext {M : Type*} [Monoid M] {φ ψ : ArtinPosBraid n →* M}
    (h : ∀ i : Fin (n - 1), φ (artinPosGen i) = ψ (artinPosGen i)) : φ = ψ :=
  PresentedMonoid.ext _ h

/-! ### The positive braid monoid is the Artin monoid -/

/-- **The easy direction**: each Artin generator is the simple of an adjacent transposition. -/
def posOfArtinPos (n : ℕ) : ArtinPosBraid n →* PosBraid n :=
  ArtinPosBraid.lift _ isArtinFamily_posPerm_adjT

@[simp] theorem posOfArtinPos_gen (i : Fin (n - 1)) :
    posOfArtinPos n (artinPosGen i) = posPerm (adjT i) := rfl

/-- **The Matsumoto section**: the positive lift `σ ↦ σ̂`, well defined because the two Artin
relations resolve every ambiguity in the descent recursion. -/
noncomputable def posToArtinPos (n : ℕ) : PosBraid n →* ArtinPosBraid n :=
  PosBraid.liftArtin artinPosGen isArtinFamily_artinPosGen

@[simp] theorem posToArtinPos_posPerm (σ : Perm (Fin n)) :
    posToArtinPos n (posPerm σ) = matsuLift artinPosGen σ := rfl

/-- **The Artin presentation of the positive braid monoid.** -/
noncomputable def posBraid_equiv_artinPos (n : ℕ) : PosBraid n ≃* ArtinPosBraid n :=
  MonoidHom.toMulEquiv (posToArtinPos n) (posOfArtinPos n)
    (posPerm_ext fun σ => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, posToArtinPos_posPerm,
        map_matsuLift, posOfArtinPos_gen]
      exact (posPerm_eq_matsuLift (MonoidHom.id (PosBraid n)) σ).symm)
    (artinPosGen_ext fun i => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, posOfArtinPos_gen,
        posToArtinPos_posPerm]
      exact matsuLift_adjT artinPosGen isArtinFamily_artinPosGen i)

@[simp] theorem posBraid_equiv_artinPos_adjT (i : Fin (n - 1)) :
    posBraid_equiv_artinPos n (posPerm (adjT i)) = artinPosGen i :=
  matsuLift_adjT artinPosGen isArtinFamily_artinPosGen i

/-! ### Word length is the Coxeter length

Both Artin relations are length-homogeneous (`isArtinFamily_const`), so the letter count descends
to the monoid; an atom crosses one pair, so it *is* `permLen`.  Since `permLen` is additive on the
germ relation by definition, every spelling of a simple has the same length — the length is not a
minimum over factorisations, it is a value. -/

/-- Evaluating a word in the presented monoid is evaluating it in the free one. -/
theorem ArtinPosBraid.lift_mk {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (hg : IsArtinFamily g)
    (w : FreeMonoid (Fin (n - 1))) :
    ArtinPosBraid.lift g hg (PresentedMonoid.mk (ArtinRel n) w) = FreeMonoid.lift g w := rfl

/-- The constant-one lift counts letters. -/
theorem freeMonoid_lift_const_one {α : Type*} (w : FreeMonoid α) :
    FreeMonoid.lift (fun _ : α => Multiplicative.ofAdd 1) w = Multiplicative.ofAdd w.length := by
  induction w with
  | one => rfl
  | of a => rfl
  | mul x y hx hy => rw [map_mul, hx, hy, FreeMonoid.length_mul, ofAdd_add]

/-- **The word length of an Artin braid.** -/
def artinLen (n : ℕ) : ArtinPosBraid n →* Multiplicative ℕ :=
  ArtinPosBraid.lift _ (isArtinFamily_const (Multiplicative.ofAdd 1))

@[simp] theorem artinLen_gen (i : Fin (n - 1)) :
    artinLen n (artinPosGen i) = Multiplicative.ofAdd 1 := rfl

/-- **Every spelling of `β` has the same number of letters.** -/
@[simp] theorem artinLen_mk (w : FreeMonoid (Fin (n - 1))) :
    artinLen n (PresentedMonoid.mk (ArtinRel n) w) = Multiplicative.ofAdd w.length :=
  (ArtinPosBraid.lift_mk _ (isArtinFamily_const _) w).trans (freeMonoid_lift_const_one w)

/-- **Word length is the germ length**: an atom crosses exactly one pair. -/
theorem artinLen_eq (n : ℕ) : artinLen n = (posLen n).comp (posOfArtinPos n) :=
  artinPosGen_ext fun i => by
    rw [artinLen_gen, MonoidHom.comp_apply, posOfArtinPos_gen, posLen_posPerm, permLen_adjT]

/-- **Every atom factorisation of a simple has `permLen` letters** — no minimising. -/
theorem length_of_word_eq_posPerm {σ : Perm (Fin n)} {w : FreeMonoid (Fin (n - 1))}
    (hw : FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ) :
    w.length = permLen σ := by
  have h : posOfArtinPos n (PresentedMonoid.mk (ArtinRel n) w) = posPerm σ :=
    (ArtinPosBraid.lift_mk _ isArtinFamily_posPerm_adjT w).trans hw
  have hlen := congrArg (posLen n) h
  rw [← MonoidHom.comp_apply, ← artinLen_eq, artinLen_mk, posLen_posPerm] at hlen
  exact Multiplicative.ofAdd.injective hlen

/-- …and there is one, `matsuLift`'s own spelling. -/
theorem exists_word_eq_posPerm (σ : Perm (Fin n)) :
    ∃ w : FreeMonoid (Fin (n - 1)),
      FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ ∧ w.length = permLen σ := by
  obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk (posToArtinPos n (posPerm σ))
  have h : FreeMonoid.lift (fun i => posPerm (adjT i)) w = posPerm σ :=
    (ArtinPosBraid.lift_mk _ isArtinFamily_posPerm_adjT w).symm.trans
      (by rw [hw]; exact (posBraid_equiv_artinPos n).symm_apply_apply (posPerm σ))
  exact ⟨w, h, length_of_word_eq_posPerm h⟩

/-! ### The Artin presentation of the braid group -/

/-- The simples are their own lift, in the group. -/
theorem ofPerm_eq_matsuLift (σ : Perm (Fin n)) :
    ofPerm σ = matsuLift (fun i => ofPerm (adjT i)) σ :=
  eq_matsuLift_of_ascent ofPerm_one (fun _ _ h => ofPerm_mul_adjT h) σ

/-- The positive lift, as a section of `garsideOfArtin`. -/
noncomputable def garsideToArtin (n : ℕ) : GarsideBraid n →* ArtinBraid n :=
  Braid.lift (matsuLift artinGen) (matsuLift_mul artinGen isArtinFamily_artinGen)

@[simp] theorem garsideToArtin_ofPerm (σ : Perm (Fin n)) :
    garsideToArtin n (ofPerm σ) = matsuLift artinGen σ :=
  Braid.lift_ofPerm σ

/-- **The Garside germ presentation is the Artin braid group.** -/
noncomputable def garside_equiv_artin (n : ℕ) : GarsideBraid n ≃* ArtinBraid n :=
  MonoidHom.toMulEquiv (garsideToArtin n) (garsideOfArtin n)
    (PresentedGroup.ext fun σ => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply,
        show (PresentedGroup.of σ : GarsideBraid n) = ofPerm σ from rfl, garsideToArtin_ofPerm,
        map_matsuLift, garsideOfArtin_gen]
      exact (ofPerm_eq_matsuLift σ).symm)
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
