import CubeChains.Machinery.Braid.PosGerm

/-!
# Machinery/Braid/Matsumoto — the germ is the Artin monoid

Peeling one adjacent descent at a time takes `σ` to `1`; which descent is peeled is immaterial in a
monoid where the two Artin relations hold.  Local confluence is the two-descent dichotomy — far
apart, or consecutive — and termination is `permLen`.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

section Recursion

variable {M : Type*} [Monoid M]

/-! ### The descent recursion -/

/-- Peel adjacent descents off the right of `σ` until none is left. -/
noncomputable def matsuLift (g : Fin (n - 1) → M) (σ : Perm (Fin n)) : M :=
  if h : ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) then
    matsuLift g (σ * adjT h.choose) * g h.choose
  else 1
  termination_by permLen σ
  decreasing_by
    have := permLen_mul_adjT_of_descent h.choose_spec
    omega

variable (g : Fin (n - 1) → M)

theorem matsuLift_of_no_descent {σ : Perm (Fin n)}
    (h : ¬ ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i)) : matsuLift g σ = 1 := by
  rw [matsuLift, dif_neg h]

theorem matsuLift_choose {σ : Perm (Fin n)}
    (h : ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i)) :
    matsuLift g σ = matsuLift g (σ * adjT h.choose) * g h.choose := by
  rw [matsuLift, dif_pos h]

@[simp] theorem matsuLift_one : matsuLift g (1 : Perm (Fin n)) = 1 :=
  matsuLift_of_no_descent g fun ⟨i, hi⟩ => by
    simp only [Perm.one_apply] at hi
    rw [Fin.lt_def, adjLo_val, adjHi_val] at hi
    omega

/-- **Uniqueness**: the recursion pins the map down, relations or no relations. -/
theorem eq_matsuLift {f : Perm (Fin n) → M} (h1 : f 1 = 1)
    (hstep : ∀ (σ : Perm (Fin n)) (i : Fin (n - 1)), σ (adjHi i) < σ (adjLo i) →
      f σ = f (σ * adjT i) * g i) (σ : Perm (Fin n)) : f σ = matsuLift g σ := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    by_cases h : ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i)
    · rw [matsuLift_choose g h, hstep σ h.choose h.choose_spec,
        ih _ (by have := permLen_mul_adjT_of_descent h.choose_spec; omega)]
    · rw [eq_one_of_no_adjacent_descent σ (not_exists.mp h), h1, matsuLift_one]

/-- A monoid map transports the recursion. -/
theorem map_matsuLift {N : Type*} [Monoid N] (φ : M →* N) (σ : Perm (Fin n)) :
    φ (matsuLift g σ) = matsuLift (fun i => φ (g i)) σ := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    by_cases h : ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i)
    · rw [matsuLift_choose g h, matsuLift_choose (fun i => φ (g i)) h, map_mul,
        ih _ (by have := permLen_mul_adjT_of_descent h.choose_spec; omega)]
    · rw [matsuLift_of_no_descent g h, matsuLift_of_no_descent _ h, map_one]

/-! ### Local confluence

Two descents `i < k` of `σ` are far apart or consecutive.  Far apart, the two peels meet after one
more step at `σ sᵢ s_k = σ s_k sᵢ`, and the leftover letters commute.  Consecutive, they meet after
two more steps at `σ sᵢ s_k sᵢ = σ s_k sᵢ s_k`, and the leftover letters braid. -/

/-- **Any adjacent descent peels**: the choice `matsuLift` makes is immaterial once `g` is an
Artin family. -/
theorem matsuLift_mul_adjT (hg : IsArtinFamily g)
    (σ : Perm (Fin n)) : ∀ j : Fin (n - 1), σ (adjHi j) < σ (adjLo j) →
      matsuLift g σ = matsuLift g (σ * adjT j) * g j := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    -- the ordered two-descent step; the symmetric one follows by swapping `i` and `k`
    have main : ∀ i k : Fin (n - 1), (i : ℕ) < (k : ℕ) →
        σ (adjHi i) < σ (adjLo i) → σ (adjHi k) < σ (adjLo k) →
        matsuLift g (σ * adjT i) * g i = matsuLift g (σ * adjT k) * g k := by
      intro i k hik hi hk
      have hli : permLen (σ * adjT i) < permLen σ := by
        have := permLen_mul_adjT_of_descent hi; omega
      have hlk : permLen (σ * adjT k) < permLen σ := by
        have := permLen_mul_adjT_of_descent hk; omega
      rcases Nat.lt_or_ge ((i : ℕ) + 1) (k : ℕ) with hfar | hnear
      · -- far apart: the peels commute
        have e1 : adjT i (adjLo k) = adjLo k := adjT_adjLo_of_ne (by omega) (by omega)
        have e2 : adjT i (adjHi k) = adjHi k := adjT_adjHi_of_ne (by omega) (by omega)
        have e3 : adjT k (adjLo i) = adjLo i := adjT_adjLo_of_ne (by omega) (by omega)
        have e4 : adjT k (adjHi i) = adjHi i := adjT_adjHi_of_ne (by omega) (by omega)
        have d1 : (σ * adjT i) (adjHi k) < (σ * adjT i) (adjLo k) := by
          rw [Perm.mul_apply, Perm.mul_apply, e1, e2]; exact hk
        have d2 : (σ * adjT k) (adjHi i) < (σ * adjT k) (adjLo i) := by
          rw [Perm.mul_apply, Perm.mul_apply, e3, e4]; exact hi
        rw [ih _ hli k d1, ih _ hlk i d2, mul_adjT_comm σ hfar]
        simp only [mul_assoc]
        rw [hg.comm i k hfar]
      · -- consecutive: the peels braid
        have hadj : (k : ℕ) = (i : ℕ) + 1 := by omega
        have hmid : adjLo k = adjHi i := adjLo_eq_adjHi hadj
        -- how the two swaps act on the three positions `i, i+1, i+2`
        have a1 : adjT i (adjLo i) = adjHi i := adjT_lo i
        have a3 : adjT i (adjLo k) = adjLo i := by rw [hmid, adjT_hi]
        have a4 : adjT i (adjHi k) = adjHi k := adjT_adjHi_of_ne (by omega) (by omega)
        have b2 : adjT k (adjHi k) = adjLo k := adjT_hi k
        have b3 : adjT k (adjLo i) = adjLo i := adjT_adjLo_of_ne (by omega) (by omega)
        have b4 : adjT k (adjHi i) = adjHi k := by rw [← hmid, adjT_lo]
        have hk' : σ (adjHi k) < σ (adjHi i) := by rw [← hmid]; exact hk
        have hchain : σ (adjHi k) < σ (adjLo i) := lt_trans hk' hi
        have d1 : (σ * adjT i) (adjHi k) < (σ * adjT i) (adjLo k) := by
          simp only [Perm.mul_apply, a3, a4]; exact hchain
        have d2 : (σ * adjT i * adjT k) (adjHi i) < (σ * adjT i * adjT k) (adjLo i) := by
          simp only [Perm.mul_apply, b3, b4, a1, a4]; exact hk'
        have d3 : (σ * adjT k) (adjHi i) < (σ * adjT k) (adjLo i) := by
          simp only [Perm.mul_apply, b3, b4]; exact hchain
        have d4 : (σ * adjT k * adjT i) (adjHi k) < (σ * adjT k * adjT i) (adjLo k) := by
          simp only [Perm.mul_apply, a3, a4, b2, b3]; rw [hmid]; exact hi
        have hl2 : permLen (σ * adjT i * adjT k) < permLen σ := by
          have := permLen_mul_adjT_of_descent d1; omega
        have hl4 : permLen (σ * adjT k * adjT i) < permLen σ := by
          have := permLen_mul_adjT_of_descent d3; omega
        rw [ih _ hli k d1, ih _ hl2 i d2, ih _ hlk i d3, ih _ hl4 k d4, mul_adjT_braid σ hadj]
        have hb := hg.braid i k hadj
        simp only [mul_assoc] at hb ⊢
        rw [hb]
    intro j hj
    have hex : ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) := ⟨j, hj⟩
    rw [matsuLift_choose g hex]
    rcases lt_trichotomy ((hex.choose : ℕ)) ((j : ℕ)) with h | h | h
    · exact main _ _ h hex.choose_spec hj
    · rw [show hex.choose = j from Fin.ext h]
    · exact (main _ _ h hj hex.choose_spec).symm

/-! ### The lift, as a map out of the germ -/

variable (hg : IsArtinFamily g)

include hg

theorem matsuLift_mul_adjT_ascent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjLo i) < σ (adjHi i)) : matsuLift g (σ * adjT i) = matsuLift g σ * g i := by
  rw [matsuLift_mul_adjT g hg _ i (by
    simpa only [Perm.mul_apply, adjT_lo, adjT_hi] using h), mul_adjT_adjT]

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

/-- **The opposite family lifts the inverse permutation** — this is what `IsArtinFamily.op` buys:
the recursion peels descents off the right, so reversing the multiplication reverses the word. -/
theorem matsuLift_op (σ : Perm (Fin n)) :
    matsuLift (fun i => MulOpposite.op (g i)) σ = MulOpposite.op (matsuLift g σ⁻¹) := by
  refine (eq_matsuLift (f := fun τ => MulOpposite.op (matsuLift g τ⁻¹))
    (fun i => MulOpposite.op (g i)) (by simp) (fun τ i hdesc => ?_) σ).symm
  have hinv : (adjT i : Perm (Fin n))⁻¹ = adjT i :=
    inv_eq_of_mul_eq_one_right (adjT_mul_self i)
  have hrev : (τ * adjT i)⁻¹ = adjT i * τ⁻¹ := by rw [mul_inv_rev, hinv]
  have hlen : permLen (adjT i * (adjT i * τ⁻¹))
      = permLen (adjT i) + permLen (adjT i * τ⁻¹) := by
    rw [← mul_assoc, adjT_mul_self, one_mul, permLen_adjT, permLen_inv, ← hrev, permLen_inv,
      permLen_mul_adjT_of_descent hdesc]
    omega
  have hstep : matsuLift g τ⁻¹ = g i * matsuLift g (adjT i * τ⁻¹) := by
    rw [← matsuLift_adjT g hg i, matsuLift_mul g hg _ _ hlen, ← mul_assoc, adjT_mul_self, one_mul]
  simp only [hrev, hstep]
  rfl

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

theorem isArtinFamily_artinPosGen : IsArtinFamily (artinPosGen (n := n)) where
  comm i j h := PresentedMonoid.mk_eq_mk_of_rel (ArtinRel.comm i j h)
  braid i j h := PresentedMonoid.mk_eq_mk_of_rel (ArtinRel.braid i j h)

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

/-- The simples are their own lift. -/
theorem posPerm_eq_matsuLift (σ : Perm (Fin n)) :
    posPerm σ = matsuLift (fun i => posPerm (adjT i)) σ :=
  eq_matsuLift_of_ascent posPerm_one (fun _ _ h => posPerm_mul_adjT h) σ

/-- **The Artin presentation of the positive braid monoid.** -/
noncomputable def posBraid_equiv_artinPos (n : ℕ) : PosBraid n ≃* ArtinPosBraid n :=
  MonoidHom.toMulEquiv (posToArtinPos n) (posOfArtinPos n)
    (posPerm_ext fun σ => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, posToArtinPos_posPerm,
        map_matsuLift, posOfArtinPos_gen]
      exact (posPerm_eq_matsuLift σ).symm)
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
