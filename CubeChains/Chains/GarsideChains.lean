import CubeChains.Chains.ChainLocMonoid
import CubeChains.Foundations.GarsidePresentation

/-!
# Chains/GarsideChains — the strand component, presented by its interval

For the bead merges the coarsest chain is wide-terminal (`topWideTerminal`) and the run of edges is
wide-initial (`onesWideInitial`), so `Foundations/GarsidePresentation` presents the localized
component by the interval `1ⁿ ⟶ [n]`: generators the chain morphisms, relations their
factorisations through the category.

That presentation *is* the Garside germ one.  The interval is `Sₙ` (`simpleEquivPerm`), and a
factorisation of simples is exactly a length-additive product of permutations —
`permLen_crossPermN_comp` forwards, `exists_atom_pairN` backwards.
-/

open CategoryTheory CubeChains BPSet Equiv

namespace ChainCat

variable {n : ℕ}

/-! ### The permutation of a morphism of the component

`crossPermAt` with the strand count supplied by the component itself — everything below is that
lemma, with `A.property` filled in. -/

/-- The crossing permutation of a morphism of `ChStrands Zbp n`, read on `Fin n`. -/
def crossPermN {A B : ChStrands Zbp n} (f : A ⟶ B) : Perm (Fin n) := crossPermAt A.property f.hom

/-- **The cocycle law in the component.** -/
theorem crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    crossPermN (f ≫ g) = crossPermN g * crossPermN f :=
  crossPermAt_comp A.property B.property f.hom g.hom

/-- **Length-additivity in the component** — a crossing made is never undone. -/
theorem permLen_crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    permLen (crossPermN g * crossPermN f) = permLen (crossPermN g) + permLen (crossPermN f) :=
  permLen_crossPermAt_comp A.property B.property f.hom g.hom

/-- **Two arrows of the component with the same crossing permutation agree** —
`crossPermAt_injective`, read at the component's strand count. -/
theorem hom_ext_of_crossPermN {A B : ChStrands Zbp n} {f g : A ⟶ B}
    (h : crossPermN f = crossPermN g) : f = g :=
  ObjectProperty.hom_ext _ (crossPermAt_injective A.property h)

/-- **The merges are exactly the arrows that cross nothing.** -/
theorem wStrands_iff_crossPermN {A B : ChStrands Zbp n} (f : A ⟶ B) :
    WStrands Zbp n f ↔ crossPermN f = 1 :=
  (wStrands_iff f).trans ((W_iff_crossPerm_eq_one f.hom).trans crossPermAt_eq_one_iff.symm)

theorem crossPermN_eq_one_of_WStrands {A B : ChStrands Zbp n} {f : A ⟶ B} (h : WStrands Zbp n f) :
    crossPermN f = 1 := (wStrands_iff_crossPermN f).mp h

/-- **The merges are the arrows of length zero.**  `codim` counts the junctions a refinement
removes and `permLen ∘ crossPermN` counts the crossings it makes; a merge has codimension without
crossing, which is exactly what the localization inverts. -/
theorem wStrands_iff_permLen {A B : ChStrands Zbp n} (f : A ⟶ B) :
    WStrands Zbp n f ↔ permLen (crossPermN f) = 0 :=
  (wStrands_iff_crossPermN f).trans
    ⟨fun h => by rw [h, permLen_one], eq_one_of_permLen_eq_zero _⟩

/-! ### The two ends of the interval

The run of edges receives no constraint from its beads and the coarsest chain imposes none, so the
merges make the first initial (`onesWideInitial`) and the second terminal (`topWideTerminal`). -/

/-- The run of `n` edges — the source every simple is read from. -/
def onesObj (n : ℕ) : ChStrands Zbp n := ⟨zObj (𝟙^n), dimSum_replicate n⟩

/-- **A merge out of the run reaches every chain of the component.** -/
theorem exists_WStrands_from_ones (A : ChStrands Zbp n) :
    ∃ u : onesObj n ⟶ A, WStrands Zbp n u := by
  obtain ⟨a, ha⟩ := A
  obtain ⟨d, map⟩ := a
  obtain rfl : map = (zObj d).map := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := exists_W_from_ones d ha
  exact ⟨ObjectProperty.homMk u, hu⟩

/-- **The run of edges is wide-initial**: a merge out of it reaches every chain of the
component. -/
noncomputable def onesWideInitial (n : ℕ) : IsWideInitial (WStrands Zbp n) (onesObj n) :=
  wideInitialOfExistsMerge _ exists_WStrands_from_ones

/-! ### The interval is `Sₙ` -/

/-- `arrowOnes`, in the component: the simple realising a permutation. -/
noncomputable def onesToTop (n : ℕ) (σ : Perm (Fin n)) : onesObj n ⟶ topObj n :=
  ObjectProperty.homMk (arrowOnes n σ)

@[simp] theorem crossPermN_onesToTop (n : ℕ) (σ : Perm (Fin n)) :
    crossPermN (onesToTop n σ) = σ := crossPermAt_arrowOnes n σ

@[simp] theorem onesToTop_crossPermN (h : onesObj n ⟶ topObj n) :
    onesToTop n (crossPermN h) = h := hom_ext_of_crossPermN (crossPermN_onesToTop n (crossPermN h))

/-- **A simple is its crossing permutation**: `arrowOnes` realises every permutation, and
`hom_ext_of_crossPermN` says nothing else does. -/
noncomputable def simpleEquivPerm (n : ℕ) : (onesObj n ⟶ topObj n) ≃ Perm (Fin n) where
  toFun := crossPermN
  invFun := onesToTop n
  left_inv := onesToTop_crossPermN
  right_inv := crossPermN_onesToTop n

/-- **The atom pair of `Chains/AtomPair`, in the component.**  An index of `Fin (n-1)` forces
`n` positive, where `topDims n` is the one-bead chain `atomComp` already lands in. -/
theorem exists_atom_pairN (β : Perm (Fin n)) (i : Fin (n - 1))
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ (M : ChStrands Zbp n) (F : onesObj n ⟶ M) (G : M ⟶ topObj n),
      crossPermN F = adjT i ∧ crossPermN G = β := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  obtain ⟨f, g, hf, hg, -⟩ := exists_atom_pair i hβ
  exact ⟨⟨zObj (atomComp (k + 1) i), dimSum_atomComp (k + 1) i⟩,
    ObjectProperty.homMk f, ObjectProperty.homMk g, hf, hg⟩

/-! ### The interval's monoid is the positive braid monoid

The two presentations have the same generators (`simpleEquivPerm`) and the same relations: a
factorisation of a simple is a length-additive product, and every length-additive product is a
factorisation. -/

/-- **The germ relation**, between the simples a composable pair names. -/
theorem posPerm_crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    posPerm (crossPermN g) * posPerm (crossPermN f) = posPerm (crossPermN (f ≫ g)) := by
  rw [posPerm_mul (permLen_crossPermN_comp f g), crossPermN_comp]

theorem posPerm_crossPermN_eq_one {A B : ChStrands Zbp n} {f : A ⟶ B} (h : WStrands Zbp n f) :
    posPerm (crossPermN f) = 1 := by
  rw [crossPermN_eq_one_of_WStrands h, posPerm_one]

/-- **Forward**: a simple is the positive braid of its crossing permutation.  Padding by the two
`W`-arrows leaves the permutations alone, so the factorisation relation becomes the germ one. -/
noncomputable def garToPos (n : ℕ) :
    GarsideMonoid (WStrands Zbp n) (onesObj n) (topObj n) →* PosBraid n :=
  GarsideMonoid.lift _ (fun h => posPerm (crossPermN h))
    (fun hw => posPerm_crossPermN_eq_one hw)
    fun f g u v hu hv => by
      change posPerm (crossPermN (u ≫ g)) * posPerm (crossPermN (f ≫ v))
        = posPerm (crossPermN (f ≫ g))
      rw [crossPermN_comp u g, crossPermN_comp f v, crossPermN_eq_one_of_WStrands hu,
        crossPermN_eq_one_of_WStrands hv, mul_one, one_mul]
      exact posPerm_crossPermN_comp f g

/-- **Backward**: a permutation is the simple realising it.  The atom relation is the
factorisation `1ⁿ ⟶ atomComp n i ⟶ [n]`, padded to simples at the middle chain. -/
noncomputable def posToGar (n : ℕ) :
    PosBraid n →* GarsideMonoid (WStrands Zbp n) (onesObj n) (topObj n) :=
  PosBraid.liftAtom (fun σ => garOf (WStrands Zbp n) (onesToTop n σ))
    (garOf_triv ((wStrands_iff_crossPermN _).mpr (crossPermN_onesToTop n 1)))
    fun β i hβ => by
      obtain ⟨M, F, G, hF, hG⟩ := exists_atom_pairN β i hβ
      have hu := (onesWideInitial n).mem M
      have hv := (topWideTerminal n).mem M
      have h1 : (onesWideInitial n).to M ≫ G = onesToTop n β :=
        hom_ext_of_crossPermN (by
          rw [crossPermN_comp, hG, crossPermN_eq_one_of_WStrands hu, mul_one,
            crossPermN_onesToTop])
      have h2 : F ≫ (topWideTerminal n).from M = onesToTop n (adjT i) :=
        hom_ext_of_crossPermN (by
          rw [crossPermN_comp, hF, crossPermN_eq_one_of_WStrands hv, one_mul,
            crossPermN_onesToTop])
      have h3 : F ≫ G = onesToTop n (β * adjT i) :=
        hom_ext_of_crossPermN (by rw [crossPermN_comp, hF, hG, crossPermN_onesToTop])
      change garOf (WStrands Zbp n) (onesToTop n β) * garOf (WStrands Zbp n) (onesToTop n (adjT i))
        = garOf (WStrands Zbp n) (onesToTop n (β * adjT i))
      rw [← h1, ← h2, ← h3]
      exact garOf_comp F G hu hv

theorem posToGar_comp_garToPos (n : ℕ) : (posToGar n).comp (garToPos n)
    = MonoidHom.id (GarsideMonoid (WStrands Zbp n) (onesObj n) (topObj n)) :=
  garsideMonoid_ext fun h => congrArg (garOf (WStrands Zbp n)) (onesToTop_crossPermN h)

theorem garToPos_comp_posToGar (n : ℕ) :
    (garToPos n).comp (posToGar n) = MonoidHom.id (PosBraid n) :=
  posPerm_ext fun σ => congrArg posPerm (crossPermN_onesToTop n σ)

/-- **The interval's monoid is the positive braid monoid** — the Garside germ presentation, with
the generating set intrinsic to the chains. -/
noncomputable def garsideEquivPosBraid (n : ℕ) :
    GarsideMonoid (WStrands Zbp n) (onesObj n) (topObj n) ≃* PosBraid n where
  toFun := garToPos n
  invFun := posToGar n
  left_inv q := DFunLike.congr_fun (posToGar_comp_garToPos n) q
  right_inv b := DFunLike.congr_fun (garToPos_comp_posToGar n) b
  map_mul' := map_mul (garToPos n)

@[simp] theorem garsideEquivPosBraid_garOf (n : ℕ) (h : onesObj n ⟶ topObj n) :
    garsideEquivPosBraid n (garOf (WStrands Zbp n) h) = posPerm (crossPermN h) := rfl

/-! ### The Garside element

`Δ` is the simple that reverses the run.  It crosses every pair, so the two complements of a simple
`σ` — `σ⁻¹Δ` on the right and `Δσ⁻¹` on the left — multiply back to it length-additively, which is
divisibility on both sides. -/

/-- **The Garside element**: the simple reversing the run, which crosses every pair. -/
noncomputable def garsideDelta (n : ℕ) : onesObj n ⟶ topObj n := onesToTop n Fin.revPerm

@[simp] theorem crossPermN_garsideDelta (n : ℕ) :
    crossPermN (garsideDelta n) = Fin.revPerm := crossPermN_onesToTop n _

/-- The right complement of a simple in `Δ`. -/
noncomputable def rightComplement (h : onesObj n ⟶ topObj n) : onesObj n ⟶ topObj n :=
  onesToTop n ((crossPermN h)⁻¹ * Fin.revPerm)

/-- The left complement of a simple in `Δ`. -/
noncomputable def leftComplement (h : onesObj n ⟶ topObj n) : onesObj n ⟶ topObj n :=
  onesToTop n (Fin.revPerm * (crossPermN h)⁻¹)

/-- **A composable pair of simples reversing the run multiplies to `Δ`**: the crossings add up, so
`posPerm` is multiplicative on them. -/
theorem garOf_mul_of_mul_eq_rev {h k : onesObj n ⟶ topObj n}
    (hmul : crossPermN h * crossPermN k = Fin.revPerm) :
    garOf (WStrands Zbp n) h * garOf (WStrands Zbp n) k = garOf (WStrands Zbp n) (garsideDelta n) :=
  (garsideEquivPosBraid n).injective <| by
    rw [map_mul, garsideEquivPosBraid_garOf, garsideEquivPosBraid_garOf,
      garsideEquivPosBraid_garOf, crossPermN_garsideDelta,
      posPerm_mul (permLen_mul_of_eq_rev hmul), hmul]

/-- **Every simple left-divides `Δ`.** -/
theorem garOf_mul_rightComplement (h : onesObj n ⟶ topObj n) :
    garOf (WStrands Zbp n) h * garOf (WStrands Zbp n) (rightComplement h)
      = garOf (WStrands Zbp n) (garsideDelta n) :=
  garOf_mul_of_mul_eq_rev (by rw [rightComplement, crossPermN_onesToTop, mul_inv_cancel_left])

/-- **…and right-divides it.** -/
theorem garOf_leftComplement_mul (h : onesObj n ⟶ topObj n) :
    garOf (WStrands Zbp n) (leftComplement h) * garOf (WStrands Zbp n) h
      = garOf (WStrands Zbp n) (garsideDelta n) :=
  garOf_mul_of_mul_eq_rev (by rw [leftComplement, crossPermN_onesToTop, inv_mul_cancel_right])

/-! ### The other two readings

`Foundations/GarsidePresentation` names the same monoid by all the arrows (`LocMonoid`) and by the
loops at the basepoint; both come for free once the interval is named. -/

/-- **The strand-`n` component, localized at the bead merges, is presented by its interval** —
generators the chain morphisms `1ⁿ ⟶ [n]`, relations their factorisations. -/
noncomputable def endEquivGarsideZ (n : ℕ) :
    GarsideMonoid (WStrands Zbp n) (onesObj n) (topObj n)
      ≃* End ((WStrands Zbp n).Q.obj (topObj n)) :=
  endEquivGarside (topWideTerminal n) (onesWideInitial n)

/-- **The monoid presented by the chain morphisms is the positive braid monoid.** -/
noncomputable def locEquivPosBraid (n : ℕ) : LocMonoid (WStrands Zbp n) ≃* PosBraid n :=
  (locEquivGarside (topWideTerminal n) (onesWideInitial n)).trans (garsideEquivPosBraid n)

/-- The pads contribute no crossing, which is why a class is named by its permutation. -/
theorem crossPermN_pad {A B : ChStrands Zbp n} (f : A ⟶ B) :
    crossPermN (pad (topWideTerminal n) (onesWideInitial n) f) = crossPermN f := by
  simp only [pad]
  rw [crossPermN_comp, crossPermN_comp, crossPermN_eq_one_of_WStrands ((onesWideInitial n).mem A),
    crossPermN_eq_one_of_WStrands ((topWideTerminal n).mem B), one_mul, mul_one]

@[simp] theorem locEquivPosBraid_locOf {A B : ChStrands Zbp n} (f : A ⟶ B) :
    locEquivPosBraid n (locOf (WStrands Zbp n) f) = posPerm (crossPermN f) := by
  change posPerm (crossPermN (pad (topWideTerminal n) (onesWideInitial n) f)) = _
  rw [crossPermN_pad]

/-- **The serial wedges, localized at the bead merges, have the positive braid monoid as the
endomorphisms of the coarsest chain** — the Garside germ presentation, arrived at from the
geometry of refinement rather than assumed. -/
noncomputable def endEquivPosBraid (n : ℕ) :
    End ((WStrands Zbp n).Q.obj (topObj n)) ≃* PosBraid n :=
  (endEquivWStrands n).symm.trans (locEquivPosBraid n)

/-! ### The length function

`permLen` is additive over composition (`permLen_crossPermN_comp`) and vanishes exactly on the
merges (`wStrands_iff_permLen`), so it survives the localization as a monoid hom.  Being additive
and detecting the identity, it is the Garside length function — not transported from `Perm`, but
equal
to the number of factors of any factorisation. -/

/-- **The length of a class**: the crossings any representative makes. -/
noncomputable def locLen (n : ℕ) : LocMonoid (WStrands Zbp n) →* Multiplicative ℕ :=
  (posLen n).comp (locEquivPosBraid n).toMonoidHom

@[simp] theorem locLen_locOf {A B : ChStrands Zbp n} (f : A ⟶ B) :
    locLen n (locOf (WStrands Zbp n) f) = Multiplicative.ofAdd (permLen (crossPermN f)) := by
  rw [locLen, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, locEquivPosBraid_locOf,
    posLen_posPerm]

/-- **The length detects the identity.** -/
theorem locLen_eq_zero_iff {x : LocMonoid (WStrands Zbp n)} :
    Multiplicative.toAdd (locLen n x) = 0 ↔ x = 1 := by
  rw [locLen, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, posLen_eq_zero_iff,
    ← map_one (locEquivPosBraid n), (locEquivPosBraid n).apply_eq_iff_eq]

/-- **Inverting the merges creates no units**: a product is trivial only if its factors are. -/
theorem loc_eq_one_of_mul_eq_one {x y : LocMonoid (WStrands Zbp n)} (h : x * y = 1) : x = 1 := by
  have hsum := congrArg (fun z => Multiplicative.toAdd (locLen n z)) h
  simp only [map_mul, toAdd_mul, map_one, toAdd_one] at hsum
  exact locLen_eq_zero_iff.mp (by omega)

end ChainCat
