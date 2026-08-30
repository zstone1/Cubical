import CubeChains.Concurrency.Presentation.ChainLocMonoid

/-!
# Concurrency/Presentation/GarsideChains — the strand component is the positive braid monoid

The bead merges have two ends in each strand component: the run of edges is wide-initial
(`onesWideInitial`) and the coarsest chain wide-terminal (`topWideTerminal`).  Padding an arrow
between them makes it a simple `1ⁿ ⟶ [n]` without changing its class or its crossings, and the
simples are exactly `Sₙ` (`simpleEquivPerm`).  So `LocMonoid (WStrands Zbp n)` is the germ monoid
on `Sₙ`: a factorisation of simples is a length-additive product (`permLen_crossPermN_comp`) and
conversely (`exists_atom_pairN`).  `garsideDelta` is the Garside element, divided on both sides by
every simple.
-/

open CategoryTheory CubeChains BPSet Equiv

namespace ChainCat

variable {n : ℕ}

/-! ### The permutation of a morphism of the component

`crossPerm` with the strand count supplied by the component itself.  Everything below is the
`Ch Zbp` law with `A.property` filled in: the count `crossPerm` forces on the target of `f` and the
one `B` carries are proofs of the same equation, hence the same term, so nothing transports. -/

/-- The crossing permutation of a morphism of `ChStrands Zbp n`, read on `Fin n`. -/
def crossPermN {A B : ChStrands Zbp n} (f : A ⟶ B) : Perm (Fin n) := crossPerm A.property f.hom

/-- **The cocycle law in the component.** -/
theorem crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    crossPermN (f ≫ g) = crossPermN g * crossPermN f :=
  crossPerm_comp A.property f.hom g.hom

/-- **Length-additivity in the component** — a crossing made is never undone. -/
theorem permLen_crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    permLen (crossPermN g * crossPermN f) = permLen (crossPermN g) + permLen (crossPermN f) := by
  rw [← crossPermN_comp]
  exact (permLen_crossPerm_comp A.property f.hom g.hom).trans (Nat.add_comm _ _)

/-- **Two arrows of the component with the same crossing permutation agree.** -/
theorem hom_ext_of_crossPermN {A B : ChStrands Zbp n} {f g : A ⟶ B}
    (h : crossPermN f = crossPermN g) : f = g :=
  ObjectProperty.hom_ext _ (hom_ext_of_crossPerm h)

/-- **The merges are exactly the arrows that cross nothing.** -/
theorem wStrands_iff_crossPermN {A B : ChStrands Zbp n} (f : A ⟶ B) :
    WStrands Zbp n f ↔ crossPermN f = 1 :=
  (wStrands_iff f).trans (W_iff_crossPerm_eq_one A.property f.hom)

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

/-- **A simple is its crossing permutation** — `onesTopEquiv`, in the component. -/
noncomputable def simpleEquivPerm (n : ℕ) : (onesObj n ⟶ topObj n) ≃ Perm (Fin n) :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans (onesTopEquiv n)

/-- The simple realising a permutation. -/
noncomputable def onesToTop (n : ℕ) (σ : Perm (Fin n)) : onesObj n ⟶ topObj n :=
  (simpleEquivPerm n).symm σ

@[simp] theorem crossPermN_onesToTop (n : ℕ) (σ : Perm (Fin n)) :
    crossPermN (onesToTop n σ) = σ := (simpleEquivPerm n).apply_symm_apply σ

@[simp] theorem onesToTop_crossPermN (h : onesObj n ⟶ topObj n) :
    onesToTop n (crossPermN h) = h := (simpleEquivPerm n).symm_apply_apply h

/-- **The atom pair of `Concurrency/Merge/AtomPair`, in the component.**  An index of `Fin (n-1)`
forces `n` positive, where `topDims n` is the one-bead chain `atomComp` already lands in. -/
theorem exists_atom_pairN (β : Perm (Fin n)) (i : Fin (n - 1))
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ (M : ChStrands Zbp n) (F : onesObj n ⟶ M) (G : M ⟶ topObj n),
      crossPermN F = adjT i ∧ crossPermN G = β := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  obtain ⟨f, g, hf, hg, -⟩ := exists_atom_pair i hβ
  exact ⟨⟨zObj (atomComp (k + 1) i), dimSum_atomComp (k + 1) i⟩,
    ObjectProperty.homMk f, ObjectProperty.homMk g, hf, hg⟩

/-! ### The localized component is the positive braid monoid

Both directions are the crossing permutation.  Forwards it is a grading: additive over composition
and trivial on the merges.  Backwards a permutation is the simple realising it, and the atom
relation is the factorisation `1ⁿ ⟶ atomComp n i ⟶ [n]`. -/

/-- **The germ relation**, between the simples a composable pair names. -/
theorem posPerm_crossPermN_comp {A B C : ChStrands Zbp n} (f : A ⟶ B) (g : B ⟶ C) :
    posPerm (crossPermN g) * posPerm (crossPermN f) = posPerm (crossPermN (f ≫ g)) := by
  rw [posPerm_mul (permLen_crossPermN_comp f g), crossPermN_comp]

theorem posPerm_crossPermN_eq_one {A B : ChStrands Zbp n} {f : A ⟶ B} (h : WStrands Zbp n f) :
    posPerm (crossPermN f) = 1 := by
  rw [crossPermN_eq_one_of_WStrands h, posPerm_one]

/-- **Padding an arrow by the two ends changes neither its class nor its crossings** — both pads
are merges, so they are inverted in `LocMonoid` and cross nothing. -/
theorem locOf_onesToTop_crossPermN {A B : ChStrands Zbp n} (f : A ⟶ B) :
    locOf (WStrands Zbp n) (onesToTop n (crossPermN f)) = locOf (WStrands Zbp n) f := by
  have ht := (onesWideInitial n).mem A
  have hs := (topWideTerminal n).mem B
  have hpad : onesToTop n (crossPermN f)
      = (onesWideInitial n).to A ≫ f ≫ (topWideTerminal n).from B :=
    hom_ext_of_crossPermN (by
      rw [crossPermN_onesToTop, crossPermN_comp, crossPermN_comp,
        crossPermN_eq_one_of_WStrands ht, crossPermN_eq_one_of_WStrands hs, one_mul, mul_one])
  rw [hpad, ← locOf_comp, ← locOf_comp, locOf_triv ht, locOf_triv hs, one_mul, mul_one]

/-- **Forward**: a class is the positive braid of the crossings any representative makes. -/
noncomputable def locToPos (n : ℕ) : LocMonoid (WStrands Zbp n) →* PosBraid n :=
  LocMonoid.lift _ (fun f => posPerm (crossPermN f)) posPerm_crossPermN_comp
    posPerm_crossPermN_eq_one

/-- **Backward**: a permutation is the class of the simple realising it. -/
noncomputable def posToLoc (n : ℕ) : PosBraid n →* LocMonoid (WStrands Zbp n) :=
  PosBraid.liftAtom (fun σ => locOf (WStrands Zbp n) (onesToTop n σ))
    (locOf_triv ((wStrands_iff_crossPermN _).mpr (crossPermN_onesToTop n 1)))
    fun β i hβ => by
      obtain ⟨M, F, G, hF, hG⟩ := exists_atom_pairN β i hβ
      have h : crossPermN (F ≫ G) = β * adjT i := by rw [crossPermN_comp, hF, hG]
      change locOf (WStrands Zbp n) (onesToTop n β) * locOf (WStrands Zbp n) (onesToTop n (adjT i))
        = locOf (WStrands Zbp n) (onesToTop n (β * adjT i))
      rw [← h, ← hG, ← hF]
      simp only [locOf_onesToTop_crossPermN]
      exact locOf_comp F G

theorem locToPos_comp_posToLoc (n : ℕ) :
    (locToPos n).comp (posToLoc n) = MonoidHom.id (PosBraid n) :=
  posPerm_ext fun σ => congrArg posPerm (crossPermN_onesToTop n σ)

theorem posToLoc_comp_locToPos (n : ℕ) :
    (posToLoc n).comp (locToPos n) = MonoidHom.id (LocMonoid (WStrands Zbp n)) :=
  locMonoid_ext fun f => locOf_onesToTop_crossPermN f

/-- **The monoid presented by the chain morphisms is the positive braid monoid** — the Garside
germ presentation, with the generating set intrinsic to the chains. -/
noncomputable def locEquivPosBraid (n : ℕ) : LocMonoid (WStrands Zbp n) ≃* PosBraid n where
  toFun := locToPos n
  invFun := posToLoc n
  left_inv p := DFunLike.congr_fun (posToLoc_comp_locToPos n) p
  right_inv b := DFunLike.congr_fun (locToPos_comp_posToLoc n) b
  map_mul' := map_mul (locToPos n)

@[simp] theorem locEquivPosBraid_locOf {A B : ChStrands Zbp n} (f : A ⟶ B) :
    locEquivPosBraid n (locOf (WStrands Zbp n) f) = posPerm (crossPermN f) := rfl

/-- **The serial wedges, localized at the bead merges, have the positive braid monoid as the
endomorphisms of the coarsest chain** — the Garside germ presentation, arrived at from the
geometry of refinement rather than assumed. -/
noncomputable def endEquivPosBraid (n : ℕ) :
    End ((WStrands Zbp n).Q.obj (topObj n)) ≃* PosBraid n :=
  (endEquivWStrands n).symm.trans (locEquivPosBraid n)

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

/-- **A pair of simples whose crossings reverse the run multiplies to `Δ`**: the crossings add up,
so `posPerm` is multiplicative on them. -/
theorem locOf_mul_of_mul_eq_rev {h k : onesObj n ⟶ topObj n}
    (hmul : crossPermN h * crossPermN k = Fin.revPerm) :
    locOf (WStrands Zbp n) h * locOf (WStrands Zbp n) k
      = locOf (WStrands Zbp n) (garsideDelta n) :=
  (locEquivPosBraid n).injective <| by
    rw [map_mul, locEquivPosBraid_locOf, locEquivPosBraid_locOf, locEquivPosBraid_locOf,
      crossPermN_garsideDelta, posPerm_mul (permLen_mul_of_eq_rev hmul), hmul]

/-- **Every simple left-divides `Δ`.** -/
theorem locOf_mul_rightComplement (h : onesObj n ⟶ topObj n) :
    locOf (WStrands Zbp n) h * locOf (WStrands Zbp n) (rightComplement h)
      = locOf (WStrands Zbp n) (garsideDelta n) :=
  locOf_mul_of_mul_eq_rev (by rw [rightComplement, crossPermN_onesToTop, mul_inv_cancel_left])

/-- **…and right-divides it.** -/
theorem locOf_leftComplement_mul (h : onesObj n ⟶ topObj n) :
    locOf (WStrands Zbp n) (leftComplement h) * locOf (WStrands Zbp n) h
      = locOf (WStrands Zbp n) (garsideDelta n) :=
  locOf_mul_of_mul_eq_rev (by rw [leftComplement, crossPermN_onesToTop, inv_mul_cancel_right])

/-! ### The length function

`permLen` is additive over composition (`permLen_crossPermN_comp`) and vanishes exactly on the
merges (`wStrands_iff_permLen`), so it survives the localization as a monoid hom.  Being additive
and detecting the identity, it is the Garside length function — not transported from `Perm`, but
equal to the number of factors of any factorisation. -/

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
