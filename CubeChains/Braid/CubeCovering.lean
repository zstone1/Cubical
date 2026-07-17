import CubeChains.Braid.CubeViaZ
import CubeChains.Braid.ElementaryBraiding
import CubeChains.Salvetti.BraidReindex
import CubeChains.Arrangements.BraidPreorder
import CubeChains.Foundations.QuotientCat
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Braid/CubeCovering — injectivity of the cube→terminal comparison map `φ_x`

`concToZAut n x` (`φ_x`, `CubeViaZ`) is the vertex-group map of the forgetful push
`FreeGroupoid.map (concToZ (□n))`; injectivity of `φ_x` is the categorical `Pₙ ↪ Bₙ` (the
ordered→unordered covering's injection on `π₁`).  It holds iff that pushed functor is faithful, and
injectivity transports along any concurrency iso, so it suffices to check one execution per
component (`concToZAut_injective_of_concRun`).

The covering that supplies that faithfulness is the free `Sₙ`-reorientation action on the Salvetti
poset (Pełka–Ziemiański's principal-`Sₙ`-bundle): reorientation is an order-free action
(`OrderFreeAction`), so `OrderQuotient.QuotCat` presents the unordered Salvetti as its quotient.

Gotcha: `concToZ` is faithful on the base `ConcCat (□n)` but this does **not** descend.
`concToZ` is star-bijective (refinements lift freely — axis labels ride along) yet **not**
costar-bijective: a coarse cell downstairs has extra unordered coarsenings (e.g. the opposite
boundary path of a square), with no cube lift.  The `Sₙ`-quotient of the Salvetti model is the
covering that repairs this.
-/

open CategoryTheory

namespace CubeChains

/-! ## `mapAut` injectivity is vertex-faithfulness -/

variable {C : Type*} [Groupoid C] {D : Type*} [Groupoid D]

/-- `F.mapAut X` is injective as soon as `F.map` is injective on the vertex endos `X ⟶ X`. -/
theorem mapAut_injective_of_map_injective (F : C ⥤ D) (X : C)
    (h : Function.Injective (fun g : X ⟶ X => F.map g)) :
    Function.Injective (F.mapAut X) := by
  intro a b hab
  apply Aut.ext
  apply h
  exact congrArg Iso.hom hab

/-- Conversely, `F.mapAut X` injective forces `F.map` injective on vertex endos:
in a groupoid every endo is the `.hom` of an `Aut`. -/
theorem map_injective_of_mapAut_injective (F : C ⥤ D) (X : C)
    (h : Function.Injective (F.mapAut X)) :
    Function.Injective (fun g : X ⟶ X => F.map g) := by
  intro g g' hgg
  have hg : (Groupoid.isoEquivHom X X).symm g = (Groupoid.isoEquivHom X X).symm g' := by
    apply h
    apply Aut.ext
    exact hgg
  simpa using congrArg (Groupoid.isoEquivHom X X) hg

/-! ## Conjugation transports vertex-faithfulness across a connecting iso -/

/-- Conjugate automorphisms of `X` by an iso `p : X ≅ Y` — a group isomorphism `Aut X ≃* Aut Y`. -/
@[simps]
def autConj {X Y : C} (p : X ≅ Y) : Aut X ≃* Aut Y where
  toFun a := p.symm ≪≫ a ≪≫ p
  invFun b := p ≪≫ b ≪≫ p.symm
  left_inv a := by ext; simp
  right_inv b := by ext; simp
  map_mul' a b := by
    apply Aut.ext
    simp only [Aut.Aut_mul_def, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]

/-- **Naturality of `mapAut` under conjugation.**  Pushing a conjugated automorphism and conjugating
a pushed automorphism agree: `F` preserves `≪≫`. -/
theorem mapAut_autConj (F : C ⥤ D) {X Y : C} (p : X ≅ Y) (a : Aut X) :
    F.mapAut Y (autConj p a) = autConj (F.mapIso p) (F.mapAut X a) := by
  apply Aut.ext
  change F.map ((p.symm ≪≫ a ≪≫ p).hom) = _
  simp only [autConj_apply, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp]
  rfl

/-- **Transport of `mapAut` injectivity across a connecting iso.**  If `mapAut` is injective at `X`
and `p : X ≅ Y`, then it is injective at `Y`. -/
theorem mapAut_injective_of_iso (F : C ⥤ D) {X Y : C} (p : X ≅ Y)
    (h : Function.Injective (F.mapAut X)) :
    Function.Injective (F.mapAut Y) := by
  intro a b hab
  -- pull `a, b` back to `Aut X`
  have ha : F.mapAut Y a = F.mapAut Y (autConj p ((autConj p).symm a)) := by
    rw [MulEquiv.apply_symm_apply]
  have hb : F.mapAut Y b = F.mapAut Y (autConj p ((autConj p).symm b)) := by
    rw [MulEquiv.apply_symm_apply]
  rw [ha, hb, mapAut_autConj, mapAut_autConj] at hab
  have hab' := (autConj (F.mapIso p)).injective hab
  have := h hab'
  have := (autConj p).symm.injective this
  simpa using this

/-! ## The base functor `concToZ` is faithful

The comparison push forgets only a cube's axis labels; the underlying wedge map of a refinement is
untouched, and a `Ch`/`ConcCat` morphism is determined by that wedge map.  So `concToZ` is faithful
on the base category `ConcCat (□n)`.  This is the *easy* half — it does **not** give injectivity of
`concToZAut`, which lives on the free groupoid (see the module note below). -/

/-- `ChainCat.pushforward f` is faithful: it leaves the underlying wedge map `Hom.φ` unchanged, and
a chain morphism is determined by its wedge map (`hom_ext'`). -/
instance ChainCat.pushforward_faithful {K L : BPSet} (f : K ⟶ L) :
    (ChainCat.pushforward f).Faithful where
  map_injective {_ _} {g g'} h := by
    apply ChainCat.hom_ext'
    rw [← ChainCat.pushforward_map_φ f g, ← ChainCat.pushforward_map_φ f g']
    exact congrArg ChainCat.Hom.φ h

/-- `concMap f` is faithful: on `(Lines _).Elements` a morphism is determined by its underlying
`Ch`-morphism (`CategoryOfElements.ext`), which `pushforward f` preserves faithfully. -/
instance concMap_faithful {K L : BPSet} (f : K ⟶ L) : (concMap f).Faithful where
  map_injective {_ _} g g' h :=
    CategoryOfElements.ext _ g g'
      ((ChainCat.pushforward f).op.map_injective (congrArg Subtype.val h))

/-- **`concToZ (□n)` is faithful.**  Forgetting axis labels is injective on refinement morphisms. -/
instance concToZ_faithful (n : ℕ) : (concToZ (□n)).Faithful := concMap_faithful _

/-! ## `concToZ` is star-bijective: outgoing refinements lift uniquely

For **any** `f : K ⟶ L` the pushforward `concMap f` is star-bijective.  An outgoing refinement of
`(concMap f).obj x` is a wedge map `φ` into `x`'s chain; its source chain over `K` is forced to
`⟨_, φ ≫ x.chain.map⟩` by the triangle, so every downstairs refinement lifts and the triangle pins
the lift (the axis labels ride along on the carried line).  `concToZ (□n)` is
`concMap (toZbp (□n))`, so it is the `n`-cube instance. -/

section StarBijective

open Opposite Quiver

/-- Map-only extensionality for chains: equal classifying maps over equal dims give equal chains. -/
theorem ChainCat.obj_ext_map {K : BPSet} {d : List ℕ+} {m₁ m₂ : (⋁d) ⟶ K}
    (h : m₁ = m₂) : (⟨d, m₁⟩ : Ch K) = ⟨d, m₂⟩ := by rw [h]

/-- Two execution refinements out of `x` with equal underlying wedge maps are heterogeneously equal
once their targets agree (`ConcCat` morphisms are determined by their `Ch`-morphism, which is
determined by its wedge map). -/
theorem ConcCat.hom_heq_of_φ {K : BPSet} {x z₁ z₂ : ConcCat K} (hz : z₁ = z₂)
    {g₁ : x ⟶ z₁} {g₂ : x ⟶ z₂}
    (hφ : HEq (ChainCat.Hom.φ g₁.val.unop) (ChainCat.Hom.φ g₂.val.unop)) : HEq g₁ g₂ := by
  subst hz
  exact heq_of_eq
    (CategoryOfElements.ext (Lines K) g₁ g₂
      (Quiver.Hom.unop_inj (ChainCat.hom_ext' (eq_of_heq hφ))))

/-- The lift of an outgoing refinement `s` of `(concMap f).obj x`: rebuild the source chain over `K`
by pre-composing the wedge map with `x`'s classifying map (the triangle is `rfl`), and carry the
line. -/
def concMapStarInv {K L : BPSet} (f : K ⟶ L) (x : ConcCat K)
    (s : Quiver.Star ((concMap f).obj x)) : Quiver.Star x :=
  let φ0 := ChainCat.Hom.φ s.2.val.unop
  let b : Ch K := ⟨s.1.chain.dims, φ0 ≫ x.chain.map⟩
  let h : b ⟶ x.chain := ⟨φ0, rfl⟩
  ⟨⟨op b, (Lines K).map h.op x.2⟩, ⟨h.op, rfl⟩⟩

/-- **`concMap f` is star-bijective.**  Every outgoing refinement of `(concMap f).obj x` lifts, and
uniquely, to one of `x`. -/
theorem concMap_star_bijective {K L : BPSet} (f : K ⟶ L) (x : ConcCat K) :
    Function.Bijective ((concMap f).toPrefunctor.star x) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨concMapStarInv f x, ?_, ?_⟩
  · rintro ⟨z, g⟩
    have hbz : (⟨z.chain.dims, ChainCat.Hom.φ g.val.unop ≫ x.chain.map⟩ : Ch K) = z.chain :=
      ChainCat.obj_ext_map g.val.unop.w
    have hfst : (concMapStarInv f x ((concMap f).toPrefunctor.star x ⟨z, g⟩)).1 = z := by
      refine Sigma.ext ?_ (heq_of_eq g.property)
      exact congrArg op hbz
    exact Sigma.ext hfst (ConcCat.hom_heq_of_φ hfst HEq.rfl)
  · rintro s
    have hs1 : (ChainCat.pushforward f).obj
        (⟨s.1.chain.dims, ChainCat.Hom.φ s.2.val.unop ≫ x.chain.map⟩ : Ch K) = s.1.chain :=
      ChainCat.obj_ext_map (by rw [Category.assoc]; exact s.2.val.unop.w)
    have hfst : ((concMap f).toPrefunctor.star x (concMapStarInv f x s)).1 = s.1 := by
      refine Sigma.ext ?_ (heq_of_eq s.2.property)
      exact congrArg op hs1
    exact Sigma.ext hfst (ConcCat.hom_heq_of_φ hfst HEq.rfl)

/-- **`concToZ (□n)` is star-bijective.**  Every outgoing refinement of `(concToZ (□n)).obj x` lifts
uniquely to a refinement of `x`. -/
theorem concToZ_star_bijective {n : ℕ} (x : ConcCat (□n)) :
    Function.Bijective ((concToZ (□n)).toPrefunctor.star x) :=
  concMap_star_bijective (toZbp (□n)) x

end StarBijective

/-! ## The reduction: `φ_x` injective from free-groupoid faithfulness

`φ_x = (FreeGroupoid.map (concToZ (□n))).mapAut (mk x)`, so it is injective exactly when the pushed
functor is faithful on the vertex homs `mk x ⟶ mk x`.  Base faithfulness (above) does **not**
suffice: the free groupoid inverts and quotients morphisms, so faithfulness must be re-established
*there*.  The remaining content is precisely the categorical `Pₙ ↪ Bₙ` — the ordered→unordered
covering's injection on `π₁`. -/

/-- **`φ_x` injective, reduced to faithfulness of the pushed groupoid functor.**  If
`FreeGroupoid.map (concToZ (□n))` is faithful on vertex homs, every comparison map `φ_x` is
injective.  The remaining content — that faithfulness — is the `Pₙ ↪ Bₙ` covering-descent pursued
below via the free `Sₙ` reorientation action (Pełka–Ziemiański's principal-`Sₙ`-bundle). -/
theorem concToZAut_injective_of_faithful (n : ℕ)
    (hF : (FreeGroupoid.map (concToZ (□n))).Faithful) (x : ConcCat (□n)) :
    Function.Injective (concToZAut n x) :=
  mapAut_injective_of_map_injective _ (FreeGroupoid.mk x) (fun _ _ h => hF.map_injective h)

/-- **Transport of `φ_x` injectivity across a concurrency iso.**  If `φ_x` is injective and `x`, `y`
are isomorphic in `ConcGrpd (□n)`, then `φ_y` is injective — so injectivity is a property of the
connected component of `x`. -/
theorem concToZAut_injective_of_iso (n : ℕ) {x y : ConcCat (□n)}
    (p : (FreeGroupoid.mk x : ConcGrpd (□n)) ≅ FreeGroupoid.mk y)
    (h : Function.Injective (concToZAut n x)) :
    Function.Injective (concToZAut n y) :=
  mapAut_injective_of_iso (FreeGroupoid.map (concToZ (□n))) p h

/-- The run obtained by sequentializing `x` along its own line — a maximal (all-events-serial)
execution `x` refines into. -/
def concRun (n : ℕ) (x : ConcCat (□n)) : ConcCat (□n) :=
  runExec (seqChain x.line) (seqChain_isRun x.line)

/-- **Reduce `φ_x` injectivity to a run.**  Every execution refines to a run (`seqMor`), an iso in
`ConcGrpd (□n)`; injectivity transports back along it.  So it suffices to check `φ` at runs. -/
theorem concToZAut_injective_of_concRun (n : ℕ) (x : ConcCat (□n))
    (h : Function.Injective (concToZAut n (concRun n x))) :
    Function.Injective (concToZAut n x) :=
  concToZAut_injective_of_iso n
    ((Groupoid.isoEquivHom (FreeGroupoid.mk x) (FreeGroupoid.mk (concRun n x))).symm
      (FreeGroupoid.homMk (seqMor x x.line))).symm h

/-! ## The deck group: the `Sₙ`-reorientation action is order-free

The covering that supplies the missing free-groupoid faithfulness is the free `Sₙ` action on the
braid-arrangement Salvetti poset (`reorient`/`salReindex`).  Its freeness — the paper's
principal-`Sₙ`-bundle hypothesis — rests on **order rigidity**: an injective height and its
`σ`-relabeling induce the same braid sign only for `σ = 1`.  Every tope is realised by an injective
height (`braidCOM_isTope_iff_injective`), and every Salvetti cell carries a tope, so `σ` fixing a
cell (even weakly upward) forces `σ = 1`. -/

open SignType

variable {n : ℕ}

/-- **Order rigidity.**  For injective `ρ`, the relabeling `ρ ∘ π` has the same braid sign as `ρ`
only when `π = 1`: `π` would be an order-automorphism of the finite total order `ρ` induces, hence
the identity (ranks are preserved and injective). -/
theorem perm_eq_one_of_braidSign_comp {ρ : Fin n → ℤ} (hρ : Function.Injective ρ)
    {π : Equiv.Perm (Fin n)} (h : braidSign (fun i => ρ (π i)) = braidSign ρ) : π = 1 := by
  have hord : ∀ p q : Fin n, ρ (π p) < ρ (π q) ↔ ρ p < ρ q := by
    intro p q
    have hs : sign (ρ (π p) - ρ (π q)) = sign (ρ p - ρ q) := by
      rw [← signAt_braidSign (fun i => ρ (π i)) p q, ← signAt_braidSign ρ p q, h]
    rw [show (ρ (π p) < ρ (π q)) ↔ (ρ (π p) - ρ (π q) < 0) from by omega,
        show (ρ p < ρ q) ↔ (ρ p - ρ q < 0) from by omega,
        ← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, hs]
  have rank_lt : ∀ {p q : Fin n}, ρ p < ρ q →
      (Finset.univ.filter (fun a => ρ a < ρ p)).card
        < (Finset.univ.filter (fun a => ρ a < ρ q)).card := by
    intro p q hpq
    apply Finset.card_lt_card
    have hsub : Finset.univ.filter (fun a => ρ a < ρ p)
        ⊆ Finset.univ.filter (fun a => ρ a < ρ q) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, lt_trans ha.2 hpq⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩,
      fun hc => absurd (Finset.mem_filter.mp hc).2 (lt_irrefl _)⟩
  have rank_eq : ∀ p : Fin n,
      (Finset.univ.filter (fun a => ρ a < ρ (π p))).card
        = (Finset.univ.filter (fun a => ρ a < ρ p)).card := by
    intro p
    apply Finset.card_equiv π.symm
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hord (π.symm i) p
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  refine Equiv.ext fun p => ?_
  have hp : ρ (π p) = ρ p := by
    rcases lt_trichotomy (ρ (π p)) (ρ p) with hlt | heq | hgt
    · exact absurd (rank_eq p) (ne_of_lt (rank_lt hlt))
    · exact heq
    · exact absurd (rank_eq p).symm (ne_of_lt (rank_lt hgt))
  rw [Equiv.Perm.one_apply]
  exact hρ hp

/-- **Reorientation acts freely on topes.**  A tope is `braidSign ρ` for injective `ρ`
(`braidCOM_isTope_iff_injective`); `reorient σ` fixing it is order rigidity for `σ⁻¹`. -/
theorem reorient_eq_one_of_isTope {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T)
    {σ : Equiv.Perm (Fin n)} (h : reorient σ T = T) : σ = 1 := by
  obtain ⟨ρ, hρ, rfl⟩ := (braidCOM_isTope_iff_injective T).mp hT
  rw [reorient_braidSign] at h
  exact inv_eq_one.mp (perm_eq_one_of_braidSign_comp hρ h)

/-- A permutation fixing a Salvetti cell is the identity: the cell's tope is fixed, and
reorientation is free on topes. -/
theorem salReindexObj_eq_self {a : Sal (braidCOM n)} {σ : Equiv.Perm (Fin n)}
    (h : salReindexObj σ a = a) : σ = 1 :=
  reorient_eq_one_of_isTope a.2.2.1 (congrArg (fun c : Sal (braidCOM n) => c.1.2) h)

/-- A permutation that weakly moves a cell *up* is the identity.  The orbit `σ ^ i • a` is monotone
and periodic (finite order), hence constant, so `a = σ • a`; freeness finishes. -/
theorem salReindexObj_eq_one_of_le_smul {a : Sal (braidCOM n)} {σ : Equiv.Perm (Fin n)}
    (h : a ≤ salReindexObj σ a) : σ = 1 := by
  have hstep : ∀ i : ℕ, σ ^ i • a ≤ σ ^ (i + 1) • a := by
    intro i
    rw [pow_succ, mul_smul]
    exact salReindexObj_monotone (σ ^ i) h
  have hmono : Monotone (fun i : ℕ => σ ^ i • a) := monotone_nat_of_le_succ hstep
  have key := hmono (show (1 : ℕ) ≤ orderOf σ from orderOf_pos σ)
  simp only [pow_one, pow_orderOf_eq_one, one_smul] at key
  exact salReindexObj_eq_self (le_antisymm key h)

/-- **The `Sₙ`-reorientation action on `Sal (braidCOM n)` is order-free** — the paper's
principal-`Sₙ`-bundle input.  Reorientation preserves/reflects the Salvetti order, and only the
identity moves a cell weakly up.  This is the data `OrderQuotient.QuotCat` consumes to present the
unordered Salvetti as the `Sₙ`-quotient covering. -/
instance : OrderQuotient.OrderFreeAction (Equiv.Perm (Fin n)) (Sal (braidCOM n)) where
  smul_le_smul_iff σ := (salReindexOrderIso σ).le_iff_le
  eq_one_of_le_smul _ _ h := salReindexObj_eq_one_of_le_smul h

end CubeChains
