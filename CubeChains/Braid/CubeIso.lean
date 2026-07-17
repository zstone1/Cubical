import CubeChains.Braid.Grading
import CubeChains.Events.EventLocalSystem

/-!
# Braid/CubeIso — `braidGrpd` on a cube is an isomorphism onto the pure braids

Target (`Cubical-xhj.6`): the map `braidGrpd (□n)` induces on the vertex group `ConcBraid(□n) x` is
a group isomorphism onto `Pₙ` — pure, injective, surjective.  Under construction; currently
**feature 1 (purity)**.

The purity mechanism: for a cube every event carries a refinement-invariant axis in `Fin n`
(`cubeName`), so the permutation shadow of the braid depends only on the endpoints of a zigzag —
it is a `SingleObj.differenceFunctor`, which sends every loop to the identity.
-/

open CategoryTheory CategoryTheory.Sigma

namespace CubeChains

/-- A frame-difference functor sends every **loop** to the identity: `differenceFunctor g` maps a
morphism to `g y · (g x)⁻¹`, which depends only on the endpoints, and a loop has `x = y`. -/
theorem differenceFunctor_loop {C : Type*} [Category C] {G : Type*} [Group G]
    (g : C → G) {X : C} (γ : X ⟶ X) :
    (SingleObj.differenceFunctor g).map γ = 𝟙 _ := by
  rw [SingleObj.differenceFunctor_map, mul_inv_cancel]
  rfl

/-! ## The two event frames of a cube execution -/

variable {n : ℕ}

/-- The **axis frame**: the refinement-invariant naming of a cube chain's events by their `Fin n`
axis (`cubeName`), as a bijection. -/
noncomputable def cubeAxis (a : Ch (□n)) : EventObj a ≃ Fin n :=
  Equiv.ofBijective (cubeName a)
    ((Fintype.bijective_iff_injective_and_card (cubeName a)).mpr
      ⟨cubeName_faithful a, (eventObj_card_cube a).trans (Fintype.card_fin n).symm⟩)

@[simp] theorem cubeAxis_apply (a : Ch (□n)) (e : EventObj a) : cubeAxis a e = cubeName a e := rfl

/-- The **line frame**: a cube execution's events named in `evKey` order, as `Fin n`. -/
def cubeLine (x : ConcCat (□n)) : EventObj x.chain ≃ Fin n :=
  (keyEquiv (evKey x.line) (evKey_injective x.line)).trans (finCongr (eventObj_card_cube x.chain))

/-- The **frame difference** of a cube execution: the axis frame read through the line frame. -/
noncomputable def cubeFrameDiff (x : ConcCat (□n)) : Equiv.Perm (Fin n) :=
  (cubeAxis x.chain).symm.trans (cubeLine x)

/-! ## The permutation shadow of the braid, as a frame-difference functor -/

/-- The event transition of a morphism of executions (source events → target events). -/
def cubeTrans {x y : ConcCat (□n)} (f : x ⟶ y) :
    EventObj x.chain ≃ EventObj y.chain :=
  (eventEquiv (concRefine' f)).symm

/-- The permutation shadow: a morphism `f` acts on `Fin n` by transporting the line frames through
the event transition (`cubeLine x⁻¹`, then `cubeTrans f`, then `cubeLine y`). -/
def cubeSh (n : ℕ) : ConcCat (□n) ⥤ SingleObj (Equiv.Perm (Fin n)) where
  obj _ := SingleObj.star _
  map {x y} f := ((cubeLine x).symm.trans (cubeTrans f)).trans (cubeLine y)
  map_id x := by
    have h : cubeTrans (𝟙 x) = Equiv.refl (EventObj x.chain) := by
      rw [cubeTrans, show concRefine' (𝟙 x) = 𝟙 x.chain from rfl, eventEquiv_id]; rfl
    change ((cubeLine x).symm.trans (cubeTrans (𝟙 x))).trans (cubeLine x) = 1
    rw [h, Equiv.trans_refl, Equiv.symm_trans_self]; rfl
  map_comp {x y z} f g := by
    have h : cubeTrans (f ≫ g) = (cubeTrans f).trans (cubeTrans g) := by
      apply Equiv.ext; intro e
      simp only [cubeTrans, show concRefine' (f ≫ g) = concRefine' g ≫ concRefine' f from rfl,
        eventEquiv_comp, Equiv.symm_trans_apply, Equiv.trans_apply]
    change ((cubeLine x).symm.trans (cubeTrans (f ≫ g))).trans (cubeLine z)
      = (((cubeLine y).symm.trans (cubeTrans g)).trans (cubeLine z))
        * (((cubeLine x).symm.trans (cubeTrans f)).trans (cubeLine y))
    rw [h]
    ext k
    simp only [Equiv.Perm.mul_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp] theorem cubeSh_map {x y : ConcCat (□n)} (f : x ⟶ y) :
    (cubeSh n).map f = ((cubeLine x).symm.trans (cubeTrans f)).trans (cubeLine y) := rfl

/-- **`cubeName` coherence, as an equality of event bijections.**  The event transition of a
refinement is the change of axis-frame: refinements identify events by their axis. -/
theorem cubeTrans_eq_axis {x y : ConcCat (□n)} (f : x ⟶ y) :
    cubeTrans f = (cubeAxis x.chain).trans (cubeAxis y.chain).symm := by
  apply Equiv.ext
  intro e
  rw [Equiv.trans_apply, Equiv.eq_symm_apply, cubeAxis_apply, cubeAxis_apply]
  show cubeName y.chain ((eventEquiv (concRefine' f)).symm e) = cubeName x.chain e
  have hev : eventMap (concRefine' f) ((eventEquiv (concRefine' f)).symm e) = e := by
    change (eventEquiv (concRefine' f)) ((eventEquiv (concRefine' f)).symm e) = e
    exact Equiv.apply_symm_apply _ e
  have h := cubeName_coherent (concRefine' f) ((eventEquiv (concRefine' f)).symm e)
  exact (hev ▸ h).symm

/-- The shadow's value on a morphism is the frame difference of its endpoints. -/
theorem cubeSh_map_eq {x y : ConcCat (□n)} (f : x ⟶ y) :
    (cubeSh n).map f = cubeFrameDiff y * (cubeFrameDiff x)⁻¹ := by
  rw [cubeSh_map, cubeTrans_eq_axis]
  unfold cubeFrameDiff
  apply Equiv.ext
  intro k
  simp [Equiv.Perm.mul_apply]

/-- **The shadow is a frame difference.**  Hence, lifted to the free groupoid, it kills loops. -/
theorem cubeSh_eq_differenceFunctor (n : ℕ) :
    cubeSh n = SingleObj.differenceFunctor cubeFrameDiff := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y f => ?_
  rw [cubeSh_map_eq, SingleObj.differenceFunctor_map]
  show cubeFrameDiff y * (cubeFrameDiff x)⁻¹
      = 𝟙 (SingleObj.star (Equiv.Perm (Fin n)))
        ≫ (cubeFrameDiff y * (cubeFrameDiff x)⁻¹) ≫ 𝟙 (SingleObj.star (Equiv.Perm (Fin n)))
  rw [Category.id_comp, Category.comp_id]

/-- **The permutation shadow of the cube braid kills every loop.**  On the free groupoid the shadow
`cubeSh` is a `differenceFunctor`, whose value depends only on the endpoints. -/
theorem cubeSh_lift_loop {x : ConcCat (□n)}
    (γ : (FreeGroupoid.mk x : ConcGrpd (□n)) ⟶ FreeGroupoid.mk x) :
    (FreeGroupoid.lift (cubeSh n)).map γ = 𝟙 _ := by
  have h : FreeGroupoid.lift (cubeSh n)
      = SingleObj.differenceFunctor (fun Y : ConcGrpd (□n) => cubeFrameDiff Y.as.as) := by
    refine (FreeGroupoid.lift_unique _ _ ?_).symm
    refine CategoryTheory.Functor.ext (fun _ => rfl) fun a b f => ?_
    rw [cubeSh_map_eq, Functor.comp_map, SingleObj.differenceFunctor_map]
    show cubeFrameDiff b * (cubeFrameDiff a)⁻¹
        = 𝟙 (SingleObj.star (Equiv.Perm (Fin n)))
          ≫ (cubeFrameDiff b * (cubeFrameDiff a)⁻¹) ≫ 𝟙 (SingleObj.star (Equiv.Perm (Fin n)))
    rw [Category.id_comp, Category.comp_id]
  rw [h]
  exact differenceFunctor_loop _ γ

/-! ## Connecting the shadow to the real braid functor

`braidGrpd (□n)` lands in `Braids = Σ m, SingleObj (Braid m)`, whose objects vary with the event
count.  `readPerm` collapses that onto the *fixed* `SingleObj (Perm (Fin n))` by reading each
braid's permutation transported to `Fin n`; the collapse is what lets the loop-killing
`differenceFunctor` mechanism (`cubeSh`) apply to the real functor. -/

/-- Conjugation of permutations along an equivalence, packaged as a monoid hom. -/
def permCongrHom {α β : Type*} (e : α ≃ β) : Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := Equiv.ext fun x => by simp [Equiv.permCongr_apply]
  map_mul' p q := Equiv.ext fun x => by simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

@[simp] theorem permCongrHom_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) :
    permCongrHom e σ = e.permCongr σ := rfl

/-- Read a braid on `a` strands as a permutation of `Fin n`: transported when `a = n`, trivial
otherwise (only the `a = n` fibre is hit by `braidGrpd (□n)`). -/
def braidPermHom (n a : ℕ) : Braid a →* Equiv.Perm (Fin n) :=
  if h : a = n then (permCongrHom (finCongr h)).comp (permHom a) else 1

theorem braidPermHom_apply_eq (n : ℕ) {a : ℕ} (h : a = n) (b : Braid a) :
    braidPermHom n a b = (finCongr h).permCongr (permHom a b) := by
  have hd : braidPermHom n a = (permCongrHom (finCongr h)).comp (permHom a) := dif_pos h
  rw [hd, MonoidHom.comp_apply, permCongrHom_apply]

/-- Collapse `𝔅` onto `SingleObj (Perm (Fin n))`, reading each braid's permutation transported to
`Fin n`. -/
def readPerm (n : ℕ) : Braids ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  CategoryTheory.Sigma.desc fun a =>
    SingleObj.mapHom (Braid a) (Equiv.Perm (Fin n)) (braidPermHom n a)

theorem readPerm_map_braidHom (n : ℕ) {a : ℕ} (b : Braid a) :
    (readPerm n).map (braidHom b) = braidPermHom n a b := rfl

theorem braidGrading_map_eq {K : BPSet} {x y : ConcCat K} (f : x ⟶ y) :
    (braidGrading K).map f
      = braidHom (ofPerm (evPerm' f)) ≫ eqToHom (congrArg strands (nEvents_eq f)) := rfl

/-- **Transport identity.**  The permutation shadow of a refinement is its event permutation, read
in the cube's fixed frame `Fin n`. -/
theorem cubeSh_map_eq_permCongr {x y : ConcCat (□n)} (f : x ⟶ y) (h : nEvents x = n) :
    (cubeSh n).map f = (finCongr h).permCongr (evPerm' f) := by
  apply Equiv.ext
  intro e
  rfl

/-- **The real braid grading, collapsed to `Fin n`, is the permutation shadow.** -/
theorem braidGrading_comp_readPerm (n : ℕ) :
    braidGrading (□n) ⋙ readPerm n = cubeSh n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y f => ?_
  have hcard : nEvents x = n := eventObj_card_cube x.chain
  have hid : (readPerm n).map (eqToHom (congrArg strands (nEvents_eq f))) = 𝟙 _ := by
    rw [eqToHom_map]; rfl
  rw [Functor.comp_map, braidGrading_map_eq]
  erw [Functor.map_comp, hid, Category.comp_id]
  change braidPermHom n (nEvents x) (ofPerm (evPerm' f)) = _
  rw [braidPermHom_apply_eq n hcard, permHom_ofPerm, ← cubeSh_map_eq_permCongr f hcard]
  rfl

/-- Read the braid wrapped inside an endomorphism of `strands a`. -/
def endBraid {a : ℕ} (f : strands a ⟶ strands a) : Braid a :=
  match f with
  | SigmaHom.mk b => b

@[simp] theorem braidHom_endBraid {a : ℕ} (f : strands a ⟶ strands a) :
    braidHom (endBraid f) = f := by
  cases f with
  | mk b => rfl

/-- Reading the braid off a composite reverses the order, matching `braidHom_comp`: `𝔅`'s fibre
`SingleObj (Braid a)` composes by `flip (· * ·)`. -/
theorem endBraid_comp {a : ℕ} (F G : strands a ⟶ strands a) :
    endBraid (F ≫ G) = endBraid G * endBraid F := by
  cases F with
  | mk b => cases G with
    | mk c => rfl

/-- **Feature 1 (purity): `braidGrpd (□n)` sends cube loops to pure braids.**  The permutation
underlying the braid of a loop is the identity — the loop's braid is pure. -/
theorem cube_braidGrpd_pure (n : ℕ) (x : ConcCat (□n))
    (γ : (FreeGroupoid.mk x : ConcGrpd (□n)) ⟶ FreeGroupoid.mk x) :
    permHom (nEvents x) (endBraid ((braidGrpd (□n)).map γ)) = 1 := by
  have hcard : nEvents x = n := eventObj_card_cube x.chain
  have hfun : braidGrpd (□n) ⋙ readPerm n = FreeGroupoid.lift (cubeSh n) := by
    change FreeGroupoid.lift (braidGrading (□n)) ⋙ readPerm n = FreeGroupoid.lift (cubeSh n)
    rw [← FreeGroupoid.lift_comp, braidGrading_comp_readPerm]
  have hloop : (readPerm n).map ((braidGrpd (□n)).map γ) = 𝟙 _ :=
    (show (readPerm n).map ((braidGrpd (□n)).map γ) = (FreeGroupoid.lift (cubeSh n)).map γ by
      rw [← Functor.comp_map, hfun]).trans (cubeSh_lift_loop γ)
  have hb : braidPermHom n (nEvents x) (endBraid ((braidGrpd (□n)).map γ)) = 1 :=
    calc braidPermHom n (nEvents x) (endBraid ((braidGrpd (□n)).map γ))
        = (readPerm n).map (braidHom (endBraid ((braidGrpd (□n)).map γ))) :=
          (readPerm_map_braidHom n _).symm
      _ = (readPerm n).map ((braidGrpd (□n)).map γ) :=
          congrArg (fun m => (readPerm n).map m) (braidHom_endBraid _)
      _ = 𝟙 _ := hloop
      _ = 1 := by rw [SingleObj.id_as_one]
  rw [braidPermHom_apply_eq n hcard] at hb
  have h1 : (finCongr hcard).permCongr (permHom (nEvents x) (endBraid ((braidGrpd (□n)).map γ)))
      = (finCongr hcard).permCongr 1 := by
    rw [Equiv.Perm.one_def, Equiv.permCongr_refl, ← Equiv.Perm.one_def]
    exact hb
  exact (finCongr hcard).permCongr.injective h1

/-! ## The codomain plumbing: automorphisms of `strands n` are the braids on `n` strands

`𝔅` is a groupoid, so every endomorphism of `strands n` is invertible; `endBraid` reads it off as a
braid.  `braidHom` is *anti*-multiplicative for `≫` (`braidHom_comp`), but the reversal cancels
against the reversed `Aut` product (`f * g = g ≫ f`), so this is a genuine group iso. -/

/-- **Automorphisms of `strands n` are the braids on `n` strands.** -/
@[simps] def autStrandsBraid (n : ℕ) : Aut (strands n) ≃* Braid n where
  toFun a := endBraid a.hom
  invFun b :=
    { hom := braidHom b
      inv := braidHom b⁻¹
      hom_inv_id := by rw [braidHom_comp, inv_mul_cancel]; rfl
      inv_hom_id := by rw [braidHom_comp, mul_inv_cancel]; rfl }
  left_inv a := Aut.ext (braidHom_endBraid a.hom)
  right_inv b := rfl
  map_mul' a b := by rw [Aut.Aut_mul_def, Iso.trans_hom, endBraid_comp]

/-! ## The concurrency braid group map `Φ`

`Φ x = concBraidHom n x` is the group homomorphism `braidGrpd (□n)` induces on the vertex group
`ConcBraid (□n) x = Aut (mk x)`: a loop of executions at `x` goes to the braid it traces on the
`nEvents x` events.  Feature 1 (purity) says its image lands in the pure braids
(`concBraidHom_mem_pure`); the remaining content of `Cubical-xhj.6` is that it is a bijection onto
`PureBraid (nEvents x)`. -/

/-- **The concurrency braid of a loop.**  The vertex-group map of `braidGrpd (□n)`. -/
def concBraidHom (n : ℕ) (x : ConcCat (□n)) :
    ConcBraid (□n) x →* Braid (nEvents x) :=
  (autStrandsBraid (nEvents x)).toMonoidHom.comp ((braidGrpd (□n)).mapAut (FreeGroupoid.mk x))

@[simp] theorem concBraidHom_apply (n : ℕ) (x : ConcCat (□n)) (a : ConcBraid (□n) x) :
    concBraidHom n x a = endBraid ((braidGrpd (□n)).map a.hom) := rfl

/-- **Feature 1, as a membership.**  `braidGrpd (□n)` sends every concurrency loop to a pure braid. -/
theorem concBraidHom_mem_pure (n : ℕ) (x : ConcCat (□n)) (a : ConcBraid (□n) x) :
    concBraidHom n x a ∈ PureBraid (nEvents x) := by
  rw [MonoidHom.mem_ker, concBraidHom_apply]
  exact cube_braidGrpd_pure n x a.hom

/-- **Feature 1, packaged.**  The concurrency braid group maps into the pure braids: the
codomain-restriction of `concBraidHom`. -/
def concPureBraidHom (n : ℕ) (x : ConcCat (□n)) :
    ConcBraid (□n) x →* PureBraid (nEvents x) :=
  (concBraidHom n x).codRestrict (PureBraid (nEvents x)) (concBraidHom_mem_pure n x)

/-! ## Surjectivity via the `Sₙ`-symmetry

`Pₙ` has no presentation, so hitting every pure braid *directly* has no handle.  Instead climb into
the extension where the target *is* presented (`Braid n = ⟨ofPerm (adjT i)⟩`): enlarge the
concurrency groupoid by the axis-relabelings — the `Sₙ` permuting the `n` coordinate axes of `□n`
— to `LabConc x`, and read a relabeling as its permutation braid `ofPerm σ`, a pure loop as
`concBraidHom`.  This gives a map of short exact sequences (`↪` kernel, `↠` cokernel):

```
        ConcBraid(□n) x  ↪   LabConc x   ↠   Sₙ
              │                  │             ║
   concPureBraidHom             Φ̃            id
              ▼                  ▼             ║
             Pₙ          ↪    Braid n    ↠    Sₙ
```

Right square: `Φ̃`'s permutation shadow is the axis-permutation (`permHom (Φ̃ g) = π g`).  Left
square: on the kernel `Φ̃` restricts to `concPureBraidHom`, which lands in `Pₙ` by purity
(`concBraidHom_mem_pure`).

**Surjectivity chase** — `Φ̃` onto + right map injective ⟹ `concPureBraidHom` onto:  for `p : Pₙ`,
write `p = Φ̃ g`; then `π g = id (π g) = permHom p = 1`, so `g ∈ ConcBraid(□n) x` and
`p = concPureBraidHom g`.  *No generator of `Pₙ` is ever named* — only `Pₙ = ker (permHom n)` and
`Braid n = ⟨ofPerm (adjT i)⟩`, each `σᵢ` hit by swapping two adjacent (hence concurrent) axes.

`Φ̃`'s well-definedness is the `Sₙ`-equivariance of `concBraidHom`
(`concBraidHom (σ • γ) = ofPerm σ * concBraidHom γ * (ofPerm σ)⁻¹`).  `LabConc ↠ Sₙ` needs `x` and
`σ • x` in one component — connectedness of `ConcCat (□n)`, provable since all `n` cube events are
mutually concurrent.  Injectivity then reduces to `Φ̃` injective (a presentation match against
`ArtinBraid`), `concPureBraidHom` being its restriction. -/

end CubeChains
