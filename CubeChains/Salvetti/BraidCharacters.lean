import CubeChains.Salvetti.BraidFunctor
import CubeChains.Salvetti.Braiding
import CubeChains.Schedule.EventLocalSystem

/-!
# Salvetti/BraidCharacters — the invariants of `braidFunctor` as its characters

Everything the concurrency groupoid knows about events is a character of the braid functor
`Φ = braidFunctor K n : ConcGrpdN K n ⥤ BraidGrpd n`:

* the **permutation part** of `Φ` is the event monodromy (`evMonodromy`, §A);
* the **writhe** — `salCross` on `Sal (braidCOM n)` pushed to `BraidCat n` — pulls back along `Ψ` to
  the *inversion number* of the event permutation (`writhe_braidPsi`, §B), and restricts to
  `salWind` on the pure (`σ = 1`) part;
* the **orientation character** `orSign` of `Sched K` is `sign ∘ evPerm` twisted by the frame
  coboundary comparing the lex order of events with the line's `evKey` order (`sign_evPerm`, §C);
* **purity ⟺ HDA** (§D): `HasGlobalEventNaming K` is *exactly* triviality of the event monodromy
  `ρ` of the local system `a ↦ EventObj a` on `Ch K` (`hasGlobalEventNaming_iff_monodromyTrivial`).

Gotcha: purity is a statement about **loops** (`evMonodromy_loop_eq_one_iff`), where the source and
target frames of `evPerm` coincide and cancel.  Demanding `evPerm f = 1` for *every* morphism is a
different — and much stronger — condition: it says `K` has no concurrency at all
(`forall_isRun_of_evPerm_one`, `not_forall_evPerm_eq_one_iff_hasGlobalEventNaming`).
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

/-! ## Groupoids of sets, named sets and frames

Three tiny groupoids.  They are the *targets* of the local systems below; their whole purpose is
that an automorphism in the last two is forced to be the identity, which is what turns "coherent
naming" into "trivial monodromy". -/

/-- Sets and bijections. -/
structure EvSet : Type 1 where
  /-- The underlying set. -/
  carrier : Type

instance : Groupoid EvSet where
  Hom X Y := X.carrier ≃ Y.carrier
  id _ := Equiv.refl _
  comp f g := f.trans g
  id_comp _ := Equiv.refl_trans _
  comp_id _ := Equiv.trans_refl _
  assoc _ _ _ := Equiv.trans_assoc _ _ _
  inv f := f.symm
  inv_comp f := f.symm_trans_self
  comp_inv f := f.self_trans_symm

theorem EvSet.inv_eq {X Y : EvSet} (u : X ⟶ Y) : CategoryTheory.inv u = u.symm :=
  IsIso.inv_eq_of_hom_inv_id (u.self_trans_symm)

/-- Sets with an injective naming in `σ`, and name-preserving bijections. -/
structure NamedSet (σ : Type) : Type 1 where
  /-- The underlying set. -/
  carrier : Type
  /-- The naming. -/
  name : carrier → σ
  /-- Distinct elements have distinct names. -/
  inj : Function.Injective name

instance (σ : Type) : Groupoid (NamedSet σ) where
  Hom X Y := { u : X.carrier ≃ Y.carrier // ∀ e, Y.name (u e) = X.name e }
  id _ := ⟨Equiv.refl _, fun _ => rfl⟩
  comp f g := ⟨f.1.trans g.1, fun e => by rw [Equiv.trans_apply, g.2, f.2]⟩
  id_comp _ := Subtype.ext (Equiv.refl_trans _)
  comp_id _ := Subtype.ext (Equiv.trans_refl _)
  assoc _ _ _ := Subtype.ext (Equiv.trans_assoc _ _ _)
  inv f := ⟨f.1.symm, fun e => by
    have h := f.2 (f.1.symm e)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm⟩
  inv_comp f := Subtype.ext f.1.symm_trans_self
  comp_inv f := Subtype.ext f.1.self_trans_symm

/-- A named set has no nontrivial automorphisms: names pin every element. -/
theorem NamedSet.aut_eq_id {σ : Type} {X : NamedSet σ} (u : X ⟶ X) : u = 𝟙 X :=
  Subtype.ext (Equiv.ext fun e => X.inj (u.2 e))

/-- Forget the names. -/
def NamedSet.forget (σ : Type) : NamedSet σ ⥤ EvSet where
  obj X := ⟨X.carrier⟩
  map f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Injective `Fin n`-frames in a naming set `σ`, and the permutations relating them. -/
structure Frame (σ : Type) (n : ℕ) : Type where
  /-- The name of the `k`-th element of the frame. -/
  name : Fin n → σ
  /-- Distinct slots have distinct names. -/
  inj : Function.Injective name

instance (σ : Type) (n : ℕ) : Groupoid (Frame σ n) where
  Hom u v := { π : Equiv.Perm (Fin n) // ∀ k, v.name (π k) = u.name k }
  id _ := ⟨1, fun _ => rfl⟩
  comp f g := ⟨g.1 * f.1, fun k => by rw [Equiv.Perm.mul_apply, g.2, f.2]⟩
  id_comp _ := Subtype.ext (mul_one _)
  comp_id _ := Subtype.ext (one_mul _)
  assoc _ _ _ := Subtype.ext (mul_assoc _ _ _).symm
  inv f := ⟨f.1⁻¹, fun k => by
    have h := f.2 (f.1⁻¹ k)
    rw [show (f.1 : Equiv.Perm (Fin n)) (f.1⁻¹ k) = k by simp] at h
    exact h.symm⟩
  inv_comp f := Subtype.ext (mul_inv_cancel _)
  comp_inv f := Subtype.ext (inv_mul_cancel _)

/-- A frame has no nontrivial automorphisms. -/
theorem Frame.aut_eq_one {σ : Type} {n : ℕ} {u : Frame σ n} (π : u ⟶ u) : π.1 = 1 :=
  Equiv.ext fun k => u.inj (π.2 k)

/-- The permutation underlying a frame change. -/
def Frame.forget (σ : Type) (n : ℕ) : Frame σ n ⥤ SingleObj (Equiv.Perm (Fin n)) where
  obj _ := SingleObj.star _
  map f := f.1
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## §A The permutation part of the braid functor is the event monodromy -/

variable {K : BPSet} {n : ℕ}

/-- The **event monodromy** on the concurrency *groupoid*: the permutation part of the braid
functor, read on zigzags. -/
noncomputable def evMonodromy (K : BPSet) (n : ℕ) :
    ConcGrpdN K n ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  FreeGroupoid.lift (eventMonodromy K n)

theorem eventMonodromy_eq (K : BPSet) (n : ℕ) :
    eventMonodromy K n = braidPsi K n ⋙ braidPermFunctor n := rfl

/-- **`Φ` factors the event monodromy**: the underlying permutation of the braid of a zigzag is the
`evKey`-frame monodromy. -/
theorem braidFunctor_comp_braidPerm (K : BPSet) (n : ℕ) :
    braidFunctor K n ⋙ FreeGroupoid.lift (braidPermFunctor n) = evMonodromy K n :=
  FreeGroupoid.lift_unique (eventMonodromy K n) _ (by
    rw [braidFunctor, ← Functor.assoc, FreeGroupoid.of_comp_map, Functor.assoc,
      FreeGroupoid.lift_spec]
    rfl)

/-! ## §D The event monodromy and the naming property

The event local system `a ↦ EventObj a`, `f ↦ eventEquiv f` on `Ch K` sends every morphism to a
bijection (`eventMap_bijective`, for every `K`), so it extends to the free groupoid: a **zigzag** of
refinements induces a permutation of a chain's events, the **monodromy** `ρ`. -/

/-- The **event local system** of `K`: chains, their events, and the refinement bijections. -/
noncomputable def eventSystem (K : BPSet) : Ch K ⥤ EvSet where
  obj a := ⟨EventObj a⟩
  map f := eventEquiv f
  map_id a := eventEquiv_id a
  map_comp f g := eventEquiv_comp f g

/-- The **event monodromy** `ρ` of `K`: the event local system on zigzags of refinements. -/
noncomputable def eventRho (K : BPSet) : FreeGroupoid (Ch K) ⥤ EvSet :=
  FreeGroupoid.lift (eventSystem K)

/-- The permutation of a chain's events along a zigzag of refinements. -/
noncomputable def rhoMap {a b : Ch K}
    (γ : (FreeGroupoid.mk a : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk b) :
    EventObj a ≃ EventObj b :=
  (eventRho K).map γ

@[simp] theorem rhoMap_homMk {a b : Ch K} (f : a ⟶ b) :
    rhoMap (FreeGroupoid.homMk f) = eventEquiv f :=
  FreeGroupoid.lift_map_homMk (eventSystem K) f

@[simp] theorem rhoMap_id (a : Ch K) :
    rhoMap (𝟙 (FreeGroupoid.mk a : FreeGroupoid (Ch K))) = Equiv.refl (EventObj a) :=
  (eventRho K).map_id _

theorem rhoMap_comp {a b c : Ch K}
    (γ : (FreeGroupoid.mk a : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk b)
    (δ : (FreeGroupoid.mk b : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk c) :
    rhoMap (γ ≫ δ) = (rhoMap γ).trans (rhoMap δ) :=
  (eventRho K).map_comp γ δ

theorem rhoMap_inv {a b : Ch K}
    (γ : (FreeGroupoid.mk a : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk b) :
    rhoMap (CategoryTheory.inv γ) = (rhoMap γ).symm := by
  change (eventRho K).map (CategoryTheory.inv γ) = _
  rw [Functor.map_inv, EvSet.inv_eq]
  rfl

/-- **Trivial monodromy**: every zigzag of refinements from a chain to itself permutes its events
trivially.  (`ρ = 1`.) -/
def EventMonodromyTrivial (K : BPSet) : Prop :=
  ∀ (a : Ch K) (γ : (FreeGroupoid.mk a : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk a),
    rhoMap γ = Equiv.refl (EventObj a)

/-- A chain of `EventRel`-steps is a zigzag: it is realised by a morphism of the free groupoid,
transporting the events along. -/
theorem exists_grpd_hom_of_eqvGen {p q : Σ a : Ch K, EventObj a}
    (h : Relation.EqvGen (EventRel K) p q) :
    ∃ γ : (FreeGroupoid.mk p.1 : FreeGroupoid (Ch K)) ⟶ FreeGroupoid.mk q.1,
      rhoMap γ p.2 = q.2 := by
  induction h with
  | rel p q hpq =>
      obtain ⟨f, hf⟩ := hpq
      exact ⟨FreeGroupoid.homMk f, by rw [rhoMap_homMk]; exact hf⟩
  | refl p => exact ⟨𝟙 _, by rw [rhoMap_id]; rfl⟩
  | symm p q _ ih =>
      obtain ⟨γ, hγ⟩ := ih
      refine ⟨CategoryTheory.inv γ, ?_⟩
      rw [rhoMap_inv, ← hγ]
      exact (rhoMap γ).symm_apply_apply p.2
  | trans p q r _ _ ih₁ ih₂ =>
      obtain ⟨γ₁, h₁⟩ := ih₁
      obtain ⟨γ₂, h₂⟩ := ih₂
      refine ⟨γ₁ ≫ γ₂, ?_⟩
      rw [rhoMap_comp, Equiv.trans_apply, h₁, h₂]

/-- The event local system, with a coherent naming carried along. -/
noncomputable def namedEventSystem (K : BPSet) {σ : Type}
    (name : (Σ a : Ch K, EventObj a) → σ)
    (hcoh : ∀ {a b : Ch K} (f : a ⟶ b) (e : EventObj a), name ⟨b, eventMap f e⟩ = name ⟨a, e⟩)
    (hinj : ∀ a : Ch K, Function.Injective fun e : EventObj a => name ⟨a, e⟩) :
    Ch K ⥤ NamedSet σ where
  obj a := ⟨EventObj a, fun e => name ⟨a, e⟩, hinj a⟩
  map f := ⟨eventEquiv f, fun e => hcoh f e⟩
  map_id a := Subtype.ext (eventEquiv_id a)
  map_comp f g := Subtype.ext (eventEquiv_comp f g)

/-- **Purity ⟺ HDA, at the level of chains.**  A globally coherent event naming exists **iff** the
event monodromy is trivial: `ρ` is the obstruction, and the canonical quotient folds two events of a
chain exactly when some zigzag of refinements moves one to the other. -/
theorem hasGlobalEventNaming_iff_monodromyTrivial (K : BPSet) :
    HasGlobalEventNaming K ↔ EventMonodromyTrivial K := by
  constructor
  · -- a naming forces every loop to preserve names, hence to be the identity
    rintro ⟨σ, name, hcoh, hinj⟩ a γ
    have hF : FreeGroupoid.lift (namedEventSystem K name hcoh hinj) ⋙ NamedSet.forget σ
        = eventRho K :=
      FreeGroupoid.lift_unique (eventSystem K) _ (by
        rw [← Functor.assoc, FreeGroupoid.lift_spec]; rfl)
    have h2 : ((FreeGroupoid.lift (namedEventSystem K name hcoh hinj)).map γ).1 = rhoMap γ :=
      Functor.congr_hom hF γ
    have hloop := NamedSet.aut_eq_id
      ((FreeGroupoid.lift (namedEventSystem K name hcoh hinj)).map γ)
    change rhoMap γ = Equiv.refl _
    rw [← h2, hloop]
    rfl
  · -- trivial monodromy ⟹ the canonical quotient is fibrewise injective
    intro htriv
    refine (hasGlobalEventNaming_iff K).mpr ?_
    intro a e e' he
    obtain ⟨γ, hγ⟩ := exists_grpd_hom_of_eqvGen (Quot.eqvGen_exact
      (show canonicalName (⟨a, e⟩ : Σ a : Ch K, EventObj a) = canonicalName ⟨a, e'⟩ from he))
    rw [htriv a γ] at hγ
    exact hγ

/-! ### Purity of the braid functor

A naming gives every execution a frame-independent name for each event, so a **loop** of the
concurrency groupoid must fix every event: its braid is pure. -/

/-- The `evKey`-frame of an execution, named by a coherent event naming. -/
noncomputable def evFrame {σ : Type}
    (name : (Σ a : Ch K, EventObj a) → σ)
    (hinj : ∀ a : Ch K, Function.Injective fun e : EventObj a => name ⟨a, e⟩)
    (x : ConcCatN K n) : Frame σ n where
  name k := name ⟨x.obj.chain, (evIdx x).symm k⟩
  inj := fun _ _ h => (evIdx x).symm.injective (hinj _ h)

/-- The frame local system of `K`: an execution goes to its named `evKey`-frame, a refinement to its
event permutation. -/
noncomputable def frameSystem (K : BPSet) (n : ℕ) {σ : Type}
    (name : (Σ a : Ch K, EventObj a) → σ)
    (hcoh : ∀ {a b : Ch K} (f : a ⟶ b) (e : EventObj a), name ⟨b, eventMap f e⟩ = name ⟨a, e⟩)
    (hinj : ∀ a : Ch K, Function.Injective fun e : EventObj a => name ⟨a, e⟩) :
    ConcCatN K n ⥤ Frame σ n where
  obj x := evFrame name hinj x
  map {x y} f := ⟨evPerm f, fun k => by
    change name ⟨y.obj.chain, (evIdx y).symm (evPerm f k)⟩
      = name ⟨x.obj.chain, (evIdx x).symm k⟩
    have hu : (evIdx y).symm (evPerm f k)
        = (eventEquiv (concRefine f)).symm ((evIdx x).symm k) :=
      (evIdx y).symm_apply_apply _
    rw [hu]
    have h := hcoh (concRefine f) ((eventEquiv (concRefine f)).symm ((evIdx x).symm k))
    rw [show eventMap (concRefine f) ((eventEquiv (concRefine f)).symm ((evIdx x).symm k))
        = (evIdx x).symm k from (eventEquiv (concRefine f)).apply_symm_apply _] at h
    exact h.symm⟩
  map_id x := Subtype.ext (evPerm_id x)
  map_comp f g := Subtype.ext (evPerm_comp f g)

/-- **The braid of a loop is pure, for an HDA.**  If `K` has a globally coherent event naming, then
the event monodromy of every zigzag from an execution to itself is trivial: the image of
`braidFunctor` on the vertex groups lies in the pure braid group. -/
theorem evMonodromy_loop_eq_one (h : HasGlobalEventNaming K) (x : ConcCatN K n)
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x) :
    (evMonodromy K n).map γ = 𝟙 _ := by
  obtain ⟨σ, name, hcoh, hinj⟩ := h
  have hF : FreeGroupoid.lift (frameSystem K n name hcoh hinj) ⋙ Frame.forget σ n
      = evMonodromy K n :=
    FreeGroupoid.lift_unique (eventMonodromy K n) _ (by
      rw [← Functor.assoc, FreeGroupoid.lift_spec]; rfl)
  have h2 : ((FreeGroupoid.lift (frameSystem K n name hcoh hinj)).map γ).1
      = (evMonodromy K n).map γ := Functor.congr_hom hF γ
  rw [← h2, Frame.aut_eq_one]
  rfl

/-- **Purity of the braid functor for an HDA**: every vertex-group braid of `Φ` has trivial
underlying permutation. -/
theorem braidFunctor_pure (h : HasGlobalEventNaming K) (x : ConcCatN K n)
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x) :
    (FreeGroupoid.lift (braidPermFunctor n)).map ((braidFunctor K n).map γ) = 𝟙 _ := by
  have := evMonodromy_loop_eq_one h x γ
  rwa [← braidFunctor_comp_braidPerm K n] at this

/-! ### On a loop the frames cancel

`evPerm f` reads the event bijection of `f` through *two* frames (`evIdx x`, `evIdx y`).  On a loop
the two frames are the same, so they cancel: the loop's `evPerm` is the raw event monodromy of the
loop, conjugated by the one frame.  Purity is therefore frame-independent. -/

/-- Sets with a `Fin n`-frame, and bijections (which need not respect the frames). -/
structure EvFrame (n : ℕ) : Type 1 where
  /-- The underlying set. -/
  carrier : Type
  /-- The frame. -/
  frame : carrier ≃ Fin n

instance (n : ℕ) : Groupoid (EvFrame n) where
  Hom X Y := X.carrier ≃ Y.carrier
  id _ := Equiv.refl _
  comp f g := f.trans g
  id_comp _ := Equiv.refl_trans _
  comp_id _ := Equiv.trans_refl _
  assoc _ _ _ := Equiv.trans_assoc _ _ _
  inv f := f.symm
  inv_comp f := f.symm_trans_self
  comp_inv f := f.self_trans_symm

/-- A frame-forgetting morphism, as a plain bijection. -/
def EvFrame.toEquiv {n : ℕ} {X Y : EvFrame n} (u : X ⟶ Y) : X.carrier ≃ Y.carrier := u

/-- Read a bijection through the two frames. -/
def EvFrame.toPerm (n : ℕ) : EvFrame n ⥤ SingleObj (Equiv.Perm (Fin n)) where
  obj _ := SingleObj.star _
  map {X Y} u := (X.frame.symm.trans (EvFrame.toEquiv u)).trans Y.frame
  map_id X := by
    apply Equiv.ext
    intro k
    change X.frame (X.frame.symm k) = k
    exact X.frame.apply_symm_apply k
  map_comp {X Y Z} u v := by
    apply Equiv.ext
    intro k
    change Z.frame (EvFrame.toEquiv v (EvFrame.toEquiv u (X.frame.symm k)))
      = Z.frame (EvFrame.toEquiv v (Y.frame.symm (Y.frame (EvFrame.toEquiv u (X.frame.symm k)))))
    rw [Equiv.symm_apply_apply]

/-- Forget the frame. -/
def EvFrame.forget (n : ℕ) : EvFrame n ⥤ EvSet where
  obj X := ⟨X.carrier⟩
  map u := u
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The framed event local system of the executions with `n` events. -/
noncomputable def concFrameSystem (K : BPSet) (n : ℕ) : ConcCatN K n ⥤ EvFrame n where
  obj x := ⟨EventObj x.obj.chain, evIdx x⟩
  map f := (eventEquiv (concRefine f)).symm
  map_id x := by
    change (eventEquiv (concRefine (𝟙 x))).symm = Equiv.refl _
    rw [concRefine_id, eventEquiv_id]
    rfl
  map_comp {x y z} f g := by
    change (eventEquiv (concRefine (f ≫ g))).symm
      = (eventEquiv (concRefine f)).symm.trans (eventEquiv (concRefine g)).symm
    rw [concRefine_comp, eventEquiv_comp]
    rfl

/-- The **event monodromy of an execution zigzag**: the permutation of the events of the underlying
chain, frame-free. -/
noncomputable def concRho (K : BPSet) (n : ℕ) : ConcGrpdN K n ⥤ EvFrame n :=
  FreeGroupoid.lift (concFrameSystem K n)

/-- The event permutation of an execution zigzag, frame-free. -/
noncomputable def concRhoMap {x y : ConcCatN K n}
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk y) :
    EventObj x.obj.chain ≃ EventObj y.obj.chain :=
  (concRho K n).map γ

theorem evMonodromy_eq_toPerm (K : BPSet) (n : ℕ) :
    concRho K n ⋙ EvFrame.toPerm n = evMonodromy K n :=
  FreeGroupoid.lift_unique (eventMonodromy K n) _ (by
    rw [concRho, ← Functor.assoc, FreeGroupoid.lift_spec]; rfl)

/-- **The frames cancel on a loop.**  A loop's braid is pure exactly when the loop's event
monodromy (the composite of the `eventMap` bijections around it) is trivial — the `evKey` frames of
`evPerm` enter only through a conjugation. -/
theorem evMonodromy_loop_eq_one_iff (x : ConcCatN K n)
    (γ : (FreeGroupoid.mk x : ConcGrpdN K n) ⟶ FreeGroupoid.mk x) :
    (evMonodromy K n).map γ = 𝟙 _ ↔ concRhoMap γ = Equiv.refl (EventObj x.obj.chain) := by
  have h2 : (((evIdx x).symm.trans ((concRhoMap γ).trans (evIdx x))) : Equiv.Perm (Fin n))
      = (evMonodromy K n).map γ :=
    Functor.congr_hom (evMonodromy_eq_toPerm K n) γ
  rw [← h2]
  constructor
  · intro h
    apply Equiv.ext
    intro e
    have hk := congrArg (fun p : Equiv.Perm (Fin n) => p (evIdx x e)) h
    simp only [SingleObj.id_as_one, Equiv.Perm.coe_one, id_eq, Equiv.trans_apply,
      Equiv.symm_apply_apply] at hk
    exact (evIdx x).injective hk
  · intro h
    rw [h]
    apply Equiv.ext
    intro k
    change (evIdx x) ((evIdx x).symm k) = _
    rw [Equiv.apply_symm_apply]
    rfl

/-! ## §D′ `evPerm ≡ 1` is not the naming property — it is the absence of concurrency

A refinement may split a bead in an order the line disagrees with; then `evPerm f ≠ 1` no matter how
coherently the events are named.  Demanding `evPerm f = 1` for *every* morphism therefore forces
every chain to be a run (every bead an edge): `K` has no concurrency at all. -/

/-- The chamber ordering the directions by their index. -/
def Chamber.std (d : ℕ) : Chamber d := ⟨(· < ·), inferInstance⟩

/-- The chamber ordering the directions by their index, reversed. -/
def Chamber.rev (d : ℕ) : Chamber d := ⟨(· > ·), inferInstance⟩

/-- A cube of dimension `≥ 2` has at least two chambers. -/
theorem Chamber.std_ne_rev {d : ℕ} (hd : 2 ≤ d) : Chamber.std d ≠ Chamber.rev d := by
  intro h
  have h0 : (0 : ℕ) < d := by omega
  have h1 : (1 : ℕ) < d := by omega
  have hij : (⟨0, h0⟩ : Fin d) < ⟨1, h1⟩ := by
    change (0 : ℕ) < 1
    omega
  have hp : ((⟨0, h0⟩ : Fin d) < ⟨1, h1⟩) = ((⟨1, h1⟩ : Fin d) < ⟨0, h0⟩) :=
    congrFun (congrFun (congrArg Chamber.lt h) ⟨0, h0⟩) ⟨1, h1⟩
  have hji : (1 : ℕ) < 0 := hp ▸ hij
  omega

/-- A chain with a unique line is a run: a bead of dimension `≥ 2` carries two chambers. -/
theorem isRun_of_linesObj_subsingleton {a : Ch K} (h : Subsingleton (LinesObj a)) : IsRun a := by
  intro i
  by_contra hne
  have hpos : 0 < ChainCat.beadDim a i := (a.dims.get i).pos
  have hd : 2 ≤ ChainCat.beadDim a i := by omega
  have hL : (fun j => Chamber.std (ChainCat.beadDim a j))
      = (fun j => Chamber.rev (ChainCat.beadDim a j)) := h.elim _ _
  exact Chamber.std_ne_rev hd (congrFun hL i)

/-- The events of an execution, listed by the `evKey` frame (unfolded form of `evPerm`). -/
theorem evPerm_apply {x y : ConcCatN K n} (f : x ⟶ y) (k : Fin n) :
    evPerm f k = evIdx y ((eventEquiv (concRefine f)).symm ((evIdx x).symm k)) := rfl

/-- `evPerm f = 1` says exactly that the two `evKey` frames rank matched events alike. -/
theorem evIdx_eventMap_of_evPerm_one {x y : ConcCatN K n} (f : x ⟶ y) (hf : evPerm f = 1)
    (u : EventObj y.obj.chain) :
    evIdx y u = evIdx x (eventMap (concRefine f) u) := by
  set e := eventMap (concRefine f) u with he
  have h1 : evPerm f (evIdx x e) = evIdx x e := by rw [hf]; rfl
  rw [evPerm_apply, Equiv.symm_apply_apply] at h1
  rw [← h1, he]
  exact congrArg (evIdx y) ((eventEquiv (concRefine f)).symm_apply_apply u).symm

/-- In a run, the `evKey` order is the bead order. -/
theorem evKey_runLine_lt {b : Ch K} (hb : IsRun b) {u u' : EventObj b}
    (h : (u.1 : ℕ) < (u'.1 : ℕ)) : evKey (runLine b hb) u < evKey (runLine b hb) u' := by
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- Two events of one bead are `evKey`-ordered by that bead's chamber. -/
theorem evKey_same_bead_lt_iff {b : Ch K} (L : LinesObj b) (i : ChainCat.Bead b)
    (p q : Fin (ChainCat.beadDim b i)) :
    evKey L ⟨i, p⟩ < evKey L ⟨i, q⟩ ↔ (L i).lt p q := by
  rw [evKey, evKey, Prod.Lex.toLex_lt_toLex, ← chamberRank_lt_iff]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (lt_irrefl _)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-- `(a, L)` as an execution with `card (EventObj a)` events. -/
def execN {a : Ch K} (L : LinesObj a) : ConcCatN K (Fintype.card (EventObj a)) :=
  ⟨⟨op a, L⟩, rfl⟩

/-- The sequentialization of the line `L'` as an execution with the same events. -/
noncomputable def seqExecN {a : Ch K} (L' : LinesObj a) :
    ConcCatN K (Fintype.card (EventObj a)) :=
  ⟨runExec (seqChain L') (seqChain_isRun L'), card_eventObj_eq_of_hom (seqRefine L')⟩

/-- The execution `(a, L)` mapped into the sequentialization of a **different** line `L'`: the
refinement follows `L'`'s order of the events, which `L` need not agree with.  The target's line is
forced (a run has only one). -/
noncomputable def seqHomN {a : Ch K} (L L' : LinesObj a) : execN L ⟶ seqExecN L' :=
  ObjectProperty.homMk
    ⟨(seqRefine L').op, @Subsingleton.elim _ (linesObj_subsingleton (seqChain_isRun L')) _ _⟩

theorem concRefine_seqHomN {a : Ch K} (L L' : LinesObj a) :
    concRefine (seqHomN L L') = seqRefine L' := rfl

/-- **Trivial event permutations ⟹ unique lines.**  Sequentialize along `L'` and read the result in
the frame of `L`: `evPerm = 1` forces the two lines to order the events alike, i.e. `L = L'`. -/
theorem linesObj_subsingleton_of_evPerm_one
    (h : ∀ (m : ℕ) (x y : ConcCatN K m) (f : x ⟶ y), evPerm f = 1) (a : Ch K) :
    Subsingleton (LinesObj a) := by
  refine ⟨fun L L' => ?_⟩
  -- the two frames rank matched events alike
  have key0 := evIdx_eventMap_of_evPerm_one (seqHomN L L') (h _ _ _ (seqHomN L L'))
  have key : ∀ u : EventObj (seqChain L'),
      evIdx (seqExecN L') u = evIdx (execN L) (eventMap (seqRefine L') u) := fun u => key0 u
  -- the bead of the `L'`-sequentialization is the `L'`-rank of the event
  have hbeta : ∀ u : EventObj (seqChain L'),
      keyRank (evKey L') (eventMap (seqRefine L') u) = ((u.1 : Fin _) : ℕ) := by
    intro u
    have hb := beta_eventMap (seqBeta L') (seqBeta_surjective L') (seqBeta_mono L') u
    simpa [seqBeta] using hb
  -- `L'`-order ⟹ `L`-order
  have hmono : ∀ e e' : EventObj a, evKey L' e < evKey L' e' → evKey L e < evKey L e' := by
    intro e e' hlt
    obtain ⟨u, rfl⟩ : ∃ u : EventObj (seqChain L'), eventMap (seqRefine L') u = e :=
      ⟨(eventEquiv (seqRefine L')).symm e, (eventEquiv (seqRefine L')).apply_symm_apply e⟩
    obtain ⟨u', rfl⟩ : ∃ u' : EventObj (seqChain L'), eventMap (seqRefine L') u' = e' :=
      ⟨(eventEquiv (seqRefine L')).symm e', (eventEquiv (seqRefine L')).apply_symm_apply e'⟩
    have h1 : ((u.1 : Fin _) : ℕ) < ((u'.1 : Fin _) : ℕ) := by
      rw [← hbeta u, ← hbeta u']
      exact keyRank_strictMono (evKey L') hlt
    have h3 : evIdx (seqExecN L') u < evIdx (seqExecN L') u' :=
      (evIdx_lt_iff (seqExecN L') u u').mpr (evKey_runLine_lt (seqChain_isRun L') h1)
    rw [key u, key u'] at h3
    exact (evIdx_lt_iff (execN L) _ _).mp h3
  have hiff : ∀ e e' : EventObj a, evKey L' e < evKey L' e' ↔ evKey L e < evKey L e' := by
    intro e e'
    refine ⟨hmono e e', fun hlt => ?_⟩
    rcases lt_trichotomy (evKey L' e) (evKey L' e') with h1 | h1 | h1
    · exact h1
    · exact absurd (congrArg (evKey L) (evKey_injective L' h1)) (ne_of_lt hlt)
    · exact absurd (hmono e' e h1) (asymm hlt)
  -- the two lines order every bead alike, so they are equal
  funext i
  apply Chamber.ext
  funext p q
  refine propext ?_
  calc (L i).lt p q
      ↔ evKey L (⟨i, p⟩ : EventObj a) < evKey L ⟨i, q⟩ := (evKey_same_bead_lt_iff L i p q).symm
    _ ↔ evKey L' (⟨i, p⟩ : EventObj a) < evKey L' ⟨i, q⟩ := (hiff ⟨i, p⟩ ⟨i, q⟩).symm
    _ ↔ (L' i).lt p q := evKey_same_bead_lt_iff L' i p q

/-- **`evPerm ≡ 1` means no concurrency.**  If every morphism of every `ConcCatN K m` has trivial
event permutation, then every chain of `K` is a run: no bead ever fires two events at once. -/
theorem forall_isRun_of_evPerm_one
    (h : ∀ (m : ℕ) (x y : ConcCatN K m) (f : x ⟶ y), evPerm f = 1) (a : Ch K) : IsRun a :=
  isRun_of_linesObj_subsingleton (linesObj_subsingleton_of_evPerm_one h a)

/-! ### The witness: `□ⁿ` names its events, and runs the whole cube at once -/

/-- The one-block partition of the coordinates of `□ⁿ`. -/
theorem cubeTop_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (fun _ : Fin n => (0 : Fin 1)) :=
  fun _ => ⟨⟨0, hn⟩, Subsingleton.elim _ _⟩

/-- The single bead of the all-at-once chain: the top cell of `□ⁿ`. -/
noncomputable def cubeTopCubes (n : ℕ) (hn : 0 < n) : List (Σ m : ℕ+, (□n).cells (m : ℕ)) :=
  [bead (fun _ : Fin n => (0 : Fin 1)) (cubeTop_surjective hn) 0]

theorem cubeTopCubes_isChain (n : ℕ) (hn : 0 < n) :
    IsCubeChain (□n).init (cubeTopCubes n hn) (□n).final :=
  ⟨(vertex₀_blockCell _ _).trans (juncVertex_zero _),
    (vertex₁_blockCell _ _).trans (juncVertex_top _ (fun p => by simp))⟩

/-- The dimension sequence of the all-at-once chain (a single bead of dimension `n`).  Gotcha: this
must be a *named* definition — inlining it into the chain below makes the elaborator unfold the
wedge pushout while checking the classifying map's type, and it never finishes. -/
noncomputable def cubeTopDims (n : ℕ) (hn : 0 < n) : List ℕ+ :=
  List.map (fun x ↦ x.fst) (cubeTopCubes n hn)

/-- The classifying map of the all-at-once chain. -/
noncomputable def cubeTopMap (n : ℕ) (hn : 0 < n) : ⋁(cubeTopDims n hn) ⟶ □n :=
  wedgeDescHom (cubeTopCubes n hn)
    (wedgeDesc (□n).init (□n).final (cubeTopCubes n hn) (cubeTopCubes_isChain n hn))

/-- The **all-at-once chain** of `□ⁿ`: a single bead, the top cell — the `n` events fire
concurrently. -/
noncomputable def cubeTopChain (n : ℕ) (hn : 0 < n) : Ch (□n) :=
  ChainCat.Obj.mk (cubeTopDims n hn) (cubeTopMap n hn)

theorem cubeTopChain_dims (n : ℕ) (hn : 0 < n) :
    (cubeTopChain n hn).dims
      = [(bead (fun _ : Fin n => (0 : Fin 1)) (cubeTop_surjective hn) 0).1] := rfl

/-- The all-at-once chain of `□ⁿ` is not a run as soon as `n ≥ 2`. -/
theorem cubeTopChain_not_isRun {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n) :
    ¬ IsRun (cubeTopChain n hn) := by
  intro hrun
  have h0 : (0 : ℕ) < (cubeTopChain n hn).dims.length := by
    rw [cubeTopChain_dims]; norm_num
  have hdim : ((cubeTopChain n hn).dims.get ⟨0, h0⟩ : ℕ) = 1 := hrun ⟨0, h0⟩
  have hval : ((cubeTopChain n hn).dims.get ⟨0, h0⟩ : ℕ) = n := by
    change (Finset.univ.filter (fun p : Fin n => (fun _ : Fin n => (0 : Fin 1)) p = 0)).card = n
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
  omega

/-- **The literal reading of "purity ⟺ HDA" is FALSE.**  `evPerm f = 1` for every morphism is not
the naming property: `□²` names its events globally (`cube_hasGlobalEventNaming`) yet runs both of
them at once (`cubeTopChain`), and a refinement splitting that bead against the line has
`evPerm ≠ 1`.  Purity must be read on **loops** (`evMonodromy_loop_eq_one`). -/
theorem not_forall_evPerm_eq_one_iff_hasGlobalEventNaming :
    ¬ ∀ K : BPSet,
      (∀ (m : ℕ) (x y : ConcCatN K m) (f : x ⟶ y), evPerm f = 1) ↔ HasGlobalEventNaming K := by
  intro hyp
  have hev := (hyp (□2)).mpr (cube_hasGlobalEventNaming 2)
  exact cubeTopChain_not_isRun (by norm_num) (by norm_num)
    (forall_isRun_of_evPerm_one hev (cubeTopChain 2 (by norm_num)))

/-! ## §C `orSign` and `sign ∘ evPerm` are cohomologous

`orSign` (`Schedule/Orientation`) compares the **lex** orders of the events (bead, then coordinate);
`evPerm` compares the **`evKey`** orders (bead, then chamber rank).  They differ by the per-object
sign `frameSign` comparing the two orders — a coboundary, so the two cocycles are one class. -/

/-- The line's order on the events of an execution (`evKey`: bead, then the chamber's rank). -/
@[reducible] noncomputable def evKeyOrder (x : ConcCatN K n) : LinearOrder (EventObj x.obj.chain) :=
  LinearOrder.lift' (evKey x.obj.line) (evKey_injective _)

/-- `evIdx` is the monotone enumeration of the `evKey` order. -/
theorem monoEquivOfFin_evKey (x : ConcCatN K n) :
    (@monoEquivOfFin (EventObj x.obj.chain) _ (evKeyOrder x) n x.property).toEquiv
      = (evIdx x).symm := by
  letI := evKeyOrder x
  have hlt : ∀ k l : Fin n,
      evKey x.obj.line ((evIdx x).symm k) < evKey x.obj.line ((evIdx x).symm l) ↔ k < l := by
    intro k l
    rw [← evIdx_lt_iff x, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hmono : ∀ k l : Fin n, (evIdx x).symm k ≤ (evIdx x).symm l ↔ k ≤ l := by
    intro k l
    constructor
    · intro h
      by_contra hkl
      exact absurd ((hlt l k).mpr (not_le.mp hkl)) (not_lt.mpr h)
    · intro h
      by_contra hkl
      exact absurd ((hlt l k).mp (not_le.mp hkl)) (not_lt.mpr h)
  let E : Fin n ≃o EventObj x.obj.chain := ⟨(evIdx x).symm, fun {k l} => hmono k l⟩
  exact congrArg (fun e : Fin n ≃o EventObj x.obj.chain => e.toEquiv)
    (Subsingleton.elim (@monoEquivOfFin (EventObj x.obj.chain) _ (evKeyOrder x) n x.property) E)

theorem ordPerm_evKey (x y : ConcCatN K n) (u : EventObj x.obj.chain ≃ EventObj y.obj.chain) :
    ordPerm (evKeyOrder x) (evKeyOrder y) x.property y.property u
      = ((evIdx x).symm.trans u).trans (evIdx y) := by
  letI := evKeyOrder y
  have hy : (@monoEquivOfFin (EventObj y.obj.chain) _ (evKeyOrder y) n y.property).symm.toEquiv
      = evIdx y := by
    have h := congrArg Equiv.symm (monoEquivOfFin_evKey y)
    rw [Equiv.symm_symm] at h
    exact h
  rw [ordPerm, monoEquivOfFin_evKey x, hy, Equiv.trans_assoc]

/-- The event permutation *is* the `evKey`-order sign datum of the event bijection. -/
theorem evPerm_eq_ordPerm {x y : ConcCatN K n} (f : x ⟶ y) :
    evPerm f = ordPerm (evKeyOrder x) (evKeyOrder y) x.property y.property
      (eventEquiv (concRefine f)).symm :=
  (ordPerm_evKey x y _).symm

/-- The sign of a bijection of finite linear orders is unchanged by inverting it (with the two
orders swapped): `ℤˣ` has exponent `2`. -/
theorem ordSign_symm {α β : Type*} [Fintype α] [Fintype β]
    (Lα : LinearOrder α) (Lβ : LinearOrder β) {k : ℕ}
    (ha : Fintype.card α = k) (hb : Fintype.card β = k) (u : α ≃ β) :
    ordSign Lβ Lα hb ha u.symm = ordSign Lα Lβ ha hb u := by
  have h1 : ordSign Lα Lβ ha hb u * ordSign Lβ Lα hb ha u.symm = 1 := by
    rw [← ordSign_trans Lα Lβ Lα ha hb ha u u.symm, Equiv.self_trans_symm]
    exact ordSign_refl _ _ _
  rw [eq_comm, ← inv_eq_of_mul_eq_one_right h1, intUnits_inv_self]

/-- The **frame sign** of an execution: the sign comparing the lex order of its events with the
order its line puts them in.  This is the coboundary relating `orSign` to `sign ∘ evPerm`. -/
noncomputable def frameSign (x : ConcCatN K n) : ℤˣ :=
  ordSign (eventObjLinearOrder x.obj.chain) (evKeyOrder x) x.property x.property (Equiv.refl _)

/-- **The coboundary identity.**  The sign of the event permutation is the orientation sign of the
underlying refinement, twisted by the frame signs of the two executions. -/
theorem sign_evPerm {x y : ConcCatN K n} (f : x ⟶ y) :
    Equiv.Perm.sign (evPerm f) = frameSign x * orSign (concRefine f) * frameSign y := by
  set w : EventObj x.obj.chain ≃ EventObj y.obj.chain := (eventEquiv (concRefine f)).symm with hw
  have h0 : Equiv.Perm.sign (evPerm f)
      = ordSign (evKeyOrder x) (evKeyOrder y) x.property y.property w := by
    rw [evPerm_eq_ordPerm f]; rfl
  have h1 : ordSign (evKeyOrder x) (evKeyOrder y) x.property y.property w
      = ordSign (evKeyOrder x) (eventObjLinearOrder x.obj.chain) x.property x.property
          (Equiv.refl _)
        * ordSign (eventObjLinearOrder x.obj.chain) (evKeyOrder y) x.property y.property w := by
    rw [← ordSign_trans (evKeyOrder x) (eventObjLinearOrder x.obj.chain) (evKeyOrder y)
      x.property x.property y.property (Equiv.refl _) w, Equiv.refl_trans]
  have h2 : ordSign (eventObjLinearOrder x.obj.chain) (evKeyOrder y) x.property y.property w
      = ordSign (eventObjLinearOrder x.obj.chain) (eventObjLinearOrder y.obj.chain)
          x.property y.property w * frameSign y := by
    rw [frameSign, ← ordSign_trans (eventObjLinearOrder x.obj.chain)
      (eventObjLinearOrder y.obj.chain) (evKeyOrder y) x.property y.property y.property
      w (Equiv.refl _), Equiv.trans_refl]
  have hA : ordSign (evKeyOrder x) (eventObjLinearOrder x.obj.chain) x.property x.property
      (Equiv.refl _) = frameSign x := by
    rw [frameSign, ← ordSign_symm (eventObjLinearOrder x.obj.chain) (evKeyOrder x)
      x.property x.property (Equiv.refl _)]
    rfl
  have hB : ordSign (eventObjLinearOrder x.obj.chain) (eventObjLinearOrder y.obj.chain)
      x.property y.property w = orSign (concRefine f) := by
    rw [hw, ordSign_symm, orSign]
    exact ordSign_cast _ _ _ _ _ _ _
  rw [h0, h1, h2, hA, hB, mul_assoc]

/-- Read the other way: the orientation character of `Sched K`, pulled back to the executions with
`n` events, is `sign ∘ evPerm` twisted by the same coboundary. -/
theorem orSign_concRefine {x y : ConcCatN K n} (f : x ⟶ y) :
    orSign (concRefine f) = frameSign x * Equiv.Perm.sign (evPerm f) * frameSign y := by
  rw [sign_evPerm f]
  rcases Int.units_eq_one_or (frameSign x) with hx | hx <;>
    rcases Int.units_eq_one_or (frameSign y) with hy | hy <;>
    rw [hx, hy] <;> simp [mul_comm]

/-- **`orSign` and `sign ∘ evPerm` are the same class.**  Pulled back to `ConcCatN K n`, one is a
coboundary iff the other is — they differ by the frame coboundary. -/
theorem evPerm_sign_coboundary_iff :
    (∃ δ : ConcCatN K n → ℤˣ,
        ∀ {x y : ConcCatN K n} (f : x ⟶ y), Equiv.Perm.sign (evPerm f) = δ x * δ y)
      ↔ (∃ ε : ConcCatN K n → ℤˣ,
        ∀ {x y : ConcCatN K n} (f : x ⟶ y), orSign (concRefine f) = ε x * ε y) := by
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨fun x => frameSign x * δ x, fun {x y} f => ?_⟩
    rw [orSign_concRefine f, hδ f]
    simp only [mul_comm, mul_left_comm]
  · rintro ⟨ε, hε⟩
    refine ⟨fun x => frameSign x * ε x, fun {x y} f => ?_⟩
    rw [sign_evPerm f, hε f]
    simp only [mul_comm, mul_left_comm]

/-- An orientable `K` has a coboundary `sign ∘ evPerm` on every `ConcCatN K n`. -/
theorem evPerm_sign_coboundary_of_orientable (h : Orientable K) :
    ∃ δ : ConcCatN K n → ℤˣ,
      ∀ {x y : ConcCatN K n} (f : x ⟶ y), Equiv.Perm.sign (evPerm f) = δ x * δ y := by
  obtain ⟨ε, hε⟩ := h
  exact evPerm_sign_coboundary_iff.mpr
    ⟨fun x => ε x.obj.chain, fun {x y} f => by rw [hε (concRefine f), mul_comm]⟩

/-! ## §B The writhe: `salCross` extended to the braid action category

`salCross` counts the walls separating two topes.  The `Sₙ`-action reindexes the ground set (an
unordered pair of strands goes to an unordered pair, `pairEquiv`), so the count is **invariant**;
hence it extends from `Sal (braidCOM n)` (where it is `salWind`) to all of `BraidCat n`.  Pulled
back along `Ψ`, all topes are the identity chamber, so the writhe of a refinement is the **inversion
number** of its event permutation. -/

section Writhe

variable {n : ℕ}

/-- The `Sₙ`-action on the strand pairs: reindex, then re-sort. -/
def pairMap (σ : Equiv.Perm (Fin n)) (e : BraidGround n) : BraidGround n :=
  if h : σ e.1.1 < σ e.1.2 then ⟨(σ e.1.1, σ e.1.2), h⟩
  else ⟨(σ e.1.2, σ e.1.1), by
    refine lt_of_le_of_ne (not_lt.mp h) (fun hc => ?_)
    exact absurd (σ.injective hc) (ne_of_lt e.2).symm⟩

theorem pairMap_of_lt (σ : Equiv.Perm (Fin n)) {e : BraidGround n} (h : σ e.1.1 < σ e.1.2) :
    pairMap σ e = ⟨(σ e.1.1, σ e.1.2), h⟩ := dif_pos h

theorem pairMap_of_gt (σ : Equiv.Perm (Fin n)) {e : BraidGround n} (h : σ e.1.2 < σ e.1.1) :
    pairMap σ e = ⟨(σ e.1.2, σ e.1.1), h⟩ := by
  rw [pairMap, dif_neg (asymm h)]

theorem pairMap_pairMap (σ τ : Equiv.Perm (Fin n)) (hτ : ∀ i, τ (σ i) = i) (e : BraidGround n) :
    pairMap τ (pairMap σ e) = e := by
  rcases lt_trichotomy (σ e.1.1) (σ e.1.2) with h | h | h
  · rw [pairMap_of_lt σ h]
    have h1 : τ (σ e.1.1) < τ (σ e.1.2) := by rw [hτ, hτ]; exact e.2
    rw [pairMap_of_lt τ (e := ⟨(σ e.1.1, σ e.1.2), h⟩) h1]
    exact Subtype.ext (Prod.ext (hτ _) (hτ _))
  · exact absurd (σ.injective h) (ne_of_lt e.2)
  · rw [pairMap_of_gt σ h]
    have h1 : τ (σ e.1.1) < τ (σ e.1.2) := by rw [hτ, hτ]; exact e.2
    rw [pairMap_of_gt τ (e := ⟨(σ e.1.2, σ e.1.1), h⟩) h1]
    exact Subtype.ext (Prod.ext (hτ _) (hτ _))

/-- The strand pairs are permuted by `Sₙ`. -/
def pairEquiv (σ : Equiv.Perm (Fin n)) : Equiv.Perm (BraidGround n) where
  toFun := pairMap σ
  invFun := pairMap σ⁻¹
  left_inv e := pairMap_pairMap σ σ⁻¹ (fun i => by simp) e
  right_inv e := pairMap_pairMap σ⁻¹ σ (fun i => by simp) e

theorem signType_neg_inj {s t : SignType} (h : -s = -t) : s = t := by
  revert h; revert s; revert t; decide

/-- The action only reindexes (and flips the sign of) each ground element, so it does not change
*whether* two covectors disagree there. -/
theorem smul_ne_iff (σ : Equiv.Perm (Fin n)) (X Y : SignVec (BraidGround n)) (e : BraidGround n) :
    (σ • X) e ≠ (σ • Y) e ↔ X (pairMap σ⁻¹ e) ≠ Y (pairMap σ⁻¹ e) := by
  rw [smul_signVec_apply, smul_signVec_apply]
  have hne : σ⁻¹ e.1.1 ≠ σ⁻¹ e.1.2 := fun hc => absurd (Equiv.injective _ hc) (ne_of_lt e.2)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [signMat_lt X h, signMat_lt Y h, pairMap_of_lt σ⁻¹ h]
  · rw [signMat_gt X h, signMat_gt Y h, pairMap_of_gt σ⁻¹ h]
    exact ⟨fun hc hcon => hc (by rw [hcon]), fun hc hcon => hc (signType_neg_inj hcon)⟩

/-- **`salCross` is `Sₙ`-invariant** — the wall count of the braid arrangement does not see the
strand names.  (The sign flips of the reversed pairs cancel: they flip both topes.) -/
theorem salCross_smul (σ : Equiv.Perm (Fin n)) (a b : Sal (braidCOM n)) :
    salCross (σ • a) (σ • b) = salCross a b := by
  have hcard : (Finset.univ.filter fun e => (σ • a).tope e ≠ (σ • b).tope e).card
      = (Finset.univ.filter fun e => a.tope e ≠ b.tope e).card := by
    refine Finset.card_equiv (pairEquiv σ⁻¹) (fun e => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h := smul_ne_iff σ a.tope b.tope e
    rw [← salSmul_tope σ a, ← salSmul_tope σ b] at h
    exact h
  rw [salCross, salCross, hcard]

/-- **The writhe of a braid**: the number of walls its Salvetti relation crosses.  Well defined
because `salCross` is `Sₙ`-invariant. -/
noncomputable def writhe (n : ℕ) : BraidCat n ⥤ SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map {x y} f := Multiplicative.ofAdd (salCross (f.1 • x.cell) y.cell)
  map_id x := by
    change Multiplicative.ofAdd (salCross ((1 : Equiv.Perm (Fin n)) • x.cell) x.cell) = 1
    rw [one_smul, salCross_eq_zero_of_tope_eq rfl]
    rfl
  map_comp {x y z} f g := by
    change Multiplicative.ofAdd (salCross ((g.1 * f.1) • x.cell) z.cell) = _
    rw [SingleObj.comp_as_mul]
    change _ = Multiplicative.ofAdd (salCross (g.1 • y.cell) z.cell)
      * Multiplicative.ofAdd (salCross (f.1 • x.cell) y.cell)
    rw [← ofAdd_add, mul_smul,
      salCross_add (salSmul_le g.1 f.2) g.2, salCross_smul, add_comm]

/-- The pure part: a Salvetti relation is the braid with trivial permutation. -/
def salIncl (n : ℕ) : Sal (braidCOM n) ⥤ BraidCat n where
  obj a := ⟨a⟩
  map {a b} f := ⟨1, by rw [one_smul]; exact leOfHom f⟩
  map_id _ := rfl
  map_comp _ _ := Subtype.ext (one_mul 1).symm

/-- **The writhe extends `salWind`**: on the pure braids it is the wall-crossing number of the
Salvetti poset. -/
theorem writhe_salIncl_map {n : ℕ} {a b : Sal (braidCOM n)} (f : a ⟶ b) :
    (writhe n).map ((salIncl n).map f) = (salWind (braidCOM n)).map f := by
  change Multiplicative.ofAdd (salCross ((1 : Equiv.Perm (Fin n)) • a) b) = _
  rw [one_smul]
  rfl

theorem salIncl_comp_writhe (n : ℕ) : salIncl n ⋙ writhe n = salWind (braidCOM n) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun a b f => by
    simp only [Functor.comp_map, writhe_salIncl_map f]
    exact (Category.id_comp _).symm.trans
      (congrArg (fun g => eqToHom (by rfl) ≫ g) (Category.comp_id _).symm))

/-- The **inversion number** of a permutation: the strand pairs it crosses. -/
def invCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun e : BraidGround n => σ e.1.2 < σ e.1.1)).card

theorem braidSign_rankHt_comp_eq_neg_one_iff (τ : Equiv.Perm (Fin n)) (e : BraidGround n) :
    braidSign (rankHt n ∘ ⇑τ) e = -1 ↔ τ e.1.1 < τ e.1.2 := by
  constructor
  · intro h
    by_contra hc
    have hgt : τ e.1.2 < τ e.1.1 :=
      lt_of_le_of_ne (not_lt.mp hc) (fun hcon => absurd (τ.injective hcon) (ne_of_lt e.2).symm)
    have hz : ((τ e.1.2 : ℕ) : ℤ) < ((τ e.1.1 : ℕ) : ℤ) := by exact_mod_cast Fin.lt_def.mp hgt
    have hpos : braidSign (rankHt n ∘ ⇑τ) e = 1 := by
      rw [braidSign_apply]
      refine sign_pos ?_
      simp only [Function.comp_apply, rankHt]
      omega
    rw [hpos] at h
    exact absurd h (by decide)
  · intro h
    refine braidSign_neg_of_lt _ e ?_
    have hz : ((τ e.1.1 : ℕ) : ℤ) < ((τ e.1.2 : ℕ) : ℤ) := by exact_mod_cast Fin.lt_def.mp h
    simpa [rankHt] using hz

variable {K : BPSet}

/-- **The writhe of a refinement is the inversion number of its event permutation.**  Every
execution sits in the *identity* chamber of its own frame, so the only walls the Salvetti relation
crosses are the pairs of events that the two frames order differently. -/
theorem writhe_braidPsi {x y : ConcCatN K n} (f : x ⟶ y) :
    (writhe n).map ((braidPsi K n).map f)
      = Multiplicative.ofAdd ((invCount (evPerm f)⁻¹ : ℕ) : ℤ) := by
  change Multiplicative.ofAdd (salCross (evPerm f • braidCell x) (braidCell y)) = _
  congr 1
  have hfilter : (Finset.univ.filter
        fun e => (evPerm f • braidCell x).tope e ≠ (braidCell y).tope e)
      = Finset.univ.filter (fun e : BraidGround n => (evPerm f)⁻¹ e.1.2 < (evPerm f)⁻¹ e.1.1) := by
    refine Finset.filter_congr (fun e _ => ?_)
    rw [salSmul_tope, braidCell_tope, braidCell_tope, smul_braidSign, braidSign_rankHt]
    constructor
    · intro hne
      rcases lt_trichotomy ((evPerm f)⁻¹ e.1.1) ((evPerm f)⁻¹ e.1.2) with h | h | h
      · exact absurd ((braidSign_rankHt_comp_eq_neg_one_iff _ e).mpr h) hne
      · exact absurd (Equiv.injective _ h) (ne_of_lt e.2)
      · exact h
    · intro h hcon
      exact absurd ((braidSign_rankHt_comp_eq_neg_one_iff _ e).mp hcon) (asymm h)
  rw [salCross, hfilter]
  rfl

end Writhe

end CubeChains
