import CubeChains.Braid.Category
import CubeChains.Braid.Functor
import CubeChains.Salvetti.Normalize

/-!
# Braid/Grading — the braid of an execution, at every strand count at once

`Braid/Functor` works one stratum at a time, which is not enough: composing executions **adds**
strand counts, so the braid 2-functor cannot be stated per-stratum.

The friction is that `ConcCat K` is not literally a `Σ`-category: `nEvents x = nEvents y` holds only
*propositionally* (`card_eventObj_eq_of_hom`), while `SigmaHom.mk` wants the indices definitionally
equal.  Hence the `eqToHom` recast in `braidGrading.map`, and the transport lemmas below.

Same shape as `Events/OrdSign`'s `orSign`, which carries its count equalities explicitly.
-/

namespace CubeChains

open CategoryTheory Equiv

variable {K : BPSet}

/-! ## Recasting a braid along an equality of strand counts -/

/-- Transport a braid along an equality of strand counts. -/
def braidCast {n m : ℕ} (h : n = m) (b : Braid n) : Braid m := cast (congrArg Braid h) b

@[simp] theorem braidCast_rfl {n : ℕ} (b : Braid n) : braidCast rfl b = b := rfl

theorem braidCast_ofPerm {n m : ℕ} (h : n = m) (σ : Perm (Fin n)) :
    braidCast h (ofPerm σ) = ofPerm ((finCongr h).permCongr σ) := by
  subst h
  simp [braidCast, ← Equiv.Perm.one_def]

theorem permLen_permCongr {n m : ℕ} (h : n = m) (σ : Perm (Fin n)) :
    permLen ((finCongr h).permCongr σ) = permLen σ := by
  subst h
  simp [← Equiv.Perm.one_def]

/-- A recast slides past a braid. -/
theorem braidHom_eqToHom {n m : ℕ} (h : n = m) (b : Braid n) :
    (braidHom b ≫ eqToHom (congrArg strands h) : strands n ⟶ strands m)
      = eqToHom (congrArg strands h) ≫ braidHom (braidCast h b) := by
  subst h
  simp

/-! ## The event count and the event permutation, ungraded -/

/-- The number of events of an execution — the strand count of its braid. -/
def nEvents (x : ConcCat K) : ℕ := Fintype.card (EventObj x.chain)

/-- The refinement underlying a morphism of executions (`y`'s chain refines `x`'s). -/
def concRefine' {x y : ConcCat K} (f : x ⟶ y) : y.chain ⟶ x.chain := f.1.unop

/-- **The strand count is well defined**: a refinement neither creates nor destroys events. -/
theorem nEvents_eq {x y : ConcCat K} (f : x ⟶ y) : nEvents x = nEvents y :=
  (card_eventObj_eq_of_hom (concRefine' f)).symm

/-- The frame of an execution: its events in `evKey` order (bead first, then the line). -/
def evIdx' (x : ConcCat K) : EventObj x.chain ≃ Fin (nEvents x) :=
  keyEquiv (evKey x.line) (evKey_injective _)

/-- The event permutation of a refinement, read in the *source's* frame. -/
def evPerm' {x y : ConcCat K} (f : x ⟶ y) : Perm (Fin (nEvents x)) :=
  (((evIdx' x).symm.trans (eventEquiv (concRefine' f)).symm).trans (evIdx' y)).trans
    (finCongr (nEvents_eq f)).symm

/-! ## Reading an execution in a stratum

`ConcCatN K n` is the full subcategory on the `n`-event executions, so an execution and a refinement
sit in *any* stratum their counts allow.  That is the whole bridge: the graded lemmas
(`evPerm_comp`, `permLen_evPerm_comp`) transport to the ungraded ones by `finCongr`, and `permLen`
is blind to the transport (`permLen_permCongr`). -/

/-- An execution, placed in the stratum its event count names. -/
def objAt (x : ConcCat K) {n : ℕ} (h : nEvents x = n) : ConcCatN K n := ⟨x, h⟩

/-- A refinement, placed in a stratum. -/
noncomputable def homAt {x y : ConcCat K} (f : x ⟶ y) {n : ℕ}
    (hx : nEvents x = n) (hy : nEvents y = n) :
    objAt x hx ⟶ objAt y hy := ObjectProperty.homMk f

/-- **The graded event permutation is the ungraded one, transported.** -/
theorem evPerm_homAt {x y : ConcCat K} (f : x ⟶ y) {n : ℕ}
    (hx : nEvents x = n) (hy : nEvents y = n) :
    evPerm (homAt f hx hy) = (finCongr hx).permCongr (evPerm' f) := by
  apply Equiv.ext
  intro k
  simp only [evPerm, evPerm', evIdx, evIdx', objAt, homAt, Equiv.permCongr_apply,
    Equiv.trans_apply, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply, Fin.cast_cast]
  rfl

theorem permLen_evPerm_homAt {x y : ConcCat K} (f : x ⟶ y) {n : ℕ}
    (hx : nEvents x = n) (hy : nEvents y = n) :
    permLen (evPerm (homAt f hx hy)) = permLen (evPerm' f) := by
  rw [evPerm_homAt, permLen_permCongr]

theorem homAt_comp {x y z : ConcCat K} (f : x ⟶ y) (g : y ⟶ z) {n : ℕ}
    (hx : nEvents x = n) (hy : nEvents y = n) (hz : nEvents z = n) :
    homAt f hx hy ≫ homAt g hy hz = homAt (f ≫ g) hx hz := rfl

@[simp] theorem evPerm'_id (x : ConcCat K) : evPerm' (𝟙 x) = 1 := by
  have h := evPerm_homAt (𝟙 x) (rfl : nEvents x = nEvents x) rfl
  rw [show homAt (𝟙 x) (rfl : nEvents x = nEvents x) rfl = 𝟙 (objAt x rfl) from rfl,
    evPerm_id] at h
  simpa [finCongr_refl] using h.symm

/-- **The event permutation composes**, once `g`'s frame is transported into `x`'s. -/
theorem evPerm'_comp {x y z : ConcCat K} (f : x ⟶ y) (g : y ⟶ z) :
    evPerm' (f ≫ g)
      = (finCongr (nEvents_eq f).symm).permCongr (evPerm' g) * evPerm' f := by
  have hy : nEvents y = nEvents x := (nEvents_eq f).symm
  have hz : nEvents z = nEvents x := (nEvents_eq (f ≫ g)).symm
  have key := evPerm_comp (homAt f rfl hy) (homAt g hy hz)
  rw [homAt_comp, evPerm_homAt, evPerm_homAt, evPerm_homAt] at key
  simpa [finCongr_refl] using key

/-- **The germ relation, ungraded**: composable refinements never cross the same pair twice. -/
theorem permLen_evPerm'_comp {x y z : ConcCat K} (f : x ⟶ y) (g : y ⟶ z) :
    permLen (evPerm' (f ≫ g)) = permLen (evPerm' g) + permLen (evPerm' f) := by
  have hy : nEvents y = nEvents x := (nEvents_eq f).symm
  have hz : nEvents z = nEvents x := (nEvents_eq (f ≫ g)).symm
  have key := permLen_evPerm_comp (homAt f rfl hy) (homAt g hy hz)
  rw [← evPerm_comp, homAt_comp, permLen_evPerm_homAt, permLen_evPerm_homAt,
    permLen_evPerm_homAt] at key
  exact key

/-! ## The braid of an execution, at every strand count at once -/

/-- Composition in a fibre of `𝔅` multiplies braids — reversed, as `SingleObj` composes. -/
theorem braidHom_comp {n : ℕ} (a b : Braid n) :
    (braidHom a ≫ braidHom b : strands n ⟶ strands n) = braidHom (b * a) := rfl

/-- A recast slides *left* past a braid — the mirror of `braidHom_eqToHom`. -/
theorem eqToHom_braidHom {n m : ℕ} (h : n = m) (b : Braid m) :
    (eqToHom (congrArg strands h) ≫ braidHom b : strands n ⟶ strands m)
      = braidHom (braidCast h.symm b) ≫ eqToHom (congrArg strands h) := by
  subst h
  simp [braidCast]

/-- **The globally graded braid functor** `Int(Lines K) ⥤ 𝔅`: an execution goes to the object
naming its **event count**, a refinement to the simple braid of its event permutation.

The `eqToHom` is the strand-count recast — `nEvents x = nEvents y` only *propositionally*, while
`SigmaHom.mk` wants the indices definitionally equal.  Functoriality is the germ relation
(`permLen_evPerm'_comp`): composable refinements never cross the same pair of events twice. -/
noncomputable def braidGrading (K : BPSet) : ConcCat K ⥤ Braids where
  obj x := strands (nEvents x)
  map {x y} f := braidHom (ofPerm (evPerm' f)) ≫ eqToHom (congrArg strands (nEvents_eq f))
  map_id x := by
    rw [evPerm'_id, ofPerm_one,
      show (braidHom (1 : Braid (nEvents x))) = 𝟙 (strands (nEvents x)) from rfl,
      Category.id_comp]
    exact eqToHom_refl _ _
  map_comp {x y z} f g := by
    have hbraid : braidCast (nEvents_eq f).symm (ofPerm (evPerm' g)) * ofPerm (evPerm' f)
        = ofPerm (evPerm' (f ≫ g)) := by
      rw [braidCast_ofPerm]
      refine (ofPerm_mul ?_).trans (congrArg ofPerm (evPerm'_comp f g).symm)
      rw [← evPerm'_comp f g, permLen_permCongr]
      exact permLen_evPerm'_comp f g
    rw [Category.assoc, ← Category.assoc (eqToHom _) (braidHom _) (eqToHom _),
      eqToHom_braidHom (nEvents_eq f) (ofPerm (evPerm' g)),
      Category.assoc, eqToHom_trans, ← Category.assoc, braidHom_comp, hbraid]

@[simp] theorem braidGrading_obj (x : ConcCat K) :
    (braidGrading K).obj x = strands (nEvents x) := rfl

/-- **The braid functor on the concurrency groupoid.**  `Braids` is already a groupoid — braids are
invertible — so this is a bare `FreeGroupoid.lift`: no groupoidification of the target, no
`Localization.uniq`.

For `K.repoint u v` this is the functor on `Int(Lines(K;u,v))` the enrichment wants: a 1-cell goes
to the object naming its length, a 2-cell to its braid. -/
noncomputable def braidGrpd (K : BPSet) : ConcGrpd K ⥤ Braids :=
  FreeGroupoid.lift (braidGrading K)

@[simp] theorem braidGrpd_obj (x : ConcCat K) :
    (braidGrpd K).obj (FreeGroupoid.mk x) = strands (nEvents x) := rfl

@[simp] theorem braidGrpd_homMk {x y : ConcCat K} (f : x ⟶ y) :
    (braidGrpd K).map (FreeGroupoid.homMk f)
      = braidHom (ofPerm (evPerm' f)) ≫ eqToHom (congrArg strands (nEvents_eq f)) :=
  FreeGroupoid.lift_map_homMk _ f

end CubeChains
