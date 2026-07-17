import CubeChains.Events.EventMapBij

/-!
# Salvetti/SignLine — the event-indexed sign presentation of `Lines`

A `SignLine a` records a line of `a` as a `Bool` comparator on **same-bead ordered event
pairs** of `EventObj a` (plus a per-bead strict-total-order proof), rather than as the
`Fin`-indexed chamber tuple `LinesObj a`.  `signLineEquiv` shows the two carry the same data.

The payoff is `signRestrict`: because `eventMap f` is a bijection of event sets, restriction
along `f : a ⟶ b` is **precomposition of the comparator with `eventMap f`** — no `Fin.cast`,
no `Chamber.restrict` reindex in the data — and functoriality is a thin wrapper over the
already-proven `eventMap_id` / `eventMap_comp`.  The order-reindex transport that the chamber
`linesRestrict` carries in its data lives here only inside the one-off `signLineEquiv`.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

variable {K : BPSet}

/-- Two events lie in the **same bead** when they share a bead index. -/
abbrev SameBead {a : Ch K} (e e' : EventObj a) : Prop := e.1 = e'.1

/-- A **sign line** of `a`: a `Bool` comparator on same-bead ordered event pairs whose
restriction to each bead's directions is a strict total order.  The event-indexed counterpart
of `LinesObj a = ∀ i, Chamber (beadDim a i)`. -/
structure SignLine (a : Ch K) where
  /-- The pairwise sign on same-bead events (`sgn e e' _ = true` means `e ≺ e'`). -/
  sgn : ∀ e e' : EventObj a, SameBead e e' → Bool
  /-- On each bead the comparator is a strict total order of that bead's directions. -/
  sto : ∀ i : ChainCat.Bead a,
    IsStrictTotalOrder (Fin (ChainCat.beadDim a i))
      (fun δ δ' => sgn ⟨i, δ⟩ ⟨i, δ'⟩ rfl = true)

/-- A sign line is determined by its comparator (`sto` is a `Subsingleton`). -/
@[ext] theorem SignLine.ext {a : Ch K} {L₁ L₂ : SignLine a} (h : L₁.sgn = L₂.sgn) :
    L₁ = L₂ := by
  obtain ⟨s₁, t₁⟩ := L₁; obtain ⟨s₂, t₂⟩ := L₂
  cases h
  exact congrArg (SignLine.mk s₁) (Subsingleton.elim t₁ t₂)

/-- Move the comparator's two event arguments along equalities (proof arguments are irrelevant). -/
theorem SignLine.sgn_hcongr {a : Ch K} (L : SignLine a) {x x' y y' : EventObj a}
    (wx : x = y) (wx' : x' = y') (hx : SameBead x x') (hy : SameBead y y') :
    L.sgn x x' hx = L.sgn y y' hy := by
  subst wx; subst wx'; rfl

/-- Move only the comparator's second event argument along an equality. -/
theorem SignLine.sgn_congr₂ {a : Ch K} (L : SignLine a) (e : EventObj a) {x y : EventObj a}
    (w : x = y) (hx : SameBead e x) (hy : SameBead e y) : L.sgn e x hx = L.sgn e y hy := by
  subst w; rfl

/-- `decide (b = true) = b`, discharging the `Bool`/`Prop` round-trip in `signLineEquiv`. -/
private theorem decide_beq_true (b : Bool) : decide (b = true) = b := by cases b <;> rfl

/-! ### `SignLine a ≃ LinesObj a` — the sign line *is* the chamber tuple

The transport that separates the two presentations (`h ▸`/`Fin.cast` comparing two events
known to share a bead) is confined to this equivalence's `invFun`. -/

/-- A chamber-per-bead is exactly a per-bead strict-order comparator on events. -/
def signLineEquiv (a : Ch K) : SignLine a ≃ LinesObj a where
  toFun L i :=
    { lt := fun δ δ' => L.sgn ⟨i, δ⟩ ⟨i, δ'⟩ rfl = true
      sto := L.sto i
      decLt := fun _ _ => inferInstance }
  invFun C :=
    { sgn := fun e e' h =>
        decide ((C e.1).lt e.2 (Fin.cast (congrArg (ChainCat.beadDim a) h.symm) e'.2))
      sto := fun i => by
        have hsto := (C i).sto
        have hrel : (C i).lt
            = (fun δ δ' : Fin (ChainCat.beadDim a i) => decide ((C i).lt δ δ') = true) := by
          funext δ δ'; exact decide_eq_true_eq.symm
        rw [hrel] at hsto
        exact hsto }
  left_inv L := by
    apply SignLine.ext
    funext e e' h
    -- reconstructed sign = `decide (L.sgn e ⟨e.1, cast e'.2⟩ rfl = true)`; collapse the round-trip
    -- and move the second event back to `e'`
    change decide (L.sgn e ⟨e.1, Fin.cast (congrArg (ChainCat.beadDim a) h.symm) e'.2⟩ rfl = true)
        = L.sgn e e' h
    rw [decide_beq_true]
    have hw : (⟨e.1, Fin.cast (congrArg (ChainCat.beadDim a) h.symm) e'.2⟩ : EventObj a) = e' := by
      obtain ⟨i', d'⟩ := e'
      cases h
      rfl
    exact L.sgn_congr₂ e hw rfl h
  right_inv C := by
    funext i
    apply Chamber.ext
    funext δ δ'
    exact decide_eq_true_eq

/-! ### Restriction rides the event bijection

`signRestrict f L` precomposes `L`'s comparator with `eventMap f`.  The `sgn` field carries no
`Fin.cast`/`Chamber.restrict`; the free-coordinate embedding appears only in the `sto` proof. -/

/-- Restriction of a sign line along `f : a ⟶ b` (`a` finer than `b`): compare fine events by
comparing their images under the event bijection `eventMap f`.  `eventMap` sends same-fine-bead
pairs to same-coarse-bead pairs, so the coarse comparison is defined. -/
def signRestrict {a b : Ch K} (f : a ⟶ b) (L : SignLine b) : SignLine a where
  sgn e e' h :=
    L.sgn (eventMap f e) (eventMap f e') (congrArg (fun j => blockIdx fᵂ j) h)
  sto := fun i =>
    haveI := L.sto (blockIdx fᵂ i)
    { trichotomous := fun δ δ' h1 h2 =>
        (faceEmb (blockFace fᵂ i)).injective
          (@Std.Trichotomous.trichotomous _
            (fun d d' => L.sgn (⟨blockIdx fᵂ i, d⟩ : EventObj b) ⟨blockIdx fᵂ i, d'⟩ rfl = true) _
            (faceEmb (blockFace fᵂ i) δ) (faceEmb (blockFace fᵂ i) δ') h1 h2)
      irrefl := fun δ =>
        @Std.Irrefl.irrefl _
          (fun d d' => L.sgn (⟨blockIdx fᵂ i, d⟩ : EventObj b) ⟨blockIdx fᵂ i, d'⟩ rfl = true) _
          (faceEmb (blockFace fᵂ i) δ)
      trans := fun δ δ' δ'' hab hbc =>
        @IsTrans.trans _
          (fun d d' => L.sgn (⟨blockIdx fᵂ i, d⟩ : EventObj b) ⟨blockIdx fᵂ i, d'⟩ rfl = true) _
          (faceEmb (blockFace fᵂ i) δ) (faceEmb (blockFace fᵂ i) δ')
          (faceEmb (blockFace fᵂ i) δ'') hab hbc }

/-- Restriction along the identity is the identity — delegates to `eventMap_id`. -/
theorem signRestrict_id {a : Ch K} (L : SignLine a) : signRestrict (𝟙 a) L = L := by
  apply SignLine.ext
  funext e e' h
  dsimp only [signRestrict]
  exact L.sgn_hcongr (eventMap_id e) (eventMap_id e') _ _

/-- Restriction is functorial — delegates to `eventMap_comp`. -/
theorem signRestrict_comp {a b c : Ch K} (f : a ⟶ b) (g : b ⟶ c) (L : SignLine c) :
    signRestrict (f ≫ g) L = signRestrict f (signRestrict g L) := by
  apply SignLine.ext
  funext e e' h
  dsimp only [signRestrict]
  exact L.sgn_hcongr (eventMap_comp f g e) (eventMap_comp f g e') _ _

/-- The sign presheaf `SignLine K : (Ch K)ᵒᵖ ⥤ Type`, the event-indexed twin of `Lines K`. -/
def SignLines (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type where
  obj X := SignLine X.unop
  map φ := TypeCat.ofHom (signRestrict φ.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro L
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact signRestrict_id L
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro L
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact signRestrict_comp ψ.unop φ.unop L

end CubeChains
