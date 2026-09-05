import CubeChains.Concurrency.Merge.WedgeSlice
import CubeChains.Concurrency.Merge.WedgeSplit
import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Concurrency/Merge/WedgeLocalize — a localized slice splits off its first bead

`⋁(n :: rest)` *is* `□n ∨ ⋁rest` (`serialWedge_cons` is `rfl`), so B3's wedge splitting already is
the recursion on a dimension list — no reindexing, no transport, no `eqToHom`.  Localizing it needs
only the **binary** `IsLocalization.prod`: `chConcat` is an equivalence carrying `(W X).prod (W Y)`
to `W (X ∨ Y)`, so `chConcat ⋙ Q` *is* a localization of `Ch X × Ch Y`, and `Localization.uniq`
compares it with the product of the two localizations.

The recursion is on the cons rather than over `Fin a.length` because `Presents.prod` is binary and
there is no `Presents.pi`: a `Fin`-indexed decomposition would strand C3.
-/

open CategoryTheory CategoryTheory.MonoidalCategory BPSet CubeChains

namespace ChainCat

/-! ## Pushing a chain forward along an isomorphism -/

section Pushforward

variable {K L : BPSet}

/-- The triangle over an iso can be cancelled, so `pushforward` along it is fully faithful. -/
def pushforwardFullyFaithful (e : K ≅ L) : (pushforward e.hom).FullyFaithful where
  preimage {a b} g :=
    ⟨@Hom.φ L ((pushforward e.hom).obj a) ((pushforward e.hom).obj b) g,
      (cancel_mono e.hom).mp (by rw [Category.assoc]; exact g.w)⟩
  map_preimage _ := hom_ext' rfl
  preimage_map _ := hom_ext' rfl

theorem pushforward_essSurj (e : K ≅ L) : (pushforward e.hom).EssSurj where
  mem_essImage c := ⟨⟨c.dims, c.map ≫ e.inv⟩, ⟨eqToIso (Obj.mk_eq_mk rfl (by simp))⟩⟩

theorem pushforward_isEquivalence (e : K ≅ L) : (pushforward e.hom).IsEquivalence :=
  haveI := (pushforwardFullyFaithful e).full
  haveI := (pushforwardFullyFaithful e).faithful
  haveI := pushforward_essSurj e
  { }

/-- `W` is both preserved and reflected by `pushforward` (`W_inverseImage`), so pushing forward
descends to the localizations. -/
noncomputable def locPushforward (φ : K ⟶ L) : (W K).Localization ⥤ (W L).Localization :=
  Localization.lift (pushforward φ ⋙ (W L).Q)
    (fun _ _ f hf => Localization.inverts (W L).Q (W L) _
      ((W_inverseImage φ).le f hf)) (W K).Q

/-- The defining factorisation of `locPushforward`. -/
noncomputable def locPushforwardFac (φ : K ⟶ L) :
    (W K).Q ⋙ locPushforward φ ≅ pushforward φ ⋙ (W L).Q :=
  Localization.fac _ _ _

/-- Pushing forward along an iso is a localization of the source at `W`, `W` being reflected as
well as preserved (`W_inverseImage`). -/
theorem isLocalization_pushforward (e : K ≅ L) :
    (pushforward e.hom ⋙ (W L).Q).IsLocalization (W K) :=
  haveI := pushforward_isEquivalence e
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_inverseImage e.hom)

/-- **An iso of bipointed sets is an iso of localized chain categories.** -/
noncomputable def locPushforwardEquiv (e : K ≅ L) :
    (W K).Localization ≌ (W L).Localization :=
  haveI := isLocalization_pushforward e
  Localization.uniq (W K).Q (pushforward e.hom ⋙ (W L).Q) (W K)

end Pushforward

/-! ## The binary splitting, localized -/

section Binary

variable {X Y : BPSet}

/-- **`chConcat` followed by the localization is itself a localization**, at the product class.
This is the whole of B4: everything below is `Localization.uniq` applied to it. -/
theorem isLocalization_chConcat (h : (X ∨ Y).AdmitsAltitude) :
    (chConcat X Y ⋙ (W (X ∨ Y)).Q).IsLocalization ((W X).prod (W Y)) :=
  haveI := chConcat_full h
  haveI := chConcat_essSurj h
  haveI : (chConcat X Y).IsEquivalence := { }
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_prod_eq_inverseImage_chConcat X Y)

/-- **`Ch (X ∨ Y)[W⁻¹] ≌ Ch X[W⁻¹] × Ch Y[W⁻¹]`** — `IsLocalization.prod` on the left,
`isLocalization_chConcat` on the right, compared by `Localization.uniq`. -/
noncomputable def locChConcatEquiv (h : (X ∨ Y).AdmitsAltitude) :
    (W X).Localization × (W Y).Localization ≌ (W (X ∨ Y)).Localization :=
  haveI := isLocalization_chConcat h
  Localization.uniq ((W X).Q.prod (W Y).Q) (chConcat X Y ⋙ (W (X ∨ Y)).Q) ((W X).prod (W Y))

end Binary

/-! ## The recursion on a dimension list -/

/-- **The first bead splits off**, with nothing to transport: `⋁(n :: rest)` is `□n ∨ ⋁rest`. -/
noncomputable def locChConsEquiv (n : ℕ+) (rest : List ℕ+) :
    (W (□(n : ℕ))).Localization × (W (⋁rest)).Localization
      ≌ (W (⋁(n :: rest))).Localization :=
  locChConcatEquiv (wedge2_admitsAltitude (cube_admitsAltitude (n : ℕ))
    (serialWedge_admitsAltitude rest))

/-! ## Read on the slices of `Ch Zbp`

B3 identifies `Over (zObj d)` with `Ch (⋁d)` and `W/d` with `W`, so the two localizations agree. -/

theorem isLocalization_overToWedgeChains (d : List ℕ+) :
    (overToWedgeChains d ⋙ (W (⋁d)).Q).IsLocalization ((W Zbp).over (X := zObj d)) :=
  Functor.IsLocalization.of_inverseImage _ _ _ _ (over_W_eq_inverseImage d)

/-- **`(Ch(Z)/d)[W/d⁻¹] ≌ Ch(⋁d)[W⁻¹]`.** -/
noncomputable def locOverEquivWedge (d : List ℕ+) :
    ((W Zbp).over (X := zObj d)).Localization ≌ (W (⋁d)).Localization :=
  haveI := isLocalization_overToWedgeChains d
  Localization.uniq ((W Zbp).over (X := zObj d)).Q (overToWedgeChains d ⋙ (W (⋁d)).Q)
    ((W Zbp).over (X := zObj d))

/-- **The localized slice over a shape splits off its first bead** — the cons step the bead
induction runs on. -/
noncomputable def locOverConsEquiv (n : ℕ+) (rest : List ℕ+) :
    (W (□(n : ℕ))).Localization × ((W Zbp).over (X := zObj rest)).Localization
      ≌ ((W Zbp).over (X := zObj (n :: rest))).Localization :=
  ((CategoryTheory.Equivalence.prod
    (CategoryTheory.Equivalence.refl (C := (W (□(n : ℕ))).Localization))
    (locOverEquivWedge rest)).trans (locChConsEquiv n rest)).trans
    (locOverEquivWedge (n :: rest)).symm

/-- A one-bead slice is the cube's: `⋁[n] = □n ∨ □0` and `□0` is the monoidal unit. -/
noncomputable def locOverSingleton (n : ℕ+) :
    ((W Zbp).over (X := zObj [n])).Localization ≌ (W (□(n : ℕ))).Localization :=
  (locOverEquivWedge [n]).trans (locPushforwardEquiv (ρ_ (□(n : ℕ))))

/-! ## Naturality in the ambient wedge

A map of wedges that respects the splitting is a pair of maps, and pushing a concatenation forward
along it is concatenating the two pushforwards.  Strictly — not up to iso. -/

/-- **The splitting is natural**: `pushforward (φ ∨ ψ)` is `pushforward φ` beside
`pushforward ψ`. -/
theorem chConcat_pushforward {X X' Y Y' : BPSet} (φ : X ⟶ X') (ψ : Y ⟶ Y') :
    (pushforward φ).prod (pushforward ψ) ⋙ chConcat X' Y'
      = chConcat X Y ⋙ pushforward (φ ⊗ₘ ψ) := by
  have hob : ∀ ab : Ch X × Ch Y,
      (chConcat X' Y').obj (⟨ab.1.dims, ab.1.map ≫ φ⟩, ⟨ab.2.dims, ab.2.map ≫ ψ⟩)
        = (pushforward (φ ⊗ₘ ψ)).obj ((chConcat X Y).obj ab) := by
    rintro ⟨a, b⟩
    refine congrArg (ChainCat.Obj.mk (a.dims ++ b.dims)) ?_
    change (serialWedgeAppend a.dims b.dims).inv ≫ ((a.map ≫ φ) ⊗ₘ (b.map ≫ ψ))
      = ((serialWedgeAppend a.dims b.dims).inv ≫ (a.map ⊗ₘ b.map)) ≫ (φ ⊗ₘ ψ)
    rw [Category.assoc, tensorHom_comp_tensorHom]
  exact Functor.hext hob (fun ab ab' g => chain_hom_hext (hob ab) (hob ab') HEq.rfl)

/-! ## Appending two shapes

`splitTarget` splits a wedge map at an *append* of the target, not at a cons, so this is the form a
general map of shapes is natural for. -/

/-- Concatenating chains of two serial wedges into a chain of the appended shape. -/
noncomputable def chAppend (x y : List ℕ+) : Ch (⋁x) × Ch (⋁y) ⥤ Ch (⋁(x ++ y)) :=
  chConcat (⋁x) (⋁y) ⋙ pushforward (serialWedgeAppend x y).hom

theorem chAppend_isEquivalence (x y : List ℕ+) : (chAppend x y).IsEquivalence :=
  haveI : (chConcat (⋁x) (⋁y)).IsEquivalence := (serialChConcatEquiv x y).isEquivalence_functor
  haveI := pushforward_isEquivalence (serialWedgeAppend x y)
  inferInstanceAs (chConcat (⋁x) (⋁y) ⋙ pushforward (serialWedgeAppend x y).hom).IsEquivalence

theorem W_prod_eq_inverseImage_chAppend (x y : List ℕ+) :
    (W (⋁x)).prod (W (⋁y)) = (W (⋁(x ++ y))).inverseImage (chAppend x y) :=
  (W_prod_eq_inverseImage_chConcat (⋁x) (⋁y)).trans
    (congrArg (MorphismProperty.inverseImage · (chConcat (⋁x) (⋁y)))
      (W_inverseImage (serialWedgeAppend x y).hom))

/-- **The appended splitting is a localization**, so `Ch (⋁(x ++ y))[W⁻¹]` is the product. -/
theorem isLocalization_chAppend (x y : List ℕ+) :
    (chAppend x y ⋙ (W (⋁(x ++ y))).Q).IsLocalization ((W (⋁x)).prod (W (⋁y))) :=
  haveI := chAppend_isEquivalence x y
  Functor.IsLocalization.of_inverseImage _ _ _ _ (W_prod_eq_inverseImage_chAppend x y)

noncomputable def locChAppendEquiv (x y : List ℕ+) :
    (W (⋁x)).Localization × (W (⋁y)).Localization ≌ (W (⋁(x ++ y))).Localization :=
  haveI := isLocalization_chAppend x y
  Localization.uniq ((W (⋁x)).Q.prod (W (⋁y)).Q) (chAppend x y ⋙ (W (⋁(x ++ y))).Q)
    ((W (⋁x)).prod (W (⋁y)))

/-- **Naturality of the append splitting in a map of shapes.**  `splitTarget` presents every wedge
map `⋁(x ++ y) ⟶ ⋁(x' ++ y')` that respects the junction in exactly this conjugated form, so this
is the square a map of shapes induces between the two products. -/
theorem chAppend_pushforward {x x' y y' : List ℕ+} (φ : ⋁x ⟶ ⋁x') (ψ : ⋁y ⟶ ⋁y') :
    (pushforward φ).prod (pushforward ψ) ⋙ chAppend x' y'
      = chAppend x y ⋙ pushforward ((serialWedgeAppend x y).inv ≫ (φ ⊗ₘ ψ)
          ≫ (serialWedgeAppend x' y').hom) := by
  rw [chAppend, chAppend, ← Functor.assoc, chConcat_pushforward, Functor.assoc, Functor.assoc,
    ← pushforward_comp, ← pushforward_comp, Iso.hom_inv_id_assoc]

/-- **Naturality, localized.**  Both routes round the square are lifts, through the localization
`(W ⋁x).Q.prod (W ⋁y).Q`, of the one functor `chAppend ⋙ pushforward θ ⋙ Q`; the strict square
`chAppend_pushforward` is what identifies them. -/
noncomputable def locChAppend_natural {x x' y y' : List ℕ+} (φ : ⋁x ⟶ ⋁x') (ψ : ⋁y ⟶ ⋁y') :
    (locPushforward φ).prod (locPushforward ψ) ⋙ (locChAppendEquiv x' y').functor
      ≅ (locChAppendEquiv x y).functor ⋙ locPushforward ((serialWedgeAppend x y).inv
          ≫ (φ ⊗ₘ ψ) ≫ (serialWedgeAppend x' y').hom) := by
  haveI := isLocalization_chAppend x y
  haveI := isLocalization_chAppend x' y'
  set θ := (serialWedgeAppend x y).inv ≫ (φ ⊗ₘ ψ) ≫ (serialWedgeAppend x' y').hom with hθ
  haveI : Localization.Lifting ((W (⋁x)).Q.prod (W (⋁y)).Q) ((W (⋁x)).prod (W (⋁y)))
      (chAppend x y ⋙ pushforward θ ⋙ (W (⋁(x' ++ y'))).Q)
      ((locPushforward φ).prod (locPushforward ψ) ⋙ (locChAppendEquiv x' y').functor) :=
    ⟨Functor.isoWhiskerRight (NatIso.prod (locPushforwardFac φ) (locPushforwardFac ψ))
        (locChAppendEquiv x' y').functor ≪≫
      Functor.isoWhiskerLeft ((pushforward φ).prod (pushforward ψ))
        (Localization.compUniqFunctor ((W (⋁x')).Q.prod (W (⋁y')).Q)
          (chAppend x' y' ⋙ (W (⋁(x' ++ y'))).Q) ((W (⋁x')).prod (W (⋁y')))) ≪≫
      eqToIso (congrArg (· ⋙ (W (⋁(x' ++ y'))).Q) (chAppend_pushforward φ ψ))⟩
  haveI : Localization.Lifting ((W (⋁x)).Q.prod (W (⋁y)).Q) ((W (⋁x)).prod (W (⋁y)))
      (chAppend x y ⋙ pushforward θ ⋙ (W (⋁(x' ++ y'))).Q)
      ((locChAppendEquiv x y).functor ⋙ locPushforward θ) :=
    ⟨Functor.isoWhiskerRight (Localization.compUniqFunctor ((W (⋁x)).Q.prod (W (⋁y)).Q)
        (chAppend x y ⋙ (W (⋁(x ++ y))).Q) ((W (⋁x)).prod (W (⋁y)))) (locPushforward θ) ≪≫
      Functor.isoWhiskerLeft (chAppend x y) (locPushforwardFac θ)⟩
  exact Localization.liftNatIso ((W (⋁x)).Q.prod (W (⋁y)).Q) ((W (⋁x)).prod (W (⋁y)))
    (chAppend x y ⋙ pushforward θ ⋙ (W (⋁(x' ++ y'))).Q)
    (chAppend x y ⋙ pushforward θ ⋙ (W (⋁(x' ++ y'))).Q)
    ((locPushforward φ).prod (locPushforward ψ) ⋙ (locChAppendEquiv x' y').functor)
    ((locChAppendEquiv x y).functor ⋙ locPushforward θ) (Iso.refl _)

end ChainCat
