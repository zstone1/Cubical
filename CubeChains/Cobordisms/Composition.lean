import CubeChains.Cobordisms.Cobordism

/-!
# Cobordisms/Composition — the pushout composite of directed cobordisms (M4b)

The **closure theorem**: the pushout composite of two directed cobordisms is again a
directed cobordism.  Given `W₁ : X ⇒c Y` and `W₂ : Y ⇒c Z`, glue them along the
shared `Y` (the M2 cospan composite `W₁.toCospan.comp W₂.toCospan`, middle
`pushout W₁.inr W₂.inl`) and supply all five fields of `DirectedCobordism X Z`:

* `legsDisjoint` — directly from M2 (`Cospan.LegsDisjoint.comp`);
* `srcCollar` / `sinkCollar` — push the existing collars forward along the relevant
  pushout injection (`mono ∘ mono`, the bottom/top condition unfolds by `comp_inl`/
  `comp_inr`);
* `srcSieve` / `sinkCosieve` — **the barrier theorem**: the source image survives as a
  sieve, and the sink image as a cosieve, in the glued total space.

## The barrier argument (`srcSieve` / `sinkCosieve`)

Write `W := pushout C₁.inr C₂.inl`, `p₁ := pushout.inl …`, `p₂ := pushout.inr …`
(both mono).  Since `(C₁.comp C₂).inl = C₁.inl ≫ p₁`, the composite source image is
the `p₁`-image of `srcImage C₁`.  We prove this is a *sieve* in `W`
(`pushout_inl_srcImage_isSieve`) by induction on `Reaches W`:

* **Joint surjectivity** of the levelwise pushout (`comp_isPushout_app`,
  `Types.eq_or_eq_of_isPushout`): every cell of `W` is a `p₁`-cell or a `p₂`-cell.
* On a one-step face relation we split on which block the *top* cell lives in.  If it
  is a `p₁`-cell, the predecessor is the `p₁`-image of the corresponding face in `C₁`,
  and `C₁.srcSieve` pulls source-membership back.  If it is a pure `p₂`-cell, a
  `p₁`-source cell equal to it would, by the van Kampen pullback
  (`comp_isPullback_app`), factor through the glued `Y` (= `sinkImage C₁`), which is
  **disjoint** from `srcImage C₁` (`C₁.legsDisjoint`) — so that sub-case is vacuous.

`trans` is handled by composing the inductive hypotheses; `refl` is trivial.  The
sink cosieve is the exact mirror image on the `p₂`/`C₂` side.

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Cobordism` (the bundle + M2 cospan
composition, the collars, the directed-boundary sieve/cosieve API).
-/

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open Precubical.Cobordism

namespace PrecubicalSet

universe u

variable {X Y Z : PrecubicalSet}

/-! ### Cell-structure helpers

`mapCell` is functorial, mono maps act injectively on cells, and the levelwise
pushout is jointly surjective.  These are the combinatorial inputs the barrier
induction consumes. -/

/-- `mapCell` is functorial: applying a composite is applying the factors in turn. -/
theorem mapCell_comp {A B C : PrecubicalSet} (f : A ⟶ B) (g : B ⟶ C)
    (x : A.TotalCell) : mapCell (f ≫ g) x = mapCell g (mapCell f x) := by
  rfl

/-- `mapCell` on an explicit level-`n` cell. -/
theorem mapCell_mk {A B : PrecubicalSet} (f : A ⟶ B) (n : ℕ) (x : A.cells n) :
    mapCell f ⟨n, x⟩ = ⟨n, f⟪n⟫ x⟩ := rfl

/-- If `mapCell f a` equals a cell at a *fixed* level `m`, then `a` itself sits at
level `m`: there is `a' : A.cells m` with `a = ⟨m, a'⟩` and `f.app a' = c`.  This
extracts the level-`m` data cleanly (no leftover `HEq`), the workhorse for unfolding
image-membership inside the barrier induction. -/
theorem mapCell_eq_sigma {A B : PrecubicalSet} (f : A ⟶ B) (a : A.TotalCell)
    {m : ℕ} {c : B.cells m} (h : mapCell f a = ⟨m, c⟩) :
    ∃ a' : A.cells m, a = ⟨m, a'⟩ ∧ f⟪m⟫ a' = c := by
  obtain ⟨k, a'⟩ := a
  obtain ⟨rfl, ha⟩ := Sigma.mk.inj h
  exact ⟨a', rfl, eq_of_heq ha⟩

/-- A monomorphism of precubical sets is injective on cells at every fixed level. -/
theorem app_injective_of_mono {A B : PrecubicalSet} (f : A ⟶ B) [Mono f] (n : ℕ) :
    Function.Injective (f⟪n⟫) := by
  rw [← mono_iff_injective]
  exact (NatTrans.mono_iff_mono_app f).1 inferInstance (op ▫n)

/-- The levelwise pushout of the cospan-composition gluing square, at level `n`.
(The presheaf pushout `pushout C₁.inr C₂.inl` transported to `Type` by the
colimit-preserving evaluation functor.) -/
theorem comp_isPushout_app (C₁ : Cospan X Y) (C₂ : Cospan Y Z) (n : ℕ) :
    IsPushout (C₁.inr⟪n⟫) (C₂.inl⟪n⟫)
      ((pushout.inl C₁.inr C₂.inl)⟪n⟫)
      ((pushout.inr C₁.inr C₂.inl)⟪n⟫) :=
  (IsPushout.of_hasPushout C₁.inr C₂.inl).map
    (F := (evaluation Boxᵒᵖ Type).obj (op ▫n))

/-- **Joint surjectivity.**  Every `n`-cell of `pushout C₁.inr C₂.inl` is a `p₁`-cell
or a `p₂`-cell. -/
theorem comp_cell_cases (C₁ : Cospan X Y) (C₂ : Cospan Y Z) (n : ℕ)
    (c : (pushout C₁.inr C₂.inl).cells n) :
    (∃ a, (pushout.inl C₁.inr C₂.inl)⟪n⟫ a = c) ∨
      ∃ b, (pushout.inr C₁.inr C₂.inl)⟪n⟫ b = c :=
  Types.eq_or_eq_of_isPushout (comp_isPushout_app C₁ C₂ n) c

/-! ### The source-sieve barrier

The `p₁`-image of a sieve `S` of `C₁.mid` that is disjoint from the gluing image
(`= sinkImage C₁ = image of C₁.inr`) is a sieve of the glued total space. -/

/-- **The source barrier (general form).**  Let `C₁ : Cospan X Y`, `C₂ : Cospan Y Z`,
`W := pushout C₁.inr C₂.inl`, `p₁ := pushout.inl …`.  If `S` is a sieve of `C₁.mid`
that is *disjoint from the image of the gluing leg* `C₁.inr`, then the `p₁`-image of
`S` is a sieve of `W`.

This is the heart of M4b: the induction on `Reaches W` shows the predecessor of a
`p₁`-source cell is again a `p₁`-source cell, the cross-gluing sub-case being killed
by the van Kampen pullback + disjointness. -/
theorem pushout_inl_image_isSieve (C₁ : Cospan X Y) (C₂ : Cospan Y Z)
    (S : C₁.mid.TotalCell → Prop) (hS : IsSieve C₁.mid S)
    (hdisj : ∀ (a : C₁.mid.TotalCell) (y : Y.cells a.1),
      C₁.inr⟪a.1⟫ y = a.2 → ¬ S a) :
    IsSieve (pushout C₁.inr C₂.inl)
      (fun w => ∃ a, S a ∧ mapCell (pushout.inl C₁.inr C₂.inl) a = w) := by
  -- Abbreviations.
  set p₁ := pushout.inl C₁.inr C₂.inl with hp₁
  set p₂ := pushout.inr C₁.inr C₂.inl with hp₂
  -- The induction.
  intro u w hreach
  induction hreach with
  | refl x => exact id
  | @source n i c =>
      -- `u = ⟨n, faceMap false i c⟩`, `w = ⟨n+1, c⟩`.
      rintro ⟨a, hSa, hav⟩
      -- `hav : mapCell p₁ a = ⟨n+1, c⟩`; pin `a` to level `n+1`.
      obtain ⟨a', rfl, ha''⟩ := mapCell_eq_sigma p₁ a hav
      -- Which block does the top cell `c` live in?
      rcases comp_cell_cases C₁ C₂ (n + 1) c with ⟨c₁, hc₁⟩ | ⟨c₂, hc₂⟩
      · -- `c = p₁.app c₁`: a genuine `C₁` step.
        have hac : a' = c₁ :=
          app_injective_of_mono p₁ (n + 1) (ha''.trans hc₁.symm)
        subst hac
        refine ⟨⟨n, C₁.mid.faceMap false i a'⟩, ?_, ?_⟩
        · -- `S` is a sieve: the face is reached-from-below by `a'`.
          exact hS _ _ (Reaches.source i a') hSa
        · -- `mapCell p₁ ⟨n, face⟩ = ⟨n, faceMap false i c⟩` via face-commutation.
          rw [mapCell_mk]
          exact congrArg (Sigma.mk n) (by rw [map_faceMap p₁ false i a', ha''])
      · -- `c = p₂.app c₂`: the cross-gluing case is vacuous.
        exfalso
        -- `p₁.app a' = c = p₂.app c₂`, so `a'` factors through the glued `Y`.
        have hcross : p₁⟪n + 1⟫ a' = p₂⟪n + 1⟫ c₂ :=
          ha''.trans hc₂.symm
        obtain ⟨y, hy₁, _hy₂⟩ :=
          Types.exists_of_isPullback (comp_isPullback_app C₁ C₂ (n + 1)) a' c₂ hcross
        -- `a' = C₁.inr y`, so `⟨n+1, a'⟩ ∈ image C₁.inr`, contradicting disjointness.
        exact hdisj ⟨n + 1, a'⟩ y hy₁ hSa
  | @target n i c =>
      -- `u = ⟨n+1, c⟩`, `w = ⟨n, faceMap true i c⟩`.
      rintro ⟨a, hSa, hav⟩
      obtain ⟨a', rfl, ha''⟩ := mapCell_eq_sigma p₁ a hav
      -- The bigger cell `c` decides the block.
      rcases comp_cell_cases C₁ C₂ (n + 1) c with ⟨c₁, hc₁⟩ | ⟨c₂, hc₂⟩
      · -- `c = p₁.app c₁`.
        -- The target face of `c` is the `p₁`-image of the target face of `c₁`.
        have hfc : (pushout C₁.inr C₂.inl).faceMap true i c
            = p₁⟪n⟫ (C₁.mid.faceMap true i c₁) := by
          rw [← hc₁, map_faceMap p₁ true i c₁]
        have hac : a' = C₁.mid.faceMap true i c₁ :=
          app_injective_of_mono p₁ n (ha''.trans hfc)
        subst hac
        refine ⟨⟨n + 1, c₁⟩, ?_, ?_⟩
        · -- `S` sieve: `c₁` reaches its target face, so source-membership pulls back.
          exact hS _ _ (Reaches.target i c₁) hSa
        · -- `mapCell p₁ ⟨n+1, c₁⟩ = ⟨n+1, c⟩`.
          rw [mapCell_mk]
          exact congrArg (Sigma.mk (n + 1)) hc₁
      · -- `c = p₂.app c₂`: cross-gluing, vacuous.
        exfalso
        have hfc : (pushout C₁.inr C₂.inl).faceMap true i c
            = p₂⟪n⟫ (C₂.mid.faceMap true i c₂) := by
          rw [← hc₂, map_faceMap p₂ true i c₂]
        have hcross : p₁⟪n⟫ a'
            = p₂⟪n⟫ (C₂.mid.faceMap true i c₂) := ha''.trans hfc
        obtain ⟨y, hy₁, _hy₂⟩ :=
          Types.exists_of_isPullback (comp_isPullback_app C₁ C₂ n) a'
            (C₂.mid.faceMap true i c₂) hcross
        exact hdisj ⟨n, a'⟩ y hy₁ hSa
  | @trans x v w _hxv _hvw ihxv ihvw =>
      intro hPw
      exact ihxv (ihvw hPw)

/-- **The sink barrier (general form), dual to `pushout_inl_image_isSieve`.**  The
`p₂`-image of a cosieve `T` of `C₂.mid`, disjoint from the gluing image (`= srcImage
C₂ = image of C₂.inl`), is a cosieve of `W := pushout C₁.inr C₂.inl`. -/
theorem pushout_inr_image_isCosieve (C₁ : Cospan X Y) (C₂ : Cospan Y Z)
    (T : C₂.mid.TotalCell → Prop) (hT : IsCosieve C₂.mid T)
    (hdisj : ∀ (b : C₂.mid.TotalCell) (y : Y.cells b.1),
      C₂.inl⟪b.1⟫ y = b.2 → ¬ T b) :
    IsCosieve (pushout C₁.inr C₂.inl)
      (fun w => ∃ b, T b ∧ mapCell (pushout.inr C₁.inr C₂.inl) b = w) := by
  set p₁ := pushout.inl C₁.inr C₂.inl with hp₁
  set p₂ := pushout.inr C₁.inr C₂.inl with hp₂
  intro u w hreach
  induction hreach with
  | refl x => exact id
  | @source n i c =>
      -- `u = ⟨n, faceMap false i c⟩`, `w = ⟨n+1, c⟩`; cosieve: given `T u`, get `T w`.
      rintro ⟨b, hTb, hbv⟩
      obtain ⟨b', rfl, hb''⟩ := mapCell_eq_sigma p₂ b hbv
      rcases comp_cell_cases C₁ C₂ (n + 1) c with ⟨c₁, hc₁⟩ | ⟨c₂, hc₂⟩
      · -- `c = p₁.app c₁`: cross-gluing, vacuous.
        exfalso
        have hfc : (pushout C₁.inr C₂.inl).faceMap false i c
            = p₁⟪n⟫ (C₁.mid.faceMap false i c₁) := by
          rw [← hc₁, map_faceMap p₁ false i c₁]
        have hcross : p₂⟪n⟫ b'
            = p₁⟪n⟫ (C₁.mid.faceMap false i c₁) := hb''.trans hfc
        obtain ⟨y, _hy₁, hy₂⟩ :=
          Types.exists_of_isPullback (comp_isPullback_app C₁ C₂ n)
            (C₁.mid.faceMap false i c₁) b' hcross.symm
        exact hdisj ⟨n, b'⟩ y hy₂ hTb
      · -- `c = p₂.app c₂`: a genuine `C₂` step.
        have hfc : (pushout C₁.inr C₂.inl).faceMap false i c
            = p₂⟪n⟫ (C₂.mid.faceMap false i c₂) := by
          rw [← hc₂, map_faceMap p₂ false i c₂]
        have hbc : b' = C₂.mid.faceMap false i c₂ :=
          app_injective_of_mono p₂ n (hb''.trans hfc)
        subst hbc
        refine ⟨⟨n + 1, c₂⟩, ?_, ?_⟩
        · -- `T` cosieve: the source face reaches `c₂`, so push forward.
          exact hT _ _ (Reaches.source i c₂) hTb
        · rw [mapCell_mk]
          exact congrArg (Sigma.mk (n + 1)) hc₂
  | @target n i c =>
      -- `u = ⟨n+1, c⟩`, `w = ⟨n, faceMap true i c⟩`; given `T u`, get `T w`.
      rintro ⟨b, hTb, hbv⟩
      obtain ⟨b', rfl, hb''⟩ := mapCell_eq_sigma p₂ b hbv
      rcases comp_cell_cases C₁ C₂ (n + 1) c with ⟨c₁, hc₁⟩ | ⟨c₂, hc₂⟩
      · -- `c = p₁.app c₁`: cross-gluing, vacuous.
        exfalso
        have hcross : p₂⟪n + 1⟫ b'
            = p₁⟪n + 1⟫ c₁ := hb''.trans hc₁.symm
        obtain ⟨y, _hy₁, hy₂⟩ :=
          Types.exists_of_isPullback (comp_isPullback_app C₁ C₂ (n + 1)) c₁ b'
            hcross.symm
        exact hdisj ⟨n + 1, b'⟩ y hy₂ hTb
      · -- `c = p₂.app c₂`: a genuine `C₂` step.
        have hbc : b' = c₂ :=
          app_injective_of_mono p₂ (n + 1) (hb''.trans hc₂.symm)
        subst hbc
        refine ⟨⟨n, C₂.mid.faceMap true i b'⟩, ?_, ?_⟩
        · exact hT _ _ (Reaches.target i b') hTb
        · rw [mapCell_mk]
          exact congrArg (Sigma.mk n) (by rw [map_faceMap p₂ true i b', hc₂])
  | @trans x v w _hxv _hvw ihxv ihvw =>
      intro hPx
      exact ihvw (ihxv hPx)

/-! ### Assembling the composite cobordism

We feed the barrier lemmas the cobordism's own sieve/cosieve + leg-disjointness data,
after identifying `srcImage (comp)` with the `p₁`-image of `srcImage C₁` and
`sinkImage (comp)` with the `p₂`-image of `sinkImage C₂`. -/

/-- The composite source image is exactly the `p₁`-image of the first source image. -/
theorem comp_srcImage_eq (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    (C₁.comp C₂).srcImage
      = fun w => ∃ a, C₁.srcImage a ∧ mapCell (pushout.inl C₁.inr C₂.inl) a = w := by
  funext w
  simp only [Cospan.srcImage, Cospan.comp_inl]
  apply propext
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨mapCell C₁.inl x, ⟨x, rfl⟩, (mapCell_comp C₁.inl _ x).symm.trans hx⟩
  · rintro ⟨a, ⟨x, hx⟩, ha⟩
    exact ⟨x, (mapCell_comp C₁.inl _ x).trans (by rw [hx]; exact ha)⟩

/-- The composite sink image is exactly the `p₂`-image of the second sink image. -/
theorem comp_sinkImage_eq (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    (C₁.comp C₂).sinkImage
      = fun w => ∃ b, C₂.sinkImage b ∧ mapCell (pushout.inr C₁.inr C₂.inl) b = w := by
  funext w
  simp only [Cospan.sinkImage, Cospan.comp_inr]
  apply propext
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨mapCell C₂.inr z, ⟨z, rfl⟩, (mapCell_comp C₂.inr _ z).symm.trans hz⟩
  · rintro ⟨b, ⟨z, hz⟩, hb⟩
    exact ⟨z, (mapCell_comp C₂.inr _ z).trans (by rw [hz]; exact hb)⟩

/-- **M4b — the closure theorem.**  The pushout composite of two directed cobordisms
is again a directed cobordism `X ⇒c Z`, with underlying cospan the M2 composite
`W₁.toCospan.comp W₂.toCospan`. -/
noncomputable def DirectedCobordism.comp (W₁ : DirectedCobordism X Y)
    (W₂ : DirectedCobordism Y Z) : DirectedCobordism X Z where
  toCospan := W₁.toCospan.comp W₂.toCospan
  -- C1: M2.
  legsDisjoint := Cospan.LegsDisjoint.comp W₁.legsDisjoint W₂.legsDisjoint
  -- C2: the source sieve survives (barrier on the `p₁`/`C₁` side).
  srcSieve := by
    rw [Cospan.SrcSieve, comp_srcImage_eq]
    refine pushout_inl_image_isSieve W₁.toCospan W₂.toCospan
      W₁.toCospan.srcImage W₁.srcSieve ?_
    -- source/sink images of `W₁` are disjoint (`legsDisjoint`).
    rintro a y hy ⟨x, hx⟩
    obtain ⟨n, a'⟩ := a
    -- `hx : mapCell W₁.inl x = ⟨n, a'⟩`, `hy : W₁.inr y = a'`.
    obtain ⟨x', rfl, hx''⟩ := mapCell_eq_sigma W₁.inl x hx
    exact W₁.legsDisjoint x' y (hx''.trans hy.symm)
  -- C3: the sink cosieve survives (barrier on the `p₂`/`C₂` side).
  sinkCosieve := by
    rw [Cospan.SinkCosieve, comp_sinkImage_eq]
    refine pushout_inr_image_isCosieve W₁.toCospan W₂.toCospan
      W₂.toCospan.sinkImage W₂.sinkCosieve ?_
    rintro b y hy ⟨z, hz⟩
    obtain ⟨n, b'⟩ := b
    obtain ⟨z', rfl, hz''⟩ := mapCell_eq_sigma W₂.inr z hz
    -- `hy : W₂.inl y = b'`, `hz'' : W₂.inr z' = b'`; `legsDisjoint`.
    exact W₂.legsDisjoint y z' (hy.trans hz''.symm)
  -- C4 (source): push `W₁`'s source collar through `p₁`.
  srcCollar :=
    { collar := W₁.srcCollar.collar ≫ pushout.inl W₁.inr W₂.inl
      mono := mono_comp' W₁.srcCollar.mono (comp_pushout_inl_mono W₁.toCospan W₂.toCospan)
      endEq := by
        rw [Cospan.comp_inl, ← Category.assoc]
        congr 1
        exact W₁.srcCollar.endEq }
  -- C4 (sink): push `W₂`'s sink collar through `p₂`.
  sinkCollar :=
    { collar := W₂.sinkCollar.collar ≫ pushout.inr W₁.inr W₂.inl
      mono := mono_comp' W₂.sinkCollar.mono (comp_pushout_inr_mono W₁.toCospan W₂.toCospan)
      endEq := by
        rw [Cospan.comp_inr, ← Category.assoc]
        congr 1
        exact W₂.sinkCollar.endEq }

@[simp] theorem DirectedCobordism.comp_toCospan (W₁ : DirectedCobordism X Y)
    (W₂ : DirectedCobordism Y Z) :
    (W₁.comp W₂).toCospan = W₁.toCospan.comp W₂.toCospan := rfl

end PrecubicalSet
