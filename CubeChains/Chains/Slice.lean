import CubeChains.Chains.Correspondence
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Chains/Slice

`Ch K` as a subcategory of the slice `Over K.toPsh`: the inclusion `chToOver` and
when it is **fully faithful** — Faithful unconditionally, Full from injectivity on
vertices (`chToOver_full_of_vertexInj`), hence under `NonSelfLinked + AdmitsAltitude`.

**Layer:** Chains.  **Imports:** `Correspondence`, mathlib `Over`/`KanExtension`/`FullSubcategory`.
The in-repo exemplar of mathlib reuse (`Over`, Kan extension). Vertex-injectivity is
*strictly weaker* than the full `descent_mono`.

Working in the slice topos `Precubical / K` (here `Over K.toPsh`), `Ch K` is the
subcategory of **bi-pointed** serial wedges over `K`.  This file records the inclusion
functor `chToOver : Ch K ⥤ Over K.toPsh` and studies when it is **fully faithful** —
i.e. when a *not necessarily basepoint-preserving* wedge map over `K` is automatically
basepoint-preserving.

* **Faithful is unconditional** (`chToOver.Faithful`): a bi-pointed map is determined
  by its underlying presheaf map.
* **Full needs only that each chain's descent map is injective on vertices**
  (`chToOver_full_of_vertexInj`): then a map over `K` sends `init ↦ init`, `final ↦
  final` because both land on the unique vertex over `K.init` / `K.final`.
* In particular `NonSelfLinked + AdmitsAltitude ⟹ Full` (`chToOver_full`), via
  `descent_mono` (the descent map is mono, hence injective on every dimension, in
  particular on vertices).  Vertex-injectivity is **strictly weaker** than the full
  `descent_mono`, so full faithfulness does *not* need the side conditions in their
  full strength — only injectivity on `0`-cells.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace CubeChain

variable {K : BPSet}

/-- **The inclusion `Ch K ↪ Precubical / K`.**  A chain `⟨dims, map⟩` is sent to its
descent map `serialWedge dims ⟶ K`, viewed as an object of the slice over `K.toPsh`
(forgetting the bi-pointed structure); a chain morphism is sent to its underlying
presheaf map, which commutes over `K`. -/
noncomputable def chToOver : Ch K ⥤ Over K.toPsh where
  obj a := Over.mk a.map.hom
  map {a b} g := Over.homMk gᵂ (by
    change gᵂ ≫ b.map.hom = a.map.hom
    have h := congrArg BPSet.Hom.hom g.w
    rwa [comp_hom] at h)
  map_id a := by apply Over.OverMorphism.ext; simp
  map_comp f g := by apply Over.OverMorphism.ext; simp

/-- **Faithful (unconditional).**  A bi-pointed wedge map is determined by its
underlying presheaf map, so `chToOver` is faithful. -/
instance : (chToOver (K := K)).Faithful where
  map_injective {a b} {g₁ g₂} h :=
    ChainCat.hom_ext' (hom_ext (by simpa using congrArg (fun m => m.left) h))

/-- **Full from vertex-injectivity.**  If every chain's descent map is injective on
`0`-cells, then any presheaf map `serialWedge a.dims ⟶ serialWedge b.dims` over `K`
preserves `init`/`final` (both sides land on the unique vertex over `K.init`/`K.final`),
hence is bi-pointed.  So `chToOver` is full. -/
lemma chToOver_full_of_vertexInj
    (hinj : ∀ b : Ch K, Function.Injective (b.map.hom⟪0⟫)) :
    (chToOver (K := K)).Full where
  map_surjective {a b} h := by
    have hw : h.left ≫ b.map.hom = a.map.hom := Over.w h
    have hinit : h.left⟪0⟫ (⋁a.dims).init
        = (⋁b.dims).init := by
      apply hinj b
      have e : b.map.hom⟪0⟫
          (h.left⟪0⟫ (⋁a.dims).init) = K.init :=
        (NatTrans.comp_app_apply h.left b.map.hom (op ▫0)
            (⋁a.dims).init).symm.trans (by rw [hw]; exact a.map.app_init)
      rw [e, b.map.app_init]
    have hfinal : h.left⟪0⟫ (⋁a.dims).final
        = (⋁b.dims).final := by
      apply hinj b
      have e : b.map.hom⟪0⟫
          (h.left⟪0⟫ (⋁a.dims).final) = K.final :=
        (NatTrans.comp_app_apply h.left b.map.hom (op ▫0)
            (⋁a.dims).final).symm.trans (by rw [hw]; exact a.map.app_final)
      rw [e, b.map.app_final]
    refine ⟨{ φ := ⟨h.left, hinit, hfinal⟩
              w := by apply hom_ext; rw [comp_hom]; exact hw }, ?_⟩
    apply Over.OverMorphism.ext
    rfl

/-- **Full under `NonSelfLinked` + `AdmitsAltitude`.**  The descent map of every chain
is a monomorphism (`descent_mono`), hence injective on every dimension, in particular
on `0`-cells; so vertex-injectivity holds and `chToOver` is full. -/
lemma chToOver_full (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    (chToOver (K := K)).Full :=
  chToOver_full_of_vertexInj fun b =>
    (mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp (descent_mono h₁ h₂ b) (op ▫0))

/-- **`Ch K ↪ Precubical / K` is fully faithful** under `NonSelfLinked` +
`AdmitsAltitude`.  (Faithfulness is unconditional; only fullness uses the hypotheses,
and only through vertex-injectivity of descent maps.) -/
noncomputable def chToOverFullyFaithful (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    (chToOver (K := K)).FullyFaithful :=
  haveI := chToOver_full h₁ h₂
  Functor.FullyFaithful.ofFullyFaithful chToOver

/-! ### `AllCh K`: the wedge subcategory of the slice

`AllCh K` is the **full** subcategory of `Precubical/K` on the objects whose domain is a
serial wedge — i.e. *all* (not-necessarily-bi-pointed) cube chains over `K`.  Since it is
a full subcategory of the slice containing the image of `chToOver`, full faithfulness of
the inclusion `Ch K ↪ AllCh K` is **equivalent** to that of `Ch K ↪ Precubical/K`:
faithful unconditionally, full under vertex-injectivity (so under `NonSelfLinked +
AdmitsAltitude`).  No new hypotheses are needed — full faithfulness only sees hom-sets,
which a full subcategory shares with the ambient slice. -/

/-- The object property "the domain is a serial wedge", carving `AllCh K` out of the
slice `Precubical/K`. -/
def IsWedgeOver (K : BPSet) : ObjectProperty (Over K.toPsh) :=
  fun X => ∃ dims : List ℕ+, Nonempty (X.left ≅ (⋁dims).toPsh)

/-- **`AllCh K`** — the full subcategory of `Precubical/K` on the wedge-shaped objects
(all cube chains over `K`, basepoints not required). -/
abbrev AllCh (K : BPSet) := (IsWedgeOver K).FullSubcategory

/-- The inclusion `Ch K ↪ AllCh K`: `chToOver` corestricted to the wedge subcategory. -/
noncomputable abbrev chToAllCh : Ch K ⥤ AllCh K :=
  (IsWedgeOver K).lift chToOver fun a => ⟨a.dims, ⟨Iso.refl _⟩⟩

/-- **`Ch K ↪ AllCh K` is faithful (unconditional).** -/
instance : (chToAllCh (K := K)).Faithful := inferInstance

/-- **`Ch K ↪ AllCh K` is full** under `NonSelfLinked + AdmitsAltitude` — transferred
from `chToOver_full`, since `AllCh K` is a full subcategory of the slice. -/
theorem chToAllCh_full (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    (chToAllCh (K := K)).Full := by
  haveI := chToOver_full h₁ h₂
  infer_instance

/-- **`Ch K ↪ AllCh K` is fully faithful** under `NonSelfLinked + AdmitsAltitude`. -/
noncomputable def chToAllChFullyFaithful (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    (chToAllCh (K := K)).FullyFaithful :=
  haveI := chToAllCh_full h₁ h₂
  Functor.FullyFaithful.ofFullyFaithful chToAllCh

/-! ### The blind extension `F^` and its restriction back to `Ch K`

A functor `F : Ch K ⥤ Ch K` extends "blindly" to the slice by the **pointwise left
Kan extension** of `F ⋙ chToOver` along `chToOver`.  It always exists (`Over K.toPsh`
is cocomplete), and — because `chToOver` is fully faithful (`chToOverFullyFaithful`) —
its unit is an isomorphism, i.e. `F^` **restricts back** to `F`.  Both facts are
supplied directly by mathlib's pointwise-Kan-extension API
(`pointwiseLeftKanExtension`, `IsPointwiseLeftKanExtension.isIso_hom`). -/

/-- The **blind extension** `F^ : Precubical/K ⥤ Precubical/K` of a functor `F` on
`Ch K`: the pointwise left Kan extension of `F ⋙ chToOver` along `chToOver`.  It exists
unconditionally (the slice is cocomplete). -/
noncomputable def slan (F : Ch K ⥤ Ch K) : Over K.toPsh ⥤ Over K.toPsh :=
  (chToOver (K := K)).pointwiseLeftKanExtension (F ⋙ chToOver)

/-- The Kan-extension unit `F ⋙ chToOver ⟶ chToOver ⋙ F^`. -/
noncomputable def slanUnit (F : Ch K ⥤ Ch K) :
    F ⋙ chToOver ⟶ chToOver ⋙ slan F :=
  (chToOver (K := K)).pointwiseLeftKanExtensionUnit (F ⋙ chToOver)

/-- **The blind extension restricts back.**  Under `NonSelfLinked + AdmitsAltitude`
(so `chToOver` is fully faithful), the Kan-extension unit is an isomorphism:
`F^` agrees with `F` on `Ch K` (through `chToOver`).  This is mathlib's
`IsPointwiseLeftKanExtension.isIso_hom` for a fully faithful base functor. -/
theorem isIso_slanUnit (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (F : Ch K ⥤ Ch K) : IsIso (slanUnit F) := by
  haveI := chToOver_full h₁ h₂
  exact ((chToOver (K := K)).pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    (F ⋙ chToOver)).isIso_hom

end CubeChain
