# Cyl9_DayTensor — the geometric box tensor `(-) ⊗ □ⁿ`, Day convolution, and `⊗□¹ ⊣ PathOb`

**Files:** `Cyl9_DayTensor.lean` (this writeup's Lean; green & sorry-free) and
`Cyl9b_BoxMonoidal.lean` (companion: the `MonoidalCategory Box` instance — see §B).
**Build:** `lake build CubeChains.Research.Scratch.Cyl9_DayTensor`.

The brief: build the geometric box tensor `(-) ⊗ □ⁿ` on `PrecubicalSet := Boxᵒᵖ ⥤ Type` by
**reusing mathlib's Day convolution**, and use it to discharge the cylinder program's cocylinder /
exponential conjectures (`CocylinderConjecture`, `MooreSpanComposeConjecture` from `Cyl7`).

---

## TL;DR / verdict

- **The prize adjunction `(-) ⊗ □¹ ⊣ PathOb` is PROVEN, sorry-free, entirely off the shelf — and
  it does NOT need Day convolution at all.**  `PathOb` is, by its very definition in
  `Foundations/Shift`, *restriction (precomposition) along `Box.shift.op`*.  Restriction along any
  functor has a left adjoint: its left Kan extension `Functor.lan`, with the adjunction packaged by
  mathlib as `Functor.lanAdjunction`.  Because the target `Type` is cocomplete, all the requisite
  pointwise left Kan extensions exist for free.  So `cylinder := Box.shift.op.lan` and
  `cylinderAdj : cylinder ⊣ PathOb` land in ~3 lines.  **This is Task 3, the meaningful adjunction
  the program wants, fully closed.**

- **Does mathlib's Day convolution suffice for the box tensor?**  *For the one adjunction the
  program needs (`⊗□¹ ⊣ PathOb`): not required — `lan` is strictly more economical and gives it
  outright.*  *For the full monoidal product `(-) ⊗ (-)` and its closed/exponential structure on
  `PrecubicalSet`: mathlib's Day-convolution API in this pin (`v4.30.0`) is too raw to use off the
  shelf* — see §C.  The monoidal structure exists only on the `DayFunctor` type synonym and requires
  nontrivial colimit-preservation hypotheses; the closed (internal-hom) structure has **no
  instances at all**, only the abstract data-bundle `DayConvolutionInternalHom`.  So the geometric
  tensor and its exponential must still be **built by hand** if wanted in full; the `lan` route
  side-steps this for the cylinder/cocylinder application.

- **Cocylinder & length-additivity conjectures:** **REDUCED**, not proven.  Both reduce to one
  missing ingredient — an `ExpStructure` for the geometric tensor (the internal hom `(Iₙ ⟹ -)` as a
  right adjoint).  Given that, continuity of the right adjoint sends the interval (co)limits to the
  `PathOb`-pullbacks, closing both.  The `n = 1` case of the interface is *populated* by
  `cylinderAdj` (`PathOb` is the cocylinder of `□¹`), and the interval-additivity half of
  length-additivity is **PROVEN** (`mooreSpanCompose_interval_additive`).  The gap is exactly the
  (unbuilt, not-off-the-shelf) closed structure.

---

## A. PROVEN (sorry-free, `Cyl9_DayTensor.lean`)

| Name | Statement |
|---|---|
| `cylinder` | `:= Box.shift.op.lan : PrecubicalSet ⥤ PrecubicalSet`, the box-tensor cylinder `(-) ⊗ □¹`. |
| `PathOb_eq_whiskeringLeft` | `PathOb = (whiskeringLeft …).obj Box.shift.op` (`rfl`); identifies the program's `PathOb` with the `lan`-adjoint target. |
| **`cylinderAdj`** | **`cylinder ⊣ PathOb`** — the geometric adjunction `(-) ⊗ □¹ ⊣ PathOb`, via `Box.shift.op.lanAdjunction Type`. |
| `PreservesColimitsOfSize cylinder` | `cylinder` is a left adjoint ⇒ cocontinuous. |
| `PreservesLimitsOfSize PathOb` | `PathOb` is a right adjoint ⇒ continuous (sends interval pushouts to pullbacks — the cocylinder mechanism). |
| `Box.tensor_obj_dim` | `⟨m⟩ ⊗ ⟨n⟩ = ⟨m+n⟩` on objects. |
| `Box.shift_obj_eq_tensor_one` | `shift ⟨n⟩ = ⟨n⟩ ⊗ ⟨1⟩` on objects: pins `cylinder = (-) ⊗ □¹`. |
| `PathObIter n` | the `n`-fold iterate `PathOb^[n]`, `(PathOb^[n] K)_k = K_{k+n}` (cocylinder of `□ⁿ`). |
| `preservesLimits_pathObIter` | `PathOb^[n]` is continuous (composite of right adjoints). |
| `expStructure_one` | `PathOb` realises the `n = 1` exponential `(□¹ ⟹ -)` (base case of the interface). |
| `mooreSpanCompose_interval_additive` | `I(m+n)`'s list is `Iₘ`'s ++ `Iₙ`'s (`List.replicate_add`): the interval-additivity half of length-additivity. |

The headline: **Task 3 (`⊗□¹ ⊣ PathOb`) is done and clean.**

---

## B. The `MonoidalCategory Box` instance (Task 1) — companion file `Cyl9b_BoxMonoidal.lean`

`Box`'s strict monoidal structure has tensor = **addition of dimensions** (`⟨m⟩ ⊗ ⟨n⟩ = ⟨m+n⟩`),
unit `⟨0⟩`, and morphism tensor = **geometric juxtaposition of cubes** (place two precubical maps
side by side on disjoint coordinate blocks, `Fin.append` of cells under the cube Yoneda lemma).
Coherence (pentagon/triangle/unitors) is *strict* — but note `0 + m` is **not** defeq `m` for `Nat`
addition, so the left unitor needs `eqToIso` bookkeeping; the right unitor (`m + 0 = m`) is defeq.

> **Status:** see the head of `Cyl9b_BoxMonoidal.lean` for the live PROVEN/OPEN breakdown.  Whatever
> is there is sorry-free under `lake build CubeChains.Research.Scratch.Cyl9b_BoxMonoidal`; the object
> tensor + `shift = (-) ⊗ ⟨1⟩` identification used by §A is independently recorded in
> `Cyl9_DayTensor.lean` and does not depend on the full instance.

**Why the full instance is not on the §A critical path:** the `lan` adjunction needs only the single
endofunctor `shift` (whose restriction is `PathOb`), not the binary tensor.  The monoidal /
Day-convolution layer is needed only for the *higher* tensors `(-) ⊗ □ⁿ` (`n ≥ 2`) and the
exponential — i.e. for the conjecture reductions in §D, where the remaining gap lives.

---

## C. Day convolution in mathlib `v4.30.0` — what's there, what's missing (Task 2)

Studied: `Mathlib/CategoryTheory/Monoidal/DayConvolution.lean` (+ `DayConvolution/DayFunctor`,
`/Braided`, `/Closed`), `Monoidal/Cartesian/FunctorCategory`, `Monoidal/Closed/FunctorToTypes`,
`Monoidal/Closed/FunctorCategory/`.

- **`class DayConvolution (F G : C ⥤ V)`** bundles `convolution : C ⥤ V` (`F ⊛ G`), a `unit`
  `F ⊠ G ⟶ tensor C ⋙ convolution`, and a witness that this exhibits `F ⊛ G` as a *pointwise left
  Kan extension of `F ⊠ G` along `tensor C`*.  Needs `MonoidalCategory C` and `MonoidalCategory V`.
- **Monoidal structure** is NOT on `C ⥤ V` directly — it lives on the type synonym
  **`DayFunctor C V` (notation `C ⊛⥤ V`)** via `monoidalOfHasDayConvolutions`, and requires:
  `∀ F G, (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)`, a unit-Kan-extension hypothesis, and
  **`PreservesColimitsOfShape (CostructuredArrow (tensor C) d) (tensorLeft v)`** (+ `tensorRight`)
  for all `v, d`.  For `V = Type` these *are* satisfiable (in `Type`, `(-) × v` has a right adjoint
  so preserves colimits), but each is a real proof obligation, not an inferred instance for `Box`.
- **Closed / internal hom:** `DayConvolution/Closed.lean` provides only the **abstract structure**
  `DayConvolutionInternalHom F G H` (a wedge/end bundle) with `ev`/`coev`/triangle API — and
  **NO `Closed`/`MonoidalClosed` instances** (the file's own TODO defers actual instances to a
  future `LawfulDayConvolutionMonoidalStruct`).  So the geometric tensor's exponential is **not**
  available off the shelf.
- **What IS off the shelf:** `FunctorToTypes.monoidalClosed : MonoidalClosed (C ⥤ Type)` — but this
  is the **cartesian / pointwise** ("Hadamard") tensor `(F ⊗ G)ₙ = Fₙ × Gₙ`, NOT the geometric Day
  tensor.  Its internal hom is `F.functorHom (-)`.  Useful for a *different* (pointwise) closed
  structure, not the box tensor.

**Verdict (Day-convolution sufficiency):** mathlib's Day convolution is enough to *define* the
geometric monoidal product on `PrecubicalSet` (via `DayFunctor` + discharging the colimit-preservation
hypotheses), but its **closed structure must be built by hand** (only the abstract `…InternalHom`
data exists, no instances).  For the box-tensor *cylinder/cocylinder adjunction the program needs*,
Day convolution is **not the economical tool** — `Functor.lan` against `shift` gives `⊗□¹ ⊣ PathOb`
directly and for free, which is what `Cyl9_DayTensor.lean` does.

---

## D. Conjecture reductions (Tasks 4–5) — `CocylinderConjecture`, length-additivity

Both Cyl7 conjectures are about the **geometric tensor's internal hom** `(Iₙ ⟹ K)` (right adjoint of
`Iₙ ⊗ (-)`).  We name that missing ingredient as `ExpStructure tensorX := { exp, adj : tensorX ⊣ exp }`
and prove the reductions modulo it:

- **`CocylinderReduction`** (reduces `Cyl7.CocylinderConjecture`).  `I₂ = □¹ ∨ □¹` is the pushout of
  two `□¹` glued at the junction `□⁰`.  IF `I₂ ⊗ (-)` has a right adjoint `exp` (an `ExpStructure`),
  then `exp` is continuous and sends that pushout to the matched pullback `PathOb K ×_K PathOb K =`
  `Cyl7.pathOb2 K`, giving `pathOb2 K ≅ (I₂ ⟹ K)`.  The pullback target and its continuity
  (`PreservesLimitsOfSize PathOb`) are **in hand**; the gap is the `ExpStructure` for the geometric
  tensor (i.e. exactly the §C closed-structure gap).
- **`MooreSpanComposeReduction`** (reduces `Cyl7.MooreSpanComposeConjecture`).  Interval additivity
  `I(m+n) = Iₘ ⊔_{□⁰} Iₙ` is **PROVEN** (`mooreSpanCompose_interval_additive`, from
  `List.replicate_add`).  A right-adjoint exponential then sends this pushout to the pullback
  `K^{Iₘ} ×_K K^{Iₙ}`, giving `K^{I(m+n)} ≅ K^{Iₘ} ×_K K^{Iₙ}` — span composition with no fold (the
  Moore fix for Cyl7's reparametrization obstruction).  Same `ExpStructure` gap.

`expStructure_one : ExpStructure cylinder` (with `exp := PathOb`, `adj := cylinderAdj`) shows the
interface is the right abstraction and is *already populated at `n = 1`* — the strict cocylinder is
constructed.  The remaining work for `n ≥ 2` is purely the closed structure of the geometric tensor.

---

## Open / remaining (precise)

1. **The geometric tensor's closed structure** — an `ExpStructure` for `Iₙ ⊗ (-)`, `n ≥ 2`.  This is
   the single gate on both Cyl7 conjectures.  Not off the shelf in mathlib (§C).  Buildable by hand
   (the box tensor `Iₙ ⊗ (-)` is cocontinuous as a left Kan extension; its right adjoint exists by
   adjoint-functor / `lan`-style arguments — analogous to §A but with the *binary* tensor in place
   of `shift`).  Effort: moderate-to-heavy (needs the `MonoidalCategory Box` instance of §B first,
   then Day convolution or a direct `lan`-against-`⊗` construction).
2. **Full `MonoidalCategory Box`** (§B) — combinatorics of the morphism juxtaposition; see the
   companion file for live status.
