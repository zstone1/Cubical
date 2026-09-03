import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Concurrency.Merge.MergeGenerate
import CubeChains.Precubical.Segal.Split
import Mathlib.CategoryTheory.Localization.Prod

/-!
# Concurrency/Merge/WedgeSplit — chains of a wedge are pairs of chains

`chConcat` appends the beads, and a refinement of a concatenation respects the junction, so it is
an equivalence `Ch X × Ch Y ≌ Ch (X ∨ Y)`.  Under it `W` on the wedge is the product of the `W`s
on the factors: `crossPerm` is block-diagonal over a concatenation (`crossPerm_chConcat`) and a
block-diagonal permutation is trivial only when both blocks are.

`Localization.Prod` is imported for its `Functor.IsLocalization.prod` instance, which
`(W X).IsMultiplicative` discharges: that instance *is* B1, and needs no wrapper.
-/

open CategoryTheory CategoryTheory.MonoidalCategory BPSet CubeChains

namespace ChainCat

variable {X Y : BPSet}

/-! ## `chConcat` is an equivalence

`Faithful` is already known.  Fullness is the junction-respecting statement: the source of a wedge
map splits wherever its target does (`splitTarget`), and a chain of `X ∨ Y` splits in only one way
(`splitObj`), so the two splittings agree and the map is a concatenation. -/

/-- **A map of concatenations is a concatenation of maps.** -/
theorem chConcat_full (h : (X ∨ Y).AdmitsAltitude) : (chConcat X Y).Full where
  map_surjective {ab ab'} F := by
    obtain ⟨a, b⟩ := ab
    obtain ⟨a', b'⟩ := ab'
    obtain ⟨ad₁, ad₂, φ₁, φ₂, hd, hφ⟩ := splitTarget (Hom.φ F)
    have hobj : (chConcat X Y).obj (a, b)
        = (chConcat X Y).obj (⟨ad₁, φ₁ ≫ a'.map⟩, ⟨ad₂, φ₂ ≫ b'.map⟩) := by
      refine Obj.mk_eq_mk hd ((F.w).symm.trans ?_)
      rw [hφ]
      exact (Category.assoc _ _ _).trans
        (congrArg (eqToHom (congrArg BPSet.serialWedge hd) ≫ ·)
          (tensorTransport_comp_tensorHom (serialWedgeAppend ad₁ ad₂)
            (serialWedgeAppend a'.dims b'.dims) φ₁ φ₂ a'.map b'.map))
    have hsplit := congrArg (splitObj h) hobj
    rw [splitObj_chConcat_obj h, splitObj_chConcat_obj h] at hsplit
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hsplit
    refine ⟨(⟨φ₁, rfl⟩, ⟨φ₂, rfl⟩), hom_ext' ?_⟩
    rw [chConcat_map_φ, hφ]
    rfl

/-- Every chain of a wedge is a concatenation — `splitObj`, read as essential surjectivity. -/
theorem chConcat_essSurj (h : (X ∨ Y).AdmitsAltitude) : (chConcat X Y).EssSurj where
  mem_essImage c := ⟨splitObj h c, ⟨eqToIso (chConcat_obj_splitObj h c)⟩⟩

/-- **`Ch X × Ch Y ≌ Ch (X ∨ Y)`.**  `AdmitsAltitude` is not an extra assumption in practice:
`serialWedge_admitsAltitude` discharges it for every wedge of serial wedges. -/
noncomputable def chConcatEquiv (h : (X ∨ Y).AdmitsAltitude) : Ch X × Ch Y ≌ Ch (X ∨ Y) :=
  haveI := chConcat_full h
  haveI := chConcat_essSurj h
  haveI : (chConcat X Y).IsEquivalence := { }
  (chConcat X Y).asEquivalence

/-- The wedge of two serial wedges needs no hypothesis. -/
noncomputable def serialChConcatEquiv (d e : List ℕ+) :
    Ch (⋁d) × Ch (⋁e) ≌ Ch (⋁d ∨ ⋁e) :=
  chConcatEquiv (wedge2_admitsAltitude (serialWedge_admitsAltitude d)
    (serialWedge_admitsAltitude e))

/-! ## `W` splits with the chains -/

/-- **A concatenated map is inert exactly when both halves are.** -/
theorem W_chConcat_iff {X Y : BPSet} {ab ab' : Ch X × Ch Y} (fg : ab ⟶ ab') :
    W (X ∨ Y) ((chConcat X Y).map fg) ↔ W X fg.1 ∧ W Y fg.2 := by
  rw [W_iff_crossPerm_eq_one (dimSum_append ab.1.dims ab.2.dims), crossPerm_chConcat,
    permSum_eq_one_iff, ← W_iff_crossPerm_eq_one rfl, ← W_iff_crossPerm_eq_one rfl]

/-- **`W` on a wedge is the product of the `W`s on the factors** — what `IsLocalization.prod`
consumes. -/
theorem W_prod_eq_inverseImage_chConcat (X Y : BPSet) :
    (W X).prod (W Y) = (W (X ∨ Y)).inverseImage (chConcat X Y) :=
  MorphismProperty.ext _ _ fun _ _ fg => (W_chConcat_iff fg).symm

end ChainCat
