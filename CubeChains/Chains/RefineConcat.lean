import CubeChains.Chains.RefineFunctor
import CubeChains.Cylinder.Cylinder

/-!
# Chains/RefineConcat

Concatenation and left-whiskering in the refinement category:

* `RefineObj.append` (+ `_cubes`/`ext''`/`append_assoc`) — object-level concatenation;
* `appendRefinement`/`appendIncl`/`ChainRefine.append` — morphism-level concatenation;
* `RefineObj.appendLeft` — the left-whiskering functor (prepend a fixed prefix chain), with
  the `HEq` seam helpers its functor laws need.

Unlike the wedge-map `Ch` — whose concatenation needs the Segal pushout machinery
(`concatWedgeMap`, `Chains/Segal.lean`) — concatenation here is **literally list append**:
`isCubeChain_append` splices the chain proofs, and a `ChainRefine` morphism is index-keyed
reindexing + per-cube inclusion data, so two morphisms concatenate by offsetting the second
block's indices.
-/

open CategoryTheory Opposite

namespace CubeChain

variable {K : BPSet}

/-- **Object-level concatenation of refinement chains.**  Append the cube lists; the spliced
chain proof is `isCubeChain_append`.  (`a ⇝ m` then `m ⇝ b` gives `a ⇝ b`.) -/
def RefineObj.append {a m b : K.cells 0}
    (x : RefineObj (K := K) a m) (y : RefineObj (K := K) m b) : RefineObj (K := K) a b where
  cubes := x.cubes ++ y.cubes
  isChain := isCubeChain_append x.isChain y.isChain

@[simp] theorem RefineObj.append_cubes {a m b : K.cells 0}
    (x : RefineObj (K := K) a m) (y : RefineObj (K := K) m b) :
    (x.append y).cubes = x.cubes ++ y.cubes := rfl

/-- A refinement object is determined by its cube list (`isChain` is a `Prop`); local copy of
`Correspondence.RefineObj.ext'` (not imported here). -/
theorem RefineObj.ext'' {a b : K.cells 0} {x y : RefineObj (K := K) a b}
    (h : x.cubes = y.cubes) : x = y := by
  obtain ⟨xc, xh⟩ := x; obtain ⟨yc, _⟩ := y; subst h; rfl

/-- **Associativity of refinement-chain concatenation** (on the nose, `isChain` being a `Prop`):
`(x.append y).append z = x.append (y.append z)`.  This is the single object bridge the
list-indexed staircase fold reassociates `.append` by (`eqToHom` of it, promoted through
`FreeGroupoid.of`). -/
theorem RefineObj.append_assoc {a m₁ m₂ b : K.cells 0}
    (x : RefineObj (K := K) a m₁) (y : RefineObj (K := K) m₁ m₂) (z : RefineObj (K := K) m₂ b) :
    (x.append y).append z = x.append (y.append z) :=
  RefineObj.ext'' (by simp [RefineObj.append, List.append_assoc])

/-! ### Morphism-level concatenation

A `ChainRefine` on appended chains is the disjoint union of the two component refinements:
index `i` in the first block uses `f`, in the second block uses `g` offset by the first
refined block's length — combinatorially, over raw `++` lists, rather than via Segal
pushouts. -/

/-- The reindexing of the concatenation: `Fin.addCases` of `f.refinement` (cast into the left
block of `x' ++ y'`) and `g.refinement` (cast into the right block), under the
`List.length_append` casts. -/
def appendRefinement
    {x x' y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length) :
    Fin (x ++ y).length → Fin (x' ++ y').length := fun i =>
  Fin.cast (List.length_append ..).symm
    (Fin.addCases
      (fun a => (rf a).castAdd y'.length)
      (fun b => (rg b).natAdd x'.length)
      (Fin.cast (List.length_append ..) i))

/-- The `ℕ`-value of `appendRefinement` at an index in the **left** block (`i.val < x.length`)
is the value of `rf` there. -/
theorem appendRefinement_val_left
    {x x' y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length)
    (i : Fin (x ++ y).length) (hi : (i : ℕ) < x.length) :
    (appendRefinement rf rg i : ℕ) = (rf ⟨i, hi⟩ : ℕ) := by
  simp only [appendRefinement, Fin.val_cast]
  rw [show Fin.cast (List.length_append ..) i
        = Fin.castAdd y.length ⟨i, hi⟩ from by apply Fin.ext; simp,
    Fin.addCases_left]
  simp

/-- The `ℕ`-value of `appendRefinement` at an index in the **right** block
(`x.length ≤ i.val`) is `x'.length` plus the value of `rg` there. -/
theorem appendRefinement_val_right
    {x x' y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length)
    (i : Fin (x ++ y).length) (hi : x.length ≤ (i : ℕ))
    (hi' : (i : ℕ) - x.length < y.length) :
    (appendRefinement rf rg i : ℕ) = x'.length + (rg ⟨(i : ℕ) - x.length, hi'⟩ : ℕ) := by
  simp only [appendRefinement, Fin.val_cast]
  rw [show Fin.cast (List.length_append ..) i
        = Fin.natAdd x.length ⟨(i : ℕ) - x.length, hi'⟩ from by apply Fin.ext; simp; omega,
    Fin.addCases_right]
  simp

/-- The left-block `.get` of an append (with the `length_append` cast). -/
theorem get_append_castAdd {l l' : List (Σ n : ℕ+, K.cells (n : ℕ))} (i : Fin l.length) :
    (l ++ l').get (Fin.cast (List.length_append ..).symm (i.castAdd l'.length)) = l.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left] <;> simp

/-- The right-block `.get` of an append (with the `length_append` cast). -/
theorem get_append_natAdd {l l' : List (Σ n : ℕ+, K.cells (n : ℕ))} (i : Fin l'.length) :
    (l ++ l').get (Fin.cast (List.length_append ..).symm (i.natAdd l.length)) = l'.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_right] <;> simp

/-- The per-cube inclusion of the concatenation, as a *named* `Fin.addCases` (so the
`inclSpec` proof can rewrite it by `Fin.addCases_left/right`): each cube keeps its own block's
`incl`, bridged by the `get_append_*` `eqToHom` transports. -/
noncomputable def appendIncl {a m b : K.cells 0}
    {x x' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (i : Fin (x ++ y).length) :
    ▫(((x ++ y).get i).1 : ℕ) ⟶
      ▫(((x' ++ y').get (appendRefinement f.refinement g.refinement i)).1 : ℕ) :=
  Fin.addCases
    (motive := fun i₀ =>
      ▫(((x ++ y).get (Fin.cast (List.length_append ..).symm i₀)).1 : ℕ) ⟶
        ▫(((x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm i₀))).1 : ℕ))
    (fun ia =>
      eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ)) (get_append_castAdd ia))
        ≫ f.incl ia
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ))
            ((get_append_castAdd (f.refinement ia)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))))
    (fun ib =>
      eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ)) (get_append_natAdd ib))
        ≫ g.incl ib
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ))
            ((get_append_natAdd (g.refinement ib)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))))
    (Fin.cast (List.length_append ..) i)

/-- `appendIncl` reduces on a **left**-block index `i.castAdd` to `f`'s inclusion (the cast
inside `appendIncl` collapses, then `Fin.addCases_left` fires). -/
theorem appendIncl_castAdd {a m b : K.cells 0}
    {x x' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (ia : Fin x.length) :
    appendIncl f g (Fin.cast (List.length_append ..).symm (ia.castAdd y.length))
      = eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ)) (get_append_castAdd ia))
        ≫ f.incl ia
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ))
            ((get_append_castAdd (f.refinement ia)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))) := by
  rw [appendIncl]
  simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_left]

/-- `appendIncl` reduces on a **right**-block index `i.natAdd` to `g`'s inclusion. -/
theorem appendIncl_natAdd {a m b : K.cells 0}
    {x x' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (ib : Fin y.length) :
    appendIncl f g (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
      = eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ)) (get_append_natAdd ib))
        ≫ g.incl ib
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => ▫(c.1 : ℕ))
            ((get_append_natAdd (g.refinement ib)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))) := by
  rw [appendIncl]
  simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_right]

/-- The block-wise `inclSpec` of the concatenation, proved by `Fin.addCases` on the casted
index: on each branch `appendIncl` reduces (`appendIncl_castAdd`/`_natAdd`), the `.get`s reduce
(`get_append_*`), and the goal is `f`/`g`'s own `inclSpec` modulo the `eqToHom` transports
(`map_eqToHom_op_cell`). -/
theorem appendInclSpec {a m b : K.cells 0}
    {x x' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (i : Fin (x ++ y).length) :
    ((x ++ y).get i).2
      = K.toPsh.map (appendIncl f g i).op
        ((x' ++ y').get (appendRefinement f.refinement g.refinement i)).2 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
    ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
  induction j using Fin.addCases with
  | left ia =>
    -- the source/target cube cells are `x.get ia`, `x'.get (f.refinement ia)`.
    have hsrc := get_append_castAdd (l := x) (l' := y) ia
    have htgt : (x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm (ia.castAdd y.length)))
        = x'.get (f.refinement ia) := by
      rw [show appendRefinement f.refinement g.refinement
            (Fin.cast (List.length_append ..).symm (ia.castAdd y.length))
          = Fin.cast (List.length_append ..).symm ((f.refinement ia).castAdd y'.length) from by
          apply Fin.ext; rw [appendRefinement_val_left _ _ _ (by simp)]; simp]
      exact get_append_castAdd (f.refinement ia)
    rw [appendIncl_castAdd f g ia, op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp,
      types_comp_apply, types_comp_apply,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp htgt).2, ← f.inclSpec ia,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp hsrc).2.symm]
  | right ib =>
    have hsrc := get_append_natAdd (l := x) (l' := y) ib
    have htgt : (x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm (ib.natAdd x.length)))
        = y'.get (g.refinement ib) := by
      rw [show appendRefinement f.refinement g.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
          = Fin.cast (List.length_append ..).symm ((g.refinement ib).natAdd x'.length) from by
          apply Fin.ext; rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp]
      exact get_append_natAdd (g.refinement ib)
    rw [appendIncl_natAdd f g ib, op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp,
      types_comp_apply, types_comp_apply,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp htgt).2, ← g.inclSpec ib,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp hsrc).2.symm]

/-- **Morphism-level concatenation of refinements.**  Given `f : ChainRefine a m x x'` and
`g : ChainRefine m b y y'`, splice them to a refinement of the appended chains
`x ++ y ⟶ x' ++ y'` (over `a, b`): the reindexing is `appendRefinement`, each cube keeps its
own block's inclusion (`appendIncl`, bridged by the `get_append_*` `eqToHom` transports), and
`inclSpec`/monotonicity hold block-wise. -/
noncomputable def ChainRefine.append {a m b : K.cells 0}
    {x x' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') :
    ChainRefine a b (x ++ y) (x' ++ y') where
  chainx := isCubeChain_append f.chainx g.chainx
  chainy := isCubeChain_append f.chainy g.chainy
  refinement := appendRefinement f.refinement g.refinement
  refinementMono := by
    intro i j hij
    have hijn : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
    rw [Fin.le_def]
    by_cases hj : (j : ℕ) < x.length
    · -- both in the left block (`i ≤ j < x.length`); use `f` monotone.
      have hi : (i : ℕ) < x.length := lt_of_le_of_lt hijn hj
      rw [appendRefinement_val_left _ _ i hi, appendRefinement_val_left _ _ j hj]
      exact Fin.le_def.mp (f.refinementMono ⟨i, hi⟩ ⟨j, hj⟩ (by rw [Fin.le_def]; exact hijn))
    · -- `j` in the right block; `appendRefinement j ≥ x'.length`.
      rw [not_lt] at hj
      have hj' : (j : ℕ) - x.length < y.length := by have := j.isLt; simp at this; omega
      rw [appendRefinement_val_right _ _ j hj hj']
      by_cases hi : (i : ℕ) < x.length
      · -- `i` left, `j` right: left value `< x'.length ≤ right value`.
        rw [appendRefinement_val_left _ _ i hi]
        exact le_trans (Nat.le_of_lt (f.refinement ⟨i, hi⟩).isLt) (Nat.le_add_right _ _)
      · -- both right; use `g` monotone.
        rw [not_lt] at hi
        have hi' : (i : ℕ) - x.length < y.length := by have := i.isLt; simp at this; omega
        rw [appendRefinement_val_right _ _ i hi hi']
        have : (⟨(i : ℕ) - x.length, hi'⟩ : Fin y.length) ≤ ⟨(j : ℕ) - x.length, hj'⟩ := by
          rw [Fin.le_def]; simp only []; omega
        exact Nat.add_le_add_left (Fin.le_def.mp (g.refinementMono _ _ this)) _
  incl := appendIncl f g
  inclSpec := appendInclSpec f g

/-! ### Left-whiskering: prepend a fixed chain (the per-block promotion functor)

Fixing a prefix chain `pre : RefineObj a m`, post-composing `pre.append (-) : RefineObj m b ⥤
RefineObj a b` is a functor: on morphisms it is `ChainRefine.append (𝟙 pre) g` (identity on the
fixed prefix, `g` on the variable tail).  `FreeGroupoid.map` of it promotes a *local* per-block
sweep up to the d-path groupoid.

The morphism map is `RefineObj.appendLeftMap`; the functor laws `map_id`/`map_comp` are
discharged via `ChainRefine.ext` over the `appendIncl`-`Fin.addCases` transports (the
reindexings collapse to the identity/composite definitionally). -/

/-- The value of `appendRefinement id rg` is `rg` offset, computed pointwise (the prefix block
is fixed: `id` on the first `x.length` indices). -/
theorem appendRefinement_id_left {x y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (rg : Fin y.length → Fin y'.length) (i : Fin (x ++ y).length) :
    (appendRefinement (id : Fin x.length → Fin x.length) rg i : ℕ)
      = if h : (i : ℕ) < x.length then (i : ℕ)
        else x.length + (rg ⟨(i : ℕ) - x.length, by
          have := i.isLt
          have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
          omega⟩ : ℕ) := by
  by_cases h : (i : ℕ) < x.length
  · rw [dif_pos h, appendRefinement_val_left _ _ i h]; rfl
  · rw [dif_neg h]
    have hi' : (i : ℕ) - x.length < y.length := by
      have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
      omega
    rw [appendRefinement_val_right _ _ i (by omega) hi']

/-- **Left-whiskering on morphisms.**  Prepend the identity on the fixed prefix `pre` to a tail
refinement `g : y₁ ⟶ y₂`. -/
noncomputable def RefineObj.appendLeftMap {a m b : K.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    pre.append y₁ ⟶ pre.append y₂ :=
  ChainRefine.append (𝟙 pre) g

/-- The prefix-whiskering reindexing of the **identity** tail is the identity. -/
theorem appendRefinement_id_id {x y : List (Σ n : ℕ+, K.cells (n : ℕ))} :
    appendRefinement (id : Fin x.length → Fin x.length) (id : Fin y.length → Fin y.length)
      = id := by
  funext i
  apply Fin.ext
  rw [appendRefinement_id_left]
  by_cases h : (i : ℕ) < x.length
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; simp only [id_eq]
    have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
    omega

/-- The prefix-whiskering reindexing distributes over composition of the tail (the
`refineCategory` composition `g₂.refinement ∘ g₁.refinement`). -/
theorem appendRefinement_id_comp {x y y' y'' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (rg₁ : Fin y.length → Fin y'.length) (rg₂ : Fin y'.length → Fin y''.length) :
    appendRefinement (id : Fin x.length → Fin x.length) (rg₂ ∘ rg₁)
      = appendRefinement (id : Fin x.length → Fin x.length) rg₂
        ∘ appendRefinement (id : Fin x.length → Fin x.length) rg₁ := by
  funext i
  apply Fin.ext
  -- abbreviate the inner whiskering and its value (via `appendRefinement_id_left`).
  set j := appendRefinement (id : Fin x.length → Fin x.length) rg₁ i with hj
  have hjv := appendRefinement_id_left (x := x) rg₁ i
  rw [← hj] at hjv
  by_cases h : (i : ℕ) < x.length
  · -- left block: LHS `= i`; inner `j` also `= i < x.length`, outer `= j = i`.
    have hji : (j : ℕ) = (i : ℕ) := by rw [hjv, dif_pos h]
    rw [Function.comp_apply, appendRefinement_id_left, dif_pos h, ← hj, appendRefinement_id_left,
      dif_pos (by rw [hji]; exact h), hji]
  · -- right block: LHS `= x.length + rg₂ (rg₁ (i-x.length))`; outer of inner agrees.
    have hi' : (i : ℕ) - x.length < y.length := by
      have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
      omega
    -- inner `j` lands in the right block of `x ++ y'` at offset `rg₁ (i-x.length)`.
    have hjge : ¬ (j : ℕ) < x.length := by
      rw [hjv, dif_neg h]; omega
    have hjsub : (j : ℕ) - x.length = (rg₁ ⟨(i : ℕ) - x.length, hi'⟩ : ℕ) := by
      rw [hjv, dif_neg h]; omega
    rw [Function.comp_apply, appendRefinement_id_left, dif_neg h, ← hj, appendRefinement_id_left,
      dif_neg hjge]
    -- `x.length + ↑((rg₂∘rg₁)⟨i-x.length⟩) = x.length + ↑(rg₂⟨j-x.length⟩)`; the `Fin` args agree.
    congr 1
    exact congrArg (fun z : Fin y'.length => (rg₂ z : ℕ)) (Fin.ext hjsub.symm)

/-! ### The left-whiskering functor

Assembling `appendLeftMap` into a genuine `Functor`.  The two functor laws are proved as
plain morphism equalities by `ChainRefine.ext`: the reindexings of `map_id`/`map_comp` are
*not* definitionally `id`/`∘` (they route through `Fin.addCases`/`Fin.cast`), so the
reindexing halves are `appendRefinement_id_id`/`appendRefinement_id_comp`, and the inclusion
halves are `HEq`s reduced branch-wise via `appendIncl_castAdd`/`_natAdd`.

The `incl`-`HEq` is reduced to a *pointwise equality* via `incl_heq_of_index_eq`: when two
refinements `f g` of the SAME pair of chains have reindexings related by `hr : f.ref = g.ref`,
their inclusion families are `HEq` iff they agree after the canonical `eqToHom` transport of
`hr` (the `subst`-based `incl_index_eq` of `RefineFunctor.lean`, here over `f.ref i = g.ref i`).
Both functor laws are between refinements of the same chains, so this applies. -/

/-- The identity refinement's reindexing is `id` (definitional unfold of `refineCategory.id`). -/
theorem refine_id_refinement {a b : K.cells 0} (x : RefineObj (K := K) a b) :
    (𝟙 x : x ⟶ x).refinement = id := rfl

/-- The identity refinement's inclusion is `𝟙` (definitional unfold of `refineCategory.id`). -/
theorem refine_id_incl {a b : K.cells 0} (x : RefineObj (K := K) a b)
    (i : Fin x.cubes.length) : (𝟙 x : x ⟶ x).incl i = 𝟙 _ := rfl

/-- A composite refinement's reindexing is the composite of reindexings. -/
theorem refine_comp_refinement {a b : K.cells 0} {x y z : RefineObj (K := K) a b}
    (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).refinement = g.refinement ∘ f.refinement := rfl

/-- A composite refinement's inclusion is the composite of inclusions. -/
theorem refine_comp_incl {a b : K.cells 0} {x y z : RefineObj (K := K) a b}
    (f : x ⟶ y) (g : y ⟶ z) (i : Fin x.cubes.length) :
    (f ≫ g).incl i = f.incl i ≫ g.incl (f.refinement i) := rfl

/-- `incl`-`HEq` between two refinements of the **same** chains whose reindexings are equal:
it suffices to check, for each index, that `f.incl i` equals `g.incl i` post-composed with the
canonical `eqToHom` transport of the target across `hr : f.ref = g.ref` (`f`/`g` share the
source `x.get i`, differing only on the target `y.get (· i)`). -/
private theorem incl_heq_of_index_eq {a b : K.cells 0}
    {x y : RefineObj (K := K) a b} {f g : x ⟶ y} (hr : f.refinement = g.refinement)
    (h : ∀ i, f.incl i
      = g.incl i
        ≫ eqToHom (congrArg (fun l => ▫((y.cubes.get l).1 : ℕ)) (congrFun hr i).symm)) :
    HEq f.incl g.incl := by
  refine Function.hfunext rfl ?_
  intro i i' hii
  obtain rfl : i = i' := eq_of_heq hii
  rw [h i]
  -- `HEq (g.incl i ≫ eqToHom η) (g.incl i)`: the `eqToHom` is between equal objects (`hr`).
  exact comp_eqToHom_heq _ _

/-- Any morphism built from `eqToHom`s and a `𝟙` seam, framed by an `eqToHom h` of the right
endpoints, equals `eqToHom h`: the `eqToHom`-conjugate of a `𝟙` is again an `eqToHom`.  Used to
close the per-index `map_id` goals where `simp`'s syntactic `id_comp` cannot see the defeq
seam. -/
theorem eqToHom_id_seam {C : Type*} [Category C] {X Y Z : C}
    (h1 : X = Y) (h2 : Y = Z) (h : X = Z) :
    eqToHom h1 ≫ 𝟙 Y ≫ eqToHom h2 = eqToHom h := by
  subst h1; subst h2; simp

/-- `𝟙 ≫ eqToHom h₂ = eqToHom h` framed at the right endpoints (the `𝟙`-seam variant with no
leading `eqToHom`). -/
theorem id_eqToHom_seam {C : Type*} [Category C] {X Z : C} (h2 : X = Z) (h : X = Z) :
    𝟙 X ≫ eqToHom h2 = eqToHom h := by
  subst h2; simp

/-- **`eqToHom`-composites are heterogeneously the identity.**  Any morphism that is `≍ 𝟙` of
its domain (e.g. any composite of `eqToHom`s and `𝟙`s) is determined: two such parallel
morphisms are equal.  This sidesteps `eqToHom_trans`'s *syntactic* seam-matching, which fails
when the intermediate objects are only *definitionally* equal (as the `appendIncl` transports
produce). -/
theorem hom_eq_of_heq_id {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (hf : f ≍ 𝟙 X) (hg : g ≍ 𝟙 X) : f = g :=
  eq_of_heq (hf.trans hg.symm)

/-- Two parallel morphisms that are each `≍` a common `core` are equal (the `core` may live over
different — but defeq — endpoints; used to compare two `eqToHom`-framed copies of the same
`incl`-composite). -/
theorem hom_eq_of_heq_core {C : Type*} [Category C] {X Y X' Y' : C} {f g : X ⟶ Y}
    {core : X' ⟶ Y'} (hf : f ≍ core) (hg : g ≍ core) : f = g :=
  eq_of_heq (hf.trans hg.symm)

/-- A leading `eqToHom` is `≍`-transparent: from `f ≍ g` conclude `eqToHom h ≫ f ≍ g` — the
`=`-typed restatement of `eqToHom_comp_heq` that unifies the seam by **defeq** (so it fires
where the syntactic `eqToHom_trans` simp lemma stalls on the `appendIncl` transports).  `g` is
fully general (`≍` ignores its endpoints). -/
theorem eqToHom_comp_heq' {C : Type*} [Category C] {W X Y : C} (h : W = X)
    (f : X ⟶ Y) {Z Z' : C} (g : Z ⟶ Z') (hfg : f ≍ g) : eqToHom h ≫ f ≍ g :=
  (eqToHom_comp_heq f h).trans hfg

/-- A trailing `eqToHom` is `≍`-transparent: from `f ≍ g` conclude `f ≫ eqToHom h ≍ g` (defeq
seam; `g` fully general). -/
theorem comp_eqToHom_heq' {C : Type*} [Category C] {X Y Z : C} (h : Y = Z)
    (f : X ⟶ Y) {W W' : C} (g : W ⟶ W') (hfg : f ≍ g) : f ≫ eqToHom h ≍ g :=
  (comp_eqToHom_heq f h).trans hfg

/-- Move a `ChainRefine.append`'s inclusion across an index equality `i = i'`, inserting the
canonical `eqToHom` transports (`subst`-robust against the `Fin.cast` round-trips). -/
theorem appendIncl_index_eq {a m b : K.cells 0}
    {x x' y y' : List (Σ n : ℕ+, K.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y')
    {i i' : Fin (x ++ y).length} (h : i = i') :
    appendIncl f g i
      = eqToHom (congrArg (fun l => ▫(((x ++ y).get l).1 : ℕ)) h)
        ≫ appendIncl f g i'
        ≫ eqToHom (congrArg
            (fun l => ▫(((x' ++ y').get
              (appendRefinement f.refinement g.refinement l)).1 : ℕ)) h.symm) :=
  -- `appendIncl f g = (f.append g).incl` definitionally, so this is the promoted
  -- index-transport lemma `ChainRefine.incl_index_eq` of `RefineFunctor.lean`.
  ChainRefine.incl_index_eq (f.append g) h

/-- The cube of `pre.append y` at a prefix-whiskered tail index (`appendRefinement id rg` of a
`natAdd ib`) is the tail's cube `y.get (rg ib)` (the prefix-`id` part collapses). -/
theorem append_get_natAdd
    {x y y' : List (Σ n : ℕ+, K.cells (n : ℕ))} (rg : Fin y.length → Fin y'.length)
    (ib : Fin y.length) :
    ((x ++ y').get (appendRefinement (id : Fin x.length → Fin x.length) rg
        (Fin.cast (List.length_append ..).symm (ib.natAdd x.length)))).1
      = (y'.get (rg ib)).1 := by
  have hv : appendRefinement (id : Fin x.length → Fin x.length) rg
        (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
      = Fin.cast (List.length_append ..).symm ((rg ib).natAdd x.length) := by
    apply Fin.ext
    rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp
  rw [hv]; exact congrArg (·.1) (get_append_natAdd (rg ib))

/-- **The prefix-whiskered inclusion is heterogeneously the tail's inclusion.**  On a tail
(`natAdd`) index, `appendIncl (𝟙 pre) g` is `g.incl ib` framed by `eqToHom`s, so `≍ g.incl ib`
(the frames strip under `≍`, which tolerates the defeq seams). -/
theorem appendIncl_natAdd_heq {a m b : K.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂)
    (ib : Fin y₁.cubes.length) :
    appendIncl (𝟙 pre) g (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))
      ≍ g.incl ib := by
  rw [appendIncl_natAdd]
  refine eqToHom_comp_heq' _ _ (g.incl ib) ?_
  exact comp_eqToHom_heq' _ _ (g.incl ib) HEq.rfl

/-- `appendLeftMap pre g` is definitionally `ChainRefine.append (𝟙 pre) g`, hence its inclusion
is `appendIncl (𝟙 pre) g` — a `rfl` bridge so `appendIncl_castAdd`/`_natAdd` apply. -/
theorem appendLeftMap_incl {a m b : K.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    (pre.appendLeftMap g).incl = appendIncl (𝟙 pre) g := rfl

/-- The reindexing of `appendLeftMap` is `appendRefinement id g.refinement`. -/
theorem appendLeftMap_refinement {a m b : K.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    (pre.appendLeftMap g).refinement = appendRefinement id g.refinement := rfl

/-- **The left-whiskering functor.**  Prepend the fixed prefix `pre` to a tail chain; on
morphisms this is `appendLeftMap`.  `FreeGroupoid.map` of it promotes a local sweep up to the
d-path groupoid. -/
noncomputable def RefineObj.appendLeft {a m b : K.cells 0}
    (pre : RefineObj (K := K) a m) : RefineObj (K := K) m b ⥤ RefineObj (K := K) a b where
  obj y := pre.append y
  map g := pre.appendLeftMap g
  map_id y := by
    refine ChainRefine.ext appendRefinement_id_id (incl_heq_of_index_eq appendRefinement_id_id ?_)
    intro i
    rw [refine_id_incl, appendLeftMap_incl]
    obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
      ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
    induction j using Fin.addCases with
    | left ia =>
      rw [appendIncl_castAdd, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp, eqToHom_trans]
      rfl
    | right ib =>
      rw [appendIncl_natAdd, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp, eqToHom_trans]
      rfl
  map_comp {y₁ y₂ y₃} g₁ g₂ := by
    refine ChainRefine.ext (appendRefinement_id_comp g₁.refinement g₂.refinement)
      (incl_heq_of_index_eq (appendRefinement_id_comp g₁.refinement g₂.refinement) ?_)
    intro i
    -- The helper's goal: `(appendLeftMap pre (g₁≫g₂)).incl i = (compose).incl i ≫ eqToHom _`.
    -- `(compose).incl i = (appendLeftMap pre g₁).incl i ≫ (appendLeftMap pre g₂).incl (f.ref i)`
    -- (defeq, `refine_comp_incl`); index-split and reduce each side branch-wise.
    change (pre.appendLeftMap (g₁ ≫ g₂)).incl i
        = ((pre.appendLeftMap g₁).incl i
            ≫ (pre.appendLeftMap g₂).incl (appendRefinement id g₁.refinement i)) ≫ eqToHom _
    rw [appendLeftMap_incl, appendLeftMap_incl, appendLeftMap_incl]
    obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
      ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
    induction j using Fin.addCases with
    | left ia =>
      -- prefix block: LHS `append (𝟙 pre) (g₁≫g₂)` is `𝟙`-conjugated; RHS composes two
      -- `𝟙`-conjugated appends; both collapse to a single `eqToHom`.
      rw [appendIncl_castAdd (𝟙 pre) (g₁ ≫ g₂) ia, refine_id_incl,
        appendIncl_index_eq (𝟙 pre) g₂ (i := appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ia.castAdd y₁.cubes.length)))
          (i' := Fin.cast (List.length_append ..).symm (ia.castAdd y₂.cubes.length)) (by
            apply Fin.ext; rw [appendRefinement_val_left _ _ _ (by simp)]; simp),
        appendIncl_castAdd (𝟙 pre) g₁ ia, refine_id_incl,
        appendIncl_castAdd (𝟙 pre) g₂ ia, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp]
      refine hom_eq_of_heq_id ?_ ?_ <;>
        · repeat first
            | refine eqToHom_comp_heq' _ _ _ ?_
            | refine comp_eqToHom_heq' _ _ _ ?_
            | refine (heq_of_eq (Category.assoc _ _ _)).trans ?_
          refine (eqToHom_heq_id_dom _ _ _).trans ?_
          rw [get_append_castAdd ia]
    | right ib =>
      -- Tail block.  Both sides are `≍ g₁.incl ib ≫ g₂.incl (g₁.refinement ib)`:
      --   LHS = `appendIncl (𝟙 pre) (g₁≫g₂) (natAdd ib) ≍ (g₁≫g₂).incl ib` (the frame strips);
      --   RHS = `(appendIncl g₁ (natAdd ib) ≫ appendIncl g₂ (natAdd (g₁.ref ib))) ≫ eqToHom`,
      --   each `appendIncl` stripping to its `incl` (`appendIncl_natAdd_heq`), the `eqToHom`
      --   stripping, and the two `incl`s glued by `heq_comp` (object eqs via `append_get_natAdd`).
      apply eq_of_heq
      refine (appendIncl_natAdd_heq pre (g₁ ≫ g₂) ib).trans ?_
      rw [refine_comp_incl]
      refine HEq.symm (comp_eqToHom_heq' _ _ (g₁.incl ib ≫ g₂.incl (g₁.refinement ib)) ?_)
      -- the second factor's index is
      -- `appendRefinement id g₁.ref (natAdd ib) = natAdd (g₁.ref ib)`; move it across
      -- (`appendIncl_index_eq`, frames strip) then reduce by `appendIncl_natAdd_heq`.
      have hidx : (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))
          = Fin.cast (List.length_append ..).symm
              ((g₁.refinement ib).natAdd pre.cubes.length) := by
        apply Fin.ext; rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp
      have hg₂ : appendIncl (𝟙 pre) g₂ (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))
          ≍ g₂.incl (g₁.refinement ib) := by
        rw [appendIncl_index_eq (𝟙 pre) g₂ hidx]
        exact eqToHom_comp_heq' _ _ (g₂.incl (g₁.refinement ib))
          (comp_eqToHom_heq' _ _ (g₂.incl (g₁.refinement ib))
            (appendIncl_natAdd_heq pre g₂ (g₁.refinement ib)))
      -- the three object equalities (domain/middle/codomain), via `get_append_natAdd` and
      -- `append_get_natAdd`; stated up to the defeq `pre.append y = pre.cubes ++ y.cubes`.
      have hdom : ((pre.append y₁).cubes.get
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))).1
          = (y₁.cubes.get ib).1 := congrArg (·.1) (get_append_natAdd (l := pre.cubes) ib)
      have hmid : ((pre.append y₂).cubes.get (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))).1
          = (y₂.cubes.get (g₁.refinement ib)).1 :=
        append_get_natAdd (x := pre.cubes) g₁.refinement ib
      have hcod : ((pre.append y₃).cubes.get (appendRefinement id g₂.refinement
            (appendRefinement id g₁.refinement
              (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))))).1
          = (y₃.cubes.get (g₂.refinement (g₁.refinement ib))).1 := by
        rw [hidx]; exact append_get_natAdd (x := pre.cubes) g₂.refinement (g₁.refinement ib)
      exact heq_comp (congrArg (fun n : ℕ+ => ▫(n : ℕ)) hdom)
        (congrArg (fun n : ℕ+ => ▫(n : ℕ)) hmid)
        (congrArg (fun n : ℕ+ => ▫(n : ℕ)) hcod) (appendIncl_natAdd_heq pre g₁ ib) hg₂

end CubeChain
