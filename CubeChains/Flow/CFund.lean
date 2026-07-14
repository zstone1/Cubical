import CubeChains.Flow.Flow

/-!
# Flow/CFund — the flow 2-category of `K`, as a `Cat`-enriched category

    0-cells  vertices of `K`
    1-cells  executions: a cube chain together with a line
    2-cells  braids

`EnrichedCategory Cat` *is* a strict 2-category (mathlib's `CatEnriched` turns it into a
`Bicategory.Strict`), and strictness costs nothing here: the two ways of concatenating three
executions are **literally the same execution**, once the `List.append_assoc` transport is paid.
There is no non-trivial associator to be had — a 2-cell is a zigzag of refinements, and no
refinement connects `(a ++ b) ++ c` to `a ++ (b ++ c)`.

The two inputs are `chConc_assoc` (chains, `Flow/ChainConcat`) and `chambersConcat_assoc` (lines,
`Flow/Flow`); `lift₂_ext` is what carries them through groupoidification.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

variable {K : BPSet}

/-! ## Executions are pinned by their chain and their line -/

/-- An object of `ConcCat` is a `Σ`: equal chains and (heterogeneously) equal lines. -/
theorem concCat_ext {x y : ConcCat K} (h₁ : x.1 = y.1) (h₂ : HEq x.2 y.2) : x = y := by
  obtain ⟨X, L⟩ := x
  obtain ⟨Y, M⟩ := y
  cases h₁
  cases h₂
  rfl

/-! ## Concatenation of executions is strictly associative and unital -/

/-- **Associativity on executions**: chains re-bracket (`chConc_assoc`) and each bead keeps its own
factor's chamber (`chambersConcat_assoc`). -/
theorem concConc_obj_assoc (K : BPSet) (u v w x : K.cells 0)
    (a : ConcCat (K.repoint u v)) (b : ConcCat (K.repoint v w)) (c : ConcCat (K.repoint w x)) :
    (concConc K u w x).obj ((concConc K u v w).obj (a, b), c)
      = (concConc K u v x).obj (a, (concConc K v w x).obj (b, c)) :=
  concCat_ext (congrArg op (chConc_assoc a.1.unop b.1.unop c.1.unop))
    (chambersConcat_assoc a.1.unop.dims b.1.unop.dims c.1.unop.dims a.2 b.2 c.2)

/-- **Left unit on executions**: the empty chain contributes no bead. -/
theorem concConc_obj_id_left (K : BPSet) (u v : K.cells 0) (b : ConcCat (K.repoint u v)) :
    (concConc K u u v).obj (concId K u, b) = b :=
  concCat_ext (congrArg op (chConc_id_left b.1.unop)) (by
    refine HEq.trans ?_ (heq_of_eq (chambersConcat_nil_left b.1.unop.dims (fun i => i.elim0) b.2))
    exact HEq.rfl)

/-- **Right unit on executions**, across the `A ++ [] = A` transport. -/
theorem concConc_obj_id_right (K : BPSet) (u v : K.cells 0) (a : ConcCat (K.repoint u v)) :
    (concConc K u v v).obj (a, concId K v) = a :=
  concCat_ext (congrArg op (chConc_id_right a.1.unop))
    (chambersConcat_nil_right a.1.unop.dims a.2 (fun i => i.elim0))

/-! ## …and on morphisms

A morphism of `ConcCat` is a `Subtype` over a morphism of `(Ch K)ᵒᵖ`, so each of these is
`ChainConcat`'s corresponding statement, read through `unop`. -/

/-- `eqToHom` in `ConcCat` is `eqToHom` on the chain. -/
theorem concCat_eqToHom_val {x y : ConcCat K} (h : x = y) :
    (eqToHom h : x ⟶ y).1 = eqToHom (congrArg Sigma.fst h) := by
  subst h
  rfl

theorem concCat_comp_val {x y z : ConcCat K} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

theorem concConc_map_assoc (K : BPSet) (u v w x : K.cells 0)
    {a a' : ConcCat (K.repoint u v)} {b b' : ConcCat (K.repoint v w)}
    {c c' : ConcCat (K.repoint w x)} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    (concConc K u w x).map ((concConc K u v w).map (f, g), h)
      = eqToHom (concConc_obj_assoc K u v w x a b c)
        ≫ (concConc K u v x).map (f, (concConc K v w x).map (g, h))
        ≫ eqToHom (concConc_obj_assoc K u v w x a' b' c').symm := by
  apply Subtype.ext
  simp only [concCat_comp_val, concCat_eqToHom_val]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_assoc f.1.unop g.1.unop h.1.unop

theorem concConc_map_id_left (K : BPSet) (u v : K.cells 0)
    {b b' : ConcCat (K.repoint u v)} (g : b ⟶ b') :
    (concConc K u u v).map ((𝟙 (concId K u), g) : (concId K u, b) ⟶ (concId K u, b'))
      = eqToHom (concConc_obj_id_left K u v b) ≫ g
        ≫ eqToHom (concConc_obj_id_left K u v b').symm := by
  apply Subtype.ext
  simp only [concCat_comp_val, concCat_eqToHom_val]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_id_left g.1.unop

theorem concConc_map_id_right (K : BPSet) (u v : K.cells 0)
    {a a' : ConcCat (K.repoint u v)} (f : a ⟶ a') :
    (concConc K u v v).map ((f, 𝟙 (concId K v)) : (a, concId K v) ⟶ (a', concId K v))
      = eqToHom (concConc_obj_id_right K u v a) ≫ f
        ≫ eqToHom (concConc_obj_id_right K u v a').symm := by
  apply Subtype.ext
  simp only [concCat_comp_val, concCat_eqToHom_val]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, eqToHom_unop]
  exact chConcMor_id_right f.1.unop

end CubeChains
