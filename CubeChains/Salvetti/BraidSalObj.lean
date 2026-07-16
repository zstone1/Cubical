import CubeChains.Salvetti.BraidReindex
import CubeChains.Braid.Naturality
import Mathlib.Data.List.GetD

/-!
# Salvetti/BraidSalObj — object-map characterization of `braidSalEquiv`

`braidSalEquiv n` is assembled (`Salvetti/BraidIso`) as a four-leg composite; three legs have an
`rfl` object map and the remaining one (base transport `preEquivalence.symm`) is a choice-based
`Functor.inv`.  Pinning that leg down uses that its codomain `(salFunctor (braidCOM n)).Elements`
is a poset (base `Face (braidCOM n)` is antisymmetric), so an iso there is an equality.

The upshot (`braidSalEquiv_functor_obj`): the image of a Salvetti cell `a` is the execution whose
chain is the ordered-set-partition `y` realising `a.face` and whose line is the chamber tuple
`toLines y a.tope`.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

open SignVec COM

variable {n : ℕ}

instance refineOpToFace_isEquiv (n : ℕ) : (refineOpToFace n).IsEquivalence := { }

/-! ## Skeletality of a category of elements over a thin, antisymmetric base -/

/-- In a category of elements over a thin base whose homs are antisymmetric, an isomorphism is an
equality of objects. -/
theorem elements_iso_eq {C : Type*} [Category C] [Quiver.IsThin C]
    (hanti : ∀ {X Y : C}, (X ⟶ Y) → (Y ⟶ X) → X = Y)
    {P : C ⥤ Type*} {p q : P.Elements} (e : p ≅ q) : p = q := by
  have h1 : p.1 = q.1 := hanti e.hom.1 e.inv.1
  refine Functor.Elements.ext p q h1 ?_
  rw [show (eqToHom h1 : p.1 ⟶ q.1) = e.hom.1 from Subsingleton.elim _ _]
  exact e.hom.2

/-- Antisymmetry of `Face L` homs. -/
theorem face_hom_antisymm {E : Type*} {L : COM E} {X Y : COM.Face L}
    (f : X ⟶ Y) (g : Y ⟶ X) : X = Y :=
  le_antisymm (leOfHom f) (leOfHom g)

/-! ## Reductions of the four legs (three are `rfl`) -/

/-- The whole forward object map is the composite of the four legs' object maps. -/
theorem braidSalEquiv_functor_obj_legs (a : Sal (braidCOM n)) :
    (braidSalEquiv n).functor.obj a =
      (refineLinesEquiv n).functor.obj
        ((CategoryOfElements.mapEquivalence (salLinesIso n).symm).functor.obj
          ((CategoryOfElements.preEquivalence (COM.salFunctor (braidCOM n))
              (refineOpToFace n).asEquivalence).symm.functor.obj
            ((COM.salElementsEquiv (braidCOM n)).functor.obj a))) :=
  rfl

/-! ## The forward object map -/

/-- **The forward object map of `braidSalEquiv`.**  A Salvetti cell `a` maps to the execution
whose chain is the ordered-set-partition `y` realising `a.face` (`braidSign (covectorHeight y) =
a.face`) and whose line is the chamber tuple `toLines y a.tope` read off the tope `a.tope`. -/
theorem braidSalEquiv_functor_obj (a : Sal (braidCOM n)) :
    ∃ (y : RefineObj (□n).init (□n).final) (hle : braidSign (covectorHeight y) ⊑ a.tope),
      braidSign (covectorHeight y) = a.face ∧
      (braidSalEquiv n).functor.obj a
        = ⟨op ((cubeChainRefineEquiv n).functor.obj y),
            toLines y ⟨a.tope, a.2.2.1, hle⟩⟩ := by
  set P := COM.salFunctor (braidCOM n) with hP
  set G := refineOpToFace n with hG
  set W2 := (CategoryOfElements.preEquivalence P G.asEquivalence).symm.functor.obj
              ((COM.salElementsEquiv (braidCOM n)).functor.obj a) with hW2
  have hcollapse : (CategoryOfElements.pre P G).obj W2
      = (COM.salElementsEquiv (braidCOM n)).functor.obj a := by
    apply elements_iso_eq face_hom_antisymm
    exact (CategoryOfElements.pre P G).objObjPreimageIso _
  have hface : braidSign (covectorHeight W2.1.unop) = a.face :=
    congrArg (fun w : P.Elements => (w.1).1) hcollapse
  have htope : W2.2.1 = a.tope :=
    congrArg (fun w : P.Elements => (w.2).1) hcollapse
  have hle : braidSign (covectorHeight W2.1.unop) ⊑ a.tope := hface ▸ a.2.2.2
  refine ⟨W2.1.unop, hle, hface, ?_⟩
  rw [braidSalEquiv_functor_obj_legs]
  refine Sigma.ext rfl (heq_of_eq ?_)
  show toLines W2.1.unop W2.2 = toLines W2.1.unop ⟨a.tope, a.2.2.1, hle⟩
  congr 1
  exact Subtype.ext htope

/-- **Reading a cell off its execution.**  From `braidSalEquiv_functor_obj`, packaged as: an
ordered-set-partition `y` and its chamber tuple `L` with `heightOf y L` realising the tope, whose
block index realises the face, and whose chain matches. -/
theorem braidSalEquiv_functor_obj_read (a : Sal (braidCOM n)) :
    ∃ (y : RefineObj (□n).init (□n).final) (L : (RefineLines n).obj (op y)),
      Function.Injective (heightOf y L)
      ∧ a.tope = braidSign (heightOf y L)
      ∧ a.face = braidSign (covectorHeight y)
      ∧ ((braidSalEquiv n).functor.obj a).1.unop
          = (cubeChainRefineEquiv n).functor.obj y := by
  obtain ⟨y, hle, hfaceEq, hobj⟩ := braidSalEquiv_functor_obj a
  refine ⟨y, toLines y ⟨a.tope, a.2.2.1, hle⟩, heightOf_injective _ _, ?_, hfaceEq.symm, ?_⟩
  · exact (congrArg Subtype.val (ofLines_toLines y ⟨a.tope, a.2.2.1, hle⟩)).symm
  · rw [hobj]

/-! ## Height decomposition -/

variable (y : RefineObj (□n).init (□n).final)

/-- The local rank is `< dᵢ` (the bead dimension), sharper than `localRank_lt`. -/
theorem localRank_lt_beadDim (L : (RefineLines n).obj (op y)) (i : Fin y.cubes.length)
    (p : Fin n) (hp : p ∈ blockOf y i) :
    localRank y L i p hp < ((y.cubes.get i).1 : ℕ) := by
  have hb := (chamberRank_bounded (L (Fin.cast (dseqLen y).symm i))
    (Fin.cast (dseqGetNat y i).symm (nonesIdx (toStar (y.cubes.get i).2) p hp))).2
  have hD : (((cubeChainRefineEquiv n).functor.obj y).dims.get (Fin.cast (dseqLen y).symm i) : ℕ)
      = ((y.cubes.get i).1 : ℕ) := dseqGetNat y i
  calc localRank y L i p hp
      < (((cubeChainRefineEquiv n).functor.obj y).dims.get (Fin.cast (dseqLen y).symm i) : ℕ) := hb
    _ = ((y.cubes.get i).1 : ℕ) := by exact_mod_cast hD

/-- **Block index is the height's high digit.**  `blockIndex y p = (heightOf y L p) / n`, since
`heightOf = n · blockIndex + localRank` with `0 ≤ localRank < n`. -/
theorem blockIndex_heightOf_ediv (L : (RefineLines n).obj (op y)) (p : Fin n) :
    (blockIndex y p : ℤ) = heightOf y L p / (n : ℤ) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le p.1) p.2
  have hr0 : 0 ≤ localRank y L (blockIndex y p) p (blockIndex_mem y p) :=
    localRank_nonneg y L (blockIndex y p) p (blockIndex_mem y p)
  have hrn : localRank y L (blockIndex y p) p (blockIndex_mem y p) < (n : ℤ) :=
    localRank_lt y L (blockIndex y p) p (blockIndex_mem y p)
  have hdecomp : heightOf y L p
      = localRank y L (blockIndex y p) p (blockIndex_mem y p) + (blockIndex y p : ℤ) * (n : ℤ) := by
    rw [heightOf]; ring
  rw [hdecomp, Int.add_mul_ediv_right _ _ (ne_of_gt hn),
    Int.ediv_eq_zero_of_lt hr0 hrn, zero_add]

/-! ## The set of realised heights depends only on the dimension sequence -/

/-- The heights realisable on a chain with dimension sequence `D`: block `i` (size `Dᵢ`)
contributes the block `{n·i, …, n·i + Dᵢ − 1}`.  Depends only on `D`. -/
def blockVals (n : ℕ) (D : List ℕ+) : Finset ℤ :=
  (Finset.range D.length).biUnion fun i =>
    (Finset.range ((D.getD i 1 : ℕ+) : ℕ)).image fun r : ℕ => (n : ℤ) * (i : ℤ) + (r : ℤ)

theorem getD_map_dims (i : Fin y.cubes.length) :
    (((y.cubes.map (·.1)).getD (i : ℕ) 1 : ℕ+) : ℕ) = ((y.cubes.get i).1 : ℕ) := by
  rw [List.getD_eq_getElem (l := y.cubes.map (·.1)) (d := 1)
      (by rw [List.length_map]; exact i.isLt), List.getElem_map, List.get_eq_getElem]

/-- Every realised height lies in `blockVals`. -/
theorem heightOf_mem_blockVals (L : (RefineLines n).obj (op y)) (p : Fin n) :
    heightOf y L p ∈ blockVals n (y.cubes.map (·.1)) := by
  set i := blockIndex y p with hi
  set r := localRank y L i p (blockIndex_mem y p) with hr
  have hr0 : 0 ≤ r := localRank_nonneg y L i p (blockIndex_mem y p)
  have hrlt : r < ((y.cubes.get i).1 : ℕ) := localRank_lt_beadDim y L i p (blockIndex_mem y p)
  rw [blockVals, Finset.mem_biUnion]
  refine ⟨(i : ℕ), Finset.mem_range.mpr (by rw [List.length_map]; exact i.isLt), ?_⟩
  rw [Finset.mem_image]
  refine ⟨r.toNat, Finset.mem_range.mpr ?_, ?_⟩
  · rw [getD_map_dims]
    exact (Int.toNat_lt_of_ne_zero (y.cubes.get i).1.pos.ne').mpr hrlt
  · rw [Int.toNat_of_nonneg hr0]
    show (n : ℤ) * (i : ℕ) + r = heightOf y L p
    rw [heightOf]

/-- `blockVals` of a cube chain's dims has at most `n` elements (the blocks sum to `n`). -/
theorem blockVals_card_le :
    (blockVals n (y.cubes.map (·.1))).card ≤ n := by
  rw [blockVals]
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun i _ =>
    le_trans Finset.card_image_le (le_of_eq (Finset.card_range _)))) ?_
  rw [List.length_map, ← Fin.sum_univ_eq_sum_range
    (fun i => (((y.cubes.map (·.1)).getD i 1 : ℕ+) : ℕ))]
  simp_rw [getD_map_dims]
  rw [sum_get_eq_sum_map y.cubes (fun c => (c.1 : ℕ))]
  exact le_of_eq (cubes_dims_sum y)

/-- Every height realiser hits exactly `blockVals`. -/
theorem image_heightOf_eq_blockVals (L : (RefineLines n).obj (op y)) :
    Finset.univ.image (heightOf y L) = blockVals n (y.cubes.map (·.1)) := by
  refine Finset.eq_of_subset_of_card_le (fun v hv => ?_) ?_
  · rw [Finset.mem_image] at hv
    obtain ⟨p, _, rfl⟩ := hv
    exact heightOf_mem_blockVals y L p
  · rw [Finset.card_image_of_injective _ (heightOf_injective y L), Finset.card_univ,
      Fintype.card_fin]
    exact blockVals_card_le y

/-- **Same dimension sequence ⟹ same set of realised heights.**  The image of `heightOf`
depends only on the dimension sequence, so two chains with equal dims realise the same heights. -/
theorem range_heightOf_eq {y' : RefineObj (□n).init (□n).final}
    (L : (RefineLines n).obj (op y)) (L' : (RefineLines n).obj (op y'))
    (hD : y.cubes.map (·.1) = y'.cubes.map (·.1)) :
    Set.range (heightOf y L) = Set.range (heightOf y' L') := by
  have h1 : ∀ (z : RefineObj (□n).init (□n).final) (M : (RefineLines n).obj (op z)),
      Set.range (heightOf z M) = ↑(Finset.univ.image (heightOf z M)) := fun z M => by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h1 y L, h1 y' L', image_heightOf_eq_blockVals, image_heightOf_eq_blockVals, hD]

/-- Two injective heights with the same range are related by a permutation: `ρ' ∘ π = ρ`. -/
theorem perm_of_range_eq {ρ ρ' : Fin n → ℤ} (hρ : Function.Injective ρ)
    (hρ' : Function.Injective ρ') (hrange : Set.range ρ = Set.range ρ') :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ρ' (π i) = ρ i := by
  refine ⟨(Equiv.ofInjective ρ hρ).trans
    ((Equiv.setCongr hrange).trans (Equiv.ofInjective ρ' hρ').symm), fun i => ?_⟩
  simp only [Equiv.trans_apply]
  exact congrArg Subtype.val (Equiv.apply_symm_apply (Equiv.ofInjective ρ' hρ')
    (Equiv.setCongr hrange (Equiv.ofInjective ρ hρ i)))

/-! ## The principal-`Sₙ`-bundle fiber -/

/-- **Fiber of the terminal comparison.**  If two Salvetti cells are pushed to the *same* execution
of the terminal set (same dimension sequence and same line, up to axis relabelling), they lie in one
`Sₙ`-reorientation orbit.  The relabelling `σ` is the permutation matching the two cells'
event-orderings (their tope heights), recovered from `perm_of_range_eq`. -/
theorem braidSal_concToZ_fiber {a a' : Sal (braidCOM n)}
    (h : (concToZ (□n)).obj ((braidSalEquiv n).functor.obj a)
       = (concToZ (□n)).obj ((braidSalEquiv n).functor.obj a')) :
    ∃ σ : Equiv.Perm (Fin n), salReindexObj σ a' = a := by
  obtain ⟨y, L, hLinj, htope, hface, hchain⟩ := braidSalEquiv_functor_obj_read a
  obtain ⟨y', L', hLinj', htope', hface', hchain'⟩ := braidSalEquiv_functor_obj_read a'
  have hdims : y.cubes.map (·.1) = y'.cubes.map (·.1) := by
    have hd : ((braidSalEquiv n).functor.obj a).1.unop.dims
        = ((braidSalEquiv n).functor.obj a').1.unop.dims :=
      congrArg (fun w : ConcCat Zbp => w.1.unop.dims) h
    rw [hchain, hchain'] at hd
    exact hd
  obtain ⟨π, hπ⟩ := perm_of_range_eq hLinj hLinj' (range_heightOf_eq y L L' hdims)
  refine ⟨π⁻¹, Subtype.ext (Prod.ext ?_ ?_)⟩
  · -- face
    show reorient π⁻¹ a'.face = a.face
    rw [hface', hface, reorient_braidSign]
    simp only [inv_inv]
    refine congrArg braidSign (funext (fun i => ?_))
    show covectorHeight y' (π i) = covectorHeight y i
    unfold covectorHeight
    rw [blockIndex_heightOf_ediv y' L' (π i), hπ i, ← blockIndex_heightOf_ediv y L i]
  · -- tope
    show reorient π⁻¹ a'.tope = a.tope
    rw [htope', htope, reorient_braidSign]
    simp only [inv_inv]
    exact congrArg braidSign (funext (fun i => hπ i))

end CubeChains
