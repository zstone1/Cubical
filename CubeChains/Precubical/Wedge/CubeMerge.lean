import CubeChains.Machinery.Cube.BoxMonoidal
import CubeChains.Precubical.Wedge.WedgeMonoidal

/-!
# Precubical/Wedge/CubeMerge — the two staircases out of a pair of cubes

`□(p+q)` has two block faces through each vertex: `headFace ε p q` frees the first `p` axes and
holds the rest at `ε`, `tailFace ε p q` frees the last `q`.  A `p`-cube followed by a `q`-cube
lands on them in two ways: `cubeMerge` runs the first bead through the head block, `cubeReorder`
through the tail.  Both are descents out of the wedge.
-/

open CategoryTheory Opposite StdCube BPSet PrecubicalSet

namespace Box

/-- The face of `□(p+q)` free on the first `p` axes, the last `q` held at `ε`. -/
def headFace (ε : Bool) (p q : ℕ) : ▫p ⟶ ▫(p + q) :=
  ofSign (appendCell (topCell p) (constVertex q ε))

/-- The face of `□(p+q)` free on the last `q` axes, the first `p` held at `ε`. -/
def tailFace (ε : Bool) (p q : ℕ) : ▫q ⟶ ▫(p + q) :=
  ofSign ⟨Fin.append (constVertex p ε).val (topCell q).val, by
    rw [card_noneSet_append, (constVertex p ε).prop, (topCell q).prop, Nat.zero_add]⟩

theorem sign_headFace (ε : Bool) (p q : ℕ) :
    (sign (headFace ε p q)).val = Fin.append (topCell p).val (constVertex q ε).val := rfl

theorem sign_tailFace (ε : Bool) (p q : ℕ) :
    (sign (tailFace ε p q)).val = Fin.append (constVertex p ε).val (topCell q).val := rfl

/-- A vertex of a cube pushed along a face: the free coordinates take the vertex's value. -/
private theorem sign_endVertexMap_comp {N n : ℕ} (ε : Bool) (g : ▫n ⟶ ▫N) (j : Fin N) :
    (sign (endVertexMap ε n ≫ g)).val j = some (((sign g).val j).getD ε) := by
  rw [sign_comp, subst_val]
  by_cases h : (sign g).val j = none
  · rw [substFun_of_none _ _ h]
    exact (congrArg (fun o : Option Bool => some (o.getD ε)) h).symm
  · rw [substFun_of_some _ _ h]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
    rw [hb]; rfl

/-- **The corner of the two block faces**: the head face at its `ε'`-vertex is the tail face at its
`ε`-vertex — both are the vertex `(ε'ᵖ, εᑫ)`. -/
theorem endVertexMap_headFace (ε' ε : Bool) (p q : ℕ) :
    endVertexMap ε' p ≫ headFace ε p q = endVertexMap ε q ≫ tailFace ε' p q :=
  hom_ext (Subtype.ext (funext fun j => by
    rw [sign_endVertexMap_comp, sign_endVertexMap_comp, sign_headFace, sign_tailFace]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left, Fin.append_left]; rfl
    · rw [Fin.append_right, Fin.append_right]; rfl))

/-- The head face at its own constant is that extreme vertex of `□(p+q)`. -/
theorem endVertexMap_headFace_self (ε : Bool) (p q : ℕ) :
    endVertexMap ε p ≫ headFace ε p q = endVertexMap ε (p + q) :=
  hom_ext (Subtype.ext (funext fun j => by
    rw [sign_endVertexMap_comp, sign_headFace]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl))

/-- The tail face at its own constant is that extreme vertex of `□(p+q)`. -/
theorem endVertexMap_tailFace_self (ε : Bool) (p q : ℕ) :
    endVertexMap ε q ≫ tailFace ε p q = endVertexMap ε (p + q) :=
  (endVertexMap_headFace ε ε p q).symm.trans (endVertexMap_headFace_self ε p q)

/-- A face whose free coordinates are enumerated by a strictly monotone `f` **is** `f`. -/
theorem faceEmb_eq_of_none {k N : ℕ} (g : ▫k ⟶ ▫N) {f : Fin k → Fin N} (hf : StrictMono f)
    (hnone : ∀ i, (sign g).val (f i) = none) (i : Fin k) : faceEmb g i = f i :=
  congrFun (Finset.orderEmbOfFin_unique (sign g).prop
    (fun z => mem_noneSet.mpr (hnone z)) hf).symm i

/-- The head face frees the coordinate block `[0, p)`. -/
theorem faceEmb_headFace (ε : Bool) (p q : ℕ) (k : Fin p) :
    faceEmb (headFace ε p q) k = Fin.castAdd q k :=
  faceEmb_eq_of_none _ (f := Fin.castAdd q) (fun _ _ hab => hab)
    (fun z => by rw [sign_headFace, Fin.append_left]; rfl) k

/-- The tail face frees the coordinate block `[p, p + q)`. -/
theorem faceEmb_tailFace (ε : Bool) (p q : ℕ) (k : Fin q) :
    faceEmb (tailFace ε p q) k = Fin.natAdd p k :=
  faceEmb_eq_of_none _ (f := Fin.natAdd p) (fun _ _ hab => Nat.add_lt_add_left hab p)
    (fun z => by rw [sign_tailFace, Fin.append_right]; rfl) k

end Box

namespace ChainCat

open Box

/-- A vertex of a cube, pushed along a face, is the vertex of the composite. -/
private theorem vertexOf_yoneda_map {n N : ℕ} (ε : Bool) (g : ▫n ⟶ ▫N) :
    (□n).vertexOf ε ≫ yoneda.map g = yonedaEquiv.symm (endVertexMap ε n ≫ g) := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, vertexOf, vertexMap, PrecubicalSet.cubeMap,
    Equiv.apply_symm_apply]
  cases ε <;> rfl

/-- Two faces meeting at a vertex, as maps out of the two endpoints. -/
private theorem vertexOf_corner {n n' N : ℕ} {ε ε' : Bool} {g : ▫n ⟶ ▫N} {g' : ▫n' ⟶ ▫N}
    (h : endVertexMap ε n ≫ g = endVertexMap ε' n' ≫ g') :
    (□n).vertexOf ε ≫ yoneda.map g = (□n').vertexOf ε' ≫ yoneda.map g' :=
  (vertexOf_yoneda_map ε g).trans
    ((congrArg yonedaEquiv.symm h).trans (vertexOf_yoneda_map ε' g').symm)

/-- A face through an extreme vertex of `□N`, as a map out of that endpoint. -/
private theorem vertexOf_end {n N : ℕ} {ε : Bool} {g : ▫n ⟶ ▫N}
    (h : endVertexMap ε n ≫ g = endVertexMap ε N) :
    (□n).vertexOf ε ≫ yoneda.map g = (□N).vertexOf ε :=
  (vertexOf_yoneda_map ε g).trans ((congrArg yonedaEquiv.symm h).trans (by cases ε <;> rfl))

/-- **The bead merge** `□p ∨ □q ⟶ □(p+q)`: the first bead on the head block (the rest at `0`), the
second on the tail block (the rest at `1`). -/
def cubeMerge (p q : ℕ) : □p ∨ □q ⟶ □(p + q) :=
  wedge2DescBP (yoneda.map (headFace false p q)) (yoneda.map (tailFace true p q))
    (vertexOf_corner (endVertexMap_headFace true false p q))
    (vertexOf_end (endVertexMap_headFace_self false p q))
    (vertexOf_end (endVertexMap_tailFace_self true p q))

/-- **The bead reordering** `□p ∨ □q ⟶ □(q+p)`: the same two beads on the opposite blocks. -/
def cubeReorder (p q : ℕ) : □p ∨ □q ⟶ □(q + p) :=
  wedge2DescBP (yoneda.map (tailFace false q p)) (yoneda.map (headFace true q p))
    (vertexOf_corner (endVertexMap_headFace false true q p).symm)
    (vertexOf_end (endVertexMap_tailFace_self false q p))
    (vertexOf_end (endVertexMap_headFace_self true q p))

@[reassoc (attr := simp)] theorem wedgeInl_cubeMerge (p q : ℕ) :
    wedgeInl (□p) (□q) ≫ (cubeMerge p q : BPSet.Hom _ _).hom = yoneda.map (headFace false p q) :=
  wedge2Desc_inl _ _ _

@[reassoc (attr := simp)] theorem wedgeInr_cubeMerge (p q : ℕ) :
    wedgeInr (□p) (□q) ≫ (cubeMerge p q : BPSet.Hom _ _).hom = yoneda.map (tailFace true p q) :=
  wedge2Desc_inr _ _ _

@[reassoc (attr := simp)] theorem wedgeInl_cubeReorder (p q : ℕ) :
    wedgeInl (□p) (□q) ≫ (cubeReorder p q : BPSet.Hom _ _).hom = yoneda.map (tailFace false q p) :=
  wedge2Desc_inl _ _ _

@[reassoc (attr := simp)] theorem wedgeInr_cubeReorder (p q : ℕ) :
    wedgeInr (□p) (□q) ≫ (cubeReorder p q : BPSet.Hom _ _).hom = yoneda.map (headFace true q p) :=
  wedge2Desc_inr _ _ _

/-- A leg of a staircase, read as a cell of the target cube, is its block face. -/
private theorem yonedaEquiv_leg {n N : ℕ} {f : (□n).toPsh ⟶ (□N).toPsh} {g : ▫n ⟶ ▫N}
    (h : f = yoneda.map g) : yonedaEquiv f = g :=
  h ▸ yonedaEquiv_yoneda_map g

/-! ### The coordinate blocks of the two staircases

`cubeMerge` keeps the block order, `cubeReorder` exchanges it. -/

theorem faceEmb_cubeMerge_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) :=
  congrArg Fin.val ((yonedaEquiv_leg (wedgeInl_cubeMerge m n)).symm ▸ faceEmb_headFace _ _ _ k)

theorem faceEmb_cubeMerge_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = m + (k : ℕ) :=
  congrArg Fin.val ((yonedaEquiv_leg (wedgeInr_cubeMerge m n)).symm ▸ faceEmb_tailFace _ _ _ k)

theorem faceEmb_cubeReorder_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = n + (k : ℕ) :=
  congrArg Fin.val ((yonedaEquiv_leg (wedgeInl_cubeReorder m n)).symm ▸ faceEmb_tailFace _ _ _ k)

theorem faceEmb_cubeReorder_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) :=
  congrArg Fin.val ((yonedaEquiv_leg (wedgeInr_cubeReorder m n)).symm ▸ faceEmb_headFace _ _ _ k)

/-- **Merging is not reordering**: the first bead of `cubeMerge 1 1` frees coordinate `0`, that of
`cubeReorder 1 1` holds it at `0`. -/
theorem cubeMerge_ne_cubeReorder : cubeMerge 1 1 ≠ cubeReorder 1 1 := by
  intro h
  have hg : headFace false 1 1 = tailFace false 1 1 :=
    (yonedaEquiv_leg (wedgeInl_cubeMerge 1 1)).symm.trans
      (h ▸ yonedaEquiv_leg (wedgeInl_cubeReorder 1 1))
  exact absurd (congrFun (congrArg (fun g => (sign g).val) hg) 0) (by decide)

end ChainCat
