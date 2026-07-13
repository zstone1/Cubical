import CubeChains.Schedule.HDA
import CubeChains.Foundations.Reachability
import CubeChains.Salvetti.SalBraidPartition

/-!
# Schedule/Sculpture — a sculptural HDA is run-injective

A **sculpture** is a precubical set `K` embedded in a single standard cube `□ᴺ` (a *regular*
precubical embedding — no basepoint condition): its events are named by (a subset of) the `N`
ambient coordinate directions, and its HDA labelling is the cube's coordinate labelling
(`cubeLabelling`) pulled back along the embedding.

`Sculpture.runInjective` proves that labelling is `RunInjective` — no run of a sculpture repeats a
label.  The content: a run of `K` pushes forward (`φ`) to a **cube chain** `□ᴺ` between two
arbitrary vertices, whose beads flip **pairwise-disjoint** coordinate sets (`blockOf_unique`, the
ordered-set-partition property, which holds for *any* endpoints).  Neither bipointedness nor
injectivity of the embedding is used — only that `φ` is a precubical map.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

open HDA

variable {K L : BPSet} {A : Type}

/-! ### Pullback of an edge labelling along a precubical map -/

/-- **Pullback of an edge labelling** along a precubical map `φ : K.toPsh ⟶ L.toPsh`: label an edge
of `K` by the label of its image in `L`.  The concurrency axiom transfers by naturality of `φ`
w.r.t. faces (a square of `K` maps to a square of `L`, whose parallel edges are equal-labelled). -/
def EdgeLabelling.comap (φ : K.toPsh ⟶ L.toPsh) (ℓ : EdgeLabelling L A) : EdgeLabelling K A where
  label e := ℓ.label (φ⟪1⟫ e)
  opp_eq s i := by
    rw [PrecubicalSet.map_faceMap φ false i s, PrecubicalSet.map_faceMap φ true i s]
    exact ℓ.opp_eq (φ⟪2⟫ s) i

/-! ### The pulled-back cube labelling reads off the ambient coordinate -/

/-- The `cubeLabelling` value of the direction-`δ` edge of a cube cell `c` is `c`'s `δ`-th free
coordinate (`nones (toStar c) δ`).  The `axisEdge`/`toStar` computation of `cube_evLabel_eq`. -/
theorem cube_axisLabel {N k : ℕ} (c : (□N).cells k) (δ : Fin k) :
    nones (toStar ((□N).toPsh.map (axisEdge δ).op c)) 0
      = nones (toStar c) δ := by
  have hmap : (□N).toPsh.map (axisEdge δ).op c
      = ((□N).toPsh.cubeMap c)⟪1⟫ (axisEdge δ) := by
    rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply]
  rw [hmap, toStar_cubeMap_app, nones_app]
  have hδ : nones (toStar (axisEdge δ)) 0 = δ := by
    rw [toStar_eq]; exact nones_axisEdge_zero δ
  rw [hδ]

/-- **The pulled-back cube label of an event is its image bead's `δ`-th free coordinate.** -/
theorem evLabel_comap_cube {N : ℕ} (φ : K.toPsh ⟶ (□N).toPsh) (a : Ch K)
    (i : ChainCat.Bead a) (δ : Fin (ChainCat.beadDim a i)) :
    evLabel (EdgeLabelling.comap φ (cubeLabelling N)) ⟨a, ⟨i, δ⟩⟩
      = nones (toStar (φ.app _ (beadCell a i))) δ := by
  change (cubeLabelling N).label (φ.app _ (K.toPsh.map (axisEdge δ).op (beadCell a i)))
    = nones (toStar (φ.app _ (beadCell a i))) δ
  rw [NatTrans.naturality_apply]
  exact cube_axisLabel (φ.app _ (beadCell a i)) δ

/-! ### The pushed-forward cube chain and its disjoint blocks -/

/-- A run `a` of `K`, pushed forward along a precubical map `φ : K.toPsh ⟶ □ᴺ`, is a cube chain of
`□ᴺ` (between the `φ`-images of `a`'s endpoints). -/
noncomputable def pushChain {N : ℕ} (φ : K.toPsh ⟶ (□N).toPsh) (a : Ch K) :
    RefineObj ((a.map.hom ≫ φ)⟪0⟫ (⋁a.dims).init)
      ((a.map.hom ≫ φ)⟪0⟫ (⋁a.dims).final) where
  cubes := wedgeToCubes ⟨a.dims, a.map.hom ≫ φ⟩
  isChain := wedgeToCubes_isCubeChain a.dims (a.map.hom ≫ φ)

/-- The `k`-th block of `pushChain φ a` is the flipped-coordinate set of the image of bead `k`. -/
theorem blockOf_pushChain {N : ℕ} (φ : K.toPsh ⟶ (□N).toPsh) (a : Ch K)
    (k : Fin (pushChain φ a).cubes.length) :
    blockOf (pushChain φ a) k
      = noneSet (toStar (φ.app _
          (beadCell a (Fin.cast (wedgeToCubes_length a.dims (a.map.hom ≫ φ)) k)))).val := by
  have step1 : blockOf (pushChain φ a) k
      = noneSet (toStar (yonedaEquiv (ιᵂ a.dims
          (Fin.cast (wedgeToCubes_length a.dims (a.map.hom ≫ φ)) k) ≫ (a.map.hom ≫ φ)))).val :=
    congrArg (fun s : (Σ m : ℕ+, (□N).cells (m : ℕ)) =>
        noneSet (toStar s.2).val)
      (wedgeToCubes_get a.dims (a.map.hom ≫ φ) k)
  rw [step1]
  have hXY : yonedaEquiv (ιᵂ a.dims
        (Fin.cast (wedgeToCubes_length a.dims (a.map.hom ≫ φ)) k) ≫ (a.map.hom ≫ φ))
      = φ.app _ (beadCell a (Fin.cast (wedgeToCubes_length a.dims (a.map.hom ≫ φ)) k)) := by
    rw [← Category.assoc]
    exact yonedaEquiv_comp _ φ
  rw [hXY]

/-! ### The theorem -/

/-- **Any precubical embedding into a cube is run-injective.**  A run maps to a cube chain, whose
events flip distinct coordinates (`blockOf_unique`): distinct beads have disjoint blocks, and within
a bead `nones` is an order embedding.  No bipointedness, no injectivity of `φ`. -/
theorem cubeEmbed_runInjective {N : ℕ} (φ : K.toPsh ⟶ (□N).toPsh) :
    RunInjective (EdgeLabelling.comap φ (cubeLabelling N)) := by
  intro a
  rintro ⟨i, δ⟩ ⟨i', δ'⟩ heq
  have heq2 : evLabel (EdgeLabelling.comap φ (cubeLabelling N)) ⟨a, ⟨i, δ⟩⟩
      = evLabel (EdgeLabelling.comap φ (cubeLabelling N)) ⟨a, ⟨i', δ'⟩⟩ := heq
  rw [evLabel_comap_cube, evLabel_comap_cube] at heq2
  have hlen := wedgeToCubes_length a.dims (a.map.hom ≫ φ)
  have hmem : nones (toStar (φ.app _ (beadCell a i))) δ
      ∈ blockOf (pushChain φ a) (Fin.cast hlen.symm i) := by
    rw [blockOf_pushChain]
    exact Finset.orderEmbOfFin_mem _ (toStar (φ.app _ (beadCell a i))).prop δ
  have hmem' : nones (toStar (φ.app _ (beadCell a i))) δ
      ∈ blockOf (pushChain φ a) (Fin.cast hlen.symm i') := by
    rw [blockOf_pushChain, heq2]
    exact Finset.orderEmbOfFin_mem _ (toStar (φ.app _ (beadCell a i'))).prop δ'
  have hi : i = i' := by
    have hc := blockOf_unique (pushChain φ a) hmem hmem'
    have hval : (i : ℕ) = (i' : ℕ) := by simpa using congrArg Fin.val hc
    exact Fin.ext hval
  subst hi
  exact congrArg (Sigma.mk i) ((nones (toStar (φ.app _ (beadCell a i)))).injective heq2)

/-! ### Sculptures -/

/-- A **sculpture**: a precubical embedding of `K` into a standard cube `□ᵈⁱᵐ` (its events named by
the `dim` ambient coordinate directions).  `embed` is a bare precubical map — no basepoint
condition; `mono` witnesses that it is an embedding. -/
structure Sculpture (K : BPSet) where
  /-- The ambient cube dimension. -/
  dim : ℕ
  /-- The precubical embedding of `K` into `□ᵈⁱᵐ`. -/
  embed : K.toPsh ⟶ (□dim).toPsh
  /-- The embedding is a monomorphism (a sub-HDA of the cube). -/
  mono : Mono embed

/-- **The coordinate labelling of a sculpture:** the cube's `cubeLabelling` pulled back along the
embedding. -/
noncomputable def Sculpture.labelling (S : Sculpture K) : EdgeLabelling K (Fin S.dim) :=
  EdgeLabelling.comap S.embed (cubeLabelling S.dim)

/-- **A sculptural HDA is run-injective.**  (The embedding's monomorphism is not even needed —
`cubeEmbed_runInjective` gives this for any precubical map into a cube.) -/
theorem Sculpture.runInjective (S : Sculpture K) : RunInjective S.labelling :=
  cubeEmbed_runInjective S.embed

end CubeChains
