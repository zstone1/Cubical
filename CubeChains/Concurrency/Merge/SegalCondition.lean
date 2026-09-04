import CubeChains.Precubical.Basic.Representable
import CubeChains.Machinery.Cube.SymBox
import CubeChains.Precubical.Basic.Terminal
import CubeChains.Precubical.Wedge.WedgeTensor
import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Concurrency/Merge/SegalCondition — for `K` the wedge is the tensor

`wedgeToTensor X Y : X ∨ Y ⟶ X ⊗ᵍ Y` compares sequential with parallel composition, and
`cubeMerge` is it at a pair of cubes.  `IsSegal K` says `K` inverts it: read on cells, a `p`-cell
and a `q`-cell meeting at a vertex are the **front** face (first `p` axes, the rest at `0`) and the
**back** face (last `q` axes, the rest at `1`) of exactly one `(p+q)`-cell.

The gap between the two sides is the set of interleavings, which is what a bead merge of chains
sees — `Concurrency/Presentation/ElementsFibration`, where the condition meets `Ch K`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite StdCube BPSet ChainCat

namespace CubeChains

/-! ### The two legs of a bead merge -/

/-- The face on the first `p` axes, the last `q` held at `0`. -/
def frontHom (p q : ℕ) : ▫p ⟶ ▫(p + q) :=
  yonedaEquiv (wedgeInl (□p) (□q) ≫ (cubeMerge p q : BPSet.Hom _ _).hom)

/-- The face on the last `q` axes, the first `p` held at `1`. -/
def backHom (p q : ℕ) : ▫q ⟶ ▫(p + q) :=
  yonedaEquiv (wedgeInr (□p) (□q) ≫ (cubeMerge p q : BPSet.Hom _ _).hom)

theorem sign_frontHom (p q : ℕ) :
    (Box.sign (frontHom p q)).val = Fin.append (topCell p).val (constVertex q false).val :=
  sign_cubeMerge_inl p q

theorem sign_backHom (p q : ℕ) :
    (Box.sign (backHom p q)).val = Fin.append (constVertex p true).val (topCell q).val :=
  sign_cubeMerge_inr p q

theorem faceEmb_frontHom (p q : ℕ) (k : Fin p) : faceEmb (frontHom p q) k = Fin.castAdd q k :=
  Fin.ext (faceEmb_cubeMerge_inl p q k)

theorem faceEmb_backHom (p q : ℕ) (k : Fin q) : faceEmb (backHom p q) k = Fin.natAdd p k :=
  Fin.ext (faceEmb_cubeMerge_inr p q k)

/-! The two legs read coordinatewise: the front keeps the first block and holds the second at `0`,
the back holds the first at `1` and keeps the second. -/

@[simp] theorem cellCoord_frontHom_castAdd (p q : ℕ) (i : Fin p) :
    cellCoord (Box.sign (frontHom p q)) (Fin.castAdd q i) = Sum.inr i :=
  (cellCoord_eq_inr_iff _ _ _).2 (faceEmb_frontHom p q i).symm

@[simp] theorem cellCoord_frontHom_natAdd (p q : ℕ) (j : Fin q) :
    cellCoord (Box.sign (frontHom p q)) (Fin.natAdd p j) = Sum.inl false :=
  (cellCoord_eq_inl_iff _ _ _).2 (by rw [sign_frontHom, Fin.append_right]; rfl)

@[simp] theorem cellCoord_backHom_castAdd (p q : ℕ) (i : Fin p) :
    cellCoord (Box.sign (backHom p q)) (Fin.castAdd q i) = Sum.inl true :=
  (cellCoord_eq_inl_iff _ _ _).2 (by rw [sign_backHom, Fin.append_left]; rfl)

@[simp] theorem cellCoord_backHom_natAdd (p q : ℕ) (j : Fin q) :
    cellCoord (Box.sign (backHom p q)) (Fin.natAdd p j) = Sum.inr j :=
  (cellCoord_eq_inr_iff _ _ _).2 (faceEmb_backHom p q j).symm

/-! ### Faces of a cell -/

/-- The front face of a `(p+q)`-cell. -/
def frontFace (K : PrecubicalSet) (p q : ℕ) (c : K.cells (p + q)) : K.cells p :=
  K.map (frontHom p q).op c

/-- The back face of a `(p+q)`-cell. -/
def backFace (K : PrecubicalSet) (p q : ℕ) (c : K.cells (p + q)) : K.cells q :=
  K.map (backHom p q).op c

/-! ### Locality

`IsLocal K w` — every map into `K` restricts along `w` in exactly one way — is mathlib's left
Bousfield `isLocal` at the one-object property `{K}`, which is where `IsMultiplicative`,
`HasTwoOutOfThreeProperty` and the two `RespectsIso` directions come from.  The base points play
no part: they are a *property* of a presheaf map, preserved and reflected by precomposition with a
bi-pointed `w`, so the bi-pointed statement follows (`bijective_of_isLocal`). -/

/-- `K` is **local** for `w`: restriction along `w` is a bijection on maps into `K`. -/
def IsLocal (K : PrecubicalSet) {A B : BPSet} (w : A ⟶ B) : Prop :=
  ObjectProperty.isLocal (ObjectProperty.singleton K) w.hom

theorem isLocal_iff_bijective {K : PrecubicalSet} {A B : BPSet} (w : A ⟶ B) :
    IsLocal K w ↔ Function.Bijective fun f : B.toPsh ⟶ K => w.hom ≫ f where
  mp h := h K (by simp)
  mpr h Z hZ := by
    obtain rfl : K = Z := by simpa using hZ
    exact h

theorem IsLocal.bijective {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (h : IsLocal K w) :
    Function.Bijective fun f : B.toPsh ⟶ K => w.hom ≫ f := (isLocal_iff_bijective w).mp h

/-- A bi-pointed map carries the initial vertex to the initial vertex. -/
theorem initVertex_comp {A B : BPSet} (w : A ⟶ B) : A.initVertex ≫ w.hom = B.initVertex := by
  rw [show A.initVertex ≫ w.hom = yonedaEquiv.symm (w.hom⟪0⟫ A.init) from
    yonedaEquiv_symm_naturality_right ▫0 w.hom A.init, w.app_init]
  rfl

/-- …and the final vertex to the final vertex. -/
theorem finalVertex_comp {A B : BPSet} (w : A ⟶ B) : A.finalVertex ≫ w.hom = B.finalVertex := by
  rw [show A.finalVertex ≫ w.hom = yonedaEquiv.symm (w.hom⟪0⟫ A.final) from
    yonedaEquiv_symm_naturality_right ▫0 w.hom A.final, w.app_final]
  rfl

/-- **Locality only depends on `w` up to isomorphism of its source and target** — `RespectsIso`,
read on the arrow category. -/
theorem isLocal_congr {K : PrecubicalSet} {A B A' B' : BPSet} {w : A ⟶ B} {w' : A' ⟶ B'}
    (i : A' ≅ A) (j : B ≅ B') (he : w' = i.hom ≫ w ≫ j.hom) :
    IsLocal K w' ↔ IsLocal K w :=
  MorphismProperty.arrow_mk_iso_iff (ObjectProperty.isLocal (ObjectProperty.singleton K))
    (Arrow.isoMk (BPSet.toPshFunctor.mapIso i) (BPSet.toPshFunctor.mapIso j).symm
      (by subst he; simp [← BPSet.comp_hom]))

theorem IsLocal.congr {K : PrecubicalSet} {A B A' B' : BPSet} {w : A ⟶ B} {w' : A' ⟶ B'}
    (i : A' ≅ A) (j : B ≅ B') (he : w' = i.hom ≫ w ≫ j.hom) (h : IsLocal K w) : IsLocal K w' :=
  (isLocal_congr i j he).mpr h

/-- **Nothing to compare**: restriction along an isomorphism is a bijection. -/
theorem IsLocal.of_isIso {K : PrecubicalSet} {A B : BPSet} (w : A ⟶ B) [IsIso w.hom] :
    IsLocal K w := ObjectProperty.isLocal_of_isIso _ _

/-- Locality only sees `K` up to isomorphism — the one-object property, closed under isomorphism. -/
theorem IsLocal.of_iso {K L : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (e : K ≅ L)
    (h : IsLocal K w) : IsLocal L w := by
  have h' : ObjectProperty.isLocal (ObjectProperty.singleton K).isoClosure w.hom := by
    rwa [ObjectProperty.isoClosure_isLocal]
  intro Z hZ
  obtain rfl : L = Z := by simpa using hZ
  exact h' _ ⟨K, by simp, ⟨e.symm⟩⟩

/-! ### The condition

`wedgeToTensor X Y : X ∨ Y ⟶ X ⊗ᵍ Y` compares *sequential* with *parallel* composition: it runs
`X` at `Y`'s initial vertex, then `Y` at `X`'s final one.  Locality at it has two failure modes and
they are the whole story — a wedge with no tensor filler, or two tensor cells with the same wedge
restriction. -/

/-- **The Segal condition**: for `K` the wedge of two cubes *is* their tensor — a `(p+q)`-cell is
no more and no less than a `p`-cell followed by a `q`-cell. -/
def IsSegal (K : PrecubicalSet) : Prop := ∀ p q : ℕ, IsLocal K (wedgeToTensor (□p) (□q))

@[reassoc]
theorem tensorHom_inl {A B X Y : BPSet} (f : A ⟶ B) (g : X ⟶ Y) :
    wedgeInl A X ≫ (f ⊗ₘ g : A ∨ X ⟶ B ∨ Y).hom = f.hom ≫ wedgeInl B Y :=
  wedge2MapPsh_inl f g

@[reassoc]
theorem tensorHom_inr {A B X Y : BPSet} (f : A ⟶ B) (g : X ⟶ Y) :
    wedgeInr A X ≫ (f ⊗ₘ g : A ∨ X ⟶ B ∨ Y).hom = g.hom ≫ wedgeInr B Y :=
  wedge2MapPsh_inr f g

/-- **Locality is inherited by the right whiskering** `w ∨ 𝟙`: a map out of a wedge is a pair
agreeing at the glued vertex, and `w` only touches the left half. -/
theorem IsLocal.tensor_id {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (h : IsLocal K w)
    (Y : BPSet) : IsLocal K (w ⊗ₘ 𝟙 Y) := by
  refine (isLocal_iff_bijective _).mpr ⟨fun {f g} hfg => ?_, fun u => ?_⟩
  · have hfg' : (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f = (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := hfg
    refine wedge2_hom_ext (h.bijective.1 ?_) ?_
    · have hl : wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
          = wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
      rw [tensorHom_inl_assoc, tensorHom_inl_assoc] at hl
      exact hl
    · have hr : wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
          = wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
      rwa [tensorHom_inr_assoc, tensorHom_inr_assoc, BPSet.id_hom, Category.id_comp,
        Category.id_comp] at hr
  · obtain ⟨g, hg⟩ := h.bijective.2 (wedgeInl A Y ≫ u)
    have hg' : w.hom ≫ g = wedgeInl A Y ≫ u := hg
    have hcompat : B.finalVertex ≫ g = Y.initVertex ≫ (wedgeInr A Y ≫ u) := by
      rw [← finalVertex_comp w, Category.assoc, hg', ← Category.assoc, wedge2_condition A Y,
        Category.assoc]
    refine ⟨wedge2Desc g (wedgeInr A Y ≫ u) hcompat, ?_⟩
    show (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ wedge2Desc g (wedgeInr A Y ≫ u) hcompat = u
    refine wedge2_hom_ext ?_ ?_
    · rw [tensorHom_inl_assoc, wedge2Desc_inl, hg']
    · rw [tensorHom_inr_assoc, BPSet.id_hom, Category.id_comp, wedge2Desc_inr]

/-- **…and by the left whiskering** `𝟙 ∨ w`. -/
theorem IsLocal.id_tensor {K : PrecubicalSet} {A B : BPSet} (X : BPSet) {w : A ⟶ B}
    (h : IsLocal K w) : IsLocal K (𝟙 X ⊗ₘ w) := by
  refine (isLocal_iff_bijective _).mpr ⟨fun {f g} hfg => ?_, fun u => ?_⟩
  · have hfg' : (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f = (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := hfg
    refine wedge2_hom_ext ?_ (h.bijective.1 ?_)
    · have hl : wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
          = wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
      rwa [tensorHom_inl_assoc, tensorHom_inl_assoc, BPSet.id_hom, Category.id_comp,
        Category.id_comp] at hl
    · have hr : wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
          = wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
      rw [tensorHom_inr_assoc, tensorHom_inr_assoc] at hr
      exact hr
  · obtain ⟨g, hg⟩ := h.bijective.2 (wedgeInr X A ≫ u)
    have hg' : w.hom ≫ g = wedgeInr X A ≫ u := hg
    have hcompat : X.finalVertex ≫ (wedgeInl X A ≫ u) = B.initVertex ≫ g := by
      rw [← initVertex_comp w, Category.assoc, hg', ← Category.assoc, wedge2_condition X A,
        Category.assoc]
    refine ⟨wedge2Desc (wedgeInl X A ≫ u) g hcompat, ?_⟩
    show (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ wedge2Desc (wedgeInl X A ≫ u) g hcompat = u
    refine wedge2_hom_ext ?_ ?_
    · rw [tensorHom_inl_assoc, BPSet.id_hom, Category.id_comp, wedge2Desc_inl]
    · rw [tensorHom_inr_assoc, wedge2Desc_inr, hg']

/-- **The base points come along for free**: a bi-pointed `w` preserves and reflects them, so
locality upgrades to bi-pointed maps. -/
theorem bijective_of_isLocal {A B : BPSet} {K : BPSet} {w : A ⟶ B} (h : IsLocal K.toPsh w) :
    Function.Bijective fun f : B ⟶ K => w ≫ f := by
  constructor
  · exact fun {f g} hfg => BPSet.hom_ext (h.bijective.1 (congrArg (·.hom) hfg))
  · intro f
    obtain ⟨g, hg⟩ := h.bijective.2 f.hom
    refine ⟨⟨g, ?_, ?_⟩, BPSet.hom_ext hg⟩
    · rw [← w.app_init]
      exact (comp_app_cell hg 0 A.init).trans f.app_init
    · rw [← w.app_final]
      exact (comp_app_cell hg 0 A.final).trans f.app_final

/-- **Locality is bijectivity at every choice of base points** — the base points cost nothing in
one direction and are recovered in the other. -/
theorem isLocal_iff_bijective_repoint {A B : BPSet} (w : A ⟶ B) (K : BPSet) :
    IsLocal K.toPsh w
      ↔ ∀ u v : K.cells 0, Function.Bijective fun f : B ⟶ K.repoint u v => w ≫ f := by
  refine ⟨fun h u v => bijective_of_isLocal (K := K.repoint u v) h,
    fun h => (isLocal_iff_bijective _).mpr ⟨?_, ?_⟩⟩
  · intro f g hfg
    have hfg' : w.hom ≫ f = w.hom ≫ g := hfg
    have hb : ∀ (t : B.toPsh ⟶ K.toPsh) (c : A.cells 0),
        (w.hom ≫ t)⟪0⟫ c = t⟪0⟫ (w.hom⟪0⟫ c) := fun t c => (comp_app_cell rfl 0 c).symm
    have hu : g⟪0⟫ B.init = f⟪0⟫ B.init := by
      rw [← w.app_init, ← hb f A.init, ← hb g A.init, hfg']
    have hv : g⟪0⟫ B.final = f⟪0⟫ B.final := by
      rw [← w.app_final, ← hb f A.final, ← hb g A.final, hfg']
    have key : (⟨f, rfl, rfl⟩ : B ⟶ K.repoint (f⟪0⟫ B.init) (f⟪0⟫ B.final)) = ⟨g, hu, hv⟩ :=
      (h (f⟪0⟫ B.init) (f⟪0⟫ B.final)).1 (BPSet.hom_ext hfg')
    exact congrArg (fun t : B ⟶ K.repoint (f⟪0⟫ B.init) (f⟪0⟫ B.final) =>
      (t : BPSet.Hom _ _).hom) key
  · intro t
    obtain ⟨F, hF⟩ := (h (t⟪0⟫ A.init) (t⟪0⟫ A.final)).2 ⟨t, rfl, rfl⟩
    exact ⟨F.hom, congrArg (fun s : A ⟶ K.repoint (t⟪0⟫ A.init) (t⟪0⟫ A.final) =>
      (s : BPSet.Hom _ _).hom) hF⟩

/-- **The unit whiskering is the map itself** — the wedge unit is `□⁰`. -/
theorem IsLocal.of_unit_tensor {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B}
    (h : IsLocal K (𝟙 (𝟙_ BPSet) ⊗ₘ w)) : IsLocal K w :=
  IsLocal.congr (λ_ A).symm (λ_ B) (by
    rw [Iso.symm_hom, MonoidalCategory.id_tensorHom, leftUnitor_naturality, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]) h

theorem IsLocal.of_tensor_unit {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B}
    (h : IsLocal K (w ⊗ₘ 𝟙 (𝟙_ BPSet))) : IsLocal K w :=
  IsLocal.congr (ρ_ A).symm (ρ_ B) (by
    rw [Iso.symm_hom, MonoidalCategory.tensorHom_id, rightUnitor_naturality, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]) h

/-- **The Segal condition is locality at the bead merges.** -/
theorem isSegal_iff_isLocal_cubeMerge (K : PrecubicalSet) :
    IsSegal K ↔ ∀ p q : ℕ, IsLocal K (cubeMerge p q) :=
  forall_congr' fun p => forall_congr' fun q =>
    (isLocal_congr (w := wedgeToTensor (□p) (□q)) (Iso.refl _) (GeoTensor.cubeTensorIsoBP p q)
      (by rw [Iso.refl_hom, Category.id_comp]; rfl)).symm

/-! ### Reading the comparison on cells -/

/-- The final vertex of a cube map, read through Yoneda. -/
theorem yonedaEquiv_finalVertex_comp {K : PrecubicalSet} {n : ℕ} (f : (□n).toPsh ⟶ K) :
    yonedaEquiv ((□n).finalVertex ≫ f) = K.vertex₁ (yonedaEquiv f) :=
  (yonedaEquiv_comp _ _).trans
    (by rw [yonedaEquiv_finalVertex, PrecubicalSet.vertex₁_yonedaEquiv]; rfl)

/-- …and the initial vertex. -/
theorem yonedaEquiv_initVertex_comp {K : PrecubicalSet} {n : ℕ} (f : (□n).toPsh ⟶ K) :
    yonedaEquiv ((□n).initVertex ≫ f) = K.vertex₀ (yonedaEquiv f) :=
  (yonedaEquiv_comp _ _).trans
    (by rw [yonedaEquiv_initVertex, PrecubicalSet.vertex₀_yonedaEquiv]; rfl)

/-- **A map out of a cube is a cell** — cube Yoneda, at the bi-pointed spelling. -/
def cubeHomEquiv (K : PrecubicalSet) (m : ℕ) : ((□m).toPsh ⟶ K) ≃ K.cells m := yonedaEquiv

/-- **A map out of a wedge is a pair of maps agreeing at the glued vertex** — `wedge2Desc` and
`wedge2_hom_ext`, packaged. -/
def wedge2HomEquiv (X Y : BPSet) (K : PrecubicalSet) :
    ((X ∨ Y).toPsh ⟶ K) ≃
      {fg : (X.toPsh ⟶ K) × (Y.toPsh ⟶ K) // X.finalVertex ≫ fg.1 = Y.initVertex ≫ fg.2} where
  toFun f := ⟨(wedgeInl X Y ≫ f, wedgeInr X Y ≫ f),
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (wedge2_condition X Y))).trans
      (Category.assoc _ _ _)⟩
  invFun fg := wedge2Desc fg.1.1 fg.1.2 fg.2
  left_inv _ := wedge2_hom_ext (wedge2Desc_inl _ _ _) (wedge2Desc_inr _ _ _)
  right_inv _ := Subtype.ext (Prod.ext (wedge2Desc_inl _ _ _) (wedge2Desc_inr _ _ _))

/-- **A map out of a wedge of two cubes is a composable pair of cells** — the wedge descent, read
through cube Yoneda on each leg. -/
def wedgeCubeHomEquiv (K : PrecubicalSet) (p q : ℕ) :
    ((□p ∨ □q).toPsh ⟶ K) ≃ {xy : K.cells p × K.cells q // K.vertex₁ xy.1 = K.vertex₀ xy.2} :=
  (wedge2HomEquiv (□p) (□q) K).trans <|
    Equiv.subtypeEquiv (Equiv.prodCongr (cubeHomEquiv K p) (cubeHomEquiv K q)) fun fg =>
      yonedaEquiv.apply_eq_iff_eq.symm.trans
        (by rw [yonedaEquiv_finalVertex_comp, yonedaEquiv_initVertex_comp]; rfl)

@[simp] theorem wedgeCubeHomEquiv_comparison (K : PrecubicalSet) (p q : ℕ)
    (f : (□(p + q)).toPsh ⟶ K) :
    (wedgeCubeHomEquiv K p q ((cubeMerge p q : BPSet.Hom _ _).hom ≫ f)).1
      = (frontFace K p q (yonedaEquiv f), backFace K p q (yonedaEquiv f)) :=
  Prod.ext
    (((congrArg yonedaEquiv (Category.assoc _ _ _).symm).trans (yonedaEquiv_comp _ _)).trans
      (map_yonedaEquiv f (frontHom p q)).symm)
    (((congrArg yonedaEquiv (Category.assoc _ _ _).symm).trans (yonedaEquiv_comp _ _)).trans
      (map_yonedaEquiv f (backHom p q)).symm)

/-- **The front and back faces of a cell meet at a vertex.** -/
theorem vertex₁_frontFace (K : PrecubicalSet) (p q : ℕ) (c : K.cells (p + q)) :
    K.vertex₁ (frontFace K p q c) = K.vertex₀ (backFace K p q c) := by
  have h := (wedgeCubeHomEquiv K p q
    ((cubeMerge p q : BPSet.Hom _ _).hom ≫ yonedaEquiv.symm c)).2
  rwa [wedgeCubeHomEquiv_comparison, Equiv.apply_symm_apply] at h

/-- **The comparison, read on cells**: a `(p+q)`-cell goes to its front and back faces. -/
def faceComparison (K : PrecubicalSet) (p q : ℕ) :
    K.cells (p + q) → {xy : K.cells p × K.cells q // K.vertex₁ xy.1 = K.vertex₀ xy.2} :=
  fun c => ⟨(frontFace K p q c, backFace K p q c), vertex₁_frontFace K p q c⟩

/-- The wedge-tensor comparison at a pair of cubes *is* the face comparison. -/
theorem isLocal_cubeMerge_iff_bijective (K : PrecubicalSet) (p q : ℕ) :
    IsLocal K (cubeMerge p q) ↔ Function.Bijective (faceComparison K p q) := by
  have hcomm : faceComparison K p q = (wedgeCubeHomEquiv K p q)
      ∘ (fun f : (□(p + q)).toPsh ⟶ K => (cubeMerge p q : BPSet.Hom _ _).hom ≫ f)
      ∘ (cubeHomEquiv K (p + q)).symm := by
    funext c
    refine (Subtype.ext ((wedgeCubeHomEquiv_comparison K p q _).trans ?_)).symm
    rw [show yonedaEquiv ((cubeHomEquiv K (p + q)).symm c) = c from
      (cubeHomEquiv K (p + q)).apply_symm_apply c]
    rfl
  rw [isLocal_iff_bijective, hcomm]
  exact ((Equiv.comp_bijective _ (wedgeCubeHomEquiv K p q)).trans
    (Equiv.bijective_comp (cubeHomEquiv K (p + q)).symm _)).symm

/-- **The Segal condition is bijectivity of the face comparison.** -/
theorem isSegal_iff_bijective_faceComparison (K : PrecubicalSet) :
    IsSegal K ↔ ∀ p q : ℕ, Function.Bijective (faceComparison K p q) :=
  (isSegal_iff_isLocal_cubeMerge K).trans
    (forall_congr' fun p => forall_congr' fun q => isLocal_cubeMerge_iff_bijective K p q)

/-- **The cell reading of the Segal condition**: composable cells have a unique composite. -/
theorem isSegal_iff_existsUnique (K : PrecubicalSet) :
    IsSegal K ↔ ∀ (p q : ℕ) (x : K.cells p) (y : K.cells q), K.vertex₁ x = K.vertex₀ y →
      ∃! c : K.cells (p + q), frontFace K p q c = x ∧ backFace K p q c = y := by
  rw [isSegal_iff_bijective_faceComparison]
  refine forall_congr' fun p => forall_congr' fun q => ?_
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h x y hxy
    obtain ⟨c, hc, hu⟩ := h ⟨(x, y), hxy⟩
    exact ⟨c, ⟨congrArg (·.1.1) hc, congrArg (·.1.2) hc⟩,
      fun c' hc' => hu c' (Subtype.ext (Prod.ext hc'.1 hc'.2))⟩
  · intro h xy
    obtain ⟨c, hc, hu⟩ := h xy.1.1 xy.1.2 xy.2
    exact ⟨c, Subtype.ext (Prod.ext hc.1 hc.2),
      fun c' hc' => hu c' ⟨congrArg (·.1.1) hc', congrArg (·.1.2) hc'⟩⟩

/-- **Only the positive blocks matter**: at a unit factor the comparison is a pair of unitors. -/
theorem isSegal_iff_isLocal_cubeMerge_pos (K : PrecubicalSet) :
    IsSegal K ↔ ∀ p q : ℕ+, IsLocal K (cubeMerge (p : ℕ) (q : ℕ)) := by
  rw [isSegal_iff_isLocal_cubeMerge]
  refine ⟨fun h p q => h _ _, fun h p q => ?_⟩
  match p, q with
  | 0, _ => exact IsLocal.of_isIso _
  | _ + 1, 0 => exact IsLocal.of_isIso _
  | p + 1, q + 1 => exact h ⟨p + 1, p.succ_pos⟩ ⟨q + 1, q.succ_pos⟩

/-! ### The terminal object -/

/-- **The Segal condition only sees `K` up to isomorphism.** -/
theorem isSegal_of_iso {K L : PrecubicalSet} (e : K ≅ L) (h : IsSegal K) : IsSegal L :=
  fun p q => (h p q).of_iso e

/-- **The terminal precubical set is Segal** — one cell in each dimension, one composable pair. -/
theorem isSegal_Z : IsSegal Z := fun _ _ =>
  (isLocal_iff_bijective _).mpr
    ⟨fun _ _ _ => isTerminalZ.hom_ext _ _,
      fun _ => ⟨isTerminalZ.from _, isTerminalZ.hom_ext _ _⟩⟩

/-! ### Too few cells: the square's other traversal

`Box` is rigid, so `□(p+q)` has a single top cell — but the wedge has one map for each staircase.
The reordering `cubeReorder` is the missing filler: `□²` fails *surjectivity*, and injectivity
holds for free. -/

/-- A cube has one top cell — `Box` is rigid. -/
instance subsingleton_boxEnd (n : ℕ) : Subsingleton (▫n ⟶ ▫n) :=
  ⟨fun _ _ => Box.hom_ext ((eq_topCell _).trans (eq_topCell _).symm)⟩

instance subsingleton_cubeTop (n : ℕ) : Subsingleton ((□n).cells n) :=
  inferInstanceAs (Subsingleton (▫n ⟶ ▫n))

/-- **The reordering staircase has no filler**: `cubeReorder` is a map out of the wedge that does
not factor through the tensor. -/
theorem not_isLocal_cubeMerge_cube_two : ¬ IsLocal (□(1 + 1)).toPsh (cubeMerge 1 1) := by
  intro h
  obtain ⟨f, hf⟩ := h.bijective.2 (cubeReorder 1 1 : BPSet.Hom _ _).hom
  have hf' : (cubeMerge 1 1 : BPSet.Hom _ _).hom ≫ f = (cubeReorder 1 1 : BPSet.Hom _ _).hom := hf
  have hfid : f = 𝟙 ((□(1 + 1)).toPsh) :=
    (cubeHomEquiv ((□(1 + 1)).toPsh) (1 + 1)).injective
      (Subsingleton.elim (α := (□(1 + 1)).cells (1 + 1)) _ _)
  refine cubeMerge_ne_cubeReorder (BPSet.hom_ext ?_)
  rw [← hf', hfid, Category.comp_id]

/-- **A cell of a cube is determined by its front and back faces.**  The front reads the first
block of axes and holds the second at `0`, the back the reverse, so between them every ambient axis
is read twice, and the two readings agree only for the cell they came from: `Sum.inl`/`Sum.inr`
separates a fixed axis from a free one on whichever side sees it free. -/
theorem injective_faceComparison_cube (n p q : ℕ) :
    Function.Injective (faceComparison (□n).toPsh p q) := by
  intro c c' h
  have hf : Box.sign (frontHom p q ≫ c) = Box.sign (frontHom p q ≫ c') :=
    congrArg Box.sign (congrArg (fun z => z.1.1) h)
  have hb : Box.sign (backHom p q ≫ c) = Box.sign (backHom p q ≫ c') :=
    congrArg Box.sign (congrArg (fun z => z.1.2) h)
  rw [Box.sign_comp, Box.sign_comp] at hf
  rw [Box.sign_comp, Box.sign_comp] at hb
  refine Box.hom_ext (cell_ext_cellCoord fun a => ?_)
  have hfa := congrArg (fun s => cellCoord s a) hf
  have hba := congrArg (fun s => cellCoord s a) hb
  simp only [cellCoord_subst] at hfa hba
  rcases hc : cellCoord (Box.sign c) a with b | k <;>
    rcases hc' : cellCoord (Box.sign c') a with b' | k' <;>
    rw [hc, hc'] at hfa hba <;> simp only [Sum.elim_inl, Sum.elim_inr] at hfa hba
  · rw [Sum.inl.inj hfa]
  · induction k' using Fin.addCases with
    | left i => simp at hfa
    | right j => simp at hba
  · induction k using Fin.addCases with
    | left i => simp at hfa
    | right j => simp at hba
  · induction k using Fin.addCases with
    | left i =>
      induction k' using Fin.addCases with
      | left i' =>
        simp only [cellCoord_frontHom_castAdd, Sum.inr.injEq] at hfa
        subst hfa; rfl
      | right j' => simp at hfa
    | right j =>
      induction k' using Fin.addCases with
      | left i' => simp at hfa
      | right j' =>
        simp only [cellCoord_backHom_natAdd, Sum.inr.injEq] at hba
        subst hba; rfl

/-- **`□²` has too few cells**: one top cell against two edge paths. -/
theorem not_surjective_faceComparison_cube_two :
    ¬ Function.Surjective (faceComparison (□(1 + 1)).toPsh 1 1) := fun hs =>
  not_isLocal_cubeMerge_cube_two
    ((isLocal_cubeMerge_iff_bijective _ 1 1).mpr ⟨injective_faceComparison_cube _ 1 1, hs⟩)

theorem not_isSegal_cube_two : ¬ IsSegal (□(1 + 1)).toPsh := fun h =>
  not_isLocal_cubeMerge_cube_two ((isSegal_iff_isLocal_cubeMerge _).mp h 1 1)

/-! ## Separated: the injective half alone

`IsLocal` asks restriction along `w` to be *bijective*.  **Separated** asks only *injective*: a map
out of the target is determined by its restriction.  The two halves do different jobs downstream —
injectivity is what makes a lift **unique**, surjectivity what makes it **exist** — and they are
independent: `□²` is separated and not Segal, `H Z` is Segal-covering and not separated. -/

/-- `K` is **separated** for `w`: a map out of `w`'s target is determined by its restriction. -/
def IsSeparated (K : PrecubicalSet) {A B : BPSet} (w : A ⟶ B) : Prop :=
  Function.Injective fun f : B.toPsh ⟶ K => w.hom ≫ f

theorem IsLocal.isSeparated {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (h : IsLocal K w) :
    IsSeparated K w := h.bijective.1

theorem IsSeparated.of_isIso {K : PrecubicalSet} {A B : BPSet} (w : A ⟶ B) [IsIso w.hom] :
    IsSeparated K w := (IsLocal.of_isIso w).isSeparated

/-- **Separation composes** — which is what carries it along the multiplicative closure `W`. -/
theorem IsSeparated.comp {K : PrecubicalSet} {A B D : BPSet} {u : A ⟶ B} {v : B ⟶ D}
    (hu : IsSeparated K u) (hv : IsSeparated K v) : IsSeparated K (u ≫ v) := by
  intro f g hfg
  refine hv (hu ?_)
  simpa only [BPSet.comp_hom, Category.assoc] using hfg

/-- **Separation only depends on `w` up to isomorphism of its source and target.** -/
theorem IsSeparated.congr {K : PrecubicalSet} {A B A' B' : BPSet} {w : A ⟶ B} {w' : A' ⟶ B'}
    (i : A' ≅ A) (j : B ≅ B') (he : w' = i.hom ≫ w ≫ j.hom) (h : IsSeparated K w) :
    IsSeparated K w' := by
  subst he
  haveI : IsIso (i.hom).hom := ⟨(i.inv).hom, congrArg BPSet.Hom.hom i.hom_inv_id,
    congrArg BPSet.Hom.hom i.inv_hom_id⟩
  haveI : IsIso (j.hom).hom := ⟨(j.inv).hom, congrArg BPSet.Hom.hom j.hom_inv_id,
    congrArg BPSet.Hom.hom j.inv_hom_id⟩
  exact (IsSeparated.of_isIso i.hom).comp (h.comp (IsSeparated.of_isIso j.hom))

/-- **Separation is inherited by the right whiskering** `w ∨ 𝟙` — the injective half of
`IsLocal.tensor_id`, and it needs nothing of the surjective one. -/
theorem IsSeparated.tensor_id {K : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (h : IsSeparated K w)
    (Y : BPSet) : IsSeparated K (w ⊗ₘ 𝟙 Y) := by
  intro f g hfg
  have hfg' : (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f = (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := hfg
  refine wedge2_hom_ext (h ?_) ?_
  · have hl : wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
        = wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
    rw [tensorHom_inl_assoc, tensorHom_inl_assoc] at hl
    exact hl
  · have hr : wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
        = wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
    rwa [tensorHom_inr_assoc, tensorHom_inr_assoc, BPSet.id_hom, Category.id_comp,
      Category.id_comp] at hr

/-- **…and by the left whiskering** `𝟙 ∨ w`. -/
theorem IsSeparated.id_tensor {K : PrecubicalSet} {A B : BPSet} (X : BPSet) {w : A ⟶ B}
    (h : IsSeparated K w) : IsSeparated K (𝟙 X ⊗ₘ w) := by
  intro f g hfg
  have hfg' : (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f = (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := hfg
  refine wedge2_hom_ext ?_ (h ?_)
  · have hl : wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
        = wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
    rwa [tensorHom_inl_assoc, tensorHom_inl_assoc, BPSet.id_hom, Category.id_comp,
      Category.id_comp] at hl
  · have hr : wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
        = wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
    rw [tensorHom_inr_assoc, tensorHom_inr_assoc] at hr
    exact hr

/-- **The base points come along for free**, as for `IsLocal`. -/
theorem injective_of_isSeparated {A B : BPSet} {K : BPSet} {w : A ⟶ B}
    (h : IsSeparated K.toPsh w) : Function.Injective fun f : B ⟶ K => w ≫ f :=
  fun _ _ hfg => BPSet.hom_ext (h (congrArg (·.hom) hfg))

/-- **The Segal *separation* condition**: a cell is determined by its front and back faces. -/
def IsSegalSep (K : PrecubicalSet) : Prop := ∀ p q : ℕ, IsSeparated K (cubeMerge p q)

theorem IsSegal.isSegalSep {K : PrecubicalSet} (h : IsSegal K) : IsSegalSep K :=
  fun p q => ((isSegal_iff_isLocal_cubeMerge K).mp h p q).isSeparated

/-- **Separation is injectivity of the face comparison.** -/
theorem isSegalSep_iff_injective_faceComparison (K : PrecubicalSet) :
    IsSegalSep K ↔ ∀ p q : ℕ, Function.Injective (faceComparison K p q) := by
  refine forall_congr' fun p => forall_congr' fun q => ?_
  have hcomm : faceComparison K p q = (wedgeCubeHomEquiv K p q)
      ∘ (fun f : (□(p + q)).toPsh ⟶ K => (cubeMerge p q : BPSet.Hom _ _).hom ≫ f)
      ∘ (cubeHomEquiv K (p + q)).symm := by
    funext c
    refine (Subtype.ext ((wedgeCubeHomEquiv_comparison K p q _).trans ?_)).symm
    rw [show yonedaEquiv ((cubeHomEquiv K (p + q)).symm c) = c from
      (cubeHomEquiv K (p + q)).apply_symm_apply c]
    rfl
  rw [hcomm]
  exact ((Equiv.comp_injective _ (wedgeCubeHomEquiv K p q)).trans
    (Equiv.injective_comp (cubeHomEquiv K (p + q)).symm _)).symm

/-- **A cube is separated but not Segal** — it is surjectivity that breaks there
(`not_surjective_faceComparison_cube_two`), and this is the separated half on its own, with no
Segal hypothesis anywhere in its proof. -/
theorem isSegalSep_cube (n : ℕ) : IsSegalSep (□n).toPsh :=
  (isSegalSep_iff_injective_faceComparison _).mpr (injective_faceComparison_cube n)

end CubeChains
