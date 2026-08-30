import CubeChains.Chains.ElementsFibration
import CubeChains.Foundations.SymBox

/-!
# Chains/SegalCondition — for `K` the wedge is the tensor

`wedgeToTensor X Y : X ∨ Y ⟶ X ⊗ᵍ Y` compares sequential with parallel composition, and
`cubeMerge` is it at a pair of cubes.  `IsSegal K` says `K` inverts it: read on cells, a `p`-cell
and a `q`-cell meeting at a vertex are the **front** face (first `p` axes, the rest at `0`) and the
**back** face (last `q` axes, the rest at `1`) of exactly one `(p+q)`-cell.

The gap between the two sides is the set of interleavings, and it is what the bead merges see:
`InvertsMerges` at every choice of base points is exactly this condition on the positive blocks.
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

/-! ### The comparison map, and the condition

`wedgeToTensor X Y : X ∨ Y ⟶ X ⊗ᵍ Y` compares *sequential* with *parallel* composition: it runs
`X` at `Y`'s initial vertex, then `Y` at `X`'s final one.  Restricting along it is the map whose
two failure modes are the whole story — a wedge with no tensor filler, or two tensor cells with
the same wedge restriction. -/

/-- **The wedge-tensor comparison on maps into `K`**: restrict a map off the tensor to the wedge
that runs one factor after the other. -/
def wedgeTensorComparison (K : PrecubicalSet) (X Y : BPSet) :
    ((X ⊗ᵍ Y).toPsh ⟶ K) → ((X ∨ Y).toPsh ⟶ K) := fun f => (wedgeToTensor X Y).hom ≫ f

/-- **The Segal condition**: for `K` the wedge of two cubes *is* their tensor — a `(p+q)`-cell is
no more and no less than a `p`-cell followed by a `q`-cell. -/
def IsSegal (K : PrecubicalSet) : Prop :=
  ∀ p q : ℕ, Function.Bijective (wedgeTensorComparison K (□p) (□q))

/-! ### Locality

`IsLocal K w` — every map into `K` restricts along `w` in exactly one way.  The base points play
no part: they are a *property* of a presheaf map, preserved and reflected by precomposition with a
bi-pointed `w`, so the bi-pointed statement follows (`bijective_of_isLocal`). -/

/-- `K` is **local** for `w`: restriction along `w` is a bijection on maps into `K`. -/
def IsLocal (K : PrecubicalSet) {A B : BPSet} (w : A ⟶ B) : Prop :=
  Function.Bijective fun f : B.toPsh ⟶ K => w.hom ≫ f

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

/-- Restriction along an isomorphism — `yoneda`, at the underlying presheaves. -/
def precompIso {X Y : BPSet} (e : X ≅ Y) (K : PrecubicalSet) :
    (Y.toPsh ⟶ K) ≃ (X.toPsh ⟶ K) :=
  ((yoneda.obj K).mapIso (BPSet.toPshFunctor.mapIso e).op).toEquiv

/-- **Locality only depends on `w` up to isomorphism of its source and target.** -/
theorem isLocal_congr {K : PrecubicalSet} {A B A' B' : BPSet} {w : A ⟶ B} {w' : A' ⟶ B'}
    (i : A' ≅ A) (j : B ≅ B') (he : w' = i.hom ≫ w ≫ j.hom) :
    IsLocal K w' ↔ IsLocal K w := by
  have key : (fun f : B'.toPsh ⟶ K => w'.hom ≫ f)
      = (precompIso i K) ∘ (fun f : B.toPsh ⟶ K => w.hom ≫ f) ∘ (precompIso j K) := by
    funext f
    rw [he]
    simp only [BPSet.comp_hom, Function.comp_apply, Category.assoc]
    rfl
  show Function.Bijective (fun f : B'.toPsh ⟶ K => w'.hom ≫ f) ↔ _
  rw [key]
  exact (Equiv.comp_bijective _ (precompIso i K)).trans
    (Equiv.bijective_comp (precompIso j K) _)

theorem IsLocal.congr {K : PrecubicalSet} {A B A' B' : BPSet} {w : A ⟶ B} {w' : A' ⟶ B'}
    (i : A' ≅ A) (j : B ≅ B') (he : w' = i.hom ≫ w ≫ j.hom) (h : IsLocal K w) : IsLocal K w' :=
  (isLocal_congr i j he).mpr h

/-- Post-composition with an isomorphism of the target — `coyoneda`. -/
def postcompIso {K L : PrecubicalSet} (e : K ≅ L) (X : BPSet) : (X.toPsh ⟶ K) ≃ (X.toPsh ⟶ L) :=
  ((coyoneda.obj (op X.toPsh)).mapIso e).toEquiv

/-- Locality only sees `K` up to isomorphism. -/
theorem IsLocal.of_iso {K L : PrecubicalSet} {A B : BPSet} {w : A ⟶ B} (e : K ≅ L)
    (h : IsLocal K w) : IsLocal L w := by
  have key : (fun f : B.toPsh ⟶ L => w.hom ≫ f)
      = (postcompIso e A) ∘ (fun f : B.toPsh ⟶ K => w.hom ≫ f) ∘ (postcompIso e B).symm := by
    funext f
    show w.hom ≫ f = (w.hom ≫ f ≫ e.inv) ≫ e.hom
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
  show Function.Bijective fun f : B.toPsh ⟶ L => w.hom ≫ f
  rw [key]
  exact (postcompIso e A).bijective.comp (h.comp (postcompIso e B).symm.bijective)

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
  refine ⟨fun {f g} hfg => ?_, fun u => ?_⟩
  · have hfg' : (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f = (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := hfg
    refine wedge2_hom_ext (h.1 ?_) ?_
    · have hl : wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
          = wedgeInl A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
      rw [tensorHom_inl_assoc, tensorHom_inl_assoc] at hl
      exact hl
    · have hr : wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ f
          = wedgeInr A Y ≫ (w ⊗ₘ 𝟙 Y : A ∨ Y ⟶ B ∨ Y).hom ≫ g := by rw [hfg']
      rwa [tensorHom_inr_assoc, tensorHom_inr_assoc, BPSet.id_hom, Category.id_comp,
        Category.id_comp] at hr
  · obtain ⟨g, hg⟩ := h.2 (wedgeInl A Y ≫ u)
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
  refine ⟨fun {f g} hfg => ?_, fun u => ?_⟩
  · have hfg' : (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f = (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := hfg
    refine wedge2_hom_ext ?_ (h.1 ?_)
    · have hl : wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
          = wedgeInl X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
      rwa [tensorHom_inl_assoc, tensorHom_inl_assoc, BPSet.id_hom, Category.id_comp,
        Category.id_comp] at hl
    · have hr : wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ f
          = wedgeInr X A ≫ (𝟙 X ⊗ₘ w : X ∨ A ⟶ X ∨ B).hom ≫ g := by rw [hfg']
      rw [tensorHom_inr_assoc, tensorHom_inr_assoc] at hr
      exact hr
  · obtain ⟨g, hg⟩ := h.2 (wedgeInr X A ≫ u)
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
  · exact fun {f g} hfg => BPSet.hom_ext (h.1 (congrArg (·.hom) hfg))
  · intro f
    obtain ⟨g, hg⟩ := h.2 f.hom
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
  refine ⟨fun h u v => bijective_of_isLocal (K := K.repoint u v) h, fun h => ⟨?_, ?_⟩⟩
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
    IsSegal K ↔ ∀ p q : ℕ, IsLocal K (cubeMerge p q) := by
  refine forall_congr' fun p => forall_congr' fun q => ⟨fun h => ?_, fun h => ?_⟩
  · exact IsLocal.congr (w := wedgeToTensor (□p) (□q)) (Iso.refl _)
      (GeoTensor.cubeTensorIsoBP p q) (by rw [Iso.refl_hom, Category.id_comp]; rfl) h
  · exact IsLocal.congr (w := cubeMerge p q) (Iso.refl _) (GeoTensor.cubeTensorIsoBP p q).symm
      (by rw [Iso.refl_hom, Category.id_comp, cubeMerge, Category.assoc, Iso.symm_hom,
        Iso.hom_inv_id, Category.comp_id]) h

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
  rw [hcomm]
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

/-! ### Segal implies that the merges act bijectively

A merge *is* `𝟙 ∨ cubeMerge ∨ 𝟙` up to isomorphism (`CutData`), so the two whiskering lemmas and
`IsLocal.congr` carry the cube statement to every bead merge of every serial wedge. -/

/-- **Locality at the positive blocks makes every bead merge act bijectively.** -/
theorem invertsMerges_of_isLocal_cubeMerge {K : BPSet}
    (h : ∀ p q : ℕ+, IsLocal K.toPsh (cubeMerge (p : ℕ) (q : ℕ))) : ChainCat.InvertsMerges K := by
  refine ChainCat.invertsMerges_of_merge K ?_
  rintro a b u ⟨d, hd⟩
  have hw : IsLocal K.toPsh d.w := hd ▸ h d.p d.q
  have hu : IsLocal K.toPsh (ChainCat.Hom.φ u) :=
    IsLocal.congr d.e₁ d.e₂.symm
      (by rw [Iso.symm_hom, ← Category.assoc, d.sq, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])
      ((hw.tensor_id (⋁d.r)).id_tensor (⋁d.l))
  rw [isIso_iff_bijective]
  exact bijective_of_isLocal hu

/-- **The Segal condition makes every bead merge act bijectively.** -/
theorem invertsMerges_of_isSegal {K : BPSet} (h : IsSegal K.toPsh) : ChainCat.InvertsMerges K :=
  invertsMerges_of_isLocal_cubeMerge fun p q =>
    (isSegal_iff_isLocal_cubeMerge K.toPsh).mp h (p : ℕ) (q : ℕ)

/-- **…and conversely**: a bead merge is the wedge-tensor comparison at a pair of cubes, spliced
between two stretches of beads that the unitors strip off again. -/
theorem isLocal_cubeMerge_of_invertsMerges {K : BPSet} (p q : ℕ+)
    (h : ∀ u v : K.cells 0, ChainCat.InvertsMerges (K.repoint u v)) :
    IsLocal K.toPsh (cubeMerge (p : ℕ) (q : ℕ)) := by
  have hm : IsLocal K.toPsh (ChainCat.Hom.φ (ChainCat.mergeHom [] [] p q)) :=
    (isLocal_iff_bijective_repoint _ K).mpr fun u v =>
      (isIso_iff_bijective _).mp (h u v _ (ChainCat.Winf_mergeHom [] [] p q))
  exact IsLocal.of_tensor_unit (IsLocal.of_unit_tensor
    ((isLocal_congr (w := 𝟙 (⋁([] : List ℕ+)) ⊗ₘ (cubeMerge (p : ℕ) (q : ℕ) ⊗ₘ 𝟙 (⋁([] : List ℕ+))))
      (ChainCat.cutSrcIso ([] : List ℕ+) [] p q).symm
      (ChainCat.serialWedgeAppend ([] : List ℕ+) [p + q]) rfl).mp hm))

/-- **The Segal condition, on the positive blocks, is exactly `InvertsMerges` at every choice of
base points.** -/
theorem isLocal_cubeMerge_iff_invertsMerges_repoint (K : BPSet) :
    (∀ p q : ℕ+, IsLocal K.toPsh (cubeMerge (p : ℕ) (q : ℕ)))
      ↔ ∀ u v : K.cells 0, ChainCat.InvertsMerges (K.repoint u v) :=
  ⟨fun h u v => invertsMerges_of_isLocal_cubeMerge (K := K.repoint u v) h,
    fun h p q => isLocal_cubeMerge_of_invertsMerges p q h⟩

/-! ### The terminal object -/

/-- **The Segal condition only sees `K` up to isomorphism.** -/
theorem isSegal_of_iso {K L : PrecubicalSet} (e : K ≅ L) (h : IsSegal K) : IsSegal L :=
  (isSegal_iff_isLocal_cubeMerge L).mpr fun p q =>
    ((isSegal_iff_isLocal_cubeMerge K).mp h p q).of_iso e

/-- **The terminal precubical set is Segal** — one cell in each dimension, one composable pair. -/
theorem isSegal_Z : IsSegal Z := fun _ _ =>
  ⟨fun _ _ _ => isTerminalZ.hom_ext _ _,
    fun _ => ⟨isTerminalZ.from _, isTerminalZ.hom_ext _ _⟩⟩

/-- **…so the terminal bi-pointed set inverts the merges.** -/
theorem invertsMerges_Zbp : ChainCat.InvertsMerges Zbp := invertsMerges_of_isSegal isSegal_Z

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
  obtain ⟨f, hf⟩ := h.2 (cubeReorder 1 1 : BPSet.Hom _ _).hom
  have hf' : (cubeMerge 1 1 : BPSet.Hom _ _).hom ≫ f = (cubeReorder 1 1 : BPSet.Hom _ _).hom := hf
  have hfid : f = 𝟙 ((□(1 + 1)).toPsh) :=
    (cubeHomEquiv ((□(1 + 1)).toPsh) (1 + 1)).injective
      (Subsingleton.elim (α := (□(1 + 1)).cells (1 + 1)) _ _)
  refine cubeMerge_ne_cubeReorder (BPSet.hom_ext ?_)
  rw [← hf', hfid, Category.comp_id]

/-- **The square's cells cannot separate its traversals** — injectivity is free. -/
theorem injective_faceComparison_cube_two :
    Function.Injective (faceComparison (□(1 + 1)).toPsh 1 1) :=
  fun _ _ _ => Subsingleton.elim (α := (□(1 + 1)).cells (1 + 1)) _ _

/-- **`□²` has too few cells**: one top cell against two edge paths. -/
theorem not_surjective_faceComparison_cube_two :
    ¬ Function.Surjective (faceComparison (□(1 + 1)).toPsh 1 1) := fun hs =>
  not_isLocal_cubeMerge_cube_two
    ((isLocal_cubeMerge_iff_bijective _ 1 1).mpr ⟨injective_faceComparison_cube_two, hs⟩)

theorem not_isSegal_cube_two : ¬ IsSegal (□(1 + 1)).toPsh := fun h =>
  not_isLocal_cubeMerge_cube_two ((isSegal_iff_isLocal_cubeMerge _).mp h 1 1)

end CubeChains
