import CubeChains.Chains.Degree
import CubeChains.Foundations.Terminal
import CubeChains.Foundations.WedgeTensor
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Chains/MergeClass — the bead merges

`W` is the refinements whose coordinate map is **monotone** for the event order: gluing beads
together, without reordering the events inside them.  `pos` being the unique monotone bijection,
that is the same as preserving the flattening (`W_iff_pos`).

Its codimension-one members are the cuts whose middle map is the wedge-to-tensor comparison
`cubeMerge` (`merge`); the *other* comparison, `cubeReorder`, sends the two beads to the opposite
coordinate blocks and braids them.  A cut constrains the wedge map alone, so the class lives on
`Ch Zbp` — the serial wedges, `Zbp` being terminal — and every `Ch X` is its inverse image
along `pushforward`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CubeChains

namespace ChainCat

/-! ### `Ch Zbp`, the serial-wedge category

A wedge maps into the terminal `Zbp` in exactly one way, so an object of `Ch Zbp` is its dimension
sequence and a morphism is an arbitrary map of serial wedges. -/

/-- Serialisation: forget the classifying map, keep the wedge and the wedge map. -/
def toChZ (X : BPSet) : Ch X ⥤ Ch Zbp := pushforward (isTerminalZbp.from X)

@[simp] theorem toChZ_map_φ {X : BPSet} {a b : Ch X} (f : a ⟶ b) :
    Hom.φ ((toChZ X).map f) = Hom.φ f := rfl

/-- A chain of `Zbp` is its dimension sequence. -/
theorem Obj.eq_of_dims {a b : Ch Zbp} (h : a.dims = b.dims) : a = b := by
  obtain ⟨ad, am⟩ := a
  obtain ⟨bd, bm⟩ := b
  exact Obj.mk_eq_mk h (Subsingleton.elim _ _)

/-- `Ch Zbp` sitting inside `BPSet` as the serial wedges. -/
def serialWedgeInclusion : Ch Zbp ⥤ BPSet where
  obj a := ⋁a.dims
  map f := f.φ

/-- **A morphism of `Ch Zbp` is a bare wedge map** — the triangle over the terminal object is
free, so the inclusion is fully faithful (and computably so). -/
def serialWedgeFullyFaithful : serialWedgeInclusion.FullyFaithful where
  preimage φ := ⟨φ, Subsingleton.elim _ _⟩
  map_preimage _ := rfl
  preimage_map _ := hom_ext' rfl

instance : serialWedgeInclusion.Full := serialWedgeFullyFaithful.full

instance : serialWedgeInclusion.Faithful := serialWedgeFullyFaithful.faithful

/-! ### The class -/

variable (X : BPSet)

/-- **The bead merges**: the refinements that keep the events in order. -/
def W : MorphismProperty (Ch X) := fun _ _ f => Monotone (coordMap f.φ)

instance : (W X).IsMultiplicative where
  id_mem a := by
    change Monotone (coordMap (Hom.φ (𝟙 a)))
    rw [id_φ, coordMap_id]
    exact monotone_id
  comp_mem f g hf hg := by
    change Monotone (coordMap (Hom.φ (f ≫ g)))
    rw [comp_φ, coordMap_comp]
    exact hg.comp hf

/-- **Monotone is flattening-preserving**: a wedge map is a bijection on events, and `pos` is the
only monotone one. -/
theorem W_iff_pos {K : BPSet} {a b : Ch K} (f : a ⟶ b) :
    W K f ↔ ∀ e, (pos (coordMap (Hom.φ f) e) : ℕ) = (pos e : ℕ) :=
  ⟨fun h => pos_eq_of_monotone h (coordMap_bijective _),
    fun h _ _ hee =>
      le_iff_pos.mpr (Fin.le_def.mpr (by rw [h, h]; exact Fin.le_def.mp (le_iff_pos.mp hee)))⟩

/-! ### The generators -/

/-- A single bead merge, of any dimension: a cut whose middle map is the wedge-to-tensor
comparison. -/
def merge : MorphismProperty (Ch X) :=
  fun _ _ f => ∃ d : CutData f, d.w = cubeMerge (d.p : ℕ) (d.q : ℕ)

/-- A merge is codimension one; the converse fails (`not_merge_cutRefine_cubeReorder`). -/
theorem codim_eq_one_of_merge {a b : Ch X} {f : a ⟶ b} (h : merge X f) : codim f = 1 :=
  h.elim fun d _ => d.codim_eq_one

/-! ### Everything is a pullback from `Ch Zbp`

`CutData` constrains only the wedge map, and so does monotonicity, so `pushforward` neither creates
nor destroys either.  At the terminal object this says both are defined on the serial wedges. -/

variable {K L : BPSet} (g : K ⟶ L)

/-- A cut is data on the wedge map, copied field for field along `pushforward`. -/
def CutData.pushforwardEquiv {a b : Ch K} (f : a ⟶ b) :
    CutData f ≃ CutData ((pushforward g).map f) where
  toFun d := ⟨d.l, d.r, d.p, d.q, d.w, d.e₁, d.e₂, d.sq⟩
  invFun d := ⟨d.l, d.r, d.p, d.q, d.w, d.e₁, d.e₂, d.sq⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem merge_inverseImage : merge K = (merge L).inverseImage (pushforward g) := by
  ext a b f
  exact ⟨fun ⟨d, hw⟩ => ⟨CutData.pushforwardEquiv g f d, hw⟩,
    fun ⟨d, hw⟩ => ⟨(CutData.pushforwardEquiv g f).symm d, hw⟩⟩

theorem W_inverseImage : W K = (W L).inverseImage (pushforward g) := rfl

/-- **The generators live on the serial wedges.** -/
theorem merge_eq_inverseImage_toChZ (X : BPSet) : merge X = (merge Zbp).inverseImage (toChZ X) :=
  merge_inverseImage _

theorem W_eq_inverseImage_toChZ (X : BPSet) : W X = (W Zbp).inverseImage (toChZ X) :=
  W_inverseImage _

/-! ### The class is proper

A cut of the square into two edges may send either bead to either coordinate block: `cubeMerge`
and `cubeReorder` are both codimension one, and only the first is a merge. -/

/-- `□²` as a single bead. -/
def sqChain : Ch (□2) := ⟨[1 + 1], (ρ_ (□((1 + 1 : ℕ+) : ℕ))).hom⟩

/-- The wedge map cutting the square into two edges along a prescribed middle map. -/
def cutPhi (w : □1 ∨ □1 ⟶ □2) : ⋁[(1 : ℕ+), 1] ⟶ ⋁[(1 + 1 : ℕ+)] :=
  ((cutSrcIso [] [] 1 1).inv ≫ (𝟙 (⋁([] : List ℕ+)) ⊗ₘ (w ⊗ₘ 𝟙 (⋁([] : List ℕ+)))))
    ≫ (serialWedgeAppend ([] : List ℕ+) [(1 + 1 : ℕ+)]).hom

/-- `sqChain` cut into the two edges that `w` prescribes. -/
def cutChain (w : □1 ∨ □1 ⟶ □2) : Ch (□2) := ⟨[1, 1], cutPhi w ≫ sqChain.map⟩

/-- The refinement of `sqChain` with middle map `w`. -/
def cutRefine (w : □1 ∨ □1 ⟶ □2) : cutChain w ⟶ sqChain := ⟨cutPhi w, rfl⟩

/-- Its (unique) cut, with `w` back as the middle map. -/
def cutOfMiddle (w : □1 ∨ □1 ⟶ □2) : CutData (cutRefine w) where
  l := []
  r := []
  p := 1
  q := 1
  w := w
  e₁ := (cutSrcIso [] [] 1 1).symm
  e₂ := (serialWedgeAppend ([] : List ℕ+) [(1 + 1 : ℕ+)]).symm
  sq := (Iso.comp_inv_eq (serialWedgeAppend ([] : List ℕ+) [(1 + 1 : ℕ+)]).symm).mp rfl

theorem codim_cutRefine (w : □1 ∨ □1 ⟶ □2) : codim (cutRefine w) = 1 :=
  (cutOfMiddle w).codim_eq_one

/-- **A cut of the square is a merge exactly when its middle map is the staircase.** -/
theorem merge_cutRefine_iff (w : □1 ∨ □1 ⟶ □2) :
    merge (□2) (cutRefine w) ↔ w = cubeMerge 1 1 := by
  refine ⟨fun ⟨d, hd⟩ => ?_, fun hw => ⟨cutOfMiddle w, hw⟩⟩
  rwa [Subsingleton.elim d (cutOfMiddle w)] at hd

theorem merge_cutRefine_cubeMerge : merge (□2) (cutRefine (cubeMerge 1 1)) :=
  (merge_cutRefine_iff _).mpr rfl

/-- **The merges are a proper subclass of the codimension-one refinements.** -/
theorem not_merge_cutRefine_cubeReorder : ¬ merge (□2) (cutRefine (cubeReorder 1 1)) :=
  fun h => cubeMerge_ne_cubeReorder ((merge_cutRefine_iff _).mp h).symm

end ChainCat
