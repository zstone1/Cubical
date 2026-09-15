import CubeChains.Precubical.Chains.Altitude
import CubeChains.Precubical.Chains.Category
import CubeChains.Precubical.Chains.CubeNonSelfLinked
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Precubical/Chains/Embedding — a chain of a non-self-linked graded set is a subcomplex

Under `NonSelfLinked` and an altitude, the structure map `⋁d ⟶ K` of a chain is a monomorphism
(`descent_mono`); so `Ch K` is thin.  Into a chain injective on vertices, beads of `a` placed as
faces of beads of `b` assemble into a refinement `a ⟶ b` (`homOfBeads`), the chain condition being
reflected from `K`.  The cube meets both hypotheses (`chain_mono`).
-/

open CategoryTheory CategoryTheory.Limits Opposite StdCube BPSet

namespace CubeChain

variable {K : BPSet}

/-! ### A chain is a monomorphism

**Landmine: within-cube non-self-linkedness is not enough.**  `K = □²` with the corners
`(1,0) ~ (0,1)` identified carries the broken path `[bottom, top]` as a chain, killed by
`NonSelfLinked`; two 2-cubes glued at `c₀(1,0) ~ c₁(1,0)` share an edge between two blocks, killed
by the altitude (the cycle `c₀(1,0) → e → c₀(1,0)` wants height `+2` and `0` at once). -/

/-- **Altitude lower bound for a descent map**: every cell of `⋁d` lands at or above the start. -/
theorem descent_alt_ge (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
      (hch : IsCubeChain a c.toList b) {m : ℕ} (z : (⋁d).cells m),
      alt 0 a ≤ alt m ((wedgeDesc a b c hch).hom⟪m⟫ z)
  | a, b, [], c, hch, m, z => by
      rw [show (wedgeDesc a b c hch).hom⟪m⟫ z
          = (K.toPsh.cubeMap a)⟪m⟫ z from rfl,
        PrecubicalSet.alt_cubeMap alt hax]
      omega
  | a, b, n :: rest, c, hch, m, z => by
      rcases glue0_cell_cases (□(n : ℕ)).finalVertex _ m z with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, wedgeDesc_inl_app,
          show (yonedaEquiv.symm (c 0))⟪m⟫ x
            = (K.toPsh.cubeMap (c 0))⟪m⟫ x from rfl,
          PrecubicalSet.alt_cubeMap alt hax,
          show alt 0 a = alt ((n :: rest).get 0 : ℕ) (c 0) from by
            rw [← hch.1, PrecubicalSet.alt_vertex₀ alt hax]]
        omega
      · rw [← hy, wedgeDesc_inr_app]
        refine le_trans ?_ (descent_alt_ge alt hax (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2 y)
        rw [PrecubicalSet.alt_vertex₁ alt hax, ← hch.1, PrecubicalSet.alt_vertex₀ alt hax]
        omega

/-- **The descent map of a chain is pointwise injective**: `NonSelfLinked` inside a block, the
inductive hypothesis inside the tail, and across the junction the altitude separates a positive
head face (strictly below the junction) from every tail cell (at or above it). -/
theorem descent_app_inj (h₁ : K.NonSelfLinked) (alt : ∀ n, K.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude K.toPsh alt) :
    ∀ (a b : K.cells 0) {d : List ℕ+} (c : Beads K.toPsh d)
      (hch : IsCubeChain a c.toList b) (m : ℕ),
      Function.Injective ((wedgeDesc a b c hch).hom⟪m⟫)
  | a, _, [], _, _, m => fun _ _ huv => h₁ 0 a m huv
  | a, b, n :: rest, c, hch, m => by
      -- The cross case (head face `inl xu` collides with tail cell `inr yv`).
      have cross : ∀ (xu : (□(n : ℕ)).cells m) (yv : (⋁rest).cells m),
          (K.toPsh.cubeMap (c 0))⟪m⟫ xu
            = (wedgeDesc (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2).hom⟪m⟫ yv →
          (Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ xu
            = (Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ yv := by
        intro xu yv hcc
        have h1 := PrecubicalSet.alt_cubeMap alt hax (c 0) xu
        have h3 := descent_alt_ge alt hax (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2 yv
        have h4 := PrecubicalSet.alt_vertex₁ alt hax (c 0)
        have hT := trueCount_le (Box.sign xu)
        rw [hcc] at h1
        simp only [List.get_cons_zero] at h1 h3 h4
        have hd : (▫(n : ℕ)).dim = (n : ℕ) := rfl
        have hd2 : (Opposite.unop (Opposite.op ▫m)).dim = m := rfl
        have hn1 : 0 < (n : ℕ) := n.2
        have hm : m = 0 ∧ trueCount (Box.sign xu) = (n : ℕ) := by omega
        obtain ⟨hm0, htop⟩ := hm
        subst hm0
        have hxu : xu = (□(n : ℕ)).final := by
          have hev : Box.sign xu = constVertex (n : ℕ) true :=
            trueCount_eq_top _ htop
          have hxu' : xu = Box.ofSign (Box.sign xu) := (Box.ofSign_sign xu).symm
          rw [hxu', hev]; rfl
        have hyv : yv = (⋁rest).init := by
          apply descent_app_inj h₁ alt hax (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2 0
          rw [← hcc, hxu]
          exact (wedgeDesc_init (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2).symm
        rw [hxu, hyv]
        exact wedge2_glue (□(n : ℕ)) (⋁rest)
      intro u v huv
      rcases glue0_cell_cases (□(n : ℕ)).finalVertex _ m u with ⟨xu, hxu⟩ | ⟨yu, hyu⟩ <;>
        rcases glue0_cell_cases (□(n : ℕ)).finalVertex _ m v with ⟨xv, hxv⟩ | ⟨yv, hyv⟩
      · rw [← hxu, ← hxv, wedgeDesc_inl_app, wedgeDesc_inl_app] at huv
        rw [← hxu, ← hxv, h₁ (n : ℕ) (c 0) m huv]
      · rw [← hxu, ← hyv, wedgeDesc_inl_app, wedgeDesc_inr_app] at huv
        rw [← hxu, ← hyv]
        exact cross xu yv huv
      · rw [← hyu, ← hxv, wedgeDesc_inr_app, wedgeDesc_inl_app] at huv
        rw [← hyu, ← hxv]
        exact (cross xv yu huv.symm).symm
      · rw [← hyu, ← hyv, wedgeDesc_inr_app, wedgeDesc_inr_app] at huv
        rw [← hyu, ← hyv,
          descent_app_inj h₁ alt hax (K.toPsh.vertexEnd true (c 0)) b c.tail hch.2 m huv]

/-- **A chain's structure map is a monomorphism** under `NonSelfLinked` + an altitude — it is the
descent of its own beads, which is pointwise injective. -/
theorem descent_mono (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (b : Ch K) :
    Mono b.map.hom := by
  obtain ⟨alt, hax, _⟩ := h₂
  have hch := (ChainCat.chCubes K b).2
  have key : b.map = wedgeDescHom (beadCell b.map.hom) hch :=
    bpset_hom_ext_of_beadCell (congrFun (beadCell_wedgeDescHom _ hch).symm)
  rw [key, NatTrans.mono_iff_mono_app]
  exact fun X => (mono_iff_injective _).mpr (descent_app_inj h₁ alt hax _ _ _ hch X.unop.dim)

/-- **`Ch K` is thin** under `NonSelfLinked` + an altitude: arrows into `b` cancel against the
monomorphism `b.map`. -/
theorem chainCat_hom_subsingleton (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (a b : Ch K) : Subsingleton (a ⟶ b) := by
  haveI := descent_mono h₁ h₂ b
  exact ⟨fun f g => ChainCat.hom_ext' (hom_ext ((cancel_mono b.map.hom).mp
    ((congrArg BPSet.Hom.hom f.w).trans (congrArg BPSet.Hom.hom g.w).symm)))⟩

/-! ### Refinements from bead data -/

/-- The cells `a`'s beads occupy inside `⋁b`: bead `i` as the face `incl i` of bead `R i`. -/
def placedCell {a b : Ch K} (R : ChainCat.Bead a → ChainCat.Bead b)
    (incl : ∀ i, ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (R i) : ℕ)) :
    Beads (⋁b.dims).toPsh a.dims :=
  fun i => yonedaEquiv (yoneda.map (incl i) ≫ ιᵂ b.dims (R i))

/-- `b`'s structure map carries the placed cells to `a`'s beads. -/
theorem placedCell_push {a b : Ch K} {R : ChainCat.Bead a → ChainCat.Bead b}
    {incl : ∀ i, ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (R i) : ℕ)}
    (hincl : ∀ i, beadCell a.map.hom i = K.toPsh.map (incl i).op (beadCell b.map.hom (R i))) :
    (placedCell R incl).push (cellsMap b.map.hom) = beadCell a.map.hom :=
  funext fun i => ((yonedaEquiv_comp _ _).symm.trans
    (congrArg yonedaEquiv (Category.assoc _ _ _))).trans
    ((yonedaEquiv_naturality (ιᵂ b.dims (R i) ≫ b.map.hom) (incl i)).symm.trans (hincl i).symm)

/-- **A refinement from bead data**: into a chain whose structure map is injective on vertices,
beads of `a` placed as faces of beads of `b` pulling `b`'s cubes back to `a`'s form a chain of
`⋁b` — the chain condition is one on vertices, reflected from `K`. -/
def homOfBeads {a b : Ch K} (hb : Function.Injective (b.map.hom⟪0⟫))
    (R : ChainCat.Bead a → ChainCat.Bead b)
    (incl : ∀ i, ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (R i) : ℕ))
    (hincl : ∀ i, beadCell a.map.hom i = K.toPsh.map (incl i).op (beadCell b.map.hom (R i))) :
    a ⟶ b :=
  have hch : IsCubeChain (⋁b.dims).init (placedCell R incl).toList (⋁b.dims).final := by
    refine isCubeChain_of_push (u := cellsMap b.map.hom) (cellsMap_vertexEnd b.map.hom) hb _ _ _ ?_
    change IsCubeChain (b.map.hom⟪0⟫ _) _ (b.map.hom⟪0⟫ _)
    rw [← Beads.toList_push, placedCell_push hincl, b.map.app_init, b.map.app_final]
    exact (ChainCat.chCubes K a).2
  ⟨wedgeDescHom _ hch, bpset_hom_ext_of_beadCell fun i => by
    rw [comp_hom, beadCell_comp, beadCell_wedgeDescHom]
    exact congrFun (placedCell_push hincl) i⟩

@[simp] theorem beadCell_homOfBeads {a b : Ch K} (hb : Function.Injective (b.map.hom⟪0⟫))
    (R : ChainCat.Bead a → ChainCat.Bead b)
    (incl : ∀ i, ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (R i) : ℕ))
    (hincl : ∀ i, beadCell a.map.hom i = K.toPsh.map (incl i).op (beadCell b.map.hom (R i))) :
    beadCell (homOfBeads hb R incl hincl).φ.hom = placedCell R incl :=
  beadCell_wedgeDescHom _ _

end CubeChain

namespace CubeChains

open CubeChain ChainCat

/-- **A chain of the cube is a monomorphism.** -/
theorem chain_mono {N : ℕ} (A : Ch (□N)) : Mono A.map.hom :=
  descent_mono (cube_nonSelfLinked N) (BPSet.cube_admitsAltitude N) A

end CubeChains
