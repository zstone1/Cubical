import CubeChains.Chains.Segal
import CubeChains.Chains.SegalAltitude
import CubeChains.Foundations.Altitude

/-!
# Chains/SegalSplit

The combinatorial heart of the Segal splitting: a cube chain in `X ∨ Y` splits as an
`X`-prefix followed by a `Y`-suffix (`chain_split`), and the `wedgeToCubes` of a
concatenation is the corresponding append (`wedgeToCubes_concatChainMap`).  These feed
`ChainCat.chConcat_essSurj` (`Chains/SegalProd.lean`) and the computable morphism split
(`Chains/WedgeSplitMap.lean`).

The split uses only that the junction vertex `v` is hit at most once along a chain
(strict altitude increase across each cube), not any global altitude separation.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace ChainCat

open CubeChain

variable (X Y : BPSet)

/-- Push an `X`-cube into `X ∨ Y` along the left inclusion. -/
def inlPush (c : Σ n : ℕ+, X.cells (n : ℕ)) :
    Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ) :=
  ⟨c.1, (wedgeInl X Y)⟪(c.1 : ℕ)⟫ c.2⟩

/-- Push a `Y`-cube into `X ∨ Y` along the right inclusion. -/
def inrPush (c : Σ n : ℕ+, Y.cells (n : ℕ)) :
    Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ) :=
  ⟨c.1, (wedgeInr X Y)⟪(c.1 : ℕ)⟫ c.2⟩

/-- A vertex map `□⁰ ⟶ X` at the point evaluates to `X.final`. -/
theorem finalVertex_app (v : (□0).cells 0) :
    X.finalVertex⟪0⟫ v = X.final := by
  rw [finalVertex, vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply,
    show v = 𝟙 ▫0 from Subsingleton.elim _ _, op_id, X.toPsh.map_id]
  rfl

/-- A vertex map `□⁰ ⟶ Y` at the point evaluates to `Y.init`. -/
theorem initVertex_app (v : (□0).cells 0) :
    Y.initVertex⟪0⟫ v = Y.init := by
  rw [initVertex, vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply,
    show v = 𝟙 ▫0 from Subsingleton.elim _ _, op_id, Y.toPsh.map_id]
  rfl

/-- **The wedge intersection lemma.**  An `inl`-vertex equals an `inr`-vertex only at
the junction `v = inl X.final = inr Y.init`. -/
theorem wedge2_inl_eq_inr {u : X.cells 0} {w : Y.cells 0}
    (h : (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ u
       = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ w) :
    u = X.final ∧ w = Y.init := by
  obtain ⟨p, hp1, hp2⟩ :=
    Types.exists_of_isPullback (CubeChain.wedge2_isPullback_app X Y 0) u w h
  exact ⟨(hp1).symm.trans (finalVertex_app X p), (hp2).symm.trans (initVertex_app Y p)⟩

/-! ### The R-phase: a chain strictly above the junction is entirely on the `Y`-side. -/

/-- **R-phase.**  A cube chain whose start is an `inr`-vertex with altitude strictly
above the junction's (`C`) consists entirely of `inr`-cubes; corestrict to a chain in
`Y`. -/
theorem allR (alt : ∀ n, (wedge2 X Y).cells n → ℤ)
    (hax : (wedge2 X Y).toPsh.IsAltitude alt) (C : ℤ)
    (hC : C = alt 0 ((Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final)) :
    ∀ (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
      (s t : (wedge2 X Y).cells 0) (sy ty : Y.cells 0),
      s = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ sy →
      t = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ ty →
      alt 0 s > C → IsCubeChain s cs t →
      ∃ yc : List (Σ n : ℕ+, Y.cells (n : ℕ)),
        IsCubeChain sy yc ty ∧ cs = yc.map (inrPush X Y) := by
  intro cs
  induction cs with
  | nil =>
    intro s t sy ty hs ht _ hch
    have hch' : s = t := hch
    refine ⟨[], ?_, rfl⟩
    exact CubeChain.wedge2_inr_app_injective X Y (hs.symm.trans (hch'.trans ht))
  | cons hd rest ih =>
    intro s t sy ty hs ht halt hch
    obtain ⟨n, c⟩ := hd
    obtain ⟨hsrc, htail⟩ := hch
    rcases CubeChain.wedge2_cell_cases X Y (n : ℕ) c with ⟨x, hx⟩ | ⟨y, hy⟩
    · -- `c = inl x`: its source is both `inl`- and `inr`-vertex, so `= v`, altitude `C`.
      exfalso
      have hv0 : (wedge2 X Y).toPsh.vertex₀ c
          = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ (X.toPsh.vertex₀ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₀ (Glue.inl X.finalVertex Y.initVertex) x).symm
      have hs2 : s = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫
          (X.toPsh.vertex₀ x) := hsrc.symm.trans hv0
      have heq : (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ (X.toPsh.vertex₀ x)
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ sy :=
        hs2.symm.trans hs
      obtain ⟨hxfin, _⟩ := wedge2_inl_eq_inr X Y heq
      have haltC : alt 0 s = C := by rw [hs2, hxfin]; exact hC.symm
      rw [haltC] at halt
      exact absurd halt (lt_irrefl C)
    · -- `c = inr y`: corestrict and recurse (altitude stays strictly above `C`).
      have hv0 : (wedge2 X Y).toPsh.vertex₀ c
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ (Y.toPsh.vertex₀ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₀ (Glue.inr X.finalVertex Y.initVertex) y).symm
      have hsy : Y.toPsh.vertex₀ y = sy :=
        CubeChain.wedge2_inr_app_injective X Y (hv0.symm.trans (hsrc.trans hs))
      have hs' : (wedge2 X Y).toPsh.vertex₁ c
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ (Y.toPsh.vertex₁ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₁ (Glue.inr X.finalVertex Y.initVertex) y).symm
      have halt' : alt 0 ((wedge2 X Y).toPsh.vertex₁ c) > C := by
        have e1 := PrecubicalSet.alt_vertex₁ alt hax c
        have e2 : alt (n : ℕ) c = alt 0 s := by
          rw [← PrecubicalSet.alt_vertex₀ alt hax c, hsrc]
        have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.2
        rw [e1, e2]; omega
      obtain ⟨yc', hchain', hmap'⟩ :=
        ih ((wedge2 X Y).toPsh.vertex₁ c) t (Y.toPsh.vertex₁ y) ty hs' ht halt' htail
      refine ⟨⟨n, y⟩ :: yc', ⟨hsy, hchain'⟩, ?_⟩
      simp only [List.map_cons]
      rw [hmap', ← hy]
      rfl

/-! ### The L-phase: peel `inl`-cubes until the single junction crossing. -/

/-- **The chain split (with left start).**  A chain from an `inl`-vertex `inl sx` to the
final vertex splits into an `X`-chain prefix (from `sx`) and a `Y`-chain suffix. -/
theorem splitL (alt : ∀ n, (wedge2 X Y).cells n → ℤ)
    (hax : (wedge2 X Y).toPsh.IsAltitude alt) (C : ℤ)
    (hC : C = alt 0 ((Glue.inl X.finalVertex Y.initVertex)⟪0⟫ X.final)) :
    ∀ (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
      (sx : X.cells 0) (s : (wedge2 X Y).cells 0),
      s = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ sx →
      IsCubeChain s cs (wedge2 X Y).final →
      ∃ (xc : List (Σ n : ℕ+, X.cells (n : ℕ)))
        (yc : List (Σ n : ℕ+, Y.cells (n : ℕ))),
        IsCubeChain sx xc X.final ∧ IsCubeChain Y.init yc Y.final
          ∧ cs = xc.map (inlPush X Y) ++ yc.map (inrPush X Y) := by
  intro cs
  induction cs with
  | nil =>
    intro sx s hs hch
    have hch' : s = (wedge2 X Y).final := hch
    have hii : (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ sx
        = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ Y.final :=
      hs.symm.trans hch'
    obtain ⟨hsx, hyf⟩ := wedge2_inl_eq_inr X Y hii
    exact ⟨[], [], hsx, hyf.symm, rfl⟩
  | cons hd rest ih =>
    intro sx s hs hch
    obtain ⟨n, c⟩ := hd
    obtain ⟨hsrc, htail⟩ := hch
    rcases CubeChain.wedge2_cell_cases X Y (n : ℕ) c with ⟨x, hx⟩ | ⟨y, hy⟩
    · -- `c = inl x`: still in the L-phase, recurse.
      have hv0 : (wedge2 X Y).toPsh.vertex₀ c
          = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ (X.toPsh.vertex₀ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₀ (Glue.inl X.finalVertex Y.initVertex) x).symm
      have hsx : X.toPsh.vertex₀ x = sx :=
        CubeChain.wedge2_inl_app_injective X Y (hv0.symm.trans (hsrc.trans hs))
      have hs' : (wedge2 X Y).toPsh.vertex₁ c
          = (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ (X.toPsh.vertex₁ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₁ (Glue.inl X.finalVertex Y.initVertex) x).symm
      obtain ⟨xc', yc', hchx, hchy, hmap⟩ :=
        ih (X.toPsh.vertex₁ x) ((wedge2 X Y).toPsh.vertex₁ c) hs' htail
      refine ⟨⟨n, x⟩ :: xc', yc', ⟨hsx, hchx⟩, hchy, ?_⟩
      simp only [List.map_cons, List.cons_append]
      rw [hmap, ← hx]
      rfl
    · -- `c = inr y`: the single junction crossing; the rest is R-phase.
      have hv0 : (wedge2 X Y).toPsh.vertex₀ c
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ (Y.toPsh.vertex₀ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₀ (Glue.inr X.finalVertex Y.initVertex) y).symm
      have heq : (Glue.inl X.finalVertex Y.initVertex)⟪0⟫ sx
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ (Y.toPsh.vertex₀ y) :=
        hs.symm.trans (hsrc.symm.trans hv0)
      obtain ⟨hsxfin, hy0⟩ := wedge2_inl_eq_inr X Y heq
      have hsC : alt 0 s = C := by rw [hs, hsxfin]; exact hC.symm
      have hs' : (wedge2 X Y).toPsh.vertex₁ c
          = (Glue.inr X.finalVertex Y.initVertex)⟪0⟫ (Y.toPsh.vertex₁ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₁ (Glue.inr X.finalVertex Y.initVertex) y).symm
      have halt' : alt 0 ((wedge2 X Y).toPsh.vertex₁ c) > C := by
        have e1 := PrecubicalSet.alt_vertex₁ alt hax c
        have e2 : alt (n : ℕ) c = alt 0 s := by
          rw [← PrecubicalSet.alt_vertex₀ alt hax c, hsrc]
        have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.2
        rw [e1, e2, hsC]; omega
      obtain ⟨yc', hchy, hmap⟩ :=
        allR X Y alt hax C hC rest ((wedge2 X Y).toPsh.vertex₁ c)
          (wedge2 X Y).final (Y.toPsh.vertex₁ y) Y.final hs' rfl halt' htail
      refine ⟨[], ⟨n, y⟩ :: yc', ?_, ⟨hy0, hchy⟩, ?_⟩
      · -- `IsCubeChain sx [] X.final`, i.e. `sx = X.final`.
        exact hsxfin
      · simp only [List.map_nil, List.nil_append, List.map_cons]
        rw [hmap, ← hy]
        rfl

/-- **The chain split.**  A full cube chain in `X ∨ Y` splits into an `X`-chain and a
`Y`-chain glued at the junction, on the nose at the level of cube lists. -/
theorem chain_split (h : (wedge2 X Y).AdmitsAltitude)
    (cs : List (Σ n : ℕ+, (wedge2 X Y).cells (n : ℕ)))
    (hch : IsCubeChain (wedge2 X Y).init cs (wedge2 X Y).final) :
    ∃ (xc : List (Σ n : ℕ+, X.cells (n : ℕ)))
      (yc : List (Σ n : ℕ+, Y.cells (n : ℕ))),
      IsCubeChain X.init xc X.final ∧ IsCubeChain Y.init yc Y.final
        ∧ cs = xc.map (inlPush X Y) ++ yc.map (inrPush X Y) := by
  obtain ⟨alt, hax, _⟩ := h
  exact splitL X Y alt hax _ rfl cs X.init (wedge2 X Y).init rfl hch

/-! ### `wedgeToCubes` naturality and appending -/

/-- **Reading cubes commutes with post-composition** (naturality of `wedgeToCubes`). -/
theorem wedgeToCubes_comp {K L : BPSet} (g : K.toPsh ⟶ L.toPsh) :
    ∀ (dims : List ℕ+) (φ : (⋁dims).toPsh ⟶ K.toPsh),
      CubeChain.wedgeToCubes ⟨dims, φ ≫ g⟩
        = (CubeChain.wedgeToCubes ⟨dims, φ⟩).map
            (fun c => ⟨c.1, g⟪(c.1 : ℕ)⟫ c.2⟩)
  | [], _ => by simp [CubeChain.wedgeToCubes]
  | x :: rest, φ => by
      simp only [CubeChain.wedgeToCubes, List.map_cons]
      refine congr_arg₂ List.cons ?_ ?_
      · have hval : yonedaEquiv (Glue.inl _ _ ≫ φ ≫ g)
            = g⟪(x : ℕ)⟫ (yonedaEquiv (Glue.inl _ _ ≫ φ)) :=
          (congrArg yonedaEquiv (Category.assoc _ φ g).symm).trans
            (yonedaEquiv_comp (Glue.inl _ _ ≫ φ) g)
        exact congrArg (fun z => (⟨x, z⟩ : Σ m : ℕ+, L.cells (m : ℕ))) hval
      · exact (congrArg (fun m => CubeChain.wedgeToCubes ⟨rest, m⟩)
            (Category.assoc (Glue.inr _ _) φ g)).symm.trans
          (wedgeToCubes_comp g rest (Glue.inr _ _ ≫ φ))

/-- **`wedgeToCubes` of an appended serial wedge splits** as the append of the two
half-restrictions along `wedgeInclL`/`wedgeInclR`. -/
theorem wedgeToCubes_append {K : BPSet} :
    ∀ (da db : List ℕ+) (φ : (⋁(da ++ db)).toPsh ⟶ K.toPsh),
      CubeChain.wedgeToCubes ⟨da ++ db, φ⟩
        = CubeChain.wedgeToCubes ⟨da, wedgeInclL da db ≫ φ⟩
          ++ CubeChain.wedgeToCubes ⟨db, wedgeInclR da db ≫ φ⟩
  | [], db, φ => by
      change CubeChain.wedgeToCubes ⟨db, φ⟩
          = CubeChain.wedgeToCubes ⟨([] : List ℕ+), wedgeInclL [] db ≫ φ⟩
            ++ CubeChain.wedgeToCubes ⟨db, wedgeInclR [] db ≫ φ⟩
      rw [wedgeInclR_nil_left]
      simp only [CubeChain.wedgeToCubes, List.nil_append, Category.id_comp]
  | n :: da', db, φ => by
      simp only [CubeChain.wedgeToCubes, List.cons_append]
      set cinl := Glue.inl (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex with hcinl
      set cinr := Glue.inr (□(n : ℕ)).finalVertex
        (⋁(da' ++ db)).initVertex with hcinr
      set dinl := Glue.inl (□(n : ℕ)).finalVertex
        (⋁da').initVertex with hdinl
      set dinr := Glue.inr (□(n : ℕ)).finalVertex
        (⋁da').initVertex with hdinr
      have hhead : dinl ≫ wedgeInclL (n :: da') db = cinl := by
        rw [hdinl, hcinl, wedgeInclL_cons]; exact Glue.inl_desc _ _ _
      have htail : dinr ≫ wedgeInclL (n :: da') db = wedgeInclL da' db ≫ cinr := by
        rw [hdinr, hcinr, wedgeInclL_cons]; exact Glue.inr_desc _ _ _
      have hRcons : wedgeInclR (n :: da') db = wedgeInclR da' db ≫ cinr := by
        rw [hcinr]; exact wedgeInclR_cons n da' db
      have hh : dinl ≫ (wedgeInclL (n :: da') db ≫ φ) = cinl ≫ φ :=
        (Category.assoc dinl (wedgeInclL (n :: da') db) φ).symm.trans (congrArg (· ≫ φ) hhead)
      have hL : wedgeInclL da' db ≫ (cinr ≫ φ) = dinr ≫ (wedgeInclL (n :: da') db ≫ φ) :=
        ((Category.assoc (wedgeInclL da' db) cinr φ).symm.trans
          (congrArg (· ≫ φ) htail.symm)).trans (Category.assoc dinr (wedgeInclL (n :: da') db) φ)
      have hR : wedgeInclR da' db ≫ (cinr ≫ φ) = wedgeInclR (n :: da') db ≫ φ :=
        (Category.assoc (wedgeInclR da' db) cinr φ).symm.trans (congrArg (· ≫ φ) hRcons.symm)
      refine congr_arg₂ List.cons ?_ ?_
      · exact congrArg
          (fun z => (⟨n, yonedaEquiv z⟩ : Σ m : ℕ+, K.cells (m : ℕ))) hh.symm
      · exact (wedgeToCubes_append da' db (cinr ≫ φ)).trans
          (congr_arg₂ (· ++ ·)
            (congrArg (fun m => CubeChain.wedgeToCubes ⟨da', m⟩) hL)
            (congrArg (fun m => CubeChain.wedgeToCubes ⟨db, m⟩) hR))

/-- **`wedgeToCubes` of a concatenation** is the append of the two chains' cubes, pushed
into `X ∨ Y` along `inl`/`inr`. -/
theorem wedgeToCubes_concatChainMap (a : Obj X) (b : Obj Y) :
    CubeChain.wedgeToCubes ⟨a.dims ++ b.dims, (concatChainMap X Y a b).hom⟩
      = (CubeChain.wedgeToCubes ⟨a.dims, a.map.hom⟩).map (inlPush X Y)
        ++ (CubeChain.wedgeToCubes ⟨b.dims, b.map.hom⟩).map (inrPush X Y) := by
  have hL : CubeChain.wedgeToCubes ⟨a.dims, wedgeInclL a.dims b.dims ≫ (concatChainMap X Y a b).hom⟩
      = (CubeChain.wedgeToCubes ⟨a.dims, a.map.hom⟩).map (inlPush X Y) := by
    rw [concatChainMap_inclL X Y a b]
    exact wedgeToCubes_comp (L := wedge2 X Y) (Glue.inl X.finalVertex Y.initVertex)
      a.dims a.map.hom
  have hR : CubeChain.wedgeToCubes ⟨b.dims, wedgeInclR a.dims b.dims ≫ (concatChainMap X Y a b).hom⟩
      = (CubeChain.wedgeToCubes ⟨b.dims, b.map.hom⟩).map (inrPush X Y) := by
    rw [concatChainMap_inclR X Y a b]
    exact wedgeToCubes_comp (L := wedge2 X Y) (Glue.inr X.finalVertex Y.initVertex)
      b.dims b.map.hom
  rw [wedgeToCubes_append a.dims b.dims (concatChainMap X Y a b).hom, hL, hR]

/-- Two chains in `K` with the same read-off cube list are equal. -/
theorem Obj.eq_of_wedgeToCubes {K : BPSet} {c d : Obj K}
    (h : CubeChain.wedgeToCubes ⟨c.dims, c.map.hom⟩
       = CubeChain.wedgeToCubes ⟨d.dims, d.map.hom⟩) : c = d := by
  obtain ⟨cd, cm⟩ := c
  obtain ⟨dd, dm⟩ := d
  have hdims : cd = dd := by
    rw [← CubeChain.wedgeToCubes_dims cd cm.hom, ← CubeChain.wedgeToCubes_dims dd dm.hom, h]
  subst hdims
  have hmaps : cm.hom = dm.hom :=
    CubeChain.wedgeToCubes_inj cd cm.hom dm.hom h (cm.app_init.trans dm.app_init.symm)
  rw [hom_ext hmaps]

/-! ### Factorization infrastructure for the morphism split

The append pushout square `append_isPushout` (giving the cell-cases dichotomy and
junction-disjointness `append_inter`), and `himg_reduce` (promote an image-covering fact from
positive cells to all cells).  The factorization itself is computable and lives in
`Chains/WedgeSplitMap.lean` (`leftFactor`/`rightFactor`). -/

/-- The left half-inclusion is injective in every dimension (it is a mono). -/
theorem wedgeInclL_app_injective (da db : List ℕ+) (k : Boxᵒᵖ) :
    Function.Injective ((wedgeInclL da db).app k) := by
  have : Mono ((wedgeInclL da db).app k) :=
    (NatTrans.mono_iff_mono_app (wedgeInclL da db)).mp (wedgeInclL_mono da db) k
  exact CategoryTheory.injective_of_mono _

/-- The right half-inclusion is injective in every dimension (it is a mono). -/
theorem wedgeInclR_app_injective (da db : List ℕ+) (k : Boxᵒᵖ) :
    Function.Injective ((wedgeInclR da db).app k) := by
  have : Mono ((wedgeInclR da db).app k) :=
    (NatTrans.mono_iff_mono_app (wedgeInclR da db)).mp (wedgeInclR_mono da db) k
  exact CategoryTheory.injective_of_mono _

/-- **The append gluing square is a pushout.**  `□^∨(da ++ db)` glues `□^∨(da)` and
`□^∨(db)` along the junction `□⁰` (final vertex of `da` = init vertex of `db`), via the
two half-inclusions. -/
theorem append_isPushout : ∀ (da db : List ℕ+),
    IsPushout (⋁db).initVertex (⋁da).finalVertex
      (wedgeInclR da db) (wedgeInclL da db)
  | [], db => by
      have e1 : (⋁([] : List ℕ+)).finalVertex = 𝟙 (yoneda.obj ▫0) :=
        cube0_finalVertex_eq_id
      rw [e1, wedgeInclR_nil_left, wedgeInclL_nil_left]
      exact IsPushout.of_id_snd
  | n :: da', db => by
      have key := (append_isPushout da' db).paste_vert (wedgeInclL_cons_isPushout n da' db).flip
      rw [← wedge2_finalVertex (□(n : ℕ)) (⋁da')] at key
      rw [wedgeInclR_cons]
      exact key

/-- The append gluing square, transported to `Type` at level `m`. -/
theorem append_isPushout_app (da db : List ℕ+) (m : ℕ) :
    IsPushout ((⋁db).initVertex⟪m⟫)
      ((⋁da).finalVertex⟪m⟫)
      ((wedgeInclR da db)⟪m⟫)
      ((wedgeInclL da db)⟪m⟫) :=
  (append_isPushout da db).map (F := (evaluation Boxᵒᵖ Type).obj (op ▫m))

/-- The append gluing square is a pullback at every level. -/
theorem append_isPullback_app (da db : List ℕ+) (m : ℕ) :
    IsPullback ((⋁db).initVertex⟪m⟫)
      ((⋁da).finalVertex⟪m⟫)
      ((wedgeInclR da db)⟪m⟫)
      ((wedgeInclL da db)⟪m⟫) :=
  Types.isPullback_of_isPushout (append_isPushout_app da db m)
    (CubeChain.vertexMap_app_injective (⋁db).initVertex)

/-- **Junction disjointness.**  In `□^∨(da ++ db)`, a vertex that is both a
`wedgeInclL`-image and a `wedgeInclR`-image is the junction: the `da`-vertex is the
final vertex of `□^∨(da)` and the `db`-vertex is the init vertex of `□^∨(db)`. -/
theorem append_inter (da db : List ℕ+) (wL : (⋁da).cells 0)
    (wR : (⋁db).cells 0)
    (h : (wedgeInclL da db)⟪0⟫ wL
       = (wedgeInclR da db)⟪0⟫ wR) :
    wL = (⋁da).final ∧ wR = (⋁db).init := by
  obtain ⟨p, hp1, hp2⟩ := Types.exists_of_isPullback (append_isPullback_app da db 0) wR wL h.symm
  exact ⟨hp2.symm.trans (finalVertex_app (⋁da) p),
    hp1.symm.trans (initVertex_app (⋁db) p)⟩

/-! ### Block detection at bead levels

Which half of `⋁(a ++ b)` a bead cell lies in is decided by which side of `X ∨ Y` its image
under the concatenation lands on — the two blocks cannot both catch a positive-dimensional
cell (`wedge2_inl_ne_inr`). -/

theorem concatChainMap_inclL_app (a : Obj X) (b : Obj Y) (m : ℕ) (u : (⋁a.dims).cells m) :
    (concatChainMap X Y a b).hom⟪m⟫ ((wedgeInclL a.dims b.dims)⟪m⟫ u)
      = (wedgeInl X Y)⟪m⟫ (a.map.hom⟪m⟫ u) :=
  comp_app_cell₂ (concatChainMap_inclL X Y a b) m u

theorem concatChainMap_inclR_app (a : Obj X) (b : Obj Y) (m : ℕ) (u : (⋁b.dims).cells m) :
    (concatChainMap X Y a b).hom⟪m⟫ ((wedgeInclR a.dims b.dims)⟪m⟫ u)
      = (wedgeInr X Y)⟪m⟫ (b.map.hom⟪m⟫ u) :=
  comp_app_cell₂ (concatChainMap_inclR X Y a b) m u

/-- A bead cell whose concatenated image lies on the `X`-side comes from the `a`-block. -/
theorem wedgeInclL_of_concat_inl (a : Obj X) (b : Obj Y) {m : ℕ} (hm : 1 ≤ m)
    {t : (⋁(a.dims ++ b.dims)).cells m} {x : X.cells m}
    (h : (concatChainMap X Y a b).hom⟪m⟫ t = (wedgeInl X Y)⟪m⟫ x) :
    ∃ u, (wedgeInclL a.dims b.dims)⟪m⟫ u = t := by
  rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a.dims b.dims m) t with
    ⟨u, hu⟩ | ⟨v, hv⟩
  · exfalso
    have hR := concatChainMap_inclR_app X Y a b m u
    rw [hu] at hR
    exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (h.symm.trans hR)
  · exact ⟨v, hv⟩

/-- A bead cell whose concatenated image lies on the `Y`-side comes from the `b`-block. -/
theorem wedgeInclR_of_concat_inr (a : Obj X) (b : Obj Y) {m : ℕ} (hm : 1 ≤ m)
    {t : (⋁(a.dims ++ b.dims)).cells m} {y : Y.cells m}
    (h : (concatChainMap X Y a b).hom⟪m⟫ t = (wedgeInr X Y)⟪m⟫ y) :
    ∃ u, (wedgeInclR a.dims b.dims)⟪m⟫ u = t := by
  rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a.dims b.dims m) t with
    ⟨u, hu⟩ | ⟨v, hv⟩
  · exact ⟨u, hu⟩
  · exfalso
    have hL := concatChainMap_inclL_app X Y a b m v
    rw [hv] at hL
    exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (hL.symm.trans h)

/-- **Every vertex of a nonempty serial wedge lies in a block**, as a vertex of that
block's cube.  (The `m = 0` companion of `serialWedge_cell_exists`.) -/
theorem serialWedge_vertex_in_block : ∀ (dims : List ℕ+) (_hne : dims ≠ [])
    (z : (⋁dims).cells 0),
    ∃ (i : Fin dims.length) (v : (□((dims.get i) : ℕ)).cells 0),
      (ιᵂ dims i)⟪0⟫ v = z
  | [], hne, _ => absurd rfl hne
  | n :: rest, _, z => by
      rcases CubeChain.wedge2_cell_cases (□(n : ℕ)) (⋁rest) 0 z with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨0, x, by rw [CubeChain.serialWedge_ι_zero_app]; exact hx⟩
      · rcases eq_or_ne rest [] with hrest | hrest
        · subst hrest
          refine ⟨0, (□(n : ℕ)).final, ?_⟩
          rw [CubeChain.serialWedge_ι_zero_app, ← hy,
            CubeChain.wedge2_glue (□(n : ℕ)) (⋁[])]
          exact congrArg _ (Subsingleton.elim (α := (□0).cells 0) _ _)
        · obtain ⟨j, v, hjv⟩ := serialWedge_vertex_in_block rest hrest y
          exact ⟨j.succ, v, by rw [CubeChain.serialWedge_ι_succ_app, hjv]; exact hy⟩

/-- **The base case of `himg_reduce`.**  When the source wedge is the point, its single vertex is
covered as soon as one vertex is, since all `0`-cells of `⋁[]` agree. -/
theorem himg_of_nil {d e w : List ℕ+} (incl : (⋁e).toPsh ⟶ (⋁w).toPsh)
    (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh) (hd : d = []) (v : (⋁e).cells 0) (u : (⋁d).cells 0)
    (h : incl⟪0⟫ v = ρ⟪0⟫ u) : ∀ (z : (⋁d).cells 0), ∃ r, incl⟪0⟫ r = ρ⟪0⟫ z := by
  have hsub : Subsingleton ((⋁d).cells 0) := by
    rw [hd]; exact inferInstanceAs (Subsingleton ((□0).cells 0))
  exact fun z => ⟨v, by rw [hsub.elim z u]; exact h⟩

/-- **Promote an image-covering fact from positive cells to all cells.**  If a map
`μ : □^∨(dd) ⟶ Z` sends every positive cell into the image of a natural `incl : S ⟶ Z`,
and (when `dd = []`) also the single vertex, then all of `μ`'s values are `incl`-images. -/
theorem himg_reduce {S Z : PrecubicalSet} (dd : List ℕ+)
    (μ : (⋁dd).toPsh ⟶ Z) (incl : S ⟶ Z)
    (hpos : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (⋁dd).cells m),
        ∃ w, incl⟪m⟫ w = μ⟪m⟫ z)
    (hbase : dd = [] → ∀ (z : (⋁dd).cells 0),
        ∃ w, incl⟪0⟫ w = μ⟪0⟫ z) :
    ∀ (m : ℕ) (z : (⋁dd).cells m),
      ∃ w, incl⟪m⟫ w = μ⟪m⟫ z := by
  intro m z
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases eq_or_ne dd [] with hdd | hdd
    · exact hbase hdd z
    · obtain ⟨i, v, hv⟩ := serialWedge_vertex_in_block dd hdd z
      have hd1 : 1 ≤ (dd.get i : ℕ) := (dd.get i).2
      let g : ▫0 ⟶ ▫(dd.get i : ℕ) := v
      obtain ⟨w', hw'⟩ := hpos (dd.get i : ℕ) hd1
        ((ιᵂ dd i)⟪(dd.get i : ℕ)⟫ (𝟙 ▫(dd.get i : ℕ)))
      have hcubemap : (□(dd.get i : ℕ)).toPsh.map g.op (𝟙 ▫(dd.get i : ℕ)) = v :=
        Category.comp_id v
      have hzred : (⋁dd).toPsh.map g.op
          ((ιᵂ dd i)⟪(dd.get i : ℕ)⟫
            (𝟙 ▫(dd.get i : ℕ))) = z := by
        rw [← NatTrans.naturality_apply (ιᵂ dd i) g.op (𝟙 ▫(dd.get i : ℕ)),
          hcubemap]
        exact hv
      refine ⟨S.map g.op w', ?_⟩
      rw [← hzred, NatTrans.naturality_apply incl g.op w', hw']
      exact (NatTrans.naturality_apply μ g.op
        ((ιᵂ dd i)⟪(dd.get i : ℕ)⟫
          (𝟙 ▫(dd.get i : ℕ)))).symm
  · exact hpos m hm z
end ChainCat
