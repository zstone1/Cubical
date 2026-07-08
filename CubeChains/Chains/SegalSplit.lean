import CubeChains.Chains.Segal
import CubeChains.Chains.SegalAltitude
import CubeChains.Foundations.Altitude

/-!
# Chains/SegalSplit

The combinatorial heart of the Segal splitting: a cube chain in `X ∨ Y` splits as an
`X`-prefix followed by a `Y`-suffix (`chain_split`), and the `wedgeToCubes` of a
concatenation is the corresponding append (`wedgeToCubes_concatChainMap`).  These
sorry-free helpers feed `Conjectures.chConcat_essSurj`/`chConcat_full`.

**Layer:** Chains.  **Imports:** `Segal`, `SegalAltitude`, `Foundations.Altitude`.
The split uses only that the junction vertex `v` is hit at most once along a chain
(strict altitude increase across each cube), not any global altitude separation.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace ChainCat

open CubeChain

variable (X Y : BPSet)

/-- Push an `X`-cube into `X ∨ Y` along the left inclusion. -/
noncomputable def inlPush (c : Σ n : ℕ+, X.toPsh.cells (n : ℕ)) :
    Σ n : ℕ+, (BPSet.wedge2 X Y).toPsh.cells (n : ℕ) :=
  ⟨c.1, (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob (c.1 : ℕ))) c.2⟩

/-- Push a `Y`-cube into `X ∨ Y` along the right inclusion. -/
noncomputable def inrPush (c : Σ n : ℕ+, Y.toPsh.cells (n : ℕ)) :
    Σ n : ℕ+, (BPSet.wedge2 X Y).toPsh.cells (n : ℕ) :=
  ⟨c.1, (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob (c.1 : ℕ))) c.2⟩

/-- A vertex map `□⁰ ⟶ X` at the point evaluates to `X.final`. -/
theorem finalVertex_app (v : (BPSet.cube 0).toPsh.cells 0) :
    X.finalVertex.app (op (Box.ob 0)) v = X.final := by
  rw [BPSet.finalVertex, BPSet.vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply,
    show v = 𝟙 (Box.ob 0) from Subsingleton.elim _ _, op_id, X.toPsh.map_id]
  rfl

/-- A vertex map `□⁰ ⟶ Y` at the point evaluates to `Y.init`. -/
theorem initVertex_app (v : (BPSet.cube 0).toPsh.cells 0) :
    Y.initVertex.app (op (Box.ob 0)) v = Y.init := by
  rw [BPSet.initVertex, BPSet.vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply,
    show v = 𝟙 (Box.ob 0) from Subsingleton.elim _ _, op_id, Y.toPsh.map_id]
  rfl

/-- **The wedge intersection lemma.**  An `inl`-vertex equals an `inr`-vertex only at
the junction `v = inl X.final = inr Y.init`. -/
theorem wedge2_inl_eq_inr {u : X.toPsh.cells 0} {w : Y.toPsh.cells 0}
    (h : (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) u
       = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) w) :
    u = X.final ∧ w = Y.init := by
  obtain ⟨p, hp1, hp2⟩ :=
    Types.exists_of_isPullback (CubeChain.wedge2_isPullback_app X Y 0) u w h
  exact ⟨(hp1).symm.trans (finalVertex_app X p), (hp2).symm.trans (initVertex_app Y p)⟩

/-! ### The R-phase: a chain strictly above the junction is entirely on the `Y`-side. -/

/-- **R-phase.**  A cube chain whose start is an `inr`-vertex with altitude strictly
above the junction's (`C`) consists entirely of `inr`-cubes; corestrict to a chain in
`Y`. -/
theorem allR (alt : ∀ n, (BPSet.wedge2 X Y).toPsh.cells n → ℤ)
    (hax : (BPSet.wedge2 X Y).toPsh.IsAltitude alt) (C : ℤ)
    (hC : C = alt 0 ((pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) X.final)) :
    ∀ (cs : List (Σ n : ℕ+, (BPSet.wedge2 X Y).toPsh.cells (n : ℕ)))
      (s t : (BPSet.wedge2 X Y).toPsh.cells 0) (sy ty : Y.toPsh.cells 0),
      s = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) sy →
      t = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) ty →
      alt 0 s > C → IsCubeChain s cs t →
      ∃ yc : List (Σ n : ℕ+, Y.toPsh.cells (n : ℕ)),
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
      have hv0 : (BPSet.wedge2 X Y).toPsh.vertex₀ c
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) (X.toPsh.vertex₀ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₀ (pushout.inl X.finalVertex Y.initVertex) x).symm
      have hs2 : s = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0))
          (X.toPsh.vertex₀ x) := hsrc.symm.trans hv0
      have heq : (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) (X.toPsh.vertex₀ x)
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) sy :=
        hs2.symm.trans hs
      obtain ⟨hxfin, _⟩ := wedge2_inl_eq_inr X Y heq
      have haltC : alt 0 s = C := by rw [hs2, hxfin]; exact hC.symm
      rw [haltC] at halt
      exact absurd halt (lt_irrefl C)
    · -- `c = inr y`: corestrict and recurse (altitude stays strictly above `C`).
      have hv0 : (BPSet.wedge2 X Y).toPsh.vertex₀ c
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) (Y.toPsh.vertex₀ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₀ (pushout.inr X.finalVertex Y.initVertex) y).symm
      have hsy : Y.toPsh.vertex₀ y = sy :=
        CubeChain.wedge2_inr_app_injective X Y (hv0.symm.trans (hsrc.trans hs))
      have hs' : (BPSet.wedge2 X Y).toPsh.vertex₁ c
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) (Y.toPsh.vertex₁ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₁ (pushout.inr X.finalVertex Y.initVertex) y).symm
      have halt' : alt 0 ((BPSet.wedge2 X Y).toPsh.vertex₁ c) > C := by
        have e1 := PrecubicalSet.alt_vertex₁ alt hax c
        have e2 : alt (n : ℕ) c = alt 0 s := by
          rw [← PrecubicalSet.alt_vertex₀ alt hax c, hsrc]
        have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.2
        rw [e1, e2]; omega
      obtain ⟨yc', hchain', hmap'⟩ :=
        ih ((BPSet.wedge2 X Y).toPsh.vertex₁ c) t (Y.toPsh.vertex₁ y) ty hs' ht halt' htail
      refine ⟨⟨n, y⟩ :: yc', ⟨hsy, hchain'⟩, ?_⟩
      simp only [List.map_cons]
      rw [hmap', ← hy]
      rfl

/-! ### The L-phase: peel `inl`-cubes until the single junction crossing. -/

/-- **The chain split (with left start).**  A chain from an `inl`-vertex `inl sx` to the
final vertex splits into an `X`-chain prefix (from `sx`) and a `Y`-chain suffix. -/
theorem splitL (alt : ∀ n, (BPSet.wedge2 X Y).toPsh.cells n → ℤ)
    (hax : (BPSet.wedge2 X Y).toPsh.IsAltitude alt) (C : ℤ)
    (hC : C = alt 0 ((pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) X.final)) :
    ∀ (cs : List (Σ n : ℕ+, (BPSet.wedge2 X Y).toPsh.cells (n : ℕ)))
      (sx : X.toPsh.cells 0) (s : (BPSet.wedge2 X Y).toPsh.cells 0),
      s = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) sx →
      IsCubeChain s cs (BPSet.wedge2 X Y).final →
      ∃ (xc : List (Σ n : ℕ+, X.toPsh.cells (n : ℕ)))
        (yc : List (Σ n : ℕ+, Y.toPsh.cells (n : ℕ))),
        IsCubeChain sx xc X.final ∧ IsCubeChain Y.init yc Y.final
          ∧ cs = xc.map (inlPush X Y) ++ yc.map (inrPush X Y) := by
  intro cs
  induction cs with
  | nil =>
    intro sx s hs hch
    have hch' : s = (BPSet.wedge2 X Y).final := hch
    have hii : (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) sx
        = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) Y.final :=
      hs.symm.trans hch'
    obtain ⟨hsx, hyf⟩ := wedge2_inl_eq_inr X Y hii
    exact ⟨[], [], hsx, hyf.symm, rfl⟩
  | cons hd rest ih =>
    intro sx s hs hch
    obtain ⟨n, c⟩ := hd
    obtain ⟨hsrc, htail⟩ := hch
    rcases CubeChain.wedge2_cell_cases X Y (n : ℕ) c with ⟨x, hx⟩ | ⟨y, hy⟩
    · -- `c = inl x`: still in the L-phase, recurse.
      have hv0 : (BPSet.wedge2 X Y).toPsh.vertex₀ c
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) (X.toPsh.vertex₀ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₀ (pushout.inl X.finalVertex Y.initVertex) x).symm
      have hsx : X.toPsh.vertex₀ x = sx :=
        CubeChain.wedge2_inl_app_injective X Y (hv0.symm.trans (hsrc.trans hs))
      have hs' : (BPSet.wedge2 X Y).toPsh.vertex₁ c
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) (X.toPsh.vertex₁ x) := by
        rw [← hx]
        exact (PrecubicalSet.map_vertex₁ (pushout.inl X.finalVertex Y.initVertex) x).symm
      obtain ⟨xc', yc', hchx, hchy, hmap⟩ :=
        ih (X.toPsh.vertex₁ x) ((BPSet.wedge2 X Y).toPsh.vertex₁ c) hs' htail
      refine ⟨⟨n, x⟩ :: xc', yc', ⟨hsx, hchx⟩, hchy, ?_⟩
      simp only [List.map_cons, List.cons_append]
      rw [hmap, ← hx]
      rfl
    · -- `c = inr y`: the single junction crossing; the rest is R-phase.
      have hv0 : (BPSet.wedge2 X Y).toPsh.vertex₀ c
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) (Y.toPsh.vertex₀ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₀ (pushout.inr X.finalVertex Y.initVertex) y).symm
      have heq : (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) sx
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) (Y.toPsh.vertex₀ y) :=
        hs.symm.trans (hsrc.symm.trans hv0)
      obtain ⟨hsxfin, hy0⟩ := wedge2_inl_eq_inr X Y heq
      have hsC : alt 0 s = C := by rw [hs, hsxfin]; exact hC.symm
      have hs' : (BPSet.wedge2 X Y).toPsh.vertex₁ c
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) (Y.toPsh.vertex₁ y) := by
        rw [← hy]
        exact (PrecubicalSet.map_vertex₁ (pushout.inr X.finalVertex Y.initVertex) y).symm
      have halt' : alt 0 ((BPSet.wedge2 X Y).toPsh.vertex₁ c) > C := by
        have e1 := PrecubicalSet.alt_vertex₁ alt hax c
        have e2 : alt (n : ℕ) c = alt 0 s := by
          rw [← PrecubicalSet.alt_vertex₀ alt hax c, hsrc]
        have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.2
        rw [e1, e2, hsC]; omega
      obtain ⟨yc', hchy, hmap⟩ :=
        allR X Y alt hax C hC rest ((BPSet.wedge2 X Y).toPsh.vertex₁ c)
          (BPSet.wedge2 X Y).final (Y.toPsh.vertex₁ y) Y.final hs' rfl halt' htail
      refine ⟨[], ⟨n, y⟩ :: yc', ?_, ⟨hy0, hchy⟩, ?_⟩
      · -- `IsCubeChain sx [] X.final`, i.e. `sx = X.final`.
        exact hsxfin
      · simp only [List.map_nil, List.nil_append, List.map_cons]
        rw [hmap, ← hy]
        rfl

/-- **The chain split.**  A full cube chain in `X ∨ Y` splits into an `X`-chain and a
`Y`-chain glued at the junction, on the nose at the level of cube lists. -/
theorem chain_split (h : (BPSet.wedge2 X Y).AdmitsAltitude)
    (cs : List (Σ n : ℕ+, (BPSet.wedge2 X Y).toPsh.cells (n : ℕ)))
    (hch : IsCubeChain (BPSet.wedge2 X Y).init cs (BPSet.wedge2 X Y).final) :
    ∃ (xc : List (Σ n : ℕ+, X.toPsh.cells (n : ℕ)))
      (yc : List (Σ n : ℕ+, Y.toPsh.cells (n : ℕ))),
      IsCubeChain X.init xc X.final ∧ IsCubeChain Y.init yc Y.final
        ∧ cs = xc.map (inlPush X Y) ++ yc.map (inrPush X Y) := by
  obtain ⟨alt, hax, _⟩ := h
  exact splitL X Y alt hax _ rfl cs X.init (BPSet.wedge2 X Y).init rfl hch

/-! ### `wedgeToCubes` naturality and appending -/

/-- **Reading cubes commutes with post-composition** (naturality of `wedgeToCubes`). -/
theorem wedgeToCubes_comp {K L : BPSet} (g : K.toPsh ⟶ L.toPsh) :
    ∀ (dims : List ℕ+) (φ : (BPSet.serialWedge dims).toPsh ⟶ K.toPsh),
      CubeChain.wedgeToCubes ⟨dims, φ ≫ g⟩
        = (CubeChain.wedgeToCubes ⟨dims, φ⟩).map
            (fun c => ⟨c.1, g.app (op (Box.ob (c.1 : ℕ))) c.2⟩)
  | [], _ => by simp [CubeChain.wedgeToCubes]
  | x :: rest, φ => by
      simp only [CubeChain.wedgeToCubes, List.map_cons]
      refine congr_arg₂ List.cons ?_ ?_
      · have hval : yonedaEquiv (pushout.inl _ _ ≫ φ ≫ g)
            = g.app (op (Box.ob (x : ℕ))) (yonedaEquiv (pushout.inl _ _ ≫ φ)) :=
          (congrArg yonedaEquiv (Category.assoc _ φ g).symm).trans
            (yonedaEquiv_comp (pushout.inl _ _ ≫ φ) g)
        exact congrArg (fun z => (⟨x, z⟩ : Σ m : ℕ+, L.toPsh.cells (m : ℕ))) hval
      · exact (congrArg (fun m => CubeChain.wedgeToCubes ⟨rest, m⟩)
            (Category.assoc (pushout.inr _ _) φ g)).symm.trans
          (wedgeToCubes_comp g rest (pushout.inr _ _ ≫ φ))

/-- **`wedgeToCubes` of an appended serial wedge splits** as the append of the two
half-restrictions along `wedgeInclL`/`wedgeInclR`. -/
theorem wedgeToCubes_append {K : BPSet} :
    ∀ (da db : List ℕ+) (φ : (BPSet.serialWedge (da ++ db)).toPsh ⟶ K.toPsh),
      CubeChain.wedgeToCubes ⟨da ++ db, φ⟩
        = CubeChain.wedgeToCubes ⟨da, wedgeInclL da db ≫ φ⟩
          ++ CubeChain.wedgeToCubes ⟨db, wedgeInclR da db ≫ φ⟩
  | [], db, φ => by
      change CubeChain.wedgeToCubes ⟨db, φ⟩
          = CubeChain.wedgeToCubes ⟨([] : List ℕ+), wedgeInclL [] db ≫ φ⟩
            ++ CubeChain.wedgeToCubes ⟨db, wedgeInclR [] db ≫ φ⟩
      rw [show wedgeInclR ([] : List ℕ+) db = 𝟙 (BPSet.serialWedge db).toPsh from rfl]
      simp only [CubeChain.wedgeToCubes, List.nil_append, Category.id_comp]
  | n :: da', db, φ => by
      simp only [CubeChain.wedgeToCubes, List.cons_append]
      set cinl := pushout.inl (BPSet.cube (n : ℕ)).finalVertex
        (BPSet.serialWedge (da' ++ db)).initVertex with hcinl
      set cinr := pushout.inr (BPSet.cube (n : ℕ)).finalVertex
        (BPSet.serialWedge (da' ++ db)).initVertex with hcinr
      set dinl := pushout.inl (BPSet.cube (n : ℕ)).finalVertex
        (BPSet.serialWedge da').initVertex with hdinl
      set dinr := pushout.inr (BPSet.cube (n : ℕ)).finalVertex
        (BPSet.serialWedge da').initVertex with hdinr
      have hhead : dinl ≫ wedgeInclL (n :: da') db = cinl := by
        rw [hdinl, hcinl, wedgeInclL_cons]; exact pushout.inl_desc _ _ _
      have htail : dinr ≫ wedgeInclL (n :: da') db = wedgeInclL da' db ≫ cinr := by
        rw [hdinr, hcinr, wedgeInclL_cons]; exact pushout.inr_desc _ _ _
      have hRcons : wedgeInclR (n :: da') db = wedgeInclR da' db ≫ cinr := by rw [hcinr]; rfl
      have hh : dinl ≫ (wedgeInclL (n :: da') db ≫ φ) = cinl ≫ φ :=
        (Category.assoc dinl (wedgeInclL (n :: da') db) φ).symm.trans (congrArg (· ≫ φ) hhead)
      have hL : wedgeInclL da' db ≫ (cinr ≫ φ) = dinr ≫ (wedgeInclL (n :: da') db ≫ φ) :=
        ((Category.assoc (wedgeInclL da' db) cinr φ).symm.trans
          (congrArg (· ≫ φ) htail.symm)).trans (Category.assoc dinr (wedgeInclL (n :: da') db) φ)
      have hR : wedgeInclR da' db ≫ (cinr ≫ φ) = wedgeInclR (n :: da') db ≫ φ :=
        (Category.assoc (wedgeInclR da' db) cinr φ).symm.trans (congrArg (· ≫ φ) hRcons.symm)
      refine congr_arg₂ List.cons ?_ ?_
      · exact congrArg
          (fun z => (⟨n, yonedaEquiv z⟩ : Σ m : ℕ+, K.toPsh.cells (m : ℕ))) hh.symm
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
    exact wedgeToCubes_comp (L := BPSet.wedge2 X Y) (pushout.inl X.finalVertex Y.initVertex)
      a.dims a.map.hom
  have hR : CubeChain.wedgeToCubes ⟨b.dims, wedgeInclR a.dims b.dims ≫ (concatChainMap X Y a b).hom⟩
      = (CubeChain.wedgeToCubes ⟨b.dims, b.map.hom⟩).map (inrPush X Y) := by
    rw [concatChainMap_inclR X Y a b]
    exact wedgeToCubes_comp (L := BPSet.wedge2 X Y) (pushout.inr X.finalVertex Y.initVertex)
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
  rw [BPSet.hom_ext hmaps]

/-! ### Factorization infrastructure for `chConcat_full`

Generic machinery for splitting a refinement of concatenated chains into `X`- and `Y`-halves:
`factorThruMono` (factor a presheaf map through a pointwise-injective one), the append pushout
square `append_isPushout` (giving the cell-cases dichotomy and junction-disjointness
`append_inter`), and `himg_reduce` (promote an image-covering fact from positive cells to all
cells). -/

/-- Factor `ρ : A ⟶ W` through a pointwise-injective `m : L ⟶ W` when every value of
`ρ` lands in the image of `m` (the unique such factorization, chosen pointwise). -/
noncomputable def factorThruMono {A L W : PrecubicalSet} (ρ : A ⟶ W) (m : L ⟶ W)
    (himg : ∀ (k : Boxᵒᵖ) (z : A.obj k), ∃ w, m.app k w = ρ.app k z)
    (hm : ∀ (k : Boxᵒᵖ), Function.Injective (m.app k)) : A ⟶ L where
  app k := TypeCat.ofHom (fun z => Classical.choose (himg k z))
  naturality k k' f := by
    refine ConcreteCategory.hom_ext _ _ (fun z => ?_)
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    apply hm k'
    rw [Classical.choose_spec (himg k' (A.map f z)),
      NatTrans.naturality_apply m f (Classical.choose (himg k z)),
      Classical.choose_spec (himg k z)]
    exact NatTrans.naturality_apply ρ f z

@[simp] theorem factorThruMono_app_apply {A L W : PrecubicalSet} (ρ : A ⟶ W) (m : L ⟶ W)
    (himg : ∀ (k : Boxᵒᵖ) (z : A.obj k), ∃ w, m.app k w = ρ.app k z)
    (hm : ∀ (k : Boxᵒᵖ), Function.Injective (m.app k)) (k : Boxᵒᵖ) (z : A.obj k) :
    (factorThruMono ρ m himg hm).app k z = Classical.choose (himg k z) :=
  TypeCat.ofHom_apply _ z

theorem factorThruMono_comp {A L W : PrecubicalSet} (ρ : A ⟶ W) (m : L ⟶ W)
    (himg : ∀ (k : Boxᵒᵖ) (z : A.obj k), ∃ w, m.app k w = ρ.app k z)
    (hm : ∀ (k : Boxᵒᵖ), Function.Injective (m.app k)) :
    factorThruMono ρ m himg hm ≫ m = ρ := by
  refine NatTrans.ext (funext fun k => ?_)
  refine ConcreteCategory.hom_ext _ _ (fun z => ?_)
  rw [NatTrans.comp_app, types_comp_apply, factorThruMono_app_apply]
  exact Classical.choose_spec (himg k z)

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
    IsPushout (BPSet.serialWedge db).initVertex (BPSet.serialWedge da).finalVertex
      (wedgeInclR da db) (wedgeInclL da db)
  | [], db => by
      have e1 : (BPSet.serialWedge ([] : List ℕ+)).finalVertex = 𝟙 (yoneda.obj (Box.ob 0)) :=
        cube0_finalVertex_eq_id
      have e2 : wedgeInclR ([] : List ℕ+) db = 𝟙 (BPSet.serialWedge db).toPsh := rfl
      have e3 : wedgeInclL ([] : List ℕ+) db = (BPSet.serialWedge db).initVertex := rfl
      rw [e1, e2, e3]
      exact IsPushout.of_id_snd
  | n :: da', db => by
      have key := (append_isPushout da' db).paste_vert (wedgeInclL_cons_isPushout n da' db).flip
      rw [← wedge2_finalVertex (BPSet.cube (n : ℕ)) (BPSet.serialWedge da')] at key
      exact key

/-- The append gluing square, transported to `Type` at level `m`. -/
theorem append_isPushout_app (da db : List ℕ+) (m : ℕ) :
    IsPushout ((BPSet.serialWedge db).initVertex.app (op (Box.ob m)))
      ((BPSet.serialWedge da).finalVertex.app (op (Box.ob m)))
      ((wedgeInclR da db).app (op (Box.ob m)))
      ((wedgeInclL da db).app (op (Box.ob m))) :=
  (append_isPushout da db).map (F := (evaluation Boxᵒᵖ Type).obj (op (Box.ob m)))

/-- The append gluing square is a pullback at every level. -/
theorem append_isPullback_app (da db : List ℕ+) (m : ℕ) :
    IsPullback ((BPSet.serialWedge db).initVertex.app (op (Box.ob m)))
      ((BPSet.serialWedge da).finalVertex.app (op (Box.ob m)))
      ((wedgeInclR da db).app (op (Box.ob m)))
      ((wedgeInclL da db).app (op (Box.ob m))) :=
  Types.isPullback_of_isPushout (append_isPushout_app da db m)
    (CubeChain.vertexMap_app_injective (BPSet.serialWedge db).initVertex)

/-- **Junction disjointness.**  In `□^∨(da ++ db)`, a vertex that is both a
`wedgeInclL`-image and a `wedgeInclR`-image is the junction: the `da`-vertex is the
final vertex of `□^∨(da)` and the `db`-vertex is the init vertex of `□^∨(db)`. -/
theorem append_inter (da db : List ℕ+) (wL : (BPSet.serialWedge da).toPsh.cells 0)
    (wR : (BPSet.serialWedge db).toPsh.cells 0)
    (h : (wedgeInclL da db).app (op (Box.ob 0)) wL
       = (wedgeInclR da db).app (op (Box.ob 0)) wR) :
    wL = (BPSet.serialWedge da).final ∧ wR = (BPSet.serialWedge db).init := by
  obtain ⟨p, hp1, hp2⟩ := Types.exists_of_isPullback (append_isPullback_app da db 0) wR wL h.symm
  exact ⟨hp2.symm.trans (finalVertex_app (BPSet.serialWedge da) p),
    hp1.symm.trans (initVertex_app (BPSet.serialWedge db) p)⟩

/-- **Every vertex of a nonempty serial wedge lies in a block**, as a vertex of that
block's cube.  (The `m = 0` companion of `serialWedge_cell_exists`.) -/
theorem serialWedge_vertex_in_block : ∀ (dims : List ℕ+) (_hne : dims ≠ [])
    (z : (BPSet.serialWedge dims).toPsh.cells 0),
    ∃ (i : Fin dims.length) (v : (BPSet.cube ((dims.get i) : ℕ)).toPsh.cells 0),
      (BPSet.serialWedge.ι dims i).app (op (Box.ob 0)) v = z
  | [], hne, _ => absurd rfl hne
  | n :: rest, _, z => by
      rcases CubeChain.wedge2_cell_cases (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) 0 z with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨0, x, by rw [CubeChain.serialWedge_ι_zero_app]; exact hx⟩
      · rcases eq_or_ne rest [] with hrest | hrest
        · subst hrest
          refine ⟨0, (BPSet.cube (n : ℕ)).final, ?_⟩
          rw [CubeChain.serialWedge_ι_zero_app, ← hy,
            CubeChain.wedge2_glue (BPSet.cube (n : ℕ)) (BPSet.serialWedge [])]
          exact congrArg _ (Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _)
        · obtain ⟨j, v, hjv⟩ := serialWedge_vertex_in_block rest hrest y
          exact ⟨j.succ, v, by rw [CubeChain.serialWedge_ι_succ_app, hjv]; exact hy⟩

/-- **Promote an image-covering fact from positive cells to all cells.**  If a map
`μ : □^∨(dd) ⟶ Z` sends every positive cell into the image of a natural `incl : S ⟶ Z`,
and (when `dd = []`) also the single vertex, then all of `μ`'s values are `incl`-images. -/
theorem himg_reduce {S Z : PrecubicalSet} (dd : List ℕ+)
    (μ : (BPSet.serialWedge dd).toPsh ⟶ Z) (incl : S ⟶ Z)
    (hpos : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (BPSet.serialWedge dd).toPsh.cells m),
        ∃ w, incl.app (op (Box.ob m)) w = μ.app (op (Box.ob m)) z)
    (hbase : dd = [] → ∀ (z : (BPSet.serialWedge dd).toPsh.cells 0),
        ∃ w, incl.app (op (Box.ob 0)) w = μ.app (op (Box.ob 0)) z) :
    ∀ (m : ℕ) (z : (BPSet.serialWedge dd).toPsh.cells m),
      ∃ w, incl.app (op (Box.ob m)) w = μ.app (op (Box.ob m)) z := by
  intro m z
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases eq_or_ne dd [] with hdd | hdd
    · exact hbase hdd z
    · obtain ⟨i, v, hv⟩ := serialWedge_vertex_in_block dd hdd z
      have hd1 : 1 ≤ (dd.get i : ℕ) := (dd.get i).2
      let g : Box.ob 0 ⟶ Box.ob (dd.get i : ℕ) := v
      obtain ⟨w', hw'⟩ := hpos (dd.get i : ℕ) hd1
        ((BPSet.serialWedge.ι dd i).app (op (Box.ob (dd.get i : ℕ))) (𝟙 (Box.ob (dd.get i : ℕ))))
      have hcubemap : (BPSet.cube (dd.get i : ℕ)).toPsh.map g.op (𝟙 (Box.ob (dd.get i : ℕ))) = v :=
        Category.comp_id v
      have hzred : (BPSet.serialWedge dd).toPsh.map g.op
          ((BPSet.serialWedge.ι dd i).app (op (Box.ob (dd.get i : ℕ)))
            (𝟙 (Box.ob (dd.get i : ℕ)))) = z := by
        rw [← NatTrans.naturality_apply (BPSet.serialWedge.ι dd i) g.op (𝟙 (Box.ob (dd.get i : ℕ))),
          hcubemap]
        exact hv
      refine ⟨S.map g.op w', ?_⟩
      rw [← hzred, NatTrans.naturality_apply incl g.op w', hw']
      exact (NatTrans.naturality_apply μ g.op
        ((BPSet.serialWedge.ι dd i).app (op (Box.ob (dd.get i : ℕ)))
          (𝟙 (Box.ob (dd.get i : ℕ))))).symm
  · exact hpos m hm z

/-! ### Fullness of `chConcat` on morphisms

A refinement of concatenated chains splits into `X`- and `Y`-halves via `factorThruMono`,
`himg_reduce` and `append_inter`, giving the morphism whose concatenation is the given
refinement. -/

/-- **`chConcat` is full on morphisms** (unconditional): every refinement of two
concatenated chains is the concatenation of a refinement of the `X`-halves and one of
the `Y`-halves. -/
theorem chConcat_map_surjective {ab ab' : Obj X × Obj Y}
    (hh : (chConcat X Y).obj ab ⟶ (chConcat X Y).obj ab') :
    ∃ fg, (chConcat X Y).map fg = hh := by
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := ab'
  let hh2 : (⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ : Obj (BPSet.wedge2 X Y))
      ⟶ ⟨a'.dims ++ b'.dims, concatChainMap X Y a' b'⟩ := hh
  set ρL := wedgeInclL a.dims b.dims ≫ hh2.φ.hom with hρL
  set ρR := wedgeInclR a.dims b.dims ≫ hh2.φ.hom with hρR
  have hwhom : hh2.φ.hom ≫ (concatChainMap X Y a' b').hom = (concatChainMap X Y a b).hom := by
    have hw := congrArg BPSet.Hom.hom hh2.w
    simpa only [BPSet.comp_hom] using hw
  have hcompL : ρL ≫ (concatChainMap X Y a' b').hom
      = a.map.hom ≫ pushout.inl X.finalVertex Y.initVertex := by
    rw [hρL]
    simp only [Category.assoc, hwhom]
    exact concatChainMap_inclL X Y a b
  have hcompR : ρR ≫ (concatChainMap X Y a' b').hom
      = b.map.hom ≫ pushout.inr X.finalVertex Y.initVertex := by
    rw [hρR]
    simp only [Category.assoc, hwhom]
    exact concatChainMap_inclR X Y a b
  have hposL : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (BPSet.serialWedge a.dims).toPsh.cells m),
      ∃ w, (wedgeInclL a'.dims b'.dims).app (op (Box.ob m)) w = ρL.app (op (Box.ob m)) z := by
    intro m hm z
    rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a'.dims b'.dims m)
        (ρL.app (op (Box.ob m)) z) with ⟨u, hu⟩ | ⟨w, hw⟩
    · exfalso
      have hL : (concatChainMap X Y a' b').hom.app (op (Box.ob m)) (ρL.app (op (Box.ob m)) z)
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m))
            (a.map.hom.app (op (Box.ob m)) z) := by
        have hc := congrArg (fun t : (BPSet.serialWedge a.dims).toPsh ⟶ (BPSet.wedge2 X Y).toPsh =>
          t.app (op (Box.ob m)) z) hcompL
        simpa only [NatTrans.comp_app, types_comp_apply] using hc
      have hR : (concatChainMap X Y a' b').hom.app (op (Box.ob m))
            ((wedgeInclR a'.dims b'.dims).app (op (Box.ob m)) u)
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))
            (b'.map.hom.app (op (Box.ob m)) u) := by
        have hc := congrArg (fun t : (BPSet.serialWedge b'.dims).toPsh ⟶ (BPSet.wedge2 X Y).toPsh =>
          t.app (op (Box.ob m)) u) (concatChainMap_inclR X Y a' b')
        simp only [NatTrans.comp_app, types_comp_apply] at hc
        rw [hc]
        change (b'.map.hom ≫ pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m)) u
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))
            (b'.map.hom.app (op (Box.ob m)) u)
        simp only [NatTrans.comp_app, types_comp_apply]
      exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (hL.symm.trans (hu ▸ hR))
    · exact ⟨w, hw⟩
  have hposR : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (BPSet.serialWedge b.dims).toPsh.cells m),
      ∃ w, (wedgeInclR a'.dims b'.dims).app (op (Box.ob m)) w = ρR.app (op (Box.ob m)) z := by
    intro m hm z
    rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a'.dims b'.dims m)
        (ρR.app (op (Box.ob m)) z) with ⟨u, hu⟩ | ⟨w, hw⟩
    · exact ⟨u, hu⟩
    · exfalso
      have hR : (concatChainMap X Y a' b').hom.app (op (Box.ob m)) (ρR.app (op (Box.ob m)) z)
          = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m))
            (b.map.hom.app (op (Box.ob m)) z) := by
        have hc := congrArg (fun t : (BPSet.serialWedge b.dims).toPsh ⟶ (BPSet.wedge2 X Y).toPsh =>
          t.app (op (Box.ob m)) z) hcompR
        simpa only [NatTrans.comp_app, types_comp_apply] using hc
      have hL : (concatChainMap X Y a' b').hom.app (op (Box.ob m))
            ((wedgeInclL a'.dims b'.dims).app (op (Box.ob m)) w)
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m))
            (a'.map.hom.app (op (Box.ob m)) w) := by
        have hc := congrArg (fun t : (BPSet.serialWedge a'.dims).toPsh ⟶ (BPSet.wedge2 X Y).toPsh =>
          t.app (op (Box.ob m)) w) (concatChainMap_inclL X Y a' b')
        simp only [NatTrans.comp_app, types_comp_apply] at hc
        rw [hc]
        change (a'.map.hom ≫ pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)) w
          = (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m))
            (a'.map.hom.app (op (Box.ob m)) w)
        simp only [NatTrans.comp_app, types_comp_apply]
      exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (hL.symm.trans (hw ▸ hR))
  have hρLinit : ρL.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).init
      = (BPSet.serialWedge (a'.dims ++ b'.dims)).init := by
    rw [hρL, NatTrans.comp_app, types_comp_apply,
      app_init_eq_of_initVertex (wedgeInclL a.dims b.dims) (wedgeInclL_initVertex a.dims b.dims)]
    exact hh2.φ.app_init
  have hρRfinal : ρR.app (op (Box.ob 0)) (BPSet.serialWedge b.dims).final
      = (BPSet.serialWedge (a'.dims ++ b'.dims)).final := by
    rw [hρR, NatTrans.comp_app, types_comp_apply,
      app_final_eq_of_finalVertex (wedgeInclR a.dims b.dims) (wedgeInclR_finalVertex a.dims b.dims)]
    exact hh2.φ.app_final
  have hbaseL : a.dims = [] → ∀ (z : (BPSet.serialWedge a.dims).toPsh.cells 0),
      ∃ w, (wedgeInclL a'.dims b'.dims).app (op (Box.ob 0)) w = ρL.app (op (Box.ob 0)) z := by
    intro hda z
    refine ⟨(BPSet.serialWedge a'.dims).init, ?_⟩
    rw [app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)]
    have hsub : Subsingleton ((BPSet.serialWedge a.dims).toPsh.cells 0) := by
      rw [hda]; exact inferInstanceAs (Subsingleton ((BPSet.cube 0).toPsh.cells 0))
    rw [hsub.elim z (BPSet.serialWedge a.dims).init]
    exact hρLinit.symm
  have hbaseR : b.dims = [] → ∀ (z : (BPSet.serialWedge b.dims).toPsh.cells 0),
      ∃ w, (wedgeInclR a'.dims b'.dims).app (op (Box.ob 0)) w = ρR.app (op (Box.ob 0)) z := by
    intro hdb z
    refine ⟨(BPSet.serialWedge b'.dims).final, ?_⟩
    rw [app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)]
    have hsub : Subsingleton ((BPSet.serialWedge b.dims).toPsh.cells 0) := by
      rw [hdb]; exact inferInstanceAs (Subsingleton ((BPSet.cube 0).toPsh.cells 0))
    rw [hsub.elim z (BPSet.serialWedge b.dims).final]
    exact hρRfinal.symm
  have himgL := himg_reduce a.dims ρL (wedgeInclL a'.dims b'.dims) hposL hbaseL
  have himgR := himg_reduce b.dims ρR (wedgeInclR a'.dims b'.dims) hposR hbaseR
  set fhom := factorThruMono ρL (wedgeInclL a'.dims b'.dims)
    (fun k z => himgL k.unop.dim z) (wedgeInclL_app_injective a'.dims b'.dims) with hfhom
  set ghom := factorThruMono ρR (wedgeInclR a'.dims b'.dims)
    (fun k z => himgR k.unop.dim z) (wedgeInclR_app_injective a'.dims b'.dims) with hghom
  have hfhom_comp : fhom ≫ wedgeInclL a'.dims b'.dims = ρL :=
    factorThruMono_comp ρL (wedgeInclL a'.dims b'.dims)
      (fun k z => himgL k.unop.dim z) (wedgeInclL_app_injective a'.dims b'.dims)
  have hghom_comp : ghom ≫ wedgeInclR a'.dims b'.dims = ρR :=
    factorThruMono_comp ρR (wedgeInclR a'.dims b'.dims)
      (fun k z => himgR k.unop.dim z) (wedgeInclR_app_injective a'.dims b'.dims)
  have hfval : ∀ (c : (BPSet.serialWedge a.dims).toPsh.cells 0),
      (wedgeInclL a'.dims b'.dims).app (op (Box.ob 0)) (fhom.app (op (Box.ob 0)) c)
        = ρL.app (op (Box.ob 0)) c := by
    intro c
    have hc := congrArg (fun t => t.app (op (Box.ob 0)) c) hfhom_comp
    simpa only [NatTrans.comp_app, types_comp_apply] using hc
  have hgval : ∀ (c : (BPSet.serialWedge b.dims).toPsh.cells 0),
      (wedgeInclR a'.dims b'.dims).app (op (Box.ob 0)) (ghom.app (op (Box.ob 0)) c)
        = ρR.app (op (Box.ob 0)) c := by
    intro c
    have hc := congrArg (fun t => t.app (op (Box.ob 0)) c) hghom_comp
    simpa only [NatTrans.comp_app, types_comp_apply] using hc
  have hp : (wedgeInclL a'.dims b'.dims).app (op (Box.ob 0))
        (fhom.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).final)
      = (wedgeInclR a'.dims b'.dims).app (op (Box.ob 0))
        (ghom.app (op (Box.ob 0)) (BPSet.serialWedge b.dims).init) := by
    rw [hfval, hgval, hρL, hρR]
    simp only [NatTrans.comp_app, types_comp_apply]
    rw [wedgeInclL_final_eq_wedgeInclR_init a.dims b.dims]
  obtain ⟨hfin, hginit⟩ := append_inter a'.dims b'.dims _ _ hp
  have hfinit : fhom.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).init
      = (BPSet.serialWedge a'.dims).init := by
    apply wedgeInclL_app_injective a'.dims b'.dims (op (Box.ob 0))
    rw [hfval, hρLinit,
      app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
        (wedgeInclL_initVertex a'.dims b'.dims)]
  have hgfinal : ghom.app (op (Box.ob 0)) (BPSet.serialWedge b.dims).final
      = (BPSet.serialWedge b'.dims).final := by
    apply wedgeInclR_app_injective a'.dims b'.dims (op (Box.ob 0))
    rw [hgval, hρRfinal,
      app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
        (wedgeInclR_finalVertex a'.dims b'.dims)]
  let fφ : BPSet.serialWedge a.dims ⟶ BPSet.serialWedge a'.dims :=
    { hom := fhom, app_init := hfinit, app_final := hfin }
  let gφ : BPSet.serialWedge b.dims ⟶ BPSet.serialWedge b'.dims :=
    { hom := ghom, app_init := hginit, app_final := hgfinal }
  have fw : fφ ≫ a'.map = a.map := by
    apply BPSet.hom_ext
    rw [BPSet.comp_hom]
    change fhom ≫ a'.map.hom = a.map.hom
    have e : ρL ≫ (concatChainMap X Y a' b').hom
        = fhom ≫ a'.map.hom ≫ pushout.inl X.finalVertex Y.initVertex := by
      rw [← hfhom_comp, Category.assoc]
      congr 1
      exact concatChainMap_inclL X Y a' b'
    apply (cancel_mono (pushout.inl X.finalVertex Y.initVertex)).mp
    rw [Category.assoc, ← e, hcompL]
  have gw : gφ ≫ b'.map = b.map := by
    apply BPSet.hom_ext
    rw [BPSet.comp_hom]
    change ghom ≫ b'.map.hom = b.map.hom
    have e : ρR ≫ (concatChainMap X Y a' b').hom
        = ghom ≫ b'.map.hom ≫ pushout.inr X.finalVertex Y.initVertex := by
      rw [← hghom_comp, Category.assoc]
      congr 1
      exact concatChainMap_inclR X Y a' b'
    apply (cancel_mono (pushout.inr X.finalVertex Y.initVertex)).mp
    rw [Category.assoc, ← e, hcompR]
  refine ⟨((⟨fφ, fw⟩ : (a : Obj X) ⟶ a'), (⟨gφ, gw⟩ : (b : Obj Y) ⟶ b')), ?_⟩
  apply hom_ext'
  change concatHomφ (⟨fφ, fw⟩ : (a : Obj X) ⟶ a') (⟨gφ, gw⟩ : (b : Obj Y) ⟶ b') = hh2.φ
  apply BPSet.hom_ext
  refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
  · rw [concatHomφ_inclL]
    change fhom ≫ wedgeInclL a'.dims b'.dims = wedgeInclL a.dims b.dims ≫ hh2.φ.hom
    rw [hfhom_comp, hρL]
  · rw [concatHomφ_inclR]
    change ghom ≫ wedgeInclR a'.dims b'.dims = wedgeInclR a.dims b.dims ≫ hh2.φ.hom
    rw [hghom_comp, hρR]

end ChainCat
