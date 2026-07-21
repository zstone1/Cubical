import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.ChainSkeletal
import CubeChains.Chains.Flips
import CubeChains.Foundations.BoxMonoidal

/-!
# Chains/Events — a chain of `□ᴺ` is an ordered partition of its events

An *event* of `⋁A` is a free coordinate of one of its beads.  A wedge map `φ : ⋁ad ⟶ ⋁cd`
carries bead `i` into bead `blockIdx φ i` along `blockFace φ i`, hence carries events to events
(`evMap`).  Over a fixed cube an event has an intrinsic name — the coordinate its bead flips
(`cubeEv`) — and that naming is a bijection, inverse to `flipIdx`.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet ChainCat CubeChains

namespace CubeChain

/-! ## Part 1 — the events of a serial wedge -/

/-- Events are pinned by their bead and the *numeral* of their coordinate.  `Sigma.ext` would
demand `HEq` of the two coordinates instead; this is what keeps `Fin`-transport out of every
downstream statement. -/
theorem beadEvent_ext {A : List ℕ+} {e f : beadEvent A} (h1 : e.1 = f.1)
    (h2 : (e.2 : ℕ) = (f.2 : ℕ)) : e = f := by
  obtain ⟨i, p⟩ := e
  obtain ⟨i', p'⟩ := f
  subst h1
  exact congrArg _ (Fin.ext h2)

theorem card_beadEvent (A : List ℕ+) : Fintype.card (beadEvent A) = dimSum A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_get_eq_sum_map A (fun d : ℕ+ => (d : ℕ))

/-! ## Part 2 — the induced map on events, and its functoriality

Consumer: bead `Cubical-p89`, the general-`K` braid functor `ConcPos`, whose permutation is
`evOrd x.run ∘ evMap f ∘ (evOrd y.run)⁻¹` — `evMap_comp` is its cocycle law and `evEquiv` is
what inverts it. -/

/-- The event map of a wedge map: bead `i` goes to bead `blockIdx φ i`, and its free
coordinates travel along `faceEmb (blockFace φ i)`. -/
def evMap {ad cd : List ℕ+} (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (e : beadEvent ad) : beadEvent cd :=
  ⟨blockIdx φ e.1, faceEmb (blockFace φ e.1) e.2⟩

@[simp] theorem evMap_fst {ad cd : List ℕ+} (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (e : beadEvent ad) :
    (evMap φ e).1 = blockIdx φ e.1 := rfl

@[simp] theorem evMap_snd {ad cd : List ℕ+} (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (e : beadEvent ad) :
    ((evMap φ e).2 : ℕ) = (faceEmb (blockFace φ e.1) e.2 : ℕ) := rfl

/-- **Uniqueness of the block face, in numeral form.**  Any factorisation of the bead
restriction computes `blockFace`, and reading the answer through `faceEmb` as a numeral keeps the
forced index equality out of the statement. -/
theorem faceEmb_blockFace_eq_of_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i : ℕ)) ⟶ ▫((cd.get r : ℕ)))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r) (x : Fin ((ad.get i : ℕ))) :
    ((faceEmb (blockFace φ i) x : ℕ)) = ((faceEmb g x : ℕ)) := by
  obtain rfl : r = blockIdx φ i := blockIdx_eq_of_factor φ i r g h
  have hg : blockFace φ i = g := by
    have := (blockFace_spec φ i).symm.trans h
    have h2 := congrArg yonedaEquiv this
    rw [yonedaEquiv_comp, yonedaEquiv_comp] at h2
    have h3 := serialWedge_ι_app_injective cd (blockIdx φ i) h2
    rw [yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at h3
    exact h3
  rw [hg]

theorem evMap_id (A : List ℕ+) (e : beadEvent A) : evMap (𝟙 (⋁A).toPsh) e = e := by
  obtain ⟨i, p⟩ := e
  have hfac : ιᵂ A i ≫ 𝟙 (⋁A).toPsh
      = yoneda.map (𝟙 ▫((A.get i : ℕ))) ≫ ιᵂ A i := by
    rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  refine beadEvent_ext ?_ ?_
  · exact (blockIdx_eq_of_factor (𝟙 (⋁A).toPsh) i i (𝟙 _) hfac).symm
  · rw [evMap_snd, faceEmb_blockFace_eq_of_factor _ i i _ hfac p, faceEmb_id]

theorem evMap_comp {ad bd cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh) (ψ : (⋁bd).toPsh ⟶ (⋁cd).toPsh) (e : beadEvent ad) :
    evMap (φ ≫ ψ) e = evMap ψ (evMap φ e) := by
  obtain ⟨i, p⟩ := e
  refine beadEvent_ext (blockIdx_comp φ ψ i) ?_
  rw [evMap_snd, faceEmb_blockFace_eq_of_factor (φ ≫ ψ) i _ _ (blockFace_spec_comp φ ψ i) p,
    faceEmb_comp]
  rfl

/-! ## Part 2 — beads over a fixed cube

A bead of a wedge map into `□N` is a face of `□N` (`beadFace`), and an event names the coordinate
its bead flips (`cubeEv`).  This is the comparison a run-order permutation has to match. -/

theorem yonedaEquiv_symm_box {X Y : Box} (f : X ⟶ Y) :
    (yonedaEquiv.symm f : yoneda.obj X ⟶ yoneda.obj Y) = yoneda.map f :=
  yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])

/-- A coordinate is free in a cube face exactly when it is in the image of `faceEmb`. -/
theorem mem_noneSet_iff_faceEmb {k m : ℕ} (g : ▫k ⟶ ▫m) (p : Fin m) :
    p ∈ noneSet (toStar (g : (□m).cells k)).val ↔ ∃ q, faceEmb g q = p := by
  constructor
  · intro hp; exact ⟨nonesIdx (toStar g) p hp, nones_nonesIdx _ _ _⟩
  · rintro ⟨q, rfl⟩; exact mem_noneSet.mpr (val_nones (toStar g) q)

theorem cubesOf_get {M : List ℕ+} {n : ℕ} (χ : (⋁M).toPsh ⟶ (□n).toPsh)
    (i : Fin (cubesOf M χ).length) :
    (cubesOf M χ).get i
      = ⟨M.get (i.cast (cubesOf_length M χ)),
          yonedaEquiv (ιᵂ M (i.cast (cubesOf_length M χ)) ≫ χ)⟩ :=
  wedgeToCubes_get M χ i

/-- **Bead `i` of a composite into a cube** factors as bead `i`'s face followed by the cube-cell
of its target bead:

      □(ad.get i)  --ιᵂ ad i-->  ⋁ad  --φ-->  ⋁cd  --χ-->  □N
            |                                  ^            ^
      blockFace φ i             ιᵂ cd (blockIdx φ i)        |
            v                                  |            |
      □(cd.get (blockIdx φ i))  ===============+============+
-/
theorem bead_comp {ad cd : List ℕ+} {N : ℕ} (φ : ⋁ad ⟶ ⋁cd) (χ : ⋁cd ⟶ □N)
    (i : Fin ad.length) :
    yonedaEquiv (ιᵂ ad i ≫ (φ ≫ χ).hom)
      = blockFace φ.hom i ≫ yonedaEquiv (ιᵂ cd (blockIdx φ.hom i) ≫ χ.hom) := by
  have hg : yoneda.map (yonedaEquiv (ιᵂ cd (blockIdx φ.hom i) ≫ χ.hom))
      = ιᵂ cd (blockIdx φ.hom i) ≫ χ.hom := by
    rw [← yonedaEquiv_symm_box]; exact yonedaEquiv.symm_apply_apply _
  have h : ιᵂ ad i ≫ (φ.hom ≫ χ.hom)
      = yoneda.map (blockFace φ.hom i
          ≫ yonedaEquiv (ιᵂ cd (blockIdx φ.hom i) ≫ χ.hom)) := by
    refine Eq.trans (Category.assoc (ιᵂ ad i) φ.hom χ.hom).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ χ.hom) (blockFace_spec φ.hom i)) ?_
    refine Eq.trans (Category.assoc (yoneda.map (blockFace φ.hom i))
      (ιᵂ cd (blockIdx φ.hom i)) χ.hom) ?_
    refine Eq.trans (congrArg (fun t => yoneda.map (blockFace φ.hom i) ≫ t) hg.symm) ?_
    exact (yoneda.map_comp _ _).symm
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_yoneda_map _)

/-- The `⋁`-spelling of `serialWedge_ι_succ` followed by associativity: `Glue.inr`-spelled
composites do not accept `Category.assoc` by `rw`. -/
theorem ι_succ_comp {c : ℕ+} {rest : List ℕ+} {W : PrecubicalSet}
    (j' : Fin rest.length) (f : (⋁(c :: rest)).toPsh ⟶ W) :
    ιᵂ (c :: rest) j'.succ ≫ f = ιᵂ rest j' ≫ (wedgeInr (□(c : ℕ)) (⋁rest) ≫ f) :=
  Category.assoc _ _ _

/-- The face of `□N` traced by bead `i` of a wedge map — bead `i`'s entry of `cubesOf`. -/
def beadFace {A : List ℕ+} {N : ℕ} (χ : (⋁A).toPsh ⟶ (□N).toPsh) (i : Fin A.length) :
    ▫((A.get i : ℕ)) ⟶ ▫N := yonedaEquiv (ιᵂ A i ≫ χ)

theorem beadFace_succ {N : ℕ} (c : ℕ+) (rest : List ℕ+)
    (χ : (⋁(c :: rest)).toPsh ⟶ (□N).toPsh) (j : Fin rest.length) :
    beadFace χ j.succ = beadFace (wedgeInr (□(c : ℕ)) (⋁rest) ≫ χ) j :=
  congrArg yonedaEquiv (ι_succ_comp j χ)

/-- The coordinate of `□N` that an event's bead flips. -/
def cubeEv {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) (e : beadEvent ad) : Fin N :=
  faceEmb (beadFace χ.hom e.1) e.2

/-- **`evMap` preserves the coordinate an event flips.** -/
theorem cubeEv_comp {ad cd : List ℕ+} {N : ℕ} (φ : ⋁ad ⟶ ⋁cd) (χ : ⋁cd ⟶ □N) (e : beadEvent ad) :
    cubeEv (φ ≫ χ) e = cubeEv χ (evMap φ.hom e) := by
  rw [cubeEv, cubeEv, beadFace, beadFace, bead_comp φ χ e.1, faceEmb_comp]
  rfl

/-! ## Part 3 — `cubeEv` is a bijection, from surjectivity and cardinality

Every coordinate of `□N` is flipped by some bead (`flips_of_endpoints`, the endpoint reading of a
chain of a cube), so `cubeEv` is surjective; there are as many events as coordinates
(`card_beadEvent` + `dimSum_eq_of_cube`), so it is a bijection.  Injectivity — distinct events name
distinct coordinates — is then a corollary (`cubeEv_injective`, `beadFace_faceEmb_disjoint`), not a
premise.  `flipIdx` still inverts `cubeEv` numerically (`flipIdx_cubeEv`), which is what the
wall-crossing sign reads. -/

/-- The coordinates bead `i` flips are exactly the images of bead `i`'s own coordinates. -/
theorem mem_blockOf_iff_faceEmb {A : List ℕ+} {N : ℕ} (χ : (⋁A).toPsh ⟶ (□N).toPsh)
    (i : Fin (CubeChains.cubesOf A χ).length) (p : Fin N) :
    p ∈ CubeChains.blockOf (CubeChains.wedgeRefineObj A χ) i
      ↔ ∃ q, faceEmb (beadFace χ (i.cast (CubeChains.cubesOf_length A χ))) q = p := by
  change p ∈ noneSet (toStar ((CubeChains.cubesOf A χ).get i).2).val ↔ _
  rw [cubesOf_get]
  exact mem_noneSet_iff_faceEmb _ _

/-- **The bead a coordinate is flipped at is the bead it came from.** -/
theorem flipIdx_faceEmb_beadFace {A : List ℕ+} {N : ℕ} (χ : (⋁A).toPsh ⟶ (□N).toPsh)
    (i : Fin A.length) (q : Fin ((A.get i : ℕ))) :
    CubeChains.flipIdx (CubeChains.cubesOf A χ) (faceEmb (beadFace χ i) q) = i.val := by
  have hi : i.val < (CubeChains.cubesOf A χ).length := by
    rw [CubeChains.cubesOf_length]; exact i.isLt
  exact CubeChains.flipIdx_eq_of_mem_blockOf (CubeChains.wedgeRefineObj A χ) ⟨i.val, hi⟩
    ((mem_blockOf_iff_faceEmb χ ⟨i.val, hi⟩ _).mpr ⟨q, rfl⟩)

/-- **`flipIdx` inverts `cubeEv`.** -/
theorem flipIdx_cubeEv {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) (e : beadEvent ad) :
    CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) (cubeEv χ e) = (e.1 : ℕ) :=
  flipIdx_faceEmb_beadFace χ.hom e.1 e.2

/-- **A chain of `□ᴺ` has `N` events.**  `□0` *is* `⋁[]` and `□N` for `N ≥ 1` is `⋁[N]`, so both
cases are `serialWedge_dimSum_eq`. -/
theorem dimSum_eq_of_cube {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) : dimSum ad = N := by
  cases N with
  | zero => exact serialWedge_dimSum_eq (cd := []) χ
  | succ k =>
      have h := serialWedge_dimSum_eq (cd := [(⟨k + 1, k.succ_pos⟩ : ℕ+)])
        (χ ≫ (ChainCat.serialWedge1 (⟨k + 1, k.succ_pos⟩ : ℕ+)).inv)
      simpa [dimSum] using h

/-- **Every coordinate of `□ᴺ` is named by an event.**  It is flipped by some bead
(`flips_of_endpoints`: a chain of a cube runs all-`0` to all-`1`), and the bead's block is the
image of its face — so the coordinate is a `faceEmb` of one of that bead's own coordinates.  Free
of `Fval_mono`: only the constancy `.mpr` of the endpoint reading is used. -/
theorem cubeEv_surjective {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) :
    Function.Surjective (cubeEv χ) := by
  intro p
  have hf : CubeChains.Flips (CubeChains.cubesOf ad χ.hom) p :=
    CubeChains.flips_of_endpoints (CubeChains.wedgeRefineObj ad χ.hom) p
      (by rw [χ.app_init]; exact CubeChains.toStar_cube_init_val p)
      (by rw [χ.app_final]; exact CubeChains.toStar_cube_final_val p)
  have hlt : CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) p
      < (CubeChains.cubesOf ad χ.hom).length := hf
  have hmem : p ∈ CubeChains.blockOf (CubeChains.wedgeRefineObj ad χ.hom)
      ⟨CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) p, hlt⟩ := by
    change p ∈ noneSet (toStar ((CubeChains.cubesOf ad χ.hom).get
      ⟨CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) p, hlt⟩).2).val
    rw [List.get_eq_getElem]
    exact CubeChains.mem_noneSet_flipIdx hf
  obtain ⟨q, hq⟩ := (mem_blockOf_iff_faceEmb χ.hom
    ⟨CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) p, hlt⟩ p).mp hmem
  exact ⟨⟨(⟨CubeChains.flipIdx (CubeChains.cubesOf ad χ.hom) p, hlt⟩ :
      Fin (CubeChains.cubesOf ad χ.hom).length).cast (CubeChains.cubesOf_length ad χ.hom), q⟩, hq⟩

theorem cubeEv_bijective {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) :
    Function.Bijective (cubeEv χ) :=
  (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨cubeEv_surjective χ, by rw [card_beadEvent, Fintype.card_fin, dimSum_eq_of_cube χ]⟩

/-- Distinct events name distinct coordinates — a corollary of the bijection, not its input. -/
theorem cubeEv_injective {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) :
    Function.Injective (cubeEv χ) :=
  (cubeEv_bijective χ).injective

/-- Distinct beads' faces have disjoint images in `□ᴺ`: the `blockOf_disjoint` content read off
the bijection instead of feeding it. -/
theorem beadFace_faceEmb_disjoint {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N)
    {i j : Fin ad.length} (hij : i ≠ j) (q : Fin ((ad.get i : ℕ))) (q' : Fin ((ad.get j : ℕ))) :
    faceEmb (beadFace χ.hom i) q ≠ faceEmb (beadFace χ.hom j) q' := fun h =>
  hij (congrArg Sigma.fst (cubeEv_injective χ (show cubeEv χ ⟨i, q⟩ = cubeEv χ ⟨j, q'⟩ from h)))

/-- **An event of a chain of `□ᴺ` is a coordinate of `□ᴺ`.** -/
noncomputable def cubeEvEquiv {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) : beadEvent ad ≃ Fin N :=
  Equiv.ofBijective _ (cubeEv_bijective χ)

@[simp] theorem cubeEvEquiv_apply {ad : List ℕ+} {N : ℕ} (χ : ⋁ad ⟶ □N) (e : beadEvent ad) :
    cubeEvEquiv χ e = cubeEv χ e := rfl

/-! ## Part 4 — a serial wedge is a chain of a cube

`evMap` is a bijection because it is `cubeEv` conjugated: `cubeEv (φ ≫ χ) = cubeEv χ ∘ evMap φ`
for any chain `χ` of a cube, and both `cubeEv`s are bijections.  All that is needed of the
*staircase* `⋁cd ⟶ □(dimSum cd)` is that it exists — bead `j` gets the coordinate slot
`[Cⱼ, Cⱼ₊₁)` of the dimension prefix sums.  Its numbering is `cubeEv`'s job, not its own.

      □c  --lowFace-->  □(c+M)  <--highFace--  □M
      free: [0,c)                              free: [c,c+M)
-/

/-- The sign vector of the coordinate slot `[a, a+m)` of `□N`. -/
def slotCell (N a m : ℕ) : Fin N → Option Bool :=
  fun j => if j.val < a then some true else if j.val < a + m then none else some false

theorem noneSet_slotCell (N a m : ℕ) (h : a + m ≤ N) :
    noneSet (slotCell N a m)
      = Finset.univ.map
          ⟨fun q : Fin m => (⟨a + q.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left q.isLt a) h⟩ :
              Fin N),
           fun q q' hq => Fin.ext (by simpa using congrArg Fin.val hq)⟩ := by
  ext j
  rw [mem_noneSet, Finset.mem_map]
  constructor
  · intro hj
    have h1 : ¬ j.val < a := by
      intro h1; rw [slotCell, if_pos h1] at hj; exact Option.some_ne_none _ hj
    have h2 : j.val < a + m := by
      by_contra h2; rw [slotCell, if_neg h1, if_neg h2] at hj; exact Option.some_ne_none _ hj
    exact ⟨⟨j.val - a, by omega⟩, Finset.mem_univ _, Fin.ext (by simp; omega)⟩
  · rintro ⟨q, -, rfl⟩
    simp only [Function.Embedding.coeFn_mk]
    have h1 : ¬ (a + q.val < a) := by omega
    have h2 : a + q.val < a + m := Nat.add_lt_add_left q.isLt a
    rw [slotCell, if_neg h1, if_pos h2]

/-- The `m`-cell of `□N` freeing exactly the coordinate slot `[a, a+m)`. -/
def slot (N a m : ℕ) (h : a + m ≤ N) : Cell N m :=
  ⟨slotCell N a m, by
    rw [noneSet_slotCell N a m h, Finset.card_map, Finset.card_univ, Fintype.card_fin]⟩

/-- The face of `□(c+M)` freeing the first `c` coordinates. -/
def lowFace (c M : ℕ) : ▫c ⟶ ▫(c + M) := Box.ofSign (slot (c + M) 0 c (by omega))

/-- The face of `□(c+M)` freeing the last `M` coordinates. -/
def highFace (c M : ℕ) : ▫M ⟶ ▫(c + M) := Box.ofSign (slot (c + M) c M (by omega))

theorem subst_slot_constVertex_val (N a m : ℕ) (h : a + m ≤ N) (ε : Bool) (j : Fin N) :
    (subst (slot N a m h) (constVertex m ε)).val j
      = if j.val < a then some true else if j.val < a + m then some ε else some false := by
  have hval : (slot N a m h).val j
      = if j.val < a then some true else if j.val < a + m then none else some false := rfl
  rw [subst_val]
  by_cases h1 : j.val < a
  · have hne : (slot N a m h).val j ≠ none := by
      rw [hval, if_pos h1]; exact Option.some_ne_none _
    rw [substFun_of_some _ _ hne, hval, if_pos h1, if_pos h1]
  · by_cases h2 : j.val < a + m
    · have he : (slot N a m h).val j = none := by rw [hval, if_neg h1, if_pos h2]
      rw [substFun_of_none _ _ he, if_neg h1, if_pos h2]
      rfl
    · have hne : (slot N a m h).val j ≠ none := by
        rw [hval, if_neg h1, if_neg h2]; exact Option.some_ne_none _
      rw [substFun_of_some _ _ hne, hval, if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem box_ob_dim (n : ℕ) : (▫n).dim = n := rfl

theorem sign_initVertexMap (n : ℕ) :
    Box.sign (PrecubicalSet.initVertexMap n) = constVertex n false :=
  ev_canonicalMap (K := stdPre n) _

theorem sign_finalVertexMap (n : ℕ) :
    Box.sign (PrecubicalSet.finalVertexMap n) = constVertex n true :=
  ev_canonicalMap (K := stdPre n) _

theorem initVertexMap_comp_lowFace (c M : ℕ) :
    PrecubicalSet.initVertexMap c ≫ lowFace c M = PrecubicalSet.initVertexMap (c + M) := by
  refine Box.hom_ext (Subtype.ext (funext fun j => ?_))
  rw [Box.sign_comp, lowFace, Box.sign_ofSign, sign_initVertexMap,
    subst_slot_constVertex_val, sign_initVertexMap]
  have hj : (j : ℕ) < c + M := j.isLt
  simp only [box_ob_dim]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem finalVertexMap_comp_highFace (c M : ℕ) :
    PrecubicalSet.finalVertexMap M ≫ highFace c M = PrecubicalSet.finalVertexMap (c + M) := by
  refine Box.hom_ext (Subtype.ext (funext fun j => ?_))
  rw [Box.sign_comp, highFace, Box.sign_ofSign, sign_finalVertexMap,
    subst_slot_constVertex_val, sign_finalVertexMap]
  have hj : (j : ℕ) < c + M := j.isLt
  simp only [box_ob_dim]
  split_ifs <;> rfl

/-- The junction of the two slots: the far end of the low face is the near end of the high one. -/
theorem finalVertexMap_comp_lowFace (c M : ℕ) :
    PrecubicalSet.finalVertexMap c ≫ lowFace c M
      = PrecubicalSet.initVertexMap M ≫ highFace c M := by
  refine Box.hom_ext (Subtype.ext (funext fun j => ?_))
  rw [Box.sign_comp, Box.sign_comp, lowFace, highFace, Box.sign_ofSign, Box.sign_ofSign,
    sign_finalVertexMap, sign_initVertexMap, subst_slot_constVertex_val,
    subst_slot_constVertex_val]
  have hj : (j : ℕ) < c + M := j.isLt
  simp only [box_ob_dim]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cube_initVertex (n : ℕ) :
    (□n).initVertex = yoneda.map (PrecubicalSet.initVertexMap n) :=
  yonedaEquiv_symm_box _

theorem cube_finalVertex (n : ℕ) :
    (□n).finalVertex = yoneda.map (PrecubicalSet.finalVertexMap n) :=
  yonedaEquiv_symm_box _

/-- The **staircase** of `cd`: the chain of the single cube `□(dimSum cd)` that gives bead `j`
the coordinate slot `[Cⱼ, Cⱼ₊₁)` of the dimension prefix sums. -/
def stairHom : (cd : List ℕ+) → (⋁cd ⟶ □(dimSum cd))
  | [] => 𝟙 (□0)
  | c :: rest =>
      { hom := wedge2Desc (yoneda.map (lowFace (c : ℕ) (dimSum rest)))
            ((stairHom rest).hom ≫ yoneda.map (highFace (c : ℕ) (dimSum rest)))
            (by
              rw [← Category.assoc, initVertex_comp_hom (stairHom rest),
                cube_finalVertex, cube_initVertex]
              exact ((yoneda.map_comp _ _).symm.trans
                (congrArg yoneda.map (finalVertexMap_comp_lowFace (c : ℕ) (dimSum rest)))).trans
                (yoneda.map_comp _ _))
        app_init := by
          refine app_init_eq_of_initVertex _ ?_
          rw [wedge2_initVertex, Category.assoc, wedge2Desc_inl, cube_initVertex]
          exact ((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map (initVertexMap_comp_lowFace (c : ℕ) (dimSum rest)))).trans
            (cube_initVertex _).symm
        app_final := by
          refine app_final_eq_of_finalVertex _ ?_
          rw [wedge2_finalVertex, Category.assoc, wedge2Desc_inr, ← Category.assoc,
            finalVertex_comp_hom (stairHom rest), cube_finalVertex]
          exact ((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map (finalVertexMap_comp_highFace (c : ℕ) (dimSum rest)))).trans
            (cube_finalVertex _).symm }

/-- **A chain map is a bijection on events.**  `evMap φ` is `cubeEv` conjugated by the staircase,
and `cubeEv` is a bijection at both ends. -/
theorem evMap_bijective {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    Function.Bijective (evMap φ.hom) := by
  have hcomp : ∀ e, cubeEv (φ ≫ stairHom cd) e = cubeEv (stairHom cd) (evMap φ.hom e) :=
    cubeEv_comp φ (stairHom cd)
  refine ⟨fun a b hab => (cubeEv_bijective (φ ≫ stairHom cd)).injective ?_, fun y => ?_⟩
  · rw [hcomp, hcomp, hab]
  · obtain ⟨x, hx⟩ :=
      (cubeEv_bijective (φ ≫ stairHom cd)).surjective (cubeEv (stairHom cd) y)
    exact ⟨x, (cubeEv_bijective (stairHom cd)).injective ((hcomp x).symm.trans hx)⟩

/-- **The events of a chain map, as an equivalence.**  Consumer: bead `Cubical-p89` (`ConcPos`),
which inverts it in `evPerm f := evOrd x.run ∘ evMap f ∘ (evOrd y.run)⁻¹`. -/
noncomputable def evEquiv {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) : beadEvent ad ≃ beadEvent cd :=
  Equiv.ofBijective _ (evMap_bijective φ)

@[simp] theorem evEquiv_apply {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) (e : beadEvent ad) :
    evEquiv φ e = evMap φ.hom e := rfl

end CubeChain
