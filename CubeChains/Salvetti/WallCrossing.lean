import CubeChains.Salvetti.RunOrderFace
import CubeChains.Salvetti.RunHeightSplit

/-!
# Salvetti/WallCrossing — the bead-local half of the Salvetti wall-crossing law

`wallCrossing_of_sameBlock` asks that restricting a run along `f : a ⟶ b` preserve the relative
order of any two coordinates lying in one bead of `a`.  The two halves of that argument live in
`RunOrderFace` (a single bead) and `RunHeightSplit` (the concatenation).  Gluing them needs a
height defined on *raw cube lists* rather than on chains from `init` to `final` — the
recursion cuts a wedge at a junction, and the halves no longer cover `Fin n`.  `flipIdx` is that
height (`List.findIdx`, so appends and maps are free), and `flipIdx_lt_iff_endpoints` is what
replaces the covering argument: the coordinates a chain flips depend only on its two endpoints.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Part 0 — `flipIdx`: the position at which a cube list flips a coordinate

Defined on a raw list of cubes, with no chain condition, so that it survives the cut of a wedge
at a junction.  `List.findIdx` gives `flipIdx_append` and `flipIdx_map` for nothing; on an honest
chain the block is unique, so `flipIdx` *is* `blockIndex` (`flipIdx_eq_blockIndex`). -/

/-- The cubes a wedge map into `□ⁿ` traces out. -/
abbrev CubeList (n : ℕ) : Type := List (Σ d : ℕ+, (□n).cells (d : ℕ))

/-- "This cube flips coordinate `p`". -/
def flipsAt (p : Fin n) (c : Σ d : ℕ+, (□n).cells (d : ℕ)) : Bool :=
  decide (p ∈ noneSet (toStar c.2).val)

@[simp] theorem flipsAt_eq_true {p : Fin n} {c : Σ d : ℕ+, (□n).cells (d : ℕ)} :
    flipsAt p c = true ↔ p ∈ noneSet (toStar c.2).val := by
  simp [flipsAt]

/-- **The height of a coordinate in a cube list**: the position of the cube that flips it, or the
length of the list if none does. -/
def flipIdx (L : CubeList n) (p : Fin n) : ℕ := L.findIdx (flipsAt p)

/-- `p` is flipped somewhere in `L` exactly when its height is a genuine position. -/
theorem flipIdx_lt_iff (L : CubeList n) (p : Fin n) :
    flipIdx L p < L.length ↔ ∃ c ∈ L, p ∈ noneSet (toStar c.2).val := by
  rw [flipIdx, List.findIdx_lt_length]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, flipsAt_eq_true.mp h⟩,
    fun ⟨c, hc, h⟩ => ⟨c, hc, flipsAt_eq_true.mpr h⟩⟩

/-- The cube found at a coordinate's height does flip it. -/
theorem mem_noneSet_flipIdx {L : CubeList n} {p : Fin n} (h : flipIdx L p < L.length) :
    p ∈ noneSet (toStar (L[flipIdx L p]'h).2).val :=
  flipsAt_eq_true.mp (List.findIdx_getElem (w := h))

/-- `flipIdx` over an append: found in the first half, or shifted past it. -/
theorem flipIdx_append (L₁ L₂ : CubeList n) (p : Fin n) :
    flipIdx (L₁ ++ L₂) p
      = if flipIdx L₁ p < L₁.length then flipIdx L₁ p else flipIdx L₂ p + L₁.length :=
  List.findIdx_append

/-- **On a chain, `flipIdx` is `blockIndex`** — the block containing a coordinate is unique, so
the first block that flips it is the only one. -/
theorem flipIdx_eq_blockIndex (x : RefineObj (□n).init (□n).final) (p : Fin n) :
    flipIdx x.cubes p = ((blockIndex x p : ℕ)) := by
  have hex : flipIdx x.cubes p < x.cubes.length :=
    (flipIdx_lt_iff _ _).mpr ⟨x.cubes.get (blockIndex x p), List.get_mem _ _, blockIndex_mem x p⟩
  refine congrArg Fin.val (blockIndex_unique x (i := ⟨flipIdx x.cubes p, hex⟩) ?_).symm
  change p ∈ noneSet (toStar (x.cubes.get ⟨flipIdx x.cubes p, hex⟩).2).val
  rw [List.get_eq_getElem]
  exact mem_noneSet_flipIdx hex

/-! ## Part 1 — the support of a chain is read off its two endpoints

A coordinate never un-flips (`Fval_mono`), so it is flipped somewhere along a chain exactly when
it is `0` at the source vertex and `1` at the target.  This is what replaces the covering argument
of `BraidPartition` once the recursion cuts a wedge at a junction: the two halves are chains with
their own endpoints, and comparing supports across the cut costs nothing. -/

/-- A `0`-cell has no free coordinate. -/
theorem zeroCell_ne_none (v : (□n).cells 0) (p : Fin n) : (toStar v).val p ≠ none := by
  intro hv
  have hmem : p ∈ noneSet (toStar v).val := mem_noneSet.mpr hv
  rw [Finset.card_eq_zero.mp (toStar v).prop] at hmem
  simp at hmem

/-- Trichotomy for a `0`-cell's value at a coordinate. -/
theorem eq_some_false_of_ne {v : Option Bool} (h1 : v ≠ none) (h2 : ¬ v = some true) :
    v = some false := by
  cases v with
  | none => exact absurd rfl h1
  | some b => cases b with
    | true => exact absurd rfl h2
    | false => rfl

/-- **The support of a chain is its pair of endpoints.** -/
theorem flipIdx_lt_iff_endpoints {u w : (□n).cells 0} (x : RefineObj u w) (p : Fin n) :
    flipIdx x.cubes p < x.cubes.length
      ↔ ((toStar u).val p = some false ∧ (toStar w).val p = some true) := by
  have hzero : vtxCanon x.cubes w 0 = u := isCubeChain_vtx_zero u w x.cubes x.isChain
  have hlast : vtxCanon x.cubes w (Fin.last x.cubes.length) = w := vtxCanon_last _ _
  constructor
  · intro hlt
    have hb : p ∈ blockOf x ⟨flipIdx x.cubes p, hlt⟩ := by
      change p ∈ noneSet (toStar (x.cubes.get ⟨flipIdx x.cubes p, hlt⟩).2).val
      rw [List.get_eq_getElem]
      exact mem_noneSet_flipIdx hlt
    set i : Fin x.cubes.length := ⟨flipIdx x.cubes p, hlt⟩ with hi
    have hcs : Fval x p i.castSucc = false := by
      simp only [Fval]; rw [toStar_junc_castSucc x i p, if_pos hb]; rfl
    have hsc : Fval x p i.succ = true := by
      simp only [Fval]; rw [toStar_junc_succ x i p, if_pos hb]; rfl
    have h0 : Fval x p 0 = false :=
      le_antisymm (hcs ▸ Fval_mono x p (Fin.zero_le _)) (Bool.false_le _)
    have hL : Fval x p (Fin.last x.cubes.length) = true :=
      le_antisymm (Bool.le_true _) (hsc ▸ Fval_mono x p (Fin.le_last _))
    simp only [Fval] at h0 hL
    rw [hzero] at h0
    rw [hlast] at hL
    exact ⟨eq_some_false_of_ne (zeroCell_ne_none u p) (of_decide_eq_false h0), of_decide_eq_true hL⟩
  · rintro ⟨hu, hw⟩
    by_contra hnl
    have hnone : ∀ i : Fin x.cubes.length, p ∉ blockOf x i := fun i hi =>
      hnl ((flipIdx_lt_iff _ _).mpr ⟨x.cubes.get i, List.get_mem _ _, hi⟩)
    have hstep : ∀ i : Fin x.cubes.length, Fval x p i.castSucc = Fval x p i.succ := by
      intro i
      simp only [Fval]
      rw [toStar_junc_castSucc x i p, toStar_junc_succ x i p, if_neg (hnone i), if_neg (hnone i)]
    have hconst : ∀ j : Fin (x.cubes.length + 1), Fval x p j = Fval x p 0 := by
      intro j
      induction j using Fin.induction with
      | zero => rfl
      | succ k ih => rw [← hstep k]; exact ih
    have hL := hconst (Fin.last x.cubes.length)
    simp only [Fval] at hL
    rw [hzero, hlast, hu, hw] at hL
    simp at hL

/-- The chain of `□ⁿ` a wedge map traces out, with its two endpoints. -/
def wedgeRefineObj (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) :
    RefineObj (χ⟪0⟫ (⋁M).init) (χ⟪0⟫ (⋁M).final) :=
  ⟨wedgeToCubes ⟨M, χ⟩, wedgeToCubes_isCubeChain M χ⟩

/-- The support of a wedge map's cube list, in endpoint form. -/
theorem supp_iff (M : List ℕ+) (χ : (⋁M).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    flipIdx (wedgeToCubes ⟨M, χ⟩) p < (wedgeToCubes ⟨M, χ⟩).length
      ↔ ((toStar (χ⟪0⟫ (⋁M).init)).val p = some false
          ∧ (toStar (χ⟪0⟫ (⋁M).final)).val p = some true) :=
  flipIdx_lt_iff_endpoints (wedgeRefineObj M χ) p

/-- Two wedge maps with the same endpoints flip the same coordinates. -/
theorem supp_congr {M₁ M₂ : List ℕ+} (χ₁ : (⋁M₁).toPsh ⟶ (□n).toPsh)
    (χ₂ : (⋁M₂).toPsh ⟶ (□n).toPsh)
    (hi : χ₁⟪0⟫ (⋁M₁).init = χ₂⟪0⟫ (⋁M₂).init)
    (hf : χ₁⟪0⟫ (⋁M₁).final = χ₂⟪0⟫ (⋁M₂).final) (p : Fin n) :
    (flipIdx (wedgeToCubes ⟨M₁, χ₁⟩) p < (wedgeToCubes ⟨M₁, χ₁⟩).length
      ↔ flipIdx (wedgeToCubes ⟨M₂, χ₂⟩) p < (wedgeToCubes ⟨M₂, χ₂⟩).length) := by
  rw [supp_iff, supp_iff, hi, hf]

/-- **Precomposing with a bi-pointed map does not change the support** — the endpoints are
preserved.  Both a refinement `⋁A ⟶ ⋁L` and a run `runObj m ⟶ ⋁L` are of this shape, so this one
statement covers every support comparison the recursion needs. -/
theorem supp_precomp {M₁ M₂ : List ℕ+} (h : ⋁M₂ ⟶ ⋁M₁) (χ : (⋁M₁).toPsh ⟶ (□n).toPsh)
    (p : Fin n) :
    (flipIdx (wedgeToCubes ⟨M₂, h.hom ≫ χ⟩) p < (wedgeToCubes ⟨M₂, h.hom ≫ χ⟩).length
      ↔ flipIdx (wedgeToCubes ⟨M₁, χ⟩) p < (wedgeToCubes ⟨M₁, χ⟩).length) := by
  refine supp_congr _ _ ?_ ?_ p
  · rw [← comp_app_cell (rfl : h.hom ≫ χ = h.hom ≫ χ) 0 ((⋁M₂).init), h.app_init]
  · rw [← comp_app_cell (rfl : h.hom ≫ χ = h.hom ≫ χ) 0 ((⋁M₂).final), h.app_final]

/-! ## Part 2 — pushing a cube list of `□ᵏ` forward along a face

A bead of a chain of `□ⁿ` *is* a face `▫d ⟶ ▫n`, so everything that happens inside one bead is a
chain of `□ᵈ` pushed forward.  On coordinates the pushforward is `faceEmb`, and `noneSet_app` says
the free coordinates travel along it — so `flipIdx` is unchanged. -/

/-- Push a cube list of `□ᵏ` forward along a face `▫k ⟶ ▫n`. -/
def pushCubes {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) : CubeList n :=
  L.map (fun c => ⟨c.1, (c.2 : ▫((c.1 : ℕ)) ⟶ ▫k) ≫ β⟩)

@[simp] theorem pushCubes_length {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) :
    (pushCubes β L).length = L.length := List.length_map _

/-- Yoneda turns a composite of cube maps into a composite of faces. -/
theorem yonedaEquiv_comp_face {a b c : ℕ} (f : (□a).toPsh ⟶ (□b).toPsh)
    (g : (□b).toPsh ⟶ (□c).toPsh) :
    yonedaEquiv (f ≫ g) = yonedaEquiv f ≫ yonedaEquiv g :=
  (map_yonedaEquiv g (yonedaEquiv f)).symm

/-- **Free coordinates travel along `faceEmb`.** -/
theorem mem_noneSet_comp_face {k d : ℕ} (c : (□k).cells d) (β : ▫k ⟶ ▫n) (p : Fin k) :
    faceEmb β p ∈ noneSet (toStar ((c : ▫d ⟶ ▫k) ≫ β)).val ↔ p ∈ noneSet (toStar c).val := by
  rw [show toStar ((c : ▫d ⟶ ▫k) ≫ β) = act (K := stdPre n) (toStar β) (toStar c) from
      ev_comp_app c β, noneSet_app (toStar β) (toStar c)]
  exact Finset.mem_map' (nones (toStar β)).toEmbedding

/-- `flipIdx` is invariant under the pushforward. -/
theorem flipIdx_pushCubes {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) (p : Fin k) :
    flipIdx (pushCubes β L) (faceEmb β p) = flipIdx L p := by
  rw [flipIdx, pushCubes, List.findIdx_map, flipIdx]
  refine congrArg (fun q => List.findIdx q L) (funext fun c => ?_)
  simp only [Function.comp_apply, flipsAt, decide_eq_decide]
  exact mem_noneSet_comp_face c.2 β p

/-- **Postcomposing a wedge map with a face is the pushforward of its cube list.** -/
theorem wedgeToCubes_comp_face : ∀ (M : List ℕ+) {k : ℕ} (χ : (⋁M).toPsh ⟶ (□k).toPsh)
    (G : (□k).toPsh ⟶ (□n).toPsh),
    wedgeToCubes ⟨M, χ ≫ G⟩ = pushCubes (yonedaEquiv G) (wedgeToCubes ⟨M, χ⟩)
  | [], _, _, _ => by simp [CubeChain.wedgeToCubes, pushCubes]
  | c :: rest, k, χ, G => by
      have htail : Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ χ ≫ G
          = (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ χ) ≫ G :=
        (Category.assoc _ _ _).symm
      have hhead : yonedaEquiv (Glue.inl (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ χ ≫ G)
          = yonedaEquiv (Glue.inl (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ χ)
              ≫ yonedaEquiv G := by
        rw [← Category.assoc]
        exact yonedaEquiv_comp_face _ G
      have ih := wedgeToCubes_comp_face rest
        (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ χ) G
      simp only [wedgeToCubes, pushCubes, List.map_cons]
      exact congrArg₂ List.cons
        (congrArg (fun z : (□n).cells (c : ℕ) => (⟨c, z⟩ : Σ d : ℕ+, (□n).cells (d : ℕ))) hhead)
        ih

/-! ## Part 3 — one bead of the source, one bead of the target

The base case.  A one-bead chain of `□ⁿ` is a face `γ : ▫e ⟶ ▫n` and everything above it is the
pushforward of a chain of `□ᵉ`, so `RunOrderFace`'s law transfers verbatim along `faceEmb γ`. -/

/-- A chain of `□ᵏ` flips every coordinate: it runs from the all-`0` vertex to the all-`1` one. -/
theorem flipIdx_lt_of_cube {M : List ℕ+} {k : ℕ} (χ : ⋁M ⟶ □k) (p : Fin k) :
    flipIdx (wedgeToCubes ⟨M, χ.hom⟩) p < (wedgeToCubes ⟨M, χ.hom⟩).length := by
  rw [supp_iff, χ.app_init, χ.app_final,
    show (□k).init = canonicalMap (constVertex k false) from rfl,
    show (□k).final = canonicalMap (constVertex k true) from rfl,
    toStar_canonicalMap, toStar_canonicalMap]
  exact ⟨rfl, rfl⟩

/-- A coordinate is flipped by a pushed-forward chain exactly when it comes from one that the
original chain flips. -/
theorem flipIdx_pushCubes_lt_iff {k : ℕ} (β : ▫k ⟶ ▫n) (L : CubeList k) (p : Fin n) :
    flipIdx (pushCubes β L) p < (pushCubes β L).length
      ↔ ∃ p', faceEmb β p' = p ∧ flipIdx L p' < L.length := by
  constructor
  · intro h
    obtain ⟨c, hc, hpc⟩ := (flipIdx_lt_iff _ _).mp h
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
    rw [show toStar ((c₀.2 : ▫((c₀.1 : ℕ)) ⟶ ▫k) ≫ β)
        = act (K := stdPre n) (toStar β) (toStar c₀.2) from ev_comp_app c₀.2 β,
      noneSet_app (toStar β) (toStar c₀.2), Finset.mem_map] at hpc
    obtain ⟨p', hp', hpe⟩ := hpc
    exact ⟨p', hpe, (flipIdx_lt_iff _ _).mpr ⟨c₀, hc₀, hp'⟩⟩
  · rintro ⟨p', rfl, hp'⟩
    rw [flipIdx_pushCubes, pushCubes_length]
    exact hp'

/-- The cube list of the one-bead chain `γ : ▫e ⟶ ▫n`, as a pushforward. -/
theorem beadChain_cubes (e : ℕ+) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) :
    wedgeToCubes ⟨[e], (serialWedge1 e).hom.hom ≫ γ⟩
      = pushCubes (yonedaEquiv γ) (wedgeToCubes ⟨[e], (serialWedge1 e).hom.hom⟩) :=
  wedgeToCubes_comp_face [e] _ γ

/-- The cube list a one-bead run traces out in `□ⁿ`, as a pushforward of its own edge chain. -/
theorem beadRun_cubes (e : ℕ+) (u : Run [e]) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) :
    wedgeToCubes ⟨𝟙^(dimSum [e]), u.hom ≫ (serialWedge1 e).hom.hom ≫ γ⟩
      = pushCubes (yonedaEquiv γ)
          (wedgeToRefineObj (runChain (beadCh e) u)).cubes := by
  have h : (u.hom ≫ (serialWedge1 e).hom.hom) ≫ γ
      = u.hom ≫ (serialWedge1 e).hom.hom ≫ γ := Category.assoc _ _ _
  exact h ▸ wedgeToCubes_comp_face (𝟙^(dimSum [e])) (u.hom ≫ (serialWedge1 e).hom.hom) γ

/-- **A one-bead chain flips exactly the coordinates in its face.** -/
theorem flipIdx_beadChain_lt_iff (e : ℕ+) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    flipIdx (wedgeToCubes ⟨[e], (serialWedge1 e).hom.hom ≫ γ⟩) p
        < (wedgeToCubes ⟨[e], (serialWedge1 e).hom.hom ≫ γ⟩).length
      ↔ ∃ p', faceEmb (yonedaEquiv γ) p' = p := by
  rw [beadChain_cubes, flipIdx_pushCubes_lt_iff]
  exact ⟨fun ⟨p', hp', _⟩ => ⟨p', hp'⟩,
    fun ⟨p', hp'⟩ => ⟨p', hp', flipIdx_lt_of_cube (serialWedge1 e).hom p'⟩⟩

/-- **The height of a coordinate under a one-bead run** is the run's own `runHeight`, read through
the bead's face. -/
theorem flipIdx_beadRun (e : ℕ+) (u : Run [e]) (γ : (□(e : ℕ)).toPsh ⟶ (□n).toPsh)
    (p' : Fin (e : ℕ)) :
    (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [e]), u.hom ≫ (serialWedge1 e).hom.hom ≫ γ⟩)
        (faceEmb (yonedaEquiv γ) p') : ℤ)
      = runHeight (beadCh e) u p' := by
  rw [beadRun_cubes, flipIdx_pushCubes]
  exact congrArg (fun k : ℕ => (k : ℤ))
    (flipIdx_eq_blockIndex (wedgeToRefineObj (runChain (beadCh e) u)) p')

/-- **The base case**: restricting along a single face preserves the order of a run, read in the
ambient `□ⁿ`. -/
theorem key_face {e c : ℕ+} (F : (□(e : ℕ)).toPsh ⟶ (□(c : ℕ)).toPsh)
    (Φ : (□(c : ℕ)).toPsh ⟶ (□n).toPsh) (t : Run [c]) (p' q' : Fin (e : ℕ)) :
    (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [e]),
          (runRestrictFace F t).hom ≫ (serialWedge1 e).hom.hom ≫ F ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) p')
        < flipIdx (wedgeToCubes ⟨𝟙^(dimSum [e]),
          (runRestrictFace F t).hom ≫ (serialWedge1 e).hom.hom ≫ F ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) q')
      ↔ flipIdx (wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ (serialWedge1 c).hom.hom ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) p')
        < flipIdx (wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ (serialWedge1 c).hom.hom ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) q')) := by
  have hemb : ∀ x : Fin (e : ℕ), faceEmb (yonedaEquiv (F ≫ Φ)) x
      = faceEmb (yonedaEquiv Φ) (faceEmb (yonedaEquiv F) x) := by
    intro x
    rw [yonedaEquiv_comp_face F Φ]
    exact faceEmb_comp _ _ x
  have hL : ∀ x : Fin (e : ℕ),
      (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [e]),
          (runRestrictFace F t).hom ≫ (serialWedge1 e).hom.hom ≫ F ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) x) : ℤ)
        = runHeight (beadCh e) (runRestrictFace F t) x :=
    fun x => flipIdx_beadRun e (runRestrictFace F t) (F ≫ Φ) x
  have hR : ∀ x : Fin (e : ℕ),
      (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ (serialWedge1 c).hom.hom ≫ Φ⟩)
          (faceEmb (yonedaEquiv (F ≫ Φ)) x) : ℤ)
        = runHeight (beadCh c) t (faceEmb (yonedaEquiv F) x) := by
    intro x
    rw [hemb x]
    exact flipIdx_beadRun c t Φ (faceEmb (yonedaEquiv F) x)
  rw [← Nat.cast_lt (α := ℤ), ← Nat.cast_lt (α := ℤ), hL, hL, hR, hR]
  exact runHeight_runRestrictFace_lt_iff F t p' q'

/-! ## Part 4 — the append calculus for `flipIdx`

Both recursions cut a wedge at a junction, so both compare two coordinates across an append.  A
tie of the coarse chain keeps them on the same side; on each side the comparison is that side's
own. -/

theorem flipIdx_append_left {L₁ L₂ : CubeList n} {p : Fin n} (h : flipIdx L₁ p < L₁.length) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₁ p := by rw [flipIdx_append, if_pos h]

theorem flipIdx_append_right {L₁ L₂ : CubeList n} {p : Fin n} (h : ¬ flipIdx L₁ p < L₁.length) :
    flipIdx (L₁ ++ L₂) p = flipIdx L₂ p + L₁.length := by rw [flipIdx_append, if_neg h]

/-- **A tie does not straddle the junction.** -/
theorem flipIdx_sameSide {L₁ L₂ : CubeList n} {p q : Fin n}
    (h : flipIdx (L₁ ++ L₂) p = flipIdx (L₁ ++ L₂) q)
    (hp : flipIdx L₁ p < L₁.length) : flipIdx L₁ q < L₁.length := by
  by_contra hq
  rw [flipIdx_append_left hp, flipIdx_append_right hq] at h
  omega

theorem flipIdx_append_lt_iff_left {L₁ L₂ : CubeList n} {p q : Fin n}
    (hp : flipIdx L₁ p < L₁.length) (hq : flipIdx L₁ q < L₁.length) :
    (flipIdx (L₁ ++ L₂) p < flipIdx (L₁ ++ L₂) q ↔ flipIdx L₁ p < flipIdx L₁ q) := by
  rw [flipIdx_append_left hp, flipIdx_append_left hq]

theorem flipIdx_append_lt_iff_right {L₁ L₂ : CubeList n} {p q : Fin n}
    (hp : ¬ flipIdx L₁ p < L₁.length) (hq : ¬ flipIdx L₁ q < L₁.length) :
    (flipIdx (L₁ ++ L₂) p < flipIdx (L₁ ++ L₂) q ↔ flipIdx L₂ p < flipIdx L₂ q) := by
  rw [flipIdx_append_right hp, flipIdx_append_right hq]
  omega

/-! ## Part 5 — the source recursion: a wedge restricted onto one bead of the target

The three cube lists are *parameters* with defining equations rather than literal terms in the
statement.  Both recursions cut a wedge at a junction, and the two spellings of a cut composite
(`ι ≫ g ≫ Φ` versus `(ι ≫ g) ≫ Φ`, `runObj m` versus `⋁(𝟙^m)`) are `rfl`-equal but not
syntactically equal, so `rw` will not see through them; against a plain variable it always does. -/

/-- **`runRestrictWedge` preserves the order of a run inside one bead of the source.**  Recursion
on the source list: the head bead is `key_face`, the tail is the recursive call, and a tie of the
source chain never straddles the junction between them. -/
theorem key_wedge : ∀ (A : List ℕ+) (c : ℕ+) (g : (⋁A).toPsh ⟶ (□(c : ℕ)).toPsh)
    (Φ : (□(c : ℕ)).toPsh ⟶ (□n).toPsh) (t : Run [c]) (X U V : CubeList n),
    X = wedgeToCubes ⟨A, g ≫ Φ⟩ →
    U = wedgeToCubes ⟨𝟙^(dimSum A), (runRestrictWedge A g t).hom ≫ g ≫ Φ⟩ →
    V = wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ (serialWedge1 c).hom.hom ≫ Φ⟩ →
    ∀ p q : Fin n, flipIdx X p = flipIdx X q → flipIdx X p < X.length →
    (flipIdx U p < flipIdx U q ↔ flipIdx V p < flipIdx V q)
  | [], c, g, Φ, t, X, U, V, hX, _, _, p, q, _, hfound => by
      subst hX
      rw [wedgeToCubes_length] at hfound
      exact absurd hfound (by simp)
  | e :: rest, c, g, Φ, t, X, U, V, hX, hU, hV, p, q, hpq, hfound => by
    set F : (□(e : ℕ)).toPsh ⟶ (□(c : ℕ)).toPsh :=
      (serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g with hF
    set u₁ : Run [e] := runRestrictFace F t with hu₁
    set u₂ : Run rest := runRestrictWedge rest (wedgeInclR [e] rest ≫ g) t with hu₂
    set ψL : (⋁[e]).toPsh ⟶ (□n).toPsh := wedgeInclL [e] rest ≫ g ≫ Φ with hψL
    set ψR : (⋁rest).toPsh ⟶ (□n).toPsh := wedgeInclR [e] rest ≫ g ≫ Φ with hψR
    -- the source chain and the restricted run both split at the junction
    have hXs : X = wedgeToCubes ⟨[e], ψL⟩ ++ wedgeToCubes ⟨rest, ψR⟩ :=
      hX.trans (wedgeToCubes_append [e] rest (g ≫ Φ))
    have hUs : U = wedgeToCubes ⟨𝟙^(dimSum [e]), u₁.hom ≫ ψL⟩
          ++ wedgeToCubes ⟨𝟙^(dimSum rest), u₂.hom ≫ ψR⟩ :=
      hU.trans (wedgeToCubes_runAppend (K := □n) [e] rest u₁ u₂ (g ≫ Φ))
    -- the head bead, presented through its own cube
    have hid : (serialWedge1 e).hom.hom ≫ (serialWedge1 e).inv.hom = 𝟙 ((⋁[e]).toPsh) :=
      congrArg BPSet.Hom.hom (serialWedge1 e).hom_inv_id
    have hcancel : (serialWedge1 e).hom.hom ≫ F ≫ Φ = ψL := by
      rw [hF, hψL, show ((serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g) ≫ Φ
          = (serialWedge1 e).inv.hom ≫ wedgeInclL [e] rest ≫ g ≫ Φ by
            simp only [Category.assoc], ← Category.assoc, hid, Category.id_comp]
    have hX₁ : wedgeToCubes ⟨[e], ψL⟩
        = wedgeToCubes ⟨[e], (serialWedge1 e).hom.hom ≫ F ≫ Φ⟩ := by rw [hcancel]
    have hU₁ : wedgeToCubes ⟨𝟙^(dimSum [e]), u₁.hom ≫ ψL⟩
        = wedgeToCubes ⟨𝟙^(dimSum [e]),
            (runRestrictFace F t).hom ≫ (serialWedge1 e).hom.hom ≫ F ≫ Φ⟩ := by
      rw [hcancel, hu₁]
    -- the head half of the source chain and of the restricted run have the same support
    have hsupp₁ : ∀ x : Fin n,
        (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [e]), u₁.hom ≫ ψL⟩) x
            < (wedgeToCubes ⟨𝟙^(dimSum [e]), u₁.hom ≫ ψL⟩).length
          ↔ flipIdx (wedgeToCubes ⟨[e], ψL⟩) x < (wedgeToCubes ⟨[e], ψL⟩).length) :=
      fun x => supp_precomp (M₂ := 𝟙^(dimSum [e])) (M₁ := [e]) u₁ ψL x
    rw [hUs, hV]
    rw [hXs] at hpq hfound
    by_cases hcase : flipIdx (wedgeToCubes ⟨[e], ψL⟩) p < (wedgeToCubes ⟨[e], ψL⟩).length
    · -- both coordinates are flipped inside the head bead
      have hcaseq : flipIdx (wedgeToCubes ⟨[e], ψL⟩) q < (wedgeToCubes ⟨[e], ψL⟩).length :=
        flipIdx_sameSide hpq hcase
      rw [flipIdx_append_lt_iff_left ((hsupp₁ p).mpr hcase) ((hsupp₁ q).mpr hcaseq)]
      obtain ⟨p', hp'⟩ := (flipIdx_beadChain_lt_iff e (F ≫ Φ) p).mp (hX₁ ▸ hcase)
      obtain ⟨q', hq'⟩ := (flipIdx_beadChain_lt_iff e (F ≫ Φ) q).mp (hX₁ ▸ hcaseq)
      subst hp'
      subst hq'
      rw [hU₁]
      exact key_face F Φ t p' q'
    · -- both coordinates are flipped in the tail
      have hcaseq : ¬ flipIdx (wedgeToCubes ⟨[e], ψL⟩) q < (wedgeToCubes ⟨[e], ψL⟩).length :=
        fun hq => hcase (flipIdx_sameSide hpq.symm hq)
      rw [flipIdx_append_lt_iff_right (fun h => hcase ((hsupp₁ p).mp h))
        (fun h => hcaseq ((hsupp₁ q).mp h))]
      rw [flipIdx_append_right hcase, flipIdx_append_right hcaseq] at hpq
      rw [flipIdx_append_right hcase, List.length_append] at hfound
      exact key_wedge rest c (wedgeInclR [e] rest ≫ g) Φ t
        (wedgeToCubes ⟨rest, ψR⟩) (wedgeToCubes ⟨𝟙^(dimSum rest), u₂.hom ≫ ψR⟩)
        (wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ (serialWedge1 c).hom.hom ≫ Φ⟩)
        rfl rfl rfl p q (by omega) (by omega)

/-! ## Part 6 — one bead of the target, an arbitrary source -/

/-- `key_wedge` transported across `runRestrict_singleton`: the one-bead target, spelled with the
bi-pointed `f : ⋁A ⟶ ⋁[c]` that the target recursion produces. -/
theorem key_singleton (A : List ℕ+) (c : ℕ+) (f : ⋁A ⟶ ⋁[c])
    (Φ : (⋁[c]).toPsh ⟶ (□n).toPsh) (t : Run [c]) (X U V : CubeList n)
    (hX : X = wedgeToCubes ⟨A, f.hom ≫ Φ⟩)
    (hU : U = wedgeToCubes ⟨𝟙^(dimSum A), (runRestrict [c] A f t).hom ≫ f.hom ≫ Φ⟩)
    (hV : V = wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ Φ⟩)
    (p q : Fin n) (hpq : flipIdx X p = flipIdx X q) (hfound : flipIdx X p < X.length) :
    (flipIdx U p < flipIdx U q ↔ flipIdx V p < flipIdx V q) := by
  have hid : (serialWedge1 c).hom.hom ≫ (serialWedge1 c).inv.hom = 𝟙 ((⋁[c]).toPsh) :=
    congrArg BPSet.Hom.hom (serialWedge1 c).hom_inv_id
  have hgΦ : (f.hom ≫ (serialWedge1 c).hom.hom) ≫ ((serialWedge1 c).inv.hom ≫ Φ)
      = f.hom ≫ Φ := by
    rw [Category.assoc, ← Category.assoc ((serialWedge1 c).hom.hom), hid, Category.id_comp]
  have htΦ : (serialWedge1 c).hom.hom ≫ (serialWedge1 c).inv.hom ≫ Φ = Φ := by
    rw [← Category.assoc, hid, Category.id_comp]
  have hrun : runRestrict [c] A f t = runRestrictWedge A (f.hom ≫ (serialWedge1 c).hom.hom) t :=
    runRestrict_singleton f t
  refine key_wedge A c (f.hom ≫ (serialWedge1 c).hom.hom) ((serialWedge1 c).inv.hom ≫ Φ) t
    X U V ?_ ?_ ?_ p q hpq hfound
  · rw [hX]
    exact congrArg (fun z : (⋁A).toPsh ⟶ (□n).toPsh => wedgeToCubes ⟨A, z⟩) hgΦ.symm
  · rw [hU, hrun]
    exact congrArg (fun z : (⋁A).toPsh ⟶ (□n).toPsh =>
      wedgeToCubes ⟨𝟙^(dimSum A),
        (runRestrictWedge A (f.hom ≫ (serialWedge1 c).hom.hom) t).hom ≫ z⟩) hgΦ.symm
  · rw [hV]
    exact congrArg (fun z : (⋁[c]).toPsh ⟶ (□n).toPsh =>
      wedgeToCubes ⟨𝟙^(dimSum [c]), t.hom ≫ z⟩) htΦ.symm

/-! ## Part 7 — the target recursion -/

/-- **Restriction preserves the order of a run inside one bead of the source.**  Recursion on the
target list: `wedge_split_tensor` cuts `f` at the head bead, `runRestrict_tensor'` cuts the
restricted run there too, and `key_singleton` handles the head. -/
theorem key_target : ∀ (L : List ℕ+) (A : List ℕ+) (f : ⋁A ⟶ ⋁L)
    (Φ : (⋁L).toPsh ⟶ (□n).toPsh) (r : Run L) (X U V : CubeList n),
    X = wedgeToCubes ⟨A, f.hom ≫ Φ⟩ →
    U = wedgeToCubes ⟨𝟙^(dimSum A), (runRestrict L A f r).hom ≫ f.hom ≫ Φ⟩ →
    V = wedgeToCubes ⟨𝟙^(dimSum L), r.hom ≫ Φ⟩ →
    ∀ p q : Fin n, flipIdx X p = flipIdx X q → flipIdx X p < X.length →
    (flipIdx U p < flipIdx U q ↔ flipIdx V p < flipIdx V q)
  | [], A, f, Φ, r, X, U, V, hX, _, _, p, q, _, hfound => by
      subst hX
      rw [wedgeToCubes_length] at hfound
      obtain rfl : A = [] := eq_nil_of_dimSum_zero (serialWedge_dimSum_eq f)
      exact absurd hfound (by simp)
  | c :: rest, A, f, Φ, r, X, U, V, hX, hU, hV, p, q, hpq, hfound => by
      obtain ⟨A₁, A₂, ha, f₁, f₂, hf⟩ := wedge_split_tensor [c] rest f
      subst ha
      have hf' : f = wedgeTensor f₁ f₂ := hf.trans (Category.id_comp _)
      subst hf'
      set s₁ : Run [c] := (Run.split r).1 with hs₁
      set s₂ : Run rest := (Run.split r).2 with hs₂
      have hr : runAppend s₁ s₂ = r := runAppend_split r
      set ΦL : (⋁[c]).toPsh ⟶ (□n).toPsh := wedgeInclL [c] rest ≫ Φ with hΦL
      set ΦR : (⋁rest).toPsh ⟶ (□n).toPsh := wedgeInclR [c] rest ≫ Φ with hΦR
      set v₁ : Run A₁ := runRestrict [c] A₁ f₁ s₁ with hv₁
      set v₂ : Run A₂ := runRestrict rest A₂ f₂ s₂ with hv₂
      have hLcomp : wedgeInclL A₁ A₂ ≫ (wedgeTensor f₁ f₂).hom ≫ Φ = f₁.hom ≫ ΦL := by
        rw [← Category.assoc, wedgeTensor_inclL, Category.assoc]
      have hRcomp : wedgeInclR A₁ A₂ ≫ (wedgeTensor f₁ f₂).hom ≫ Φ = f₂.hom ≫ ΦR := by
        rw [← Category.assoc, wedgeTensor_inclR, Category.assoc]
      -- the three cube lists all split at the junction
      have hXs : X = wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩ ++ wedgeToCubes ⟨A₂, f₂.hom ≫ ΦR⟩ :=
        hX.trans ((wedgeToCubes_append A₁ A₂ ((wedgeTensor f₁ f₂).hom ≫ Φ)).trans
          (congrArg₂ (· ++ ·)
            (congrArg (fun z : (⋁A₁).toPsh ⟶ (□n).toPsh => wedgeToCubes ⟨A₁, z⟩) hLcomp)
            (congrArg (fun z : (⋁A₂).toPsh ⟶ (□n).toPsh => wedgeToCubes ⟨A₂, z⟩) hRcomp)))
      have hUeq : runRestrict (c :: rest) (A₁ ++ A₂) (wedgeTensor f₁ f₂) r
          = runAppend v₁ v₂ := by
        rw [← hr, runRestrict_tensor' f₁ f₂ s₁ s₂]
      have hUs : U = wedgeToCubes ⟨𝟙^(dimSum A₁), v₁.hom ≫ f₁.hom ≫ ΦL⟩
            ++ wedgeToCubes ⟨𝟙^(dimSum A₂), v₂.hom ≫ f₂.hom ≫ ΦR⟩ := by
        refine hU.trans ?_
        rw [hUeq]
        exact (wedgeToCubes_runAppend (K := □n) A₁ A₂ v₁ v₂ ((wedgeTensor f₁ f₂).hom ≫ Φ)).trans
          (congrArg₂ (· ++ ·)
            (congrArg (fun z : (⋁A₁).toPsh ⟶ (□n).toPsh =>
              wedgeToCubes ⟨𝟙^(dimSum A₁), v₁.hom ≫ z⟩) hLcomp)
            (congrArg (fun z : (⋁A₂).toPsh ⟶ (□n).toPsh =>
              wedgeToCubes ⟨𝟙^(dimSum A₂), v₂.hom ≫ z⟩) hRcomp))
      have hVs : V = wedgeToCubes ⟨𝟙^(dimSum [c]), s₁.hom ≫ ΦL⟩
            ++ wedgeToCubes ⟨𝟙^(dimSum rest), s₂.hom ≫ ΦR⟩ := by
        rw [hV, ← hr]
        exact wedgeToCubes_runAppend (K := □n) [c] rest s₁ s₂ Φ
      -- supports
      have hsuppU : ∀ x : Fin n,
          (flipIdx (wedgeToCubes ⟨𝟙^(dimSum A₁), v₁.hom ≫ f₁.hom ≫ ΦL⟩) x
              < (wedgeToCubes ⟨𝟙^(dimSum A₁), v₁.hom ≫ f₁.hom ≫ ΦL⟩).length
            ↔ flipIdx (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩) x
              < (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩).length) :=
        fun x => supp_precomp (M₂ := 𝟙^(dimSum A₁)) (M₁ := A₁) v₁ (f₁.hom ≫ ΦL) x
      have hsuppV : ∀ x : Fin n,
          (flipIdx (wedgeToCubes ⟨𝟙^(dimSum [c]), s₁.hom ≫ ΦL⟩) x
              < (wedgeToCubes ⟨𝟙^(dimSum [c]), s₁.hom ≫ ΦL⟩).length
            ↔ flipIdx (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩) x
              < (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩).length) :=
        fun x => (supp_precomp (M₂ := 𝟙^(dimSum [c])) (M₁ := [c]) s₁ ΦL x).trans
          (supp_precomp (M₂ := A₁) (M₁ := [c]) f₁ ΦL x).symm
      rw [hUs, hVs]
      rw [hXs] at hpq hfound
      by_cases hcase : flipIdx (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩) p
          < (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩).length
      · have hcaseq := flipIdx_sameSide hpq hcase
        rw [flipIdx_append_lt_iff_left ((hsuppU p).mpr hcase) ((hsuppU q).mpr hcaseq),
          flipIdx_append_lt_iff_left ((hsuppV p).mpr hcase) ((hsuppV q).mpr hcaseq)]
        rw [flipIdx_append_left hcase, flipIdx_append_left hcaseq] at hpq
        rw [flipIdx_append_left hcase, List.length_append] at hfound
        exact key_singleton A₁ c f₁ ΦL s₁ _ _ _ rfl rfl rfl p q hpq (by omega)
      · have hcaseq : ¬ flipIdx (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩) q
            < (wedgeToCubes ⟨A₁, f₁.hom ≫ ΦL⟩).length :=
          fun hq => hcase (flipIdx_sameSide hpq.symm hq)
        rw [flipIdx_append_lt_iff_right (fun h => hcase ((hsuppU p).mp h))
            (fun h => hcaseq ((hsuppU q).mp h)),
          flipIdx_append_lt_iff_right (fun h => hcase ((hsuppV p).mp h))
            (fun h => hcaseq ((hsuppV q).mp h))]
        rw [flipIdx_append_right hcase, flipIdx_append_right hcaseq] at hpq
        rw [flipIdx_append_right hcase, List.length_append] at hfound
        exact key_target rest A₂ f₂ ΦR s₂ _ _ _ rfl rfl rfl p q (by omega) (by omega)

/-! ## Part 8 — the wall-crossing law -/

/-- A sign of a difference is determined by the two strict orders. -/
theorem sign_sub_eq_of_lt_iff {x y z w : ℤ} (h1 : x < y ↔ z < w) (h2 : y < x ↔ w < z) :
    sign (x - y) = sign (z - w) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [sign_neg (by omega), sign_neg (by have := h1.mp h; omega)]
  · have hzw : ¬ z < w := fun hc => absurd (h1.mpr hc) (by omega)
    have hwz : ¬ w < z := fun hc => absurd (h2.mpr hc) (by omega)
    rw [show x - y = 0 by omega, show z - w = 0 by omega]
  · rw [sign_pos (by omega), sign_pos (by have := h2.mp h; omega)]

/-- The covector height of a chain, as a `flipIdx`. -/
theorem chCovectorHeight_eq_flipIdx (a : Ch (□n)) (p : Fin n) :
    chCovectorHeight a p = (flipIdx (wedgeToCubes ⟨a.dims, a.map.hom⟩) p : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ)) (flipIdx_eq_blockIndex (wedgeToRefineObj a) p).symm

/-- The height of a coordinate under a run, as a `flipIdx`. -/
theorem runHeight_eq_flipIdx (a : Ch (□n)) (s : Run a.dims) (p : Fin n) :
    runHeight a s p
      = (flipIdx (wedgeToCubes ⟨𝟙^(dimSum a.dims), s.hom ≫ a.map.hom⟩) p : ℤ) :=
  congrArg (fun k : ℕ => (k : ℤ))
    (flipIdx_eq_blockIndex (wedgeToRefineObj (runChain a s)) p).symm

/-- **Restriction preserves the order of the run inside one bead of `a`.** -/
theorem runHeight_lt_iff_of_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims)
    (p q : Fin n) (heq : chCovectorHeight a p = chCovectorHeight a q) :
    (runHeight a (runRestrict b.dims a.dims f.φ r) p
        < runHeight a (runRestrict b.dims a.dims f.φ r) q
      ↔ runHeight b r p < runHeight b r q) := by
  have hw : f.φ.hom ≫ b.map.hom = a.map.hom := by
    have h := congrArg BPSet.Hom.hom f.w; rwa [comp_hom] at h
  have hpq : flipIdx (wedgeToCubes ⟨a.dims, a.map.hom⟩) p
      = flipIdx (wedgeToCubes ⟨a.dims, a.map.hom⟩) q := by
    have h2 := heq
    rw [chCovectorHeight_eq_flipIdx, chCovectorHeight_eq_flipIdx] at h2
    exact_mod_cast h2
  have hkey := key_target b.dims a.dims f.φ b.map.hom r
    (wedgeToCubes ⟨a.dims, a.map.hom⟩)
    (wedgeToCubes ⟨𝟙^(dimSum a.dims), (runRestrict b.dims a.dims f.φ r).hom ≫ a.map.hom⟩)
    (wedgeToCubes ⟨𝟙^(dimSum b.dims), r.hom ≫ b.map.hom⟩)
    (congrArg (fun z : (⋁a.dims).toPsh ⟶ (□n).toPsh => wedgeToCubes ⟨a.dims, z⟩) hw.symm)
    (congrArg (fun z : (⋁a.dims).toPsh ⟶ (□n).toPsh =>
      wedgeToCubes ⟨𝟙^(dimSum a.dims), (runRestrict b.dims a.dims f.φ r).hom ≫ z⟩) hw.symm)
    rfl p q hpq (flipIdx_lt_of_cube a.map p)
  rw [runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx,
    Nat.cast_lt, Nat.cast_lt]
  exact hkey

/-- **The bead-local half of the Salvetti wall-crossing law** — the hypothesis of
`wallCrossing_of_sameBlock`, discharged. -/
theorem wallCrossing_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims)
    (e : BraidGround n) (heq : chCovectorHeight a e.1.1 = chCovectorHeight a e.1.2) :
    sign (runHeight a (runRestrict b.dims a.dims f.φ r) e.1.1
          - runHeight a (runRestrict b.dims a.dims f.φ r) e.1.2)
      = sign (runHeight b r e.1.1 - runHeight b r e.1.2) :=
  sign_sub_eq_of_lt_iff (runHeight_lt_iff_of_sameBlock f r e.1.1 e.1.2 heq)
    (runHeight_lt_iff_of_sameBlock f r e.1.2 e.1.1 heq.symm)

/-- **The Salvetti wall-crossing law.**  Restricting a run along `f : a ⟶ b` composes `a`'s
covector into the run's tope. -/
theorem wallCrossing {a b : Ch (□n)} (f : a ⟶ b) (r : Run b.dims) :
    braidSign (runHeight a (runRestrict b.dims a.dims f.φ r))
      = braidSign (chCovectorHeight a) ⊙ braidSign (runHeight b r) :=
  wallCrossing_of_sameBlock f r (fun e he => wallCrossing_sameBlock f r e he)


/-! ## Part 9 — the Salvetti comparison of presheaves

`runTopeEquiv` is objectwise a bijection; `wallCrossing` is exactly its naturality square, since
`salFunctor`'s restriction map *is* the wall-crossing composition `X' ⊙ ·`. -/

/-- **Runs are the Salvetti presheaf of the braid arrangement.** -/
def salLinesIso (n : ℕ) :
    Lines (□n) ≅ (chFaceEquiv n).functor ⋙ COM.salFunctor (braidCOM n) :=
  NatIso.ofComponents (fun a => Equiv.toIso (runTopeEquiv a.unop)) (by
    intro a b f
    ext r
    exact Subtype.ext (wallCrossing f.unop r))

end CubeChains
